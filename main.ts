import fs from 'node:fs';

// Tiny stack VM for make.fun's ISA v1 (see kit ISA.md). Plain JavaScript in a
// .ts file: Node 22 runs it as-is, no install step, no dependencies.
//
// Opcode metadata, packed: one number per opcode byte,
//   code = immBytes * 16 + pops * 4 + pushes + 1
// (0 means "not an opcode"). Decoded once into a 256-slot table.
const OP = [0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34, 48, 49, 50, 51, 52, 64, 65, 80, 81, 82, 83];
const PK = [1, 18, 66, 5, 7, 11, 12, 16, 10, 10, 10, 10, 10, 10, 10, 6, 10, 10, 10, 6, 10, 10, 10, 10, 10, 10, 33, 37, 37, 33, 1, 6, 9, 5, 5, 2, 5];
const META = new Uint8Array(256);
for (let i = 0; i < OP.length; i++) META[OP[i]] = PK[i];

const enc = new TextEncoder();

// Run one program on one input. Returns [stdoutBytes, exitCode].
// Traps end the run at once with the trap's code as the exit code and the
// output written so far kept.
function run(P, I) {
  const n = P.length;
  const S = new Int32Array(256); // data stack
  const C = new Int32Array(64); // call stack
  const M = new Int32Array(256); // memory
  const O = new Uint8Array(65536); // output
  let sp = 0, cp = 0, ol = 0, ip = 0, pc = 0, steps = 0;
  const end = (code) => [O.subarray(0, ol), code];

  for (;;) {
    if (steps === 1000000) return end(10); // step limit
    if (pc < 0 || pc >= n) return end(9); // pc outside the program
    const o = P[pc];
    const m = META[o] - 1;
    if (m < 0) return end(5); // unknown opcode
    const im = m >> 4, po = (m >> 2) & 3, pu = m & 3;
    if (pc + im >= n) return end(9); // immediate cut off by the end
    steps++;
    const nx = pc + 1 + im;
    if (sp < po) return end(2); // stack underflow
    if (sp - po + pu > 256) return end(3); // stack overflow
    pc = nx;

    if (o === 0) return end(0); // HALT
    if (o === 1) { S[sp++] = (P[nx - 1] << 24) >> 24; continue; } // PUSH8, sign-extended
    if (o === 2) { S[sp++] = P[nx - 4] | (P[nx - 3] << 8) | (P[nx - 2] << 16) | (P[nx - 1] << 24); continue; } // PUSH32
    if (o === 3) { sp--; continue; } // POP
    if (o === 4) { S[sp] = S[sp - 1]; sp++; continue; } // DUP
    if (o === 5) { const t = S[sp - 1]; S[sp - 1] = S[sp - 2]; S[sp - 2] = t; continue; } // SWAP
    if (o === 6) { S[sp] = S[sp - 2]; sp++; continue; } // OVER
    if (o === 7) { const t = S[sp - 3]; S[sp - 3] = S[sp - 2]; S[sp - 2] = S[sp - 1]; S[sp - 1] = t; continue; } // ROT
    if (o === 0x17) { S[sp - 1] = -S[sp - 1] | 0; continue; } // NEG, wraps
    if (o === 0x1b) { S[sp - 1] = ~S[sp - 1]; continue; } // NOT
    if (o === 0x52) { S[sp++] = ip < I.length ? I[ip++] : -1; continue; } // IN, -1 past the end
    if (o === 0x53) return end(S[--sp] & 255); // EXIT, low byte

    // Two-operand arithmetic / logic / comparison ops (0x10-0x16, 0x18-0x1a, 0x1c-0x1e, 0x20-0x22).
    if (o >= 0x10 && o <= 0x22 && o !== 0x17 && o !== 0x1b && o !== 0x1f) {
      const b = S[sp - 1], a = S[sp - 2];
      let r;
      if (o === 0x10) r = (a + b) | 0; // ADD, wraps
      else if (o === 0x11) r = (a - b) | 0; // SUB, wraps
      else if (o === 0x12) r = Math.imul(a, b); // MUL, low 32 bits of the exact product
      else if (o === 0x13) { // DIV, truncated toward zero
        if (b === 0) return end(4);
        r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
      } else if (o === 0x14) { // MOD, sign of a
        if (b === 0) return end(4);
        r = b === -1 ? 0 : (a % b) | 0;
      } else if (o === 0x15) { // DIVU, unsigned
        if (b === 0) return end(4);
        r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
      } else if (o === 0x16) { // MODU, unsigned
        if (b === 0) return end(4);
        r = ((a >>> 0) % (b >>> 0)) | 0;
      } else if (o === 0x18) r = a & b; // AND
      else if (o === 0x19) r = a | b; // OR
      else if (o === 0x1a) r = a ^ b; // XOR
      else if (o === 0x1c) r = a << (b & 31); // SHL, low 5 bits of the count
      else if (o === 0x1d) r = a >> (b & 31); // SHR, arithmetic
      else if (o === 0x1e) r = (a >>> (b & 31)) | 0; // SHRU, logical
      else if (o === 0x20) r = a === b ? 1 : 0; // EQ
      else if (o === 0x21) r = a < b ? 1 : 0; // LT, signed
      else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU, unsigned
      S[sp - 2] = r;
      sp--;
      continue;
    }

    // Jumps: signed 16-bit offset from the next instruction.
    if (o === 0x30 || o === 0x31 || o === 0x32) {
      const rel = ((P[nx - 2] | (P[nx - 1] << 8)) << 16) >> 16;
      if (o === 0x30) { pc = nx + rel; continue; }
      const v = S[--sp];
      if ((o === 0x31) === (v === 0)) pc = nx + rel;
      continue;
    }
    if (o === 0x33) { // CALL, unsigned 16-bit target
      if (cp === 64) return end(7);
      C[cp++] = nx;
      pc = P[nx - 2] | (P[nx - 1] << 8);
      continue;
    }
    if (o === 0x34) { // RET
      if (cp === 0) return end(8);
      pc = C[--cp];
      continue;
    }
    if (o === 0x40) { // LOAD
      const a = S[sp - 1];
      if (a < 0 || a > 255) return end(6);
      S[sp - 1] = M[a];
      continue;
    }
    if (o === 0x41) { // STORE: value below, address on top
      const a = S[sp - 1];
      if (a < 0 || a > 255) return end(6);
      sp -= 2;
      M[a] = S[sp];
      continue;
    }
    if (o === 0x50) { // PRINT: decimal ASCII, no newline
      const bytes = enc.encode(String(S[sp - 1]));
      if (ol + bytes.length > 65536) return end(11); // writes none of its bytes
      sp--;
      O.set(bytes, ol);
      ol += bytes.length;
      continue;
    }
    // PUTC (0x51): one byte, v AND 255.
    if (ol + 1 > 65536) return end(11);
    O[ol++] = S[--sp] & 255;
  }
}

// Driver: answer every instance under MAKEFUN_INPUT_DIR, in sorted order,
// writing stdout.bin and exit.txt per instance under MAKEFUN_OUTPUT_DIR.
const IN_DIR = process.env.MAKEFUN_INPUT_DIR || '/input';
const OUT_DIR = process.env.MAKEFUN_OUTPUT_DIR || '/output';

for (const id of fs.readdirSync(IN_DIR).sort()) {
  const dir = IN_DIR + '/' + id;
  if (!fs.statSync(dir).isDirectory()) continue;
  const [out, code] = run(fs.readFileSync(dir + '/program.bin'), fs.readFileSync(dir + '/input.bin'));
  const outDir = OUT_DIR + '/' + id;
  fs.mkdirSync(outDir, { recursive: true });
  fs.writeFileSync(outDir + '/stdout.bin', out);
  fs.writeFileSync(outDir + '/exit.txt', code + '\n');
}
