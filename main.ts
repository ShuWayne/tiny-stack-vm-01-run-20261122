// Tiny stack VM for make.fun's tiny stack ISA v1: one run answers a whole set
// (program.bin on input.bin -> stdout.bin + exit.txt per instance). Node 22.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const IN_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// Per opcode: [immediate bytes, popped, pushed].
const SPEC = new Map([
  [0,[0,0,0]],[1,[1,0,1]],[2,[4,0,1]],
  [3,[0,1,0]],[4,[0,1,2]],[5,[0,2,2]],
  [6,[0,2,3]],[7,[0,3,3]],
  [16,[0,2,1]],[17,[0,2,1]],[18,[0,2,1]],
  [19,[0,2,1]],[20,[0,2,1]],[21,[0,2,1]],
  [22,[0,2,1]],[23,[0,1,1]],[24,[0,2,1]],
  [25,[0,2,1]],[26,[0,2,1]],[27,[0,1,1]],
  [28,[0,2,1]],[29,[0,2,1]],[30,[0,2,1]],
  [32,[0,2,1]],[33,[0,2,1]],[34,[0,2,1]],
  [48,[2,0,0]],[49,[2,1,0]],[50,[2,1,0]],
  [51,[2,0,0]],[52,[0,0,0]],
  [64,[0,1,1]],[65,[0,2,0]],
  [80,[0,1,0]],[81,[0,1,0]],[82,[0,0,1]],
  [83,[0,1,0]],
]);

// Runs one program on its input; returns [bytes written, exit code]. A trap's
// exit code is the trap's code; the bytes written before it are kept.
function run(prog, input) {
  const n = prog.length;
  const st = new Int32Array(256);
  const cs = new Int32Array(64);
  const mem = new Int32Array(256);
  const out = new Uint8Array(65536);
  let sp = 0, cp = 0, ol = 0, ip = 0, pc = 0, steps = 0;
  const done = (code) => [out.subarray(0, ol), code];
  for (;;) {
    if (steps === 1000000) return done(10);
    if (pc < 0 || pc >= n) return done(9);
    const op = prog[pc];
    const spec = SPEC.get(op);
    if (spec === undefined) return done(5);
    const imm = spec[0], pops = spec[1], pushes = spec[2];
    if (pc + imm >= n) return done(9);
    steps++;
    const next = pc + 1 + imm;
    if (sp < pops) return done(2);
    if (sp - pops + pushes > 256) return done(3);
    pc = next;
    switch (op) {
      case 0x00: return done(0); // HALT
      case 0x01: st[sp++] = (prog[next - 1] << 24) >> 24; break; // PUSH8, sign-extended
      case 0x02: // PUSH32, little-endian
        st[sp++] = prog[next - 4] | (prog[next - 3] << 8) | (prog[next - 2] << 16) | (prog[next - 1] << 24);
        break;
      case 0x03: sp--; break; // POP
      case 0x04: st[sp] = st[sp - 1]; sp++; break; // DUP
      case 0x05: { const t = st[sp - 1]; st[sp - 1] = st[sp - 2]; st[sp - 2] = t; break; } // SWAP
      case 0x06: st[sp] = st[sp - 2]; sp++; break; // OVER
      case 0x07: { const a = st[sp - 3]; st[sp - 3] = st[sp - 2]; st[sp - 2] = st[sp - 1]; st[sp - 1] = a; break; } // ROT
      case 0x17: st[sp - 1] = (-st[sp - 1]) | 0; break; // NEG, wraps
      case 0x1b: st[sp - 1] = ~st[sp - 1]; break; // NOT
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = st[sp - 1], a = st[sp - 2];
        let r;
        switch (op) {
          case 0x10: r = (a + b) | 0; break; // ADD, wraps
          case 0x11: r = (a - b) | 0; break; // SUB, wraps
          case 0x12: r = Math.imul(a, b); break; // MUL, low 32 bits of the exact product
          case 0x13: // DIV, truncated toward zero
            if (b === 0) return done(4);
            r = (a === -2147483648 && b === -1) ? a : (a / b) | 0;
            break;
          case 0x14: // MOD, sign of a
            if (b === 0) return done(4);
            r = b === -1 ? 0 : (a % b) | 0;
            break;
          case 0x15: // DIVU, unsigned
            if (b === 0) return done(4);
            r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
            break;
          case 0x16: // MODU, unsigned
            if (b === 0) return done(4);
            r = ((a >>> 0) % (b >>> 0)) | 0;
            break;
          case 0x18: r = a & b; break;
          case 0x19: r = a | b; break;
          case 0x1a: r = a ^ b; break;
          case 0x1c: r = a << (b & 31); break; // SHL, low 5 bits of the count
          case 0x1d: r = a >> (b & 31); break; // SHR, arithmetic
          case 0x1e: r = (a >>> (b & 31)) | 0; break; // SHRU, logical
          case 0x20: r = a === b ? 1 : 0; break;
          case 0x21: r = a < b ? 1 : 0; break;
          case 0x22: r = (a >>> 0) < (b >>> 0) ? 1 : 0; break; // LTU, unsigned
        }
        sp -= 2;
        st[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: { // JMP/JZ/JNZ: pc = next + signed 16-bit offset
        const rel = ((prog[next - 2] | (prog[next - 1] << 8)) << 16) >> 16;
        let take = op === 0x30;
        if (op !== 0x30) { const v = st[--sp]; take = op === 0x31 ? v === 0 : v !== 0; }
        if (take) pc = next + rel;
        break;
      }
      case 0x33: // CALL, 64 return addresses held already traps 7
        if (cp === 64) return done(7);
        cs[cp++] = next;
        pc = prog[next - 2] | (prog[next - 1] << 8);
        break;
      case 0x34: // RET, an empty call stack traps 8
        if (cp === 0) return done(8);
        pc = cs[--cp];
        break;
      case 0x40: { // LOAD
        const a = st[sp - 1];
        if (a < 0 || a >= 256) return done(6);
        st[sp - 1] = mem[a];
        break;
      }
      case 0x41: { // STORE: ( value address -- )
        const a = st[sp - 1], v = st[sp - 2];
        if (a < 0 || a >= 256) return done(6);
        sp -= 2;
        mem[a] = v;
        break;
      }
      case 0x50: { // PRINT: decimal ASCII, no newline
        const s = String(st[sp - 1]);
        if (ol + s.length > 65536) return done(11);
        sp--;
        for (let i = 0; i < s.length; i++) out[ol++] = s.charCodeAt(i);
        break;
      }
      case 0x51: // PUTC: one byte, v AND 255
        if (ol + 1 > 65536) return done(11);
        out[ol++] = st[--sp] & 255;
        break;
      case 0x52: // IN: next input byte, -1 once the input is used up
        st[sp++] = ip < input.length ? input[ip++] : -1;
        break;
      case 0x53: return done(st[--sp] & 255); // EXIT: low byte is the code
    }
  }
}

for (const id of readdirSync(IN_DIR).sort()) {
  const prog = readFileSync(join(IN_DIR, id, 'program.bin'));
  const input = readFileSync(join(IN_DIR, id, 'input.bin'));
  const [stdout, code] = run(prog, input);
  mkdirSync(join(OUT_DIR, id), { recursive: true });
  writeFileSync(join(OUT_DIR, id, 'stdout.bin'), stdout);
  writeFileSync(join(OUT_DIR, id, 'exit.txt'), code + '\n');
}
