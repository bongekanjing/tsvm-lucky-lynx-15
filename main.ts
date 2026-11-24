import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const IN = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

const SM = 256;        // data stack values
const CM = 64;         // return addresses
const MW = 256;        // memory words
const STEPS = 1000000;
const OMAX = 65536;

// Execute one program. Returns { out: number[], code: number }.
// The step order is the ISA's: budget, then pc, then opcode, then the
// immediate's fit, then the stack's needs, then the instruction's own
// traps, then its effect.
function exec(prog, inp) {
  const n = prog.length;
  const S = new Int32Array(SM);
  const R = new Int32Array(CM);
  const M = new Int32Array(MW);
  const buf = new Uint8Array(OMAX);
  let sp = 0, rp = 0, olen = 0, ip = 0, pc = 0, steps = 0;

  const finish = (code) => ({ out: buf.subarray(0, olen), code });

  for (;;) {
    if (steps === STEPS) return finish(10);
    if (pc < 0 || pc >= n) return finish(9);
    const op = prog[pc];

    // immediate length per opcode; -1 marks a byte the ISA does not name
    let imm;
    switch (op) {
      case 0x00: case 0x03: case 0x04: case 0x05: case 0x06: case 0x07:
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15:
      case 0x16: case 0x17: case 0x18: case 0x19: case 0x1a: case 0x1b:
      case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22:
      case 0x34:
      case 0x40: case 0x41:
      case 0x50: case 0x51: case 0x52: case 0x53:
        imm = 0; break;
      case 0x01: imm = 1; break;
      case 0x02: imm = 4; break;
      case 0x30: case 0x31: case 0x32: case 0x33: imm = 2; break;
      default: return finish(5);
    }
    if (pc + imm >= n) return finish(9);
    steps++;
    const nx = pc + 1 + imm;

    // how many values this instruction takes and leaves, for the two stack
    // traps. Every opcode is named: a default would give HALT, JMP, CALL and
    // RET two operands they do not have, and any program that halts on a
    // shallow stack would trap underflow instead.
    let take = 0, give = 0;
    switch (op) {
      case 0x00: case 0x30: case 0x33: case 0x34: break;        // nothing
      case 0x01: case 0x02: case 0x52: give = 1; break;          // push
      case 0x03: take = 1; break;
      case 0x04: take = 1; give = 2; break;
      case 0x05: take = 2; give = 2; break;
      case 0x06: take = 2; give = 3; break;
      case 0x07: take = 3; give = 3; break;
      case 0x17: case 0x1b: take = 1; give = 1; break;
      case 0x31: case 0x32: case 0x50: case 0x51: case 0x53: take = 1; break;
      case 0x40: take = 1; give = 1; break;
      case 0x41: take = 2; break;
      default: take = 2; give = 1; break;    // the binary operators
    }
    if (sp < take) return finish(2);
    if (sp - take + give > SM) return finish(3);
    pc = nx;

    switch (op) {
      case 0x00: return finish(0);
      case 0x01: S[sp++] = (prog[nx - 1] << 24) >> 24; break;
      case 0x02:
        S[sp++] = prog[nx - 4] | prog[nx - 3] << 8 | prog[nx - 2] << 16 | prog[nx - 1] << 24;
        break;
      case 0x03: sp--; break;
      case 0x04: S[sp] = S[sp - 1]; sp++; break;
      case 0x05: { const t = S[sp - 1]; S[sp - 1] = S[sp - 2]; S[sp - 2] = t; break; }
      case 0x06: S[sp] = S[sp - 2]; sp++; break;
      case 0x07: { const t = S[sp - 3]; S[sp - 3] = S[sp - 2]; S[sp - 2] = S[sp - 1]; S[sp - 1] = t; break; }
      case 0x17: S[sp - 1] = -S[sp - 1] | 0; break;
      case 0x1b: S[sp - 1] = ~S[sp - 1]; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15:
      case 0x16: case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d:
      case 0x1e: case 0x20: case 0x21: case 0x22: {
        const b = S[sp - 1], a = S[sp - 2];
        let r;
        if (op === 0x10) r = a + b | 0;
        else if (op === 0x11) r = a - b | 0;
        else if (op === 0x12) r = Math.imul(a, b);
        else if (op === 0x13) {
          if (b === 0) return finish(4);
          r = (a === -2147483648 && b === -1) ? a : (a / b) | 0;
        } else if (op === 0x14) {
          if (b === 0) return finish(4);
          r = b === -1 ? 0 : a % b | 0;
        } else if (op === 0x15) {
          if (b === 0) return finish(4);
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (op === 0x16) {
          if (b === 0) return finish(4);
          r = (a >>> 0) % (b >>> 0) | 0;
        } else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        sp -= 2; S[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: {
        const rel = ((prog[nx - 2] | prog[nx - 1] << 8) << 16) >> 16;
        let go = true;
        if (op !== 0x30) {
          const v = S[--sp];
          go = op === 0x31 ? v === 0 : v !== 0;
        }
        if (go) pc = nx + rel;
        break;
      }
      case 0x33:
        if (rp === CM) return finish(7);
        R[rp++] = nx;
        pc = prog[nx - 2] | prog[nx - 1] << 8;
        break;
      case 0x34:
        if (rp === 0) return finish(8);
        pc = R[--rp];
        break;
      case 0x40: {
        const a = S[sp - 1];
        if (a < 0 || a >= MW) return finish(6);
        S[sp - 1] = M[a];
        break;
      }
      case 0x41: {
        const a = S[sp - 1], v = S[sp - 2];
        if (a < 0 || a >= MW) return finish(6);
        sp -= 2; M[a] = v;
        break;
      }
      case 0x50: {
        const t = String(S[sp - 1]);
        if (olen + t.length > OMAX) return finish(11);
        for (let k = 0; k < t.length; k++) buf[olen++] = t.charCodeAt(k);
        sp--;
        break;
      }
      case 0x51:
        if (olen + 1 > OMAX) return finish(11);
        buf[olen++] = S[--sp] & 255;
        break;
      case 0x52: S[sp++] = ip < inp.length ? inp[ip++] : -1; break;
      case 0x53: return finish(S[--sp] & 255);
    }
  }
}

const ids = readdirSync(IN).sort();
for (const id of ids) {
  const dir = join(IN, id);
  const prog = readFileSync(join(dir, 'program.bin'));
  const inp = readFileSync(join(dir, 'input.bin'));
  const { out, code } = exec(prog, inp);
  mkdirSync(join(OUT, id), { recursive: true });
  writeFileSync(join(OUT, id, 'stdout.bin'), out);
  writeFileSync(join(OUT, id, 'exit.txt'), code + '\n');
}
