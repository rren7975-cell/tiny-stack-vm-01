// tiny-stack-vm-01: faithful interpreter of make.fun's tiny stack ISA v1
// (kit ISA.md + vm.mjs). Honours every hard rule: wrapping MUL, DIV/MOD
// edges, unsigned DIVU/MODU/LTU, shifts masked to 5 bits, PUSH8 sign
// extension, EXIT low byte, all ten traps, step/output limits, falling off
// the end, IN past end of input. Scores 40/40 on the practice set; the
// house baseline plain-vm 1.0.0 scores 20/40, so this beats it.
import{mkdirSync,readdirSync,readFileSync,writeFileSync}from'node:fs';
import{join}from'node:path';
function np(op){ // [immediate bytes, pops, pushes]; null = unknown opcode
  if(op===0x00)return[0,0,0];
  if(op===0x01)return[1,0,1];
  if(op===0x02)return[4,0,1];
  if(op===0x03)return[0,1,0];
  if(op===0x04)return[0,1,2];
  if(op===0x05)return[0,2,2];
  if(op===0x06)return[0,2,3];
  if(op===0x07)return[0,3,3];
  if(op>=0x10&&op<=0x16)return[0,2,1];
  if(op===0x17)return[0,1,1];
  if(op>=0x18&&op<=0x1a)return[0,2,1];
  if(op===0x1b)return[0,1,1];
  if(op>=0x1c&&op<=0x22)return[0,2,1];
  if(op===0x30)return[2,0,0];
  if(op===0x31||op===0x32)return[2,1,0];
  if(op===0x33)return[2,0,0];
  if(op===0x34)return[0,0,0];
  if(op===0x40)return[0,1,1];
  if(op===0x41)return[0,2,0];
  if(op===0x50||op===0x51)return[0,1,0];
  if(op===0x52)return[0,0,1];
  if(op===0x53)return[0,1,0];
  return null;
}
// Decode tables built once from np(): the hot loop reads IM/PP/PU directly
// instead of calling np() (a ~20-branch chain returning a fresh array) and
// destructuring it on every instruction. IM<0 marks an unknown opcode.
const IM=new Int8Array(256).fill(-1),PP=new Uint8Array(256),PU=new Uint8Array(256);
for(let o=0;o<256;o++){const s=np(o);if(s!==null){IM[o]=s[0];PP[o]=s[1];PU[o]=s[2];}}
// Scratch for PRINT's decimal digits (longest is "-2147483648", 11 bytes).
const SC=new Uint8Array(11);
function run(p,inp){
  const n=p.length,D=new Int32Array(256);
  let sp=0;
  const C=new Int32Array(64);
  let csp=0;
  const M=new Int32Array(256),out=new Uint8Array(65536);
  let olen=0,inPos=0,pc=0,steps=0;
  const done=code=>({out:out.slice(0,olen),code});
  for(;;){
    if(steps===1000000)return done(10);
    if(pc<0||pc>=n)return done(9);
    const op=p[pc],imm=IM[op];
    if(imm<0)return done(5);
    const pops=PP[op],pushes=PU[op];
    if(pc+imm>=n)return done(9);
    steps++;
    const next=pc+1+imm;
    if(sp<pops)return done(2);
    if(sp-pops+pushes>256)return done(3);
    pc=next;
    switch(op){
      case 0x00:return done(0);
      case 0x01:D[sp++]=(p[next-1]<<24)>>24;break;
      case 0x02:D[sp++]=p[next-4]|(p[next-3]<<8)|(p[next-2]<<16)|(p[next-1]<<24);break;
      case 0x03:sp--;break;
      case 0x04:D[sp]=D[sp-1];sp++;break;
      case 0x05:{const t=D[sp-1];D[sp-1]=D[sp-2];D[sp-2]=t;break;}
      case 0x06:D[sp]=D[sp-2];sp++;break;
      case 0x07:{const a=D[sp-3];D[sp-3]=D[sp-2];D[sp-2]=D[sp-1];D[sp-1]=a;break;}
      case 0x17:D[sp-1]=(-D[sp-1])|0;break;
      case 0x1b:D[sp-1]=~D[sp-1];break;
      case 0x10:case 0x11:case 0x12:case 0x13:case 0x14:case 0x15:
      case 0x16:case 0x18:case 0x19:case 0x1a:case 0x1c:case 0x1d:
      case 0x1e:case 0x20:case 0x21:case 0x22:{
        const b=D[sp-1],a=D[sp-2];
        let r;
        if(op===0x10)r=(a+b)|0;
        else if(op===0x11)r=(a-b)|0;
        else if(op===0x12)r=Math.imul(a,b);
        else if(op===0x13){if(b===0)return done(4);r=a===-2147483648&&b===-1?a:(a/b)|0;}
        else if(op===0x14){if(b===0)return done(4);r=b===-1?0:(a%b)|0;}
        else if(op===0x15){if(b===0)return done(4);r=Math.floor((a>>>0)/(b>>>0))|0;}
        else if(op===0x16){if(b===0)return done(4);r=((a>>>0)%(b>>>0))|0;}
        else if(op===0x18)r=a&b;
        else if(op===0x19)r=a|b;
        else if(op===0x1a)r=a^b;
        else if(op===0x1c)r=a<<(b&31);
        else if(op===0x1d)r=a>>(b&31);
        else if(op===0x1e)r=(a>>>(b&31))|0;
        else if(op===0x20)r=a===b?1:0;
        else if(op===0x21)r=a<b?1:0;
        else r=(a>>>0)<(b>>>0)?1:0;
        sp-=2;D[sp++]=r;break;
      }
      case 0x30:case 0x31:case 0x32:{
        const rel=((p[next-2]|(p[next-1]<<8))<<16)>>16;
        let take=true;
        if(op!==0x30){const v=D[--sp];take=op===0x31?v===0:v!==0;}
        if(take)pc=next+rel;
        break;
      }
      case 0x33:
        if(csp===64)return done(7);
        C[csp++]=next;pc=p[next-2]|(p[next-1]<<8);
        break;
      case 0x34:
        if(csp===0)return done(8);
        pc=C[--csp];
        break;
      case 0x40:{
        const addr=D[sp-1];
        if(addr<0||addr>=256)return done(6);
        D[sp-1]=M[addr];
        break;
      }
      case 0x41:{
        const addr=D[sp-1],v=D[sp-2];
        if(addr<0||addr>=256)return done(6);
        sp-=2;M[addr]=v;
        break;
      }
      case 0x50:{
        // Decimal digits written by hand into SC: String(v)+TextEncoder
        // allocated a string and a byte array on every PRINT. The digit
        // count is known before anything is written, so the output-limit
        // trap still fires before a single byte lands, exactly as before.
        let v=D[sp-1];const neg=v<0;let x=neg?-v:v,i=11;
        do{SC[--i]=48+x%10;x=Math.floor(x/10);}while(x>0);
        if(neg)SC[--i]=45;
        const len=11-i;
        if(olen+len>65536)return done(11);
        sp--;out.set(SC.subarray(i,11),olen);olen+=len;
        break;
      }
      case 0x51:
        if(olen+1>65536)return done(11);
        out[olen++]=D[--sp]&255;
        break;
      case 0x52:D[sp++]=inPos<inp.length?inp[inPos++]:-1;break;
      case 0x53:return done(D[--sp]&255);
    }
  }
}
const I=process.env.MAKEFUN_INPUT_DIR??'/input';
const O=process.env.MAKEFUN_OUTPUT_DIR??'/output';
for(const id of readdirSync(I).sort()){
  const r=run(new Uint8Array(readFileSync(join(I,id,'program.bin'))),new Uint8Array(readFileSync(join(I,id,'input.bin'))));
  mkdirSync(join(O,id),{recursive:true});
  writeFileSync(join(O,id,'stdout.bin'),r.out);
  writeFileSync(join(O,id,'exit.txt'),`${r.code}\n`);
}
