// Independent verifier: upper Fibonacci coordinates, direct digit products,
// quadratic reciprocity, and enumeration of field elements for columns >=3.
const assert=require('node:assert/strict');
const fs=require('node:fs');
const d=JSON.parse(fs.readFileSync(process.argv[2] || 'Erdos849LindShallowExtended.json','utf8'));
assert(d.last>=9 && d.triangular>=d.last && d.columns>=2 && d.limit<=90000000);
assert.equal(d.primes.length,d.triangular-8);

function prime(p) {
  if (p<2) return false;
  for(let i=2;i*i<=p;i++) if(p%i===0) return false;
  return true;
}

function reciprocal(a,p) {
  let x=1, y=0, r=a,s=p;
  while(s) {
    const q=Math.floor(r/s);
    [r,s]=[s,r-q*s];
    [x,y]=[y,x-q*y];
  }
  assert.equal(r,1);
  return (x%p+p)%p;
}

function residue(n,k,p) {
  const bp=BigInt(p);
  let num=1,den=1;
  while(k) {
    const a=Number(n%bp), b=Number(k%bp);
    if(b>a) return 0;
    for(let j=1;j<=Math.min(b,a-b);j++) {
      num=num*(a-j+1)%p;
      den=den*j%p;
    }
    n/=bp;
    k/=bp;
  }
  return num*reciprocal(den,p)%p;
}

function jacobi(a,b) {
  let sign=1;
  a%=b;
  while(a) {
    while(a%2===0) {
      a/=2;
      if(b%8===3 || b%8===5) sign=-sign;
    }
    if(a%4===3 && b%4===3) sign=-sign;
    [a,b]=[b%a,a];
  }
  return b===1 ? sign : 0;
}

const fb=[0n,1n];
while(fb.length<=2*d.triangular+3) fb.push(fb.at(-1)+fb.at(-2));
const groups=new Map();
for(let i=9;i<=d.triangular;i++) {
  const cert=d.primes[i-9];
  assert.equal(cert.length,i<=d.last ? d.columns-1 : 1);
  for(let j=2;j<=cert.length+1;j++) {
    const p=cert[j-2];
    assert(Number.isSafeInteger(p) && p>j && p<=d.limit);
    if(!groups.has(p)) groups.set(p,new Map());
    const g=groups.get(p);
    if(!g.has(i)) g.set(i,[]);
    g.get(i).push(j);
  }
}
let checked=0;
for(const [p,indices] of groups) {
  assert(prime(p));
  const forbidden=new Map();
  for(const [i,cols] of indices) {
    const n=fb[2*i+2]*fb[2*i+3], k=fb[2*i]*fb[2*i+3];
    const y=residue(n,k,p);
    assert(y>0);
    for(const j of cols) {
      if(j===2) assert.equal(jacobi(8*y+1,p),-1);
      else {
        if(!forbidden.has(j)) forbidden.set(j,new Set());
        forbidden.get(j).add(y);
      }
      checked++;
    }
  }
  if(!forbidden.size) continue;
  const inv=new Uint32Array(p);
  inv[1]=1;
  for(let i=2;i<p;i++) inv[i]=p-Math.floor(p/i)*inv[p%i]%p;
  const wanted=new Uint8Array(p);
  for(const [j,targets] of forbidden) {
    for(const y of targets) wanted[y]=1;
    let c=1;
    for(let m=j;m<p;m++) {
      assert(!wanted[c]);
      if(m+1<p) c=(c*(m+1)%p)*inv[m+1-j]%p;
    }
    for(const y of targets) wanted[y]=0;
  }
}
console.log(`Verified ${checked} shallow exclusions with ${groups.size} prime moduli.`);
