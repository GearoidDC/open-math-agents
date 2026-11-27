// Exact multiplicity of the ninth Lind coefficient. --local verifies its own
// prime cover. The default uses the published maximal gap 1476 below 4*10^18:
// https://sweet.ua.pt/tos/gaps.html (Oliveira e Silva, Herzog and Pardi).
const assert=require('node:assert/strict');
const started=Date.now();
const fib=[0,1];
while(fib.length<=21) fib.push(fib.at(-1)+fib.at(-2));
const N=fib[20]*fib[21], K=fib[18]*fib[21];
assert.equal(N,74049690);
assert.equal(K,28284464);
const local=process.argv.includes('--local');
const power=local ? 19 : 41;
const T=Math.ceil(N/power), maxRow=BigInt(T)*2n**BigInt(power);
assert(maxRow+1476n<4n*10n**18n && 1476<T);
function modPow(a,e,p) {
  let v=1n;
  while(e) {
    if(e%2n) v=v*a%p;
    a=a*a%p;
    e/=2n;
  }
  return v;
}
// Explicit next-side endpoint for the published list of gaps between primes
// below 4*10^18. Proth's test: every prime divisor has 2^40 in the order
// of 17, and thus exceeds the square root of endpointPrime.
const endpointPrime=3999786906849116161n;
assert(maxRow<endpointPrime && endpointPrime<4n*10n**18n);
assert((endpointPrime-1n)%(2n**41n)===2n**40n && endpointPrime<2n**80n);
assert(modPow(17n,(endpointPrime-1n)/2n,endpointPrime)===endpointPrime-1n);

function parent(nodes) {
  const out=[];
  for(let i=0;i<nodes.length;i+=2) out.push(nodes[i]*(nodes[i+1] ?? 1n));
  return out;
}

function exponent(n,k,p) {
  let a=n,b=k,c=n-k,v=0;
  while(a>=p) {
    a=Math.floor(a/p); b=Math.floor(b/p); c=Math.floor(c/p);
    v+=a-b-c;
  }
  return v;
}

const limit=T+100000;
const composite=new Uint8Array(N+1);
for(let i=2;i*i<=N;i++) if(!composite[i])
  for(let m=i*i;m<=N;m+=i) composite[m]=1;
const tests=[];
let bottom, nodes=[];
for(let p=2;p<=N;p++) if(!composite[p]) {
  const e=exponent(N,K,p);
  bottom=p;
  if(e) nodes.push(BigInt(p)**BigInt(e));
  else if(p<=limit) tests.push(p);
}
assert(exponent(N,K,bottom)>0);
while(nodes.length>1) nodes=parent(nodes);
const A=nodes[0];
const hex=A.toString(16);
const digitCount=1+Math.floor(Math.log10(parseInt(hex.slice(0,10),16))+
  (hex.length-10)*Math.log10(16));
const decade=10n**BigInt(digitCount-1);
assert(decade<=A && A<10n*decade);
const levels=[tests.map(BigInt)];
while(levels.at(-1).length>1) levels.push(parent(levels.at(-1)));
let rem=[A%levels.at(-1)[0]];
for(let i=levels.length-2;i>=0;i--)
  rem=levels[i].map((x,j)=>rem[Math.floor(j/2)]%x);
const residues=Uint32Array.from(rem,Number);
assert(residues.every(v=>v>0));
console.log(`Factored the target and computed ${tests.length} prime residues. T=${T}.`);

// With p>j, possible nonzero values C(m,j) modulo p are represented by
// m=p-1-s, 0<=s<=d=p-1-j. They are (-1)^(d-s)*C(d,s). Symmetry lets
// one loop cover both s and d-s. Every modular multiplication fits in 53 bits.
let inv=new Uint32Array(0), lastP=0;
function excludes(j,p,y) {
  const d=p-1-j, half=Math.floor(d/2), ip=1/p;
  if(lastP!==p || inv.length<=half) {
    inv=new Uint32Array(half+1);
    inv[1]=1;
    for(let i=2;i<=half;i++) inv[i]=p-Math.floor(p/i)*inv[p%i]%p;
    lastP=p;
  }
  const other=p-y;
  let v=1;
  for(let s=0;s<=half;s++) {
    if(d%2 ? v===y || v===other : v===(s%2 ? other : y)) return false;
    if(s<half) {
      // Quotient estimated by multiplying by a cached reciprocal. For
      // x<p²<2^53 its error is <1; the two comparisons make reduction exact.
      let x=v*(d-s);
      x-=Math.floor(x*ip)*p;
      if(x>=p) x-=p;
      if(x<0) x+=p;
      x*=inv[s+1];
      x-=Math.floor(x*ip)*p;
      if(x>=p) x-=p;
      if(x<0) x+=p;
      v=x;
    }
  }
  return true;
}
for(const p of [13,17,23,31]) for(let j=2;j<p;j++) {
  const image=new Set();
  let q=1n;
  for(let m=j;m<p;m++) {
    image.add(Number(q%BigInt(p)));
    q=q*BigInt(m+1)/BigInt(m+1-j);
  }
  for(let y=1;y<p;y++) assert.equal(excludes(j,p,y),!image.has(y));
}
let start=0,maxWitness=0;
for(let j=2;j<T;j++) {
  while(tests[start]<=j) ++start;
  let u=start;
  while(u<tests.length && !excludes(j,tests[u],residues[u])) ++u;
  assert(u<tests.length,`Unresolved column ${j}`);
  maxWitness=Math.max(maxWitness,tests[u]);
  if(j%250000===0) console.log('Excluded through column',j,
    `(${Math.round((Date.now()-started)/1000)} s)`);
}

function prime(p) {
  for(let i=2;i*i<=p;i++) if(p%i===0) return false;
  return true;
}
let first=N+1;
while(!prime(first)) ++first;
function localCover() {
  const upper=Number(maxRow), span=2000, stride=T-span;
  assert(Number.isSafeInteger(upper) && 2*span<T);
  const trial=[];
  let factors=[];
  for(let p=2;p<=Math.ceil(Math.sqrt(upper+span));p++) if(!composite[p]) {
    trial.push(p);
    factors.push(BigInt(p));
  }
  while(factors.length>1) factors=parent(factors);
  const primorial=factors[0];
  function candidate(start,stop) {
    for(let q=start+(start%2===0);q<=stop;q+=2) {
      if(q%3===0 || q%5===0 || q%7===0 || q%11===0 || q%13===0 ||
         q%17===0 || q%19===0 || q%23===0 || q%29===0 || q%31===0) continue;
      const b=BigInt(q);
      if(modPow(2n,b-1n,b)===1n) return q;
    }
    throw Error('No candidate prime in local cover interval');
  }
  function gcd(a,b) {
    while(b) [a,b]=[b,a%b];
    return a;
  }
  let previous=first, blocks=0, maxGap=0;
  for(let base=first;base<=upper;) {
    const starts=[],qs=[];
    while(base<=upper && qs.length<8192) {
      starts.push(base);
      qs.push(candidate(base,base+span-1));
      base+=stride;
    }
    // Compute the primorial modulo every candidate by a product/remainder
    // tree. Coprimality to all primes up to sqrt(upper+span) proves primality.
    const tree=[qs.map(BigInt)];
    while(tree.at(-1).length>1) tree.push(parent(tree.at(-1)));
    let rs=[primorial%tree.at(-1)[0]];
    for(let u=tree.length-2;u>=0;u--) rs=tree[u].map((p,i)=>rs[Math.floor(i/2)]%p);
    for(let i=0;i<qs.length;i++) {
      let q=qs[i];
      if(gcd(q,Number(rs[i]))!==1) {
        // Fermat was only a filter. Certify a replacement by trial division.
        do { q=candidate(q+1,starts[i]+span-1); } while(trial.some(p=>q%p===0));
      }
      assert(q>=starts[i] && q<starts[i]+span && q-previous<T);
      maxGap=Math.max(maxGap,q-previous);
      previous=q;
      blocks++;
    }
  }
  assert(upper-previous<T);
  return {blocks,maxGap};
}
const cover=local ? localCover() : {publishedGap:1476};
// For m>=first, choose the largest prime p<=m: p>=first>N and
// m-p<1476<T<=j<=m/2. Therefore p divides C(m,j), impossible.
// Every admissible row m has m>=bottom because bottom divides A.
// Walk the neighboring coefficients in each remaining row using exact ratios.
const hits=[];
for(let m=bottom;m<first;m++) {
  let x=1n,y=1n,j=K;
  for(let r=N;r<m;r++){x*=BigInt(r+1); y*=BigInt(r+1-K);}
  for(let r=N;r>m;r--){x*=BigInt(r-K); y*=BigInt(r);}
  if(x>y) {
    while(x>y && j>T) {x*=BigInt(j); y*=BigInt(m-j+1); j--;}
  } else {
    while(x<y && 2*(j+1)<=m) {x*=BigInt(m-j); y*=BigInt(j+1); j++;}
  }
  if(x===y) hits.push([m,j]);
}
assert.deepEqual(hits,[[N-1,K+1],[N,K]]);
console.log(JSON.stringify({N,K,digitCount,T,maxRow:String(maxRow),cover,maxWitness,bottom,first,
  hits,edge:1,multiplicity:hits.length+1}));
