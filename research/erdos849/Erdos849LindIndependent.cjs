// Independent exact verifier for the sixth, seventh, and eighth Lind values.
// Run with Node: node Erdos849LindIndependent.cjs 8
// It constructs A by Legendre factorization, distributes modular residues via
// a product tree, and searches the surviving high rows in a second prime field.
const assert = require('node:assert/strict');
const started = Date.now();
const targets = {6:[229970,87840], 7:[1576239,602069], 8:[10803704,4126647]};
const index = Number(process.argv[2] ?? 8);
assert(Object.hasOwn(targets,index));
const [N,K] = targets[index];
const T = Math.ceil(N/13), maxRow = T*8192;
const sieve = new Uint8Array(N+1);
for (let p=2; p*p<=N; p++) {
  if (!sieve[p]) for (let m=p*p; m<=N; m+=p) sieve[m]=1;
}
const primes = [];
for (let p=2; p<=N; p++) if (!sieve[p]) primes.push(p);

function exponent(n, k, p) {
  let a=n, b=k, c=n-k, e=0;
  while (a>=p) {
    a=Math.floor(a/p); b=Math.floor(b/p); c=Math.floor(c/p);
    e+=a-b-c;
  }
  return e;
}

function parents(level) {
  const result = [];
  for (let i=0;i<level.length;i+=2) result.push(level[i]*(level[i+1] ?? 1n));
  return result;
}

const valuations = Uint8Array.from(primes, p => exponent(N,K,p));
let factors = primes.flatMap((p,i) => valuations[i] ? [BigInt(p)**BigInt(valuations[i])] : []);
while (factors.length>1) factors=parents(factors);
const A = factors[0];
const digitCount = A.toString().length;
const verifyPrimes = primes.filter((p,i) => p<T+Math.max(500,Math.ceil(T/8)) && !valuations[i]);
const levels = [verifyPrimes.map(BigInt)];
while (levels.at(-1).length>1) levels.push(parents(levels.at(-1)));
let remainders = [A%levels.at(-1)[0]];
for (let i=levels.length-2;i>=0;i--) {
  remainders=levels[i].map((modulus,j) => remainders[Math.floor(j/2)]%modulus);
}
const tests = verifyPrimes.map((p,i) => ({p, residue:Number(remainders[i]), inv:[0,1]}));

function lowColumnExcluded(column, {p,residue,inv}) {
  assert(p>column && residue!==0);
  // Since column! is invertible mod p, C(m,column) depends on m mod p.
  // Residues m<column give zero. Build the remaining values by stepping
  // forward through m=column,...,p-1 via C(m+1,k)=C(m,k)(m+1)/(m+1-k).
  const span=p-1-column;
  for (let i=inv.length;i<=span;i++) inv.push(p-Math.floor(p/i)*inv[p%i]%p);
  let v=1;
  for (let s=0;s<=span;s++) {
    if (v===residue) return false;
    if (s<span) v=(v*(column+s+1)%p)*inv[s+1]%p;
  }
  return true;
}

assert(tests.at(-1).p**2<Number.MAX_SAFE_INTEGER);
let first=0, highestWitness=0;
for (let column=2;column<T;column++) {
  while (tests[first].p<=column) first++;
  let j=first;
  while (j<tests.length && !lowColumnExcluded(column,tests[j])) j++;
  assert(j<tests.length, `missing exclusion for column ${column}`);
  highestWitness=Math.max(highestWitness, tests[j].p);
}

function primeAtOrAfter(n) {
  for (let m=n;;m++) {
    let prime=true;
    for (const p of primes) {
      if (p*p>m) break;
      if (m%p===0) {prime=false;break;}
    }
    if (prime) return m;
  }
}

const bottom=primes[primes.length-1];
assert(valuations.at(-1)>0); // a prime divisor of A gives m>=bottom.
const end=primeAtOrAfter(N+1);
const stride=Math.floor(T/2);
let blocks=0;
// For a column j>=T on the left, C(m,j)>=C(m,T)>=(m/T)^T.
// Since A<=2^N and N<=13T, m<=T*2^13. Each block below contains a
// certified prime >N. Gaps between selected primes are strictly <T, so a
// prime in (m-j,m] greater than j would divide C(m,j) whenever m>=end.
assert(primes.at(-1)**2>maxRow+stride);
for (let left=end;left<=maxRow;left+=stride) {
  const p=primeAtOrAfter(left);
  assert(p<left+stride);
  blocks++;
}

// For each of the remaining rows, first test every high column modulo a
// prime greater than the row. Confirm every modular hit by comparing the
// complete lists of prime exponents. All rows here are below end, the first
// prime after N, so the existing prime table is sufficient.
const q=end, desired=Number(A%BigInt(q));
assert(q*q<Number.MAX_SAFE_INTEGER);
const inverse=new Uint32Array(Math.floor((end-1)/2)+1);
inverse[1]=1;
for (let i=2;i<inverse.length;i++) inverse[i]=q-Math.floor(q/i)*inverse[q%i]%q;
let modularHits=0;
const hits=[];
for (let m=bottom;m<end;m++) {
  let v=1;
  for (let j=1;2*j<=m;j++) {
    v=(v*(m-j+1)%q)*inverse[j]%q;
    if (j>=T && v===desired) {
      modularHits++;
      if (primes.every((p,i)=>exponent(m,j,p)===valuations[i])) hits.push([m,j]);
    }
  }
}
assert.deepEqual(hits,[[N-1,K+1],[N,K]]);
console.log(JSON.stringify({index,N,K,digitCount,lowExcluded:T-2,highestWitness,
  maxRow,blocks,bottom,end,modularHits,hits,halfMultiplicity:hits.length+1,
  seconds:(Date.now()-started)/1000}));
