// Check the low-column cases left by Blokhuis, Brouwer & de Weger, section 2.2.
// Run with Node. The searched value interval is (10^64, 10^100].
const assert = require('node:assert/strict');

function choose(n, k) {
  let value = 1n;
  for (let i = 1; i <= k; ++i)
    value = value * (n - BigInt(i - 1)) / BigInt(i);
  return value;
}

function lastRow(value, k) {
  let lo = BigInt(k), hi = 2n*lo;
  while (choose(hi, k) <= value) hi *= 2n;
  while (hi - lo > 1n) {
    const mid = (lo + hi) / 2n;
    if (choose(mid, k) <= value) lo = mid;
    else hi = mid;
  }
  return lo;
}

function inverse(a, modulus) {
  let r = modulus, s = a % modulus, u = 0n, v = 1n;
  while (s) {
    const q = r / s;
    [r, s] = [s, r % s];
    [u, v] = [v, u - q*v];
  }
  assert.equal(r, 1n);
  return (u % modulus + modulus) % modulus;
}

const primes = [];
for (let p = 11; p < 510; ++p)
  if (Array.from({length: Math.floor(Math.sqrt(p))-1}, (_, i) => i+2)
    .every(d => p % d !== 0)) primes.push(p);

// For p above every column, Lucas gives C(n,k) = C(n mod p,k) modulo p.
// Pascal addition keeps every intermediate residue below 2p.
function residueColumns(p, last) {
  const cols = Array.from({length: last+1}, () => new Uint16Array(p));
  cols[0].fill(1);
  for (let k=1; k<=last; ++k)
    for (let i=k; i<p; ++i) cols[k][i] = (cols[k][i-1]+cols[k-1][i-1]) % p;
  return cols;
}

function restrictions(pattern) {
  const l = pattern.at(-1);
  return primes.filter(p => p > l).map(p => {
    const cols = residueColumns(p,l);
    const images = pattern.slice(0,-1).map(k => new Set(cols[k]));
    const allowed = Uint8Array.from(cols[l], v => images.every(s => s.has(v)));
    const count = allowed.reduce((a,b) => a+b,0);
    return {p, allowed, count};
  });
}

// Construct all residues of x mod M for which scale*x passes each rule.
function wheel(rules, scale) {
  let M = 1, xs = Float64Array.of(0);
  for (const {p, allowed, count} of rules) {
    const inv = Number(inverse(BigInt(M),BigInt(p)));
    const digits = [];
    for (let i=0; i<p; ++i) if (allowed[((scale % p)*i) % p]) digits.push(i);
    assert.equal(digits.length, count);
    const next = new Float64Array(xs.length * count);
    assert(M*p < 2**50);
    let out = 0;
    for (const x of xs) {
      const r = x % p;
      for (const d of digits)
        next[out++] = x + M*(((d-r+p)*inv) % p);
    }
    xs = next;
    M *= p;
  }
  return {M,xs};
}

function lowerBound(sorted, x) {
  let lo = 0, hi = sorted.length;
  while (lo < hi) {
    const mid = (lo + hi) >>> 1;
    if (sorted[mid] < x) lo = mid+1; else hi = mid;
  }
  return lo;
}

// Join two independent sets of CRT residues inside the closed row interval.
function visitJoined(lo, hi, groups, visit) {
  const {M,xs} = wheel(groups[0],1);
  const {M:N,xs:ys} = wheel(groups[1],M);
  ys.sort();
  const bigN = BigInt(N), invM = inverse(BigInt(M),bigN);
  assert(BigInt(M)*bigN > BigInt(hi));
  for (const a of xs) {
    const t0 = Math.ceil((lo-a)/M), t1 = Math.floor((hi-a)/M);
    if (t0 > t1) continue;
    // m=a+M*t passes the second wheel iff (a/M + t) mod N is in ys.
    const shift = Number(BigInt(a)*invM % bigN);
    const start = (shift+t0) % N, end = start+t1-t0;
    for (let segment=0; segment<=(end >= N ? 1 : 0); ++segment) {
      const left = segment === 0 ? start : 0;
      const right = segment === 0 ? Math.min(end,N-1) : end-N;
      for (let i=lowerBound(ys,left); i<ys.length && ys[i]<=right; ++i) {
        const row = a + M*(t0 + (ys[i]-start) + segment*N);
        visit(row);
      }
    }
  }
}

function search(pattern, lowValue, highValue, capacity) {
  const l = pattern.at(-1);
  const lo = Math.max(2*l, Number(lastRow(lowValue,l)+1n));
  const hi = Number(lastRow(highValue,l));
  // All rows, lifted residues and integer products used as Numbers are exact.
  assert(hi < 2**50 && Number.isSafeInteger(hi));
  const hits = [];
  let joined = 0, exact = 0;
  if (lo > hi) return {pattern,lo,hi,joined,exact,hits};
  const all = restrictions(pattern);
  const efficiency = r => -Math.log(r.count/r.p)/Math.log(r.count);
  all.sort((a,b) => efficiency(b)-efficiency(a));
  const groups = [[],[]], sizes = [1,1], other = [];
  for (const r of all) {
    const g = sizes[0] <= sizes[1] ? 0 : 1;
    if (sizes[g]*r.count <= capacity) {
      sizes[g] *= r.count;
      groups[g].push(r);
    } else other.push(r);
  }
  other.sort((a,b) => a.count/a.p-b.count/b.p);
  visitJoined(lo, hi, groups, m => {
    ++joined;
    for (const rule of other) {
      if (!rule.allowed[m % rule.p]) return;
    }
    ++exact;
    assert(lo<=m && m<=hi);
    const value = choose(BigInt(m),l);
    assert(lowValue<value && value<=highValue);
    const rows = pattern.slice(0,-1).map(k => lastRow(value,k));
    if (rows.every((n,i) => n>=BigInt(2*pattern[i]) && choose(n,pattern[i])===value))
      hits.push({m,value:value.toString(),rows:rows.map(String)});
  });
  return {pattern,lo,hi,joined,exact,hits};
}

const classified = new Set(['2,3','2,4','2,5','2,6','2,8','3,4','3,6','4,6','4,8']);
const patterns = [];
for (let i=2;i<=9;++i) for (let j=i+1;j<=9;++j)
  for (let k=j+1;k<=9;++k) for (let l=k+1;l<=9;++l) {
    const group = [i,j,k,l];
    if (group.every((v,index) => group.slice(index+1).every(w => !classified.has([v,w].join(',')))))
      patterns.push(group);
  }
assert.equal(patterns.length,10);
// Exhaust a full period with a direct residue oracle, including empty,
// single-row and wrapping joins, and check that every retained row is unique.
const rules = restrictions([3,5,7,8]).slice(0,4);
const period = rules.reduce((m,r) => m*r.p,1);
for (const [lo,hi] of [[0,period-1],[31,31],[45,46],[period-100,period-1]]) {
  const directRows = [];
  for (let n=lo; n<=hi; ++n)
    if (rules.every(r => r.allowed[n % r.p])) directRows.push(n);
  const joinedRows = [];
  visitJoined(lo,hi,[rules.slice(0,2),rules.slice(2)],m=>joinedRows.push(m));
  assert.deepEqual(joinedRows.sort((a,b)=>a-b),directRows);
}
assert.deepEqual(search([2,5,6],3002n,3003n,2000).hits.map(h => h.m),[14]);
assert.deepEqual(search([2,5,6],3003n,3004n,2000).hits,[]);
// This wider control exercises cyclic interval joins as well as the known hits.
const direct = [];
for (let m=6;m<=120;++m) {
  const a = choose(BigInt(m),3), n = lastRow(a,2);
  if (choose(n,2)===a) direct.push(m);
}
assert.deepEqual(search([2,3],19n,choose(120n,3),300).hits.map(h=>h.m).sort((a,b)=>a-b),direct);
for (const pattern of patterns)
  console.log(JSON.stringify(search(pattern,10n**64n,10n**100n,1500000)));
