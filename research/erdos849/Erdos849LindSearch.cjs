// Exact search of all half-triangle representations of later Lind coefficients.
// Run: node Erdos849LindSearch.cjs [family index, 3..8] (default 6).
const assert = require('node:assert/strict');
const { performance } = require('node:perf_hooks');

function primesThrough(limit) {
  const sieve = new Uint8Array(limit + 1).fill(1);
  for (let d = 2; d*d <= limit; d++) {
    if (sieve[d]) for (let m = d*d; m <= limit; m += d) sieve[m] = 0;
  }
  const primes = [];
  for (let p = 2; p <= limit; p++) if (sieve[p]) primes.push(p);
  return primes;
}

function isPrime(n, primes) {
  if (n < 2) return false;
  for (const p of primes) {
    if (p*p > n) return true;
    if (n % p === 0) return n === p;
  }
  throw Error('Trial divisor list too short');
}

function modPower(base, exponent, p) {
  let result = 1;
  while (exponent) {
    if (exponent % 2) result = result * base % p;
    base = base * base % p;
    exponent = Math.floor(exponent / 2);
  }
  return result;
}

function lucasResidue(n, k, p) {
  // Over the field of p elements (1+x)^p = 1+x^p. Expanding with the
  // base-p digits of n therefore gives the product of digit binomials.
  let numerator = 1, denominator = 1;
  while (k) {
    const a = n % p, b = k % p;
    if (b > a) return 0;
    for (let j = 1; j <= Math.min(b, a-b); j++) {
      numerator = numerator * (a-j+1) % p;
      denominator = denominator * j % p;
    }
    n = Math.floor(n/p);
    k = Math.floor(k/p);
  }
  return numerator * modPower(denominator, p-2, p) % p;
}

function excludesColumn(k, test) {
  const { p, residue, inverse } = test;
  assert(p > k && residue > 0);
  // Lucas reduces C(m,k) modulo p to C(m mod p,k). For a nonzero result,
  // m mod p = p-1-s, 0<=s<=d=p-1-k. Expanding the factors gives
  // C(p-1-s,k) = C(p-1-s,d-s) = (-1)^(d-s) C(d,s) modulo p.
  const d = p-1-k;
  for (let i = inverse.length; i <= Math.floor(d/2); i++) {
    inverse.push(p - Math.floor(p/i) * inverse[p%i] % p);
  }
  let value = 1;
  for (let s = 0; s <= Math.floor(d/2); s++) {
    // Check the signs for s and d-s using C(d,s) = C(d,d-s).
    if (((d-s)%2 ? p-value : value) === residue ||
        (s%2 ? p-value : value) === residue) return false;
    if (s < Math.floor(d/2)) value = (value * (d-s) % p) * inverse[s+1] % p;
  }
  return true;
}

function lowColumns(n, k, threshold) {
  const limit = threshold + Math.max(500, Math.ceil(threshold/8));
  assert(limit * limit < Number.MAX_SAFE_INTEGER);
  const tests = [];
  for (const p of primesThrough(limit)) {
    const residue = lucasResidue(n, k, p);
    if (residue) tests.push({ p, residue, inverse: [0, 1] });
  }
  let first = 0, largestPrime = 0, excluded = 0;
  const unresolved = [];
  for (let j = 2; j < threshold; j++) {
    while (first < tests.length && tests[first].p <= j) first++;
    // A successful witness excludes the entire column. A missed witness
    // leaves the column explicitly unresolved in the final result.
    const witness = tests.slice(first, first+40).find(test => excludesColumn(j, test));
    if (witness) {
      largestPrime = Math.max(largestPrime, witness.p);
      excluded++;
    } else {
      unresolved.push(j);
    }
  }
  return { excluded, unresolved, largestPrime };
}

function primeLadder(n, k, threshold) {
  // If C(m,j)=A with j>=t and 2j<=m, then (m/t)^t<=C(m,t)<=A<=2^n.
  const maxRow = threshold * 2**Math.ceil(n/threshold);
  assert(Number.isSafeInteger(maxRow));
  const primes = primesThrough(Math.ceil(Math.sqrt(2*maxRow)) + 100);
  let bottom = n;
  while (!isPrime(bottom, primes)) bottom--;
  assert(bottom > k && bottom > n-k); // bottom divides A, hence m>=bottom.
  let first = n+1;
  while (!isPrime(first, primes)) first++;
  let p = first, count = 1, maxGap = 0;
  while (p + threshold <= maxRow) {
    let next = p + threshold;
    while (!isPrime(next, primes)) next--;
    assert(next > p);
    maxGap = Math.max(maxGap, next-p);
    p = next;
    count++;
  }
  // For first<=m<=maxRow choose the last ladder prime P<=m. Then
  // m-P<t<=j, and P>m-j>=j. Hence P divides C(m,j), impossible since P>n.
  return { bottom, first, maxRow, count, maxGap };
}

function inspectRows(n, k, bottom, first, threshold) {
  let numerator = 1n, denominator = 1n;
  // Initialize C(bottom,k)/C(n,k) by exact consecutive-row identities.
  for (let m = n; m > bottom; m--) {
    numerator *= BigInt(m-k);
    denominator *= BigInt(m);
  }
  const hits = [];
  for (let m = bottom; m < first; m++) {
    assert(2*k <= m && threshold <= k);
    let j = k, u = numerator, v = denominator;
    // C(m,j) grows strictly up to the midpoint. Move to the nearest crossing.
    if (u < v) {
      while (u < v && j < Math.floor(m/2)) {
        u *= BigInt(m-j);
        v *= BigInt(j+1);
        j++;
      }
    } else {
      while (u > v && j > threshold) {
        u *= BigInt(j);
        v *= BigInt(m-j+1);
        j--;
      }
    }
    if (u === v) hits.push([m,j]);
    numerator *= BigInt(m+1);
    denominator *= BigInt(m+1-k);
  }
  return hits;
}

function search(index) {
  const fib = [0, 1];
  while (fib.length <= 2*index+3) fib.push(fib.at(-1) + fib.at(-2));
  const n = fib[2*index+2]*fib[2*index+3], k = fib[2*index]*fib[2*index+3];
  const threshold = Math.ceil(n/13);
  const start = performance.now();
  const low = lowColumns(n, k, threshold);
  const ladder = primeLadder(n, k, threshold);
  const hits = inspectRows(n, k, ladder.bottom, ladder.first, threshold);
  return { index, n, k, threshold, low, ladder, hits, seconds: (performance.now()-start)/1000 };
}

const index = Number(process.argv[2] ?? 6);
assert(Number.isInteger(index) && index >= 3 && index <= 8);
// Independently build each column of a small Pascal triangle by addition.
// Compare every residue, including modular witnesses for a true equality.
for (const p of [7, 13, 29, 43]) {
  const images = Array.from({length:p}, () => new Set([0]));
  let row = [1];
  for (let m = 0; m < p; m++) {
    for (let j = 0; j <= m; j++) {
      images[j].add(row[j]);
      assert.equal(lucasResidue(m,j,p), row[j]);
    }
    const next = [1];
    for (let j = 1; j <= m; j++) next.push((row[j-1]+row[j]) % p);
    next.push(1);
    row = next;
  }
  for (let j = 1; j < p; j++) {
    for (let residue = 1; residue < p; residue++) {
      assert.equal(excludesColumn(j, {p, residue, inverse:[0,1]}), !images[j].has(residue));
    }
  }
}
const result = search(index);
console.log(JSON.stringify(result));
if (result.low.unresolved.length === 0) {
  console.log(`Exact half-triangle multiplicity including the edge: ${result.hits.length+1}`);
}
