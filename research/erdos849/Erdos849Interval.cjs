// Exhaust every collision between distinct columns >=7 in (10^60, 10^64].
// The fixed-column classifications in Blokhuis, Brouwer & de Weger, Thm 2.2,
// make such a collision necessary for five admissible rows in this interval.
const assert = require('node:assert/strict');

function choose(n, k) {
  assert(Number.isSafeInteger(n) && Number.isSafeInteger(k) && n >= k);
  let value = 1n;
  for (let i = 1; i <= k; ++i) {
    value = value * BigInt(n - i + 1) / BigInt(i);
  }
  return value;
}

// The final n satisfying C(n,k) <= bound, in the full range n >= k.
function lastRow(bound, k) {
  let lo = k, hi = 2*k;
  while (choose(hi, k) <= bound) hi *= 2;
  while (hi - lo > 1) {
    const mid = Math.floor((lo + hi) / 2);
    if (choose(mid, k) <= bound) lo = mid;
    else hi = mid;
  }
  assert(choose(lo, k) <= bound && bound < choose(lo + 1, k));
  return lo;
}

// Pascal addition computes C(r,k) mod p for every residue r. We only use
// k<p, so Lucas's theorem reduces every natural row to exactly one residue.
function residueTable(p, maxColumn) {
  const columns = Array.from({length: maxColumn + 1}, () => new Uint16Array(p));
  columns[0].fill(1);
  for (let k = 1; k <= maxColumn; ++k) {
    for (let r = k; r < p; ++r) {
      columns[k][r] = (columns[k][r-1] + columns[k-1][r-1]) % p;
    }
  }
  const images = columns.map(column => {
    const image = new Uint8Array(p);
    for (const v of column) image[v] = 1;
    return image;
  });
  return {p, columns, images};
}

function prime(p) {
  for (let d = 2; d*d <= p; ++d) if (p % d === 0) return false;
  return p >= 2;
}

function sieveRules(k, l, tables) {
  return tables.map(({p, columns, images}) => {
    const keep = Uint8Array.from(columns[l], value => images[k][value]);
    return {p, keep, fraction: keep.reduce((a,b) => a+b, 0) / p};
  }).sort((a,b) => a.fraction - b.fraction);
}

function deepCollisions(lower, upper) {
  let maxColumn = 7;
  while (choose(2*(maxColumn+1), maxColumn+1) <= upper) ++maxColumn;
  const ranges = [];
  for (let k = 7; k <= maxColumn; ++k) {
    ranges[k] = [Math.max(2*k, lastRow(lower, k)+1), lastRow(upper, k)];
  }
  const tables = [];
  for (let p = maxColumn+1; tables.length < 26; ++p) {
    if (prime(p)) tables.push(residueTable(p, maxColumn));
  }
  const hits = [];
  let columnPairs = 0, rowTests = 0, exactTests = 0;
  for (let l = 8; l <= maxColumn; ++l) {
    const [first, last] = ranges[l];
    for (let k = 7; k < l; ++k) {
      ++columnPairs;
      if (last < first || ranges[k][0] > ranges[k][1]) continue;
      const rules = sieveRules(k, l, tables);
      rowTests += last - first + 1;
      for (let m = first; m <= last; ++m) {
        let possible = true;
        for (const rule of rules) {
          if (!rule.keep[m % rule.p]) {
            possible = false;
            break;
          }
        }
        if (!possible) continue;
        ++exactTests;
        const value = choose(m, l);
        const n = lastRow(value, k);
        if (n >= 2*k && choose(n, k) === value) hits.push([n,k,m,l]);
      }
    }
  }
  return {maxColumn, columnPairs, rowTests, exactTests, hits};
}

// An endpoint-sensitive positive control from the Lind–Singmaster family.
const example = choose(104,39);
assert.deepEqual(deepCollisions(example-1n, example).hits, [[104,39,103,40]]);
assert.deepEqual(deepCollisions(example, example+1n).hits, []);
const result = deepCollisions(10n**60n, 10n**64n);
console.log(JSON.stringify(result, null, 2));
