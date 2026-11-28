"use strict";

// Enumerate all first-row ties in a prescribed shift rectangle. The integer
// determinant bound in the proof supplies the endpoint for the first row.
const assert = require("node:assert/strict");
const SCALE = 2 ** 24;

function slope(h, v) {
  const s = BigInt(SCALE);
  let lo = 0, hi = SCALE;
  while (hi - lo > 1) {
    const m = Math.floor((lo + hi) / 2), b = BigInt(m);
    if (s ** BigInt(h) * b ** BigInt(v) < (s-b) ** BigInt(h+v)) lo = m;
    else hi = m;
  }
  return [lo,hi];
}

function products(p, width) {
  const rows = [new Uint32Array(p).fill(1)];
  for (let i=1; i<=width; ++i) {
    const row = new Uint32Array(p), previous = rows[i-1];
    for (let n=0; n<p; ++n) row[n] = previous[n] * ((n+i)%p) % p;
    rows.push(row);
  }
  return rows;
}

function residueTest(p, rows, h, v) {
  return (n,k) => rows[h][n%p] * rows[v][(k-v+p)%p] % p
                 === rows[h+v][(n-k+p)%p];
}

function nextHit(p, test) {
  const jumps = new Uint16Array(p*p);
  for (let n=0; n<p; ++n) {
    let distance = p+1;
    for (let k=2*p-1; k>=0; --k) {
      distance = test(n,k%p) ? 0 : Math.min(distance+1,p+1);
      if (k<p) jumps[n*p+k] = distance;
    }
  }
  return jumps;
}

function exact(n,k,h,v) {
  let left = 1n, right = 1n;
  for (let i=1; i<=h; ++i) left *= BigInt(n+i);
  for (let i=0; i<v; ++i) left *= BigInt(k-i);
  for (let i=1; i<=h+v; ++i) right *= BigInt(n-k+i);
  return left === right;
}

function certify(rowSpan, colSpan, focus) {
  const p=251, q=65521, width=rowSpan+colSpan;
  const G = Math.max(rowSpan,colSpan);
  let end = 30*G**3;
  if (rowSpan>=colSpan) {
    let b=0;
    while (2**b<rowSpan+2) ++b;
    const e=(rowSpan+1)*(colSpan*b+1)+7*rowSpan*colSpan;
    end=Math.min(end, Math.max(30*G**2,3*rowSpan*e));
  }
  assert(width < p && end*SCALE < Number.MAX_SAFE_INTEGER);
  const a=products(p,width), b=products(q,width);
  const ties=new Map();
  for (const [h,v] of focus) {
    const [lower,upper] = slope(h,v);
    const jumps = nextHit(p,residueTest(p,a,h,v)), filter = residueTest(q,b,h,v);
    for (let n=2*(v+1); n<end; ++n) {
      const floor = Math.max(v+1,Math.floor(lower*n/SCALE)-h);
      const ceil = Math.min(Math.floor(n/2),Math.ceil(upper*n/SCALE)+h+v);
      assert(ceil-floor<p);
      const row=(n%p)*p;
      for (let k=floor; k<=ceil; ++k) {
        k += jumps[row+k%p];
        if (k<=ceil && filter(n,k) && exact(n,k,h,v)) {
          const key=n*(end+1)+k;
          assert(Number.isSafeInteger(key));
          if (!ties.has(key)) ties.set(key,{n,k,moves:[]});
          ties.get(key).moves.push([h,v]);
        }
      }
    }
  }
  const triples=[];
  for (const {n,k,moves} of ties.values()) {
    for (const [h,v] of moves) {
      for (const [H,V] of moves) if (h<H && v<V)
        triples.push([[n,k],[n+h,k-v],[n+H,k-V]]);
    }
  }
  return triples;
}

function box(rowSpan,colSpan) {
  const shifts=[];
  for (let h=1; h<=rowSpan; ++h)
    for (let v=1; v<=colSpan; ++v) shifts.push([h,v]);
  return certify(rowSpan,colSpan,shifts);
}

if (require.main===module) {
  const cases=[
    [24,24,[]],
    [64,4,[[[14,6],[15,5],[78,2]]]],
    [110,2,[[[10,3],[16,2],[120,1]]]]
  ];
  for (const [h,v,expected] of cases) {
    const result=box(h,v);
    assert.deepEqual(result,expected);
    console.log("Row and column spans",h,v,"give",JSON.stringify(result));
  }
}
