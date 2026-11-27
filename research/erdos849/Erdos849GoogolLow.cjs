// Exhaust all four-proper-column configurations with largest column <=9
// in 10^100 < value <= 10^105. No condition on factorization of the value.
// Run: node Erdos849GoogolLow.cjs       (--plan reports wheel sizes)
'use strict';
const assert=require('node:assert/strict');
const {search}=require('./Erdos849SixteenCrosscheck.cjs');
const low=10n**100n, high=10n**105n;

// Blokhuis, Brouwer & de Weger, Theorem 2.2, arXiv:1707.06893.
const classified=new Set(['2,3','2,4','2,5','2,6','2,8','3,4','3,6','4,6','4,8']);
const patterns=[];
for(let i=2;i<7;i++) for(let j=i+1;j<8;j++)
  for(let k=j+1;k<9;k++) for(let d=k+1;d<=9;d++) {
    const cols=[i,j,k,d];
    if(cols.every((v,a)=>cols.slice(a+1).every(w=>!classified.has(v+','+w))))
      patterns.push(cols);
  }
assert.equal(patterns.length,10);
assert.deepEqual([...new Set(patterns.map(c=>c[3]))].sort(),[8,9]);

// Independently certify the endpoint returned by the sieve using the
// falling product and k! * value, without binomial division or inversion.
function checkLast(row,k,value) {
  function numerator(n) {
    let prod=1n;
    for(let i=0;i<k;i++) prod*=n-BigInt(i);
    return prod;
  }
  const target=numerator(BigInt(k))*value;
  assert(numerator(BigInt(row))<=target && target<numerator(BigInt(row)+1n));
}

const planOnly=process.argv.includes('--plan');
const selected=new Set(process.argv.slice(2).filter(s=>/^\d+$/.test(s)).map(Number));
let totalJoined=0, totalExact=0, rowPatterns=0;
const start=Date.now();
for(const [index,cols] of patterns.entries()) {
  if(selected.size && !selected.has(index+1)) continue;
  const begin=Date.now();
  const out=search(cols,105,planOnly,low,high);
  checkLast(out.lo-1,cols[3],low);
  checkLast(out.hi,cols[3],high);
  rowPatterns+=out.hi-out.lo+1;
  if(!planOnly) {
    assert.deepEqual(out.hits,[]);
    totalJoined+=out.joined;
    totalExact+=out.exact;
  }
  console.log(JSON.stringify({index:index+1,cols,...out,seconds:(Date.now()-begin)/1000}));
}
if(!planOnly)
  console.log(JSON.stringify({rowPatterns,totalJoined,totalExact,seconds:(Date.now()-start)/1000}));
