// Independent two-wheel CRT check for the eighteen cap-15 residual intervals.
// Run all with node Erdos849SixteenCrosscheck.cjs, or pass 1-based indices.
// --plan prints the parameters and expected intersection sizes without searching.
'use strict';
const assert = require('node:assert/strict');

const patterns = [
  [[3,5,8,9],111], [[3,5,7,15],179],
  [[3,5,7,12],144], [[4,5,7,12],144], [[5,6,7,12],144],
  [[3,5,7,13],134], [[4,5,7,13],134], [[5,6,7,13],134],
  [[3,5,7,11],104], [[4,5,7,11],104], [[5,6,7,11],104],
  [[3,5,7,14],121], [[4,5,7,14],121], [[5,6,7,14],121],
  [[2,7,14,15],101], [[3,5,14,15],101], [[3,7,14,15],101], [[5,7,14,15],101]
];

function binomial(n,k) {
  let value=1n;
  for (let i=0; i<k; i++) value=value*(n-BigInt(i))/BigInt(i+1);
  return value;
}

function lastRow(a,k) {
  let lo=BigInt(k-1), hi=BigInt(k);
  while (binomial(hi,k)<=a) hi*=2n;
  while (lo+1n<hi) {
    const mid=(lo+hi)/2n;
    if (binomial(mid,k)<=a) lo=mid; else hi=mid;
  }
  return lo;
}

function inverse(a,m) {
  let r=a,s=m,x=1n,y=0n;
  while (s>0n) {
    const q=r/s;
    [r,s]=[s,r-q*s];
    [x,y]=[y,x-q*y];
  }
  assert.equal(r,1n);
  return (x%m+m)%m;
}

// For prime p and p^v the coefficient sequence in all columns k<=d
// is periodic modulo p^v with period p^(v+floor(log_p d)): Vandermonde's
// identity and v_p(C(p^t,i))=t-v_p(i) for 0<i<=d prove this assertion.
function rulesFor(cols) {
  const d=cols.at(-1), rules=[];
  for (let p=2; p<400; p++) {
    let prime=true;
    for (let f=2; f*f<=p; f++) if (p%f===0) {prime=false; break;}
    if (!prime) continue;
    let factor=1;
    while (factor*p<=d) factor*=p;
    const choices=[];
    for (let mod=p; mod*factor<=16000; mod*=p) {
      const period=mod*factor;
      const residues=cols.map(()=>new Uint16Array(period));
      const row=new Uint16Array(d+1); row[0]=1;
      for (let n=0; n<period; n++) {
        for (let i=0; i<cols.length; i++) residues[i][n]=row[cols[i]];
        for (let k=d;k>0;k--) row[k]=(row[k]+row[k-1])%mod;
      }
      const allowedValues=residues.slice(0,-1).map(v=>new Set(v));
      const flags=Uint8Array.from(residues.at(-1),v=>allowedValues.every(s=>s.has(v)));
      const ids=[];
      for (let i=0;i<period;i++) if (flags[i]) ids.push(i);
      choices.push({p,period,flags,ids,score:-Math.log(ids.length/period)/Math.log(ids.length)});
    }
    rules.push(choices);
  }
  return rules;
}

function wheel(rules) {
  let period=1,rows=Float64Array.of(0);
  for (const rule of rules) {
    const next=new Float64Array(rows.length*rule.ids.length), m=rule.period;
    const inv=Number(inverse(BigInt(period),BigInt(m)));
    let count=0;
    assert(period*m<2**49);
    for (const a of rows) {
      const rem=a%m;
      for (const b of rule.ids) next[count++]=a+period*((b-rem+m)*inv%m);
    }
    period*=m; rows=next;
  }
  return {period,rows};
}

function lowerBound(xs,v) {
  let lo=0,hi=xs.length;
  while(lo<hi) {
    const mid=Math.floor((lo+hi)/2);
    if (xs[mid]<v) lo=mid+1; else hi=mid;
  }
  return lo;
}

function search(cols,K,planOnly,customLow,customHigh) {
  const d=cols.at(-1),low=customLow??10n**100n,high=customHigh??10n**BigInt(K);
  const lo=Number(lastRow(low,d)+1n),hi=Number(lastRow(high,d));
  assert(Number.isSafeInteger(hi) && hi<2**48 && lo>0);
  const rules=rulesFor(cols),groups=[[],[]],usage=[1,1],chosen=new Set(),periods=[1,1];
  const options=rules.flat().sort((a,b)=>b.score-a.score);
  const capacity=1500000;
  for (const r of options) {
    if (chosen.has(r.p)) continue;
    const side=usage[0]<=usage[1]?0:1;
    if (usage[side]*r.ids.length>capacity || periods[side]*r.period>=2**49) continue;
    chosen.add(r.p); groups[side].push(r); usage[side]*=r.ids.length; periods[side]*=r.period;
  }
  const expected=(hi-lo+1)*(usage[0]/periods[0])*(usage[1]/periods[1]);
  if (planOnly) return {lo,hi,usage,periods,expected:Math.ceil(expected)};
  const left=wheel(groups[0]),right=wheel(groups[1]),M=left.period,N=right.period;
  assert(BigInt(M)*BigInt(N)>BigInt(hi));
  const bigN=BigInt(N),invM=inverse(BigInt(M),bigN);
  // t=(row-a)/M. The second wheel admits t iff t + a/M is in B/M mod N.
  const rightQuotient=Float64Array.from(right.rows,b=>Number(BigInt(b)*invM%bigN)).sort();
  const filters=rules.map(rs=>rs.at(-1)).sort((a,b)=>a.ids.length/a.period-b.ids.length/b.period);
  let joined=0,exact=0;
  const hits=[];
  for (const a of left.rows) {
    const t0=Math.ceil((lo-a)/M),t1=Math.floor((hi-a)/M);
    // Confirm division returned both exact integer endpoints, including when
    // this residue class misses the interval. The products here are exact.
    assert(a+M*t0>=lo && a+M*(t0-1)<lo);
    assert(a+M*t1<=hi && a+M*(t1+1)>hi);
    if (t1<t0) continue;
    const shift=Number(BigInt(a)*invM%bigN);
    let start=(shift+t0)%N;
    if (start<0) start+=N;
    const length=t1-t0+1;
    assert(length<=N);
    for (const [first,last,delta] of [[start,Math.min(N,start+length),0],[0,start+length-N,N]]) {
      if (last<=first) continue;
      for (let i=lowerBound(rightQuotient,first);i<rightQuotient.length&&rightQuotient[i]<last;i++) {
        joined++;
        const t=t0+(rightQuotient[i]-start+delta);
        const n=a+M*t;
        assert(n>=lo && n<=hi);
        if (!filters.every(r=>r.flags[n%r.period])) continue;
        exact++;
        const v=binomial(BigInt(n),d);
        assert(v>low && v<=high);
        if(cols.slice(0,-1).every(k=>binomial(lastRow(v,k),k)===v)) hits.push(n);
      }
    }
  }
  return {lo,hi,joined,exact,hits};
}

if(require.main===module) {
  const planOnly=process.argv.includes('--plan');
  const selected=new Set(process.argv.slice(2).filter(v=>/^\d+$/.test(v)).map(Number));
  if (!planOnly) {
    assert.deepEqual(search([2,5,6],0,false,2999n,3005n).hits,[14]);
    const direct=[];
    for(let n=6;n<=200;n++) {
      const a=binomial(BigInt(n),3);
      if(binomial(lastRow(a,2),2)===a) direct.push(n);
    }
    const small=search([2,3],0,false,19n,binomial(200n,3)).hits;
    assert.deepEqual(small.sort((x,y)=>x-y),direct);
  }
  for(let i=0;i<patterns.length;i++) {
    if(selected.size && !selected.has(i+1)) continue;
    const [cols,K]=patterns[i],start=Date.now();
    const result=search(cols,K,planOnly);
    console.log(JSON.stringify({index:i+1,cols,K,...result,seconds:(Date.now()-start)/1000}));
    if (!planOnly) assert.deepEqual(result.hits,[]);
  }
}

module.exports={patterns,search};
