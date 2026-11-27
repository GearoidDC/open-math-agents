// Exclude shallow columns of Lind coefficients by Lucas residues and
// polynomial gcds. Emit a replayable table with --certificate FILE.
const fs = require('node:fs');
const assert = require('node:assert/strict');
const { parseArgs } = require('node:util');

function pow(a, n, p) {
  let v = 1;
  while (n) {
    if (n % 2) v = v*a % p;
    a = a*a % p;
    n = Math.floor(n/2);
  }
  return v;
}

function primes(limit) {
  const composite = new Uint8Array(limit+1);
  for (let i=2; i*i<=limit; ++i)
    if (!composite[i]) for (let j=i*i;j<=limit;j+=i) composite[j]=1;
  return (function* () {
    for (let i=2;i<=limit;++i) if (!composite[i]) yield i;
  })();
}

function trim(a) {
  while (a.length && !a.at(-1)) a.pop();
  return a;
}

function modPoly(a,b,p) {
  const d=b.length-1;
  const inverse = b[d]===1 ? 1 : pow(b[d],p-2,p);
  for (let i=a.length-1;i>=d;i--) {
    const t=(a[i]*inverse)%p;
    if (t) for(let j=0;j<d;j++) {
      const v = (a[i-d+j]-t*b[j])%p;
      a[i-d+j] = v<0 ? v+p : v;
    }
  }
  a.length=Math.min(a.length,d);
  return trim(a);
}

function mulMod(a,b,f,p) {
  if (!a.length || !b.length) return [];
  const c=new Array(a.length+b.length-1).fill(0);
  for(let i=0;i<a.length;i++) {
    if (!a[i]) continue;
    for(let j=0;j<b.length;j++) c[i+j]=(c[i+j]+a[i]*b[j])%p;
  }
  return modPoly(c,f,p);
}

function polynomial(j,y,p) {
  let f=[1], fac=1;
  for (let u=0;u<j;u++) {
    let g=new Array(f.length+1).fill(0);
    for(let i=0;i<f.length;i++) {
      g[i]=(g[i]+(p-u)*f[i])%p;
      g[i+1]=f[i];
    }
    f=g;
    fac=fac*(u+1)%p;
  }
  f[0]=(p-fac*y%p)%p;
  return f;
}

function hasRoot(j,y,p) {
  // Since j<p, f(X)=(X)_j-j!y represents zero precisely at rows
  // with C(row,j)=y mod p. X^p-X has each field element as a simple root.
  if (j===2) {
    const z=(1+8*y)%p;
    return z===0 || pow(z,(p-1)/2,p)===1;
  }
  let f=polynomial(j,y,p), u=[1], v=[0,1], e=p;
  while(e) {
    if(e%2) u=mulMod(u,v,f,p);
    e=Math.floor(e/2);
    if(e) v=mulMod(v,v,f,p);
  }
  while(u.length<2) u.push(0);
  u[1]=(u[1]+p-1)%p;
  trim(u);
  while(u.length) [f,u]=[u,modPoly(f,u,p)];
  return f.length>1;
}

function family(last,columns,triangular) {
  let a=4n,b=6n;
  const out=[];
  for(let i=1;i<=Math.max(last,triangular);i++) {
    const n=2n*a+b, k=a+2n;
    if (i>=9) {
      const upper=i<=last ? columns : 2;
      out.push({i,n,k,prime:new Array(upper-1).fill(0)});
    }
    [a,b]=[5n*a+3n*b, 3n*a+2n*b+3n];
  }
  return out;
}

function digits(n,k,p) {
  const out=[];
  while(k) {
    const a=Number(n%p), b=Number(k%p);
    if(b>a) return null;
    if (b && b<a) out.push([a,b]);
    n/=p; k/=p;
  }
  return out;
}

function lucasBatch(fits,p) {
  const points=new Set([0]);
  for (const [,ds] of fits) for (const [a,b] of ds)
    for (const v of [a,b,a-b]) points.add(v);
  const vals=new Map();
  let u=0, f=1;
  for (const t of [...points].sort((a,b)=>a-b)) {
    while(u<t) f=f*(++u)%p;
    vals.set(t,f);
  }
  return fits.map(([row,ds]) => {
    let num=1,den=1;
    for (const [a,b] of ds) {
      num=num*vals.get(a)%p;
      den=(den*vals.get(b)%p)*vals.get(a-b)%p;
    }
    return [row,num*pow(den,p-2,p)%p];
  });
}

function selfTest() {
  // Direct Pascal additions test both polynomial and triangular criteria.
  for (const p of primes(53)) {
    if (p<3) continue;
    const images=Array.from({length:p},()=>new Set([0]));
    let row=[1];
    for(let m=0;m<p;m++) {
      for(let j=0;j<=m;j++) images[j].add(row[j]);
      row=Array.from({length:m+2},(_,i)=>((row[i]||0)+(row[i-1]||0))%p);
    }
    for(let j=2;j<Math.min(p,17);j++) for(let y=0;y<p;y++)
      assert.equal(hasRoot(j,y,p),images[j].has(y));
    const fit=digits(14n,6n,BigInt(p));
    const value=fit ? lucasBatch([[0,fit]],p)[0][1] : 0;
    assert.equal(value,3003%p);
    if (p>6) for (const j of [2,5,6]) assert(hasRoot(j,value,p));
  }
}

const {values:args}=parseArgs({options:{
  last:{type:'string',default:'80'},columns:{type:'string',default:'32'},
  triangular:{type:'string',default:'120'},limit:{type:'string',default:'3000000'},
  certificate:{type:'string'},verify:{type:'string'},
}});
selfTest();

if (args.verify) {
  const data=JSON.parse(fs.readFileSync(args.verify,'utf8'));
  const rows=family(data.last,data.columns,data.triangular);
  assert.equal(rows.length,data.primes.length);
  const batches=new Map();
  for(let i=0;i<rows.length;i++) {
    const row=rows[i], cert=data.primes[i];
    assert.equal(cert.length,row.prime.length);
    for(let j=0;j<cert.length;j++) {
      const p=cert[j];
      assert(Number.isSafeInteger(p) && p>j+2 && p<=data.limit);
      if(!batches.has(p)) batches.set(p,new Map());
      const targets=batches.get(p);
      if(!targets.has(row)) targets.set(row,[]);
      targets.get(row).push(j+2);
    }
  }
  for (const p of primes(data.limit)) {
    const targets=batches.get(p);
    if(!targets) continue;
    const fits=[...targets.keys()].map(row=>[row,digits(row.n,row.k,BigInt(p))]);
    assert(fits.every(([,ds])=>ds!==null));
    for(const [row,y] of lucasBatch(fits,p))
      for(const j of targets.get(row)) assert(!hasRoot(j,y,p));
    batches.delete(p);
  }
  assert.equal(batches.size,0);
  console.log('Verified every prime, Lucas residue and column exclusion.');
} else {
  const [last,columns,triangular,limit]=[args.last,args.columns,args.triangular,args.limit].map(Number);
  assert([last,columns,triangular,limit].every(Number.isSafeInteger));
  assert(last>=9 && columns>=2 && limit<=90000000 && limit>columns);
  const rows=family(last,columns,triangular);
  let pending=rows.slice(), largest=0;
  for(const p of primes(limit)) {
    if(p<=2) continue;
    const big=BigInt(p), fits=[];
    for(const row of pending) {
      const ds=digits(row.n,row.k,big);
      if(ds) fits.push([row,ds]);
    }
    if(!fits.length) continue;
    for(const [row,y] of lucasBatch(fits,p)) {
      for(let u=0;u<row.prime.length && u+2<p;u++)
        if(!row.prime[u] && !hasRoot(u+2,y,p)) {
          row.prime[u]=p;
          largest=p;
        }
    }
    pending=pending.filter(row=>row.prime.includes(0));
    if(!pending.length) break;
  }
  const missing=pending.map(row=>[row.i,row.prime.flatMap((p,u)=>p?[]:[u+2])]);
  console.log(JSON.stringify({last,columns,triangular,largest,missing,
    certified:rows.reduce((s,r)=>s+r.prime.filter(Boolean).length,0)}));
  if(args.certificate && !missing.length)
    fs.writeFileSync(args.certificate,JSON.stringify({last,columns,triangular,limit:largest,
      primes:rows.map(row=>row.prime)})+'\n');
}
