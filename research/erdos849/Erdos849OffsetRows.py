"""Search binomial rows in translated intervals using the existing CRT kernel."""

import argparse
import ctypes as ct
from math import comb,log
import os
from pathlib import Path
import shutil
import subprocess
from tempfile import TemporaryDirectory

from Erdos849FocusedCRT import check_join,configure,rules
from Erdos849SignedCRT import intersect
from Erdos849Wheel import max_row


def images(columns):
    chosen={}
    for rule in rules(columns):
        if 0<len(rule.ids)<rule.period:
            score=-log(rule.density)/log(max(2,len(rule.ids)))
            if rule.p not in chosen or score>chosen[rule.p][0]:
                chosen[rule.p]=score,rule
    return [(rule.period,set(rule.ids)) for _,rule in chosen.values()]


def interval(kernel,columns,low,high):
    k=columns[-1]
    lo=max(2*k,max_row(low,k)+1)
    hi=max_row(high,k)
    assert low<comb(lo,k) and comb(hi,k)<=high<comb(hi+1,k)
    if lo>2*k:assert comb(lo-1,k)<=low
    masks=images(columns)
    totals=[0,0,0]
    found=[]
    for start in range(lo,hi+1,2**62-1):
        end=min(hi,start+2**62-2)
        hits,counts=intersect(kernel,start,end,masks,1500000,128)
        totals=[x+y for x,y in zip(totals,counts)]
        for n in hits:
            value=comb(n,k)
            if all((m:=max_row(value,j)) >= 2*j and comb(m,j)==value for j in columns[:-1]):
                found.append(n)
    print(columns,lo,hi,hi-lo+1,totals,found,flush=True)
    return found


def main():
    if not __debug__:raise RuntimeError('Enable assertions.')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--columns',type=int,nargs='+',required=True)
    parser.add_argument('--lower',type=int,required=True)
    parser.add_argument('--upper',type=int,required=True)
    parser.add_argument('--cc')
    args=parser.parse_args()
    assert args.columns==sorted(set(args.columns)) and len(args.columns)>1 and args.columns[0]>0
    assert args.lower<args.upper
    cc=args.cc or shutil.which('clang') or shutil.which('cc')
    if not cc:parser.error('Supply a C compiler.')
    with TemporaryDirectory(ignore_cleanup_errors=True) as work:
        path=Path(work)/('rows.dll' if os.name=='nt' else 'rows.so')
        flags=['-nostdlib','-fuse-ld=lld'] if os.name=='nt' else ['-fPIC']
        subprocess.run([cc,'-O3','-shared',*flags,'-o',str(path),
                        str(Path(__file__).with_name('Erdos849FocusedCRT.c'))],check=True)
        kernel=ct.CDLL(str(path))
        configure(kernel)
        check_join(kernel)
        large=2**93+12345
        masks=[(13,{0,1,5,10}),(17,{3,7,9}),(23,{0,3,4,11})]
        actual,_=intersect(kernel,large,large+10327,masks)
        assert actual==[n for n in range(large,large+10328) if all(n%p in a for p,a in masks)]
        assert interval(kernel,[1,2,5,6],2999,3020)==[14]
        assert not interval(kernel,args.columns,10**args.lower,10**args.upper)
        if os.name=='nt':
            import _ctypes
            _ctypes.FreeLibrary(kernel._handle)


if __name__=='__main__':main()
