method GetEven(x: array<int>) modifies x
requires x.Length>= 0 && forall j:int | 0<=j<x.Length :: x[j]>=0
ensures forall n:int | 0<=n<x.Length :: old(x[n])%2 == 1 ==> x[n] == old(x[n])+1
ensures forall n:int | 0<=n<x.Length :: old(x[n])%2 == 0 ==> x[n] == old(x[n])
ensures forall n:int :: 0<=n<x.Length ==> (x[n]%2 == 0)
{
    var i:int := 0;
    while i < x.Length
    invariant 0<=i<=x.Length 
    invariant forall y:int :: i<=y<x.Length ==> x[y]==old(x[y]) 
    invariant forall y:int :: 0<=y<i ==> if old(x[y])%2==1 then x[y]== old(x[y])+1 else x[y] == old(x[y])
    decreases x.Length - i
    {
        if x[i] % 2 == 1
        {
            x[i] := x[i] + 1;
        }
        i := i + 1; 
    }
}

