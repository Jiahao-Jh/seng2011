
predicate sortedarray(c:array<char>, m:nat, n:nat)
reads c
requires 0<=m<=n<=c.Length
{ forall j,k:: m<=j<k<n ==> c[j]<=c[k] }



method ShuffleSort(a: array<char>) returns (b: array<char>)
ensures b.Length == a.Length
ensures sortedarray(b, 0, b.Length)
ensures multiset(b[..]) == multiset(a[..]);
{ 
    b := new char[a.Length];
    var i:int := 0;
    while (i < a.Length)
    invariant 0<=i<=a.Length ;
    invariant forall x ::  0 <= x < i ==> a[x] == b[x];
    invariant multiset(b[0..i]) == multiset(a[0..i]);
    {
        b[i] := a[i];
        i := i + 1;
    }
    assert b[..b.Length] == b[..];
    assert a[..a.Length] == a[..];
    assert multiset(b[..]) == multiset(a[..]);
    if (b.Length <= 1){
        return b;
    }
    assert b.Length > 1;

    var up := 1;
    while (up < b.Length)
    invariant b.Length == a.Length
    invariant 1 <= up <= b.Length;
    invariant sortedarray(b, 0, up);
    invariant multiset(b[..]) == multiset(a[..]);
    { 
        var curr := up-1;
        var tmp := b[up];
        b[up] := b[curr];
        while (curr >= 0 && tmp < b[curr])
        invariant b.Length == a.Length
        invariant -1<= curr < b.Length;
        invariant forall k:: curr < k < up ==> b[k]>tmp
        invariant sortedarray(b, 0, up+1);
        invariant multiset(b[..]) == multiset(a[..]) - multiset{tmp} + multiset{b[curr+1]};
        { 
            b[curr+1] := b[curr];
            curr := curr-1;

        }

        assert multiset(a[..])  == multiset(b[..])  + multiset{tmp} - multiset{b[curr+1]};
        b[curr+1] := tmp;
        up := up+1;
        
    }


}


method Main()
{
    var a := new char[5]['e','d','c','b','a'];
    assert a[0]=='e' && a[1]=='d' && a[2]=='c' && a[3]=='b' && a[4]=='a';
    var b := ShuffleSort(a);
    assert sortedarray(b, 0, b.Length);
    assert multiset(b[..]) == multiset(a[..]);

}
