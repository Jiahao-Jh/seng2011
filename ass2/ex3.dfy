method StringSwap(s: string, i:nat, j:nat) returns (t: string)
ensures i == old(i)
ensures j == old(j)
ensures |s| == |t|
ensures multiset(t[..]) == multiset(s[..]);
ensures  forall x :: 0 <= x < |s| && x!= i && x !=j ==> t[x] == s[x];
ensures  0<=i <|s|  && 0<=j < |s| ==> t[i] == s[j];
ensures  0<=i <|s|  && 0<=j < |s| ==> t[j] == s[i];
{
    var tmp:string;
    t := s;
    if ( 0<=i <|s|  && 0<=j < |s|){
        var k:char := s[i];
        t := s[i := s[j]];
        t := t[j := k];
    }

}

predicate sorted(a: string, low:int, high:int)
requires 0<=low<=high<=|a|
{ forall j,k:: low<=j<k<high ==> a[j]<=a[k] }

predicate sortedbad(a:string)
requires forall x :: 0 <= x < |a|  ==> a[x] == 'b' || a[x] == 'a' || a[x] == 'd';
{
forall j,k:: 0<=j<k<|a| && a[k]=='b' ==> a[j]=='b' 
&& forall j,k:: 0<=j<k<|a| && a[k]=='a' ==> a[j]=='b' || a[j]=='a'
&& forall j,k:: 0<=j<k<|a| && a[k]=='d' ==> a[j]=='b' || a[j]=='a' || a[j]=='d'
}

predicate reds(a: string, nextcol: int)
requires 0<=nextcol<=|a|
{ forall i:: 0<=i<nextcol ==> a[i]=='b' }

predicate whites(a: string, startcol: int, nextcol:int)
requires 0<=startcol<=nextcol<=|a|
{ forall i:: startcol<=i<nextcol ==> a[i]=='a' }

predicate blues(a: string, startcol: int)
requires 0<=startcol<=|a|
{ forall i:: startcol<=i<|a| ==> a[i]=='d' }




method BadSort(a: string) returns (b: string)
requires forall x :: 0 <= x < |a|  ==> a[x] == 'b' || a[x] == 'a' || a[x] == 'd';
ensures forall x :: 0 <= x < |b|  ==> b[x] == 'b' || b[x] == 'a' || b[x] == 'd';
ensures |a| == |b|
ensures multiset(b[..]) == multiset(a[..])
ensures sortedbad(b)
{
b := a;
//assert forall x :: 0 <= x < |b|  ==> b[x] == 'b' || b[x] == 'a' || b[x] == 'd';
var white := 0;
var blue := |b|;
var next := 0;
    while (next != blue) // when next==blue, no colours left to sort
    //decreases blue - next
    invariant |a| == |b|
    invariant forall x :: 0 <= x < |b|  ==> b[x] == 'b' || b[x] == 'a' || b[x] == 'd';
    invariant 0 <= white<=next<=blue <= |b|;
    invariant reds(b, white) && whites(b, white, next) && blues(b, blue)
    invariant multiset(b[..]) == multiset(a[..])
    {
        if (b[next] == 'a'){
            next:=next+1;
        } else if (b[next] == 'd'){
            blue:=blue-1;
            b := StringSwap(b,next,blue);
        } else if (b[next] == 'b'){
            b := StringSwap(b,next,white);
            next:=next+1;
            white:=white+1;
        }
        
    }
}


method Main()
{
    var f:string := "dabdabdab";
    var g:string := BadSort(f);
    assert multiset(f)==multiset(g);
    assert sortedbad(g);
    print g;


}