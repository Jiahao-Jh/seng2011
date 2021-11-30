predicate sorted(a: string, low:int, high:int)
requires 0<=low<=high<=|a|
{ forall j,k:: low<=j<k<high ==> a[j]<=a[k] }

//swap from ex1.dfy
method StringSwap(s: string, i:nat, j:nat) returns (t: string)
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

//same structure as chapter11 InsertionSortSwap
method String3Sort(a: string) returns (b: string)
requires |a| >=1
ensures |b| == |a|
ensures sorted(b, 0, |b|);
ensures multiset(b[..]) == multiset(a[..]);
{
    b:=a;

    var up:=1;
    while (up < |a|)
    decreases |a| - up
    invariant |b| == |a|;
    invariant 1 <= up <= |b|;
    invariant sorted(b, 0, up);
    invariant multiset(b[..]) == multiset(a[..]);
    {
        
    var down := up;
    while (down >= 1 && b[down-1] > b[down])
    invariant |b| == |a|;
    invariant 0 <= down <= up;
    invariant forall i,j:: (0<=i<j<=up && j!=down) ==> b[i]<=b[j];
    invariant multiset(b[..]) == multiset(a[..]);
    {
        
        b := StringSwap(b,down-1,down);

        down:=down-1;
    }
    up:=up+1;
    }



}





method Main()
{
var a:string := "cba";
var b:string := String3Sort(a);
assert b=="abc";
}