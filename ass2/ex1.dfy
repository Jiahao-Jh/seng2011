method StringSwap(s: string, i:nat, j:nat) returns (t: string)
ensures |s| == |t|
ensures multiset(t[..]) == multiset(s[..]);
ensures  forall x :: 0 <= x < |s| && x!= i && x !=j ==> t[x] == s[x];
ensures  0<=i <|s|  && 0<=j < |s| ==> t[i] == s[j];
ensures  0<=i <|s|  && 0<=j < |s| ==> t[j] == s[i];
{
    t := s;
    if ( 0<=i <|s|  && 0<=j < |s|){
        var k:char := s[i];
        var y:char := s[j];
        t := t[i := y];
        t := t[j := k];
    }


}



method Main()
{
    var a:string := "1scow2";
    var b:string := StringSwap(a, 1, 5);
    assert b == "12cows";
    var c:string := "";
    var d:string := StringSwap(c, 1, 2);
    assert c == d;

}