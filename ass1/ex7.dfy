method BigFoot(step: nat)
requires step>=1
{
    var indx := 0; 
    while indx<=42
    invariant 0<=indx && indx !=0 ==> indx>=step;
    invariant indx%step==0
    { indx := indx+step; }
    assert indx > 42 && indx>=step;
}

