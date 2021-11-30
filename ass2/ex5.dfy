function expo(x:int, n:nat): int
decreases n
{
    if (n==0) then 1 else x * expo(x,n-1)
}


lemma {:induction false} Expon23(n: nat)
ensures ( expo(2,3*n) - expo(3,n) ) % 5 == 0;
{
    if (n == 0){
        assert ( expo(2,0) - expo(3,0) ) % 5 == 0; 
    }
    else {
        Expon23(n-1);
        assert expo(2,3*(n-1)) == expo(2,3*n-3);
        assert expo(2,3*n-1) * 2== expo(2,3*n);
        assert expo(2,3*n) == expo(2,3*n-1) * 2;
        assert expo(2,3*n) == expo(2,3*n-2) * 4;

    }
}