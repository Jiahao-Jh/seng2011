method SumOfSquares(n:int) returns(y:int)
requires n>=0
ensures y==(n*(n+1)*(2*n+1)/6)
{
    var i:int := 0;
    y := 0;
    while i < n
    invariant 0<=i<=n && y==(i*(i+1)*(2*i+1)/6)
    {
        i := i + 1;
        y := y + i*i;
    }
    
}
