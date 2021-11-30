method TopSort()
modifies this, this.buf
requires Valid()
ensures  buf == old(buf)
ensures  multiset(buf[..]) == multiset(old(buf[..]))  
ensures  multiset(shadow) == multiset(old(shadow)) 
ensures   n  == old(n) 
ensures   m  == old(m) 
ensures Valid()
//buf
ensures if (n - m) >=2 && old(buf[n-1]) < old(buf[n-2]) then buf[n-1] == old(buf[n-2]) && buf[n-2] == old(buf[n-1]) else buf == old(buf)
ensures  (n - m) >=2 && old(buf[n-1]) < old(buf[n-2]) ==> buf[m..n-2] == old(buf[m..n-2])
//shadow
ensures if (n - m) >=2 && old(buf[n-1]) < old(buf[n-2]) then shadow[|shadow|-1] == old(shadow[|shadow|-2]) && shadow[|shadow|-2] == old(shadow[|shadow|-1]) else shadow == old(shadow)
ensures  (n - m) >=2 && old(buf[n-1]) < old(buf[n-2]) ==> shadow[0..|shadow|-2] == old(shadow[0..|shadow|-2])
{
    if ((n - m) >=2 && buf[n-1] < buf[n-2]){
        buf[n-1], buf[n-2]:= buf[n-2], buf[n-1];
        ghost var k:char := shadow[|shadow|-1];
        assert k in multiset(old(shadow));
        shadow := shadow[ |shadow|-1 := shadow[|shadow|-2]];
        shadow := shadow[ |shadow|-2 := k];

        assert buf[m..n-2] == old(buf[m..n-2]);
        assert shadow[0..|shadow|-2] == old(shadow[0..|shadow|-2]);
    }

    assert n  == old(n);
    assert m  == old(m);
}