function abs'(x:int):int{
if x<0 then 
-x
else x
}

method abs(x:int) returns (r:int)
ensures r==abs'(x)
{
    if(x<0)
    {
        r:=-x;
    }
    else{
        r:=x;
    }
}

// pt sequence [1..3] de la poz 1 inclusiv pana la 3 exclusiv
//[1..] de la poz 1 pana la final
//[..3] pana la poz 3 exclusiv
//[..] toata secventa