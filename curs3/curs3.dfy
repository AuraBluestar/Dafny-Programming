method minMax(x:int, y:int) returns(min:int, max:int)
ensures min<=max
ensures min<=x<=max && min<=y<=max
ensures min==x || min==y
ensures max==x || max==y
{
    if x<y
    {
        min:=x;
        max:=y;
    }
    else
    {
        min:=y;
        max:=x;
    }
}

method minMax1(x:int, y:int) returns(min:int, max:int)
{
    if x<y
    {
        min:=x;
        max:=y;
    }
    else
    {
        min:=y;
        max:=x;
    }
}

method useMiniMax()
{
   // assert forall x : int :: x<x+13;
    var x,y:=minMax(13,18);
    assert x<=y;
    var a,b:=minMax1(13,18);
}

method double(n:int) returns(r:int)
    requires n>=0
{
    var x:=0;
    var y:=0;
    while(x < n)
     invariant 0 <= x <= n
    {
        x:=x+1;
        y:=y+2;
    }
    return y;
}

method double2(n:int) returns(r:int)
    requires n>=0
    ensures r==n*2
{
    var y:=0;
   for x:=n downto 0
   invariant y==(n-x)*2 
   {
    y:=y+2;
   }
    return y;
}

method minArray(a: array<int>) returns(r:int)
requires a.Length>0
{
    r:=a[0];
    for i:=1 to a.Length
    {
        if a[i]<r{
            r:=a[i];
        }
    }

}

method reverseArray(a: array<int>) returns(r:array<int>)
requires a.Length>0
{
    r:= new int [a.Length];
    for i:=0 to a.Length
    {
        r[i]:=a[a.Length-1-i];
    }

}

/*
method reverseArray2(a: array<int>) returns(r : array<int>)
//requires a.Length>0
ensures r.Length==a.Length
ensures forall i ::0<=i<=a.Length ==> a[ii]==r[a.Length-1-ii]
{
    r:= new int [a.Length];
    for i:=0 to a.Length
    invariant forall ii :: 0<=ii<=i ==> r[ii]==a[a.Length-1-ii]
    {
        r[i]:=a[a.Length-1-i];
    }

}*/

method reverseArrayinPlace(a: array<int>)
modifies a //frame expression
{
    for i:=0 to a.Length/2
    {
        var t:=a[i];
        a[i]:=a[a.Length-1-i];
        a[a.Length-1-i]:=t;
    }

}

method Main(){
    var min,max:=minMax(13,14);
    print min, max;
}