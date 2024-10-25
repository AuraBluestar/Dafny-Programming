// '==' -> '==>'
// '::' -> '*'
//'forall' -> 'V'
//'in' -> 'apartine'

//2
function funAbs(x: int): int {
  if x >= 0 then
    x
  else
    -x
}

//3,4,5
method computeAbs(x : int) returns (r : int)
  ensures r == funAbs(x)
  ensures r==x || r==-x
{
  if(x<0){
    r:=-x;
  } else {
    r:=x;
  }
  print x," ";
}

//6
function max2F( x: int, y:int): int{
  if x>y then x
  else y
}

method max2(x:int, y:int) returns (r : int)
  ensures r==max2F(x, y)
  ensures r>=x && r>=y
{
  if (x>y) {r:=x;}
  else {r:=y;}
}

//7
method max3(x:int, y:int, z:int) returns (r : int)
  ensures r>=x && r>=y && r>=z
{
  if (x>=y)
  {
    if(x>=z) {r:=x;}
    else {r:=z;}
  }
  else {
    if(y>=z) {r:=y;}
    else {r:=z;}
  }
}

//8
method computeFib(n : int) returns (r : int)
  requires n >= 0
  decreases n
{
  if (n == 0) {
    return 1;
  } else if (n == 1) {
    return 1;
  } else {
    var x := computeFib(n - 1);
    var y := computeFib(n - 2);
    return x + y;
  }
}

//9
method search(a : array<int>, key: int) returns (r : int)
  requires a.Length > 0
  ensures r >= -1 && r < a.Length
{
  var i:=0;
  while(i<a.Length)
  {
    if(a[i] == key)
    {
      r:= i;
      return r;
    }
    else {
      i:=i+1;
    }
  }
  return -1;
}

//10
method minArray(a : array<int>) returns (r:int)
requires a.Length > 0
//ensures forall r :: forall i:: 0<=i<=a.Length && r<=a[i]
{
  var i:=0;
  var min:=9999;
  while(i<a.Length)
  {
    if(a[i] < min)
    {
      min:=a[i];
    }
      i:=i+1;
  }
  r:=min;
}

//11
method maxArray(a : array<int>) returns (r:int)
requires a.Length > 0
{
  var i:=0;
  var max:=-9999;
  while(i<a.Length)
  {
    if(a[i] > max)
    {
      max:=a[i];
    }
      i:=i+1;
  }
  r:=max;
}

//12
method searchInv(a : array<int>, key: int) returns (r : int)
 requires a.Length > 0
 ensures r >= -1 && r < a.Length
{
  var i:=a.Length-1;
  while(i>=0)
  {
    if(a[i] == key)
    {
      r:= i;
      return r;
    }
    else {
      i:=i-1;
    }
  }
  return -1;
}

//13
method secondMax(a : array<int>) returns (r : int)
{
  var i:=0;
  var max1:=-9999;
  var max2:=-9999;
  while(i<a.Length)
  {
    if(a[i] > max1)
    {
      max2:=max1;
      max1:=a[i];
    }
    else if(a[i]>max2)
    {max2:=a[i];}
    i:=i+1;
  }
  r:=max2;
}


method Main()
{

  var x := computeAbs(-5);
  var y := max3(1,7,5);
  var z:= max2F(-1,6);
  var t:= computeFib(7);
  var a := new int[5];
  a[0], a[1], a[2], a[3], a[4] := 3, 9, 27, 9, -11;
  var x1:=search(a, 27);
  var x2:=searchInv(a, 27);
  var x3:= minArray(a);
  var x4:= maxArray(a);
  var x5:= secondMax(a);
  print x,"\n";
  print y,"\n";
  print z,"\n";
  print t,"\n";
  print x1, " ", x2, "\n";
  print x3, " ", x4,"\n";
  print x5, "\n";
}