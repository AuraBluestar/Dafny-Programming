function abs(x : int) : int
{
  if x >= 0 then
    x
  else
    -x
}

method computeAbs(x : int) returns (r : int)
  ensures r == abs(x)
{
  if (x < 0) {
    r := -x;
  } else {
    r := x;
  }
}

method computeAbs2(x : int) returns (r : int)
  ensures r >= 0
  ensures r == x || r == -x
{
  if (x < 0) {
    r := -x;
  } else {
    r := x;
  }
}

function f(n : int) : int
  requires n >= 0
{
  if n <= 1 then
    1
  else
    f(n - 1) + f(n - 2)
}

method fibImp(n : int) returns (r : int)
  requires n >= 0
  ensures r == f(n)
{
  var a := 1;
  var b := 1;
  var i := 0;
  while (i < n)
    invariant 0 <= i <= n
    invariant a == f(i)
    invariant b == f(i + 1)
  {
    var s := a + b;
    a := b;
    b := s;
    i := i + 1;
  }
  // i == n
  // a == f(i)  <==> a == f(n)
  return a;
}

method fibRec(n : int) returns (r : int)
  requires n >= 0
  decreases n
  ensures r == f(n)
{
  if (n == 0) {
    return 1;
  } else if (n == 1) {
    return 1;
  } else {
    var x := fibRec(n - 1);
    var y := fibRec(n - 2);
    return x + y;
  }
}

method linearSearch(a : array<int>, key : int) returns (pos : int)
  ensures pos == -1 ==> (forall i :: 0 <= i < a.Length ==> a[i] != key)
  ensures pos != -1 ==> 0 <= pos < a.Length && a[pos] == key
{
  var i := 0;
  while (i < a.Length)
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> a[j] != key
  {
    if (a[i] == key) {
      return i;
    }
    i := i + 1;
  }
  return -1;
}

method binarySearch(a : array<int>, key : int) returns (pos : int)
  //requires forall i :: 0 <= i < a.Length - 1 ==> a[i] <= a[i + 1]
  requires forall i :: forall j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures pos == -1 ==> (forall i :: 0 <= i < a.Length ==> a[i] != key)
  ensures pos != -1 ==> 0 <= pos < a.Length && a[pos] == key
{
  var l := 0;
  var r := a.Length - 1;
  while (l <= r)
    invariant 0 <= l <= a.Length
    invariant -1 <= r <= a.Length - 1
    invariant forall i :: 0 <= i < l ==> a[i] < key
    invariant forall i :: r < i < a.Length ==> a[i] > key
    decreases r - l
  {
    var mid := (l + r) / 2;
    if (a[mid] == key) {
      return mid;
    } else if (a[mid] > key) {
      r := mid - 1;
    } else if (a[mid] < key) {
      assert a[mid] < key;
      l := mid + 1;
    } else {
      assert false;
    }
  }
  return -1;
}

method Main()
{
  // var x := 13;
  // var y := -13;
  // var z := computeAbs(y);
  // print x, " ", y, " ", z;
  // //var zp := fib(-3);
  var x5 := fibRec(5);
  var y5 := fibImp(5);
  var x7 := fibRec(7);
  var y7 := fibImp(7);
  print x5, " ", y5, "\n";
  print x7, " ", y7, "\n";
}