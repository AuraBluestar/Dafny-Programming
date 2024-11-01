//Onisor Patricia

//ex 1
//a
ghost function fib_v1(n: int) : int

lemma fib0()
  ensures fib_v1(0) == 0

lemma fib1()
  ensures fib_v1(1) == 1

lemma fibRec(n: int)
  requires n > 1
  ensures fib_v1(n) == fib_v1(n - 1) + fib_v1(n - 2)


//b
function fib_v2(n: int) : int
  requires n >= 0
  decreases n
{
  if n == 0 then
    0
  else if n == 1 then
    1
  else
    fib_v2(n - 1) + fib_v2(n - 2)
}

//ex 2
function sumBetween(a: int, b: int) : int
  requires a <= b
  decreases b - a
{
  if a == b then
    0
  else
    a + sumBetween(a + 1, b)
}
