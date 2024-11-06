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

//ex 3
ghost function fib_axiomatized(n: int) : int

lemma fib_axiomatized0()
  ensures fib_axiomatized(0) == 0

lemma fib_axiomatized1()
  ensures fib_axiomatized(1) == 1

lemma fib_axiomatizedRec(n: int)
  requires n > 1
  ensures fib_axiomatized(n) == fib_axiomatized(n - 1) + fib_axiomatized(n - 2)

function fib_defined(n: int) : int
  requires n >= 0
  decreases n
{
  if n == 0 then
    0
  else if n == 1 then
    1
  else
    fib_defined(n - 1) + fib_defined(n - 2)
}

lemma equivalenceFib(n: int)
  requires n >= 0
  ensures fib_axiomatized(n) == fib_defined(n)
{
  if n == 0 {
    fib_axiomatized0();
    assert fib_axiomatized(0) == 0;
  } else if n == 1 {
    fib_axiomatized1();
    assert fib_axiomatized(1) == 1;
  } else {
    if n > 1 {
      fib_axiomatizedRec(n);
      equivalenceFib(n - 1);
      equivalenceFib(n - 2);
      assert fib_axiomatized(n) == fib_axiomatized(n - 1) + fib_axiomatized(n - 2);
      assert fib_axiomatized(n) == fib_defined(n - 1) + fib_defined(n - 2);
    }
  }
}

// ex 4
type BST(0)

ghost const Leaf : BST

ghost function Node(x: int, l: BST, r: BST) : BST

lemma node_injective(n1: int, l1: BST, r1: BST, n2: int, l2: BST, r2: BST)
  requires Node(n1, l1, r1) == Node(n2, l2, r2)
  ensures n1 == n2 && l1 == l2 && r1 == r2

lemma node_leaf_distinct(n: int, l: BST, r: BST)
  ensures Node(n, l, r) != Leaf

lemma bst_total(t: BST)
  ensures t == Leaf || exists n: int, l: BST, r: BST :: t == Node(n, l, r)

lemma inductionBST(P: BST -> bool)
  requires P(Leaf)
  requires forall n: int, l: BST, r: BST :: P(l) && P(r) ==> P(Node(n, l, r))
  ensures forall t: BST :: P(t)

ghost function IsLeaf(t: BST) : bool
ghost function IsNode(t: BST) : bool

lemma leaf_node_total(t: BST)
  ensures IsLeaf(t) || IsNode(t)

lemma leaf_node_exclusivity(t: BST)
  ensures IsLeaf(t) ==> !IsNode(t) && IsNode(t) ==> !IsLeaf(t)

ghost function GetValue(t: BST) : int
  requires IsNode(t)

ghost function GetLeft(t: BST) : BST
  requires IsNode(t)

ghost function GetRight(t: BST) : BST
  requires IsNode(t)

lemma node_accessors(n: int, l: BST, r: BST)
  ensures IsNode(Node(n, l, r))
  ensures GetValue(Node(n, l, r)) == n
  ensures GetLeft(Node(n, l, r)) == l
  ensures GetRight(Node(n, l, r)) == r


//ex 5
predicate isDivisorFunctional(x: int, y: int)
  requires x > 0 && y >= 0
{
  y % x == 0
}
predicate isDivisorQuantified(x: int, y: int)
  requires x>1 && y>1
{
  exists k: int :: 0 <= k <= y && y == x * k
}

//ex 6
ghost predicate isGCD(d: int, a: int, b: int)
  requires a >= 0 && b >= 0
{
  if a == 0 && b == 0 then
    d == 0
  else
    d > 0 &&
    exists k1: int :: k1 >= 0 && a == d * k1 &&
                      exists k2: int :: k2 >= 0 && b == d * k2 &&
                                        forall e: int ::
                                          (e > 0 && exists k3: int :: (k3 >= 0 && a == e * k3) && exists k4: int :: (k4 >= 0 && b == e * k4)) ==> (e <= d)
}

//ex 7
function gcd(a: int, b: int) : int
  requires a >= 0 && b >= 0
  decreases b
{
  if b == 0 then
    a
  else
    gcd(b, a % b)
}
