lemma example1()
  ensures forall n : int, m : int {:trigger} :: n > 0 ==> n * 2 + m > m + n
{
}

lemma example2()
  ensures forall n : int, m : int {:trigger} :: n * m == m * n
{
}

/*
   array a
   0 .. n - 1
   a e impartit in k blocuri de cate m elemente
   blocul al i-lea este impartit in q subblocuri de cate l elemente
   am un index 0 <= j < q al unui subbloc din al i-lea bloc
   am un index x in subbloc
   vreau sa arat ca 0 <= i * m + l * j + x < n
 */
lemma example3(n : int, k : int, m : int, q : int, l : int, i : int, j : int, x : int)
  requires n > 0
  requires m > 0
  requires q > 0
  requires l > 0
  requires n == k * m
  requires 0 <= i < k
  requires m == q * l
  requires 0 <= j < q
  requires 0 <= x < l
  ensures 0 <= i * m + l * j + x < n
{
  assert l * j + x <= l * (q - 1) + x < l * (q - 1) + l == l * q == m;
  assert l * j + x < m;
  assert i * m + l * j + x < i * m + m == m * (i + 1) <= m * k == n;
  assert i * m + l * j + x < n;
  //  assume false;
}

lemma triggerExample()
  ensures exists n : int, m : int :: n * m == 10
{
  assert 2 * 5 == 10;
}

ghost function plus(x : int, y : int) : int
{
  x + y
}

lemma triggerExample1()
  ensures exists n : int, m : int {:trigger plus(n, m)} :: n < m
{
  assert plus(2, 2) == 4;
  assert plus(2, 10) == 12;
}

ghost function identity(x : int) : int
{
  x
}

lemma triggerExample2(s : seq<int>)
  requires |s| > 10
  requires sorted(s)
{
  //   forall i :: 0 <= i < |s| - 1 ==> s[i] <= s[i + 1]
  //assert s[3] <= s[4];
  // assert identity(3) == 3;
  // assert identity(4) == 4;
  assert s[3] <= s[4];
  assert s[4] <= s[5];
  assert s[3] <= s[5];
}

lemma triggerExample3(s : seq<int>)
  requires |s| > 10
  requires sorted'(s)
{
  //   forall i : int, j : int :: 0 <= i < j < |s| ==> s[i] <= s[j]
  assert s[3] <= s[5];
}

lemma sorted'_sorted(s : seq<int>)
  requires sorted'(s)
  ensures sorted(s)
{
}

lemma helper(s : seq<int>, i : int, j : int)
  requires sorted(s)
  requires 0 <= i < j < |s|
  ensures s[i] <= s[j]
{
  if (j == i + 1) {
    // nothing to do
  } else {
    helper(s, i, j - 1); // s[i] <= s[j - 1]
    assert s[j - 1] <= s[j];
    assert s[i] <= s[j];
  }
}

lemma helper'(s : seq<int>, i : int, j : int)
  requires sorted(s)
  requires 0 <= i < j < |s|
  ensures s[i] <= s[j]
{
  var k := i;
  while (k < j)
    invariant i <= k <= j
    invariant s[i] <= s[k]
  {
    // s[i] <= s[k]
    k := k + 1;
    // s[i] <= s[k - 1]
    // s[k - 1] <= s[k] (din sorted(s))
    // s[i] <= s[k]
  }
}

ghost predicate sorted(s : seq<int>)
{
  forall i // {:trigger identity(i)}
    :: 0 <= i < |s| - 1 ==> s[i] <= s[i + 1]
}

ghost predicate sorted'(s : seq<int>)
{
  forall i : int, j : int :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

lemma sorted_sorted'(s : seq<int>)
  requires sorted(s)
  ensures sorted'(s)
{
  // forall statement (regula de introducere a lui forall in deductia naturala)
  forall i : int | i >= 0
    ensures forall j :: i < j < |s| ==> s[i] <= s[j]
  {
    forall j : int | i < j < |s|
      ensures s[i] <= s[j]
    {
      helper'(s, i, j);
    }
    assert forall j : int :: i < j < |s| ==> s[i] <= s[j];
  }
  assert forall i :: i >= 0 ==> forall j :: i < j < |s| ==> s[i] <= s[j];
}

ghost predicate even(x : int)
{
  exists half :: x == 2 * half
}

lemma l1()
  ensures forall x : int :: even(x) ==> even(x + 2)
{
  // forall x : int
  //   ensures even(x) ==> even(x + 2)
  // {
  //   l2(x);
  // }
  forall x : int | even(x)
    ensures even(x + 2)
  {
    l3(x);
  }
}

lemma l2(x : int)
  ensures even(x) ==> even(x + 2)
{
  // demonstrez o implicatie
  if even(x) // presupun antecedentul
  {
    // demonstrez consecventul
    l3(x);
    assert even(x + 2);
  }
  assert even(x) ==> even(x + 2);
}

lemma l3(x : int)
  requires even(x)
  ensures even(x + 2)
{
  assert exists half :: x == 2 * half;
  var half : int :| x == 2 * half; // regula de eliminare a lui exists
  //assert x + 2 == 2 * (half + 1);
  assert identity(half + 1) == half + 1;
  assert exists half' {:trigger identity(half')} :: x + 2 == 2 * half';
}

lemma l3'(x : int)
  requires even(x)
  ensures even(x + 2)
{
  l1();
  // assert forall x : int :: even(x) ==> even(x + 2)
}

lemma smallerLeft(n : int, m : int)
  requires 0 < m < n
  ensures m * m < n * m
{
  var k := n - m;
  assert k > 0;
  assert n * m == (m + k) * m == m * m + k * m > m * m;
}

lemma smallerRight(n : int, m : int)
  requires 0 < m < n
  ensures n * m < n * n
{
  var k := n - m;
  assert k > 0;
  assert n * n == n * (m + k) == n * m + k * n > n * m;
}

lemma smallerLeft'(a : int, b : int, c : int)
  requires c > 0
  requires 0 < a < b
  ensures a * c < b * c
{
}

lemma smallerEqRight'(a : int, b : int, c : int)
  requires c > 0
  requires 0 < a <= b
  ensures c * a <= c * b
{
}

lemma proof_by_contradiction()
  ensures forall n : int, m : int :: n > m >= 0 ==> n * n > m * m + m
{
  if !forall n : int, m : int :: n > m > 0 ==> n * n > m * m + m // presupunem contrariul
  {
    // demonstram o contradictie
    assert exists n : int, m : int :: n > m > 0 && n * n <= m * m + m;
    var n : int, m : int :| n > m > 0 && n * n <= m * m + m;
    if m > 0 { // analiza de cazuri: (I) m > 0 sau (II) m == 0
      calc {
        m * m + m;
      ==
        m * (m + 1);
      <
        {
          smallerLeft'(m, n, m + 1);
        }
        n * (m + 1);
      <=
        {
          smallerEqRight'(m + 1, n, n);
        }
        n * n;
      }
      assert false;
    } else {
      assert false;
    }
  }
}