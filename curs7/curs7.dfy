lemma Example(x: int) 
  requires x % 2 == 0 
  ensures 2 * (x / 2) == x
{
}
  
lemma {:axiom} Issue1()
  ensures 1 == 2

lemma exFalso()
  requires false
  ensures 1 == 2
{
}

lemma ex1(P : bool, Q : bool)
  requires P ==> Q
  requires Q ==> P
  ensures P <==> Q
{
}

ghost predicate P(x : int)

ghost predicate Q(x : int)

ghost predicate R(x : int)

lemma Example1(x : int)
  requires P(x)
  ensures Q(x)
{
  // T, x: T, P(x) |- Q(x)
  assert R(x) by {
    assume false;
    // T, x: T, P(x) |- R(x)
  }
  assume Q(x);
  // T, x: T, P(x), R(x) |- Q(x)
}


ghost predicate even(x : int)
{
  exists y :: x == y * 2
}

ghost predicate odd(x : int)
{
  exists y :: x == y * 2 + 1
}

lemma asdf(x : int)
  requires even(x * x)
  ensures odd(x + 1)
{
  assert even(x) by {
    assert exists y :: x * x == y * 2;
    var y :| x * x == y * 2;
    if !even(x) {
      assert x % 2 == 1 by {
        if x % 2 == 0 {
          assert (x / 2) * 2 == x;
        }
      }
      assert x == (x / 2) * 2 + 1;
      assert x * x == ((x / 2) * 2 + 1) * ((x / 2) * 2 + 1)
        ==
        (x / 2) * 2 * (x / 2) * 2 + (x / 2) * 2 + (x / 2) * 2 + 1
        ==
        2 * ((x / 2) * (x / 2) * 2 + (x / 2)  + (x / 2)) + 1
        == y * 2;
        //assume false;
    }
  }
}


lemma asdf'(x : int)
  requires even(x * x)
  ensures odd(x + 1)
{
  assert exists y :: x * x == y * 2;
  var y :| x * x == y * 2;
  if !even(x) {
    assert x % 2 == 1 by {
      if x % 2 == 0 {
        assert (x / 2) * 2 == x;
      }
    }
    assert x == (x / 2) * 2 + 1;
    assert x * x == ((x / 2) * 2 + 1) * ((x / 2) * 2 + 1)
      ==
      (x / 2) * 2 * (x / 2) * 2 + (x / 2) * 2 + (x / 2) * 2 + 1
      ==
      2 * ((x / 2) * (x / 2) * 2 + (x / 2)  + (x / 2)) + 1
      == y * 2;
      //assume false;
  }
  assert even(x);
}




// lemma asdf'(x : int)
//   requires even(x * x)
//   ensures odd(x + 1)

lemma exemplu_if(x : int)
  ensures even(x * x) ==> odd(x + 1)
{
  if even(x * x) {
    asdf'(x);
    assert odd(x + 1);
  }
  // ..., even(x * x) ==> odd(x) + 1 |- even(x * x) ==> odd(x + 1)
}






  // lemma Conclusion<T>(x: T)
  //   requires P(x)
  //   ensures Q(x)
  // {
  //   // T, x: T, P(x) |- Q(x)
  //   forall y : T
  //     ensures R(y)
  //   {
  //     // T , x: T, P(x), y : T |- R(y)
  //   }
  //   // T, x: T, P(x), forall y: T :: R(y) |- Q(x)
  // }

lemma {:axiom} Premise(x : int)
  requires P(x)
  ensures Q(x)

lemma Conclusion'()
  ensures forall x : int :: P(x) ==> Q(x)
{
  // Premise |- forall x : int :: P(x) ==> Q(x)
  forall y : int
    ensures P(y) ==> Q(y)
  {
    // Premise, y : int |- P(y) ==> Q(y)
    if P(y) {
      // Premise, y : int, P(y) |- Q(y)
      Premise(y);
      assert Q(y);
    }
  }
  // Premise, forall y : int :: P(y) ==> Q(y) |- forall x : int :: P(x) ==> Q(x)
}

lemma Conclusion''()
  ensures forall x : int :: P(x) ==> Q(x)
{
  forall y : int | P(y)
    ensures Q(y)
  {
    Premise(y);
  }
}

lemma exercise()
  ensures forall x : nat :: x % 2 == 0 ==> exists y : nat :: x == 2 * y
{
  forall x : nat
    ensures x % 2 == 0 ==> exists y : nat :: x == 2 * y
  {
    if x % 2 == 0 {
      assert x == 2 * (x / 2);
      assert exists y : nat :: x == 2 * y;
    }
  }
}

lemma v1(x : int)
  requires even(x)
  ensures odd(x + 1)
{
  assume false;
}

lemma v2(x : int)
  ensures even(x) ==> odd(x + 1)
{
  assume false;
}

lemma v3()
  ensures forall x :: even(x) ==> odd(x + 1)
{
  assume false;
}

lemma example_exists()
  ensures exists y :: 10 == 2 * y
{
  assert 10 == 2 * 5;
}

lemma example_exists'() returns (y : int)
  ensures 10 == 2 * y
{
  y := 5;
}
