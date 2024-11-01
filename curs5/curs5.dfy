type NaturalNumber(00)

ghost const zero: NaturalNumber

ghost function Successor(n : NaturalNumber) : NaturalNumber

ghost function Less(n : NaturalNumber, m : NaturalNumber) : bool
// ghost predicate Less(n : NaturalNumber, m : NaturalNumber)

// lemma Proposition()
//   ensures forall m : int, n : int :: m > 0 && n > m ==> m + n > 0

lemma Prop<T>(x : T)  // schema de lema (cate o lema pentru fiecare T, x)
  ensures x == x

lemma Prop'(x : int) 
  requires x % 2 == 0
  ensures (x / 2) * 2 == x 

predicate ConditionalExpression<T>(bexpr: bool, expr1: T, expr2: T)  {
    // expresia if-then-else
  (if bexpr then expr1 else expr2) is T // a nu se confunda cu instructiunea if-else
}

method test1() returns (r : int) // instructiunea if-else (se foloseste in metode)
{
  if true {
    r := 13;
  } else {
    r := 42;
  }
}

predicate LetBinding<U, V>(expr1: U, expr2: V)
{
  (var x := expr1; expr2) is V
    /*

       let x = expr1 in
          expr2
       
     */
    /*
       var x := expr1;
       x := x + 1;     // <--- nu pot face asta
       expr2
       */
       
}

predicate Tuple<T, U, V, W>(t: T, u: U, v: V, w : W) { (t, u, v, w) is (T, U, V, W) }

predicate TupleAccess0<T, U, V, W>(tup: (T, U, V, W)) { tup.0 is T }

predicate TupleAccess1<T, U, V, W>(tup: (T, U, V, W)) { tup.1 is U }

predicate TupleAccess2<T, U, V, W>(tup: (T, U, V, W)) { tup.2 is V }

predicate TupleAccess3<T, U, V, W>(tup: (T, U, V, W)) { tup.3 is W }

predicate LambdaAbstraction<U, V>(expr: V) { ((x: U) => expr) is U -> V }

predicate Application<U, V>(fun: U -> V, arg: U) { fun(arg) is V }

method test2()
{
  assert ((x : int) => x + 1)(3) == 4;
}

type T
  
ghost predicate P(x : T)

lemma PredicateLogicConnectives()
  ensures (forall x: T :: P(x)) is bool
  ensures (exists x: T :: P(x)) is bool
  
// lemma SecondOrder()
//   ensures forall P: int -> bool :: forall x: int :: P(x) || !P(x)

// lemma ThirdOrder()
//   ensures forall P2: (int -> bool) -> bool :: forall P1: int -> bool :: P2(P1) || !P2(P1)

// lemma Partial() 
//   ensures forall x : int :: x * 1 / x == x 

lemma Test2()
  ensures forall x: int :: x != 0 ==> x / x == 1

predicate Q(x: int)

lemma HilbertEpsilon() 
  requires forall x: int :: Q(x)
  ensures var x: int :| Q(x); x == x && Q(x)
  
  // var x : int :| isPrime(x); <---- x este un numar prim, dar nu stiu care
  // in general, acest operator nu se poate compila

method NotReferentiallyTransparent()
{
  //assert (var x: int :| true; x) == (var x: int :| true; x);
}

type T'

predicate P'(x : T') 

// refinement types (tipuri rafinate)
  
type U = x : T' | P'(x) witness * // U ca fiind submultimea lui T' cu proprietatea P'

// U ar fi putea fi vid

method asdf()
{
  // var x : U :| true; // nu exista neaparat o valoare de tip U
}
                                  
type Nat = x : int | x >= 0 witness 0 // am garantia ca Nat are cel putin un element

method asdf'()
{
  var x : Nat :| true;
}

type Even = x : Nat | x % 2 == 0 witness 2


  

lemma ReadableLiteral() ensures 4_345_765 is int

lemma asdf3()
{
  assert 4_345_765 == 4345765;
}

// lemma Aasdfkjldasjfkldsa() // asta e o axioma, deoarece nu are demonstratie
//   ensures forall m: int, n: int :: m + n == n + m
// // {
// //   // aici vine demonstratia
// // }

// VARIANTA 1: axiomatizare

ghost const x : int // am declarat o constanta de tip int, se cheama "x"

lemma EssenceOfX() // am axiomatizat ce stiu despre x
  ensures x == 0

// VARIANTA 2: definirea


// VARIANTA 1: declararea lui increment
ghost const x' : int := 0

ghost function Increment(n: int): int // declarat functia "Increment"

lemma EssenceOfIncrement(n: int) // o axiomatizez
  ensures Increment(n) == n + 1

lemma useAxiom()
  ensures Increment(4) == 5
{
  EssenceOfIncrement(4); // asa folosesc o axioma
}

ghost function Increment'(n: int): int { // cand definesc o functia, Dafny imi creaza o axiomatizare implicit
  n + 1
}

lemma useDef()
  ensures Increment'(4) == 5
{
}

ghost predicate Valid(P: int -> bool) {
  forall x: int :: P(x)
}

ghost function Divide(m: int, n: int): int

lemma EssenceOfDivide(m: int, n: int)
  requires n != 0
  ensures Divide(m, n) == m / n


ghost function Divide'(m: int, n: int): int
  requires n != 0
{
  m / n
}

ghost function Factorial(n : int) : int

lemma FactorialProp0()
  ensures Factorial(0) == 1
  
lemma FactorialProp1(n: int)
  requires n > 0
  ensures Factorial(n) == n * Factorial(n - 1)

lemma issue1()
{
  // dezavantaj al axiomatizarii (pierd proprietatea de a fi executabil)
  FactorialProp1(3); // Factorial(3) == 3 * Factorial(2)
  FactorialProp1(2); // Factorial(2) == 2 * Factorial(1)
  FactorialProp1(1); // Factorial(1) == 1 * Factorial(0)
  FactorialProp0(); // Factorial(0) == 1
  assert Factorial(3) == 6;
}



ghost function Factorial'(n : int) : int

lemma FactorialProp0'()
  ensures Factorial'(0) == 1
  
lemma FactorialProp1'(n: int)
  requires n >= 0 // ">=" in loc de ">"
  ensures Factorial'(n) == n * Factorial'(n - 1)

lemma issue2()
{
  // dezavantaj 2: risc sa am axiome inconsistente
  FactorialProp0'(); // Factorial'(0) == 1
  FactorialProp1'(0); // Factorial'(0) == 0 * Factorial'(0 - 1)
  assert 0 == 1;
}

// cand definesc simboluri, nu risc sa introduc inconsistente
ghost function Factorial''(n: int): int 
  requires 0 <= n
{
  if n == 0 then 1 else Factorial''(n - 1)
}

function rec1(a : int, b : int) : int
  requires a <= b
  decreases b - a // variant, expresie "decreases"
{
  if a >= b then
    0
  else
    a + rec1(a + 1, b)
}


type Peano(0) 
  
ghost const Zero : Peano 
    
ghost function Succ(n : Peano) : Peano 

ghost function Add(n : Peano, m : Peano) : Peano

lemma add_zero(n : Peano)
  ensures Add(n, Zero) == n
  
lemma add_succ(n : Peano, m' : Peano)
  ensures Add(n, Succ(m')) == Succ(Add(n, m'))
// alternativ:   ensures Add(n, Succ(m')) == Add(Succ(n), m')

ghost const One : Peano

lemma one_def()
  ensures One == Succ(Zero)

lemma test_add()
  ensures Add(Zero, One) == Succ(Zero)
{
  one_def(); // One == Succ(Zero), ramane de demonstrat Add(Zero, Succ(Zero)) == Succ(Zero)
  add_succ(Zero, Zero); // Add(Zero, Succ(Zero)) == Succ(Add(Zero, Zero)),
  // ramane de demonstrat Succ(Zero) == Succ(Add(Zero, Zero))
  add_zero(Zero); // Add(Zero, Zero) == Zero
  // ramane de demonstrat Succ(Zero) == Succ(Zero) (egalitatea e reflexiva)
}

// nu functioneaza fiindca nu pot gasi o expresie decreases
// lemma add_one(n : Peano)
//   ensures Add(One, n) == Succ(n)
// {
//   PeanoExhaustive(n);  //ensures n == Zero || exists m: Peano :: n == Succ(m)
//   if n == Zero {
//     // ramane de aratat Add(One, Zero) == Succ(Zero)
//     one_def();
//     // ramane de aratat Add(Succ(Zero), Zero) == Succ(Zero)
//     add_zero(Succ(Zero));
//     // ramane de aratat Succ(Zero) == Succ(Zero)
//   } else {
//     var m' :| n == Succ(m');
//     // ramane de aratat ca: Add(One, Succ(m')) == Succ(Succ(m'))
//     add_succ(One, m'); // Add(One, Succ(m')) == Succ(Add(One, m'))
//     // ramane de aratat ca: Succ(Add(One, m')) == Succ(Succ(m'))
//     // ramane de aratat ca: Add(One, m') == Succ(m')
//     add_one(m');
//     // assume false;
//   }  
// }

// lemma InductionPrinciple(P : Peano -> bool) 
//   requires P(Zero) 
//   requires forall n : Peano :: P(n) ==> P(Succ(n))
//   ensures forall n : Peano :: P(n)

ghost predicate Pn(n : Peano)
{
  Add(One, n) == Succ(n)
}

lemma caz_baza()
  ensures Pn(Zero)
{
   one_def();
   add_zero(Succ(Zero));
}

lemma caz_inductiv()
  ensures forall n : Peano :: Pn(n) ==> Pn(Succ(n))
  // ensures forall n :: Add(One, n) == Succ(n) ==> Add(One, Succ(n)) == Succ(Succ(n))
{
  // forall statement (fie n o valoare de tip Peano oarecare)
  forall n : Peano | true
  ensures Pn(n) ==> Pn(Succ(n))
  {
    // in acest bloc, avem definita valoarea "n"
    // ramane de aratat Add(One, n) == Succ(n) ==> Add(One, Succ(n)) == Succ(Succ(n))
    add_succ(One, n); // Add(One, Succ(n)) == Succ(Add(One, n))
    // ramane de aratat Add(One, n) == Succ(n) ==> Succ(Add(One, n)) == Succ(Succ(n))
    // ramane de aratat Add(One, n) == Succ(n) ==> Add(One, n) == Succ(n)
  }
}

lemma add_one'(n : Peano)
  ensures Pn(n)
{
  caz_baza();
  caz_inductiv();
  InductionPrinciple(Pn);
  // PeanoExhaustive(n);  //ensures n == Zero || exists m: Peano :: n == Succ(m)
  // if n == Zero {
  //   // ramane de aratat Add(One, Zero) == Succ(Zero)
  //   one_def();
  //   // ramane de aratat Add(Succ(Zero), Zero) == Succ(Zero)
  //   add_zero(Succ(Zero));
  //   // ramane de aratat Succ(Zero) == Succ(Zero)
  // } else {
  //   var m' :| n == Succ(m');
  //   // ramane de aratat ca: Add(One, Succ(m')) == Succ(Succ(m'))
  //   add_succ(One, m'); // Add(One, Succ(m')) == Succ(Add(One, m'))
  //   // ramane de aratat ca: Succ(Add(One, m')) == Succ(Succ(m'))
  //   // ramane de aratat ca: Add(One, m') == Succ(m')
  //   add_one(m');
  //   // assume false;
  // }  
}

lemma PeanoInjectivity(m : Peano, n : Peano)
  requires Succ(m) == Succ(n)
  ensures m == n
  
lemma PeanoDiff(n : Peano)
  ensures Succ(n) != Zero 

lemma PeanoExhaustive(n : Peano)
  ensures n == Zero || exists m: Peano :: n == Succ(m)

lemma InductionPrinciple(P : Peano -> bool) 
  requires P(Zero) 
  requires forall n : Peano :: P(n) ==> P(Succ(n))
  ensures forall n : Peano :: P(n)

datatype MyNat = Zero | Succ(MyNat) // tip algebric de date

// datatype List = Empty | Cons(head : int, tail : List)

type List(0)

ghost const Empty : List

ghost function Cons(head : int, tail : List) : List

lemma different_empty_cons(head : int, tail : List)
  ensures Empty != Cons(head, tail)

lemma injective_cons(head : int, tail : List, head' : int, tail' : List)
  requires Cons(head, tail) == Cons(head', tail')
  ensures head == head'
  ensures tail == tail'

lemma total_empty_cons(list : List)
  ensures list == Empty || exists head, tail :: list == Cons(head, tail)

lemma list_induction(P : List -> bool)
  requires P(Empty)
  requires forall head, tail :: P(tail) ==> P(Cons(head, tail))
  ensures forall list :: P(list)
  