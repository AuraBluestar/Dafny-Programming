// Onisor Maria-Patricia 3A1

//1

function abs(x : int) : int
{
  if x > 0 then
    x
  else
    -x
}

//2
predicate isEven(x : int)
{
  x%2==0
}

//3
function factorial(n : int) : int
  requires n >= 0
  decreases n
{
  if n==0 then 1 else n*factorial(n-1)
}

//4
datatype List = Nil | Cons(head : int, tail : List)

function sum(l : List) : int
  decreases l
{
  match l {
    case Nil => 0
    case Cons(head, tail) => 1 + sum(tail)
  }
}

//5
function allPozitive(l : List) : bool
  decreases l
{
  match l {
    case Nil => true
    case Cons(head, tail) => head > 0 && allPozitive(tail)
  }
}

//6
//a
predicate all(l: seq<int>, p: int -> bool)
{
  forall i :: 0 <= i < |l| ==> p(l[i])
}

//b
function map1(l : List, f : int -> int) : List
{
  match l
  {
    case Nil => Nil
    case Cons(head, tail) => Cons(f(head), map1(tail, f))
  }
}

//c
function filter(l : List, f : int -> bool) : List
{
  match l
  {
    case Nil => Nil
    case Cons(head, tail) =>
      if (f(head)) then Cons(head, filter(tail, f))
      else filter(tail,f)
  }
}

//d

function reduce(l : List, init : int, f : int -> int -> int) : int
{
  match l
  {
    case Nil => init
    case Cons(head, tail) => f(head)(reduce(tail, init, f))
  }
}

function reduce1(l : List, init : int, f : (int, int)-> int) : int
{
  match l
  {
    case Nil => init
    case Cons(head, tail) => f(head, reduce1(tail, init, f))
  }
}

//7

//a
function sumSeq(s1 : seq<int>) : int
{
  if |s1| == 0
  then 0
  else
    s1[0] + sumSeq(s1[1..])
}

//b
function ListToSeq(l :List) : seq<int>
{
  var s := [];
  match l
  {
    case Nil => s
    case Cons(head, tail) => [head] + ListToSeq(tail)
  }
}

//c
ghost predicate allIncreasing(s : seq<int>)
{
  forall i :: 0 <= i < |s|-1 ==> s[i] <= s[i+1]
}

//d
ghost predicate allDistinct(s : seq<int>)
{
  forall i, j :: 0 <= i < |s| && 0 <= j < |s| && i!=j ==> s[i]!=s[j]
}

//e
method getWord(text : string) returns(result: seq<char>)
{
  var text := "Hello, World!";
  result := text[0..5];
}

//8

//a
ghost predicate pozitive( s : set<int>)
{
  forall i :: i in s ==> i>=0
}

//b
function seqToSet(s: seq<int>): set<int>
{
  if |s| == 0 then
    {}
  else
    seqToSet(s[1..]) + {s[0]}
}

//9
datatype BST = Leaf | Node(info : int, leaf: BST, right: BST)

//10
function values(bst : BST): set <int>
{
  match bst{
    case Leaf => { }
    case Node(info, left, right)=>
      values(left) + { info } + values(right)
  }
}

//11
predicate isBST(bst: BST, min: int, max: int) {
  match bst {
    case Leaf => true
    case Node(info, left, right) =>
      min < info && info < max &&
      isBST(left, min, info) &&
      isBST(right, info, max)
  }
}

method Main()
{
  //pt 7.a
  var s1 : seq<int> := [ 1, 2, 3 ];
  print sumSeq(s1);
  //pt 7.b
  var lista := Cons(1, Cons(2, Cons(3, Nil)));
  print ListToSeq(lista);
}