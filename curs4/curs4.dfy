class Cell
  {
  var contents : int

  constructor()
    ensures contents == 0
  {
    contents := 0;
  }

  constructor fromInt(x : int)
    ensures contents == x
  {
    contents := x;
  }

  method getContents() returns (r : int)
    ensures r == contents
  {
    return contents;
  }

  method setContents(x : int)
    ensures contents == x
    modifies this // cadrul (frame-ul) metodei
  {
    contents := x;
  }
}

method update(s : seq<Cell>)
  requires |s| == 2
  requires s[0] != s[1]
  modifies s
{
  s[0].setContents(42);
  s[1].setContents(13);
  assert s[1].contents == 13;
  assert s[0].contents == 42;// || s[0].contents == 13;
}

method update'(s : seq<Cell>)
  requires |s| >= 2
  requires forall i , j :: 0 <= i < j < |s| ==> s[i] != s[j]
  modifies s
{
  for i := 0 to |s|
    invariant forall i' :: 0 <= i' < i ==> s[i'].contents == i'
  {
    s[i].setContents(i);
  }
}

method example()
{
  var c1 : Cell := new Cell();
  var c2 : Cell := new Cell.fromInt(13);
  c1.setContents(42);
  // ?
  assert c2.contents == 13;
}

method Main()
{
  var c1 : Cell := new Cell();
  var c2 : Cell := new Cell.fromInt(13);
  assert c1.contents == 0;
  assert c2.contents == 13;
  var r1 := c1.getContents();
  assert r1 == 0;
  // assert 0 == c1.getContents();
}
class Rational
  {
  var n : int
  var m : int // nu permit m == 0

  ghost predicate valid()
    reads this
  {
    m != 0
  }

  ghost function value() : real
    reads this
    requires this.valid()
  {
    (n as real) / (m as real)
  }

  constructor(n' : int, m' : int)
    requires m' != 0
    ensures valid()
    ensures n == n'
    ensures m == m'
  {
    n := n';
    m := m';
  }

  constructor fromInt(x : int)
    ensures valid()
    ensures value() == x as real
  {
    n := x;
    m := 1;
  }

  method add(o : Rational) returns (r : Rational)
    requires this.valid()
    requires o.valid()
    ensures r.valid()
    ensures r.value() == this.value() + o.value()
  {
    // n / m + o.n / o.m = n * o.m / m * o.m + o.n * m / o.m * m
    var newn : int := n * o.m +  o.n * m;
    var newm : int := m * o.m;
    r := new Rational(newn, newm);
    calc {
      value() + o.value();
    ==
      (n as real) / (m as real) + (o.n as real) / (o.m as real);
    ==
      (((n as real) * (o.m as real)) / ((m as real) * (o.m as real))) +
      ((o.n as real) * (m as real)) / ((o.m as real) * (m as real));
    ==
      ((n * o.m) as real) / ((m * o.m) as real) +
      ((o.n * m) as real) / ((o.m * m) as real);
    ==
      (((n * o.m) as real) + ((o.n * m) as real)) / ((m * o.m) as real);
    ==
      (((n * o.m) + (o.n * m)) as real) / ((m * o.m) as real);
    ==
      newn as real / newm as real;
    ==
      r.value();
    }
  }

  method add'(o : Rational)
    //requires this != o
    requires this.valid()
    requires o.valid()
    ensures this.valid()
    modifies this
    ensures this.value() == old(this.value()) + old(o.value())
  {
    // n / m + o.n / o.m = n * o.m / m * o.m + o.n * m / o.m * m
    calc {
      old(value()) + o.value();
    ==
      (n as real) / (m as real) + (o.n as real) / (o.m as real);
    ==
      (((n as real) * (o.m as real)) / ((m as real) * (o.m as real))) +
      ((o.n as real) * (m as real)) / ((o.m as real) * (m as real));
    ==
      ((n * o.m) as real) / ((m * o.m) as real) +
      ((o.n * m) as real) / ((o.m * m) as real);
    ==
      (((n * o.m) as real) + ((o.n * m) as real)) / ((m * o.m) as real);
    ==
      (((n * o.m) + (o.n * m)) as real) / ((m * o.m) as real);
    }
    assert old(value()) + o.value() == (((n * o.m) + (o.n * m)) as real) / ((m * o.m) as real);
    n := n * o.m + o.n * m;
    m := m * o.m;
    assert value() == (n as real) / (m  as real);
  }
}function sumSeq(s : seq<int>) : int
{
  if |s| == 0 then
    0
  else
    s[0] + sumSeq(s[1..])
}

class Node
  {
  var value : int
  var next : Node?
  ghost var len : int
  ghost var repr : set<Node>
  ghost var values : seq<int>

  ghost predicate valid()
    reads this
    reads this.repr
    //reads if next != null then { next } else { }
    // reads this.next
    // reads this.next.next
    // reads this.next.next.next
    decreases len
  {
    len >= 0 &&
    this in repr &&
    (next == null ==> len == 1 && repr == { this } && values == [ value ] ) &&
    (next != null ==>
       next in repr &&
       next.repr < repr &&
       this !in next.repr &&
       |values| > 0 &&
       values[0] == value &&
       this.next.values == values[1..] &&
       this.len == this.next.len + 1 &&
       this.next.valid()
    )
  }

  constructor(x : int)
    ensures value == x
    ensures next == null
    ensures valid()
  {
    value := x;
    next := null;
    len := 1;
    repr := { this };
    values := [ x ];
  }

  method push_front(x : int) returns (r : Node)
    requires valid()
    ensures r.valid()
  {
    r := new Node(x);
    r.next := this;
    r.repr := { r } + this.repr;
    r.len := 1 + this.len;
    r.values := [ x ] + this.values;
  }

  // ghost function len() : int
  //   reads this
  // {
  //   if next == null then
  //     0
  //   else
  //     1 + next.len()
  // }

  method sum() returns (r : int)
    // // as avea nevoie de: this e aciclic
    // decreases * // <--- nu am ce scrie aici...
    requires valid()
    decreases len
    ensures r == sumSeq(values)
  {
    if (this.next == null) {
      return value;
    } else {
      var s' := next.sum();
      return value + s';
    }
  }
}

method example1()
  decreases *
{
  var n1 : Node := new Node(13);
  var n2 : Node := new Node(14);
  var n3 : Node := new Node(42);
  assert n3.valid();
  n2.next := n3;
  n2.values := [ n2.value ] + n3.values;
  n2.len := 1 + n3.len;
  n2.repr := { n2 } + n3.repr;
  assert n2.valid();

  n1.next := n2;
  n1.values := [ n1.value ] + n2.values;
  n1.len := 1 + n2.len;
  n1.repr := { n1 } + n2.repr;
  assert n1.valid();

  var n0 := n1.push_front(0); // 0, 13, 14, 42
  assert n0.valid();
}

method example'()
{
  var n1 : Node := new Node(13);
  var n2 : Node := new Node(14);
  n1.next := n2;
  n2.next := n1;
}
trait Printable // putin ca o interfata sau o clasa abstracta
  {
  var log : string
  method Print()
}

class Cell1 extends Printable
  {
  var x : int
  method Print()
  {
    print log;
    print x;
  }
}

// nu pot extinde o clasa
// class Cell' extends Cell
// {
// }

class Rational1 extends Printable
  {
  var n : int
  var m : int

  method Print()
  {
    print log;
    print n, "/", m;
  }
}

// nu exista protected, public, private

trait Complex
  {
  method getX() returns (r : real)
  method getY() returns (r : real)
  method getAngle() returns (r : real)
  method getAmplitude() returns (r : real)
}

class Complex1 extends Complex
  {
  var x : real
  var y : real
  constructor()
  {
    x := 0 as real;
    y := 0 as real;
  }
  method getX() returns (r : real)
  {
    return x;
  }
  method getY() returns (r : real)
  {
    return y;
  }
  method getAngle() returns (r : real)
  {
    return 0.0; // ar trebui calculat mai complicat
  }
  method getAmplitude() returns (r : real)
  {
    return 0.0; // ar trebui calculat mai complicat
  }
}

class Complex2 extends Complex
  {
  var unghi : real
  var magnitudine : real
  constructor()
  {
    unghi := 0 as real;
    magnitudine := 0 as real;
  }
  method getX() returns (r : real)
  {
    return 0 as real;
    //return magnitudine * cos(unghi);
  }
  method getY() returns (r : real)
  {
    return 0 as real;
    //    return y;
  }
  method getAngle() returns (r : real)
  {
    return unghi;
  }
  method getAmplitude() returns (r : real)
  {
    return magnitudine;
  }
}

method exempluClient()
{
  var c : Complex := new Complex1();
  var d : Complex := new Complex2();
  var a := c.getX();
  var b := d.getY();
}