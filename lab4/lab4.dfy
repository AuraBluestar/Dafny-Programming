//Onisor Patricia

//ex 1
class Cell
{
    var contents : int
    constructor()
    ensures contents == 0
    {
        contents := 0;
    }

    constructor fromInt(x : int)
    ensures contents==x
    {
        contents:=x;
    }

    method setContents(x : int)
    modifies this
    ensures contents==x
    {
        contents:=x;
    }

    method getContents() returns (r : int)
    {
    return contents;
    }
}

//ex 2
method setCell(cell : Cell, x : int)
modifies cell
ensures cell.contents == x
{
    cell.setContents(x);
}

method setBoth(cell1 : Cell, x : int, cell2 : Cell, y : int)
    requires cell1!=cell2
    modifies cell1, cell2
    ensures cell1.contents==x
    ensures cell2.contents==y
{
    cell1.setContents(x);
    cell2.setContents(y);
}

method test1()
{
    var c1 := new Cell.fromInt(9);
    assert c1.contents == 9;
    var c2 := new Cell();
    setBoth(c1, 10, c2, 13);
    assert c1.contents == 10;
    assert c2.contents == 13;
}

//ex 3
class EvenNumber
{
    var x : int

    predicate Valid()
    reads this
    {
        x % 2 == 0
    }

    constructor()
    ensures Valid()
    {
        x := 0;
    }

    method increment()
    requires Valid()
    modifies this
    ensures Valid()
    {
        x := x + 2;
    }

    method square()
    requires Valid()
    modifies this
    ensures Valid()
    {
        x := x * 2;
    }

    method reset()
    requires Valid()
    modifies this
    ensures Valid(){}

    method getContents() returns (r : int)
    requires Valid()
    ensures r % 2 == 0
    {
        return x;
    }
}

class NaturalCounter
{
    var counter : int // should be a natural (i.e., >= 0)

    predicate Valid()
    reads this
    {
        counter >= 0
    }

    constructor()
    ensures Valid()
    {
        counter:=0;
    }

    method increment()
    requires Valid()
    modifies this
    ensures Valid()
    {
        counter:=counter+1;
    }

    method decrement() 
    requires Valid()
    modifies this
    ensures Valid()
    requires counter>=1
    {
        counter:=counter-1;
    }
}

//ex 4
method incrementCounter(c : NaturalCounter?)
requires c!=null ==> c.Valid()
modifies c
{
    if c != null {
    c.increment();
    }
}

//ex 5
class Node
{
    var info : int
    var next : Node? //poate fi null
    ghost var footprint : set<Node>
    ghost var contents : seq<int>

    ghost predicate Valid()
    reads this
    reads footprint
    decreases footprint
    {
        this in footprint && (next == null ==> contents == [ info ] ) && (next != null ==>
        (next in footprint && next.footprint < footprint && this !in next.footprint && contents == [info] + next.contents && next.Valid()))
    }

    constructor(i : int)
    ensures Valid()
    ensures next == null
    ensures footprint == { this }
    ensures contents == [ i ]
    {
        info := i;
        next := null;
        footprint := { this };
        contents := [ i ];
    }

    method push_front(info : int) returns (result : Node)
    requires this.Valid()
    ensures result.Valid()
    ensures result.contents == [info] + this.contents
    ensures result.footprint == { result } + this.footprint
    {
        result := new Node(info);
        result.next:=this;
        result.footprint := { result } + this.footprint;
        result.contents := [info] + this.contents;
    }
    

}
