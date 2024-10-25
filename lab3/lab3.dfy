//Onisor Maria-Patricia A1

//1
method ContainsDuplicates(arr: array<int>) returns (res: bool)
{
  res := false;

  var n := arr.Length;

  for i := 0 to n
  {
    for j := i + 1 to n
    {
      if arr[i] == arr[j] {
        res := true;
        return;
      }
    }
  }
}


//2
method ContainsDuplicatesGeneric<T(==)>(arr: array<T>) returns (res: bool)
{
  res := false;

  var n := arr.Length;

  for i := 0 to n
  {
    for j := i + 1 to n
    {
      if arr[i] == arr[j] {
        res := true;
        return;
      }
    }
  }
}



//3
datatype Maybe<T> = Just(what : T) | Nothing
{
  predicate IsFailure()
  {
    this.Nothing?
  }
  function PropagateFailure() : Maybe<T>
  {
    this
  }
  function Extract() : T
    requires this.Just?
  {
    this.what
  }
}

method ContainsDuplicatesMaybe(arr: array<int>) returns (result: Maybe<(int, int)>)
{
  var n := arr.Length;

  for i := 0 to n
  {
    for j := i + 1 to n
    {
      if arr[i] == arr[j] {
        return Just((i, j));
      }
    }
  }

  return Nothing;
}

//4
datatype Status<T> =
  | Success(value: T)
  | Failure(error: string)
{

  predicate IsFailure() { this.Failure? }

  function PropagateFailure(): Status<T> { this }

  function Extract(): T requires this.Success?{ this.value }
}

method Callee(i: int) returns (r: Status<int>)
{
  if i == 0 {
    return Failure("negative");
  }
  return Success((100 / i) + 10);
}

method Caller(i: int) returns (r: Status<int>)
{
  var x: int :- Callee(i);
  return Success(x);
}

//5
method swapinArray(a: array<int>, x: int, y:int)
  modifies a
  requires 0<=x<=a.Length-1 && 0<=y<=a.Length-1
{
  var t:=a[x];
  a[x]:=a[y];
  a[y]:=t;
}

//6
method insert(a: array<int>, n: int)
  modifies a
  requires 0<=n<a.Length
{
  var key := a[n];
  var i := n - 1;
  while i >= 0 && a[i] > key
  {
    a[i + 1] := a[i];
    i := i - 1;
  }
  a[i + 1] := key;

}
method insertSort(a: array<int>)
  modifies a
{
  for i := 0 to a.Length
  {
    insert(a, i);
  }
}

//7
method unique(a: array<int>) returns(r: array<int>)
    requires a.Length > 0
    ensures r.Length > 0
{
    var temp := new int[a.Length];
    temp[0] := a[0];
    var uniqueCount := 1;
    
    for i := 1 to a.Length
        invariant 1 <= uniqueCount <= temp.Length
        invariant uniqueCount <= a.Length 
    {
        var isUnique := true;
        
        for j := 0 to uniqueCount - 1
            invariant 0 <= j < uniqueCount
        {
            if a[i] == temp[j] {
                isUnique := false;
                break;
            }
        }
        
        if isUnique {
            assert uniqueCount < temp.Length;
            temp[uniqueCount] := a[i];
            uniqueCount := uniqueCount + 1;
        }
    }
    
    r := new int[uniqueCount];

    for i := 0 to uniqueCount - 1
        invariant 0 <= i < r.Length
    {
        r[i] := temp[i];
    }
}


//8
method unique2<T(==)>(arr: array<T>) returns (res: array<T>)
  requires arr.Length > 0
  requires arr != null
{
  var n := arr.Length;
  var temp := []; 
  var count := 0;

  for i := 0 to n - 1 {
    var isUnique := true;
    
    if count > 0 {
      for j := 0 to count - 1 {
        if arr[i] == temp[j] {
          isUnique := false;
          break;
        }
      }
    }
    
    if isUnique {
      temp := temp + [arr[i]]; 
      count := count + 1;
    }
  }

  if count > 0 {
    res := new T[count];
    for k := 0 to count - 1 {
      res[k] = temp[k];
    }
  } else {
    res := new T[0]; 
  }
}


//9
method compact(a: array<int>) returns (r: array<int>)
  requires a.Length > 0
  ensures r.Length <= a.Length
  modifies a
{
  var uniqueCount := 1;

  for i := 1 to a.Length
    invariant 1 <= uniqueCount <= i <= a.Length
  {
    if a[i] != a[i - 1] {
      a[uniqueCount] := a[i];
      uniqueCount := uniqueCount + 1;
    }
  }

  r := new int[uniqueCount];

  for i := 0 to uniqueCount {
    r[i] := a[i];
  }
}

//10
method CountingSort(arr: array<int>) returns (sorted: array<int>)
  requires arr != null
  ensures sorted.Length == arr.Length
{
  if arr.Length == 0 {
    sorted := new int[0];
    return;
  }

  var min := arr[0];
  var max := arr[0];

  for i := 1 to arr.Length  {
    if arr[i] < min {
      min := arr[i];
    }
    if arr[i] > max {
      max := arr[i];
    }
  }

  if max < min {
    min := max;
  }

  var range := max - min + 1;

  var count := new int[range];

  for i := 0 to arr.Length {
    if 0 <= arr[i] - min < count.Length {
      count[arr[i] - min] := count[arr[i] - min] + 1;
    }
  }

  sorted := new int[arr.Length];
  var index := 0;

  for i := 0 to count.Length - 1 {
    while count[i] > 0 {
      if index < sorted.Length {
        sorted[index] := i + min;
      }

      index := index + 1;
      count[i] := count[i] - 1;
    }
  }
}


//11
method MergeSort(left: array<int>, right: array<int>) returns (result: array<int>)
    requires left != null && right != null
    ensures result.Length == left.Length + right.Length
{
    result := new int[left.Length + right.Length]; 
    var i := 0;
    var j := 0;
    var k := 0;

    while i < left.Length && j < right.Length
        invariant 0 <= i <= left.Length
        invariant 0 <= j <= right.Length
        invariant 0 <= k <= result.Length
    {
        if left[i] <= right[j] {
            result[k] := left[i];
            i := i + 1;
        } else {
            result[k] := right[j];
            j := j + 1;
        }
        k := k + 1;
    }

    while i < left.Length
        invariant 0 <= i <= left.Length
        invariant 0 <= k <= result.Length
    {
        result[k] := left[i];
        i := i + 1;
        k := k + 1;
    }

    while j < right.Length
        invariant 0 <= j <= right.Length
        invariant 0 <= k <= result.Length
    {
        result[k] := right[j];
        j := j + 1;
        k := k + 1;
    }

    assert k == result.Length;
}

method Main()
{
  var array1 : array<int> := new int[10];
  array1[0]:=1;
  array1[1]:=1;
  array1[2]:=2;
  array1[3]:=1;

  print "Array înainte de swap: ";
  var i := 0; 
  while i < array1.Length 
  {
    print array1[i]; 
    i := i + 1; 
  }

  print "\n"; 
  var hasDuplicates1 := ContainsDuplicates(array1);
  print hasDuplicates1;
  hasDuplicates1:= ContainsDuplicatesGeneric(array1);
  print hasDuplicates1;
  swapinArray(array1, 0,2);

  var ii := 0; 
  print "\n";
  while ii < array1.Length 
  {
    print array1[ii];
    ii := ii + 1; 
  }
}
