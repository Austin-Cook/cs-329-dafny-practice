// uses functional programming (1, (2, (3, null)))
// outermost is head, innermost is tail
// snock adds to end of list (tail/innermost)
// cons adds to front of the list (head/outermost)
// shift removes the head (outermost) and makes the rest be one level up
class List {
  // container for the list's elements
  var a: array?<int>
  // current size of the list
  var size: nat
  // nat is non negative integers (easier than annotating everything as non negative)

  ghost predicate isValid()
    reads this
  {
    && a != null
    && a.Length > 0
    && 0 <= size <= a.Length
  }

  constructor init(len: int)
    requires len > 0
    ensures
      && fresh(a)
      && a.Length == len
      && size == 0
      && isValid()
  {
    a := new int[len];
    size := 0;
  }

  method snoc(e: int)
    modifies `size, a
    requires
      && isValid()
      && size < a.Length
    ensures
      && a[old(size)] == e
      && (forall i | 0 <= i < old(size) :: a[i] == old(a[i]))
      && size == old(size + 1)
      && isValid()
  {
    a[size] := e;
    size := size + 1;
  }

  method shift()
    modifies a, `size
    requires
      && isValid()
      && size > 0
    ensures
      && size == old(size) - 1
      && (forall i | 0 <= i < size :: a[i] == old(a[i + 1]))
  {
    forall (i | 0 <= i < size - 1) {
      a[i] := a[i + 1];
    }
    size := size - 1;
  }

  method head() returns (h: int)
    requires
      && isValid()
    ensures
      && h == a[0]
  {
    h := a[0];
  }
}

method {:test} test()
{
  var list := new List.init(4);
  var aux : int;

  list.snoc(2);
  aux := list.head();
  assert (aux == 2);

  list.snoc(3);
  list.snoc(4);
  aux := list.head();
  assert (aux == 2);

  list.shift();
  aux := list.head();
  assert (aux == 3);
}
