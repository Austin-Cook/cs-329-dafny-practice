module lecture
{
  method f(a: array?<int>)
    modifies a
    requires a != null
    ensures
      if (a.Length > 3) then
        && a[2] == 42
        && (forall i | 0 <= i < a.Length && i != 2 :: a[i] == old(a[i]))
      else
        && (forall i | 0 <= i < a.Length :: a[i] == old(a[i]))
  {
    if (a.Length > 3) {
      a[2] := 42;
    }
  }

  method {:test} given_arrayOfLengthFour_when_callingF_then_arrayAtIndexTwoIsFortyTwo()
  {
    // given
    var a := new int[4];
    for i := 0 to a.Length
      invariant (forall j | 0 <= j < i :: a[j] == 0)
    {
      a[i] := 0;
    }

    // when
    f(a);

    // then
    assert(a[2] == 42);
    assert(forall i | 0 <= i < a.Length && i != 2 :: a[i] == 0);
  }
}
