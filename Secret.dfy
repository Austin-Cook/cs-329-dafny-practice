class Secret {
  var secret: int
  var known: bool
  var count: int

  constructor Init(x: int)
    requires
      && 1 <= x <= 10
    ensures
      && secret == x
      && known == false
      && count == 0
  {
    secret := x;
    known := false;
    count := 0;
  }

  method Guess(g: int) returns (result: bool, guesses: int)
    modifies this`known, this`count
    requires
      && known == false
    ensures
      && count == old(count) + 1
      && (if g == secret then
            known == true
          else
            known == false)
      && result == known
      && guesses == count
  {
    count := count + 1;
    known := (g == secret);
    return known, count;
  }

}

method {:test} test() {
  var s:= new Secret.Init(5);

  var result: bool := false;
  var guesses: int := 0;

  result, guesses := s.Guess(6);
  assert
    && result == false
    && guesses == 1;
  expect
    && result == false
    && guesses == 1, "ERROR: expected result == false && guesses == 1";
}
