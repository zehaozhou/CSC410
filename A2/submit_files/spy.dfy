function method unpair(n: nat): (nat, nat)
{
    // Add an implementation for this
    if n == 0 then (0, 0) else
    var (x, y) := unpair(n-1);
    if x == 0 then (y + 1, 0) else (x - 1, y + 1)

}

function method pick(i: nat): nat
{
  var (x, y) := unpair(i);
  x + i * y
}

lemma find_pair(a: nat, b: nat)
  requires a >= 0 && b >= 0
  ensures a == unpair(((a + b) * (a + b + 1) / 2) + b).0
  ensures b == unpair(((a + b) * (a + b + 1) / 2) + b).1
  decreases a + b, b
{
  if a == 0 && b == 0 {
    assert a == unpair(0).0;
    assert b == unpair(0).1;
  } 
  else if a > 0 && b == 0
  {
    find_pair(0, a - 1);
  } 
  else // b > 0
  {
    var (x, y) := (a + 1, b - 1);
    find_pair(x, y);
    var k := ((x + y) * (x + y + 1) / 2) + y;
    assert x == unpair(k).0;
    assert y == unpair(k).1;
  } 

}

method catchTheSpy(a: nat, b: nat)
{
var t := 0;
  // prove that this loop terminates and therefore the spy is caught
  var k := ((a + b) * (a + b + 1) / 2) + b;
  find_pair(a, b);
  while a + t * b != pick(t)
    invariant t <= k;
    decreases k-t;
    { t := t + 1; }
}