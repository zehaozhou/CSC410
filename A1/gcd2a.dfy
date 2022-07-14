include "gcd.dfy"

// given for 2a
predicate divides(a: nat, b:nat)
    requires a > 0
{
    exists k: nat :: b == k * a
}


// given in class
lemma dividesLemma(a: nat, b: nat)
    requires a > 0 && b > 0
    ensures gcd(a, b) > 0
    ensures divides(gcd(a, b), a) && divides(gcd(a, b), b)
{
    if a == b {
        assert a == 1 * a;
        assert b == 1 * b;
    } 
    else if b > a {
        dividesLemma(a, b - a);

        var k :| a == k * gcd(a, b - a);
        var j :| b - a == j * gcd(a, b - a);

        calc == {
            a;
            k * gcd(a, b - a);
            k * gcd(a, b);
        }

        calc == {
            b;
            b - a + a;
            j * gcd(a, b - a) + a;
            j * gcd(a, b) + k * gcd(a, b);
            (j + k) * gcd(a, b);
        }
    } 
    else { // a > b
        dividesLemma(a - b, b);

        var k :| b == k * gcd(a - b, b);
        var j :| a - b == j * gcd(a - b, b);

        calc == {
            b;
            k * gcd(a - b, b);
            k * gcd(a, b);
        }

        calc == {
            a;
            a - b + b;
            j * gcd(a - b, b) + b;
            j * gcd(a, b) + k * gcd(a, b);
            (j + k) * gcd(a, b);
        }
    }
}


// given in class
lemma largest(a: nat, b: nat, k: nat)
    requires a > 0 && b > 0
    requires k > 0 && divides(k, a) && divides(k, b)
    ensures k <= gcd(a, b)
{
    if a == b {}
    else if b > a {
        // gcd(a, b) == gcd(a, b - a)
        // largest(a, b - a)
        // k > 0 && k | a && k | b - a ==> k <= gcd(a, b - a)

        var i :| a == i * k;
        var j :| b == j * k;

        calc == {
            b - a;
            j * k - i * k;
            (j - i) * k;
        }
    }
    else {
        var i :| a == i * k;
        var j :| b == j * k;

        calc == {
            a - b;
            i * k - j * k;
            (i - j) * k;
        }
    }
}


// given in class
lemma distributivity(a: nat, b: nat, m: nat) 
    requires a > 0 && b > 0 && m > 0
    ensures m * gcd(a, b) == gcd(m * a, m * b)
{
    if a == b 
    {}
    else if b > a
    {}
    else // a > b
    {
        calc {
            m * gcd(a, b);
            // ==
            // m * gcd(a - b, b);
            ==
            gcd(m * a - m * b, m * b);
            ==
            gcd(m * a, m * b);
        }
    }
}


// WTS: forall k, a, b : nat :: k|a && k|b ==> k|gcd(a, b)
// so basically every common divisor divides the gcd
lemma CommonDivisor(k: nat, a: nat, b: nat)
    // k > 0 cuz can't divide 0, a & b > 0 cuz requirement for gcd
    requires k > 0 && a > 0 && b > 0
    ensures divides(k, a) && divides(k, b) ==> divides(k, gcd(a, b))
{
    if k > gcd(a, b) {
        // essentially the correctness of gcd
        // Dafny needs to know that k does not divide a or b
        dividesLemma(a, b);
        forall n | n > 0 && divides(n, a) && divides(n, b) {
            largest(a, b, n);
        }
    }
    else if !divides(k, a) || !divides(k, b) {
        // this is needed so that the assertion below works
    }
    else {
    	// just to make sure this pre-req is true so everything that follows will work
        assert k <= gcd(a, b) && divides(k, a) && divides(k, b);

        var i :| a == i * k;
        var j :| b == j * k;

        distributivity(i, j, k);
        calc == {
            k * gcd(i, j);
            gcd(k * i, k * j);
            gcd(i * k, j * k);
            gcd(a, b);
        }

        assert gcd(a, b) == gcd(i, j) * k;
    }
}
