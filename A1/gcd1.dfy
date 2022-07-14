include "gcd.dfy"
lemma commutative(a: nat, b: nat)
    requires a > 0 && b > 0
    ensures gcd(a, b) == gcd(b, a)
{
}

lemma SubCancelation(a: nat, b: nat, m: nat)
    requires a > 0 && b > 0
    ensures m * b > a ==> gcd(m * b - a, b) == gcd(a,b)
    ensures m * b < a ==> gcd(a - m * b, b) == gcd(a,b)
{
    /* induction on m, base case */
    if m == 0 { 
    } /* all cases below are for the inductive step, m > 0 */
    else if m * b < a {
        SubCancelation(a, b, m - 1);

        assert m * (b - 1) < a;
        assert m * b - a - b == (m - 1) * b - a;
    } else if m * b > a && (m - 1) * b > a {
        SubCancelation(a, b, m - 1);
        
        assert a - m * b == a - (m - 1) * b - b;
    } // the sign flips in this case
    else if m * b > a && (m - 1) * b < a {
        SubCancelation(a, b, m - 1);
        commutative(a - (m - 1) * b, b);

        calc == {
            gcd(m * b - a, b);
            gcd(m * b - a, b - (m * b - a));
            gcd(m * b - a, b - m * b + a);
            gcd(m * b - a, a - m * b + b);
            gcd(m * b - a, a - (m * b - b));
            gcd(m * b - a, a - (m - 1) * b);
            gcd(b - a + (m - 1) * b, a - (m - 1) * b);
            gcd(b - (a - (m - 1) * b), a - (m - 1) * b);
            gcd(b, a - (m - 1) * b);
            gcd(a - (m - 1) * b, b);
        }
    } // equality case auto-verified
    else if m * b > a && (m - 1) * b == a {
    }
}