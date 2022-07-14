
// test
function gcd(a: nat, b: nat): nat
   requires a > 0 && b > 0
{   
   if a == b then a else
   if b > a then gcd(a,b - a) else
    gcd(a - b,b) 
}
    
  