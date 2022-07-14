// Helper function to give the functional specification
function sum(s : seq<int>) : int
{
    if s == [] then 0 else sum(s[..|s| -1]) + s[|s| - 1]
}

lemma sum_append(a: seq<int>)
    ensures forall i, j, a1 :: 0 <= i <= |a| && 0 <= j <= |a| && j < i && a1 == a[j..i] ==> sum(a1) == sum(a[j..i - 1]) + a[i - 1]
{   
    assert forall i, j, a1 :: 0 <= i <= |a| && 0 <= j <= |a| && j < i && a1 == a[j..i] ==> a[i - 1] == a1[|a1| - 1];
    assert forall i, j, a1 :: 0 <= i <= |a| && 0 <= j <= |a| && j < i && a1 == a[j..i] ==> a[j..i - 1] == a1[..|a1| - 1];
}

// The code of Maximum Tail Sum (MTS) computation

method MTS(a: array<int>) returns (mts: int)
    ensures forall i :: 0 <= i < a.Length  ==> sum(a[i..]) <= mts // postcondition for part (a)
    ensures exists i :: 0 <= i <= a.Length  && sum(a[i..]) == mts // postcondition for part (b)
{
    var i := 0;  
    mts := 0;
   
   assert sum(a[i..i]) == mts;

    while i < a.Length
        invariant i <= a.Length
        invariant forall k :: (0 <= k < i < a.Length ==> sum(a[k..i]) <= mts) && (0 <= k < i == a.Length ==> sum(a[k..]) <= mts)
        invariant exists k :: (0 <= k <= i < a.Length && sum(a[k..i]) == mts) || (0 <= k <= i == a.Length && sum(a[k..]) == mts)
    {
        assert exists k :: 0 <= k <= i < a.Length && sum(a[k..i]) == mts;
        ghost var condition_sum := mts + a[i];
        ghost var k :| 0 <= k <= i < a.Length && sum(a[k..i]) == mts;
        
        mts := if mts + a[i] > 0 then mts + a[i]  else 0;        
        i := i + 1; 

        sum_append(a[..]);

        assert 0 <= mts;
        assert i == a.Length ==> forall k :: 0 <= k < i ==> a[k..] == a[k..a.Length - 1] + a[a.Length - 1..];

        assert sum(a[i..i]) == 0;
        assert condition_sum <= 0 ==> exists k :: (0 <= k <= i < a.Length && sum(a[k..i]) == mts) || (0 <= k <= i == a.Length && sum(a[k..]) <= mts);
        assert condition_sum > 0 ==> mts == sum(a[k..i - 1]) + a[i - 1] == sum(a[k..i]);
        assert condition_sum > 0 ==> exists k :: (0 <= k <= i < a.Length && sum(a[k..i]) == mts) || (0 <= k <= i == a.Length && sum(a[k..]) <= mts);
    }
}