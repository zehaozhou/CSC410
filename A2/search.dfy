lemma greaterValues(a: array<nat>, hi: nat)
    requires a.Length > 0 && 0 <= hi < a.Length
    requires forall i,j :: (0 <= i < a.Length && 0 <= j < a.Length && i != j) ==> a[i] != a[j]
    requires forall i,j :: (0 <= i < a.Length && 0 <= j < a.Length && i < j) ==> a[i] < a[j]
    ensures forall k :: 0 <= k <= hi ==> a[k] >= k
{
    if hi == 0 {

    }
    else {
        greaterValues(a, hi - 1);
        assert a[hi] >= a[hi - 1] + 1;
    }
}

lemma strictlyGreater(a: array<nat>, lo: nat, hi: nat)
    requires a.Length > 0 && 0 <= lo <= hi < a.Length
    requires forall i,j :: (0 <= i < a.Length && 0 <= j < a.Length && i != j) ==> a[i] != a[j]
    requires forall i,j :: (0 <= i < a.Length && 0 <= j < a.Length && i < j) ==> a[i] < a[j]
    ensures a[lo] != lo ==> forall k :: lo <= k <= hi ==> a[k] > k
{
    greaterValues(a, hi);
    if hi == lo {

    }
    else {
        strictlyGreater(a, lo, hi - 1);
        assert a[lo] != lo ==> a[hi - 1] > hi - 1;
    }
}


method Find(a: array<nat>) returns (index: int)
    requires forall i,j :: (0 <= i < a.Length && 0 <= j < a.Length && i != j) ==> a[i] != a[j]
    requires forall i,j :: (0 <= i < a.Length && 0 <= j < a.Length && i < j) ==> a[i] < a[j]
    ensures 0 <= index ==> index < a.Length && a[index] == index
    ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != k
{
    if a.Length == 0 { return -1;}
    if a[0] == 0 { return 0;}
    
    strictlyGreater(a, 0, a.Length - 1);

    index := a.Length - 1;
    while index > 0 
    {

        if a[index] == index { return; }

        if a[0] == 0 { return 0;}

        index := index/2;

    }

    return -1;
}