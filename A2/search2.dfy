
predicate compare(a: array<nat>, i: nat, j: nat)
    requires 0 <= i < a.Length && 0 <= j < a.Length
    reads a
{
    a[i] + j - i <= a[j]
}
method Find(a: array<nat>) returns (index: int)
    requires forall i,j :: (0 <= i < a.Length && 0 <= j < a.Length && i != j) ==> a[i] != a[j]
    requires forall i,j :: (0 <= i < a.Length && 0 <= j < a.Length && i < j) ==> a[i] < a[j]
    ensures 0 <= index ==> index < a.Length && a[index] == index
    ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != k
{
    if a.Length == 0 { return -1;}
    if a[0] == 0 { return 0;}

    index := a.Length - 1;

    /*
    assert forall i, j :: (0 <= i < a.Length - 1 && j == i + 1) ==> compare(a, i, j);
    assert forall i, j :: (0 <= i < a.Length - 1 && i + 1 < j < a.Length) ==> (compare(a, i, j - 1) ==> compare(a, i, j));
    assert ((forall i, j :: (0 <= i < a.Length - 1 && j == i + 1) ==> compare(a, i, j)) && 
            (forall i, j :: (0 <= i < a.Length - 1 && i + 1 < j < a.Length) ==> (compare(a, i, j - 1) ==> compare(a, i, j)))) ==>
            (forall i, j :: (0 <= i < a.Length - 1 && i < j < a.Length) ==> compare(a, i, j));
    assert forall i, j :: (0 <= i < a.Length - 1 && i < j < a.Length) ==> compare(a, i, j);*/
/*
    assert ((forall i :: (0 <= i < a.Length - 1) ==> a[i] + 1 <= a[i + 1]) &&
            (forall i, j :: (0 <= i < a.Length - 1 && i + 1 < j < a.Length) ==> ((a[i] + j - 1 - i <= a[j - 1]) ==> (a[i] + j - i <= a[j])))) ==>
            (forall i, j :: (0 <= i < a.Length - 1 && i < j < a.Length) ==> a[i] + j - i <= a[j]);

    assert a[0] >= 1;*/


    assert 3/2 == 1;




    // STATEMENT T
    assert forall i, j :: (0 <= i < a.Length - 1 && i < j < a.Length) ==> a[i] + j - i <= a[j];

    // INDUCTION PROOF OF STATEMENT T, BASE CASE
    assert forall i :: (0 <= i < a.Length - 1) ==> a[i] + 1 <= a[i + 1];

    // INDUCTION STEP
    assert forall i, j :: (0 <= i < a.Length - 1 && i + 1 < j < a.Length) ==> ((a[i] + j - 1 - i <= a[j - 1]) ==> (a[i] + j - i <= a[j]));


    assert forall j :: (0 <= j < a.Length) ==> a[0] + j <= a[j]; 

    while index > 0 
    {
        if a[index] == index { return; }

        if a[0] == 0 { return 0;}

        index := index/2;
    }

    return -1;
}