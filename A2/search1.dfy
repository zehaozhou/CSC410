method Find(a: array<nat>) returns (index: int)
    requires forall i,j :: (0 <= i < a.Length && 0 <= j < a.Length && i != j) ==> a[i] != a[j]
    requires forall i,j :: (0 <= i < a.Length && 0 <= j < a.Length && i < j) ==> a[i] < a[j]
    ensures 0 <= index ==> index < a.Length && a[index] == index
    ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != k
{
    if a.Length == 0 { return -1;}
    if a[0] == 0 { return 0;}

    index := a.Length - 1;
    while index > 0 
        invariant forall k :: (0 <= k && index < k < a.Length) ==> a[k] != k 
    {
        if a[index] == index { return; }

        if a[0] == 0 { return 0;}

        index := index - 1;
    }

    return -1;
}