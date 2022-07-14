function sum(a: seq<nat>): int
    requires forall i :: 0 <= i < |a| ==> a[i] >= 1
{
    if |a| == 0 then 0 else sum(a[1..]) + a[0] * (a[0] - 1) / 2
}

lemma split_seq(a: seq<nat>, a1: seq<nat>, a2: seq<nat>, a3: seq<nat>)
    requires forall k :: 0 <= k < |a| ==> a[k] >= 1
    requires a == a1 + a2 + a3
    ensures forall i :: 0 <= i < |a1| ==> a1[i] >= 1
    ensures forall i :: 0 <= i < |a2| ==> a2[i] >= 1
    ensures forall i :: 0 <= i < |a3| ==> a3[i] >= 1
    ensures sum(a1) + sum(a2) + sum(a3) == sum(a)
{}

method Game(n: nat) returns (score: nat)
    requires n > 0
    ensures score == n * (n - 1) / 2
{
    var stacks := [n];
    score := 0;

    while |stacks| > 0
        invariant forall i :: 0 <= i < |stacks| ==> stacks[i] >= 1
        invariant score == n * (n - 1) / 2 - sum(stacks)
        decreases (n * (n - 1) - 2 * score) + |stacks|
    {
        var i :| 0 <= i < |stacks|;
        if stacks[i] == 1 {
            stacks := stacks[..i] + stacks[i + 1..];
        } else {
            var j, k :| stacks[i] == j + k && j > 0 && k > 0;

            ghost var prev_score := score;
            ghost var prev_sub1 := stacks[..i];
            ghost var prev_sub2 := stacks[i + 1..];
            ghost var val := stacks[i];
            ghost var prev_sum := sum(stacks);


            score := score + j * k;


            split_seq(stacks, stacks[..i], [val], stacks[i + 1..]);

            stacks := [j, k] + stacks[..i] + stacks[i + 1..];

            split_seq(stacks, [j, k], prev_sub1, prev_sub2);

            calc == {
                j * (j - 1) + k * (k - 1) + 2 * j * k;
                j * j - j + k * k - k + 2 * j * k;
                j * j + 2 * j * k + k * k - k - j;
                j * j + 2 * j * k + k * k - (k + j);
                j * j + j * k + j * k + k * k - (k + j);
                j * (j + k) + k * (j + k) - (k + j);
                (j + k) * (j + k) - (k + j);
                val * val - val;
                val * val - val * 1;
                val * (val - 1);
            }

            calc ==> {
                prev_score + j * k == n * (n - 1) / 2 - sum(stacks);
                score == n * (n - 1) / 2 - sum(stacks);
            }
        }
    }

    return;
}