
lemma split_seq(a: seq<nat>, a1: seq<nat>, a2: seq<nat>, a3: seq<nat>)
    requires forall k :: 0 <= k < |a| ==> a[k] >= 1
    requires a == a1 + a2 + a3
    ensures forall i :: 0 <= i < |a1| ==> a1[i] >= 1
    ensures forall i :: 0 <= i < |a2| ==> a2[i] >= 1
    ensures forall i :: 0 <= i < |a3| ==> a3[i] >= 1
    ensures sum(a1) + sum(a2) + sum(a3) == sum(a)
function sum(a: seq<nat>): int
    requires forall i :: 0 <= i < |a| ==> a[i] >= 1
{
    if |a| == 0 then 0 else sum(a[1..]) + a[0] * (a[0] - 1) / 2
}

lemma test(n: nat, score: nat) 
    ensures n * (n - 1) - 2 * score >= 0


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
            // stack length decreases by 1, score does not change

            split_seq(stacks, stacks[..i], [stacks[i]], stacks[i + 1..]);
            stacks := stacks[..i] + stacks[i + 1..];
            //assert score == n * (n - 1) / 2 - sum(stacks);
        } else {
            // stack length increases by 1, score increases at least 1

            var j, k :| stacks[i] == j + k && j > 0 && k > 0;

            ghost var prev_score := score;
            ghost var prev_sum := sum(stacks);
            ghost var t1 := stacks[..i];
            ghost var val := stacks[i];
            ghost var t2 := stacks[i + 1..];
            assert prev_score == n * (n - 1) / 2 - prev_sum;

            split_seq(stacks, stacks[..i], [val], stacks[i + 1..]);
            assert sum(stacks[..i]) + sum([val]) + sum(stacks[i + 1..]) == prev_sum;
            assert sum(t1) + val * (val - 1) / 2 + sum(t2) == prev_sum;

            score := score + j * k;
            stacks := [j, k] + stacks[..i] + stacks[i + 1..];

            assert score == prev_score + j * k;
            split_seq(stacks, [j, k], t1, t2);
            assert sum([j, k]) + sum(t1) + sum(t2) == sum(stacks);
            assert j * (j - 1) / 2 + sum([k]) + sum(t1) + sum(t2) == sum(stacks);
            assert j * (j - 1) / 2 + k * (k - 1) / 2 + sum(t1) + sum(t2) == sum(stacks);
            assert j * (j - 1) / 2 + k * (k - 1) / 2 + k * j + sum(t1) + sum(t2) == sum(stacks) + k * j;
            assert (j * j - j) / 2 + (k * k - k) / 2 + k * j + sum(t1) + sum(t2) == sum(stacks) + k * j;
            assert 2 * ((j * j - j) / 2 + (k * k - k) / 2 + k * j + sum(t1) + sum(t2)) == 2 * (sum(stacks) + k * j);
            assert 2 * (j * j - j) / 2 + 2 * (k * k - k) / 2 + 2 * k * j + 2 * sum(t1) + 2 * sum(t2) == 2 * sum(stacks) + 2 * k * j;
            assert j * j - j + k * k - k + 2 * (k * j + sum(t1) + sum(t2)) == 2 * sum(stacks) + 2 * k * j;
        }
        assert |stacks| >= 0;
        test(n, score);

    }

    return;
}