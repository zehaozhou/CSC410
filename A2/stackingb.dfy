function sum(a: seq<nat>): int
    requires forall i :: 0 <= i < |a| ==> a[i] >= 1
{
    if |a| == 0 then 0 else sum(a[1..]) + a[0] * (a[0] - 1) / 2
}

lemma sum_nonnegative(a: seq<nat>)
    requires forall i :: 0 <= i < |a| ==> a[i] >= 1
    ensures sum(a) >= 0
{
}

lemma split_seq2(a: seq<nat>, a1: seq<nat>, a2: seq<nat>)
    requires forall k :: 0 <= k < |a| ==> a[k] >= 1
    requires a1 + a2 == a
    requires forall i :: 0 <= i < |a1| ==> a1[i] >= 1
    requires forall i :: 0 <= i < |a2| ==> a2[i] >= 1
    ensures sum(a1) + sum(a2) == sum(a)
{
    if |a1| == 0 {        
        assert a2 == a;
    } else {
        split_seq2(a[1..], a1[1..], a2);
    }
}

lemma split_seq3(a: seq<nat>, a1: seq<nat>, a2: seq<nat>, a3: seq<nat>)
    requires forall k :: 0 <= k < |a| ==> a[k] >= 1
    requires a1 + a2 + a3 == a
    requires forall i :: 0 <= i < |a1| ==> a1[i] >= 1
    requires forall i :: 0 <= i < |a2| ==> a2[i] >= 1
    requires forall i :: 0 <= i < |a3| ==> a3[i] >= 1
    ensures sum(a1) + sum(a2) + sum(a3) == sum(a)
{
    split_seq2(a1 + a2, a1, a2);
    split_seq2(a, a1 + a2, a3);
}

lemma divisible(n: nat)
    ensures (n * (n - 1)) % 2 == 0
{
    if n == 0 {
    } else {
        divisible(n - 1);

        calc == {
            (n - 1) * (n - 2);
            (n - 1) * n - (n - 1) * 2;
        }
    }
}

lemma divisible2(n: nat, m: nat) 
    ensures (2 * n * m) % 2 == 0 && (2 * n * m) / 2 == n * m
{
    assert 2 * (n * m) == 2 * n * m;
}

lemma factorable(k: nat)
    ensures k * k - k == k * (k - 1)
{
}

lemma factorable2(j: nat, k: nat)
    ensures j * (j - 1) + k * (k - 1) + 2 * j * k == (j + k) * (j + k) - (j + k)
{
}

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

        ghost var prev_score := score;
        ghost var prev_sub1 := stacks[..i];
        ghost var prev_sub2 := stacks[i + 1..];
        ghost var prev_sum1 := sum(stacks[..i]);
        ghost var prev_sum2 := sum(stacks[i + 1..]);
        ghost var prev_sum := sum(stacks);
        ghost var split_val := stacks[i];

        split_seq3(stacks, stacks[..i], [split_val], stacks[i + 1..]);
        
        if stacks[i] == 1 {
            stacks := stacks[..i] + stacks[i + 1..];
            split_seq2(stacks, prev_sub1, prev_sub2);
        } else {
            var j, k :| stacks[i] == j + k && j > 0 && k > 0;
            score := score + j * k;

            assert prev_sum1 + split_val * (split_val - 1) / 2 + prev_sum2 == prev_sum;

            stacks := [j, k] + stacks[..i] + stacks[i + 1..];

            split_seq3(stacks, [j, k], prev_sub1, prev_sub2);

            calc == {
                sum(stacks);
                sum([j, k]) + prev_sum1 + prev_sum2;
                j * (j - 1) / 2 + sum([k]) + prev_sum1 + prev_sum2;
                j * (j - 1) / 2 + k * (k - 1) / 2 + prev_sum1 + prev_sum2;
            }

            factorable(split_val);
            factorable2(j, k);
            
            calc == {
                j * (j - 1) + k * (k - 1) + 2 * j * k;
                (j + k) * (j + k) - (j + k);
                split_val * split_val - split_val;
                split_val * split_val - split_val * 1;
                split_val * (split_val - 1);
            }

            divisible(j);
            divisible(k);
            divisible2(j, k);

            calc ==> {
                j * (j - 1) + k * (k - 1) + 2 * j * k == split_val * (split_val - 1);
                (j * (j - 1) + k * (k - 1) + 2 * j * k) / 2 == split_val * (split_val - 1) / 2;
                j * (j - 1) / 2 + k * (k - 1) / 2 + j * k == split_val * (split_val - 1) / 2;
                j * (j - 1) / 2 + k * (k - 1) / 2 + prev_sum1 + prev_sum2 + j * k == prev_sum1 + split_val * (split_val - 1) / 2 + prev_sum2;
                j * (j - 1) / 2 + k * (k - 1) / 2 + prev_sum1 + prev_sum2 + j * k == prev_sum;
                sum(stacks) + j * k == prev_sum;
                n * (n - 1) / 2 - prev_sum + j * k == n * (n - 1) / 2 - sum(stacks);
                prev_score + j * k == n * (n - 1) / 2 - sum(stacks);
                score == n * (n - 1) / 2 - sum(stacks);
            }

        }

        assert |stacks| >= 0;

        divisible(n);
        sum_nonnegative(stacks);

        calc == {
            n * (n - 1) - 2 * score;
            n * (n - 1) - 2 * (n * (n - 1) / 2 - sum(stacks));
            2 * sum(stacks);
        }

        assert n * (n - 1) - 2 * score >= 0;
    }

    return;
}