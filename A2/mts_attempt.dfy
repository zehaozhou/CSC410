// Helper function to give the functional specification
function sum(s : seq<int>) : int
{
    if s == [] then 0 else sum(s[..|s| -1]) + s[|s| - 1]
}


lemma maxLemma(i:int, a:array<int>, vals: seq<int>)
    requires 0<=i<=a.Length;
    requires |vals|==a.Length+1;
    requires vals[0]==0;
    requires forall j :: 0<=j<=i-1==> (vals[j]+a[j]<=0 ==> vals[j+1]==0);
    requires forall j :: 0<=j<=i-1==> (vals[j]+a[j]>0==>vals[j+1]==vals[j]+a[j]);
    ensures forall k :: 0 <= k <= i  ==>  vals[i] >= sum(a[k..i]) {
        if i==0{
            assert vals[i]==0==sum(a[i..i]);
        }
        else{
            if vals[i-1]+a[i-1]<=0{
                assert vals[i]==0>=vals[i-1]+a[i-1];
                maxLemma(i-1,a,vals);
                // Q: Why not use forall{} clause?  A: If so, Dafny complains that it is not visible outside the clauase and the lemma does not hold.
                assert forall r :: 0 <= r <= i-1==>vals[i-1]>= sum(a[r..i-1]);
                assert forall r :: 0 <= r <= i-1==>a[r..i-1]+a[i-1..i]==a[r..i];
                assert forall r :: 0 <= r <= i-1==>sum(a[i-1..i]) == a[i-1];
                assert forall r :: 0 <= r <= i-1==>sum(a[r..i])==sum(a[r..i-1])+sum(a[i-1..i]);
                assert forall r :: 0 <= r <= i-1==>sum(a[r..i-1])+sum(a[i-1..i])==sum(a[r..i-1])+a[i-1];
                assert forall r :: 0 <= r <= i-1==>vals[i]>=vals[i-1]+a[i-1]>=sum(a[r..i-1])+a[i-1]==sum(a[r..i]);
                assert forall r :: 0 <= r <= i-1==>vals[i]>= sum(a[r..i]);
                assert forall r :: 0 <= r <= i-1==>vals[i]==0==sum(a[i..i]);
                assert forall r :: 0 <= r <= i-1==>vals[i] >= sum(a[r..i]);

            }
            else{
                assert vals[i-1]+a[i-1]>0;
                assert vals[i]==vals[i-1]+a[i-1]>0;
                maxLemma(i-1,a,vals);
                assert forall k :: 0 <= k <= i-1==>vals[i-1]>= sum(a[k..i-1]);
                assert forall k :: 0 <= k <= i-1==>a[k..i-1]+a[i-1..i]==a[k..i];
                assert a[i-1]==sum(a[i-1..i]);
                assert forall k :: 0 <= k <= i-1==>vals[i-1]+a[i-1]>=sum(a[k..i-1])+sum(a[i-1..i])==sum(a[k..i]);
                assert forall k :: 0 <= k <= i-1==>vals[i]>=sum(a[k..i]) && vals[i]>0==sum(a[i..i]);
                assert forall r :: 0 <= r <= i  ==>  vals[i] >= sum(a[r..i]);

            }

        }

    }

lemma existLemma(i:int, a:array<int>, vals: array<int>)
    requires 0<=i<=a.Length;
    requires vals.Length==a.Length+1;
    requires vals[0]==0;
    requires forall j :: 0<=j<=i-1==> vals[j+1]==0 || vals[j+1]==vals[j]+a[j];
    ensures exists k :: 0 <= k <= i  && sum(a[k..i]) == vals[i]{
        if i==0{
            assert vals[i]==0==sum(a[i..i]);
        }
        else{
            if vals[i]==0{
                assert vals[i]==0==sum(a[i..i]);
            }
            else{
                existLemma(i-1,a,vals);
                var r :| 0 <= r <= i-1  && sum(a[r..i-1]) == vals[i-1];
                assert a[r..i-1]+a[i-1..i]==a[r..i];
                assert vals[i]==vals[i-1]+a[i-1]==sum(a[r..i-1])+a[i-1]==sum(a[r..i-1])+sum(a[i-1..i])==sum(a[r..i]);

            }

        }

    }

// The code of Maximum Tail Sum (MTS) computation

method MTS(a: array<int>) returns (mts: int)
    ensures forall i :: 0 <= i < a.Length  ==> sum(a[i..]) <= mts // postcondition for part (a)
    ensures exists i :: 0 <= i <= a.Length  && sum(a[i..]) == mts // postcondition for part (b)
    {
        var i := 0;
        mts := 0;

				// Records the maximum sum of subarray ends at but not including a[i] for each i (at the end of iteration i, for i=0 to a.Length)
        var b := new int[a.Length+1];

        assert b.Length==a.Length+1;


        while i < a.Length
        invariant 0<= i<= a.Length
        invariant mts >= 0

        {
           	b[i]:= mts; // becomes old mts at b[i-1] after the increament of i by 1
            // Q: Why having this extra step?  A: Otherwise Dafny wouldn't realize b[i]==0 || b[i]==b[i-1]+a[i-1];
            // But now Dafny disagrees with b[0]==0 

            mts := if mts + a[i] > 0 then mts + a[i]  else 0;

            i := i + 1;
            b[i]:=mts;
            
            assert b[i]==0 || b[i]==b[i-1]+a[i-1]; // ???
            existLemma(i,a,b); //???


        }
    }
