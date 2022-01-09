---- MODULE Util ----
LOCAL INSTANCE Integers
LOCAL INSTANCE Sequences

Last(s) ==
    s[Len(s)]

ContainsSeq(seq, sub) ==
    IF sub = <<>> THEN TRUE
    ELSE \E m, n \in 1..Len(seq) : m <= n /\ SubSeq(seq, m, n) = sub

Min(nums) ==
    CHOOSE i \in nums: \A j \in nums: i <= j

Max(nums) ==
    CHOOSE i \in nums: \A j \in nums: i >= j
====
