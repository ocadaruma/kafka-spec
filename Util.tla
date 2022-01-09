---- MODULE Util ----
LOCAL INSTANCE Integers
LOCAL INSTANCE Sequences

Last(s) == s[Len(s)]

IsSubSeq(sub, parent) == IF sub = <<>> THEN
                            TRUE
                         ELSE
                            \E m, n \in 1..Len(parent) : m <= n /\ SubSeq(parent, m, n) = sub

Min(nums) == CHOOSE i \in nums: \A j \in nums: i <= j

Max(nums) == CHOOSE i \in nums: \A j \in nums: i >= j
====
