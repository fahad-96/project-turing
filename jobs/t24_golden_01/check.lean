import TuringTask.Basic

open TuringTask

example (n : Nat) (hn : 0 < n) :
    exists k : Nat, 0 < k /\ k <= 6 * n /\ Nat.fib k % n = 0 /\ Nat.fib (k + 1) % n = 1 % n :=
  TuringTask.pisano_le_six_mul n hn

example (n : Nat) (hn : 0 < n) :
    (Nat.fib (6 * n) % n = 0 /\ Nat.fib (6 * n + 1) % n = 1 % n /\
      forall k : Nat, 0 < k -> k < 6 * n ->
        Not (Nat.fib k % n = 0 /\ Nat.fib (k + 1) % n = 1 % n)) <->
      exists j : Nat, 0 < j /\ n = 2 * 5 ^ j :=
  TuringTask.pisano_eq_six_mul_iff n hn

example (n : Nat) (hn : 0 < n) :
    (Nat.fib n % n = 0 /\ Nat.fib (n + 1) % n = 1 % n /\
      forall k : Nat, 0 < k -> k < n ->
        Not (Nat.fib k % n = 0 /\ Nat.fib (k + 1) % n = 1 % n)) <->
      (n = 1 \/ exists j : Nat, n = 24 * 5 ^ j) :=
  TuringTask.pisano_eq_self_iff n hn

example (n : Nat) (hn : 0 < n) :
    (Nat.fib (2 * n) % n = 0 /\ forall k : Nat, 0 < k -> k < 2 * n -> 0 < Nat.fib k % n) <->
      exists j : Nat, n = 6 * 5 ^ j :=
  TuringTask.entry_eq_two_mul_iff n hn

example (n : Nat) (hn : 0 < n) :
    (Nat.fib n % n = 0 /\ forall k : Nat, 0 < k -> k < n -> 0 < Nat.fib k % n) <->
      ((exists j : Nat, n = 5 ^ j) \/ exists j : Nat, n = 12 * 5 ^ j) :=
  TuringTask.entry_eq_self_iff n hn

#print axioms TuringTask.pisano_le_six_mul
#print axioms TuringTask.pisano_eq_six_mul_iff
#print axioms TuringTask.pisano_eq_self_iff
#print axioms TuringTask.entry_eq_two_mul_iff
#print axioms TuringTask.entry_eq_self_iff
