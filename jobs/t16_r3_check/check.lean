import TuringTask.Basic

open TuringTask

example (n x : Nat) (h : Nat.fib n = x ^ 2) :
    n = 0 \/ n = 1 \/ n = 2 \/ n = 12 :=
  TuringTask.fib_eq_sq n x h

example (n x : Nat) (hn : 1 <= n) (h : Nat.fib (n - 1) + Nat.fib (n + 1) = x ^ 2) :
    n = 1 \/ n = 3 :=
  TuringTask.lucas_eq_sq n x hn h

example (n x : Nat) (h : Nat.fib n = 2 * x ^ 2) :
    n = 0 \/ n = 3 \/ n = 6 :=
  TuringTask.fib_eq_two_mul_sq n x h

example (n x : Nat) (hn : 1 <= n)
    (h : Nat.fib (n - 1) + Nat.fib (n + 1) = 2 * x ^ 2) :
    n = 6 :=
  TuringTask.lucas_eq_two_mul_sq n x hn h

example (n k : Nat) (h : Nat.fib n = 2 ^ k) :
    n = 1 \/ n = 2 \/ n = 3 \/ n = 6 :=
  TuringTask.fib_eq_two_pow n k h

#print axioms TuringTask.fib_eq_sq
#print axioms TuringTask.lucas_eq_sq
#print axioms TuringTask.fib_eq_two_mul_sq
#print axioms TuringTask.lucas_eq_two_mul_sq
#print axioms TuringTask.fib_eq_two_pow
