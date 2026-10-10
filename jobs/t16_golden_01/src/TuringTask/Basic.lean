import Mathlib
import TuringTask.Equations

namespace TuringTask

theorem fib_eq_sq (n x : Nat) (h : Nat.fib n = x ^ 2) :
    n = 0 \/ n = 1 \/ n = 2 \/ n = 12 := by
  exact fib_eq_sq_cases n x h

theorem lucas_eq_sq (n x : Nat) (hn : 1 <= n) (h : Nat.fib (n - 1) + Nat.fib (n + 1) = x ^ 2) :
    n = 1 \/ n = 3 := by
  exact lucNat_eq_sq_cases n x hn h

theorem fib_eq_two_mul_sq (n x : Nat) (h : Nat.fib n = 2 * x ^ 2) :
    n = 0 \/ n = 3 \/ n = 6 := by
  exact fib_eq_two_mul_sq_cases n x h

theorem lucas_eq_two_mul_sq (n x : Nat) (hn : 1 <= n)
    (h : Nat.fib (n - 1) + Nat.fib (n + 1) = 2 * x ^ 2) :
    n = 6 := by
  exact lucNat_eq_two_mul_sq_cases n x hn h

theorem fib_eq_two_pow (n k : Nat) (h : Nat.fib n = 2 ^ k) :
    n = 1 \/ n = 2 \/ n = 3 \/ n = 6 := by
  exact fib_eq_two_pow_cases n k h

end TuringTask
