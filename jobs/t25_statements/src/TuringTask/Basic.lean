import Mathlib

namespace TuringTask

theorem fib_add_one_eq_sq_iff (n : Nat) :
    (exists x : Nat, Nat.fib n + 1 = x ^ 2) <-> Membership.mem ({0, 4, 6} : Finset Nat) n := by
  sorry

theorem fib_eq_sq_add_one_iff (n : Nat) :
    (exists x : Nat, Nat.fib n = x ^ 2 + 1) <-> Membership.mem ({1, 2, 3, 5} : Finset Nat) n := by
  sorry

theorem fib_eq_two_mul_sq_add_one_iff (n : Nat) :
    (exists x : Nat, Nat.fib n = 2 * x ^ 2 + 1) <->
      Membership.mem ({1, 2, 4} : Finset Nat) n := by
  sorry

theorem lucas_eq_sq_add_one_iff (n : Nat) :
    (exists x : Nat, Nat.fib n + (x ^ 2 + 1) = 2 * Nat.fib (n + 1)) <->
      Membership.mem ({0, 1} : Finset Nat) n := by
  sorry

theorem lucas_add_one_eq_two_mul_sq_iff (n : Nat) :
    (exists x : Nat, Nat.fib n + 2 * x ^ 2 = 2 * Nat.fib (n + 1) + 1) <->
      Membership.mem ({1, 4, 11} : Finset Nat) n := by
  sorry

end TuringTask
