import Mathlib

namespace TuringTask

theorem prime_eq_sq_add_five_mul_sq_iff (p : Nat) (hp : p.Prime) :
    (exists x y : Nat, p = x ^ 2 + 5 * y ^ 2) <->
      (p = 5 \/ Membership.mem ({1, 9} : Finset Nat) (p % 20)) := by
  sorry

theorem mul_eq_sq_add_five_mul_sq (p q : Nat) (hp : p.Prime) (hq : q.Prime)
    (hp20 : Membership.mem ({3, 7} : Finset Nat) (p % 20))
    (hq20 : Membership.mem ({3, 7} : Finset Nat) (q % 20)) :
    exists x y : Nat, p * q = x ^ 2 + 5 * y ^ 2 := by
  sorry

theorem prime_eq_sq_add_six_mul_sq_iff (p : Nat) (hp : p.Prime) :
    (exists x y : Nat, p = x ^ 2 + 6 * y ^ 2) <->
      Membership.mem ({1, 7} : Finset Nat) (p % 24) := by
  sorry

theorem prime_eq_sq_add_thirteen_mul_sq_iff (p : Nat) (hp : p.Prime) :
    (exists x y : Nat, p = x ^ 2 + 13 * y ^ 2) <->
      (p = 13 \/ Membership.mem ({1, 9, 17, 25, 29, 49} : Finset Nat) (p % 52)) := by
  sorry

theorem prime_eq_sq_add_twenty_one_mul_sq_iff (p : Nat) (hp : p.Prime) :
    (exists x y : Nat, p = x ^ 2 + 21 * y ^ 2) <->
      Membership.mem ({1, 25, 37} : Finset Nat) (p % 84) := by
  sorry

end TuringTask
