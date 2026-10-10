import Mathlib

namespace TuringTask

theorem mul_succ_smooth_seven (n : Nat)
    (h : forall p : Nat, p.Prime -> n * (n + 1) % p = 0 -> p <= 7) :
    Membership.mem ({1, 2, 3, 4, 5, 6, 7, 8, 9, 14, 15, 20, 24, 27, 35, 48, 49, 63, 80, 125, 224,
      2400, 4374} : Finset Nat) n := by
  sorry

theorem sq_sub_one_smooth_seven (x : Nat)
    (h : forall p : Nat, p.Prime -> (x ^ 2 - 1) % p = 0 -> p <= 7) :
    Membership.mem ({2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 15, 17, 19, 26, 29, 31, 41, 49, 55, 71, 97,
      99, 127, 161, 244, 251, 449, 4801, 8749} : Finset Nat) x := by
  sorry

theorem three_consecutive_smooth_seven (n : Nat)
    (h : forall p : Nat, p.Prime -> n * (n + 1) * (n + 2) % p = 0 -> p <= 7) :
    Membership.mem ({1, 2, 3, 4, 5, 6, 7, 8, 14, 48} : Finset Nat) n := by
  sorry

theorem sq_add_one_smooth_thirteen (x : Nat)
    (h : forall p : Nat, p.Prime -> (x ^ 2 + 1) % p = 0 -> p <= 13) :
    Membership.mem ({0, 1, 2, 3, 5, 7, 8, 18, 57, 239} : Finset Nat) x := by
  sorry

theorem sq_sub_two_mul_sq_smooth_thirteen (x y : Nat)
    (h : x ^ 2 = 2 * y ^ 2 + 1 \/ x ^ 2 + 1 = 2 * y ^ 2)
    (hs : forall p : Nat, p.Prime -> y % p = 0 -> p <= 13) :
    Membership.mem ({1, 2, 5, 12, 70, 169, 13860} : Finset Nat) y := by
  sorry

end TuringTask
