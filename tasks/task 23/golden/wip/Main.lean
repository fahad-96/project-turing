import Mathlib
import TuringTask.Stormer

/-!
# The five statements

The theorems of the task, stated as in `TuringTask/Basic.lean`, with proofs from `Stormer.lean`.
-/

namespace TuringTask

theorem main_mul_succ (n : Nat)
    (h : forall p : Nat, p.Prime -> n * (n + 1) % p = 0 -> p <= 7) :
    Membership.mem ({1, 2, 3, 4, 5, 6, 7, 8, 9, 14, 15, 20, 24, 27, 35, 48, 49, 63, 80, 125, 224,
      2400, 4374} : Finset Nat) n :=
  mul_succ_smooth h

theorem main_sq_sub_one (x : Nat)
    (h : forall p : Nat, p.Prime -> (x ^ 2 - 1) % p = 0 -> p <= 7) :
    Membership.mem ({2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 15, 17, 19, 26, 29, 31, 41, 49, 55, 71, 97,
      99, 127, 161, 244, 251, 449, 4801, 8749} : Finset Nat) x :=
  sq_sub_one_smooth h

theorem main_three (n : Nat)
    (h : forall p : Nat, p.Prime -> n * (n + 1) * (n + 2) % p = 0 -> p <= 7) :
    Membership.mem ({1, 2, 3, 4, 5, 6, 7, 8, 14, 48} : Finset Nat) n :=
  three_smooth h

theorem main_sq_add_one (x : Nat)
    (h : forall p : Nat, p.Prime -> (x ^ 2 + 1) % p = 0 -> p <= 13) :
    Membership.mem ({0, 1, 2, 3, 5, 7, 8, 18, 57, 239} : Finset Nat) x :=
  sq_add_one_smooth h

theorem main_pell (x y : Nat)
    (h : x ^ 2 = 2 * y ^ 2 + 1 \/ x ^ 2 + 1 = 2 * y ^ 2)
    (hs : forall p : Nat, p.Prime -> y % p = 0 -> p <= 13) :
    Membership.mem ({1, 2, 5, 12, 70, 169, 13860} : Finset Nat) y :=
  pell_smooth h hs

end TuringTask
