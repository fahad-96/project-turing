import Mathlib

namespace TuringTask

theorem card_sq_add_mul_add_sq (n : Nat) (hn : 0 < n) :
    ((Finset.filter (fun v : Prod Int Int => v.1 ^ 2 + v.1 * v.2 + v.2 ^ 2 = (n : Int))
        (Finset.product (Finset.Icc (-(n : Int)) n) (Finset.Icc (-(n : Int)) n))).card : Int) =
      6 * Finset.sum (Nat.divisors n) (fun d => jacobiSym (d : Int) 3) := by
  sorry

theorem card_sq_add_three_mul_sq (n : Nat) (hn : 0 < n) :
    ((Finset.filter (fun v : Prod Int Int => v.1 ^ 2 + 3 * v.2 ^ 2 = (n : Int))
        (Finset.product (Finset.Icc (-(n : Int)) n) (Finset.Icc (-(n : Int)) n))).card : Int) =
      2 * Finset.sum (Nat.divisors n) (fun d => jacobiSym (d : Int) 3) +
        4 * Finset.sum (Finset.filter (fun d => d % 4 = 0) (Nat.divisors n))
          (fun d => jacobiSym ((d / 4 : Nat) : Int) 3) := by
  sorry

theorem card_sq_add_two_mul_sq (n : Nat) (hn : 0 < n) :
    ((Finset.filter (fun v : Prod Int Int => v.1 ^ 2 + 2 * v.2 ^ 2 = (n : Int))
        (Finset.product (Finset.Icc (-(n : Int)) n) (Finset.Icc (-(n : Int)) n))).card : Int) =
      2 * Finset.sum (Nat.divisors n) (fun d => jacobiSym (-2) d) := by
  sorry

theorem card_sq_add_mul_add_two_mul_sq (n : Nat) (hn : 0 < n) :
    ((Finset.filter (fun v : Prod Int Int => v.1 ^ 2 + v.1 * v.2 + 2 * v.2 ^ 2 = (n : Int))
        (Finset.product (Finset.Icc (-(n : Int)) n) (Finset.Icc (-(n : Int)) n))).card : Int) =
      2 * Finset.sum (Nat.divisors n) (fun d => jacobiSym (d : Int) 7) := by
  sorry

theorem card_sq_add_seven_mul_sq (n : Nat) (hn : 0 < n) :
    ((Finset.filter (fun v : Prod Int Int => v.1 ^ 2 + 7 * v.2 ^ 2 = (n : Int))
        (Finset.product (Finset.Icc (-(n : Int)) n) (Finset.Icc (-(n : Int)) n))).card : Int) =
      2 * Finset.sum (Nat.divisors n) (fun d => jacobiSym (d : Int) 7) -
        4 * Finset.sum (Finset.filter (fun d => d % 2 = 1 /\ n / d % 2 = 0)
          (Nat.divisors n)) (fun d => jacobiSym (d : Int) 7) := by
  sorry

end TuringTask
