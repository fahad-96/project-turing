import Mathlib

namespace TuringTask

theorem dickson_bijective_iff (K : Type*) [Field K] [Fintype K] (a : K) (ha : Not (a = 0))
    (n : Nat) :
    Function.Bijective (fun x : K => (Polynomial.dickson 1 a n).eval x) <->
      Nat.Coprime n (Fintype.card K ^ 2 - 1) := by
  sorry

theorem dickson_bijective_zmod_iff (m n : Nat) (a : ZMod m) (ha : IsUnit a) :
    Function.Bijective (fun x : ZMod m => (Polynomial.dickson 1 a n).eval x) <->
      forall p : Nat, p.Prime -> m % p = 0 ->
        Nat.Coprime n (p ^ 2 - 1) /\ (m % p ^ 2 = 0 -> Not (n % p = 0)) := by
  sorry

theorem card_image_dickson (K : Type*) [Field K] [Fintype K] [DecidableEq K] (a : K)
    (ha : Not (a = 0)) (n : Nat) :
    (Finset.image (fun x : K => (Polynomial.dickson 1 a n).eval x) Finset.univ).card =
      ((Fintype.card K - 1) / Nat.gcd n (Fintype.card K - 1) +
          (Fintype.card K + 1) / Nat.gcd n (Fintype.card K + 1) + 1) / 2 +
        (if Not (IsSquare a) /\
            (Fintype.card K ^ 2 - 1) / Nat.gcd n (Fintype.card K ^ 2 - 1) % 4 = 2
          then 1 else 0) := by
  sorry

theorem card_fixed_dickson_one (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (hK : Fintype.card K % 2 = 1) (n : Nat) (hn : 1 <= n) :
    (Finset.filter (fun x : K => (Polynomial.dickson 1 (1 : K) n).eval x = x)
        Finset.univ).card =
      (Nat.gcd (n - 1) (Fintype.card K - 1) + Nat.gcd (n + 1) (Fintype.card K - 1) +
          Nat.gcd (n - 1) (Fintype.card K + 1) + Nat.gcd (n + 1) (Fintype.card K + 1)) / 2 -
        1 - n % 2 := by
  sorry

theorem iterate_dickson_one_eq_id_iff (K : Type*) [Field K] [Fintype K] (n k : Nat) :
    Nat.iterate (fun x : K => (Polynomial.dickson 1 (1 : K) n).eval x) k = id <->
      (((n : Int) ^ k - 1) % ((Fintype.card K : Int) - 1) = 0 \/
          ((n : Int) ^ k + 1) % ((Fintype.card K : Int) - 1) = 0) /\
        (((n : Int) ^ k - 1) % ((Fintype.card K : Int) + 1) = 0 \/
          ((n : Int) ^ k + 1) % ((Fintype.card K : Int) + 1) = 0) := by
  sorry

end TuringTask
