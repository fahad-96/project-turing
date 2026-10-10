import Mathlib

namespace TuringTask

theorem resultant_cyclotomic_eq_one (m n : Nat) (hn : 1 <= n) (hnm : n < m)
    (h : forall p k : Nat, p.Prime -> Not (m = n * p ^ k)) :
    Polynomial.resultant (Polynomial.cyclotomic m Int) (Polynomial.cyclotomic n Int) = 1 := by
  sorry

theorem resultant_cyclotomic_mul_prime_pow (n p k : Nat) (hn : 1 <= n) (hp : p.Prime)
    (hk : 1 <= k) (h : Not (n = 1 /\ p = 2 /\ k = 1)) :
    Polynomial.resultant (Polynomial.cyclotomic (n * p ^ k) Int) (Polynomial.cyclotomic n Int) =
      (p : Int) ^ n.totient := by
  sorry

theorem discr_cyclotomic (n : Nat) (hn : 1 <= n) :
    Polynomial.discr (Polynomial.cyclotomic n Int) *
        n.primeFactors.prod (fun p => (p : Int) ^ (n.totient / (p - 1))) =
      (-1) ^ (n.totient / 2) * (n : Int) ^ n.totient := by
  sorry

theorem isCoprime_cyclotomic_iff (m n : Nat) (hn : 1 <= n) (hnm : n < m) :
    IsCoprime (Polynomial.cyclotomic m Int) (Polynomial.cyclotomic n Int) <->
      forall p k : Nat, p.Prime -> Not (m = n * p ^ k) := by
  sorry

theorem resultant_cyclotomic_X_pow_sub_one (n m : Nat) (hn : 3 <= n) (hm : 1 <= m)
    (h : Not (m % n = 0)) :
    Polynomial.resultant (Polynomial.cyclotomic n Int) (Polynomial.X ^ m - 1) =
      Polynomial.eval 1 (Polynomial.cyclotomic (n / Nat.gcd n m) Int) ^
        (n.totient / (n / Nat.gcd n m).totient) := by
  sorry

end TuringTask
