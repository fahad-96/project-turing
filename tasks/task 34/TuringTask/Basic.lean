import Mathlib

namespace TuringTask

theorem exists_sum_pow_eq_zero_iff (m n : Nat) (hm : 0 < m) (z : Complex)
    (hz : IsPrimitiveRoot z m) :
    (exists e : Fin n -> Nat, Finset.sum Finset.univ (fun i => z ^ e i) = 0) <->
      exists c : Nat -> Nat, n = Finset.sum m.primeFactors (fun p => c p * p) := by
  sorry

theorem sum_mul_pow_eq_zero_iff (m : Nat) (z : Complex) (hz : IsPrimitiveRoot z m)
    (a : Nat -> Int) :
    Finset.sum (Finset.range m) (fun k => (a k : Complex) * z ^ k) = 0 <->
      exists b : Nat -> Nat -> Int, forall k, k < m ->
        a k = Finset.sum m.primeFactors
          (fun p => Finset.sum (Finset.range p) (fun j => b p ((k + j * (m / p)) % m))) := by
  sorry

theorem exists_nonneg_of_sum_mul_pow_eq_zero (m : Nat) (hm : m.primeFactors.card <= 2)
    (z : Complex) (hz : IsPrimitiveRoot z m) (a : Nat -> Nat)
    (ha : Finset.sum (Finset.range m) (fun k => (a k : Complex) * z ^ k) = 0) :
    exists b : Nat -> Nat -> Nat, forall k, k < m ->
      a k = Finset.sum m.primeFactors
        (fun p => Finset.sum (Finset.range p) (fun j => b p ((k + j * (m / p)) % m))) := by
  sorry

theorem div_pow_primorial_eq_one (k : Nat) (a : Fin k -> Int) (z : Fin k -> Complex)
    (hz : forall i, exists n, 0 < n /\ z i ^ n = 1)
    (hsum : Finset.sum Finset.univ (fun i => (a i : Complex) * z i) = 0)
    (hmin : forall S : Finset (Fin k),
      Finset.sum S (fun i => (a i : Complex) * z i) = 0 -> S.card = 0 \/ S.card = k) :
    forall i j, (z i / z j) ^ primorial k = 1 := by
  sorry

theorem exists_orderOf_eq_iff (n : Nat) :
    (exists A : Matrix (Fin 6) (Fin 6) Int, orderOf A = n) <->
      Membership.mem
        ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 18, 20, 24, 30} : Finset Nat) n := by
  sorry

end TuringTask
