import TuringTask.Basic

open TuringTask

example (m n : Nat) (hm : 0 < m) (z : Complex)
    (hz : IsPrimitiveRoot z m) :
    (exists e : Fin n -> Nat, Finset.sum Finset.univ (fun i => z ^ e i) = 0) <->
      exists c : Nat -> Nat, n = Finset.sum m.primeFactors (fun p => c p * p) :=
  TuringTask.exists_sum_pow_eq_zero_iff m n hm z hz

example (m : Nat) (z : Complex) (hz : IsPrimitiveRoot z m)
    (a : Nat -> Int) :
    Finset.sum (Finset.range m) (fun k => (a k : Complex) * z ^ k) = 0 <->
      exists b : Nat -> Nat -> Int, forall k, k < m ->
        a k = Finset.sum m.primeFactors
          (fun p => Finset.sum (Finset.range p) (fun j => b p ((k + j * (m / p)) % m))) :=
  TuringTask.sum_mul_pow_eq_zero_iff m z hz a

example (m : Nat) (hm : m.primeFactors.card <= 2)
    (z : Complex) (hz : IsPrimitiveRoot z m) (a : Nat -> Nat)
    (ha : Finset.sum (Finset.range m) (fun k => (a k : Complex) * z ^ k) = 0) :
    exists b : Nat -> Nat -> Nat, forall k, k < m ->
      a k = Finset.sum m.primeFactors
        (fun p => Finset.sum (Finset.range p) (fun j => b p ((k + j * (m / p)) % m))) :=
  TuringTask.exists_nonneg_of_sum_mul_pow_eq_zero m hm z hz a ha

example (k : Nat) (a : Fin k -> Int) (z : Fin k -> Complex)
    (hz : forall i, exists n, 0 < n /\ z i ^ n = 1)
    (hsum : Finset.sum Finset.univ (fun i => (a i : Complex) * z i) = 0)
    (hmin : forall S : Finset (Fin k),
      Finset.sum S (fun i => (a i : Complex) * z i) = 0 -> S.card = 0 \/ S.card = k) :
    forall i j, (z i / z j) ^ primorial k = 1 :=
  TuringTask.div_pow_primorial_eq_one k a z hz hsum hmin

example (n : Nat) :
    (exists A : Matrix (Fin 6) (Fin 6) Int, orderOf A = n) <->
      Membership.mem
        ({0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 18, 20, 24, 30} : Finset Nat) n :=
  TuringTask.exists_orderOf_eq_iff n

#print axioms TuringTask.exists_sum_pow_eq_zero_iff
#print axioms TuringTask.sum_mul_pow_eq_zero_iff
#print axioms TuringTask.exists_nonneg_of_sum_mul_pow_eq_zero
#print axioms TuringTask.div_pow_primorial_eq_one
#print axioms TuringTask.exists_orderOf_eq_iff
