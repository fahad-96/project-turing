import TuringTask.Basic

open TuringTask

example (K : Type*) [Field K] [Fintype K]
    (hK : Fintype.card K % 2 = 1) (P Q : Polynomial K) (hP : P.Monic) (hQ : Q.Monic)
    (hP' : Irreducible P) (hQ' : Irreducible Q) (hPQ : Not (P = Q)) :
    ((exists A : Polynomial K, (A ^ 2 - P) % Q = 0) <->
        (exists B : Polynomial K, (B ^ 2 - Q) % P = 0)) <->
      (Fintype.card K % 4 = 1 \/ P.natDegree % 2 = 0 \/ Q.natDegree % 2 = 0) :=
  TuringTask.isSquare_mod_iff_isSquare_mod_iff K hK P Q hP hQ hP' hQ' hPQ

example (K : Type*) [Field K] [Fintype K] (Q : Polynomial K)
    (hQ : Q.Monic) (hQ' : Irreducible Q) (c : K) :
    (exists A : Polynomial K, (A ^ 2 - (Polynomial.X - Polynomial.C c)) % Q = 0) <->
      IsSquare ((-1) ^ Q.natDegree * Q.eval c) :=
  TuringTask.isSquare_X_sub_C_mod_iff K Q hQ hQ' c

example (K : Type*) [Field K] [Fintype K] (Q : Polynomial K)
    (hQ' : Irreducible Q) (c : K) :
    (exists A : Polynomial K, (A ^ 2 - Polynomial.C c) % Q = 0) <->
      (IsSquare c \/ Q.natDegree % 2 = 0) :=
  TuringTask.isSquare_C_mod_iff K Q hQ' c

example (K : Type*) [Field K] [Fintype K] (n : Nat) :
    ((n * Nat.card {P : Polynomial K // P.Monic /\ Irreducible P /\ P.natDegree = n} : Nat) :
        Int) =
      Finset.sum (Nat.divisors n)
        (fun d => ArithmeticFunction.moebius d * (Fintype.card K : Int) ^ (n / d)) :=
  TuringTask.card_monic_irreducible K n

example (K : Type*) [Field K] [Fintype K] (d : Nat) :
    Finset.prod Finset.univ (fun c : Fin d -> K =>
        Polynomial.X ^ d +
          Finset.sum Finset.univ (fun i : Fin d => Polynomial.C (c i) * Polynomial.X ^ (i : Nat))) =
      Finset.prod (Finset.range d)
        (fun i => Polynomial.X ^ (Fintype.card K ^ d) - Polynomial.X ^ (Fintype.card K ^ i)) :=
  TuringTask.prod_monic_eq_prod_X_pow_sub_X_pow K d

#print axioms TuringTask.isSquare_mod_iff_isSquare_mod_iff
#print axioms TuringTask.isSquare_X_sub_C_mod_iff
#print axioms TuringTask.isSquare_C_mod_iff
#print axioms TuringTask.card_monic_irreducible
#print axioms TuringTask.prod_monic_eq_prod_X_pow_sub_X_pow
