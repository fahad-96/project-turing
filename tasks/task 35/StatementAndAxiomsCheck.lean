import TuringTask.Basic

open TuringTask

example (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (hK : Fintype.card K % 2 = 1) (f : Polynomial K) (hf : Squarefree f) :
    IsSquare f.discr <->
      (Multiset.card (UniqueFactorizationMonoid.normalizedFactors f) + f.natDegree) % 2 = 0 :=
  TuringTask.isSquare_discr_iff K hK f hf

example (F : Polynomial Int) (hF : F.Monic)
    (hsq : Squarefree (F.map (Int.castRingHom (ZMod 2)))) :
    F.discr % 8 = 1 <->
      (Multiset.card (UniqueFactorizationMonoid.normalizedFactors
          (F.map (Int.castRingHom (ZMod 2)))) + F.natDegree) % 2 = 0 :=
  TuringTask.discr_emod_eight_eq_one_iff F hF hsq

example (n k : Nat) (hk : 0 < k) (hkn : k < n) (a b : Int) :
    (Polynomial.X ^ n + Polynomial.C a * Polynomial.X ^ k + Polynomial.C b).discr =
      (-1) ^ (n * (n - 1) / 2) * b ^ (k - 1) *
        ((n : Int) ^ (n / Nat.gcd n k) * b ^ (n / Nat.gcd n k - k / Nat.gcd n k) -
          (-1) ^ (n / Nat.gcd n k) * ((n - k : Nat) : Int) ^ (n / Nat.gcd n k - k / Nat.gcd n k) *
            (k : Int) ^ (k / Nat.gcd n k) * a ^ (n / Nat.gcd n k)) ^ Nat.gcd n k :=
  TuringTask.discr_trinomial n k hk hkn a b

example (n k : Nat) (hk : 0 < k) (hkn : k < n)
    (hnk : (n + k) % 2 = 1) :
    Multiset.card (UniqueFactorizationMonoid.normalizedFactors
        (Polynomial.X ^ n + Polynomial.X ^ k + 1 : Polynomial (ZMod 2))) % 2 = 0 <->
      (n % 2 = 0 /\ Not (n = 2 * k) /\ n * k / 2 % 4 <= 1) \/
        (n % 2 = 1 /\ Not (2 * n % k = 0) /\ (n % 8 = 3 \/ n % 8 = 5)) \/
          (n % 2 = 1 /\ 2 * n % k = 0 /\ (n % 8 = 1 \/ n % 8 = 7)) :=
  TuringTask.even_card_normalizedFactors_trinomial_iff n k hk hkn hnk

example (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (n : Nat) :
    Finset.sum Finset.univ (fun c : Fin n -> K =>
        (-1 : Int) ^ Multiset.card (UniqueFactorizationMonoid.normalizedFactors
          (Polynomial.X ^ n +
            Finset.sum Finset.univ
              (fun i : Fin n => Polynomial.C (c i) * Polynomial.X ^ (i : Nat))))) =
      (-1) ^ n * (Fintype.card K : Int) ^ ((n + 1) / 2) :=
  TuringTask.sum_neg_one_pow_card_normalizedFactors K n

#print axioms TuringTask.isSquare_discr_iff
#print axioms TuringTask.discr_emod_eight_eq_one_iff
#print axioms TuringTask.discr_trinomial
#print axioms TuringTask.even_card_normalizedFactors_trinomial_iff
#print axioms TuringTask.sum_neg_one_pow_card_normalizedFactors
