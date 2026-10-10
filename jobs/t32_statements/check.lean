import TuringTask.Basic

open TuringTask

example (K : Type*) [Field K] [Fintype K] (a : K) (ha : Not (a = 0))
    (n : Nat) :
    Function.Bijective (fun x : K => (Polynomial.dickson 1 a n).eval x) <->
      Nat.Coprime n (Fintype.card K ^ 2 - 1) :=
  TuringTask.dickson_bijective_iff K a ha n

example (m n : Nat) (a : ZMod m) (ha : IsUnit a) :
    Function.Bijective (fun x : ZMod m => (Polynomial.dickson 1 a n).eval x) <->
      forall p : Nat, p.Prime -> m % p = 0 ->
        Nat.Coprime n (p ^ 2 - 1) /\ (m % p ^ 2 = 0 -> Not (n % p = 0)) :=
  TuringTask.dickson_bijective_zmod_iff m n a ha

example (K : Type*) [Field K] [Fintype K] [DecidableEq K] (a : K)
    (ha : Not (a = 0)) (n : Nat) :
    (Finset.image (fun x : K => (Polynomial.dickson 1 a n).eval x) Finset.univ).card =
      ((Fintype.card K - 1) / Nat.gcd n (Fintype.card K - 1) +
          (Fintype.card K + 1) / Nat.gcd n (Fintype.card K + 1) + 1) / 2 +
        (if Not (IsSquare a) /\
            (Fintype.card K ^ 2 - 1) / Nat.gcd n (Fintype.card K ^ 2 - 1) % 4 = 2
          then 1 else 0) :=
  TuringTask.card_image_dickson K a ha n

example (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (hK : Fintype.card K % 2 = 1) (n : Nat) (hn : 1 <= n) :
    (Finset.filter (fun x : K => (Polynomial.dickson 1 (1 : K) n).eval x = x)
        Finset.univ).card =
      (Nat.gcd (n - 1) (Fintype.card K - 1) + Nat.gcd (n + 1) (Fintype.card K - 1) +
          Nat.gcd (n - 1) (Fintype.card K + 1) + Nat.gcd (n + 1) (Fintype.card K + 1)) / 2 -
        1 - n % 2 :=
  TuringTask.card_fixed_dickson_one K hK n hn

example (K : Type*) [Field K] [Fintype K] (n k : Nat) :
    Nat.iterate (fun x : K => (Polynomial.dickson 1 (1 : K) n).eval x) k = id <->
      (((n : Int) ^ k - 1) % ((Fintype.card K : Int) - 1) = 0 \/
          ((n : Int) ^ k + 1) % ((Fintype.card K : Int) - 1) = 0) /\
        (((n : Int) ^ k - 1) % ((Fintype.card K : Int) + 1) = 0 \/
          ((n : Int) ^ k + 1) % ((Fintype.card K : Int) + 1) = 0) :=
  TuringTask.iterate_dickson_one_eq_id_iff K n k

#print axioms TuringTask.dickson_bijective_iff
#print axioms TuringTask.dickson_bijective_zmod_iff
#print axioms TuringTask.card_image_dickson
#print axioms TuringTask.card_fixed_dickson_one
#print axioms TuringTask.iterate_dickson_one_eq_id_iff
