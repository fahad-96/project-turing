import Mathlib

namespace TuringTask

theorem prod_coprime_emod (n : Nat) (hn : Not (n = 1)) :
    ((Finset.filter (fun k => Nat.Coprime k n) (Finset.Icc 1 n)).prod id % n = 1 \/
        (Finset.filter (fun k => Nat.Coprime k n) (Finset.Icc 1 n)).prod id % n = n - 1) /\
      ((Finset.filter (fun k => Nat.Coprime k n) (Finset.Icc 1 n)).prod id % n = n - 1 <->
        n = 2 \/ n = 4 \/
          exists p a : Nat, p.Prime /\ p % 2 = 1 /\ 1 <= a /\ (n = p ^ a \/ n = 2 * p ^ a)) := by
  sorry

theorem prod_half_emod_of_three_le (n : Nat)
    (hn : 3 <= (Finset.filter (fun p => p % 2 = 1) n.primeFactors).card) :
    (Finset.filter (fun k => Nat.Coprime k n) (Finset.Icc 1 (n / 2))).prod id % n = 1 := by
  sorry

theorem prod_half_two_primes (p q a b : Nat) (hp : p.Prime) (hq : q.Prime) (hp2 : p % 2 = 1)
    (hq2 : q % 2 = 1) (hpq : Not (p = q)) (ha : 1 <= a) (hb : 1 <= b) :
    (Finset.filter (fun k => Nat.Coprime k (p ^ a * q ^ b))
        (Finset.Icc 1 (p ^ a * q ^ b / 2))).prod id ^ 2 % (p ^ a * q ^ b) = 1 /\
      ((Finset.filter (fun k => Nat.Coprime k (p ^ a * q ^ b))
          (Finset.Icc 1 (p ^ a * q ^ b / 2))).prod id % (p ^ a * q ^ b) = 1 \/
        (Finset.filter (fun k => Nat.Coprime k (p ^ a * q ^ b))
          (Finset.Icc 1 (p ^ a * q ^ b / 2))).prod id % (p ^ a * q ^ b) =
          p ^ a * q ^ b - 1 <->
        p % 4 = 1 /\ q % 4 = 1) := by
  sorry

theorem prod_half_sq_add_one (p a n : Nat) (hp : p.Prime) (hp4 : p % 4 = 1)
    (hn : n = p ^ a \/ n = 2 * p ^ a) :
    ((Finset.filter (fun k => Nat.Coprime k n) (Finset.Icc 1 (n / 2))).prod id ^ 2 + 1) %
      n = 0 := by
  sorry

theorem prod_half_two_pow_and_eight_dvd :
    (forall k : Nat, 4 <= k ->
      (Finset.filter (fun j => Nat.Coprime j (2 ^ k)) (Finset.Icc 1 (2 ^ k / 2))).prod id %
          2 ^ k = 2 ^ (k - 1) + 1) /\
      forall n : Nat, n % 8 = 0 -> (exists p : Nat, p.Prime /\ p % 2 = 1 /\ n % p = 0) ->
        (Finset.filter (fun j => Nat.Coprime j n) (Finset.Icc 1 (n / 2))).prod id % n = 1 := by
  sorry

end TuringTask
