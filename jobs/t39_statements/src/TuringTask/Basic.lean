import Mathlib

namespace TuringTask

theorem exists_polynomial_iff (n : Nat) (hn : 0 < n) (F : ZMod n -> ZMod n) :
    (exists P : Polynomial (ZMod n), forall x : ZMod n, F x = P.eval x) <->
      forall j : Nat, j < n ->
        (Finset.range (j + 1)).sum (fun i =>
            (-1 : Int) ^ (j - i) * (j.choose i : Int) * ((F (i : ZMod n)).val : Int)) %
          (Nat.gcd n j.factorial : Int) = 0 := by
  sorry

theorem ncard_polynomial_functions (n : Nat) (hn : 0 < n) :
    Set.ncard {F : ZMod n -> ZMod n | exists P : Polynomial (ZMod n), forall x, F x = P.eval x} =
      (Finset.range n).prod (fun j => n / Nat.gcd n j.factorial) := by
  sorry

theorem ncard_bijective_polynomial_functions (p k : Nat) (hp : p.Prime) (hk : 2 <= k) :
    Set.ncard {F : ZMod (p ^ k) -> ZMod (p ^ k) |
        Function.Bijective F /\
          exists P : Polynomial (ZMod (p ^ k)), forall x, F x = P.eval x} * p ^ (2 * p) =
      p.factorial * (p - 1) ^ p *
        (Finset.range (p ^ k)).prod (fun j => p ^ k / Nat.gcd (p ^ k) j.factorial) := by
  sorry

theorem exists_digits_of_minimal (p k s : Nat) (hp : p.Prime) (hk : 1 <= k)
    (hs : s.factorial % p ^ k = 0)
    (hmin : forall m : Nat, m < s -> Not (m.factorial % p ^ k = 0)) :
    exists (t : Nat) (c : Nat -> Nat), 1 <= c t /\ (forall i, i <= t -> c i <= p) /\
      (forall i j, i < j -> j <= t -> c j = p -> c i = 0) /\
      k = (Finset.range (t + 1)).sum (fun i => c i * ((p ^ (i + 1) - 1) / (p - 1))) /\
      s = (Finset.range (t + 1)).sum (fun i => c i * p ^ (i + 1)) := by
  sorry

theorem natDegree_lt_of_minimal (n s : Nat) (hn : 2 <= n) (hs : s.factorial % n = 0)
    (hmin : forall m : Nat, m < s -> Not (m.factorial % n = 0)) :
    (forall P : Polynomial (ZMod n), exists Q : Polynomial (ZMod n),
        Q.natDegree < s /\ forall x, P.eval x = Q.eval x) /\
      exists P : Polynomial (ZMod n), forall Q : Polynomial (ZMod n),
        (forall x, P.eval x = Q.eval x) -> s - 1 <= Q.natDegree := by
  sorry

end TuringTask
