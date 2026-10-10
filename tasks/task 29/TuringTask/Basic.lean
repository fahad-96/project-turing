import Mathlib

namespace TuringTask

theorem sign_mulLeft_eq_jacobiSym (n a : Nat) [NeZero n] (hn : n % 2 = 1) (ha : Nat.Coprime a n) :
    (Equiv.Perm.sign (Units.mulLeft (ZMod.unitOfCoprime a ha)) : Int) = jacobiSym a n := by
  sorry

theorem sign_mulLeft_of_even (n a : Nat) [NeZero n] (hn : n % 2 = 0) (ha : Nat.Coprime a n) :
    (Equiv.Perm.sign (Units.mulLeft (ZMod.unitOfCoprime a ha)) : Int) =
      if n % 4 = 2 then 1 else if a % 4 = 1 then 1 else -1 := by
  sorry

theorem sign_mulLeft_units_eq_neg_one_iff (n : Nat) [NeZero n] (u : Units (ZMod n)) :
    Equiv.Perm.sign (Equiv.mulLeft u) = -1 <->
      (n = 4 \/
        exists p k : Nat, p.Prime /\ p % 2 = 1 /\ 0 < k /\ (n = p ^ k \/ n = 2 * p ^ k)) /\
        Not (IsSquare u) := by
  sorry

theorem sign_ofBijective_pow (p k : Nat) [NeZero p] (hp : p.Prime)
    (hk : Function.Bijective (fun x : ZMod p => x ^ k)) :
    (Equiv.Perm.sign (Equiv.ofBijective (fun x : ZMod p => x ^ k) hk) : Int) =
      if p % 4 = 1 /\ k % 4 = 3 then -1 else 1 := by
  sorry

theorem sign_transpose (m n : Nat) :
    (Equiv.Perm.sign ((finProdFinEquiv.symm.trans (Equiv.prodComm (Fin m) (Fin n))).trans
        (finProdFinEquiv.trans (finCongr (Nat.mul_comm n m)))) : Int) =
      (-1) ^ (Nat.choose m 2 * Nat.choose n 2) := by
  sorry

end TuringTask
