import Mathlib
import TuringTask.Core
import TuringTask.Consequences

namespace TuringTask

theorem charSum_norm_le (p : Nat) (hp : p.Prime) (chi : MulChar (ZMod p) Complex)
    (h : Not (chi = 1)) (N : Nat) :
    Norm.norm ((Finset.Icc 1 N).sum (fun n => chi (n : ZMod p))) <= Real.sqrt p * Real.log p := by
  exact charSum_norm_le_core p hp chi h N

theorem legendreSum_le (p : Nat) [hp : Fact p.Prime] (h2 : Not (p = 2)) (N : Nat) :
    abs (((Finset.Icc 1 N).sum (fun n => legendreSym p (n : Int)) : Int) : Real) <=
      Real.sqrt p * Real.log p := by
  exact legendreSum_le_core p h2 N

theorem exists_not_pow_le (p k : Nat) (hp : p.Prime) (hk : 2 <= k) (hkp : (p - 1) % k = 0) :
    exists n : Nat, 1 <= n /\ (n : Real) <= Real.sqrt p * Real.log p + 1 /\
      forall x : ZMod p, Not (x ^ k = (n : ZMod p)) := by
  exact exists_not_pow_le_core p k hp hk hkp

theorem card_residues_sub_le (p : Nat) [hp : Fact p.Prime] (h2 : Not (p = 2)) (N : Nat)
    (hN : N < p) :
    abs (2 * (((Finset.Icc 1 N).filter (fun n : Nat => legendreSym p (n : Int) = 1)).card : Real) -
        N) <= Real.sqrt p * Real.log p := by
  exact card_residues_sub_le_core p h2 N hN

theorem exists_prime_nonresidue_le (p : Nat) [hp : Fact p.Prime] (h2 : Not (p = 2)) :
    exists q : Nat, q.Prime /\ (q : Real) <= Real.sqrt p * Real.log p + 1 /\
      legendreSym p (q : Int) = -1 := by
  exact exists_prime_nonresidue_le_core p h2

end TuringTask
