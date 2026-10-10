import TuringTask.Basic

open TuringTask

example (p : Nat) (hp : p.Prime) (chi : MulChar (ZMod p) Complex)
    (h : Not (chi = 1)) (N : Nat) :
    Norm.norm ((Finset.Icc 1 N).sum (fun n => chi (n : ZMod p))) <= Real.sqrt p * Real.log p :=
  TuringTask.charSum_norm_le p hp chi h N

example (p : Nat) [hp : Fact p.Prime] (h2 : Not (p = 2)) (N : Nat) :
    abs (((Finset.Icc 1 N).sum (fun n => legendreSym p (n : Int)) : Int) : Real) <=
      Real.sqrt p * Real.log p :=
  TuringTask.legendreSum_le p h2 N

example (p k : Nat) (hp : p.Prime) (hk : 2 <= k) (hkp : (p - 1) % k = 0) :
    exists n : Nat, 1 <= n /\ (n : Real) <= Real.sqrt p * Real.log p + 1 /\
      forall x : ZMod p, Not (x ^ k = (n : ZMod p)) :=
  TuringTask.exists_not_pow_le p k hp hk hkp

example (p : Nat) [hp : Fact p.Prime] (h2 : Not (p = 2)) (N : Nat)
    (hN : N < p) :
    abs (2 * (((Finset.Icc 1 N).filter (fun n : Nat => legendreSym p (n : Int) = 1)).card : Real) -
        N) <= Real.sqrt p * Real.log p :=
  TuringTask.card_residues_sub_le p h2 N hN

example (p : Nat) [hp : Fact p.Prime] (h2 : Not (p = 2)) :
    exists q : Nat, q.Prime /\ (q : Real) <= Real.sqrt p * Real.log p + 1 /\
      legendreSym p (q : Int) = -1 :=
  TuringTask.exists_prime_nonresidue_le p h2

#print axioms TuringTask.charSum_norm_le
#print axioms TuringTask.legendreSum_le
#print axioms TuringTask.exists_not_pow_le
#print axioms TuringTask.card_residues_sub_le
#print axioms TuringTask.exists_prime_nonresidue_le
