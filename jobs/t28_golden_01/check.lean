import TuringTask.Basic

open TuringTask

example (p : Nat) (hp : p.Prime) (hp4 : p % 4 = 1) :
    (exists x : ZMod p, x ^ 4 = 2) <-> exists a b : Nat, p = a ^ 2 + 64 * b ^ 2 :=
  TuringTask.exists_pow_four_eq_two_iff p hp hp4

example (p : Nat) (hp : p.Prime) (hp8 : p % 8 = 1) :
    (exists x : ZMod p, x ^ 8 = -4) <-> exists a b : Nat, p = a ^ 2 + 32 * b ^ 2 :=
  TuringTask.exists_pow_eight_eq_neg_four_iff p hp hp8

example (p : Nat) (hp : p.Prime) (hp2 : p % 2 = 1) :
    (exists x : ZMod p, x ^ 4 = 2) <->
      exists e f : Nat,
        e ^ 2 = p + 2 * f ^ 2 /\ Membership.mem ({1, 3} : Finset Nat) (e % 8) :=
  TuringTask.exists_pow_four_eq_two_iff_sq_eq_add_two_mul_sq p hp hp2

example (p q c d : Nat) (hp : p.Prime) (hp4 : p % 4 = 1)
    (hq : Membership.mem ({2, 3} : Finset Nat) (q % 4)) (hpcd : p = c ^ 2 + q * d ^ 2) :
    (exists x : ZMod p, x ^ 4 = (q : ZMod p)) <-> jacobiSym (q : Int) c = 1 :=
  TuringTask.exists_pow_four_eq_iff_jacobiSym p q c d hp hp4 hq hpcd

example (p : Nat) (hp : p.Prime) (hp8 : p % 8 = 1) :
    (exists s t : ZMod p, s ^ 2 = 2 /\ t ^ 2 = 1 + s) <->
      exists a b : Nat, p = a ^ 2 + 32 * b ^ 2 :=
  TuringTask.exists_sq_eq_one_add_sqrt_two_iff p hp hp8

#print axioms TuringTask.exists_pow_four_eq_two_iff
#print axioms TuringTask.exists_pow_eight_eq_neg_four_iff
#print axioms TuringTask.exists_pow_four_eq_two_iff_sq_eq_add_two_mul_sq
#print axioms TuringTask.exists_pow_four_eq_iff_jacobiSym
#print axioms TuringTask.exists_sq_eq_one_add_sqrt_two_iff
