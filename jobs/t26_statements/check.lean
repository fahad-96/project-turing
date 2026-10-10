import TuringTask.Basic

open TuringTask

example (p : Nat) (hp : p.Prime) :
    (exists x y : Nat, p = x ^ 2 + 5 * y ^ 2) <->
      (p = 5 \/ Membership.mem ({1, 9} : Finset Nat) (p % 20)) :=
  TuringTask.prime_eq_sq_add_five_mul_sq_iff p hp

example (p q : Nat) (hp : p.Prime) (hq : q.Prime)
    (hp20 : Membership.mem ({3, 7} : Finset Nat) (p % 20))
    (hq20 : Membership.mem ({3, 7} : Finset Nat) (q % 20)) :
    exists x y : Nat, p * q = x ^ 2 + 5 * y ^ 2 :=
  TuringTask.mul_eq_sq_add_five_mul_sq p q hp hq hp20 hq20

example (p : Nat) (hp : p.Prime) :
    (exists x y : Nat, p = x ^ 2 + 6 * y ^ 2) <->
      Membership.mem ({1, 7} : Finset Nat) (p % 24) :=
  TuringTask.prime_eq_sq_add_six_mul_sq_iff p hp

example (p : Nat) (hp : p.Prime) :
    (exists x y : Nat, p = x ^ 2 + 13 * y ^ 2) <->
      (p = 13 \/ Membership.mem ({1, 9, 17, 25, 29, 49} : Finset Nat) (p % 52)) :=
  TuringTask.prime_eq_sq_add_thirteen_mul_sq_iff p hp

example (p : Nat) (hp : p.Prime) :
    (exists x y : Nat, p = x ^ 2 + 21 * y ^ 2) <->
      Membership.mem ({1, 25, 37} : Finset Nat) (p % 84) :=
  TuringTask.prime_eq_sq_add_twenty_one_mul_sq_iff p hp

#print axioms TuringTask.prime_eq_sq_add_five_mul_sq_iff
#print axioms TuringTask.mul_eq_sq_add_five_mul_sq
#print axioms TuringTask.prime_eq_sq_add_six_mul_sq_iff
#print axioms TuringTask.prime_eq_sq_add_thirteen_mul_sq_iff
#print axioms TuringTask.prime_eq_sq_add_twenty_one_mul_sq_iff
