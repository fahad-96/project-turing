import TuringTask.Basic

open TuringTask

example (p q : Nat) (hp : p.Prime) (hq : q.Prime)
    (hpq : Not (p = q)) (k : Nat) :
    Membership.mem ({0, 1} : Finset Int)
      (Finset.sum (Finset.range (k + 1))
        (fun i => (Polynomial.cyclotomic (p * q) Int).coeff i)) :=
  TuringTask.sum_range_coeff_cyclotomic_mul_mem p q hp hq hpq k

example (p q u v : Nat) (hp : p.Prime) (hq : q.Prime)
    (hu : u * p % q = 1) (hv : v * q % p = 1) (huq : u < q) (hvp : v < p) :
    (Finset.filter (fun k => (Polynomial.cyclotomic (p * q) Int).coeff k = 1)
      (Finset.range (p * q))).card = u * v :=
  TuringTask.card_coeff_cyclotomic_mul_eq_one p q u v hp hq hu hv huq hvp

example (p q r : Nat) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (k : Nat) :
    |(Polynomial.cyclotomic (p * q * r) Int).coeff k| <= (p : Int) - 1 :=
  TuringTask.abs_coeff_cyclotomic_mul_mul_le p q r hp hq hr k

example (p q r : Nat) (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hr' : r % (p * q) = 1 \/ r % (p * q) + 1 = p * q) (k : Nat) :
    Membership.mem ({-1, 0, 1} : Finset Int) ((Polynomial.cyclotomic (p * q * r) Int).coeff k) :=
  TuringTask.coeff_cyclotomic_mul_mul_mem_of_mod p q r hp hq hr hr' k

example (p q r : Nat) (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (k : Nat) :
    |(Polynomial.cyclotomic (p * q * r) Int).coeff (k + 1) -
      (Polynomial.cyclotomic (p * q * r) Int).coeff k| <= 1 :=
  TuringTask.abs_coeff_succ_sub_coeff_cyclotomic_le p q r hp hq hr k

#print axioms TuringTask.sum_range_coeff_cyclotomic_mul_mem
#print axioms TuringTask.card_coeff_cyclotomic_mul_eq_one
#print axioms TuringTask.abs_coeff_cyclotomic_mul_mul_le
#print axioms TuringTask.coeff_cyclotomic_mul_mul_mem_of_mod
#print axioms TuringTask.abs_coeff_succ_sub_coeff_cyclotomic_le
