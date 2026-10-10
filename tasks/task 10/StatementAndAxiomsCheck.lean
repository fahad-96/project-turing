import TuringTask.Basic

open TuringTask

example (a b n : Nat) (hba : b < a) (hb : 1 <= b) (hab : Nat.Coprime a b)
    (hn : 2 <= n) (h2 : Not (n = 2 /\ exists t : Nat, a + b = 2 ^ t))
    (h6 : Not (a = 2 /\ b = 1 /\ n = 6)) :
    exists q : Nat, q.Prime /\ (a ^ n - b ^ n) % q = 0 /\
      forall k : Nat, 1 <= k -> k < n -> Not ((a ^ k - b ^ k) % q = 0) :=
  TuringTask.exists_prime_sub a b n hba hb hab hn h2 h6

example (a b n : Nat) (hba : b < a) (hb : 1 <= b) (hab : Nat.Coprime a b)
    (hn : 2 <= n) (h3 : Not (a = 2 /\ b = 1 /\ n = 3)) :
    exists q : Nat, q.Prime /\ (a ^ n + b ^ n) % q = 0 /\
      forall k : Nat, 1 <= k -> k < n -> Not ((a ^ k + b ^ k) % q = 0) :=
  TuringTask.exists_prime_add a b n hba hb hab hn h3

example (a n : Nat) (ha : 2 <= a) (hn : 1 <= n) :
    n.divisors.card <= (a ^ n - 1).primeFactors.card + 2 :=
  TuringTask.card_divisors_le a n ha hn

example (a n q m : Nat) (ha : 2 <= a) (hn : 2 <= n) (hq : q.Prime) (hm : 2 <= m)
    (h : a ^ n - 1 = q ^ m) :
    a = 3 /\ n = 2 /\ q = 2 /\ m = 3 :=
  TuringTask.eq_prime_pow a n q m ha hn hq hm h

example (a m n : Nat) (ha : 2 <= a) (hm : 1 <= m) (hmn : m < n)
    (h : (a ^ m - 1).primeFactors = (a ^ n - 1).primeFactors) :
    m = 1 /\ n = 2 /\ exists t : Nat, a + 1 = 2 ^ t :=
  TuringTask.primeFactors_eq a m n ha hm hmn h

#print axioms TuringTask.exists_prime_sub
#print axioms TuringTask.exists_prime_add
#print axioms TuringTask.card_divisors_le
#print axioms TuringTask.eq_prime_pow
#print axioms TuringTask.primeFactors_eq
