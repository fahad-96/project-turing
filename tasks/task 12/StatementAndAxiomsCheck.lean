import TuringTask.Basic

open TuringTask

example (n : Nat) (hn : 3 <= n) (h6 : Not (n = 6)) (h12 : Not (n = 12)) :
    exists q : Nat, q.Prime /\ Nat.fib n % q = 0 /\
      forall k : Nat, 1 <= k -> k < n -> Not (Nat.fib k % q = 0) :=
  TuringTask.exists_prime_fib n hn h6 h12

example (n : Nat) (hn : 2 <= n) (h6 : Not (n = 6)) :
    exists q : Nat, q.Prime /\ (Nat.fib (n - 1) + Nat.fib (n + 1)) % q = 0 /\
      forall k : Nat, 1 <= k -> k < n -> Not ((Nat.fib (k - 1) + Nat.fib (k + 1)) % q = 0) :=
  TuringTask.exists_prime_lucas n hn h6

example (n : Nat) (hn : 1 <= n) :
    n.divisors.card <= (Nat.fib n).primeFactors.card + 4 :=
  TuringTask.card_divisors_le n hn

example (m n : Nat) (hm : 3 <= m) (hmn : m < n)
    (h : (Nat.fib m).primeFactors = (Nat.fib n).primeFactors) :
    m = 3 /\ n = 6 :=
  TuringTask.primeFactors_fib_eq m n hm hmn h

example (n : Nat) (hn : 3 <= n) (h5 : Not (n = 5)) (h6 : Not (n = 6))
    (h12 : Not (n = 12)) :
    exists q : Nat, q.Prime /\ Nat.fib n % q = 0 /\ (q % n = 1 \/ q % n = n - 1) :=
  TuringTask.exists_prime_fib_mod n hn h5 h6 h12

#print axioms TuringTask.exists_prime_fib
#print axioms TuringTask.exists_prime_lucas
#print axioms TuringTask.card_divisors_le
#print axioms TuringTask.primeFactors_fib_eq
#print axioms TuringTask.exists_prime_fib_mod
