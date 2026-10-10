import Mathlib

namespace TuringTask

theorem exists_prime_fib (n : Nat) (hn : 3 <= n) (h6 : Not (n = 6)) (h12 : Not (n = 12)) :
    exists q : Nat, q.Prime /\ Nat.fib n % q = 0 /\
      forall k : Nat, 1 <= k -> k < n -> Not (Nat.fib k % q = 0) := by
  sorry

theorem exists_prime_lucas (n : Nat) (hn : 2 <= n) (h6 : Not (n = 6)) :
    exists q : Nat, q.Prime /\ (Nat.fib (n - 1) + Nat.fib (n + 1)) % q = 0 /\
      forall k : Nat, 1 <= k -> k < n -> Not ((Nat.fib (k - 1) + Nat.fib (k + 1)) % q = 0) := by
  sorry

theorem card_divisors_le (n : Nat) (hn : 1 <= n) :
    n.divisors.card <= (Nat.fib n).primeFactors.card + 4 := by
  sorry

theorem primeFactors_fib_eq (m n : Nat) (hm : 3 <= m) (hmn : m < n)
    (h : (Nat.fib m).primeFactors = (Nat.fib n).primeFactors) :
    m = 3 /\ n = 6 := by
  sorry

theorem exists_prime_fib_mod (n : Nat) (hn : 3 <= n) (h5 : Not (n = 5)) (h6 : Not (n = 6))
    (h12 : Not (n = 12)) :
    exists q : Nat, q.Prime /\ Nat.fib n % q = 0 /\ (q % n = 1 \/ q % n = n - 1) := by
  sorry

end TuringTask
