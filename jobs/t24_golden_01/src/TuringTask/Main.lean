import Mathlib
import TuringTask.Entry

/-!
# The five statements

The theorems of the task, stated as in `TuringTask/Basic.lean`, with proofs from `Pisano.lean`
and `Entry.lean`. The lemmas `prompt_per` and `prompt_zer` turn the remainders into `Per` and
`Zer`.
-/

namespace TuringTask

lemma prompt_zer0 (n k : ℕ) : Nat.fib k % n = 0 ↔ Zer n k :=
  (Nat.dvd_iff_mod_eq_zero).symm

theorem main_pisano_le (n : Nat) (hn : 0 < n) :
    exists k : Nat, 0 < k /\ k <= 6 * n /\ Nat.fib k % n = 0 /\ Nat.fib (k + 1) % n = 1 % n :=
  pisano_le hn

theorem main_pisano_six (n : Nat) (hn : 0 < n) :
    (Nat.fib (6 * n) % n = 0 /\ Nat.fib (6 * n + 1) % n = 1 % n /\
      forall k : Nat, 0 < k -> k < 6 * n ->
        Not (Nat.fib k % n = 0 /\ Nat.fib (k + 1) % n = 1 % n)) <->
      exists j : Nat, 0 < j /\ n = 2 * 5 ^ j := by
  simpa only [← and_assoc, prompt_per] using pisano_eq_six_mul hn

theorem main_pisano_self (n : Nat) (hn : 0 < n) :
    (Nat.fib n % n = 0 /\ Nat.fib (n + 1) % n = 1 % n /\
      forall k : Nat, 0 < k -> k < n ->
        Not (Nat.fib k % n = 0 /\ Nat.fib (k + 1) % n = 1 % n)) <->
      (n = 1 \/ exists j : Nat, n = 24 * 5 ^ j) := by
  simpa only [← and_assoc, prompt_per] using pisano_eq_self hn

theorem main_entry_two (n : Nat) (hn : 0 < n) :
    (Nat.fib (2 * n) % n = 0 /\ forall k : Nat, 0 < k -> k < 2 * n -> 0 < Nat.fib k % n) <->
      exists j : Nat, n = 6 * 5 ^ j := by
  simpa only [prompt_zer0, prompt_zer] using entry_eq_two_mul hn

theorem main_entry_self (n : Nat) (hn : 0 < n) :
    (Nat.fib n % n = 0 /\ forall k : Nat, 0 < k -> k < n -> 0 < Nat.fib k % n) <->
      ((exists j : Nat, n = 5 ^ j) \/ exists j : Nat, n = 12 * 5 ^ j) := by
  simpa only [prompt_zer0, prompt_zer] using entry_eq_self hn

end TuringTask
