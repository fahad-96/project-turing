import Mathlib
import TuringTask.LucEq

/-!
# The five statements

The theorems of the task, stated as in `TuringTask/Basic.lean`, with proofs from `FibEq.lean`
and `LucEq.lean`. The equation `F(n) + c = 2 F(n + 1)` of the prompt is `lnat n = c`
(`lnat_add`), and the members of each set get explicit witnesses.
-/

namespace TuringTask

theorem main_fib_add_one (n : Nat) :
    (exists x : Nat, Nat.fib n + 1 = x ^ 2) <-> Membership.mem ({0, 4, 6} : Finset Nat) n := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨x, hx⟩
    exact fib_add_one_sq hx
  · rintro (rfl | rfl | rfl)
    exacts [⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩]

theorem main_fib_sq_add_one (n : Nat) :
    (exists x : Nat, Nat.fib n = x ^ 2 + 1) <-> Membership.mem ({1, 2, 3, 5} : Finset Nat) n := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨x, hx⟩
    exact fib_sq_add_one hx
  · rintro (rfl | rfl | rfl | rfl)
    exacts [⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩]

theorem main_fib_two_sq_add_one (n : Nat) :
    (exists x : Nat, Nat.fib n = 2 * x ^ 2 + 1) <->
      Membership.mem ({1, 2, 4} : Finset Nat) n := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨x, hx⟩
    exact fib_two_sq_add_one hx
  · rintro (rfl | rfl | rfl)
    exacts [⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩]

theorem main_lucas_sq_add_one (n : Nat) :
    (exists x : Nat, Nat.fib n + (x ^ 2 + 1) = 2 * Nat.fib (n + 1)) <->
      Membership.mem ({0, 1} : Finset Nat) n := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨x, hx⟩
    have := lnat_add n
    exact lnat_sq_add_one (x := x) (by omega)
  · rintro (rfl | rfl)
    exacts [⟨1, by decide⟩, ⟨0, by decide⟩]

theorem main_lucas_add_one (n : Nat) :
    (exists x : Nat, Nat.fib n + 2 * x ^ 2 = 2 * Nat.fib (n + 1) + 1) <->
      Membership.mem ({1, 4, 11} : Finset Nat) n := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨x, hx⟩
    have := lnat_add n
    exact lnat_add_one_two_sq (x := x) (by omega)
  · rintro (rfl | rfl | rfl)
    exacts [⟨1, by decide⟩, ⟨2, by decide⟩, ⟨10, by decide⟩]

end TuringTask
