import Mathlib
import TuringTask.Octic

/-!
# The five statements

The results of `Quartic`, `Jacobi` and `Octic`, restated with the membership conditions of the
task (`e % 8 ∈ {1, 3}` and `q % 4 ∈ {2, 3}`).
-/

namespace TuringTask

/-- `2` is a fourth power modulo `p = 1 (mod 4)` iff `p = a^2 + 64 b^2`. -/
theorem main_two_quartic (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1) :
    (∃ x : ZMod p, x ^ 4 = 2) ↔ ∃ a b : ℕ, p = a ^ 2 + 64 * b ^ 2 :=
  two_quartic_iff hp hp4

/-- `-4` is an eighth power modulo `p = 1 (mod 8)` iff `p = a^2 + 32 b^2`. -/
theorem main_neg_four_octic (p : ℕ) (hp : p.Prime) (hp8 : p % 8 = 1) :
    (∃ x : ZMod p, x ^ 8 = -4) ↔ ∃ a b : ℕ, p = a ^ 2 + 32 * b ^ 2 :=
  octic_neg_four hp hp8

/-- `2` is a fourth power modulo an odd prime `p` iff `e^2 = p + 2 f^2` with
`e = 1, 3 (mod 8)`. -/
theorem main_two_quartic_odd (p : ℕ) (hp : p.Prime) (hp2 : p % 2 = 1) :
    (∃ x : ZMod p, x ^ 4 = 2) ↔
      ∃ e f : ℕ, e ^ 2 = p + 2 * f ^ 2 ∧ e % 8 ∈ ({1, 3} : Finset ℕ) := by
  rw [two_quartic_iff' hp hp2]
  simp only [Finset.mem_insert, Finset.mem_singleton]

/-- For `p = c^2 + q d^2` with `q = 2, 3 (mod 4)`, `q` is a fourth power modulo `p` iff
`J(q | c) = 1`. -/
theorem main_quartic_jacobi (p q c d : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1)
    (hq : q % 4 ∈ ({2, 3} : Finset ℕ)) (hpcd : p = c ^ 2 + q * d ^ 2) :
    (∃ x : ZMod p, x ^ 4 = (q : ZMod p)) ↔ jacobiSym (q : ℤ) c = 1 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  exact quartic_q hp hp4 hq hpcd

/-- For `p = 1 (mod 8)`, some `1 + sqrt 2` is a square modulo `p` iff `p = a^2 + 32 b^2`. -/
theorem main_sqrt_two (p : ℕ) (hp : p.Prime) (hp8 : p % 8 = 1) :
    (∃ s t : ZMod p, s ^ 2 = 2 ∧ t ^ 2 = 1 + s) ↔ ∃ a b : ℕ, p = a ^ 2 + 32 * b ^ 2 :=
  sqrt_two_octic hp hp8

end TuringTask
