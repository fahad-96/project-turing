import Mathlib
import TuringTask.Rings

/-!
# Split, ramified and inert primes in `R1`, `R3`, `R4`

* `split_of`: if `J(b^2 + 4 a | p) = 1` for an odd prime `p ∤ b^2 + 4 a`, then `p = N(π)` with
  `π` and `π̄` prime and `π ∤ π̄` (`exists_norm_of_jacobi`, `not_dvd_star`).
* `inert_of_jacobi`: if `J(b^2 + 4 a | p) = -1`, no element has norm `p` (`jacobi_of_norm`), so
  `p` stays prime (`prime_or_norm`).
* `jac1`, `jac3`, `jac4`: tables modulo `12`, `32` and `28` give `J(-3 | p) = J(p | 3)`,
  `J(-8 | p) = J(-2 | p)` and `J(-7 | p) = J(p | 7)` for odd primes `p` prime to `3`, `2`, `7`.
* `type1`, `type3`, `type4`: every prime is split, ramified or inert, with `χ p = 1, 0, -1`.
  The ramified primes are `3 = N(1 - ω)`, `2 = N(√-2)` and `7 = N(1 - 2 t)`; in `R4` the prime
  `2 = N(t)` splits, and in `R1` the prime `2` is inert because `x^2 - x y + y^2 ≠ 2`.
-/

namespace TuringTask

variable {a b : ℤ}

local notation "Nm" => QuadraticAlgebra.norm

lemma split_of (hD : b ^ 2 + 4 * a < 0)
    (hIP : ∀ z : QuadraticAlgebra ℤ a b, Irreducible z → Prime z) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpD : ¬ (p : ℤ) ∣ b ^ 2 + 4 * a) (hJ : jacobiSym (b ^ 2 + 4 * a) p = 1) :
    ∃ π : QuadraticAlgebra ℤ a b, Nm π = p ∧ Prime π ∧ Prime (star π) ∧ ¬ π ∣ star π := by
  obtain ⟨π, hπ⟩ := exists_norm_of_jacobi hD hIP hp hp2 hJ
  refine ⟨π, hπ, hIP _ (irreducible_of_norm_prime hD hp hπ),
    hIP _ (irreducible_of_norm_prime hD hp (by rw [QuadraticAlgebra.norm_star, hπ])),
    not_dvd_star hp hπ hpD⟩

lemma inert_of (hD : b ^ 2 + 4 * a < 0)
    (hIP : ∀ z : QuadraticAlgebra ℤ a b, Irreducible z → Prime z) {p : ℕ} (hp : p.Prime)
    (hno : ∀ π : QuadraticAlgebra ℤ a b, Nm π ≠ p) : Prime ((p : ℤ) : QuadraticAlgebra ℤ a b) :=
  (prime_or_norm hD hIP hp).resolve_left (by rintro ⟨π, h⟩; exact hno π h)

lemma inert_of_jacobi (hD : b ^ 2 + 4 * a < 0)
    (hIP : ∀ z : QuadraticAlgebra ℤ a b, Irreducible z → Prime z) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpD : ¬ (p : ℤ) ∣ b ^ 2 + 4 * a) (hJ : jacobiSym (b ^ 2 + 4 * a) p = -1) :
    Prime ((p : ℤ) : QuadraticAlgebra ℤ a b) :=
  inert_of hD hIP hp fun π hπ => by
    have := jacobi_of_norm hp hp2 hπ hpD
    rw [hJ] at this
    norm_num at this

lemma odd_of_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : p % 2 = 1 :=
  Nat.odd_iff.mp (hp.odd_of_ne_two hp2)

lemma not_dvd_of_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ¬ (p : ℤ) ∣ (q : ℤ) := by
  intro h
  have := (Nat.prime_dvd_prime_iff_eq hp hq).mp (Int.natCast_dvd_natCast.mp h)
  exact hpq this

/-! ### Jacobi symbol tables -/

lemma jac1 {p : ℕ} (hodd : p % 2 = 1) (h3 : p % 3 ≠ 0) :
    jacobiSym (-3) p = jacobiSym (p : ℤ) 3 ∧
      (jacobiSym (p : ℤ) 3 = 1 ∨ jacobiSym (p : ℤ) 3 = -1) := by
  rw [jacobiSym.mod_right (-3) (Nat.odd_iff.mpr hodd), jacobiSym.mod_left (p : ℤ) 3]
  simp only [Nat.cast_ofNat]
  have e : (p : ℤ) % 3 = ((p % 12 : ℕ) : ℤ) % 3 := by omega
  rw [e, show 4 * Int.natAbs (-3) = 12 from rfl]
  have h12 : p % 12 = 1 ∨ p % 12 = 5 ∨ p % 12 = 7 ∨ p % 12 = 11 := by omega
  rcases h12 with h | h | h | h <;> rw [h] <;> norm_num

lemma jac3 {p : ℕ} (hodd : p % 2 = 1) :
    jacobiSym (-8) p = jacobiSym (-2) p ∧ (jacobiSym (-2) p = 1 ∨ jacobiSym (-2) p = -1) := by
  rw [jacobiSym.mod_right (-8) (Nat.odd_iff.mpr hodd),
    jacobiSym.mod_right (-2) (Nat.odd_iff.mpr hodd)]
  rw [show 4 * Int.natAbs (-8) = 32 from rfl, show 4 * Int.natAbs (-2) = 8 from rfl]
  have e : p % 8 = p % 32 % 8 := by omega
  rw [e]
  have h32 : p % 32 = 1 ∨ p % 32 = 3 ∨ p % 32 = 5 ∨ p % 32 = 7 ∨ p % 32 = 9 ∨ p % 32 = 11 ∨
      p % 32 = 13 ∨ p % 32 = 15 ∨ p % 32 = 17 ∨ p % 32 = 19 ∨ p % 32 = 21 ∨ p % 32 = 23 ∨
      p % 32 = 25 ∨ p % 32 = 27 ∨ p % 32 = 29 ∨ p % 32 = 31 := by omega
  rcases h32 with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    rw [h] <;> norm_num

lemma jac4 {p : ℕ} (hodd : p % 2 = 1) (h7 : p % 7 ≠ 0) :
    jacobiSym (-7) p = jacobiSym (p : ℤ) 7 ∧
      (jacobiSym (p : ℤ) 7 = 1 ∨ jacobiSym (p : ℤ) 7 = -1) := by
  rw [jacobiSym.mod_right (-7) (Nat.odd_iff.mpr hodd), jacobiSym.mod_left (p : ℤ) 7]
  simp only [Nat.cast_ofNat]
  have e : (p : ℤ) % 7 = ((p % 28 : ℕ) : ℤ) % 7 := by omega
  rw [e, show 4 * Int.natAbs (-7) = 28 from rfl]
  have h28 : p % 28 = 1 ∨ p % 28 = 3 ∨ p % 28 = 5 ∨ p % 28 = 9 ∨ p % 28 = 11 ∨ p % 28 = 13 ∨
      p % 28 = 15 ∨ p % 28 = 17 ∨ p % 28 = 19 ∨ p % 28 = 23 ∨ p % 28 = 25 ∨ p % 28 = 27 := by
    omega
  rcases h28 with h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> norm_num

/-! ### The type of every prime -/

lemma norm_ne_two_R1 (π : QuadraticAlgebra ℤ (-1) (-1)) : Nm π ≠ 2 := by
  intro h
  have h' : π.re ^ 2 + (-1) * π.re * π.im - (-1) * π.im ^ 2 = ((2 : ℕ) : ℤ) := by
    rw [← norm_mk]; exact h
  obtain ⟨b1, b2, b3, b4⟩ := in_box (by norm_num) (by norm_num) h' (by norm_num)
  generalize π.re = x at h' b1 b2
  generalize π.im = y at h' b3 b4
  push_cast at b1 b2 b3 b4
  interval_cases x <;> interval_cases y <;> norm_num at h'

theorem type1 (p : ℕ) (hp : p.Prime) :
    (jacobiSym (p : ℤ) 3 = 1 ∧ ∃ π : QuadraticAlgebra ℤ (-1) (-1), Nm π = p ∧ Prime π ∧
      Prime (star π) ∧ ¬ π ∣ star π) ∨
    (jacobiSym (p : ℤ) 3 = 0 ∧ ∃ π : QuadraticAlgebra ℤ (-1) (-1), Nm π = p ∧ Prime π ∧
      π ∣ star π) ∨
    (jacobiSym (p : ℤ) 3 = -1 ∧ Prime ((p : ℤ) : QuadraticAlgebra ℤ (-1) (-1))) := by
  have hD : ((-1 : ℤ)) ^ 2 + 4 * (-1) < 0 := by norm_num
  by_cases h2 : p = 2
  · subst h2
    right; right
    exact ⟨by norm_num, inert_of hD hIP1 hp norm_ne_two_R1⟩
  by_cases h3 : p = 3
  · subst h3
    right; left
    refine ⟨by norm_num, ⟨1, -1⟩, by rw [norm_mk]; norm_num, hIP1 _
      (irreducible_of_norm_prime hD hp (by rw [norm_mk]; norm_num)), ⟨⟨1, 1⟩, ?_⟩⟩
    ext <;> simp
  have hodd := odd_of_prime hp h2
  have hpD : ¬ (p : ℤ) ∣ (-1) ^ 2 + 4 * (-1) := by
    have := not_dvd_of_prime hp Nat.prime_three h3
    norm_num
    exact fun h => this (by simpa using h)
  have hp3 : p % 3 ≠ 0 := by
    intro h
    exact h3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.dvd_of_mod_eq_zero h)).symm
  obtain ⟨hJ, hv⟩ := jac1 hodd hp3
  have hJ' : jacobiSym ((-1) ^ 2 + 4 * (-1)) p = jacobiSym (p : ℤ) 3 := by norm_num; exact hJ
  rcases hv with hv | hv
  · left
    exact ⟨hv, split_of hD hIP1 hp h2 hpD (by rw [hJ', hv])⟩
  · right; right
    exact ⟨hv, inert_of_jacobi hD hIP1 hp h2 hpD (by rw [hJ', hv])⟩

theorem type3 (p : ℕ) (hp : p.Prime) :
    (jacobiSym (-2) p = 1 ∧ ∃ π : QuadraticAlgebra ℤ (-2) 0, Nm π = p ∧ Prime π ∧
      Prime (star π) ∧ ¬ π ∣ star π) ∨
    (jacobiSym (-2) p = 0 ∧ ∃ π : QuadraticAlgebra ℤ (-2) 0, Nm π = p ∧ Prime π ∧
      π ∣ star π) ∨
    (jacobiSym (-2) p = -1 ∧ Prime ((p : ℤ) : QuadraticAlgebra ℤ (-2) 0)) := by
  have hD : ((0 : ℤ)) ^ 2 + 4 * (-2) < 0 := by norm_num
  by_cases h2 : p = 2
  · subst h2
    right; left
    refine ⟨by norm_num, ⟨0, 1⟩, by rw [norm_mk]; norm_num, hIP3 _
      (irreducible_of_norm_prime hD hp (by rw [norm_mk]; norm_num)), ⟨-1, ?_⟩⟩
    ext <;> simp
  have hodd := odd_of_prime hp h2
  have hpD : ¬ (p : ℤ) ∣ 0 ^ 2 + 4 * (-2) := by
    intro h
    have h8 : (p : ℤ) ∣ 2 ^ 3 := by
      have : (p : ℤ) ∣ -(0 ^ 2 + 4 * (-2)) := dvd_neg.mpr h
      norm_num at this ⊢
      exact this
    have := (prime_int hp).dvd_of_dvd_pow h8
    exact not_dvd_of_prime hp Nat.prime_two h2 (by simpa using this)
  obtain ⟨hJ, hv⟩ := jac3 hodd
  have hJ' : jacobiSym (0 ^ 2 + 4 * (-2)) p = jacobiSym (-2) p := by norm_num; exact hJ
  rcases hv with hv | hv
  · left
    exact ⟨hv, split_of hD hIP3 hp h2 hpD (by rw [hJ', hv])⟩
  · right; right
    exact ⟨hv, inert_of_jacobi hD hIP3 hp h2 hpD (by rw [hJ', hv])⟩

theorem type4 (p : ℕ) (hp : p.Prime) :
    (jacobiSym (p : ℤ) 7 = 1 ∧ ∃ π : QuadraticAlgebra ℤ (-2) 1, Nm π = p ∧ Prime π ∧
      Prime (star π) ∧ ¬ π ∣ star π) ∨
    (jacobiSym (p : ℤ) 7 = 0 ∧ ∃ π : QuadraticAlgebra ℤ (-2) 1, Nm π = p ∧ Prime π ∧
      π ∣ star π) ∨
    (jacobiSym (p : ℤ) 7 = -1 ∧ Prime ((p : ℤ) : QuadraticAlgebra ℤ (-2) 1)) := by
  have hD : ((1 : ℤ)) ^ 2 + 4 * (-2) < 0 := by norm_num
  have hpD7 : ∀ q : ℕ, q.Prime → q ≠ 7 → ¬ (q : ℤ) ∣ 1 ^ 2 + 4 * (-2) := by
    intro q hq hq7 h
    have : (q : ℤ) ∣ ((7 : ℕ) : ℤ) := by
      have := dvd_neg.mpr h
      norm_num at this ⊢
      exact this
    exact not_dvd_of_prime hq (by norm_num) hq7 this
  by_cases h2 : p = 2
  · subst h2
    left
    have hπ : Nm (⟨0, 1⟩ : QuadraticAlgebra ℤ (-2) 1) = ((2 : ℕ) : ℤ) := by
      rw [norm_mk]; norm_num
    refine ⟨by norm_num, ⟨0, 1⟩, hπ, hIP4 _ (irreducible_of_norm_prime hD hp hπ),
      hIP4 _ (irreducible_of_norm_prime hD hp (by rw [QuadraticAlgebra.norm_star, hπ])),
      not_dvd_star hp hπ (hpD7 2 hp (by norm_num))⟩
  by_cases h7 : p = 7
  · subst h7
    right; left
    refine ⟨by norm_num, ⟨1, -2⟩, by rw [norm_mk]; norm_num, hIP4 _
      (irreducible_of_norm_prime hD hp (by rw [norm_mk]; norm_num)), ⟨-1, ?_⟩⟩
    ext <;> simp
  have hodd := odd_of_prime hp h2
  have hp7 : p % 7 ≠ 0 := by
    intro h
    exact h7 ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp (Nat.dvd_of_mod_eq_zero h)).symm
  obtain ⟨hJ, hv⟩ := jac4 hodd hp7
  have hJ' : jacobiSym (1 ^ 2 + 4 * (-2)) p = jacobiSym (p : ℤ) 7 := by norm_num; exact hJ
  rcases hv with hv | hv
  · left
    exact ⟨hv, split_of hD hIP4 hp h2 (hpD7 p hp h7) (by rw [hJ', hv])⟩
  · right; right
    exact ⟨hv, inert_of_jacobi hD hIP4 hp h2 (hpD7 p hp h7) (by rw [hJ', hv])⟩

end TuringTask
