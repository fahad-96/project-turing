import Mathlib
import TuringTask.PellSeq

/-!
# Every solution is a power of the unit

`pell_descent`: let `a + b √D` have norm `σ = ±1`, and assume that no solution of norm `1` or
`σ` has `0 < y < b`. Then every solution `x ^ 2 - D y ^ 2 ∈ {1, σ}` in natural numbers is
`(pX k, pY k)` for some `k`. The proof divides `x + y √D` by the unit: the quotient
`x' + y' √D` with `x' = σ (a x - D b y)` and `y' = σ (a y - b x)` again has natural coordinates,
norm `1` or `σ`, and `y' < y`. Each inequality comes from comparing squares.

`not_sq_of_sqrt` turns the finite minimality check into `Nat.sqrt` evaluations.
-/

namespace TuringTask

variable {D a b : ℕ}

lemma lt_of_sq_lt' {u v : ℤ} (hv : 0 ≤ v) (h : u ^ 2 < v ^ 2) : u < v := by
  by_contra h'
  push Not at h'
  nlinarith [mul_le_mul h' h' hv (le_trans hv h')]

lemma le_of_sq_le' {u v : ℤ} (hv : 0 ≤ v) (h : u ^ 2 ≤ v ^ 2) : u ≤ v := by
  by_contra h'
  push Not at h'
  nlinarith [mul_lt_mul'' h' h' hv hv]

/-- A square equal to `N` forces `Nat.sqrt N ^ 2 = N`. -/
lemma sqrt_sq_of_sq {x N : ℕ} (h : x ^ 2 = N) : Nat.sqrt N ^ 2 = N := by
  rw [← h, Nat.sqrt_eq']

/-- One descent step. -/
lemma descent_step' {σ τ : ℤ} (hσ : (a : ℤ) ^ 2 - D * b ^ 2 = σ) (hσ1 : σ = 1 ∨ σ = -1)
    (hτ1 : τ = 1 ∨ τ = σ) (ha : 1 ≤ a) (hb : 1 ≤ b) {x y : ℕ} (hyb : b ≤ y)
    (hτ : (x : ℤ) ^ 2 - D * y ^ 2 = τ) :
    0 < σ * (a * x - D * b * y) ∧ 0 ≤ σ * (a * y - b * x) ∧ σ * (a * y - b * x) < y := by
  have hD : (0 : ℤ) ≤ D := by positivity
  have hyb' : (b : ℤ) ≤ y := by exact_mod_cast hyb
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hx0 : (0 : ℤ) ≤ x := by positivity
  have i1 : ((a : ℤ) * x) ^ 2 - (D * b * y) ^ 2 = a ^ 2 * τ + σ * D * y ^ 2 := by
    linear_combination (a : ℤ) ^ 2 * hτ + (D : ℤ) * (y : ℤ) ^ 2 * hσ
  have i2 : ((a : ℤ) * y) ^ 2 - (b * x) ^ 2 = σ * y ^ 2 - τ * b ^ 2 := by
    linear_combination (y : ℤ) ^ 2 * hσ - (b : ℤ) ^ 2 * hτ
  have i3 : ((b : ℤ) * x) ^ 2 - ((a - 1) * y) ^ 2 = b ^ 2 * τ + (2 * a - 1 - σ) * y ^ 2 := by
    linear_combination (b : ℤ) ^ 2 * hτ - (y : ℤ) ^ 2 * hσ
  have i4 : (((a : ℤ) + 1) * y) ^ 2 - (b * x) ^ 2 = (2 * a + 1 + σ) * y ^ 2 - b ^ 2 * τ := by
    linear_combination -(b : ℤ) ^ 2 * hτ + (y : ℤ) ^ 2 * hσ
  have hy2 : (b : ℤ) ^ 2 ≤ (y : ℤ) ^ 2 := by nlinarith
  have hDy : (D : ℤ) * b ^ 2 ≤ D * y ^ 2 := mul_le_mul_of_nonneg_left hy2 hD
  rcases hσ1 with rfl | rfl
  · have hτ' : τ = 1 := by rcases hτ1 with h | h <;> exact h
    subst hτ'
    refine ⟨?_, ?_, ?_⟩
    · have : (D : ℤ) * b * y < a * x :=
        lt_of_sq_lt' (by positivity) (by nlinarith [sq_nonneg (D * y : ℤ)])
      linarith
    · have : (b : ℤ) * x ≤ a * y := le_of_sq_le' (by positivity) (by nlinarith)
      linarith
    · have : ((a : ℤ) - 1) * y < b * x :=
        lt_of_sq_lt' (by positivity) (by nlinarith [sq_nonneg (y : ℤ)])
      linarith
  · refine ⟨?_, ?_, ?_⟩
    · have : (a : ℤ) * x < D * b * y := by
        refine lt_of_sq_lt' (by positivity) ?_
        rcases hτ1 with rfl | rfl
        · nlinarith
        · nlinarith [sq_nonneg (a : ℤ), sq_nonneg (y : ℤ)]
      linarith
    · have : (a : ℤ) * y ≤ b * x := by
        refine le_of_sq_le' (by positivity) ?_
        rcases hτ1 with rfl | rfl <;> nlinarith
      linarith
    · have : (b : ℤ) * x < (a + 1) * y := by
        refine lt_of_sq_lt' (by positivity) ?_
        rcases hτ1 with rfl | rfl <;> nlinarith
      linarith

/-- Every solution of norm `1` or `σ` is a power of the unit. -/
theorem pell_descent {σ : ℤ} (hσ : (a : ℤ) ^ 2 - D * b ^ 2 = σ) (hσ1 : σ = 1 ∨ σ = -1)
    (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hmin : ∀ x y : ℕ, 0 < y → y < b → (x : ℤ) ^ 2 - D * y ^ 2 ≠ 1 ∧
      (x : ℤ) ^ 2 - D * y ^ 2 ≠ σ) :
    ∀ y x : ℕ, ((x : ℤ) ^ 2 - D * y ^ 2 = 1 ∨ (x : ℤ) ^ 2 - D * y ^ 2 = σ) →
      ∃ k, x = pX D a b k ∧ y = pY D a b k := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
  intro x hx
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · refine ⟨0, ?_, rfl⟩
    have hx1 : (x : ℤ) ^ 2 = 1 := by
      rcases hx with h | h
      · simpa using h
      · rcases hσ1 with rfl | rfl
        · simpa using h
        · have h0 : (x : ℤ) ^ 2 = -1 := by simpa using h
          nlinarith [sq_nonneg (x : ℤ)]
    have : (x : ℤ) = 1 := by nlinarith [sq_nonneg ((x : ℤ) - 1), sq_nonneg ((x : ℤ) + 1)]
    simp only [pX_zero]
    exact_mod_cast this
  have hyb : b ≤ y := by
    by_contra h
    push Not at h
    have := hmin x y hy h
    rcases hx with h' | h'
    · exact this.1 h'
    · exact this.2 h'
  obtain ⟨τ, hτ, hτ1⟩ : ∃ τ : ℤ, (x : ℤ) ^ 2 - D * y ^ 2 = τ ∧ (τ = 1 ∨ τ = σ) :=
    ⟨_, rfl, hx⟩
  obtain ⟨h1, h2, h3⟩ := descent_step' hσ hσ1 hτ1 ha hb hyb hτ
  set x' : ℤ := σ * (a * x - D * b * y) with hx'
  set y' : ℤ := σ * (a * y - b * x) with hy'
  have hσσ : σ * σ = 1 := by rcases hσ1 with rfl | rfl <;> norm_num
  have hn : x' ^ 2 - D * y' ^ 2 = τ * σ := by
    rw [hx', hy']
    linear_combination σ ^ 2 * ((x : ℤ) ^ 2 - D * y ^ 2) * hσ + σ ^ 3 * hτ + τ * σ * hσσ
  obtain ⟨k, hk1, hk2⟩ := ih y'.toNat (by omega) x'.toNat (by
    have e1 : ((x'.toNat : ℕ) : ℤ) = x' := Int.toNat_of_nonneg h1.le
    have e2 : ((y'.toNat : ℕ) : ℤ) = y' := Int.toNat_of_nonneg h2
    rw [e1, e2, hn]
    rcases hτ1 with rfl | rfl
    · right; ring
    · left; linear_combination hσσ)
  refine ⟨k + 1, ?_, ?_⟩
  · have e : (pX D a b (k + 1) : ℤ) = x := by
      rw [pX_succ]; push_cast
      rw [← hk1, ← hk2, Int.toNat_of_nonneg h1.le, Int.toNat_of_nonneg h2, hx', hy']
      linear_combination σ * x * hσ + x * hσσ
    exact_mod_cast e.symm
  · have e : (pY D a b (k + 1) : ℤ) = y := by
      rw [pY_succ]; push_cast
      rw [← hk1, ← hk2, Int.toNat_of_nonneg h1.le, Int.toNat_of_nonneg h2, hx', hy']
      linear_combination σ * y * hσ + y * hσσ
    exact_mod_cast e.symm

end TuringTask
