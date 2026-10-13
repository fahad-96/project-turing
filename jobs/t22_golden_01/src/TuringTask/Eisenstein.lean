import Mathlib

/-!
# Eisenstein integers

`Eis` is Mathlib's `QuadraticAlgebra ℤ (-1) (-1)`: the elements are `x + y ω` with
`ω ^ 2 = -1 - ω`, stored as the pair `⟨x, y⟩`. The norm is `x ^ 2 - x y + y ^ 2`.

* `Eis.euclid`: division with rounding makes `Eis` a Euclidean domain. It is a definition, and
  the lemmas below use it locally through `letI`.
* `Eis.exists_assoc_cube`: coprime factors of a cube are cubes up to a unit.
* `Eis.eq_of_isUnit`: the six units `±1`, `±ω`, `±ω ^ 2`.
-/

namespace TuringTask

open QuadraticAlgebra

/-- The Eisenstein integers `ℤ[ω]` with `ω ^ 2 = -1 - ω`. -/
abbrev Eis : Type := QuadraticAlgebra ℤ (-1) (-1)

namespace Eis

lemma norm_eq (z : Eis) : norm z = z.re ^ 2 - z.re * z.im + z.im ^ 2 := by
  rw [norm_def]; ring

lemma four_mul_norm (z : Eis) : 4 * norm z = (2 * z.re - z.im) ^ 2 + 3 * z.im ^ 2 := by
  rw [norm_eq]; ring

lemma norm_nonneg' (z : Eis) : 0 ≤ norm z := by
  nlinarith [four_mul_norm z, sq_nonneg (2 * z.re - z.im), sq_nonneg z.im]

lemma eq_zero_of_norm_eq_zero {z : Eis} (h : norm z = 0) : z = 0 := by
  have h4 := four_mul_norm z
  rw [h] at h4
  have him : z.im = 0 := by nlinarith [sq_nonneg (2 * z.re - z.im), sq_nonneg z.im]
  have hre : z.re = 0 := by
    rw [him] at h4
    nlinarith [sq_nonneg z.re]
  ext
  · exact hre
  · exact him

lemma norm_pos {z : Eis} (hz : z ≠ 0) : 0 < norm z :=
  lt_of_le_of_ne (norm_nonneg' z) (fun h => hz (eq_zero_of_norm_eq_zero h.symm))

lemma mul_star_self (z : Eis) : z * star z = ((norm z : ℤ) : Eis) :=
  (algebraMap_norm_eq_mul_star z).symm.trans (eq_intCast _ _)

/-! ### Division with rounding -/

/-- A nearest integer to `p / n` for `n > 0`, namely `⌊(2 p + n) / (2 n)⌋`. -/
def rnd (p n : ℤ) : ℤ := (2 * p + n) / (2 * n)

lemma rnd_spec (p : ℤ) {n : ℤ} (hn : 0 < n) :
    -n ≤ 2 * (p - n * rnd p n) ∧ 2 * (p - n * rnd p n) ≤ n := by
  have h1 := Int.ediv_mul_le (2 * p + n) (b := 2 * n) (by omega)
  have h2 := Int.lt_ediv_add_one_mul_self (2 * p + n) (b := 2 * n) (by omega)
  unfold rnd
  constructor <;> nlinarith

/-- The rounded quotient: round both coordinates of `x * star y / norm y`. -/
def quo (x y : Eis) : Eis :=
  ⟨rnd (x * star y).re (norm y), rnd (x * star y).im (norm y)⟩

/-- The remainder `x - y * quo x y`. -/
def rem (x y : Eis) : Eis := x - y * quo x y

lemma quo_zero (x : Eis) : quo x 0 = 0 := by
  ext <;> simp [quo, rnd]

lemma four_norm_sub (P q : Eis) (n : ℤ) :
    4 * norm (P - (n : Eis) * q) =
      (2 * (P.re - n * q.re)) ^ 2 - (2 * (P.re - n * q.re)) * (2 * (P.im - n * q.im)) +
        (2 * (P.im - n * q.im)) ^ 2 := by
  rw [norm_eq]; simp; ring

lemma norm_rem_lt (x : Eis) {y : Eis} (hy : y ≠ 0) : norm (rem x y) < norm y := by
  have hn : 0 < norm y := norm_pos hy
  obtain ⟨h1, h2⟩ := rnd_spec (x * star y).re hn
  obtain ⟨h3, h4⟩ := rnd_spec (x * star y).im hn
  have hmul : rem x y * star y = x * star y - ((norm y : ℤ) : Eis) * quo x y := by
    rw [rem, sub_mul, ← mul_star_self]; ring
  have hkey : 4 * (norm (rem x y) * norm y) =
      (2 * ((x * star y).re - norm y * rnd (x * star y).re (norm y))) ^ 2 -
        (2 * ((x * star y).re - norm y * rnd (x * star y).re (norm y))) *
          (2 * ((x * star y).im - norm y * rnd (x * star y).im (norm y))) +
        (2 * ((x * star y).im - norm y * rnd (x * star y).im (norm y))) ^ 2 := by
    have hns : norm (rem x y) * norm y = norm (rem x y * star y) := by
      rw [map_mul, QuadraticAlgebra.norm_star]
    rw [hns, hmul, four_norm_sub]
    rfl
  generalize 2 * ((x * star y).re - norm y * rnd (x * star y).re (norm y)) = A at h1 h2 hkey
  generalize 2 * ((x * star y).im - norm y * rnd (x * star y).im (norm y)) = B at h3 h4 hkey
  nlinarith [mul_nonneg (by linarith : 0 ≤ norm y - A) (by linarith : 0 ≤ norm y + A),
    mul_nonneg (by linarith : 0 ≤ norm y - B) (by linarith : 0 ≤ norm y + B),
    mul_nonneg (by linarith : 0 ≤ norm y + A) (by linarith : 0 ≤ norm y + B),
    mul_nonneg (by linarith : 0 ≤ norm y - A) (by linarith : 0 ≤ norm y - B)]

lemma natAbs_norm_mul_le (a : Eis) {b : Eis} (hb : b ≠ 0) :
    (norm a).natAbs ≤ (norm (a * b)).natAbs := by
  have hb1 : 1 ≤ norm b := norm_pos hb
  have ha := norm_nonneg' a
  rw [map_mul]
  zify [ha, mul_nonneg ha (norm_nonneg' b)]
  rw [abs_of_nonneg ha, abs_of_nonneg (mul_nonneg ha (norm_nonneg' b))]
  nlinarith

/-- `Eis` with rounding division as a Euclidean domain. It is used locally with `letI`. -/
abbrev euclid : EuclideanDomain Eis :=
  { QuadraticAlgebra.instCommRing with
    exists_pair_ne := ⟨0, 1, fun h => by simpa using congrArg QuadraticAlgebra.re h⟩
    quotient := quo
    quotient_zero := quo_zero
    remainder := rem
    quotient_mul_add_remainder_eq := fun x y => by simp [rem]
    r := fun a b => (norm a).natAbs < (norm b).natAbs
    r_wellFounded := (measure fun z : Eis => (norm z).natAbs).wf
    remainder_lt := fun x y hy => by
      have h := norm_rem_lt x hy
      have h0 := norm_nonneg' (rem x y)
      omega
    mul_left_not_lt := fun a b hb => not_lt_of_ge (natAbs_norm_mul_le a hb) }

/-- Coprime factors of a cube in `Eis` are cubes up to a unit. -/
lemma exists_assoc_cube {x y c : Eis} (hxy : IsCoprime x y) (h : x * y = c ^ 3) :
    ∃ d : Eis, Associated (d ^ 3) x := by
  letI := euclid
  exact exists_associated_pow_of_mul_eq_pow' hxy h

/-! ### Units -/

lemma norm_eq_one_of_isUnit {w : Eis} (hw : IsUnit w) : norm w = 1 := by
  have h := (isUnit_iff_norm_isUnit.mp hw)
  rcases Int.isUnit_iff.mp h with h | h
  · exact h
  · have := norm_nonneg' w
    omega

/-- The six units of `Eis`. -/
lemma eq_of_isUnit {w : Eis} (hw : IsUnit w) :
    w = ⟨1, 0⟩ ∨ w = ⟨-1, 0⟩ ∨ w = ⟨0, 1⟩ ∨ w = ⟨0, -1⟩ ∨ w = ⟨-1, -1⟩ ∨ w = ⟨1, 1⟩ := by
  have h4 := four_mul_norm w
  rw [norm_eq_one_of_isUnit hw] at h4
  have hi1 : w.im ≤ 1 := by nlinarith [sq_nonneg (2 * w.re - w.im)]
  have hi2 : -1 ≤ w.im := by nlinarith [sq_nonneg (2 * w.re - w.im)]
  have hr1 : 2 * w.re - w.im ≤ 2 := by nlinarith [sq_nonneg w.im]
  have hr2 : -2 ≤ 2 * w.re - w.im := by nlinarith [sq_nonneg w.im]
  have hr3 : w.re ≤ 1 := by omega
  have hr4 : -1 ≤ w.re := by omega
  obtain ⟨r, i⟩ := w
  simp only at hi1 hi2 hr3 hr4 h4 ⊢
  interval_cases r <;> interval_cases i <;> simp_all

end Eis

end TuringTask
