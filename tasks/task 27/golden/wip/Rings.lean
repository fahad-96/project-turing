import Mathlib
import TuringTask.Euclid

/-!
# The three Euclidean rings and their primes

* `R1 = ℤ[ω]`, `ω^2 = -1 - ω` (norm `x^2 - x y + y^2`, discriminant `-3`, 6 units),
  `R3 = ℤ[√-2]` (norm `x^2 + 2 y^2`, discriminant `-8`, 2 units) and
  `R4 = ℤ[t]`, `t^2 = -2 + t` (norm `x^2 + x y + 2 y^2`, discriminant `-7`, 2 units).
* `quo2` rounds both coordinates of `x ȳ / N(y)`. This works for `R1` and `R3`, where the
  remainder has norm at most `3/4` of `N(y)`. For `R4`, `quo4` rounds the second coordinate first
  and then `2 A + B`, which gives the bound `11/16`.
* `type1`, `type3`, `type4`: for every prime `p` the character value decides whether `p` splits
  (`p = π π̄` with `π ∤ π̄`), ramifies (`π ∣ π̄`) or stays prime. The characters are
  `χ1 d = J(d | 3)`, `χ3 d = J(-2 | d)` and `χ4 d = J(d | 7)`, as in the prompt, and
  `jacobiSym.mod_right` matches them with `J(-3 | p)`, `J(-8 | p)` and `J(-7 | p)`.
-/

namespace TuringTask

variable {a b : ℤ}

local notation "Nm" => QuadraticAlgebra.norm

/-- Round both coordinates of `x ȳ / N(y)`. -/
def quo2 (x y : QuadraticAlgebra ℤ a b) : QuadraticAlgebra ℤ a b :=
  ⟨rnd (x * star y).re (Nm y), rnd (x * star y).im (Nm y)⟩

lemma quo2_zero (x : QuadraticAlgebra ℤ a b) : quo2 x 0 = 0 := by
  ext <;> simp [quo2, rnd, QuadraticAlgebra.norm_zero]

lemma rem_norm (x y q : QuadraticAlgebra ℤ a b) :
    Nm (x - y * q) * Nm y =
      ((x * star y).re - Nm y * q.re) ^ 2 +
        b * ((x * star y).re - Nm y * q.re) * ((x * star y).im - Nm y * q.im) -
        a * ((x * star y).im - Nm y * q.im) ^ 2 := by
  rw [norm_rem_mul, intCast_mul_mk]
  rw [show (x * star y - (⟨Nm y * q.re, Nm y * q.im⟩ : QuadraticAlgebra ℤ a b)) =
    ⟨(x * star y).re - Nm y * q.re, (x * star y).im - Nm y * q.im⟩ by ext <;> simp, norm_mk]

/-- The bound for `quo2` from a bound on the norm form over the box `[-n/2, n/2]^2`. -/
lemma quo2_lt (hD : b ^ 2 + 4 * a < 0)
    (hb : ∀ A B n : ℤ, 0 < n → -n ≤ 2 * A → 2 * A ≤ n → -n ≤ 2 * B → 2 * B ≤ n →
      A ^ 2 + b * A * B - a * B ^ 2 < n ^ 2)
    (x y : QuadraticAlgebra ℤ a b) (hy : y ≠ 0) : Nm (x - y * quo2 x y) < Nm y := by
  have hn : 0 < Nm y := lt_of_le_of_ne (norm_nonneg' hD y)
    (fun h => hy (eq_zero_of_norm_eq_zero hD h.symm))
  have key := rem_norm x y (quo2 x y)
  obtain ⟨h1, h2⟩ := rnd_spec (x * star y).re hn
  obtain ⟨h3, h4⟩ := rnd_spec (x * star y).im hn
  have hlt := hb _ _ _ hn h1 h2 h3 h4
  have e1 : (quo2 x y).re = rnd (x * star y).re (Nm y) := rfl
  have e2 : (quo2 x y).im = rnd (x * star y).im (Nm y) := rfl
  rw [e1, e2] at key
  rw [← key] at hlt
  by_contra hc
  push Not at hc
  nlinarith [norm_nonneg' hD (x - y * quo2 x y)]

/-! ### `R1`: `a = b = -1` -/

lemma bound1 (A B n : ℤ) (hn : 0 < n) (h1 : -n ≤ 2 * A) (h2 : 2 * A ≤ n) (h3 : -n ≤ 2 * B)
    (h4 : 2 * B ≤ n) : A ^ 2 + (-1) * A * B - (-1) * B ^ 2 < n ^ 2 := by
  nlinarith [mul_nonneg (by linarith : 0 ≤ n - 2 * A) (by linarith : 0 ≤ n + 2 * A),
    mul_nonneg (by linarith : 0 ≤ n - 2 * B) (by linarith : 0 ≤ n + 2 * B),
    mul_nonneg (by linarith : 0 ≤ n + 2 * A) (by linarith : 0 ≤ n + 2 * B),
    mul_nonneg (by linarith : 0 ≤ n - 2 * A) (by linarith : 0 ≤ n - 2 * B)]

lemma hIP1 (z : QuadraticAlgebra ℤ (-1) (-1)) (hz : Irreducible z) : Prime z :=
  prime_of_irreducible (by norm_num) quo2 quo2_zero (quo2_lt (by norm_num) bound1) hz

/-! ### `R3`: `a = -2`, `b = 0` -/

lemma bound3 (A B n : ℤ) (hn : 0 < n) (h1 : -n ≤ 2 * A) (h2 : 2 * A ≤ n) (h3 : -n ≤ 2 * B)
    (h4 : 2 * B ≤ n) : A ^ 2 + 0 * A * B - (-2) * B ^ 2 < n ^ 2 := by
  nlinarith [mul_nonneg (by linarith : 0 ≤ n - 2 * A) (by linarith : 0 ≤ n + 2 * A),
    mul_nonneg (by linarith : 0 ≤ n - 2 * B) (by linarith : 0 ≤ n + 2 * B)]

lemma hIP3 (z : QuadraticAlgebra ℤ (-2) 0) (hz : Irreducible z) : Prime z :=
  prime_of_irreducible (by norm_num) quo2 quo2_zero (quo2_lt (by norm_num) bound3) hz

/-! ### `R4`: `a = -2`, `b = 1` -/

/-- Round the second coordinate, then `2 A + B`. -/
def quo4 (x y : QuadraticAlgebra ℤ (-2) 1) : QuadraticAlgebra ℤ (-2) 1 :=
  ⟨rnd (2 * (x * star y).re + ((x * star y).im - Nm y * rnd (x * star y).im (Nm y))) (2 * Nm y),
    rnd (x * star y).im (Nm y)⟩

lemma quo4_zero (x : QuadraticAlgebra ℤ (-2) 1) : quo4 x 0 = 0 := by
  ext <;> simp [quo4, rnd, QuadraticAlgebra.norm_zero]

lemma quo4_lt (x y : QuadraticAlgebra ℤ (-2) 1) (hy : y ≠ 0) : Nm (x - y * quo4 x y) < Nm y := by
  have hD : (1 : ℤ) ^ 2 + 4 * (-2) < 0 := by norm_num
  have hn : 0 < Nm y := lt_of_le_of_ne (norm_nonneg' hD y)
    (fun h => hy (eq_zero_of_norm_eq_zero hD h.symm))
  have key := rem_norm x y (quo4 x y)
  have e1 : (quo4 x y).re = rnd (2 * (x * star y).re + ((x * star y).im -
      Nm y * rnd (x * star y).im (Nm y))) (2 * Nm y) := rfl
  have e2 : (quo4 x y).im = rnd (x * star y).im (Nm y) := rfl
  rw [e1, e2] at key
  set n := Nm y
  set P := x * star y
  obtain ⟨h3, h4⟩ := rnd_spec P.im hn
  set B := P.im - n * rnd P.im n with hB
  obtain ⟨h1, h2⟩ := rnd_spec (2 * P.re + B) (show 0 < 2 * n by omega)
  set A := P.re - n * rnd (2 * P.re + B) (2 * n) with hA
  have hAB1 : -n ≤ 2 * A + B := by rw [hA]; nlinarith
  have hAB2 : 2 * A + B ≤ n := by rw [hA]; nlinarith
  have h0 := norm_nonneg' hD (x - y * quo4 x y)
  have : 4 * (A ^ 2 + 1 * A * B - (-2) * B ^ 2) < 4 * n ^ 2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ n - (2 * A + B)) (by linarith : 0 ≤ n + (2 * A + B)),
      mul_nonneg (by linarith : 0 ≤ n - 2 * B) (by linarith : 0 ≤ n + 2 * B)]
  by_contra hc
  push Not at hc
  nlinarith

lemma hIP4 (z : QuadraticAlgebra ℤ (-2) 1) (hz : Irreducible z) : Prime z :=
  prime_of_irreducible (by norm_num) quo4 quo4_zero quo4_lt hz

end TuringTask
