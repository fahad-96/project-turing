import Mathlib
import TuringTask.Count

/-!
# Euclidean division in `ℤ[ω]` and the type of each rational prime

* `rnd`, `rnd_spec`: a nearest integer to `p / n`.
* `euclidOf`: a rounded quotient `quo` with `N(x - y quo x y) < N(y)` makes
  `QuadraticAlgebra ℤ a b` a Euclidean domain. It is a definition and is used with `letI`, so
  irreducible elements are prime (`prime_of_irreducible`).
* `norm_rem_mul`: `N(x - y q) N(y) = N(x ȳ - N(y) q)`, which reduces the bound to the two
  coordinates of `x ȳ - N(y) q`.
* `prime_of_norm_prime`, `prime_or_norm`: an element of prime norm is prime, and a rational
  prime `p` is prime in the ring unless `p = N(π)` for some `π`.
* `not_dvd_star`: if `N(π) = p` and `p ∤ b^2 + 4 a`, then `π ∤ π̄`.
* `sq_of_norm`: if `N(π) = p` with `p` odd and `p ∤ b^2 + 4 a`, then `b^2 + 4 a` is a square
  modulo `p`, so `J(b^2 + 4 a | p) = 1`.
* `exists_norm_of_sq`: conversely, if `b^2 + 4 a` is a square modulo an odd prime `p`, then
  `p = N(π)` for some `π`.
-/

namespace TuringTask

variable {a b : ℤ}

local notation "Nm" => QuadraticAlgebra.norm

/-- A nearest integer to `p / n` for `n > 0`. -/
def rnd (p n : ℤ) : ℤ := (2 * p + n) / (2 * n)

lemma rnd_spec (p : ℤ) {n : ℤ} (hn : 0 < n) :
    -n ≤ 2 * (p - n * rnd p n) ∧ 2 * (p - n * rnd p n) ≤ n := by
  have h1 := Int.ediv_mul_le (2 * p + n) (b := 2 * n) (by omega)
  have h2 := Int.lt_ediv_add_one_mul_self (2 * p + n) (b := 2 * n) (by omega)
  unfold rnd
  constructor <;> nlinarith

lemma norm_rem_mul (x y q : QuadraticAlgebra ℤ a b) :
    Nm (x - y * q) * Nm y = Nm (x * star y - ((Nm y : ℤ) : QuadraticAlgebra ℤ a b) * q) := by
  have h : (x - y * q) * star y = x * star y - ((Nm y : ℤ) : QuadraticAlgebra ℤ a b) * q := by
    rw [intCast_norm]; ring
  rw [← h, map_mul, QuadraticAlgebra.norm_star]

/-- `QuadraticAlgebra ℤ a b` as a Euclidean domain, from a rounded quotient. -/
abbrev euclidOf (hD : b ^ 2 + 4 * a < 0) (quo : QuadraticAlgebra ℤ a b → QuadraticAlgebra ℤ a b →
    QuadraticAlgebra ℤ a b) (hq0 : ∀ x, quo x 0 = 0)
    (hlt : ∀ x y, y ≠ 0 → Nm (x - y * quo x y) < Nm y) : EuclideanDomain (QuadraticAlgebra ℤ a b) :=
  { QuadraticAlgebra.instCommRing with
    exists_pair_ne := ⟨0, 1, fun h => by
      have h' := congrArg QuadraticAlgebra.re h
      change (0 : ℤ) = 1 at h'
      omega⟩
    quotient := quo
    quotient_zero := hq0
    remainder := fun x y => x - y * quo x y
    quotient_mul_add_remainder_eq := fun x y => by simp
    r := fun u v => (Nm u).natAbs < (Nm v).natAbs
    r_wellFounded := (measure fun z : QuadraticAlgebra ℤ a b => (Nm z).natAbs).wf
    remainder_lt := fun x y hy => by
      have h := hlt x y hy
      have h0 := norm_nonneg' hD (x - y * quo x y)
      omega
    mul_left_not_lt := fun u v hv => by
      have hb1 : 1 ≤ Nm v := by
        rcases (norm_nonneg' hD v).lt_or_eq with h | h
        · exact h
        · exact absurd (eq_zero_of_norm_eq_zero hD h.symm) hv
      have hu := norm_nonneg' hD u
      simp only [map_mul, not_lt]
      rw [Int.natAbs_mul]
      exact Nat.le_mul_of_pos_right _ (by omega) }

lemma prime_of_irreducible (hD : b ^ 2 + 4 * a < 0) (quo : QuadraticAlgebra ℤ a b →
    QuadraticAlgebra ℤ a b → QuadraticAlgebra ℤ a b) (hq0 : ∀ x, quo x 0 = 0)
    (hlt : ∀ x y, y ≠ 0 → Nm (x - y * quo x y) < Nm y) {z : QuadraticAlgebra ℤ a b}
    (hz : Irreducible z) : Prime z := by
  letI := euclidOf hD quo hq0 hlt
  exact hz.prime

lemma isUnit_of_norm_one {z : QuadraticAlgebra ℤ a b} (h : Nm z = 1) : IsUnit z :=
  QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr (by rw [h]; exact isUnit_one)

lemma norm_one_of_isUnit (hD : b ^ 2 + 4 * a < 0) {z : QuadraticAlgebra ℤ a b} (h : IsUnit z) :
    Nm z = 1 := by
  rcases Int.isUnit_iff.mp (QuadraticAlgebra.isUnit_iff_norm_isUnit.mp h) with h | h
  · exact h
  · have := norm_nonneg' hD z; omega

lemma irreducible_of_norm_prime (hD : b ^ 2 + 4 * a < 0) {π : QuadraticAlgebra ℤ a b} {p : ℕ}
    (hp : p.Prime) (h : Nm π = p) : Irreducible π := by
  refine ⟨fun hu => ?_, fun x y hxy => ?_⟩
  · have := norm_one_of_isUnit hD hu
    rw [h] at this
    exact hp.one_lt.ne' (by exact_mod_cast this)
  · have hn := congrArg QuadraticAlgebra.norm hxy
    rw [h, map_mul] at hn
    have hx := norm_nonneg' hD x
    have hy := norm_nonneg' hD y
    have hnat : (Nm x).toNat * (Nm y).toNat = p := by
      have : (((Nm x).toNat * (Nm y).toNat : ℕ) : ℤ) = p := by
        push_cast; rw [Int.toNat_of_nonneg hx, Int.toNat_of_nonneg hy]; exact hn.symm
      exact_mod_cast this
    rcases (Nat.prime_mul_iff.mp (hnat ▸ hp)) with ⟨-, h1⟩ | ⟨-, h1⟩
    · right
      exact isUnit_of_norm_one (by omega)
    · left
      exact isUnit_of_norm_one (by omega)

lemma prime_or_norm (hD : b ^ 2 + 4 * a < 0)
    (hIP : ∀ z : QuadraticAlgebra ℤ a b, Irreducible z → Prime z) {p : ℕ} (hp : p.Prime) :
    (∃ π : QuadraticAlgebra ℤ a b, Nm π = p) ∨ Prime ((p : ℤ) : QuadraticAlgebra ℤ a b) := by
  by_cases hirr : Irreducible ((p : ℤ) : QuadraticAlgebra ℤ a b)
  · exact Or.inr (hIP _ hirr)
  · left
    have hnu : ¬ IsUnit ((p : ℤ) : QuadraticAlgebra ℤ a b) := by
      intro hu
      have := norm_one_of_isUnit hD hu
      rw [QuadraticAlgebra.norm_intCast] at this
      push_cast at this
      have h1 : (1 : ℤ) < p := by exact_mod_cast hp.one_lt
      nlinarith
    rw [irreducible_iff] at hirr
    push Not at hirr
    obtain ⟨x, y, hxy, hx, hy⟩ := hirr hnu
    have hn := congrArg QuadraticAlgebra.norm hxy
    rw [QuadraticAlgebra.norm_intCast, map_mul] at hn
    have hx0 := norm_nonneg' hD x
    have hy0 := norm_nonneg' hD y
    have hx1 : Nm x ≠ 1 := fun h => hx (isUnit_of_norm_one h)
    have hy1 : Nm y ≠ 1 := fun h => hy (isUnit_of_norm_one h)
    have hdvd : (Nm x).toNat ∣ p ^ 2 := by
      refine ⟨(Nm y).toNat, ?_⟩
      have : ((p ^ 2 : ℕ) : ℤ) = (((Nm x).toNat * (Nm y).toNat : ℕ) : ℤ) := by
        push_cast; rw [Int.toNat_of_nonneg hx0, Int.toNat_of_nonneg hy0]; exact hn
      exact_mod_cast this
    obtain ⟨i, hi, hix⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    interval_cases i
    · exfalso; apply hx1; simp at hix; omega
    · exact ⟨x, by rw [← Int.toNat_of_nonneg hx0, hix]; simp⟩
    · exfalso
      apply hy1
      have hxp : Nm x = (p : ℤ) ^ 2 := by
        rw [← Int.toNat_of_nonneg hx0, hix]; push_cast; ring
      rw [hxp] at hn
      have hp0 : (p : ℤ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast hp.ne_zero)
      have := mul_left_cancel₀ hp0 (hn.symm.trans (mul_one _).symm)
      exact this

lemma prime_int {p : ℕ} (hp : p.Prime) : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp

lemma intCast_mul_mk (c : ℤ) (u : QuadraticAlgebra ℤ a b) :
    (c : QuadraticAlgebra ℤ a b) * u = ⟨c * u.re, c * u.im⟩ := by
  ext <;> simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]

/-- No `p^2` divides a prime norm `p`, so `p ∤ x` or `p ∤ y`. -/
lemma not_dvd_both {π : QuadraticAlgebra ℤ a b} {p : ℕ} (hp : p.Prime) (hπ : Nm π = p)
    (hx : (p : ℤ) ∣ π.re) (hy : (p : ℤ) ∣ π.im) : False := by
  obtain ⟨x, hx⟩ := hx
  obtain ⟨y, hy⟩ := hy
  have h := QuadraticAlgebra.norm_def π
  rw [hπ, hx, hy] at h
  have hp1 : (1 : ℤ) < p := by exact_mod_cast hp.one_lt
  have : (p : ℤ) ∣ 1 := ⟨x * x + b * x * y - a * y * y, by
    have hp0 : (p : ℤ) ≠ 0 := by omega
    apply mul_left_cancel₀ hp0
    linear_combination h⟩
  have := Int.le_of_dvd one_pos this
  omega

lemma not_dvd_star {π : QuadraticAlgebra ℤ a b} {p : ℕ} (hp : p.Prime)
    (hπ : Nm π = p) (hpD : ¬ (p : ℤ) ∣ b ^ 2 + 4 * a) : ¬ π ∣ star π := by
  intro h
  have h1 : π ∣ star π - π := dvd_sub h dvd_rfl
  have h2 := map_dvd QuadraticAlgebra.norm h1
  have e : star π - π = ⟨b * π.im, -2 * π.im⟩ := by
    ext <;> simp [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]; ring
  rw [e, hπ, norm_mk] at h2
  have hp' := prime_int hp
  have hy : (p : ℤ) ∣ π.im := by
    have : (p : ℤ) ∣ -(b ^ 2 + 4 * a) * π.im ^ 2 := by
      have e2 : (b * π.im) ^ 2 + b * (b * π.im) * (-2 * π.im) - a * (-2 * π.im) ^ 2 =
          -(b ^ 2 + 4 * a) * π.im ^ 2 := by ring
      rw [← e2]; exact h2
    rcases hp'.dvd_or_dvd this with h3 | h3
    · exact absurd (dvd_neg.mp h3) hpD
    · exact hp'.dvd_of_dvd_pow h3
  have hx : (p : ℤ) ∣ π.re := by
    have e3 : π.re ^ 2 = Nm π - b * π.re * π.im + a * π.im ^ 2 := by
      rw [QuadraticAlgebra.norm_def]; ring
    have : (p : ℤ) ∣ π.re ^ 2 := by
      rw [e3, hπ]
      exact dvd_add (dvd_sub dvd_rfl (Dvd.dvd.mul_left hy _))
        (Dvd.dvd.mul_left (dvd_pow hy two_ne_zero) _)
    exact hp'.dvd_of_dvd_pow this
  exact not_dvd_both hp hπ hx hy

/-- A prime norm `p` (odd, prime to `b^2 + 4 a`) makes `b^2 + 4 a` a square modulo `p`. -/
lemma jacobi_of_norm {π : QuadraticAlgebra ℤ a b} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hπ : Nm π = p) (hpD : ¬ (p : ℤ) ∣ b ^ 2 + 4 * a) : jacobiSym (b ^ 2 + 4 * a) p = 1 := by
  haveI := Fact.mk hp
  have hp' := prime_int hp
  have h4 := four_norm π
  rw [hπ] at h4
  have hy : ¬ (p : ℤ) ∣ π.im := by
    intro hy
    have h5 : (p : ℤ) ∣ (2 * π.re + b * π.im) ^ 2 := by
      have : (2 * π.re + b * π.im) ^ 2 = 4 * p + (b ^ 2 + 4 * a) * π.im ^ 2 := by linarith
      rw [this]
      exact dvd_add (Dvd.dvd.mul_left dvd_rfl _) (Dvd.dvd.mul_left (dvd_pow hy two_ne_zero) _)
    have h6 : (p : ℤ) ∣ 2 * π.re := by
      have := hp'.dvd_of_dvd_pow h5
      have h7 : (p : ℤ) ∣ b * π.im := Dvd.dvd.mul_left hy _
      have := dvd_sub this h7
      simpa using this
    have h8 : (p : ℤ) ∣ π.re := by
      rcases hp'.dvd_or_dvd h6 with h | h
      · exfalso
        have := Int.le_of_dvd (by norm_num) h
        have h2 := hp.two_le
        have : (p : ℤ) = 2 := by omega
        exact hp2 (by exact_mod_cast this)
      · exact h
    exact not_dvd_both hp hπ h8 hy
  have hy0 : ((π.im : ℤ) : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hD0 : ((b ^ 2 + 4 * a : ℤ) : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_one_iff p hD0]
  refine ⟨((2 * π.re + b * π.im : ℤ) : ZMod p) * ((π.im : ℤ) : ZMod p)⁻¹, ?_⟩
  have hz : ((4 * (p : ℤ) : ℤ) : ZMod p) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact Dvd.dvd.mul_left dvd_rfl _
  have := congrArg (Int.cast : ℤ → ZMod p) h4
  push_cast at this hz
  rw [hz] at this
  field_simp
  push_cast
  linear_combination this

/-- If `b^2 + 4 a` is a square modulo an odd prime `p`, then `p` is a norm. -/
lemma exists_norm_of_jacobi (hD : b ^ 2 + 4 * a < 0)
    (hIP : ∀ z : QuadraticAlgebra ℤ a b, Irreducible z → Prime z) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : jacobiSym (b ^ 2 + 4 * a) p = 1) :
    ∃ π : QuadraticAlgebra ℤ a b, Nm π = p := by
  haveI := Fact.mk hp
  have hp' := prime_int hp
  obtain ⟨s, hs⟩ := ZMod.isSquare_of_jacobiSym_eq_one h
  have ht : (p : ℤ) ∣ (s.val : ℤ) ^ 2 - (b ^ 2 + 4 * a) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val s, sq, ← hs]
    push_cast
    ring
  set t : ℤ := (s.val : ℤ)
  have hodd : (p : ℤ) % 2 = 1 := by
    have := hp.eq_one_or_self_of_dvd 2
    rcases Nat.even_or_odd p with ⟨r, hr⟩ | ⟨r, hr⟩
    · exfalso
      rcases this ⟨r, by omega⟩ with h | h <;> omega
    · omega
  set x : ℤ := (t - b) * (((p : ℤ) + 1) / 2)
  have hx : 2 * x + b - t = (t - b) * p := by
    have : 2 * (((p : ℤ) + 1) / 2) = p + 1 := by omega
    rw [show 2 * x = (t - b) * (2 * (((p : ℤ) + 1) / 2)) by ring, this]; ring
  set z : QuadraticAlgebra ℤ a b := ⟨x, 1⟩
  have hz4 : (p : ℤ) ∣ 4 * Nm z := by
    rw [four_norm]
    simp only [z]
    have : (2 * x + b * 1) ^ 2 - (b ^ 2 + 4 * a) * 1 ^ 2 =
        (2 * x + b - t) * (2 * x + b + t) + (t ^ 2 - (b ^ 2 + 4 * a)) := by ring
    rw [this, hx]
    exact dvd_add (Dvd.dvd.mul_right (Dvd.dvd.mul_left dvd_rfl _) _) ht
  have hz : (p : ℤ) ∣ Nm z := by
    rcases hp'.dvd_or_dvd hz4 with h4 | h4
    · exfalso
      have := Int.le_of_dvd (by norm_num) h4
      have h2 := hp.two_le
      have h44 : (p : ℤ) ∣ 2 ^ 2 := by simpa using h4
      have := hp'.dvd_of_dvd_pow h44
      have := Int.le_of_dvd (by norm_num) this
      have : (p : ℤ) = 2 := by omega
      exact hp2 (by exact_mod_cast this)
    · exact h4
  rcases prime_or_norm hD hIP hp with h | h
  · exact h
  · exfalso
    obtain ⟨m, hm⟩ := hz
    have hzz : ((p : ℤ) : QuadraticAlgebra ℤ a b) ∣ z * star z := by
      rw [← intCast_norm, hm]
      exact ⟨(m : QuadraticAlgebra ℤ a b), by push_cast; ring⟩
    rcases h.dvd_or_dvd hzz with ⟨u, hu⟩ | ⟨u, hu⟩
    · have := congrArg QuadraticAlgebra.im hu
      rw [intCast_mul_mk] at this
      have h1 : (p : ℤ) ∣ 1 := ⟨u.im, by simpa [z] using this⟩
      have := Int.le_of_dvd one_pos h1
      have := hp.two_le
      omega
    · have := congrArg QuadraticAlgebra.im hu
      rw [intCast_mul_mk] at this
      have h1 : (p : ℤ) ∣ 1 := ⟨-u.im, by simp [z] at this; linarith⟩
      have := Int.le_of_dvd one_pos h1
      have := hp.two_le
      omega

end TuringTask
