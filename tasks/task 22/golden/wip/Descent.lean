import Mathlib
import TuringTask.EulerCube

/-!
# The equation `x ^ 3 + y ^ 3 = 2 z ^ 3`

`two_cubes`: every integer solution has `x = y` or `x + y = 0` (Euler's descent).

For coprime `x`, `y` both are odd. With `u = (x + y) / 2` and `v = (x - y) / 2` the equation
reads `u (u ^ 2 + 3 v ^ 2) = z ^ 3`.
* If `3 ∤ u`, the two factors are coprime cubes, and `euler_cube` gives
  `u = a (a - 3 b) (a + 3 b)` with three coprime cubes `e ^ 3`, `f ^ 3`, `g ^ 3`; then
  `f ^ 3 + g ^ 3 = 2 e ^ 3`.
* If `u = 3 w`, then `9 w (v ^ 2 + 3 w ^ 2) = z ^ 3`, `euler_cube` on `v ^ 2 + 3 w ^ 2` gives
  `w = 3 b (a - b) (a + b)`, and `g ^ 3 + (-f) ^ 3 = 2 e ^ 3` with `b = e ^ 3`.
In both cases `0 < |e| < |z|`, and the new solution is again nontrivial.
-/

namespace TuringTask

lemma cube_inj {a b : ℤ} (h : a ^ 3 = b ^ 3) : a = b :=
  (Odd.pow_inj (by decide)).mp h

lemma not_isCoprime_of_two_dvd {a b : ℤ} (ha : (2 : ℤ) ∣ a) (hb : (2 : ℤ) ∣ b) :
    ¬ IsCoprime a b := by
  intro h
  rcases Int.isUnit_iff.mp (h.isUnit_of_dvd' ha hb) with h2 | h2 <;> omega

lemma isCoprime_of_not_three_dvd {a : ℤ} (h : ¬ (3 : ℤ) ∣ a) : IsCoprime a 3 :=
  ((Prime.coprime_iff_not_dvd Int.prime_three).mpr h).symm

/-- Coprimality facts for `a ± c` from `a`, `c` coprime. -/
lemma isCoprime_add_sub {a c : ℤ} (h : IsCoprime a c) :
    IsCoprime a (a - c) ∧ IsCoprime a (a + c) ∧ IsCoprime c (a - c) ∧ IsCoprime c (a + c) := by
  obtain ⟨e, f, hef⟩ := h
  exact ⟨⟨e + f, -f, by linear_combination hef⟩, ⟨e - f, f, by linear_combination hef⟩,
    ⟨e + f, e, by linear_combination hef⟩, ⟨f - e, e, by linear_combination hef⟩⟩

/-- `a - c` and `a + c` are coprime when `a`, `c` are coprime and `a - c` is odd. -/
lemma isCoprime_sub_add {a c : ℤ} (h : IsCoprime a c) (ho : Odd (a - c)) :
    IsCoprime (a - c) (a + c) := by
  obtain ⟨e, f, hef⟩ := h
  obtain ⟨t, ht⟩ := ho
  exact ⟨1 - t * e + t * f, -(t * e) - t * f, by linear_combination ht - 2 * t * hef⟩

/-- Three pairwise coprime integers with a cube product are cubes. -/
lemma cubes_of_mul {a b c r : ℤ} (hab : IsCoprime a b) (hac : IsCoprime a c)
    (hbc : IsCoprime b c) (h : a * (b * c) = r ^ 3) :
    ∃ x y z : ℤ, a = x ^ 3 ∧ b = y ^ 3 ∧ c = z ^ 3 := by
  obtain ⟨x, hx⟩ := Int.eq_pow_of_mul_eq_pow_odd_left (hab.mul_right hac) (by decide) h
  obtain ⟨t, ht⟩ := Int.eq_pow_of_mul_eq_pow_odd_right (hab.mul_right hac) (by decide) h
  obtain ⟨y, hy⟩ := Int.eq_pow_of_mul_eq_pow_odd_left hbc (by decide) ht
  obtain ⟨z, hz⟩ := Int.eq_pow_of_mul_eq_pow_odd_right hbc (by decide) ht
  exact ⟨x, y, z, hx, hy, hz⟩

/-- The pair `(a ^ 3 - 9 a b ^ 2, 3 a ^ 2 b - 3 b ^ 3)` of `euler_cube`: if it is coprime, then
`a`, `b` are coprime and of different parity. -/
lemma euler_pair {a b : ℤ}
    (h : IsCoprime (a ^ 3 - 9 * a * b ^ 2) (3 * a ^ 2 * b - 3 * b ^ 3)) :
    IsCoprime a b ∧ Odd (a - b) ∧ Odd (a - 3 * b) := by
  have hab : IsCoprime a b := by
    obtain ⟨m, n, hmn⟩ := h
    exact ⟨m * a ^ 2 - 9 * m * b ^ 2 + 3 * n * a * b, -(3 * n * b ^ 2),
      by linear_combination hmn⟩
  have hodd : Odd (a - b) := by
    rcases Int.even_or_odd (a - b) with he | ho
    · exfalso
      have key : ∀ x y : ZMod 2, x - y = 0 →
          x ^ 3 - 9 * x * y ^ 2 = 0 ∧ 3 * x ^ 2 * y - 3 * y ^ 3 = 0 := by decide
      rw [← ZMod.intCast_eq_zero_iff_even] at he
      push_cast at he
      obtain ⟨h1, h2⟩ := key _ _ he
      refine not_isCoprime_of_two_dvd ?_ ?_ h
      · rw [← even_iff_two_dvd, ← ZMod.intCast_eq_zero_iff_even]; push_cast; exact h1
      · rw [← even_iff_two_dvd, ← ZMod.intCast_eq_zero_iff_even]; push_cast; exact h2
    · exact ho
  refine ⟨hab, hodd, ?_⟩
  have : a - 3 * b = (a - b) - 2 * b := by ring
  rw [this]
  exact hodd.sub_even (even_two_mul b)

lemma sq_add_three_sq_ge {u v : ℤ} (hv : v ≠ 0) : 3 ≤ u ^ 2 + 3 * v ^ 2 := by
  have : 1 ≤ v ^ 2 := by
    have := sq_pos_of_ne_zero hv
    omega
  nlinarith [sq_nonneg u]

lemma natAbs_lt_of_cube {e z : ℤ} (h : |e| ^ 3 < |z| ^ 3) : e.natAbs < z.natAbs := by
  have h' : |e| < |z| := lt_of_pow_lt_pow_left₀ 3 (abs_nonneg z) h
  zify
  exact h'

/-- One descent step for `x = u + v`, `y = u - v`: a nontrivial solution with smaller `|z|`. -/
lemma descent_step {u v z : ℤ} (huv : IsCoprime u v) (hu : u ≠ 0) (hv : v ≠ 0)
    (h : u * (u ^ 2 + 3 * v ^ 2) = z ^ 3) :
    ∃ f g e : ℤ, IsCoprime f g ∧ f ^ 3 + g ^ 3 = 2 * e ^ 3 ∧ f ≠ g ∧ f + g ≠ 0 ∧
      e.natAbs < z.natAbs := by
  have hpos : 0 < u ^ 2 + 3 * v ^ 2 := by linarith [sq_add_three_sq_ge (u := u) hv]
  have hz3 : |z| ^ 3 = |u| * (u ^ 2 + 3 * v ^ 2) := by
    rw [← abs_pow, ← h, abs_mul, abs_of_pos hpos]
  by_cases h3 : (3 : ℤ) ∣ u
  · -- `u = 3 w`
    obtain ⟨w, rfl⟩ := h3
    have hw : w ≠ 0 := by rintro rfl; simp at hu
    have hwv : IsCoprime w v := huv.of_mul_left_right
    have h3v : ¬ (3 : ℤ) ∣ v := fun hd =>
      Int.prime_three.not_unit (huv.isUnit_of_dvd' (dvd_mul_right 3 w) hd)
    have hv3 : IsCoprime v 3 := isCoprime_of_not_three_dvd h3v
    have hc1 : IsCoprime v (3 * w) := hv3.mul_right hwv.symm
    have hcop : IsCoprime (9 * w) (v ^ 2 + 3 * w ^ 2) := by
      refine IsCoprime.mul_left ?_ ?_
      · have : IsCoprime (3 : ℤ) (v ^ 2 + 3 * w ^ 2) := by
          have := (hv3.symm.pow_right (n := 2)).add_mul_left_right (w ^ 2)
          convert this using 1
        convert this.pow_left (m := 2) using 1; norm_num
      · rw [show v ^ 2 + 3 * w ^ 2 = v ^ 2 + w * (3 * w) by ring]
        exact (hwv.pow_right (n := 2)).add_mul_left_right (3 * w)
    have hz : 9 * w * (v ^ 2 + 3 * w ^ 2) = z ^ 3 := by rw [← h]; ring
    obtain ⟨r, hr⟩ := Int.eq_pow_of_mul_eq_pow_odd_left hcop (by decide) hz
    obtain ⟨s, hs⟩ := Int.eq_pow_of_mul_eq_pow_odd_right hcop (by decide) hz
    obtain ⟨a, b, ha, hb⟩ := Eis.euler_cube hc1 hs
    have hvw : IsCoprime (a ^ 3 - 9 * a * b ^ 2) (3 * a ^ 2 * b - 3 * b ^ 3) := by
      rw [← ha, ← hb]; exact hwv.symm
    obtain ⟨hab, hodd, -⟩ := euler_pair hvw
    obtain ⟨h1, h2, h3, h4⟩ := isCoprime_add_sub hab
    -- `r = 3 r'` and `b (a - b) (a + b) = r' ^ 3`
    have h3r : (3 : ℤ) ∣ r := Int.prime_three.dvd_of_dvd_pow (n := 3)
      ⟨9 * (3 * a ^ 2 * b - 3 * b ^ 3) / 3 * 1, by rw [← hr, hb]; ring_nf; omega⟩
    obtain ⟨r', rfl⟩ := h3r
    have hprod : b * ((a - b) * (a + b)) = r' ^ 3 := by
      have : (27 : ℤ) * (b * ((a - b) * (a + b))) = 27 * r' ^ 3 := by
        rw [show (27 : ℤ) * r' ^ 3 = (3 * r') ^ 3 by ring, ← hr, hb]; ring
      exact mul_left_cancel₀ (by norm_num) this
    obtain ⟨e, f, g, hbe, hf, hg⟩ :=
      cubes_of_mul h3 h4 (isCoprime_sub_add hab hodd) hprod
    have hb0 : b ≠ 0 := by rintro rfl; apply hw; rw [hb]; ring
    have ha0 : a ≠ 0 := by rintro rfl; apply hv; rw [ha]; ring
    refine ⟨g, -f, e, ?_, ?_, ?_, ?_, ?_⟩
    · have := (isCoprime_sub_add hab hodd).symm
      rw [hf, hg] at this
      exact ((IsCoprime.pow_iff (by norm_num) (by norm_num)).mp this).neg_right
    · rw [Odd.neg_pow (by decide), ← hf, ← hg, ← hbe]; ring
    · intro hgf
      apply ha0
      have : a + b = -(a - b) := by rw [hf, hg, hgf]; ring
      linarith
    · intro hgf
      apply hb0
      have : a + b = a - b := by rw [hf, hg, show g = f by linarith]
      linarith
    · apply natAbs_lt_of_cube
      have he0 : 0 < |e| ^ 3 := by
        have : e ≠ 0 := by rintro rfl; apply hb0; rw [hbe]; ring
        positivity
      have hw' : |w| = 3 * |e| ^ 3 * |(a - b) * (a + b)| := by
        rw [hb, show 3 * a ^ 2 * b - 3 * b ^ 3 = 3 * b * ((a - b) * (a + b)) by ring, abs_mul,
          abs_mul, hbe, abs_pow]
        norm_num
      have hab0 : 1 ≤ |(a - b) * (a + b)| := by
        have : (a - b) * (a + b) ≠ 0 := by
          intro h0; apply hw; rw [hb]; linear_combination 3 * b * h0
        exact Int.one_le_abs this
      have hY := sq_add_three_sq_ge (u := 3 * w) hv
      have hX : |e| ^ 3 ≤ |e| ^ 3 * |(a - b) * (a + b)| := by
        nlinarith [mul_le_mul_of_nonneg_left hab0 he0.le]
      rw [hz3, abs_mul, hw', abs_of_pos (by norm_num : (0 : ℤ) < 3)]
      have hX0 : 0 ≤ |e| ^ 3 * |(a - b) * (a + b)| := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hY hX0]
  · -- `3 ∤ u`
    have hu3 : IsCoprime u 3 := isCoprime_of_not_three_dvd h3
    have hc1 : IsCoprime u (3 * v) := hu3.mul_right huv
    have hcop : IsCoprime u (u ^ 2 + 3 * v ^ 2) := by
      rw [show u ^ 2 + 3 * v ^ 2 = 3 * v ^ 2 + u * u by ring]
      exact (hu3.mul_right (huv.pow_right (n := 2))).add_mul_left_right u
    obtain ⟨r, hr⟩ := Int.eq_pow_of_mul_eq_pow_odd_left hcop (by decide) h
    obtain ⟨s, hs⟩ := Int.eq_pow_of_mul_eq_pow_odd_right hcop (by decide) h
    obtain ⟨a, b, ha, hb⟩ := Eis.euler_cube hc1 hs
    have hvw : IsCoprime (a ^ 3 - 9 * a * b ^ 2) (3 * a ^ 2 * b - 3 * b ^ 3) := by
      rw [← ha, ← hb]; exact huv
    obtain ⟨hab, -, hodd⟩ := euler_pair hvw
    have h3a : ¬ (3 : ℤ) ∣ a := by
      intro hd; apply h3; rw [ha]
      exact dvd_sub (dvd_pow hd (by norm_num)) (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd 9) _)
    have ha3b : IsCoprime a (3 * b) := (isCoprime_of_not_three_dvd h3a).mul_right hab
    obtain ⟨h1, h2, -, -⟩ := isCoprime_add_sub ha3b
    have hprod : a * ((a - 3 * b) * (a + 3 * b)) = r ^ 3 := by rw [← hr, ha]; ring
    obtain ⟨e, f, g, hae, hf, hg⟩ :=
      cubes_of_mul h1 h2 (isCoprime_sub_add ha3b hodd) hprod
    have hb0 : b ≠ 0 := by rintro rfl; apply hv; rw [hb]; ring
    have ha0 : a ≠ 0 := by rintro rfl; apply hu; rw [ha]; ring
    refine ⟨f, g, e, ?_, ?_, ?_, ?_, ?_⟩
    · have := isCoprime_sub_add ha3b hodd
      rw [hf, hg] at this
      exact (IsCoprime.pow_iff (by norm_num) (by norm_num)).mp this
    · rw [← hf, ← hg, ← hae]; ring
    · intro hfg
      apply hb0
      have : a - 3 * b = a + 3 * b := by rw [hf, hg, hfg]
      linarith
    · intro hfg
      apply ha0
      have : a + 3 * b = -(a - 3 * b) := by rw [hf, hg, show g = -f by linarith]; ring
      linarith
    · apply natAbs_lt_of_cube
      have he0 : 0 < |e| ^ 3 := by
        have : e ≠ 0 := by rintro rfl; apply ha0; rw [hae]; ring
        positivity
      have hu' : |u| = |e| ^ 3 * |(a - 3 * b) * (a + 3 * b)| := by
        rw [ha, show a ^ 3 - 9 * a * b ^ 2 = a * ((a - 3 * b) * (a + 3 * b)) by ring, abs_mul,
          hae, abs_pow]
      have hab0 : 1 ≤ |(a - 3 * b) * (a + 3 * b)| := by
        have : (a - 3 * b) * (a + 3 * b) ≠ 0 := by
          intro h0; apply hu; rw [ha]; linear_combination a * h0
        exact Int.one_le_abs this
      have h3le := sq_add_three_sq_ge (u := u) hv
      rw [hz3, hu']
      nlinarith [mul_le_mul_of_nonneg_left hab0 he0.le,
        mul_le_mul_of_nonneg_left h3le (mul_nonneg he0.le (abs_nonneg ((a - 3 * b) * (a + 3 * b))))]

/-- The coprime case, by strong induction on `|z|`. -/
lemma two_cubes_coprime : ∀ (N : ℕ) (x y z : ℤ), z.natAbs = N → IsCoprime x y →
    x ^ 3 + y ^ 3 = 2 * z ^ 3 → x = y ∨ x + y = 0 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro x y z hN hxy h
  by_contra hne
  push Not at hne
  obtain ⟨hne1, hne2⟩ := hne
  -- `x` and `y` are odd
  have hev : Even (x ^ 3 + y ^ 3) := ⟨z ^ 3, by rw [h]; ring⟩
  rw [Int.even_add, Int.even_pow, Int.even_pow] at hev
  have hxo : Odd x := by
    rcases Int.even_or_odd x with hx | hx
    · exfalso
      have hy : Even y := (hev.mp ⟨hx, by norm_num⟩).1
      exact not_isCoprime_of_two_dvd (even_iff_two_dvd.mp hx) (even_iff_two_dvd.mp hy) hxy
    · exact hx
  have hyo : Odd y := by
    rcases Int.even_or_odd y with hy | hy
    · exfalso
      have hx : Even x := (hev.mpr ⟨hy, by norm_num⟩).1
      exact Int.not_even_iff_odd.mpr hxo hx
    · exact hy
  obtain ⟨u, hu⟩ := hxo.add_odd hyo
  obtain ⟨v, hv⟩ := hxo.sub_odd hyo
  have hx : x = u + v := by linarith
  have hy : y = u - v := by linarith
  subst hx hy
  have hu0 : u ≠ 0 := by rintro rfl; apply hne2; ring
  have hv0 : v ≠ 0 := by rintro rfl; apply hne1; ring
  have huv : IsCoprime u v := by
    obtain ⟨m, n, hmn⟩ := hxy
    exact ⟨m + n, m - n, by linear_combination hmn⟩
  have hz : u * (u ^ 2 + 3 * v ^ 2) = z ^ 3 := by
    have : 2 * (u * (u ^ 2 + 3 * v ^ 2)) = 2 * z ^ 3 := by rw [← h]; ring
    exact mul_left_cancel₀ two_ne_zero this
  obtain ⟨f, g, e, hfg, he, hne3, hne4, hlt⟩ := descent_step huv hu0 hv0 hz
  rcases ih e.natAbs (hN ▸ hlt) f g e rfl hfg he with h1 | h1
  · exact hne3 h1
  · exact hne4 h1

/-- If `G ^ 3` divides `2 z ^ 3`, then `G` divides `z`. -/
lemma dvd_of_cube_dvd_two_mul {G z : ℤ} (hG : G ≠ 0) (h : G ^ 3 ∣ 2 * z ^ 3) : G ∣ z := by
  have hpos : 0 < Int.gcd G z := Int.gcd_pos_of_ne_zero_left z hG
  obtain ⟨d, G1, z1, hd, hcop, rfl, rfl⟩ := Int.exists_gcd_one' hpos
  have hd0 : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  have h1 : G1 ^ 3 ∣ 2 * z1 ^ 3 := by
    obtain ⟨c, hc⟩ := h
    refine ⟨c, ?_⟩
    have : (d : ℤ) ^ 3 * (2 * z1 ^ 3) = (d : ℤ) ^ 3 * (G1 ^ 3 * c) := by
      linear_combination hc
    exact mul_left_cancel₀ (pow_ne_zero 3 hd0) this
  have hc' : IsCoprime (G1 ^ 3) (z1 ^ 3) :=
    (IsCoprime.pow_iff (by norm_num) (by norm_num)).mpr (Int.isCoprime_iff_gcd_eq_one.mpr hcop)
  have h2 : G1 ^ 3 ∣ 2 := hc'.dvd_of_dvd_mul_right h1
  have hG1 : G1 ≠ 0 := by rintro rfl; simp at hG
  have hle : |G1| ^ 3 ≤ 2 := by
    rw [← abs_pow]
    exact Int.le_of_dvd (by norm_num) ((abs_dvd _ _).mpr h2)
  have h1le : |G1| ≤ 1 := by
    by_contra hc
    push Not at hc
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℤ) ≤ 2) (by omega : (2 : ℤ) ≤ |G1|) 3]
  have hunit : IsUnit G1 := by
    rcases abs_cases G1 with ⟨h, -⟩ | ⟨h, -⟩
    · have : 1 ≤ |G1| := Int.one_le_abs hG1
      exact Int.isUnit_iff.mpr (Or.inl (by omega))
    · have : 1 ≤ |G1| := Int.one_le_abs hG1
      exact Int.isUnit_iff.mpr (Or.inr (by omega))
  exact mul_dvd_mul (hunit.dvd) (dvd_refl _)

/-- Every integer solution of `x ^ 3 + y ^ 3 = 2 z ^ 3` has `x = y` or `x + y = 0`. -/
theorem two_cubes {x y z : ℤ} (h : x ^ 3 + y ^ 3 = 2 * z ^ 3) : x = y ∨ x + y = 0 := by
  by_cases h0 : x = 0 ∧ y = 0
  · left; rw [h0.1, h0.2]
  have hpos : 0 < Int.gcd x y := Int.gcd_pos_iff.mpr (by tauto)
  obtain ⟨g, x', y', hg, hcop, rfl, rfl⟩ := Int.exists_gcd_one' hpos
  have hg0 : (g : ℤ) ≠ 0 := by exact_mod_cast hg.ne'
  have hdiv : (g : ℤ) ^ 3 ∣ 2 * z ^ 3 := ⟨x' ^ 3 + y' ^ 3, by rw [← h]; ring⟩
  obtain ⟨z', rfl⟩ := dvd_of_cube_dvd_two_mul hg0 hdiv
  have h' : x' ^ 3 + y' ^ 3 = 2 * z' ^ 3 := by
    have : (g : ℤ) ^ 3 * (x' ^ 3 + y' ^ 3) = (g : ℤ) ^ 3 * (2 * z' ^ 3) := by
      linear_combination h
    exact mul_left_cancel₀ (pow_ne_zero 3 hg0) this
  rcases two_cubes_coprime _ x' y' z' rfl (Int.isCoprime_iff_gcd_eq_one.mpr hcop) h' with
    h1 | h1
  · left; rw [h1]
  · right; linear_combination (g : ℤ) * h1

end TuringTask
