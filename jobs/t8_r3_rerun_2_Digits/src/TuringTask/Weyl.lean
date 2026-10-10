import Mathlib

namespace TuringTask.Weyl

open scoped BigOperators
open Filter

/-- The standard additive character of `ℝ / ℤ`, written on representatives. -/
noncomputable def phase (x : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * x * Complex.I)

@[simp] theorem phase_zero : phase 0 = 1 := by
  simp [phase]

@[simp] theorem phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  rw [phase, phase, phase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

@[simp] theorem phase_neg (x : ℝ) : phase (-x) = (phase x)⁻¹ := by
  rw [phase, phase]
  push_cast
  rw [show (2 : ℂ) * Real.pi * (-x) * Complex.I = -(2 * Real.pi * x * Complex.I) by ring]
  exact Complex.exp_neg _

@[simp] theorem phase_sub (x y : ℝ) : phase (x - y) = phase x / phase y := by
  rw [sub_eq_add_neg, phase_add, phase_neg, div_eq_mul_inv]

@[simp] theorem norm_phase (x : ℝ) : ‖phase x‖ = 1 := by
  rw [phase, Complex.norm_exp]
  simp

@[simp] theorem conj_phase (x : ℝ) : starRingEnd ℂ (phase x) = phase (-x) := by
  rw [phase, phase, ← Complex.exp_conj]
  congr 1
  have htwo : starRingEnd ℂ (2 : ℂ) = 2 := map_ofNat (starRingEnd ℂ) 2
  simp only [map_mul, htwo, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

@[simp] theorem phase_intCast (z : ℤ) : phase (z : ℝ) = 1 := by
  rw [phase]
  convert Complex.exp_int_mul_two_pi_mul_I z using 1 <;> push_cast <;> ring

theorem phase_ne_one_of_irrational {x : ℝ} (hx : Irrational x) : phase x ≠ 1 := by
  intro he
  rw [phase, Complex.exp_eq_one_iff] at he
  obtain ⟨z, hz⟩ := he
  have him := congrArg Complex.im hz
  norm_num at him
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hxz : x = (z : ℝ) := by
    apply (mul_left_cancel₀ (show (2 * Real.pi : ℝ) ≠ 0 by positivity))
    convert him using 1 <;> ring
  exact hx (hxz.symm ▸ ⟨(z : ℚ), by norm_num⟩)

/-- A geometric progression with a unit-modulus irrational ratio has zero Cesàro
mean. This is the degree-one base case of Weyl's argument. -/
theorem tendsto_geometric_average (q : ℂ) (hq : q ≠ 1) (hnorm : ‖q‖ = 1) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, q ^ n) / (N : ℂ))
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun N => show ‖(∑ n ∈ Finset.range N, q ^ n) / (N : ℂ)‖ ≤
      (2 / ‖q - 1‖) * (1 / (N : ℝ)) by
      rw [geom_sum_eq hq, norm_div, norm_div, norm_natCast]
      have hden : 0 < ‖q - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hq)
      have hnum : ‖q ^ N - 1‖ ≤ 2 := by
        calc
          ‖q ^ N - 1‖ ≤ ‖q ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ = 2 := by rw [norm_pow, hnorm]; norm_num
      calc
        ‖q ^ N - 1‖ / ‖q - 1‖ / (N : ℝ) ≤
            (2 / ‖q - 1‖) / (N : ℝ) :=
          div_le_div_of_nonneg_right
            (div_le_div_of_nonneg_right hnum (norm_nonneg _)) (Nat.cast_nonneg _)
        _ = (2 / ‖q - 1‖) * (1 / (N : ℝ)) := by ring)
  have hzero : Tendsto (fun N : ℕ => (1 / (N : ℝ))) atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  simpa using hzero.const_mul (2 / ‖q - 1‖)

/-- The exponential sums for a nonzero integral multiple of an irrational
linear phase tend to zero. -/
theorem tendsto_phase_linear (x : ℝ) (hx : Irrational x) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, phase ((n : ℝ) * x)) / (N : ℂ))
      atTop (nhds 0) := by
  have hp : phase x ≠ 1 := phase_ne_one_of_irrational hx
  have hgeom := tendsto_geometric_average (phase x) hp (norm_phase x)
  have hpow : ∀ n : ℕ, phase ((n : ℝ) * x) = phase x ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Nat.cast_succ, add_mul, phase_add, ih, pow_succ]
        norm_num
  simpa only [hpow] using hgeom

/-- A convenient base case including a constant term and a nonzero Fourier
frequency. -/
theorem tendsto_phase_affine (a b : ℝ) (ha : Irrational a) (k : ℤ) (hk : k ≠ 0) :
    Tendsto
      (fun N : ℕ =>
        (∑ n ∈ Finset.range N, phase ((k : ℝ) * (a * n + b))) / (N : ℂ))
      atTop (nhds 0) := by
  have hka : Irrational ((k : ℝ) * a) := ha.intCast_mul hk
  have hlin := tendsto_phase_linear ((k : ℝ) * a) hka
  have heq : (fun N : ℕ =>
      (∑ n ∈ Finset.range N, phase ((k : ℝ) * (a * n + b))) / (N : ℂ)) =
      (fun N : ℕ => phase ((k : ℝ) * b) *
        ((∑ n ∈ Finset.range N, phase ((n : ℝ) * ((k : ℝ) * a))) / (N : ℂ))) := by
    funext N
    have hterm : ∀ n : ℕ, phase ((k : ℝ) * (a * n + b)) =
        phase ((k : ℝ) * b) * phase ((n : ℝ) * ((k : ℝ) * a)) := by
      intro n
      rw [← phase_add]
      congr 1
      push_cast
      ring
    simp_rw [hterm]
    rw [← Finset.mul_sum]
    ring
  rw [heq]
  simpa using hlin.const_mul (phase ((k : ℝ) * b))

/-- The forward difference used in the induction step of Weyl's proof. Taylor
translation is preferable to coefficient-level substitution because Mathlib
already tracks its degree and leading coefficient. -/
noncomputable def forwardDiff (P : Polynomial ℝ) (h : ℝ) : Polynomial ℝ :=
  (Polynomial.taylor h) P - P

@[simp] theorem eval_forwardDiff (P : Polynomial ℝ) (h x : ℝ) :
    Polynomial.eval x (forwardDiff P h) =
      Polynomial.eval (x + h) P - Polynomial.eval x P := by
  simp [forwardDiff, Polynomial.taylor_eval]

theorem degree_forwardDiff_lt (P : Polynomial ℝ) (h : ℝ) (hP : P ≠ 0) :
    (forwardDiff P h).degree < P.degree := by
  have ht : (Polynomial.taylor h) P ≠ 0 := by
    rw [Polynomial.taylor_apply]
    exact Polynomial.comp_X_add_C_ne_zero_iff.mpr hP
  have hd := Polynomial.degree_sub_lt (Polynomial.degree_taylor P h) ht
    (Polynomial.leadingCoeff_taylor h P)
  simpa [forwardDiff, Polynomial.degree_taylor] using hd

private theorem coeff_forwardDiff_eq_zero_of_natDegree_le (Q : Polynomial ℝ)
    (h : ℝ) (m : ℕ) (hQ : Q.natDegree ≤ m) :
    (forwardDiff Q h).coeff m = 0 := by
  rw [forwardDiff, Polynomial.coeff_sub]
  by_cases hzero : Q = 0
  · simp [hzero]
  by_cases hlt : Q.natDegree < m
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by
      simpa only [Polynomial.natDegree_taylor] using hlt)]
    exact sub_self 0
  · have heq : Q.natDegree = m := Nat.le_antisymm hQ (Nat.le_of_not_gt hlt)
    subst m
    rw [Polynomial.coeff_taylor_natDegree, Polynomial.coeff_natDegree]
    exact sub_self _

theorem leadingCoeff_forwardDiff (P : Polynomial ℝ) (h : ℝ)
    (hdeg : 0 < P.natDegree) (hlc : P.leadingCoeff ≠ 0) (hh : h ≠ 0) :
    (forwardDiff P h).natDegree = P.natDegree - 1 ∧
      (forwardDiff P h).leadingCoeff =
        (P.natDegree : ℝ) * h * P.leadingCoeff := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hdeg)
  rw [hd]
  have hP : P ≠ 0 := fun hp => hlc (by simp [hp])
  let E := P.eraseLead
  let L := Polynomial.C P.leadingCoeff * Polynomial.X ^ (d + 1)
  have hdecomp : E + L = P := by
    simpa [E, L, hd] using Polynomial.eraseLead_add_C_mul_X_pow P
  have hEdeg : E.natDegree ≤ d := by
    have hele := Polynomial.eraseLead_natDegree_le P
    simpa [E, hd] using hele
  have hEcoeff : (forwardDiff E h).coeff d = 0 :=
    coeff_forwardDiff_eq_zero_of_natDegree_le E h d hEdeg
  have hLcoeff : (forwardDiff L h).coeff d =
      ((d + 1 : ℕ) : ℝ) * h * P.leadingCoeff := by
    rw [forwardDiff, Polynomial.coeff_sub]
    simp [L, Polynomial.taylor_X_pow, Polynomial.coeff_X_add_C_pow,
      Nat.choose_succ_self_right]
    ring
  have hadd : forwardDiff P h = forwardDiff E h + forwardDiff L h := by
    rw [← hdecomp]
    simp [forwardDiff]
    ring
  have hcoeff : (forwardDiff P h).coeff d =
      ((d + 1 : ℕ) : ℝ) * h * P.leadingCoeff := by
    rw [hadd, Polynomial.coeff_add, hEcoeff, hLcoeff, zero_add]
  have hcoeff_ne : (forwardDiff P h).coeff d ≠ 0 := by
    rw [hcoeff]
    positivity
  have hlower : d ≤ (forwardDiff P h).natDegree :=
    Polynomial.le_natDegree_of_ne_zero hcoeff_ne
  have hdegree_lt := degree_forwardDiff_lt P h hP
  have hupper : (forwardDiff P h).natDegree < d + 1 := by
    have hdiff : forwardDiff P h ≠ 0 := fun hp => hcoeff_ne (by simp [hp])
    rw [Polynomial.natDegree_lt_iff_degree_lt hdiff]
    rw [Polynomial.degree_eq_natDegree hP, hd] at hdegree_lt
    simpa using hdegree_lt
  have hnat : (forwardDiff P h).natDegree = d := Nat.le_antisymm (Nat.lt_succ_iff.mp hupper) hlower
  constructor
  · simpa [hd] using hnat
  · rw [← Polynomial.coeff_natDegree, hnat, hcoeff]

/-- Correlations of polynomial phases are phases of forward differences. This
is the algebraic bridge required by van der Corput's lemma. -/
theorem phase_correlation (P : Polynomial ℝ) (h : ℕ) (n : ℕ) :
    starRingEnd ℂ (phase (Polynomial.eval (n : ℝ) P)) *
        phase (Polynomial.eval (n + h : ℕ) P) =
      phase (Polynomial.eval (n : ℝ) (forwardDiff P h)) := by
  rw [conj_phase, ← phase_add, eval_forwardDiff]
  congr 1
  push_cast
  ring

private theorem norm_sum_sq_le_card_mul_sum_norm_sq {ι : Type*} (s : Finset ι)
    (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
  have hre_sum : (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re := by
    rw [← Complex.reCLM_apply, map_sum]
    simp only [Complex.reCLM_apply]
  have him_sum : (∑ i ∈ s, f i).im = ∑ i ∈ s, (f i).im := by
    rw [← Complex.imCLM_apply, map_sum]
    simp only [Complex.imCLM_apply]
  have hre := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => (f i).re) (fun _ => (1 : ℝ))
  have him := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => (f i).im) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hre him
  rw [Complex.sq_norm, Complex.normSq_apply]
  rw [hre_sum, him_sum]
  simp only [Complex.sq_norm, Complex.normSq_apply]
  calc
    (∑ i ∈ s, (f i).re) * (∑ i ∈ s, (f i).re) +
          (∑ i ∈ s, (f i).im) * (∑ i ∈ s, (f i).im) =
        (∑ i ∈ s, (f i).re) ^ 2 + (∑ i ∈ s, (f i).im) ^ 2 := by ring
    _ ≤ (s.card : ℝ) * (∑ i ∈ s, (f i).re ^ 2) +
          (s.card : ℝ) * (∑ i ∈ s, (f i).im ^ 2) := by
      simpa only [mul_comm] using add_le_add hre him
    _ = (s.card : ℝ) * ∑ i ∈ s, ((f i).re * (f i).re + (f i).im * (f i).im) := by
      simp_rw [pow_two]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

noncomputable def cesaro (u : ℕ → ℂ) (N : ℕ) : ℂ :=
  (∑ n ∈ Finset.range N, u n) / (N : ℂ)

private noncomputable def blockCesaro (u : ℕ → ℂ) (H N : ℕ) : ℂ :=
  (∑ n ∈ Finset.range N, ∑ h ∈ Finset.range H, u (n + h)) /
    ((H : ℂ) * (N : ℂ))

noncomputable def correlationCesaro (u : ℕ → ℂ) (h k N : ℕ) : ℂ :=
  (∑ n ∈ Finset.range N, starRingEnd ℂ (u (n + h)) * u (n + k)) / (N : ℂ)

private theorem norm_sq_eq_re_conj_mul (z : ℂ) :
    ‖z‖ ^ 2 = (starRingEnd ℂ z * z).re := by
  rw [Complex.sq_norm]
  have h := congrArg Complex.re (Complex.normSq_eq_conj_mul_self (z := z))
  simpa using h

private theorem sum_norm_inner_sq_eq (u : ℕ → ℂ) (H N : ℕ) :
    (∑ n ∈ Finset.range N, ‖∑ h ∈ Finset.range H, u (n + h)‖ ^ 2) =
      ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H,
        (∑ n ∈ Finset.range N,
          starRingEnd ℂ (u (n + h)) * u (n + k)).re := by
  simp_rw [norm_sq_eq_re_conj_mul]
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
  have hre (f : ℕ → ℂ) (s : Finset ℕ) :
      (∑ i ∈ s, f i).re = ∑ i ∈ s, (f i).re := by
    rw [← Complex.reCLM_apply, map_sum]
    simp only [Complex.reCLM_apply]
  simp_rw [hre]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

private noncomputable def vdcBound (u : ℕ → ℂ) (H N : ℕ) : ℝ :=
  ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H,
    if h = k then 1 else ‖correlationCesaro u h k N‖

private theorem sum_norm_inner_sq_le (u : ℕ → ℂ) (H N : ℕ)
    (hN : 0 < N) (hu : ∀ n, ‖u n‖ ≤ 1) :
    (∑ n ∈ Finset.range N, ‖∑ h ∈ Finset.range H, u (n + h)‖ ^ 2) ≤
      (N : ℝ) * vdcBound u H N := by
  rw [sum_norm_inner_sq_eq]
  rw [vdcBound, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro h hh
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  by_cases hhk : h = k
  · subst k
    simp only [if_pos]
    have hterm : ∀ n : ℕ,
        (starRingEnd ℂ (u (n + h)) * u (n + h)).re = ‖u (n + h)‖ ^ 2 := by
      intro n
      exact (norm_sq_eq_re_conj_mul (u (n + h))).symm
    rw [← Complex.reCLM_apply, map_sum]
    simp only [Complex.reCLM_apply]
    simp_rw [hterm]
    calc
      ∑ n ∈ Finset.range N, ‖u (n + h)‖ ^ 2 ≤
          ∑ _n ∈ Finset.range N, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        nlinarith [norm_nonneg (u (n + h)), sq_nonneg (1 - ‖u (n + h)‖),
          hu (n + h)]
      _ = (N : ℝ) := by simp
      _ = (N : ℝ) * 1 := by ring
  · simp only [if_neg hhk]
    let S : ℂ := ∑ n ∈ Finset.range N,
      starRingEnd ℂ (u (n + h)) * u (n + k)
    calc
      S.re ≤ ‖S‖ := Complex.re_le_norm S
      _ = (N : ℝ) * ‖correlationCesaro u h k N‖ := by
        rw [correlationCesaro, norm_div, norm_natCast]
        have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
        simp only [S]
        field_simp
      _ = (N : ℝ) * ‖correlationCesaro u h k N‖ := rfl

private theorem norm_blockCesaro_sq_le (u : ℕ → ℂ) (H N : ℕ)
    (hH : 0 < H) (hN : 0 < N) (hu : ∀ n, ‖u n‖ ≤ 1) :
    ‖blockCesaro u H N‖ ^ 2 ≤ vdcBound u H N / (H : ℝ) ^ 2 := by
  let S : ℂ := ∑ n ∈ Finset.range N, ∑ h ∈ Finset.range H, u (n + h)
  have hcs : ‖S‖ ^ 2 ≤ (N : ℝ) *
      ∑ n ∈ Finset.range N, ‖∑ h ∈ Finset.range H, u (n + h)‖ ^ 2 := by
    simpa only [S, Finset.card_range, Nat.cast_id] using
      norm_sum_sq_le_card_mul_sum_norm_sq (Finset.range N)
        (fun n => ∑ h ∈ Finset.range H, u (n + h))
  have hinner := sum_norm_inner_sq_le u H N hN hu
  have hS : ‖S‖ ^ 2 ≤ (N : ℝ) ^ 2 * vdcBound u H N := by
    calc
      ‖S‖ ^ 2 ≤ (N : ℝ) *
          ∑ n ∈ Finset.range N, ‖∑ h ∈ Finset.range H, u (n + h)‖ ^ 2 := hcs
      _ ≤ (N : ℝ) * ((N : ℝ) * vdcBound u H N) :=
        mul_le_mul_of_nonneg_left hinner (Nat.cast_nonneg N)
      _ = (N : ℝ) ^ 2 * vdcBound u H N := by ring
  have hHr : (0 : ℝ) < H := Nat.cast_pos.mpr hH
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  rw [blockCesaro, norm_div, norm_mul, norm_natCast, norm_natCast, div_pow]
  change (‖S‖ ^ 2 / ((H : ℝ) * (N : ℝ)) ^ 2) ≤
    vdcBound u H N / (H : ℝ) ^ 2
  apply (div_le_div_iff₀ (sq_pos_of_pos (mul_pos hHr hNr)) (sq_pos_of_pos hHr)).2
  have hm := mul_le_mul_of_nonneg_right hS (sq_nonneg (H : ℝ))
  convert hm using 1 <;> ring

private theorem norm_shift_sum_sub_le (u : ℕ → ℂ) (h N : ℕ)
    (hu : ∀ n, ‖u n‖ ≤ 1) :
    ‖(∑ n ∈ Finset.range N, u (n + h)) - ∑ n ∈ Finset.range N, u n‖ ≤
      2 * h := by
  have hleft := Finset.sum_range_add u h N
  have hright := Finset.sum_range_add u N h
  have hleft' : (∑ x ∈ Finset.range (N + h), u x) =
      (∑ x ∈ Finset.range h, u x) + ∑ x ∈ Finset.range N, u (x + h) := by
    simpa only [Nat.add_comm] using hleft
  have hshift : (∑ x ∈ Finset.range N, u (x + h)) =
      (∑ x ∈ Finset.range (N + h), u x) - ∑ x ∈ Finset.range h, u x := by
    rw [eq_sub_iff_add_eq]
    simpa only [add_comm] using hleft'.symm
  have hid : (∑ n ∈ Finset.range N, u (n + h)) - ∑ n ∈ Finset.range N, u n =
      (∑ j ∈ Finset.range h, u (N + j)) - ∑ j ∈ Finset.range h, u j := by
    rw [hshift, hright]
    ring
  rw [hid]
  calc
    ‖(∑ j ∈ Finset.range h, u (N + j)) - ∑ j ∈ Finset.range h, u j‖ ≤
        ‖∑ j ∈ Finset.range h, u (N + j)‖ + ‖∑ j ∈ Finset.range h, u j‖ :=
      norm_sub_le _ _
    _ ≤ (∑ _j ∈ Finset.range h, (1 : ℝ)) +
        ∑ _j ∈ Finset.range h, (1 : ℝ) := by
      gcongr
      · calc
          ‖∑ j ∈ Finset.range h, u (N + j)‖ ≤
              ∑ j ∈ Finset.range h, ‖u (N + j)‖ := norm_sum_le _ _
          _ ≤ ∑ _j ∈ Finset.range h, (1 : ℝ) := by
            exact Finset.sum_le_sum fun j hj => hu (N + j)
      · calc
          ‖∑ j ∈ Finset.range h, u j‖ ≤
              ∑ j ∈ Finset.range h, ‖u j‖ := norm_sum_le _ _
          _ ≤ ∑ _j ∈ Finset.range h, (1 : ℝ) := by
            exact Finset.sum_le_sum fun j hj => hu j
    _ = 2 * h := by simp; ring

private theorem tendsto_cesaro_shift_sub (u : ℕ → ℂ) (h : ℕ)
    (hu : ∀ n, ‖u n‖ ≤ 1) :
    Tendsto (fun N => cesaro (fun n => u (n + h)) N - cesaro u N)
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun N => show ‖cesaro (fun n => u (n + h)) N - cesaro u N‖ ≤
      (2 * h : ℝ) * (1 / (N : ℝ)) by
      rw [cesaro, cesaro, ← sub_div, norm_div, norm_natCast]
      calc
        ‖(∑ n ∈ Finset.range N, u (n + h)) - ∑ n ∈ Finset.range N, u n‖ /
            (N : ℝ) ≤ (2 * h : ℝ) / (N : ℝ) :=
          div_le_div_of_nonneg_right (norm_shift_sum_sub_le u h N hu) (Nat.cast_nonneg N)
        _ = (2 * h : ℝ) * (1 / (N : ℝ)) := by ring)
  simpa using (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * h : ℝ)

private theorem tendsto_vdcBound (u : ℕ → ℂ) (H : ℕ)
    (hcorr : ∀ h k, h ≠ k →
      Tendsto (fun N => correlationCesaro u h k N) atTop (nhds 0)) :
    Tendsto (fun N => vdcBound u H N) atTop (nhds (H : ℝ)) := by
  have hterm (h k : ℕ) : Tendsto
      (fun N => if h = k then (1 : ℝ) else ‖correlationCesaro u h k N‖)
      atTop (nhds (if h = k then 1 else 0)) := by
    by_cases hhk : h = k
    · simpa [hhk] using tendsto_const_nhds (x := (1 : ℝ))
    · simpa [hhk] using (hcorr h k hhk).norm
  have hsum : Tendsto
      (fun N => ∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H,
        if h = k then (1 : ℝ) else ‖correlationCesaro u h k N‖)
      atTop
      (nhds (∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H,
        if h = k then (1 : ℝ) else 0)) := by
    apply tendsto_finset_sum
    intro h hh
    apply tendsto_finset_sum
    intro k hk
    exact hterm h k
  have hdiag : (∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H,
      if h = k then (1 : ℝ) else 0) = (H : ℝ) := by
    calc
      (∑ h ∈ Finset.range H, ∑ k ∈ Finset.range H,
          if h = k then (1 : ℝ) else 0) =
          ∑ _h ∈ Finset.range H, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro h hh
        simp [eq_comm, hh]
      _ = (H : ℝ) := by simp
  rw [← hdiag]
  exact hsum

private theorem tendsto_blockCesaro_sub (u : ℕ → ℂ) (H : ℕ) (hH : 0 < H)
    (hu : ∀ n, ‖u n‖ ≤ 1) :
    Tendsto (fun N => blockCesaro u H N - cesaro u N) atTop (nhds 0) := by
  have hrepr (N : ℕ) : blockCesaro u H N - cesaro u N =
      (1 / (H : ℂ)) * ∑ h ∈ Finset.range H,
        (cesaro (fun n => u (n + h)) N - cesaro u N) := by
    have hHc : (H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hH)
    rw [blockCesaro, cesaro]
    simp_rw [cesaro]
    rw [Finset.sum_comm]
    rw [Finset.sum_sub_distrib, ← Finset.sum_div]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    by_cases hN : N = 0
    · simp [hN]
    · have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
      field_simp [hHc, hNc]
  simp_rw [hrepr]
  have hsum : Tendsto
      (fun N => ∑ h ∈ Finset.range H,
        (cesaro (fun n => u (n + h)) N - cesaro u N)) atTop
      (nhds (∑ _h ∈ Finset.range H, (0 : ℂ))) := by
    apply tendsto_finset_sum
    intro h hh
    exact tendsto_cesaro_shift_sub u h hu
  simpa using hsum.const_mul (1 / (H : ℂ))

/-- A van der Corput lemma for bounded complex sequences. Using correlations
between every pair of fixed shifts makes the boundary bookkeeping explicit and
keeps the statement directly usable in the polynomial induction. -/
theorem vanDerCorput (u : ℕ → ℂ) (hu : ∀ n, ‖u n‖ ≤ 1)
    (hcorr : ∀ h k, h ≠ k →
      Tendsto (fun N => correlationCesaro u h k N) atTop (nhds 0)) :
    Tendsto (fun N => cesaro u N) atTop (nhds 0) := by
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  have hepssq : 0 < ε ^ 2 := sq_pos_of_pos hε
  obtain ⟨H, hHlarge⟩ := exists_nat_gt (8 / ε ^ 2)
  have hHr : (0 : ℝ) < H := by
    have : 0 < 8 / ε ^ 2 := div_pos (by norm_num) hepssq
    linarith
  have hH : 0 < H := Nat.cast_pos.mp hHr
  have hsmall : 2 / (H : ℝ) < (ε / 2) ^ 2 := by
    have hprod : 8 < (H : ℝ) * ε ^ 2 :=
      (div_lt_iff₀ hepssq).mp hHlarge
    apply (div_lt_iff₀ hHr).2
    nlinarith
  have hvdc := tendsto_vdcBound u H hcorr
  have hvdc_event : ∀ᶠ N in atTop, vdcBound u H N < 2 * H := by
    exact hvdc.eventually_lt_const (by norm_num; linarith)
  have hN_event : ∀ᶠ N : ℕ in atTop, 0 < N := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    omega
  have hblock_event : ∀ᶠ N in atTop, ‖blockCesaro u H N‖ < ε / 2 := by
    filter_upwards [hvdc_event, hN_event] with N hb hN
    have hbound := norm_blockCesaro_sq_le u H N hH hN hu
    have hquot : vdcBound u H N / (H : ℝ) ^ 2 < 2 / (H : ℝ) := by
      apply (div_lt_div_iff₀ (sq_pos_of_pos hHr) hHr).2
      have := mul_lt_mul_of_pos_right hb hHr
      convert this using 1 <;> ring
    have hsq : ‖blockCesaro u H N‖ ^ 2 < (ε / 2) ^ 2 :=
      lt_of_le_of_lt hbound (lt_trans hquot hsmall)
    exact (sq_lt_sq₀ (norm_nonneg _) (by positivity)).mp hsq
  have hdiff := tendsto_blockCesaro_sub u H hH hu
  have hdiff_event : ∀ᶠ N in atTop,
      ‖blockCesaro u H N - cesaro u N‖ < ε / 2 :=
    (NormedAddGroup.tendsto_nhds_zero.mp hdiff) (ε / 2) (by positivity)
  filter_upwards [hblock_event, hdiff_event] with N hb hd
  calc
    ‖cesaro u N‖ = ‖blockCesaro u H N - (blockCesaro u H N - cesaro u N)‖ := by
      congr 2
      ring
    _ ≤ ‖blockCesaro u H N‖ + ‖blockCesaro u H N - cesaro u N‖ := norm_sub_le _ _
    _ < ε := by linarith

/-- Weyl's exponential-sum theorem for real polynomials. The irrationality of
the leading coefficient is inherited by every nontrivial forward difference,
so `vanDerCorput` closes the strong induction on the degree. -/
theorem tendsto_phase_polynomial (P : Polynomial ℝ)
    (hP : Irrational P.leadingCoeff) (hdeg : 1 ≤ P.natDegree) :
    Tendsto
      (fun N : ℕ =>
        (∑ n ∈ Finset.range N, phase (Polynomial.eval (n : ℝ) P)) / (N : ℂ))
      atTop (nhds 0) := by
  have aux : ∀ d : ℕ, ∀ Q : Polynomial ℝ, Q.natDegree = d →
      Irrational Q.leadingCoeff → 1 ≤ d →
      Tendsto
        (fun N : ℕ =>
          (∑ n ∈ Finset.range N, phase (Polynomial.eval (n : ℝ) Q)) / (N : ℂ))
        atTop (nhds 0) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro Q hQdeg hQirr hdpos
      by_cases hd1 : d = 1
      · have hQone : Q.natDegree = 1 := hQdeg.trans hd1
        have hform := Polynomial.eq_X_add_C_of_natDegree_le_one
          (show Q.natDegree ≤ 1 by omega)
        have hlc : Q.coeff 1 = Q.leadingCoeff := by
          rw [← Polynomial.coeff_natDegree, hQone]
        have heval (n : ℕ) : Polynomial.eval (n : ℝ) Q =
            Q.leadingCoeff * (n : ℝ) + Q.coeff 0 := by
          calc
            Polynomial.eval (n : ℝ) Q = Q.coeff 1 * (n : ℝ) + Q.coeff 0 := by
              rw [hform]
              simp
            _ = Q.leadingCoeff * (n : ℝ) + Q.coeff 0 := by rw [hlc]
        have hbase := tendsto_phase_affine Q.leadingCoeff (Q.coeff 0) hQirr 1 (by norm_num)
        simpa only [Int.cast_one, one_mul, heval] using hbase
      · have hd2 : 2 ≤ d := by omega
        have hQlcne : Q.leadingCoeff ≠ 0 := by
          intro hz
          apply hQirr
          rw [hz]
          exact ⟨0, by simp⟩
        let u : ℕ → ℂ := fun n => phase (Polynomial.eval (n : ℝ) Q)
        have hu : ∀ n, ‖u n‖ ≤ 1 := by
          intro n
          simp [u]
        have hcorr : ∀ h k, h ≠ k →
            Tendsto (fun N => correlationCesaro u h k N) atTop (nhds 0) := by
          intro h k hhk
          rcases lt_or_gt_of_ne hhk with hlt | hgt
          · let r := k - h
            have hrpos : 0 < r := Nat.sub_pos_of_lt hlt
            let F := forwardDiff Q (r : ℝ)
            let R := (Polynomial.taylor (h : ℝ)) F
            have hlead := leadingCoeff_forwardDiff Q (r : ℝ)
              (by omega) hQlcne (by exact_mod_cast (Nat.ne_of_gt hrpos))
            have hRdeg : R.natDegree = d - 1 := by
              simpa [R, F, Polynomial.natDegree_taylor, hQdeg] using hlead.1
            have hFirr : Irrational F.leadingCoeff := by
              change Irrational (forwardDiff Q (r : ℝ)).leadingCoeff
              rw [hlead.2, hQdeg]
              have hrne : r ≠ 0 := Nat.ne_of_gt hrpos
              have hdne : d ≠ 0 := by omega
              convert (hQirr.natCast_mul hrne).natCast_mul hdne using 1 <;> ring
            have hRirr : Irrational R.leadingCoeff := by
              change Irrational ((Polynomial.taylor (h : ℝ)) F).leadingCoeff
              rw [Polynomial.leadingCoeff_taylor]
              exact hFirr
            have hrec := ih (d - 1) (by omega) R hRdeg hRirr (by omega)
            have hrcast : (r : ℝ) = (k : ℝ) - (h : ℝ) := by
              simp [r, Nat.cast_sub (Nat.le_of_lt hlt)]
            have heval (n : ℕ) :
                starRingEnd ℂ (u (n + h)) * u (n + k) =
                  phase (Polynomial.eval (n : ℝ) R) := by
              simp only [u]
              rw [conj_phase, ← phase_add]
              congr 1
              simp only [R]
              rw [Polynomial.taylor_eval]
              simp only [F]
              rw [eval_forwardDiff]
              push_cast
              rw [hrcast]
              ring
            simpa only [correlationCesaro, cesaro, heval] using hrec
          · let r := h - k
            have hrpos : 0 < r := Nat.sub_pos_of_lt hgt
            let F := forwardDiff Q (r : ℝ)
            let R := -((Polynomial.taylor (k : ℝ)) F)
            have hlead := leadingCoeff_forwardDiff Q (r : ℝ)
              (by omega) hQlcne (by exact_mod_cast (Nat.ne_of_gt hrpos))
            have hRdeg : R.natDegree = d - 1 := by
              simpa [R, F, Polynomial.natDegree_taylor, hQdeg] using hlead.1
            have hFirr : Irrational F.leadingCoeff := by
              change Irrational (forwardDiff Q (r : ℝ)).leadingCoeff
              rw [hlead.2, hQdeg]
              have hrne : r ≠ 0 := Nat.ne_of_gt hrpos
              have hdne : d ≠ 0 := by omega
              convert (hQirr.natCast_mul hrne).natCast_mul hdne using 1 <;> ring
            have hRirr : Irrational R.leadingCoeff := by
              change Irrational (-((Polynomial.taylor (k : ℝ)) F)).leadingCoeff
              rw [Polynomial.leadingCoeff_neg, Polynomial.leadingCoeff_taylor]
              exact hFirr.neg
            have hrec := ih (d - 1) (by omega) R hRdeg hRirr (by omega)
            have hrcast : (r : ℝ) = (h : ℝ) - (k : ℝ) := by
              simp [r, Nat.cast_sub (Nat.le_of_lt hgt)]
            have heval (n : ℕ) :
                starRingEnd ℂ (u (n + h)) * u (n + k) =
                  phase (Polynomial.eval (n : ℝ) R) := by
              simp only [u]
              rw [conj_phase, ← phase_add]
              congr 1
              simp only [R, Polynomial.eval_neg]
              rw [Polynomial.taylor_eval]
              simp only [F]
              rw [eval_forwardDiff]
              push_cast
              rw [hrcast]
              ring
            simpa only [correlationCesaro, cesaro, heval] using hrec
        have hvdc := vanDerCorput u hu hcorr
        simpa only [u, cesaro] using hvdc
  exact aux P.natDegree P rfl hP hdeg

/-- The Fourier-frequency form of `tendsto_phase_polynomial`: every nonzero
integer multiple of a polynomial with irrational leading coefficient has a
vanishing exponential mean. -/
theorem tendsto_phase_polynomial_int_mul (P : Polynomial ℝ)
    (hP : Irrational P.leadingCoeff) (hdeg : 1 ≤ P.natDegree)
    (k : ℤ) (hk : k ≠ 0) :
    Tendsto
      (fun N : ℕ =>
        (∑ n ∈ Finset.range N,
          phase ((k : ℝ) * Polynomial.eval (n : ℝ) P)) / (N : ℂ))
      atTop (nhds 0) := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  let Q := Polynomial.C (k : ℝ) * P
  have hQdeg : Q.natDegree = P.natDegree := by
    exact Polynomial.natDegree_C_mul hkR
  have hQirr : Irrational Q.leadingCoeff := by
    change Irrational (Polynomial.C (k : ℝ) * P).leadingCoeff
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
    exact hP.intCast_mul hk
  have hmain := tendsto_phase_polynomial Q hQirr (by simpa [hQdeg] using hdeg)
  have heval (n : ℕ) : Polynomial.eval (n : ℝ) Q =
      (k : ℝ) * Polynomial.eval (n : ℝ) P := by
    simp [Q]
  simpa only [heval] using hmain

end TuringTask.Weyl
