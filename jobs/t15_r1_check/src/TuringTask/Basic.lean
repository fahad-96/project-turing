import Mathlib

namespace TuringTask

open Complex Real



lemma exp_cast_eq (N : ℕ) [NeZero N] (j_val : ℕ) :
    (2 * ↑Real.pi * Complex.I * (j_val : ℂ) / (N : ℂ)) =
      ((2 * Real.pi * (j_val : ℝ) / (N : ℝ) : ℝ) : ℂ) * I := by
  have hN : (N : ℂ) ≠ 0 := by
    have : (N : ℂ) = ((N : ℝ) : ℂ) := by simp
    rw [this]
    exact_mod_cast NeZero.ne N
  push_cast
  ring

lemma normSq_one_sub_exp_mul_I (θ : ℝ) :
    normSq (1 - exp (θ * I)) = 4 * (Real.sin (θ / 2)) ^ 2 := by
  have he : exp (θ * I) = Complex.cos θ + Complex.sin θ * I := exp_mul_I θ
  rw [he]
  have hre : (1 - (Complex.cos θ + Complex.sin θ * I)).re = 1 - Real.cos θ := by
    simp [cos_ofReal_re, sin_ofReal_re]
  have him : (1 - (Complex.cos θ + Complex.sin θ * I)).im = - Real.sin θ := by
    simp [cos_ofReal_im, sin_ofReal_re]
  rw [normSq_apply, hre, him]
  have htrig : (1 - Real.cos θ) * (1 - Real.cos θ) + (- Real.sin θ) * (- Real.sin θ) = 2 - 2 * Real.cos θ := by
    have : (Real.sin θ)^2 + (Real.cos θ)^2 = 1 := Real.sin_sq_add_cos_sq θ
    nlinarith
  rw [htrig]
  have hhalf : 1 - Real.cos θ = 2 * (Real.sin (θ / 2)) ^ 2 := by
    have hc := Real.cos_two_mul (θ / 2)
    have h2' : 2 * (θ / 2) = θ := mul_div_cancel₀ θ two_ne_zero
    rw [h2'] at hc
    have h1 : Real.cos (θ / 2) ^ 2 + Real.sin (θ / 2) ^ 2 = 1 := Real.cos_sq_add_sin_sq (θ / 2)
    linarith
  linarith

lemma norm_one_sub_exp_ge (p : ℕ) (j_val : ℕ) (hj_pos : 0 < j_val) (hj_le : j_val ≤ (p - 1) / 2) (hp : 0 < p) :
    4 * (j_val : ℝ) / (p : ℝ) ≤ ‖1 - exp (((2 * Real.pi * (j_val : ℝ) / (p : ℝ) : ℝ) : ℂ) * I)‖ := by
  set θ := 2 * Real.pi * (j_val : ℝ) / (p : ℝ) with hθ_def
  have hθ_half : θ / 2 = Real.pi * (j_val : ℝ) / (p : ℝ) := by dsimp [θ]; ring
  have hp_pos : 0 < (p : ℝ) := Nat.cast_pos.mpr hp
  have hj_pos_r : 0 < (j_val : ℝ) := Nat.cast_pos.mpr hj_pos
  have h_half_nonneg : 0 ≤ θ / 2 := by
    rw [hθ_half]
    positivity
  have h2 : 2 * j_val ≤ p := by
    have := Nat.mul_le_mul_left 2 hj_le
    have hdiv := Nat.mul_div_le (p - 1) 2
    omega
  have h2r : 2 * (j_val : ℝ) ≤ (p : ℝ) := by exact_mod_cast h2
  have hdiv : (j_val : ℝ) / (p : ℝ) ≤ 1 / 2 := by
    rw [div_le_iff₀ hp_pos]; linarith
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  have h_half_le : θ / 2 ≤ Real.pi / 2 := by
    rw [hθ_half]
    calc Real.pi * (j_val : ℝ) / (p : ℝ)
      _ = Real.pi * ((j_val : ℝ) / (p : ℝ)) := by ring
      _ ≤ Real.pi * (1 / 2) := mul_le_mul_of_nonneg_left hdiv hpi
      _ = Real.pi / 2 := by ring
  have hsin := Real.mul_le_sin h_half_nonneg h_half_le
  have hcancel : 2 / Real.pi * (θ / 2) = 2 * (j_val : ℝ) / (p : ℝ) := by
    rw [hθ_half]
    have hpi_ne : Real.pi ≠ 0 := Real.pi_ne_zero
    have : 2 / Real.pi * (Real.pi * (j_val : ℝ) / (p : ℝ)) =
        (2 * (Real.pi / Real.pi)) * (j_val : ℝ) / (p : ℝ) := by ring
    rw [div_self hpi_ne] at this
    linarith
  rw [hcancel] at hsin
  have hsq : normSq (1 - exp (θ * I)) = 4 * (Real.sin (θ / 2)) ^ 2 := by
    have he : exp (θ * I) = Complex.cos θ + Complex.sin θ * I := exp_mul_I θ
    rw [he]
    have hre : (1 - (Complex.cos θ + Complex.sin θ * I)).re = 1 - Real.cos θ := by
      simp [cos_ofReal_re, sin_ofReal_re]
    have him : (1 - (Complex.cos θ + Complex.sin θ * I)).im = - Real.sin θ := by
      simp [cos_ofReal_im, sin_ofReal_re]
    rw [normSq_apply, hre, him]
    have htrig : (1 - Real.cos θ) * (1 - Real.cos θ) + (- Real.sin θ) * (- Real.sin θ) = 2 - 2 * Real.cos θ := by
      have : (Real.sin θ)^2 + (Real.cos θ)^2 = 1 := Real.sin_sq_add_cos_sq θ
      nlinarith
    rw [htrig]
    have hhalf : 1 - Real.cos θ = 2 * (Real.sin (θ / 2)) ^ 2 := by
      have hc := Real.cos_two_mul (θ / 2)
      have h2' : 2 * (θ / 2) = θ := mul_div_cancel₀ θ two_ne_zero
      rw [h2'] at hc
      have h1 : Real.cos (θ / 2) ^ 2 + Real.sin (θ / 2) ^ 2 = 1 := Real.cos_sq_add_sin_sq (θ / 2)
      linarith
    linarith
  rw [norm_def, hsq]
  have h_sqrt : Real.sqrt (4 * Real.sin (θ / 2) ^ 2) = 2 * Real.sin (θ / 2) := by
    have : 4 * Real.sin (θ / 2) ^ 2 = (2 * Real.sin (θ / 2)) ^ 2 := by ring
    have hsin_pos : 0 ≤ 2 * Real.sin (θ / 2) := by
      have : 0 ≤ 2 * (j_val : ℝ) / (p : ℝ) := by positivity
      linarith
    rw [this, Real.sqrt_sq hsin_pos]
  rw [h_sqrt]
  calc 4 * (j_val : ℝ) / (p : ℝ)
    _ = 2 * (2 * (j_val : ℝ) / (p : ℝ)) := by ring
    _ ≤ 2 * Real.sin (θ / 2) := by linarith

lemma log_diff_ge_two_mul (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    2 * t ≤ Real.log (1 + t) - Real.log (1 - t) := by
  by_cases ht_zero : t = 0
  · subst ht_zero; simp
  have ht_pos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht_zero)
  set g := fun x => Real.log (1 + x) - Real.log (1 - x) - 2 * x
  have hg0 : g 0 = 0 := by
    dsimp [g]; simp
  have h_deriv (x : ℝ) (hx0 : -1 < x) (hx1 : x < 1) :
      HasDerivAt g (2 * x ^ 2 / (1 - x ^ 2)) x := by
    have h1 : HasDerivAt (fun y => Real.log (1 + y)) (1 / (1 + x)) x := by
      have hd : HasDerivAt (fun y => 1 + y) 1 x := by simpa using (hasDerivAt_id x).const_add 1
      have hpos : 0 < 1 + x := by linarith
      have := HasDerivAt.log hd hpos.ne'
      simpa using this
    have h2 : HasDerivAt (fun y => Real.log (1 - y)) (-1 / (1 - x)) x := by
      have hd : HasDerivAt (fun y => 1 - y) (-1) x := by simpa using (hasDerivAt_id x).const_sub 1
      have hpos : 0 < 1 - x := by linarith
      have := HasDerivAt.log hd hpos.ne'
      simpa using this
    have h3 : HasDerivAt (fun y => 2 * y) 2 x := by simpa using (hasDerivAt_id x).const_mul 2
    have hdiff := (h1.sub h2).sub h3
    have hid : 1 / (1 + x) - -1 / (1 - x) - 2 = 2 * x ^ 2 / (1 - x ^ 2) := by
      have hne1 : 1 + x ≠ 0 := by linarith
      have hne2 : 1 - x ≠ 0 := by linarith
      have hne3 : 1 - x ^ 2 ≠ 0 := by nlinarith
      have hsq : 1 - x ^ 2 = (1 + x) * (1 - x) := by ring
      rw [hsq]
      field_simp
      ring
    rw [hid] at hdiff
    exact hdiff
  have h_mono : MonotoneOn g (Set.Icc 0 t) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 t)
    · apply ContinuousOn.sub
      · apply ContinuousOn.sub
        · apply ContinuousOn.log
          · fun_prop
          · intro x hx; linarith [hx.1]
        · apply ContinuousOn.log
          · fun_prop
          · intro x hx; linarith [hx.2]
      · fun_prop
    · intro x hx
      rw [interior_Icc] at hx
      have hx0 : -1 < x := by linarith [hx.1]
      have hx1 : x < 1 := by linarith [hx.2]
      exact (h_deriv x hx0 hx1).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx0 : -1 < x := by linarith [hx.1]
      have hx1 : x < 1 := by linarith [hx.2]
      rw [(h_deriv x hx0 hx1).deriv]
      have h_num : 0 ≤ 2 * x ^ 2 := by positivity
      have h_den : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
      exact div_nonneg h_num h_den.le
  have h_le := h_mono (Set.left_mem_Icc.mpr ht0) (Set.right_mem_Icc.mpr ht0) ht0
  rw [hg0] at h_le
  dsimp [g] at h_le
  linarith

lemma inv_le_log_sub_log (j : ℕ) (hj : 1 ≤ j) :
    1 / (j : ℝ) ≤ Real.log (2 * (j : ℝ) + 1) - Real.log (2 * (j : ℝ) - 1) := by
  have hj1 : 1 ≤ (j : ℝ) := by exact_mod_cast hj
  set t := 1 / (2 * (j : ℝ)) with ht_def
  have hj_pos : 0 < (j : ℝ) := by linarith
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t < 1 := by
    dsimp [t]
    have : 1 < 2 * (j : ℝ) := by linarith
    exact (div_lt_one (by positivity)).mpr this
  have hdiff := log_diff_ge_two_mul t ht0 ht1
  have h2t : 2 * t = 1 / (j : ℝ) := by
    dsimp [t]; ring
  have hj2 : 2 * (j : ℝ) ≠ 0 := by linarith
  have hlog1 : Real.log (1 + t) = Real.log (2 * (j : ℝ) + 1) - Real.log (2 * (j : ℝ)) := by
    have hplus : 1 + t = (2 * (j : ℝ) + 1) / (2 * (j : ℝ)) := by
      dsimp [t]
      rw [add_div, div_self hj2]
    have h_num_ne : 2 * (j : ℝ) + 1 ≠ 0 := by linarith
    rw [hplus, Real.log_div h_num_ne hj2]
  have hlog2 : Real.log (1 - t) = Real.log (2 * (j : ℝ) - 1) - Real.log (2 * (j : ℝ)) := by
    have hminus : 1 - t = (2 * (j : ℝ) - 1) / (2 * (j : ℝ)) := by
      dsimp [t]
      rw [sub_div, div_self hj2]
    have h_num_ne : 2 * (j : ℝ) - 1 ≠ 0 := by linarith
    rw [hminus, Real.log_div h_num_ne hj2]
  rw [h2t] at hdiff
  rw [hlog1, hlog2] at hdiff
  linarith

lemma sum_log_telescoping (m : ℕ) :
    ∑ j ∈ Finset.Icc 1 m, (Real.log (2 * (j : ℝ) + 1) - Real.log (2 * (j : ℝ) - 1)) =
      Real.log (2 * (m : ℝ) + 1) := by
  induction' m with m ih
  · simp
  · rw [Finset.sum_Icc_succ_top (by omega)]
    rw [ih]
    push_cast
    have h1 : 2 * ((m : ℝ) + 1) - 1 = 2 * (m : ℝ) + 1 := by ring
    have h2 : 2 * ((m : ℝ) + 1) + 1 = 2 * (m + 1 : ℝ) + 1 := by ring
    rw [h1, h2]
    ring

lemma harmonic_half_le_log_p (p : ℕ) [hp : Fact p.Prime] (hp3 : 3 ≤ p) :
    ∑ j ∈ Finset.Icc 1 ((p - 1) / 2), (1 / (j : ℝ)) ≤ Real.log p := by
  set m := (p - 1) / 2
  have hsum_le : ∑ j ∈ Finset.Icc 1 m, (1 / (j : ℝ)) ≤
      ∑ j ∈ Finset.Icc 1 m, (Real.log (2 * (j : ℝ) + 1) - Real.log (2 * (j : ℝ) - 1)) := by
    apply Finset.sum_le_sum
    intro j hj
    rw [Finset.mem_Icc] at hj
    exact inv_le_log_sub_log j hj.1
  rw [sum_log_telescoping m] at hsum_le
  have hp_odd : p % 2 = 1 := by
    rcases hp.out.eq_two_or_odd with rfl | hodd
    · omega
    · exact hodd
  have hm_eq : 2 * (m : ℝ) + 1 = (p : ℝ) := by
    have : 2 * m + 1 = p := by omega
    exact_mod_cast this
  rw [hm_eq] at hsum_le
  exact hsum_le

lemma norm_stdAddChar {N : ℕ} [NeZero N] (j : ZMod N) :
    ‖ZMod.stdAddChar j‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe (ZMod.toCircle j)

lemma stdAddChar_mul_nat (p : ℕ) [NeZero p] (j : ZMod p) (n : ℕ) :
    ZMod.stdAddChar (j * (n : ZMod p)) = (ZMod.stdAddChar j) ^ n := by
  have : j * (n : ZMod p) = n • j := by
    rw [nsmul_eq_mul, mul_comm]
  rw [this]
  exact AddChar.map_nsmul_eq_pow (ZMod.stdAddChar) n j

lemma norm_geom_sum_le (ω : ℂ) (hω : ‖ω‖ = 1) (hω1 : ω ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 N, ω ^ n‖ ≤ 2 / ‖1 - ω‖ := by
  have hle : 1 ≤ N + 1 := by omega
  rw [← Finset.Ico_succ_right_eq_Icc]
  change ‖∑ n ∈ Finset.Ico 1 (N + 1), ω ^ n‖ ≤ 2 / ‖1 - ω‖
  have hgeom := geom_sum_Ico hω1 hle
  rw [pow_one] at hgeom
  rw [hgeom]
  rw [norm_div]
  have htop : ω ^ (N + 1) - ω = ω * (ω ^ N - 1) := by ring
  rw [htop, norm_mul, hω, one_mul]
  have hsub : ‖ω - 1‖ = ‖1 - ω‖ := norm_sub_rev ω 1
  rw [hsub]
  have htop_le : ‖ω ^ N - 1‖ ≤ 2 := by
    have : ‖ω ^ N - 1‖ ≤ ‖ω ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le (ω ^ N) 1
    rw [norm_pow, hω, one_pow, norm_one] at this
    linarith
  have hbot_pos : 0 < ‖1 - ω‖ := by
    rw [norm_pos_iff]
    intro h
    apply hω1
    linear_combination -h
  exact div_le_div_of_nonneg_right htop_le hbot_pos.le

lemma norm_gaussSum_eq (p : ℕ) [Fact p.Prime] (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1)
    (ψ : AddChar (ZMod p) ℂ) (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ = Real.sqrt p := by
  have h := gaussSum_mul_gaussSum_eq_card (R := ZMod p) (R' := ℂ) hχ hψ
  have hstar := star_gaussSum_eq χ ψ
  have hcard : (Fintype.card (ZMod p) : ℂ) = (p : ℂ) := by simp
  rw [← hstar] at h
  rw [hcard] at h
  have hconj : gaussSum χ ψ * star (gaussSum χ ψ) = (Complex.normSq (gaussSum χ ψ) : ℂ) := by
    exact Complex.mul_conj (gaussSum χ ψ)
  have hnormSq : (Complex.normSq (gaussSum χ ψ) : ℂ) = (p : ℂ) := by
    rw [← hconj, h]
  have hnormSq_real : Complex.normSq (gaussSum χ ψ) = p := by
    exact_mod_cast hnormSq
  rw [Complex.norm_def, hnormSq_real]

lemma sum_chi_eq (p : ℕ) [hp : Fact p.Prime] (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod p) =
      (p : ℂ)⁻¹ * gaussSum χ ZMod.stdAddChar *
        ∑ j : ZMod p, χ⁻¹ (-j) * ∑ n ∈ Finset.Icc 1 N, ZMod.stdAddChar (j * (n : ZMod p)) := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have hprim : χ.IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def]
    have hdvd := DirichletCharacter.conductor_dvd_level χ
    rcases (Nat.dvd_prime hp.out).mp hdvd with h1 | hp'
    · exfalso; exact hχ (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h1)
    · exact hp'
  have hdft := DirichletCharacter.IsPrimitive.fourierTransform_eq_inv_mul_gaussSum hprim
  have hinv : χ = ZMod.dft.symm (ZMod.dft (⇑χ)) := (ZMod.dft.symm_apply_apply (⇑χ)).symm
  have h_app (n : ZMod p) : χ n = (p : ℂ)⁻¹ * gaussSum χ ZMod.stdAddChar *
      ∑ j : ZMod p, χ⁻¹ (-j) * ZMod.stdAddChar (j * n) := by
    have ha := congr_fun hinv n
    rw [ZMod.invDFT_apply] at ha
    simp only [hdft] at ha
    simp only [smul_eq_mul] at ha
    rw [ha, mul_assoc]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  simp_rw [h_app]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]

lemma sum_chi_eq_nonzero (p : ℕ) [hp : Fact p.Prime] (χ : DirichletCharacter ℂ p) (N : ℕ) :
    ∑ j : ZMod p, χ⁻¹ (-j) * ∑ n ∈ Finset.Icc 1 N, ZMod.stdAddChar (j * (n : ZMod p)) =
    ∑ j ∈ Finset.univ.erase 0, χ⁻¹ (-j) * ∑ n ∈ Finset.Icc 1 N, ZMod.stdAddChar (j * (n : ZMod p)) := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have h0 : χ⁻¹ (- (0 : ZMod p)) = 0 := by rw [neg_zero, MulChar.map_zero]
  have h := (Finset.add_sum_erase Finset.univ (fun j : ZMod p => χ⁻¹ (-j) * ∑ n ∈ Finset.Icc 1 N, ZMod.stdAddChar (j * (n : ZMod p))) (Finset.mem_univ (0 : ZMod p)))
  rw [h0, zero_mul, zero_add] at h
  exact h.symm

lemma norm_sum_stdAddChar_neg (p : ℕ) [NeZero p] (j : ZMod p) (N : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 N, ZMod.stdAddChar ((-j) * (n : ZMod p))‖ =
    ‖∑ n ∈ Finset.Icc 1 N, ZMod.stdAddChar (j * (n : ZMod p))‖ := by
  have hstar (n : ℕ) : ZMod.stdAddChar ((-j) * (n : ZMod p)) =
      starRingEnd ℂ (ZMod.stdAddChar (j * (n : ZMod p))) := by
    rw [neg_mul]
    exact AddChar.map_neg_eq_conj (ZMod.stdAddChar) (j * (n : ZMod p))
  simp_rw [hstar]
  rw [← map_sum (starRingEnd ℂ)]
  exact RCLike.norm_conj _

lemma sum_univ_erase_zero_eq (p : ℕ) [hp : Fact p.Prime] (hp3 : 3 ≤ p) (F : ZMod p → ℝ)
    (hF_neg : ∀ j, F (-j) = F j) :
    ∑ j ∈ Finset.univ.erase 0, F j = 2 * ∑ a ∈ Finset.Icc 1 ((p - 1) / 2), F (a : ZMod p) := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  set m := (p - 1) / 2
  have hp_odd : p % 2 = 1 := by
    rcases hp.out.eq_two_or_odd with rfl | hodd
    · omega
    · exact hodd
  have hm : p - 1 = 2 * m := by omega
  have hm_lt_p : m < p := by omega
  have hval_lt : ∀ a ∈ Finset.Icc 1 m, a < p := by
    intro a ha
    rw [Finset.mem_Icc] at ha
    omega
  have hS_inj : ∀ a ∈ Finset.Icc 1 m, ∀ b ∈ Finset.Icc 1 m, (a : ZMod p) = (b : ZMod p) → a = b := by
    intro a ha b hb hab
    have hva : (a : ZMod p).val = a := ZMod.val_natCast_of_lt (hval_lt a ha)
    have hvb : (b : ZMod p).val = b := ZMod.val_natCast_of_lt (hval_lt b hb)
    rw [← hva, ← hvb, hab]
  set S := (Finset.Icc 1 m).image (fun a : ℕ => (a : ZMod p)) with hS_def
  have hcard_S : S.card = m := by
    rw [hS_def, Finset.card_image_of_injOn]
    · rw [Nat.card_Icc 1 m]; omega
    · exact hS_inj
  set S' := S.image Neg.neg with hS'_def
  have hcard_S' : S'.card = m := by
    rw [hS'_def, Finset.card_image_of_injective _ neg_injective, hcard_S]
  have h_disj : Disjoint S S' := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [hS_def, Finset.mem_image] at hx
    rcases hx with ⟨a, ha, rfl⟩
    rw [hS'_def, Finset.mem_image] at hx'
    rcases hx' with ⟨y, hy, h_neg⟩
    rw [hS_def, Finset.mem_image] at hy
    rcases hy with ⟨b, hb, rfl⟩
    rw [Finset.mem_Icc] at ha hb
    have hab : ((a + b : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination -h_neg
    have hdvd : p ∣ a + b := (CharP.cast_eq_zero_iff (ZMod p) p (a + b)).mp hab
    have hpos : 0 < a + b := by omega
    have hlt : a + b < p := by omega
    have : a + b = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
    omega
  have hsub : S ∪ S' ⊆ Finset.univ.erase 0 := by
    intro x hx
    rw [Finset.mem_union] at hx
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ x⟩
    rcases hx with hx | hx
    · rw [hS_def, Finset.mem_image] at hx
      rcases hx with ⟨a, ha, rfl⟩
      rw [Finset.mem_Icc] at ha
      intro h0
      have : (a : ZMod p).val = 0 := by rw [h0, ZMod.val_zero]
      rw [ZMod.val_natCast_of_lt (by omega)] at this
      omega
    · rw [hS'_def, Finset.mem_image] at hx
      rcases hx with ⟨y, hy, rfl⟩
      rw [hS_def, Finset.mem_image] at hy
      rcases hy with ⟨a, ha, rfl⟩
      rw [Finset.mem_Icc] at ha
      intro h0
      have : (a : ZMod p) = 0 := by linear_combination -h0
      have : (a : ZMod p).val = 0 := by rw [this, ZMod.val_zero]
      rw [ZMod.val_natCast_of_lt (by omega)] at this
      omega
  have hcard_union : (S ∪ S').card = 2 * m := by
    rw [Finset.card_union_of_disjoint h_disj, hcard_S, hcard_S']
    ring
  have hcard_erase : (Finset.univ.erase (0 : ZMod p)).card = 2 * m := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, ZMod.card p]
    omega
  have heq : S ∪ S' = Finset.univ.erase 0 := by
    exact Finset.eq_of_subset_of_card_le hsub (by rw [hcard_union, hcard_erase])
  rw [← heq, Finset.sum_union h_disj]
  have hsum_S : ∑ j ∈ S, F j = ∑ a ∈ Finset.Icc 1 m, F (a : ZMod p) := by
    rw [hS_def, Finset.sum_image hS_inj]
  have hsum_S' : ∑ j ∈ S', F j = ∑ a ∈ Finset.Icc 1 m, F (a : ZMod p) := by
    rw [hS'_def, Finset.sum_image (fun _ _ _ _ h => neg_inj.mp h)]
    simp_rw [hF_neg]
    exact hsum_S
  rw [hsum_S, hsum_S']
  ring

lemma sqrt_div_mul (p : ℕ) (hp : 0 < p) :
    (Real.sqrt (p : ℝ) / (p : ℝ)) * ((p : ℝ) * Real.log (p : ℝ)) =
      Real.sqrt (p : ℝ) * Real.log (p : ℝ) := by
  have hp_ne : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [div_mul_eq_mul_div, mul_comm (Real.sqrt (p : ℝ)), mul_assoc, mul_div_cancel_left₀ _ hp_ne, mul_comm]

theorem charSum_norm_le (p : Nat) (hp : p.Prime) (chi : MulChar (ZMod p) Complex)
    (h : Not (chi = 1)) (N : Nat) :
    Norm.norm ((Finset.Icc 1 N).sum (fun n => chi (n : ZMod p))) <= Real.sqrt p * Real.log p := by
  by_cases hp2 : p = 2
  · subst hp2
    have h_chi_one : chi = 1 := by
      ext x
      have : x = 1 := Subsingleton.elim x 1
      subst this
      simp
    exact (h h_chi_one).elim
  have hp3 : 3 ≤ p := by
    have : p ≠ 2 := hp2
    have : 2 ≤ p := hp.two_le
    omega
  haveI : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hp_pos : 0 < p := hp.pos
  have hp_pos_r : 0 < (p : ℝ) := Nat.cast_pos.mpr hp_pos
  rw [sum_chi_eq p chi h N]
  rw [sum_chi_eq_nonzero p chi N]
  set F := fun j : ZMod p => ‖∑ n ∈ Finset.Icc 1 N, ZMod.stdAddChar (j * (n : ZMod p))‖ with hF_def
  have hF_neg : ∀ j, F (-j) = F j := fun j => norm_sum_stdAddChar_neg p j N
  have h_norm_prod : ‖(p : ℂ)⁻¹ * gaussSum chi ZMod.stdAddChar *
      ∑ j ∈ Finset.univ.erase 0, chi⁻¹ (-j) * ∑ n ∈ Finset.Icc 1 N, ZMod.stdAddChar (j * (n : ZMod p))‖ ≤
      (Real.sqrt p / p) * ∑ j ∈ Finset.univ.erase 0, F j := by
    rw [norm_mul, norm_mul]
    have hinv : ‖(p : ℂ)⁻¹‖ = 1 / (p : ℝ) := by
      rw [norm_inv, Complex.norm_natCast]
      ring
    have hgauss : ‖gaussSum chi ZMod.stdAddChar‖ = Real.sqrt p :=
      norm_gaussSum_eq p chi h ZMod.stdAddChar (ZMod.isPrimitive_stdAddChar p)
    rw [hinv, hgauss]
    have h_coeff : (1 / (p : ℝ)) * Real.sqrt p = Real.sqrt p / p := by ring
    rw [h_coeff]
    have h_sum_le : ‖∑ j ∈ Finset.univ.erase 0, chi⁻¹ (-j) * ∑ n ∈ Finset.Icc 1 N, ZMod.stdAddChar (j * (n : ZMod p))‖ ≤
        ∑ j ∈ Finset.univ.erase 0, F j := by
      have h1 := norm_sum_le (Finset.univ.erase 0)
        (fun j => chi⁻¹ (-j) * ∑ n ∈ Finset.Icc 1 N, ZMod.stdAddChar (j * (n : ZMod p)))
      refine h1.trans ?_
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul]
      have h_chi_le : ‖chi⁻¹ (-j)‖ ≤ 1 := DirichletCharacter.norm_le_one (chi⁻¹) (-j)
      have h_F_nonneg : 0 ≤ F j := norm_nonneg _
      nlinarith
    have h_sqrt_nonneg : 0 ≤ Real.sqrt p / p := by positivity
    exact mul_le_mul_of_nonneg_left h_sum_le h_sqrt_nonneg
  refine h_norm_prod.trans ?_
  rw [sum_univ_erase_zero_eq p hp3 F hF_neg]
  have hF_le : ∀ a ∈ Finset.Icc 1 ((p - 1) / 2), F (a : ZMod p) ≤ (p : ℝ) / (2 * (a : ℝ)) := by
    intro a ha
    rw [Finset.mem_Icc] at ha
    have ha_pos : 0 < a := ha.1
    have ha_le : a ≤ (p - 1) / 2 := ha.2
    have ha_lt_p : a < p := by omega
    have h_a_ne : (a : ZMod p) ≠ 0 := by
      intro h0
      have := (ZMod.val_natCast_of_lt ha_lt_p).symm.trans (congr_arg ZMod.val h0)
      rw [ZMod.val_zero] at this
      omega
    have hω_ne : ZMod.stdAddChar (a : ZMod p) ≠ 1 := by
      intro h1
      have : ZMod.stdAddChar (a : ZMod p) = ZMod.stdAddChar (0 : ZMod p) := by
        rw [h1, AddChar.map_zero_eq_one]
      have h_inj := ZMod.injective_stdAddChar this
      exact h_a_ne h_inj
    have hω_norm : ‖ZMod.stdAddChar (a : ZMod p)‖ = 1 := norm_stdAddChar (a : ZMod p)
    have h_geom := norm_geom_sum_le (ZMod.stdAddChar (a : ZMod p)) hω_norm hω_ne N
    have hF_a : F (a : ZMod p) = ‖∑ n ∈ Finset.Icc 1 N, (ZMod.stdAddChar (a : ZMod p)) ^ n‖ := by
      dsimp [F]
      congr 1
      exact Finset.sum_congr rfl (fun n _ => stdAddChar_mul_nat p (a : ZMod p) n)
    rw [hF_a]
    refine h_geom.trans ?_
    have h_toCircle := ZMod.toCircle_apply (N := p) (a : ZMod p)
    have h_std := ZMod.stdAddChar_apply (N := p) (a : ZMod p)
    rw [h_std, h_toCircle]
    have hva : (a : ZMod p).val = a := ZMod.val_natCast_of_lt ha_lt_p
    rw [hva]
    have hcast := exp_cast_eq p a
    rw [hcast]
    have h_ge := norm_one_sub_exp_ge p a ha_pos ha_le hp_pos
    have h_pos_4 : 0 < 4 * (a : ℝ) / (p : ℝ) := by positivity
    have h_div_le : 2 / ‖1 - exp (((2 * Real.pi * (a : ℝ) / (p : ℝ) : ℝ) : ℂ) * I)‖ ≤
        2 / (4 * (a : ℝ) / (p : ℝ)) := div_le_div_of_nonneg_left (by norm_num) h_pos_4 h_ge
    refine h_div_le.trans ?_
    have : 2 / (4 * (a : ℝ) / (p : ℝ)) = (p : ℝ) / (2 * (a : ℝ)) := by
      have ha_ne : (a : ℝ) ≠ 0 := by positivity
      have hp_ne : (p : ℝ) ≠ 0 := by positivity
      field_simp
      ring
    rw [this]
  have h_sum_F_le : ∑ a ∈ Finset.Icc 1 ((p - 1) / 2), F (a : ZMod p) ≤
      ∑ a ∈ Finset.Icc 1 ((p - 1) / 2), ((p : ℝ) / (2 * (a : ℝ))) := by
    apply Finset.sum_le_sum hF_le
  have h_two_sum : 2 * ∑ a ∈ Finset.Icc 1 ((p - 1) / 2), F (a : ZMod p) ≤
      (p : ℝ) * Real.log p := by
    have h2 : 2 * ∑ a ∈ Finset.Icc 1 ((p - 1) / 2), ((p : ℝ) / (2 * (a : ℝ))) =
        (p : ℝ) * ∑ a ∈ Finset.Icc 1 ((p - 1) / 2), (1 / (a : ℝ)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      have ha_ne : (a : ℝ) ≠ 0 := by
        rw [Finset.mem_Icc] at ha
        exact Nat.cast_ne_zero.mpr (by omega)
      field_simp
    calc 2 * ∑ a ∈ Finset.Icc 1 ((p - 1) / 2), F (a : ZMod p)
      _ ≤ 2 * ∑ a ∈ Finset.Icc 1 ((p - 1) / 2), ((p : ℝ) / (2 * (a : ℝ))) := by linarith [h_sum_F_le]
      _ = (p : ℝ) * ∑ a ∈ Finset.Icc 1 ((p - 1) / 2), (1 / (a : ℝ)) := h2
      _ ≤ (p : ℝ) * Real.log p := by
        have := harmonic_half_le_log_p p hp3
        exact mul_le_mul_of_nonneg_left this hp_pos_r.le
  calc Real.sqrt p / p * (2 * ∑ a ∈ Finset.Icc 1 ((p - 1) / 2), F (a : ZMod p))
    _ ≤ Real.sqrt p / p * ((p : ℝ) * Real.log p) := by
      have : 0 ≤ Real.sqrt p / p := by positivity
      exact mul_le_mul_of_nonneg_left h_two_sum this
    _ = Real.sqrt p * Real.log p := sqrt_div_mul p hp_pos

lemma legendreSym_eq_quadraticChar (p : ℕ) [Fact p.Prime] (a : ℤ) :
    legendreSym p a = quadraticChar (ZMod p) (a : ZMod p) := by
  by_cases ha0 : (a : ZMod p) = 0
  · rw [(legendreSym.eq_zero_iff p a).mpr ha0]
    rw [ha0, MulChar.map_zero]
  · by_cases hsq : IsSquare (a : ZMod p)
    · rw [(legendreSym.eq_one_iff p ha0).mpr hsq]
      rw [quadraticChar_one_iff_isSquare ha0 |>.mpr hsq]
    · rw [(legendreSym.eq_neg_one_iff p).mpr hsq]
      rw [quadraticChar_neg_one_iff_not_isSquare.mpr hsq]

lemma norm_intCast_eq_abs (x : ℤ) :
    ‖(x : ℂ)‖ = abs (x : ℝ) := by
  have : (x : ℂ) = ((x : ℝ) : ℂ) := by simp
  rw [this, Complex.norm_real]
  rfl

lemma ringHomComp_ne_one_of_ne_one (p : ℕ) [hp : Fact p.Prime] (h2 : p ≠ 2) :
    (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ) ≠ 1 := by
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ringChar.eq (ZMod p) p]
    exact h2
  have hne := quadraticChar_ne_one hchar
  intro h_eq
  apply hne
  ext x
  have h_app := congr_arg (fun (c : MulChar (ZMod p) ℂ) => c (x : ZMod p)) h_eq
  rw [MulChar.ringHomComp_apply] at h_app
  rw [MulChar.one_apply x.isUnit] at h_app
  rw [MulChar.one_apply x.isUnit]
  have h_cast : ((quadraticChar (ZMod p) (x : ZMod p) : ℤ) : ℂ) = ((1 : ℤ) : ℂ) := by
    simpa using h_app
  exact Int.cast_injective h_cast

theorem legendreSum_le (p : Nat) [hp : Fact p.Prime] (h2 : Not (p = 2)) (N : Nat) :
    abs (((Finset.Icc 1 N).sum (fun n => legendreSym p (n : Int)) : Int) : Real) <=
      Real.sqrt p * Real.log p := by
  set χ := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ) with hχ_def
  have hχ_ne : χ ≠ 1 := ringHomComp_ne_one_of_ne_one p h2
  have hbound := charSum_norm_le p hp.out χ hχ_ne N
  have h_eq : ((Finset.Icc 1 N).sum (fun n => χ (n : ZMod p))) =
      (((Finset.Icc 1 N).sum (fun n => legendreSym p (n : Int)) : Int) : ℂ) := by
    push_cast
    apply Finset.sum_congr rfl
    intro n _
    rw [MulChar.ringHomComp_apply]
    simp only [Int.coe_castRingHom]
    have hcast_n : (((n : ℤ) : ZMod p)) = (n : ZMod p) := by push_cast; rfl
    have := legendreSym_eq_quadraticChar p (n : ℤ)
    rw [hcast_n] at this
    rw [this]
  rw [h_eq] at hbound
  have hnorm : ‖(((Finset.Icc 1 N).sum (fun n => legendreSym p (n : Int)) : Int) : ℂ)‖ =
      abs (((Finset.Icc 1 N).sum (fun n => legendreSym p (n : Int)) : Int) : Real) := by
    exact norm_intCast_eq_abs _
  rw [hnorm] at hbound
  exact hbound


lemma exists_order_k_of_cyclic (G : Type*) [CommGroup G] [Finite G] [IsCyclic G]
    (k : ℕ) (hk : 2 ≤ k) (hkdvd : k ∣ Nat.card G) :
    ∃ u : G, u ≠ 1 ∧ u ^ k = 1 := by
  have : 0 < k := by omega
  have hcard_pos : 0 < Nat.card G := Nat.card_pos
  rcases hkdvd with ⟨m, hm⟩
  rcases IsCyclic.exists_generator (α := G) with ⟨g, hg⟩
  have hg_card : orderOf g = Nat.card G := orderOf_eq_card_of_forall_mem_zpowers hg
  set u := g ^ m with hu_def
  refine ⟨u, ?_, ?_⟩
  · intro hu1
    have h_ord : orderOf g ∣ m := by
      rw [orderOf_dvd_iff_pow_eq_one]
      exact hu1
    rw [hg_card] at h_ord
    have hm_pos : 0 < m := by
      rcases m with _ | m <;> omega
    have hm_lt : m < Nat.card G := by
      have : 2 * m ≤ k * m := Nat.mul_le_mul_right m hk
      omega
    have : m = 0 := Nat.eq_zero_of_dvd_of_lt h_ord hm_lt
    omega
  · rw [hu_def, ← pow_mul, mul_comm m k, ← hm]
    rw [← hg_card, pow_orderOf_eq_one]

lemma natCard_units_zmod_prime (p : ℕ) [hp : Fact p.Prime] :
    Nat.card (ZMod p)ˣ = p - 1 := by
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hp.out]

lemma exists_char_order_k (p k : ℕ) [hp : Fact p.Prime] (hk : 2 ≤ k) (hkp : (p - 1) % k = 0) :
    ∃ chi : MulChar (ZMod p) ℂ, chi ≠ 1 ∧ chi ^ k = 1 := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have hkdvd : k ∣ Nat.card (ZMod p)ˣ := by
    rw [natCard_units_zmod_prime p]
    exact Nat.dvd_of_mod_eq_zero hkp
  obtain ⟨e⟩ := DirichletCharacter.mulEquiv_units ℂ p
  rcases exists_order_k_of_cyclic (G := (ZMod p)ˣ) k hk hkdvd with ⟨u, hu_ne, hu_pow⟩
  set chi := e.symm u with hchi_def
  refine ⟨chi, ?_, ?_⟩
  · intro h1
    have : e.symm u = e.symm 1 := by rw [← hchi_def, h1, map_one]
    have := e.symm.injective this
    exact hu_ne this
  · rw [hchi_def, ← map_pow, hu_pow, map_one]

lemma mulChar_pow_apply_of_isUnit (R R' : Type*) [CommMonoid R] [CommMonoidWithZero R']
    (χ : MulChar R R') (k : ℕ) (a : R) (ha : IsUnit a) :
    (χ ^ k) a = (χ a) ^ k := by
  induction' k with k ih
  · rw [pow_zero, pow_zero, MulChar.one_apply ha]
  · rw [pow_succ, pow_succ, MulChar.mul_apply, ih]

lemma chi_pow_k_eq_one_of_isSquare_pow (p k : ℕ) [hp : Fact p.Prime] (hk : 1 ≤ k)
    (chi : MulChar (ZMod p) ℂ) (hchi_pow : chi ^ k = 1)
    (n : ℕ) (hn_pos : 1 ≤ n) (hn_lt : n < p)
    (x : ZMod p) (hx : x ^ k = (n : ZMod p)) :
    chi (n : ZMod p) = 1 := by
  have hn_ne : (n : ZMod p) ≠ 0 := by
    intro h0
    have : (n : ZMod p).val = 0 := by rw [h0, ZMod.val_zero]
    rw [ZMod.val_natCast_of_lt hn_lt] at this
    omega
  have hx_ne : x ≠ 0 := by
    intro hx0
    rw [hx0, zero_pow (by omega)] at hx
    exact hn_ne hx.symm
  have hx_unit : IsUnit x := isUnit_iff_ne_zero.mpr hx_ne
  rw [← hx, map_pow]
  have := mulChar_pow_apply_of_isUnit (ZMod p) ℂ chi k x hx_unit
  rw [hchi_pow, MulChar.one_apply hx_unit] at this
  exact this.symm

lemma exists_unit_ne_one_of_chi_ne_one (R R' : Type*) [CommMonoid R] [CommMonoidWithZero R']
    (χ : MulChar R R') (h : χ ≠ 1) :
    ∃ u : Rˣ, χ (u : R) ≠ 1 := by
  by_contra! h_all
  apply h
  ext u
  rw [MulChar.one_apply u.isUnit]
  exact h_all u

theorem exists_not_pow_le (p k : Nat) (hp : p.Prime) (hk : 2 <= k) (hkp : (p - 1) % k = 0) :
    exists n : Nat, 1 <= n /\ (n : Real) <= Real.sqrt p * Real.log p + 1 /\
      forall x : ZMod p, Not (x ^ k = (n : ZMod p)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rcases exists_char_order_k p k hk hkp with ⟨chi, hchi_ne, hchi_pow⟩
  rcases exists_unit_ne_one_of_chi_ne_one (ZMod p) ℂ chi hchi_ne with ⟨u, hu⟩
  set a0 := (u : ZMod p).val with ha0_def
  have hu_ne : (u : ZMod p) ≠ 0 := u.ne_zero
  have ha0_pos : 1 ≤ a0 := by
    have : 0 < (u : ZMod p).val := ZMod.val_pos.mpr hu_ne
    omega
  have ha0_lt : a0 < p := ZMod.val_lt (u : ZMod p)
  have ha0_not_pow : ∀ x : ZMod p, ¬ x ^ k = (a0 : ZMod p) := by
    intro x hx
    have hcast : (a0 : ZMod p) = (u : ZMod p) := ZMod.natCast_zmod_val (u : ZMod p)
    rw [hcast] at hx
    have h1 := chi_pow_k_eq_one_of_isSquare_pow p k (by omega) chi hchi_pow a0 ha0_pos ha0_lt x (by rw [hcast, hx])
    rw [hcast] at h1
    exact hu h1
  have hex : ∃ n : ℕ, 1 ≤ n ∧ ∀ x : ZMod p, ¬ x ^ k = (n : ZMod p) := ⟨a0, ha0_pos, ha0_not_pow⟩
  set n0 := Nat.find hex with hn0_def
  have hn0_prop := Nat.find_spec hex
  have hn0_min : ∀ m < n0, ¬(1 ≤ m ∧ ∀ x : ZMod p, ¬ x ^ k = (m : ZMod p)) := fun m hm => Nat.find_min hex hm
  have hn0_pos : 1 ≤ n0 := hn0_prop.1
  have hn0_not_pow : ∀ x : ZMod p, ¬ x ^ k = (n0 : ZMod p) := hn0_prop.2
  have hn0_le_a0 : n0 ≤ a0 := Nat.find_min' hex ⟨ha0_pos, ha0_not_pow⟩
  have hn0_lt_p : n0 < p := hn0_le_a0.trans_lt ha0_lt
  have hn0_all_chi : ∀ m ∈ Finset.Icc 1 (n0 - 1), chi (m : ZMod p) = 1 := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hm_lt : m < n0 := by omega
    have hm_not := hn0_min m hm_lt
    have hm_pow : ∃ x : ZMod p, x ^ k = (m : ZMod p) := by
      by_contra! h_all
      exact hm_not ⟨hm.1, h_all⟩
    rcases hm_pow with ⟨x, hx⟩
    have hm_lt_p : m < p := hm_lt.trans hn0_lt_p
    exact chi_pow_k_eq_one_of_isSquare_pow p k (by omega) chi hchi_pow m hm.1 hm_lt_p x hx
  have h_sum_eq : ∑ m ∈ Finset.Icc 1 (n0 - 1), chi (m : ZMod p) = ((n0 - 1 : ℕ) : ℂ) := by
    have : ∑ m ∈ Finset.Icc 1 (n0 - 1), chi (m : ZMod p) =
        ∑ m ∈ Finset.Icc 1 (n0 - 1), (1 : ℂ) := by
      apply Finset.sum_congr rfl
      exact hn0_all_chi
    rw [this, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [Nat.card_Icc 1 (n0 - 1)]
    push_cast
    rfl
  have h_bound := charSum_norm_le p hp chi hchi_ne (n0 - 1)
  rw [h_sum_eq] at h_bound
  have hnorm : ‖((n0 - 1 : ℕ) : ℂ)‖ = ((n0 - 1 : ℕ) : ℝ) := by
    rw [Complex.norm_natCast]
  rw [hnorm] at h_bound
  have hn0_le : (n0 : ℝ) ≤ Real.sqrt p * Real.log p + 1 := by
    rw [Nat.cast_sub hn0_pos] at h_bound
    push_cast at h_bound
    linarith
  exact ⟨n0, hn0_pos, hn0_le, hn0_not_pow⟩




theorem card_residues_sub_le (p : Nat) [hp : Fact p.Prime] (h2 : Not (p = 2)) (N : Nat)
    (hN : N < p) :
    abs (2 * (((Finset.Icc 1 N).filter (fun n : Nat => legendreSym p (n : Int) = 1)).card : Real) -
        N) <= Real.sqrt p * Real.log p := by
  set S := Finset.Icc 1 N with hS_def
  set R := S.filter (fun n : Nat => legendreSym p (n : Int) = 1) with hR_def
  set T := S.filter (fun n : Nat => legendreSym p (n : Int) = -1) with hT_def
  have h_cases : ∀ n ∈ S, legendreSym p (n : Int) = 1 ∨ legendreSym p (n : Int) = -1 := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn_pos : 0 < n := hn.1
    have hn_lt : n < p := hn.2.trans_lt hN
    have h_ne_zero : ((n : ℤ) : ZMod p) ≠ 0 := by
      intro h0
      have hcast : ((n : ℤ) : ZMod p) = (n : ZMod p) := by push_cast; rfl
      rw [hcast] at h0
      have : (n : ZMod p).val = 0 := by rw [h0, ZMod.val_zero]
      rw [ZMod.val_natCast_of_lt hn_lt] at this
      omega
    exact legendreSym.eq_one_or_neg_one p h_ne_zero
  have h_disj : Disjoint R T := by
    rw [Finset.disjoint_filter]
    intro n _ h1
    omega
  have h_union : R ∪ T = S := by
    ext n
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro (⟨hn, _⟩ | ⟨hn, _⟩) <;> exact hn
    · intro hn
      rcases h_cases n hn with h1 | hneg1
      · left; exact ⟨hn, h1⟩
      · right; exact ⟨hn, hneg1⟩
  have h_sum_split : ∑ n ∈ S, legendreSym p (n : Int) =
      (∑ n ∈ R, legendreSym p (n : Int)) + (∑ n ∈ T, legendreSym p (n : Int)) := by
    rw [← h_union, Finset.sum_union h_disj]
  have h_sum_R : ∑ n ∈ R, legendreSym p (n : Int) = (R.card : ℤ) := by
    have : ∑ n ∈ R, legendreSym p (n : Int) = ∑ n ∈ R, (1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mem_filter] at hn
      exact hn.2
    rw [this, Finset.sum_const, nsmul_eq_mul, mul_one]
  have h_sum_T : ∑ n ∈ T, legendreSym p (n : Int) = - (T.card : ℤ) := by
    have : ∑ n ∈ T, legendreSym p (n : Int) = ∑ n ∈ T, (-1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mem_filter] at hn
      exact hn.2
    rw [this, Finset.sum_const, nsmul_eq_mul, mul_neg_one]
  have h_card_S : S.card = N := by
    rw [hS_def, Nat.card_Icc 1 N]
    omega
  have h_card_sum : (R.card : ℤ) + (T.card : ℤ) = (N : ℤ) := by
    have := Finset.card_union_of_disjoint h_disj
    rw [h_union, h_card_S] at this
    exact_mod_cast this.symm
  have h_sum_val : ∑ n ∈ S, legendreSym p (n : Int) = 2 * (R.card : ℤ) - (N : ℤ) := by
    rw [h_sum_split, h_sum_R, h_sum_T]
    omega
  have h_cast : (((∑ n ∈ S, legendreSym p (n : Int)) : ℤ) : ℝ) =
      2 * (R.card : ℝ) - (N : ℝ) := by
    rw [h_sum_val]
    push_cast
    ring
  have h_bound := legendreSum_le p h2 N
  rw [← h_cast]
  exact h_bound


lemma abs_cast_sub_one (q : ℕ) (hq : 1 ≤ q) :
    abs (((((q - 1 : ℕ) : ℤ) : ℤ) : ℝ)) = (q : ℝ) - 1 := by
  have : ((((q - 1 : ℕ) : ℤ) : ℤ) : ℝ) = ((q - 1 : ℕ) : ℝ) := by simp
  rw [this, Nat.cast_sub hq]
  push_cast
  have : 0 ≤ (q : ℝ) - 1 := by
    have : 1 ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  exact abs_of_nonneg this

lemma exists_legendreSym_eq_neg_one (p : ℕ) [hp : Fact p.Prime] (h2 : p ≠ 2) :
    ∃ a : ℕ, 1 ≤ a ∧ a < p ∧ legendreSym p (a : ℤ) = -1 := by
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ringChar.eq (ZMod p) p]
    exact h2
  rcases quadraticChar_exists_neg_one' hchar with ⟨u, hu⟩
  set a_nat := (u : ZMod p).val with ha_nat_def
  have hu_ne : (u : ZMod p) ≠ 0 := u.ne_zero
  have ha_pos : 1 ≤ a_nat := by
    have : 0 < (u : ZMod p).val := ZMod.val_pos.mpr hu_ne
    omega
  have ha_lt : a_nat < p := ZMod.val_lt (u : ZMod p)
  refine ⟨a_nat, ha_pos, ha_lt, ?_⟩
  rw [legendreSym_eq_quadraticChar]
  have : ((a_nat : ℤ) : ZMod p) = (u : ZMod p) := by
    push_cast
    exact ZMod.natCast_zmod_val (u : ZMod p)
  rw [this, hu]

theorem exists_prime_nonresidue_le (p : Nat) [hp : Fact p.Prime] (h2 : Not (p = 2)) :
    exists q : Nat, q.Prime /\ (q : Real) <= Real.sqrt p * Real.log p + 1 /\
      legendreSym p (q : Int) = -1 := by
  rcases exists_legendreSym_eq_neg_one p h2 with ⟨a0, ha0_pos, ha0_lt, ha0_val⟩
  have hex : ∃ n : ℕ, 1 ≤ n ∧ legendreSym p (n : ℤ) = -1 := ⟨a0, ha0_pos, ha0_val⟩
  set q := Nat.find hex with hq_def
  have hq_prop := Nat.find_spec hex
  have hq_min : ∀ m < q, ¬(1 ≤ m ∧ legendreSym p (m : ℤ) = -1) := fun m hm => Nat.find_min hex hm
  have hq_pos : 1 ≤ q := hq_prop.1
  have hq_val : legendreSym p (q : ℤ) = -1 := hq_prop.2
  have hq_le_a0 : q ≤ a0 := Nat.find_min' hex ⟨ha0_pos, ha0_val⟩
  have hq_lt_p : q < p := hq_le_a0.trans_lt ha0_lt
  have hq_all_one : ∀ n ∈ Finset.Icc 1 (q - 1), legendreSym p (n : ℤ) = 1 := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn_lt : n < q := by omega
    have hn_not := hq_min n hn_lt
    have hn_ne_neg1 : legendreSym p (n : ℤ) ≠ -1 := by
      intro hneg
      exact hn_not ⟨hn.1, hneg⟩
    have hn_lt_p : n < p := hn_lt.trans hq_lt_p
    have h_ne_zero : ((n : ℤ) : ZMod p) ≠ 0 := by
      intro h0
      have hcast : ((n : ℤ) : ZMod p) = (n : ZMod p) := by push_cast; rfl
      rw [hcast] at h0
      have : (n : ZMod p).val = 0 := by rw [h0, ZMod.val_zero]
      rw [ZMod.val_natCast_of_lt hn_lt_p] at this
      omega
    rcases legendreSym.eq_one_or_neg_one p h_ne_zero with h1 | hneg1
    · exact h1
    · exfalso; exact hn_ne_neg1 hneg1
  have hq_prime : q.Prime := by
    have hq_gt_one : 2 ≤ q := by
      by_contra! h
      have hq1 : q = 1 := by omega
      have hq_val' := hq_val
      rw [hq1] at hq_val'
      change legendreSym p (1 : ℤ) = -1 at hq_val'
      have h1 : legendreSym p (1 : ℤ) = 1 := legendreSym.at_one p
      rw [h1] at hq_val'
      norm_num at hq_val'
    rw [Nat.prime_def_lt']
    refine ⟨hq_gt_one, ?_⟩
    intro d hd_ge hd_lt hd_dvd
    have hd_val : legendreSym p (d : ℤ) = 1 := by
      have : d ∈ Finset.Icc 1 (q - 1) := by rw [Finset.mem_Icc]; omega
      exact hq_all_one d this
    rcases hd_dvd with ⟨c, hc_eq⟩
    have hc_pos : 1 ≤ c := by
      rcases c with _ | c <;> omega
    have hc_lt : c < q := by
      have : 2 ≤ d := hd_ge
      rw [hc_eq]
      nlinarith
    have hc_val : legendreSym p (c : ℤ) = 1 := by
      have : c ∈ Finset.Icc 1 (q - 1) := by rw [Finset.mem_Icc]; omega
      exact hq_all_one c this
    have hmul : legendreSym p (q : ℤ) =
        legendreSym p (d : ℤ) * legendreSym p (c : ℤ) := by
      rw [hc_eq]
      push_cast
      exact legendreSym.mul p (d : ℤ) (c : ℤ)
    rw [hq_val, hd_val, hc_val, mul_one] at hmul
    norm_num at hmul
  have h_bound := legendreSum_le p h2 (q - 1)
  have h_sum_eq : ∑ n ∈ Finset.Icc 1 (q - 1), legendreSym p (n : ℤ) = ((q - 1 : ℕ) : ℤ) := by
    have : ∑ n ∈ Finset.Icc 1 (q - 1), legendreSym p (n : ℤ) =
        ∑ n ∈ Finset.Icc 1 (q - 1), (1 : ℤ) := by
      apply Finset.sum_congr rfl
      exact hq_all_one
    rw [this, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [Nat.card_Icc 1 (q - 1)]
    omega
  have h_q_le : (q : ℝ) ≤ Real.sqrt p * Real.log p + 1 := by
    rw [h_sum_eq] at h_bound
    have habs := abs_cast_sub_one q hq_pos
    rw [habs] at h_bound
    linarith
  exact ⟨q, hq_prime, h_q_le, hq_val⟩


end TuringTask
