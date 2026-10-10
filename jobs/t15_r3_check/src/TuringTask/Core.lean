import Mathlib

namespace TuringTask

private lemma gaussSum_norm_eq_sqrt (p : ℕ) [hp : Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) (ψ : AddChar (ZMod p) ℂ)
    (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ = Real.sqrt p := by
  let G := gaussSum χ ψ
  have hprod : G * star G = (p : ℂ) := by
    have hbase := gaussSum_mul_gaussSum_eq_card hχ hψ
    rw [← star_gaussSum_eq χ ψ] at hbase
    simpa [G] using hbase
  have hsq : Complex.normSq G = (p : ℝ) := by
    apply Complex.ofReal_inj.mp
    rw [Complex.normSq_eq_conj_mul_self]
    simpa [mul_comm] using hprod
  rw [Complex.norm_def, hsq]

private lemma dft_char_norm (p : ℕ) [hp : Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) (j : ZMod p) :
    ‖ZMod.dft (⇑χ) j‖ ≤ Real.sqrt p := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  by_cases hj : j = 0
  · subst j
    simp [ZMod.dft_apply, MulChar.sum_eq_zero_of_ne_one hχ]
  · rw [DirichletCharacter.fourierTransform_eq_gaussSum_mulShift]
    apply le_of_eq
    apply gaussSum_norm_eq_sqrt p χ hχ
    intro a ha
    rw [AddChar.mulShift_mulShift]
    apply (ZMod.isPrimitive_stdAddChar p)
    exact mul_ne_zero (neg_ne_zero.mpr hj) ha

private lemma norm_exp_mul_I_sub_one (θ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ = 2 * |Real.sin (θ / 2)| := by
  rw [Complex.norm_def, Complex.normSq_apply]
  rw [Complex.sub_re, Complex.sub_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]
  norm_num
  have hsq : (Real.cos θ - 1) * (Real.cos θ - 1) + Real.sin θ * Real.sin θ =
      (2 * |Real.sin (θ / 2)|) ^ 2 := by
    have habs := sq_abs (Real.sin (θ / 2))
    have htrig := Real.sin_sq_add_cos_sq θ
    have hhalf := Real.sin_sq_add_cos_sq (θ / 2)
    have hdouble := Real.cos_two_mul' (θ / 2)
    ring_nf at habs htrig hhalf hdouble ⊢
    nlinarith
  rw [hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg]
  positivity

private lemma stdAddChar_sub_one_lower (p : ℕ) [hp : Fact p.Prime]
    (j : ZMod p) :
    (4 : ℝ) * j.valMinAbs.natAbs / p ≤ ‖ZMod.stdAddChar j - 1‖ := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  let z : ℤ := j.valMinAbs
  let θ : ℝ := 2 * Real.pi * (z : ℝ) / p
  have hstd : ZMod.stdAddChar j = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [← ZMod.coe_valMinAbs j, ZMod.stdAddChar_coe]
    congr 1
    simp only [θ, z]
    push_cast
    ring
  rw [hstd, norm_exp_mul_I_sub_one]
  have hd : (j.valMinAbs.natAbs : ℝ) = |(z : ℝ)| := by
    simp [z]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hdle : (j.valMinAbs.natAbs : ℝ) ≤ (p : ℝ) / 2 := by
    have hnat := ZMod.natAbs_valMinAbs_le j
    have htwice : 2 * j.valMinAbs.natAbs ≤ p := by omega
    have htwice' : (2 * j.valMinAbs.natAbs : ℝ) ≤ p := by exact_mod_cast htwice
    norm_num at htwice'
    linarith
  have hangle : |Real.pi * (z : ℝ) / p| ≤ Real.pi / 2 := by
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hp0, ← hd]
    apply (div_le_iff₀ hp0).2
    nlinarith [Real.pi_pos]
  have hsin := Real.mul_abs_le_abs_sin hangle
  have hhalf : θ / 2 = Real.pi * (z : ℝ) / p := by
    dsimp [θ]
    field_simp
  rw [hhalf]
  rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hp0, ← hd] at hsin
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp at hsin ⊢
  nlinarith [Real.pi_pos]

private lemma stdAddChar_nat_mul (p n : ℕ) [hp : Fact p.Prime] (j : ZMod p) :
    ZMod.stdAddChar (j * (n : ZMod p)) = ZMod.stdAddChar j ^ n := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  rw [mul_comm]
  rw [← nsmul_eq_mul]
  exact AddChar.map_nsmul_eq_pow ZMod.stdAddChar n j

private lemma interval_addChar_norm_le (p : ℕ) [hp : Fact p.Prime]
    (j : ZMod p) (hj : j ≠ 0) (N : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 N, ZMod.stdAddChar (j * (n : ZMod p))‖ ≤
      (p : ℝ) / (2 * j.valMinAbs.natAbs) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  let x : ℂ := ZMod.stdAddChar j
  have hx : x ≠ 1 := by
    intro heq
    have := ZMod.injective_stdAddChar (show ZMod.stdAddChar j = ZMod.stdAddChar 0 by simpa [x] using heq)
    exact hj this
  have hset : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
    ext a
    simp
  have hsum : (∑ n ∈ Finset.Icc 1 N, ZMod.stdAddChar (j * (n : ZMod p))) =
      (x ^ (N + 1) - x) / (x - 1) := by
    rw [hset]
    simp_rw [stdAddChar_nat_mul p]
    simpa [x] using (geom_sum_Ico (x := x) hx (m := 1) (n := N + 1) (by omega))
  rw [hsum, norm_div]
  have hnum : ‖x ^ (N + 1) - x‖ ≤ 2 := by
    calc
      ‖x ^ (N + 1) - x‖ ≤ ‖x ^ (N + 1)‖ + ‖x‖ := norm_sub_le _ _
      _ = 2 := by simp [x, AddChar.norm_apply]; norm_num
  have hden := stdAddChar_sub_one_lower p j
  change (4 : ℝ) * j.valMinAbs.natAbs / p ≤ ‖x - 1‖ at hden
  have hdpos : (0 : ℝ) < j.valMinAbs.natAbs := by
    exact_mod_cast (Int.natAbs_pos.mpr ((ZMod.valMinAbs_eq_zero j).not.mpr hj))
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hdenpos : 0 < ‖x - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
  apply (div_le_iff₀ hdenpos).2
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * j.valMinAbs.natAbs)).2
  calc
    ‖x ^ (N + 1) - x‖ * (2 * j.valMinAbs.natAbs) ≤
        2 * (2 * j.valMinAbs.natAbs) := by gcongr
    _ = (4 * j.valMinAbs.natAbs / p) * p := by field_simp; ring
    _ ≤ ‖x - 1‖ * p := by gcongr
    _ = p * ‖x - 1‖ := by ring

private lemma sum_inv_valMinAbs_le (p : ℕ) [hp : Fact p.Prime] :
    (∑ j : ZMod p, if j = 0 then (0 : ℝ) else (j.valMinAbs.natAbs : ℝ)⁻¹) ≤
      2 * (harmonic (p / 2) : ℝ) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  let s : Finset (ZMod p) := Finset.univ.filter (· ≠ 0)
  let t : Finset ℕ := Finset.Icc 1 (p / 2)
  have hmap : ∀ j ∈ s, j.valMinAbs.natAbs ∈ t := by
    intro j hj
    have hj0 : j ≠ 0 := (Finset.mem_filter.mp hj).2
    have hpos : 1 ≤ j.valMinAbs.natAbs := (Nat.one_le_iff_ne_zero).2 <|
      Int.natAbs_ne_zero.mpr ((ZMod.valMinAbs_eq_zero j).not.mpr hj0)
    exact Finset.mem_Icc.mpr ⟨hpos, ZMod.natAbs_valMinAbs_le j⟩
  have hfiber (i : ℕ) :
      ((s.filter fun j => j.valMinAbs.natAbs = i).card : ℝ) ≤ 2 := by
    let u := s.filter fun j => j.valMinAbs.natAbs = i
    by_cases hu : u.Nonempty
    · obtain ⟨a, ha⟩ := hu
      have hsub : u ⊆ {a, -a} := by
        intro b hb
        have hda : a.valMinAbs.natAbs = i := (Finset.mem_filter.mp ha).2
        have hdb : b.valMinAbs.natAbs = i := (Finset.mem_filter.mp hb).2
        have hab : a.valMinAbs.natAbs = b.valMinAbs.natAbs := hda.trans hdb.symm
        rcases ZMod.natAbs_valMinAbs_eq_natAbs_valMinAbs.mp hab with h | h
        · simp [h]
        · simp [h]
      exact_mod_cast ((Finset.card_le_card hsub).trans Finset.card_le_two)
    · simp only [Finset.not_nonempty_iff_eq_empty] at hu
      simp [u, hu]
  calc
    (∑ j : ZMod p, if j = 0 then (0 : ℝ) else (j.valMinAbs.natAbs : ℝ)⁻¹) =
        ∑ j ∈ s, (j.valMinAbs.natAbs : ℝ)⁻¹ := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro j hj
          by_cases hj0 : j = 0 <;> simp [hj0]
    _ = ∑ i ∈ t, ∑ j ∈ s with j.valMinAbs.natAbs = i,
          (j.valMinAbs.natAbs : ℝ)⁻¹ := by
          symm
          exact Finset.sum_fiberwise_of_maps_to hmap _
    _ = ∑ i ∈ t, ((s.filter fun j => j.valMinAbs.natAbs = i).card : ℝ) * (i : ℝ)⁻¹ := by
          apply Finset.sum_congr rfl
          intro i hi
          have heq : ∀ j ∈ s.filter (fun j => j.valMinAbs.natAbs = i),
              (j.valMinAbs.natAbs : ℝ)⁻¹ = (i : ℝ)⁻¹ := by
            intro j hj
            rw [(Finset.mem_filter.mp hj).2]
          rw [Finset.sum_congr rfl heq, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ t, 2 * (i : ℝ)⁻¹ := by
          gcongr with i hi
          exact hfiber i
    _ = 2 * (harmonic (p / 2) : ℝ) := by
          rw [harmonic_eq_sum_Icc]
          simp only [t, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
          rw [Finset.mul_sum]

private lemma two_mul_sub_div_add_le_log {x : ℝ} (hx : 1 ≤ x) :
    2 * (x - 1) / (x + 1) ≤ Real.log x := by
  let g : ℝ → ℝ := fun y => 2 * (y - 1) / (y + 1)
  let f : ℝ → ℝ := Real.log - g
  have hfderivAt (y : ℝ) (hy : 0 < y) :
      HasDerivAt f (y⁻¹ - 4 / (y + 1) ^ 2) y := by
    have hy0 : y ≠ 0 := ne_of_gt hy
    have hy1 : y + 1 ≠ 0 := by linarith
    have hlog := Real.hasDerivAt_log hy0
    have hrat : HasDerivAt (fun z : ℝ => 2 * (z - 1) / (z + 1))
        (4 / (y + 1) ^ 2) y := by
      have hsub : HasDerivAt (fun z : ℝ => z - 1) 1 y :=
        (hasDerivAt_id y).sub_const 1
      have hadd : HasDerivAt (fun z : ℝ => z + 1) 1 y :=
        (hasDerivAt_id y).add_const 1
      have hmul : HasDerivAt (fun z : ℝ => 2 * (z - 1)) 2 y := by
        simpa [mul_comm] using hsub.mul_const (2 : ℝ)
      have hinv := hadd.inv hy1
      have hraw := hmul.mul hinv
      convert hraw using 1
      · subsingleton
      · subsingleton
      · funext z
        simp [div_eq_mul_inv]
      · dsimp
        field_simp [hy1]
        ring
    change HasDerivAt (Real.log - g) _ y
    exact hlog.sub (by simpa [g] using hrat)
  have hfcont : ContinuousOn f (Set.Ici 1) := by
    intro y hy
    have hy' : 1 ≤ y := hy
    exact (hfderivAt y (by linarith)).continuousAt.continuousWithinAt
  have hfdiff : DifferentiableOn ℝ f (interior (Set.Ici 1)) := by
    rw [interior_Ici]
    intro y hy
    exact (hfderivAt y (by exact hy.trans' zero_lt_one)).differentiableAt.differentiableWithinAt
  have hfderiv : ∀ y ∈ interior (Set.Ici (1 : ℝ)), 0 ≤ deriv f y := by
    rw [interior_Ici]
    intro y hy
    have hypos : 0 < y := zero_lt_one.trans hy
    rw [(hfderivAt y hypos).deriv]
    have heq : y⁻¹ - 4 / (y + 1) ^ 2 = (y - 1) ^ 2 / (y * (y + 1) ^ 2) := by
      field_simp [ne_of_gt hypos, (by linarith : y + 1 ≠ 0)]
      ring
    rw [heq]
    positivity
  have hmono : MonotoneOn f (Set.Ici 1) :=
    monotoneOn_of_deriv_nonneg (convex_Ici (1 : ℝ)) hfcont hfdiff hfderiv
  have hone : f 1 = 0 := by simp [f, g]
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  simpa [f, g] using this

private lemma harmonic_le_log_two_mul_add_one (m : ℕ) :
    (harmonic m : ℝ) ≤ Real.log (2 * m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [harmonic_succ]
      push_cast
      have hpos1 : (0 : ℝ) < 2 * m + 1 := by positivity
      have hpos3 : (0 : ℝ) < 2 * m + 3 := by positivity
      have hratio : (1 : ℝ) ≤ (2 * m + 3) / (2 * m + 1) := by
        apply (le_div_iff₀ hpos1).2
        linarith
      have hlog := two_mul_sub_div_add_le_log hratio
      have hinc : ((m + 1 : ℕ) : ℝ)⁻¹ ≤
          Real.log (2 * m + 3) - Real.log (2 * m + 1) := by
        rw [← Real.log_div (ne_of_gt hpos3) (ne_of_gt hpos1)]
        calc
          ((m + 1 : ℕ) : ℝ)⁻¹ =
              2 * ((2 * m + 3) / (2 * m + 1) - 1) /
                ((2 * m + 3) / (2 * m + 1) + 1) := by
                  push_cast
                  field_simp
                  ring
          _ ≤ _ := hlog
      push_cast at hinc
      ring_nf at hinc ih ⊢
      linarith

theorem charSum_norm_le_core (p : Nat) (hp : p.Prime) (chi : MulChar (ZMod p) Complex)
    (h : Not (chi = 1)) (N : Nat) :
    Norm.norm ((Finset.Icc 1 N).sum (fun n => chi (n : ZMod p))) <= Real.sqrt p * Real.log p := by
  letI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hp2 : p ≠ 2 := by
    intro hp2
    subst p
    apply h
    ext u
    have hu : u = 1 := Subsingleton.elim _ _
    subst u
    simp
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
  have hp_half : 2 * (p / 2) + 1 = p := by omega
  have hinv (n : ℕ) : chi (n : ZMod p) =
      (p : ℂ)⁻¹ * ∑ j : ZMod p,
        ZMod.stdAddChar (j * (n : ZMod p)) * ZMod.dft (⇑chi) j := by
    have hi := ZMod.invDFT_apply (ZMod.dft (⇑chi)) (n : ZMod p)
    rw [ZMod.dft.symm_apply_apply] at hi
    simpa [smul_eq_mul] using hi
  have hrewrite : (∑ n ∈ Finset.Icc 1 N, chi (n : ZMod p)) =
      (p : ℂ)⁻¹ * ∑ j : ZMod p,
        (∑ n ∈ Finset.Icc 1 N, ZMod.stdAddChar (j * (n : ZMod p))) *
          ZMod.dft (⇑chi) j := by
    simp_rw [hinv]
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_mul]
  rw [hrewrite, norm_mul]
  calc
    ‖(p : ℂ)⁻¹‖ * ‖∑ j : ZMod p,
        (∑ n ∈ Finset.Icc 1 N, ZMod.stdAddChar (j * (n : ZMod p))) *
          ZMod.dft (⇑chi) j‖ ≤
        ‖(p : ℂ)⁻¹‖ * ∑ j : ZMod p,
          ‖(∑ n ∈ Finset.Icc 1 N, ZMod.stdAddChar (j * (n : ZMod p))) *
            ZMod.dft (⇑chi) j‖ := by gcongr; exact norm_sum_le _ _
    _ ≤ ‖(p : ℂ)⁻¹‖ * ∑ j : ZMod p,
          ((p : ℝ) / 2 * Real.sqrt p) *
            (if j = 0 then 0 else (j.valMinAbs.natAbs : ℝ)⁻¹) := by
      gcongr with j
      by_cases hj : j = 0
      · subst j
        simp [ZMod.dft_apply, MulChar.sum_eq_zero_of_ne_one h]
      · rw [norm_mul]
        have ha := interval_addChar_norm_le p j hj N
        have hd := dft_char_norm p chi h j
        rw [if_neg hj]
        calc
          ‖∑ n ∈ Finset.Icc 1 N, ZMod.stdAddChar (j * (n : ZMod p))‖ *
              ‖ZMod.dft (⇑chi) j‖ ≤
              ((p : ℝ) / (2 * j.valMinAbs.natAbs)) * Real.sqrt p := by gcongr
          _ = ((p : ℝ) / 2 * Real.sqrt p) *
              (j.valMinAbs.natAbs : ℝ)⁻¹ := by field_simp
    _ ≤ ‖(p : ℂ)⁻¹‖ * (((p : ℝ) / 2 * Real.sqrt p) *
          (2 * (harmonic (p / 2) : ℝ))) := by
      gcongr
      rw [← Finset.mul_sum]
      gcongr
      exact sum_inv_valMinAbs_le p
    _ = Real.sqrt p * (harmonic (p / 2) : ℝ) := by
      rw [norm_inv, Complex.norm_natCast]
      have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
      field_simp
    _ ≤ Real.sqrt p * Real.log p := by
      gcongr
      calc
        (harmonic (p / 2) : ℝ) ≤ Real.log (2 * ((p / 2 : ℕ) : ℝ) + 1) :=
          harmonic_le_log_two_mul_add_one _
        _ = Real.log ((2 * (p / 2) + 1 : ℕ) : ℝ) := by push_cast; rfl
        _ = Real.log p := by rw [hp_half]

end TuringTask
