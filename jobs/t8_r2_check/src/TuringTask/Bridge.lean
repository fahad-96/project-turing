import Mathlib
import TuringTask.Criterion
import TuringTask.Trap

/-!
# From the circle to `Int.fract`

We transfer `WeylEquid` to statements about real-valued continuous functions evaluated at
fractional parts, and then to indicator functions of intervals.
-/

open Finset Filter Complex Polynomial MeasureTheory AddCircle

namespace TuringTask

noncomputable section

lemma vol_eq_haar : (volume : Measure (AddCircle (1:ℝ))) = (@haarAddCircle 1 factOneLtZero) := by
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  simp

lemma coe_intCast_circle (m : ℤ) : ((m : ℝ) : AddCircle (1:ℝ)) = 0 := by
  have h : ((m : ℝ)) = m • (1:ℝ) := by simp
  rw [h, AddCircle.coe_zsmul (1:ℝ), AddCircle.coe_period, smul_zero]

/-- The fractional part has the same image in the circle. -/
lemma coe_fract_circle (x : ℝ) :
    ((Int.fract x : ℝ) : AddCircle (1:ℝ)) = ((x : ℝ) : AddCircle (1:ℝ)) := by
  have h : Int.fract x = x - ((⌊x⌋ : ℤ) : ℝ) := rfl
  rw [h, AddCircle.coe_sub, coe_intCast_circle, sub_zero]

lemma integral_circle_eq (f : AddCircle (1:ℝ) → ℂ) :
    ∫ x, f x ∂(@haarAddCircle 1 factOneLtZero)
      = ∫ a in Set.Ioc (0:ℝ) 1, f (a : AddCircle (1:ℝ)) := by
  rw [← vol_eq_haar]
  have h := AddCircle.integral_preimage (1:ℝ) 0 f
  rw [zero_add] at h
  exact h.symm


/-- Averages of a continuous `1`-periodic real function along an equidistributed sequence. -/
theorem tendsto_avg_real (g : ℕ → ℝ) (hg : WeylEquid g) (f : ℝ → ℝ) (hf0 : f 0 = f 1)
    (hc : ContinuousOn f (Set.Icc 0 1)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (Int.fract (g n))) / N) atTop
      (nhds (∫ a in Set.Ioc (0:ℝ) 1, f a)) := by
  set F : C(AddCircle (1:ℝ), ℂ) := ⟨fun x => ((AddCircle.liftIco 1 0 f x : ℝ) : ℂ),
    Complex.continuous_ofReal.comp (AddCircle.liftIco_zero_continuous hf0 hc)⟩ with hF
  have h := hg F
  -- rewrite the avg
  have havg : ∀ N : ℕ, avg g F N = ((∑ n ∈ Finset.range N, f (Int.fract (g n))) / N : ℝ) := by
    intro N
    rw [avg]
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    show ((AddCircle.liftIco 1 0 f ((g n : ℝ) : AddCircle (1:ℝ)) : ℝ) : ℂ) = _
    rw [← coe_fract_circle (g n)]
    rw [AddCircle.liftIco_zero_coe_apply (by exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩)]
  have hint : ∫ x, F x ∂(@haarAddCircle 1 factOneLtZero) = ((∫ a in Set.Ioc (0:ℝ) 1, f a : ℝ) : ℂ) := by
    rw [integral_circle_eq]
    rw [← integral_complex_ofReal]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
    show ((AddCircle.liftIco 1 0 f ((x:ℝ) : AddCircle (1:ℝ)) : ℝ) : ℂ) = ((f x : ℝ) : ℂ)
    simp only [Set.mem_Ioc] at hx
    rcases eq_or_lt_of_le hx.2 with heq | hlt
    · -- x = 1, use periodicity
      rw [show ((x:ℝ) : AddCircle (1:ℝ)) = ((0:ℝ) : AddCircle (1:ℝ)) by
        rw [show (x:ℝ) = (0:ℝ) + 1 by linarith, AddCircle.coe_add_period]]
      rw [AddCircle.liftIco_zero_coe_apply (Set.mem_Ico.2 ⟨le_rfl, one_pos⟩)]
      rw [hf0, heq]
    · rw [AddCircle.liftIco_zero_coe_apply (by exact ⟨le_of_lt hx.1, hlt⟩)]
  rw [hint] at h
  simp only [funext havg] at h
  exact_mod_cast (Complex.continuous_re.continuousAt.tendsto.comp h)


def cnt (g : ℕ → ℝ) (a b : ℝ) (N : ℕ) : ℝ :=
  (((Finset.range N).filter (fun n : Nat =>
    a ≤ Int.fract (g n) ∧ Int.fract (g n) < b)).card : ℝ) / N

lemma cnt_eq (g : ℕ → ℝ) (a b : ℝ) (N : ℕ) :
    cnt g a b N = (∑ n ∈ Finset.range N,
      (if a ≤ Int.fract (g n) ∧ Int.fract (g n) < b then (1:ℝ) else 0)) / N := by
  rw [cnt]; congr 1
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]; simp

-- For fixed a b and d, eventually cnt is within [∫trap - ε, ∫outer + ε]
lemma sandwich (g : ℕ → ℝ) (hg : WeylEquid g) (d : ℝ) (hd : 0 < d) (ε : ℝ) (hε : 0 < ε)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    ∀ᶠ N in atTop, |cnt g a b N - (b - a)| < 4 * d + ε := by
  -- lower approximation
  have hlow : Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, trap d a b (Int.fract (g n))) / N)
      atTop (nhds (∫ x in Set.Ioc (0:ℝ) 1, trap d a b x)) := by
    apply tendsto_avg_real g hg
    · rw [trap_zero hd ha, trap_one hd hb]
    · exact (trap_continuous d a b hd).continuousOn
  have hhigh : Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, outer d a b (Int.fract (g n))) / N)
      atTop (nhds (∫ x in Set.Ioc (0:ℝ) 1, outer d a b x)) := by
    apply tendsto_avg_real g hg
    · exact outer_endpoints hd ha hab hb
    · exact (outer_continuous d a b hd).continuousOn
  rw [Metric.tendsto_atTop] at hlow hhigh
  obtain ⟨N1, hN1⟩ := hlow ε hε
  obtain ⟨N2, hN2⟩ := hhigh ε hε
  filter_upwards [eventually_ge_atTop (max (max N1 N2) 1)] with N hN
  have hNpos : 0 < N := lt_of_lt_of_le one_pos (le_trans (le_max_right _ 1) hN)
  have hNR : (0:ℝ) < N := by exact_mod_cast hNpos
  have h1 := hN1 N (le_trans (le_trans (le_max_left N1 N2) (le_max_left _ 1)) hN)
  have h2 := hN2 N (le_trans (le_trans (le_max_right N1 N2) (le_max_left _ 1)) hN)
  rw [Real.dist_eq] at h1 h2
  -- the counting function is sandwiched
  have hs1 : (∑ n ∈ Finset.range N, trap d a b (Int.fract (g n))) / N ≤ cnt g a b N := by
    rw [cnt_eq]
    apply div_le_div_of_nonneg_right _ hNR.le
    exact Finset.sum_le_sum fun n _ => trap_le_ind hd _
  have hs2 : cnt g a b N ≤ (∑ n ∈ Finset.range N, outer d a b (Int.fract (g n))) / N := by
    rw [cnt_eq]
    apply div_le_div_of_nonneg_right _ hNR.le
    exact Finset.sum_le_sum fun n _ => ind_le_outer hd hab _
  -- integrals
  have hint1 : b - a - 2 * d ≤ ∫ x in Set.Ioc (0:ℝ) 1, trap d a b x := by
    rw [← intervalIntegral.integral_of_le zero_le_one]
    exact trap_integral_ge hd ha hb
  have hint2 : (∫ x in Set.Ioc (0:ℝ) 1, outer d a b x) ≤ b - a + 4 * d := by
    rw [← intervalIntegral.integral_of_le zero_le_one]
    exact outer_integral_le hd ha hab hb
  rw [abs_lt]
  constructor
  · have := abs_lt.1 h1
    linarith [this.1, hs1, hint1]
  · have := abs_lt.1 h2
    linarith [this.2, hs2, hint2]


-- cnt g a b N = cnt g 0 b N - cnt g 0 a N
lemma cnt_sub (g : ℕ → ℝ) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (N : ℕ) :
    cnt g a b N = cnt g 0 b N - cnt g 0 a N := by
  rw [cnt_eq, cnt_eq, cnt_eq, ← sub_div]
  congr 1
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  have h0 : (0:ℝ) ≤ Int.fract (g n) := Int.fract_nonneg _
  by_cases h1 : Int.fract (g n) < a
  · rw [if_neg (by push_neg; intro h; linarith), if_pos ⟨h0, by linarith⟩,
      if_pos ⟨h0, h1⟩]
    ring
  · push_neg at h1
    by_cases h2 : Int.fract (g n) < b
    · rw [if_pos ⟨h1, h2⟩, if_pos ⟨h0, h2⟩, if_neg (by push_neg; intro _; linarith)]
      ring
    · push_neg at h2
      rw [if_neg (by push_neg; intro _; linarith), if_neg (by push_neg; intro _; linarith),
        if_neg (by push_neg; intro _; linarith)]
      ring

lemma cnt_mono (g : ℕ → ℝ) (N : ℕ) {c c' : ℝ} (h : c ≤ c') : cnt g 0 c N ≤ cnt g 0 c' N := by
  rw [cnt_eq, cnt_eq]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · apply div_le_div_of_nonneg_right _ (by exact_mod_cast Nat.zero_le N)
    refine Finset.sum_le_sum fun n _ => ?_
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exact absurd ⟨h1.1, lt_of_lt_of_le h1.2 h⟩ h2
    · norm_num
    · exact le_rfl


lemma cnt_tendsto (g : ℕ → ℝ) (hg : WeylEquid g) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    Tendsto (fun N => cnt g 0 c N) atTop (nhds c) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hd : 0 < ε/16 := by linarith
  have := sandwich g hg (ε/16) hd (ε/4) (by linarith) 0 c le_rfl hc0 hc1
  rw [eventually_atTop] at this
  obtain ⟨N0, hN0⟩ := this
  refine ⟨N0, fun N hN => ?_⟩
  have h := hN0 N hN
  rw [Real.dist_eq]
  simp only [sub_zero] at h
  linarith [h]

-- uniform: ∀ ε>0, ∃ N0, ∀ N ≥ N0, ∀ c ∈ [0,1], |cnt g 0 c N - c| < ε
lemma cnt_unif (g : ℕ → ℝ) (hg : WeylEquid g) (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N ≥ N0, ∀ c : ℝ, 0 ≤ c → c ≤ 1 → |cnt g 0 c N - c| < ε := by
  -- choose K with 1/K < ε/2
  obtain ⟨K, hK⟩ := exists_nat_gt (2/ε)
  have hKpos : 0 < K := by
    by_contra hc
    have h0 : K = 0 := by omega
    subst h0
    simp only [Nat.cast_zero] at hK
    nlinarith [div_pos (by norm_num : (0:ℝ) < 2) hε]
  have hKR : (0:ℝ) < K := by exact_mod_cast hKpos
  have hKe : 1/(K:ℝ) < ε/2 := by
    rw [div_lt_div_iff₀ hKR (by norm_num)]
    rw [div_lt_iff₀ hε] at hK
    nlinarith
  -- for each j ≤ K, cnt g 0 (j/K) N → j/K
  have hgrid : ∀ j : ℕ, j ≤ K → ∀ᶠ N in atTop, |cnt g 0 ((j:ℝ)/K) N - (j:ℝ)/K| < ε/4 := by
    intro j hj
    have h0 : (0:ℝ) ≤ (j:ℝ)/K := by positivity
    have h1 : (j:ℝ)/K ≤ 1 := by
      rw [div_le_one hKR]; exact_mod_cast hj
    have := cnt_tendsto g hg ((j:ℝ)/K) h0 h1
    rw [Metric.tendsto_atTop] at this
    obtain ⟨N0, hN0⟩ := this (ε/4) (by linarith)
    rw [eventually_atTop]
    exact ⟨N0, fun N hN => by rw [← Real.dist_eq]; exact hN0 N hN⟩
  have hall : ∀ᶠ N in atTop, ∀ j ∈ Finset.range (K+1),
      |cnt g 0 ((j:ℝ)/K) N - (j:ℝ)/K| < ε/4 :=
    (eventually_all_finset _).2 (fun j hj => hgrid j (by simpa [Nat.lt_succ_iff] using hj))
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hall
  refine ⟨N0, fun N hN c hc0 hc1 => ?_⟩
  -- find j with j/K ≤ c ≤ (j+1)/K
  set j : ℕ := ⌊c * K⌋₊ with hjdef
  have hjK : j ≤ K := by
    rw [hjdef]
    have : c * K ≤ K := by nlinarith
    have := Nat.floor_le_floor (R := ℝ) this
    simpa [Nat.floor_natCast] using this
  have hjle : (j:ℝ)/K ≤ c := by
    rw [div_le_iff₀ hKR]
    exact Nat.floor_le (by positivity)
  have hcle : c ≤ ((j:ℝ)+1)/K := by
    rw [le_div_iff₀ hKR]
    exact le_of_lt (Nat.lt_floor_add_one (c * K))
  -- the two grid estimates
  have hlo := hN0 N hN j (Finset.mem_range.2 (by omega))
  -- if j = K then c = 1 exactly
  rcases eq_or_lt_of_le hjK with heq | hlt
  · -- j = K, so c ≥ K/K = 1, hence c = 1
    have hc : c = 1 := by
      have : (K:ℝ)/K ≤ c := by rw [← heq] at hjle ⊢; exact hjle
      rw [div_self (ne_of_gt hKR)] at this
      linarith
    subst hc
    have h1 : ((j:ℝ))/K = 1 := by rw [heq]; exact div_self (ne_of_gt hKR)
    rw [h1] at hlo
    linarith [abs_lt.1 hlo, abs_lt.1 hlo]
  · -- j < K
    have hhi := hN0 N hN (j+1) (Finset.mem_range.2 (by omega))
    have hmono1 : cnt g 0 ((j:ℝ)/K) N ≤ cnt g 0 c N := cnt_mono g N hjle
    have hmono2 : cnt g 0 c N ≤ cnt g 0 (((j:ℝ)+1)/K) N := by
      have := cnt_mono g N hcle
      exact this
    have hcast : (((j+1 : ℕ)):ℝ)/K = ((j:ℝ)+1)/K := by push_cast; ring
    rw [hcast] at hhi
    have hdiff : ((j:ℝ)+1)/K - (j:ℝ)/K = 1/K := by field_simp; ring
    rw [abs_lt] at hlo hhi ⊢
    have hgap : (1:ℝ)/K < ε/2 := hKe
    constructor
    · linarith [hlo.1, hmono1, hjle, hcle, hdiff, hgap]
    · linarith [hhi.2, hmono2, hjle, hcle, hdiff, hgap]


/-- Uniform convergence of the proportions over all subintervals of `[0,1]`. -/
theorem cnt_unif_ab (g : ℕ → ℝ) (hg : WeylEquid g) (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N ≥ N0, ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
      |cnt g a b N - (b - a)| < ε := by
  obtain ⟨N0, hN0⟩ := cnt_unif g hg (ε/2) (by linarith)
  refine ⟨N0, fun N hN a b ha hab hb => ?_⟩
  rw [cnt_sub g a b ha hab]
  have h1 := hN0 N hN a ha (by linarith)
  have h2 := hN0 N hN b (by linarith) hb
  rw [abs_lt] at h1 h2 ⊢
  constructor
  · linarith [h1.2, h2.1]
  · linarith [h1.1, h2.2]

end

end TuringTask
