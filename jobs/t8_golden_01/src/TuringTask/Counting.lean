import Mathlib
import TuringTask.Circle

/-!
# From exponential sums to frequencies of fractional parts

`ind a b x` is the indicator of `a <= x < b` and `freqR u a b N` the proportion of `n < N` with
`a <= fract (u n) < b`.  Under the exponential-sum hypothesis on `u`:
* `freqR_lower`: eventually `freqR u a b N > b - a - eta` (a continuous minorant on the circle);
* `tendsto_freqR`: `freqR u a b N -> b - a` (lower bounds for the complementary intervals);
* `freqR_uniform`: the convergence is uniform in `0 <= a <= b <= 1`.
-/

open Finset Filter MeasureTheory AddCircle

namespace TuringTask

/-- Exponential-sum hypothesis on a real sequence. -/
def PhaseNull (u : ℕ → ℝ) : Prop :=
  ∀ k : ℤ, k ≠ 0 → Tendsto (fun N : ℕ => (∑ n ∈ range N, ephase (k * u n)) / N) atTop (nhds 0)

/-- Indicator of `a <= x < b`. -/
noncomputable def ind (a b x : ℝ) : ℝ := if a ≤ x ∧ x < b then 1 else 0

/-- Proportion of `n < N` with `a <= fract (u n) < b`. -/
noncomputable def freqR (u : ℕ → ℝ) (a b : ℝ) (N : ℕ) : ℝ :=
  (∑ n ∈ range N, ind a b (Int.fract (u n))) / N

lemma card_div_eq_freqR (u : ℕ → ℝ) (a b : ℝ) (N : ℕ) :
    (((range N).filter (fun n => a ≤ Int.fract (u n) ∧ Int.fract (u n) < b)).card : ℝ) / N
      = freqR u a b N := by
  rw [freqR, Finset.natCast_card_filter]
  rfl

lemma ind_nonneg (a b x : ℝ) : 0 ≤ ind a b x := by
  unfold ind
  split_ifs <;> norm_num

lemma freqR_nonneg (u : ℕ → ℝ) (a b : ℝ) (N : ℕ) : 0 ≤ freqR u a b N :=
  div_nonneg (Finset.sum_nonneg fun _ _ => ind_nonneg _ _ _) (Nat.cast_nonneg _)

/-- Real-valued continuous test functions. -/
theorem tendsto_avg_circle_real (u : ℕ → ℝ) (hu : PhaseNull u) (g : C(AddCircle (1 : ℝ), ℝ)) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, g (u n)) / N) atTop
      (nhds (∫ t, g t ∂(haarAddCircle (T := (1 : ℝ))))) := by
  let F : C(AddCircle (1 : ℝ), ℂ) := ⟨fun t => (g t : ℂ), by fun_prop⟩
  have h := (Complex.continuous_re.tendsto _).comp (tendsto_avg_circle u hu F)
  have e1 : (∫ t, F t ∂(haarAddCircle (T := (1 : ℝ)))).re
      = ∫ t, g t ∂(haarAddCircle (T := (1 : ℝ))) := by
    change (∫ t, ((g t : ℝ) : ℂ) ∂(haarAddCircle (T := (1 : ℝ)))).re = _
    rw [integral_complex_ofReal, Complex.ofReal_re]
  rw [e1] at h
  refine h.congr fun N => ?_
  simp only [Function.comp_apply]
  rw [Complex.div_natCast_re, Complex.re_sum]
  rfl

/-- A continuous bump on the circle: `1` near `c`, `0` at distance `>= r` from `c`. -/
noncomputable def bump (c r δ : ℝ) : C(AddCircle (1 : ℝ), ℝ) :=
  ⟨fun z => max 0 (min 1 ((r - dist z (c : AddCircle (1 : ℝ))) / δ)), by fun_prop⟩

lemma bump_apply (c r δ : ℝ) (z : AddCircle (1 : ℝ)) :
    bump c r δ z = max 0 (min 1 ((r - dist z (c : AddCircle (1 : ℝ))) / δ)) := rfl

lemma bump_nonneg (c r δ : ℝ) (z : AddCircle (1 : ℝ)) : 0 ≤ bump c r δ z := by
  rw [bump_apply]
  exact le_max_left _ _

lemma bump_le_one (c r δ : ℝ) (z : AddCircle (1 : ℝ)) : bump c r δ z ≤ 1 := by
  rw [bump_apply]
  exact max_le zero_le_one (min_le_left _ _)

lemma dist_lt_of_bump_pos (c r δ : ℝ) (hδ : 0 < δ) (z : AddCircle (1 : ℝ))
    (h : 0 < bump c r δ z) : dist z (c : AddCircle (1 : ℝ)) < r := by
  by_contra hcon
  push Not at hcon
  have : (r - dist z (c : AddCircle (1 : ℝ))) / δ ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
  rw [bump_apply] at h
  have : min 1 ((r - dist z (c : AddCircle (1 : ℝ))) / δ) ≤ 0 := (min_le_right _ _).trans this
  have : max 0 (min 1 ((r - dist z (c : AddCircle (1 : ℝ))) / δ)) = 0 := max_eq_left this
  linarith

lemma bump_eq_one (c r δ : ℝ) (hδ : 0 < δ) (z : AddCircle (1 : ℝ))
    (h : dist z (c : AddCircle (1 : ℝ)) ≤ r - δ) : bump c r δ z = 1 := by
  rw [bump_apply]
  have : 1 ≤ (r - dist z (c : AddCircle (1 : ℝ))) / δ := by
    rw [le_div_iff₀ hδ]
    linarith
  rw [min_eq_left this, max_eq_right zero_le_one]

/-- A point of the circle within distance `r` of `c`, where `[c - r, c + r]` lies in `[0, 1]`,
has its fractional part in `(c - r, c + r)`. -/
lemma fract_mem_of_dist_lt (c r s : ℝ) (h0 : 0 ≤ c - r) (h1 : c + r ≤ 1)
    (h : dist (s : AddCircle (1 : ℝ)) (c : AddCircle (1 : ℝ)) < r) :
    c - r < Int.fract s ∧ Int.fract s < c + r := by
  rw [dist_eq_norm, ← AddCircle.coe_sub, AddCircle.norm_eq] at h
  simp only [inv_one, one_mul, mul_one] at h
  set k := round (s - c)
  have hf : Int.fract s = s - k := by
    rw [Int.fract_eq_iff]
    refine ⟨?_, ?_, k, by ring⟩
    · have := (abs_lt.mp h).1
      linarith
    · have := (abs_lt.mp h).2
      linarith
  rw [hf]
  have := abs_lt.mp h
  constructor <;> linarith

lemma bump_le_ind (a b δ : ℝ) (hδ : 0 < δ) (ha : 0 ≤ a) (hb : b ≤ 1) (s : ℝ) :
    bump ((a + b) / 2) ((b - a) / 2) δ s ≤ ind a b (Int.fract s) := by
  rcases (bump_nonneg ((a + b) / 2) ((b - a) / 2) δ s).eq_or_lt with h | h
  · rw [← h]
    exact ind_nonneg _ _ _
  · have hd := dist_lt_of_bump_pos _ _ δ hδ _ h
    have hm := fract_mem_of_dist_lt ((a + b) / 2) ((b - a) / 2) s (by linarith) (by linarith) hd
    have : ind a b (Int.fract s) = 1 := by
      unfold ind
      rw [if_pos]
      constructor <;> linarith [hm.1, hm.2]
    rw [this]
    exact bump_le_one _ _ _ _

lemma integrable_haar_real (g : C(AddCircle (1 : ℝ), ℝ)) :
    Integrable g (haarAddCircle (T := (1 : ℝ))) :=
  g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma haar_eq_volume_one :
    (haarAddCircle (T := (1 : ℝ))) = (volume : Measure (AddCircle (1 : ℝ))) := by
  rw [volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]

lemma integral_bump_ge (c r δ : ℝ) (hδ : 0 < δ) (hrδ : δ ≤ r) (hr : 2 * r ≤ 1) :
    2 * (r - δ) ≤ ∫ t, bump c r δ t ∂(haarAddCircle (T := (1 : ℝ))) := by
  set B := Metric.closedBall (c : AddCircle (1 : ℝ)) (r - δ)
  have hB : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  have hle : ∀ t, B.indicator (fun _ => (1 : ℝ)) t ≤ bump c r δ t := by
    intro t
    by_cases ht : t ∈ B
    · rw [Set.indicator_of_mem ht, bump_eq_one c r δ hδ t (Metric.mem_closedBall.mp ht)]
    · rw [Set.indicator_of_notMem ht]
      exact bump_nonneg _ _ _ _
  have hint := integral_mono ((integrable_const (1 : ℝ)).indicator hB)
    (integrable_haar_real (bump c r δ)) hle
  have hm : (haarAddCircle (T := (1 : ℝ))) B = ENNReal.ofReal (min 1 (2 * (r - δ))) := by
    rw [haar_eq_volume_one]
    exact volume_closedBall (T := (1 : ℝ)) _
  rw [integral_indicator_const (1 : ℝ) hB, smul_eq_mul, mul_one, measureReal_def, hm,
    ENNReal.toReal_ofReal (by positivity)] at hint
  rwa [min_eq_right (by linarith)] at hint

/-- Lower bound for the frequencies. -/
lemma freqR_lower (u : ℕ → ℝ) (hu : PhaseNull u) (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, b - a - η < freqR u a b N := by
  rcases lt_or_ge (b - a) η with hsmall | hbig
  · exact Eventually.of_forall fun N => by linarith [freqR_nonneg u a b N]
  set g := bump ((a + b) / 2) ((b - a) / 2) (η / 4)
  have hgint := integral_bump_ge ((a + b) / 2) ((b - a) / 2) (η / 4) (by positivity)
    (by linarith) (by linarith)
  have hlim := tendsto_avg_circle_real u hu g
  have hev := (Metric.tendsto_nhds.mp hlim) (η / 2) (by positivity)
  filter_upwards [hev] with N hN
  rw [Real.dist_eq] at hN
  have hcmp : (∑ n ∈ range N, g (u n)) / N ≤ freqR u a b N := by
    unfold freqR
    gcongr with n hn
    exact bump_le_ind a b (η / 4) (by positivity) ha hb (u n)
  have := (abs_lt.mp hN).1
  linarith

lemma ind_split (a b x : ℝ) (hab : a ≤ b) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ind 0 a x + ind a b x + ind b 1 x = 1 := by
  unfold ind
  by_cases h1 : x < a
  · rw [if_pos ⟨hx0, h1⟩, if_neg (by intro h; linarith [h.1]), if_neg (by intro h; linarith [h.1])]
    norm_num
  · push Not at h1
    by_cases h2 : x < b
    · rw [if_neg (by intro h; linarith [h.2]), if_pos ⟨h1, h2⟩,
        if_neg (by intro h; linarith [h.1])]
      norm_num
    · push Not at h2
      rw [if_neg (by intro h; linarith [h.2]), if_neg (by intro h; linarith [h.2]),
        if_pos ⟨h2, hx1⟩]
      norm_num

lemma freqR_split (u : ℕ → ℝ) (a b : ℝ) (hab : a ≤ b) (N : ℕ)
    (hN : 1 ≤ N) : freqR u 0 a N + freqR u a b N + freqR u b 1 N = 1 := by
  unfold freqR
  rw [← add_div, ← add_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have : ∀ n ∈ range N, ind 0 a (Int.fract (u n)) + ind a b (Int.fract (u n))
      + ind b 1 (Int.fract (u n)) = 1 := fun n _ =>
    ind_split a b _ hab (Int.fract_nonneg _) (Int.fract_lt_one _)
  rw [Finset.sum_congr rfl this]
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  simp [hN']

/-- Convergence of the frequencies for one interval. -/
theorem tendsto_freqR (u : ℕ → ℝ) (hu : PhaseNull u) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ 1) : Tendsto (fun N : ℕ => freqR u a b N) atTop (nhds (b - a)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have h1 := freqR_lower u hu a b ha hb (ε / 3) (by positivity)
  have h2 := freqR_lower u hu 0 a le_rfl (hab.trans hb) (ε / 3) (by positivity)
  have h3 := freqR_lower u hu b 1 (ha.trans hab) le_rfl (ε / 3) (by positivity)
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp
    (h1.and (h2.and (h3.and (eventually_ge_atTop 1))))
  refine ⟨N0, fun N hN => ?_⟩
  obtain ⟨k1, k2, k3, k4⟩ := hN0 N hN
  have hs := freqR_split u a b hab N k4
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

lemma freqR_mono (u : ℕ → ℝ) (s t : ℝ) (hst : s ≤ t) (N : ℕ) :
    freqR u 0 s N ≤ freqR u 0 t N := by
  unfold freqR
  gcongr with n hn
  unfold ind
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd ⟨h1.1, lt_of_lt_of_le h1.2 hst⟩ h2
  · norm_num
  · exact le_rfl

lemma freqR_sub (u : ℕ → ℝ) (a b : ℝ) (hab : a ≤ b) (N : ℕ) :
    freqR u a b N = freqR u 0 b N - freqR u 0 a N := by
  unfold freqR
  rw [← sub_div]
  rw [← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun n _ => ?_)
  unfold ind
  by_cases h1 : 0 ≤ Int.fract (u n)
  · by_cases h2 : Int.fract (u n) < a
    · rw [if_neg (by intro h; linarith [h.1]), if_pos ⟨h1, lt_of_lt_of_le h2 hab⟩,
        if_pos ⟨h1, h2⟩]
      norm_num
    · push Not at h2
      by_cases h3 : Int.fract (u n) < b
      · rw [if_pos ⟨h2, h3⟩, if_pos ⟨h1, h3⟩, if_neg (by intro h; linarith [h.2])]
        norm_num
      · rw [if_neg (by intro h; exact h3 h.2), if_neg (by intro h; exact h3 h.2),
          if_neg (by intro h; linarith [h.2])]
        norm_num
  · exact absurd (Int.fract_nonneg _) h1

/-- Uniform convergence of the frequencies over all intervals `[a, b)` in `[0, 1]`. -/
theorem freqR_uniform (u : ℕ → ℝ) (hu : PhaseNull u) (ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N, N0 ≤ N → ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
      |freqR u a b N - (b - a)| < ε := by
  obtain ⟨M, hM⟩ := exists_nat_gt (4 / ε)
  have hMpos : (0 : ℝ) < M := lt_trans (by positivity) hM
  have hM1 : 1 / (M : ℝ) < ε / 4 := by
    rw [div_lt_iff₀ hMpos]
    rw [div_lt_iff₀ hε] at hM
    linarith
  have hev : ∀ᶠ N : ℕ in atTop, ∀ j ∈ range (M + 1),
      |freqR u 0 ((j : ℝ) / M) N - (j : ℝ) / M| < ε / 4 := by
    rw [Filter.eventually_all_finset]
    intro j hj
    have hj' : (j : ℝ) ≤ M := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hle : (j : ℝ) / M ≤ 1 := (div_le_one hMpos).mpr hj'
    have := tendsto_freqR u hu 0 ((j : ℝ) / M) le_rfl (by positivity) hle
    rw [sub_zero] at this
    filter_upwards [(Metric.tendsto_nhds.mp this) (ε / 4) (by positivity)] with N hN
    rwa [Real.dist_eq] at hN
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp hev
  refine ⟨N0, fun N hN => ?_⟩
  have hgrid := hN0 N hN
  -- uniform bound for `[0, t)`
  have hone : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → |freqR u 0 t N - t| < ε / 2 := by
    intro t ht0 ht1
    set j := ⌊t * M⌋₊ with hj
    have hjle : (j : ℝ) ≤ t * M := Nat.floor_le (by positivity)
    have hjlt : t * M < j + 1 := Nat.lt_floor_add_one _
    have hjM : j ≤ M := by
      have : (j : ℝ) ≤ M := hjle.trans (by nlinarith)
      exact_mod_cast this
    have htj : (j : ℝ) / M ≤ t := by rw [div_le_iff₀ hMpos]; linarith
    have htj' : t - 1 / M < (j : ℝ) / M := by
      rw [sub_lt_iff_lt_add, ← add_div, lt_div_iff₀ hMpos]
      linarith
    have lowj := hgrid j (Finset.mem_range.mpr (by omega))
    have lower : t - ε / 2 < freqR u 0 t N := by
      have := freqR_mono u _ _ htj N
      have := (abs_lt.mp lowj).1
      linarith
    set j' := min (j + 1) M with hj'
    have hj'M : j' ≤ M := min_le_right _ _
    have ht_le : t ≤ (j' : ℝ) / M := by
      rw [le_div_iff₀ hMpos]
      rcases le_total (j + 1) M with h | h
      · rw [hj', min_eq_left h]
        push_cast
        linarith
      · rw [hj', min_eq_right h]
        nlinarith
    have hj'_le : (j' : ℝ) / M ≤ t + 1 / M := by
      have : (j' : ℝ) ≤ j + 1 := by exact_mod_cast min_le_left _ _
      rw [div_le_iff₀ hMpos, add_mul, div_mul_cancel₀ _ hMpos.ne']
      linarith
    have upj := hgrid j' (Finset.mem_range.mpr (by omega))
    have upper : freqR u 0 t N < t + ε / 2 := by
      have := freqR_mono u _ _ ht_le N
      have := (abs_lt.mp upj).2
      linarith
    rw [abs_lt]
    constructor <;> linarith
  intro a b ha hab hb
  rw [freqR_sub u a b hab N]
  have h1 := abs_lt.mp (hone b (ha.trans hab) hb)
  have h2 := abs_lt.mp (hone a ha (hab.trans hb))
  rw [abs_lt]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

end TuringTask
