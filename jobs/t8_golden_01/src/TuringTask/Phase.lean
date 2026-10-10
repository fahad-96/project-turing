import Mathlib

/-!
# Unit phases and a differencing inequality for averages

`ephase t = exp(2 pi i t)`.  The main result `tendsto_avg_zero_of_corr` says: if a sequence
`z` of complex numbers of modulus at most one has vanishing averaged correlations
`(1/N) sum_(n<N) z(n+r) conj(z n)` for every shift `r >= 1`, then its own averages tend to zero.
-/

open Finset Filter

namespace TuringTask

/-- The phase `exp(2 pi i t)` of a real number `t`. -/
noncomputable def ephase (t : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)

lemma norm_ephase (t : ℝ) : ‖ephase t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

lemma ephase_mul_conj (s t : ℝ) :
    ephase s * (starRingEnd ℂ) (ephase t) = ephase (s - t) := by
  unfold ephase
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

lemma ephase_add (s t : ℝ) : ephase (s + t) = ephase s * ephase t := by
  unfold ephase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma ephase_nat_mul (n : ℕ) (t : ℝ) : ephase (n * t) = ephase t ^ n := by
  unfold ephase
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma ephase_re (t : ℝ) : (ephase t).re = Real.cos (2 * Real.pi * t) :=
  Complex.exp_ofReal_mul_I_re _

/-- Shifting the summation window by `k` changes a sum of terms of modulus at most one by
at most `2 k`. -/
lemma norm_sum_shift_sub_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (N k : ℕ) :
    ‖∑ n ∈ range N, f (n + k) - ∑ n ∈ range N, f n‖ ≤ 2 * k := by
  have h1 := Finset.sum_range_add f k N
  have h2 := Finset.sum_range_add f N k
  have e : ∑ n ∈ range N, f (n + k) - ∑ n ∈ range N, f n =
      ∑ n ∈ range k, f (N + n) - ∑ n ∈ range k, f n := by
    have h3 : ∑ n ∈ range N, f (n + k) = ∑ n ∈ range N, f (k + n) := by
      refine Finset.sum_congr rfl (fun n _ => ?_)
      rw [add_comm]
    rw [h3]
    rw [add_comm k N] at h1
    linear_combination h2 - h1
  rw [e]
  have b1 : ‖∑ n ∈ range k, f (N + n)‖ ≤ k := by
    refine (norm_sum_le _ _).trans ?_
    simpa using Finset.sum_le_sum fun n (_ : n ∈ range k) => hf (N + n)
  have b2 : ‖∑ n ∈ range k, f n‖ ≤ k := by
    refine (norm_sum_le _ _).trans ?_
    simpa using Finset.sum_le_sum fun n (_ : n ∈ range k) => hf n
  linarith [norm_sub_le (∑ n ∈ range k, f (N + n)) (∑ n ∈ range k, f n)]

/-- Averaging over a window of length `H`: `H * sum_(n<N) z n` differs from
`sum_(n<N) sum_(h<H) z (n + h)` by at most `2 H^2`. -/
lemma norm_window_sub_le (z : ℕ → ℂ) (hz : ∀ n, ‖z n‖ ≤ 1) (N H : ℕ) :
    ‖(H : ℂ) * ∑ n ∈ range N, z n - ∑ n ∈ range N, ∑ h ∈ range H, z (n + h)‖
      ≤ 2 * H * H := by
  rw [Finset.sum_comm]
  have e : (H : ℂ) * ∑ n ∈ range N, z n = ∑ h ∈ range H, ∑ n ∈ range N, z n := by
    simp
  rw [e, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  have hb : ∀ h ∈ range H,
      ‖∑ n ∈ range N, z n - ∑ n ∈ range N, z (n + h)‖ ≤ 2 * (H : ℝ) := by
    intro h hh
    rw [norm_sub_rev]
    refine (norm_sum_shift_sub_le z hz N h).trans ?_
    have : (h : ℝ) ≤ H := by exact_mod_cast (Finset.mem_range.mp hh).le
    linarith
  refine (Finset.sum_le_sum hb).trans ?_
  simp only [Finset.card_range, Finset.sum_const, nsmul_eq_mul]
  linarith

/-- The correlation sum `sum_(n<N) z(n+h) conj(z(n+k))` with two shifts. -/
noncomputable def corr2 (z : ℕ → ℂ) (N h k : ℕ) : ℂ :=
  ∑ n ∈ range N, z (n + h) * (starRingEnd ℂ) (z (n + k))

lemma corr2_swap (z : ℕ → ℂ) (N h k : ℕ) :
    corr2 z N h k = (starRingEnd ℂ) (corr2 z N k h) := by
  unfold corr2
  rw [map_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [map_mul, Complex.conj_conj, mul_comm]

lemma norm_corr2_le_of_le (z : ℕ → ℂ) (hz : ∀ n, ‖z n‖ ≤ 1) (N h k : ℕ) (hkh : k ≤ h) :
    ‖corr2 z N h k‖ ≤ ‖corr2 z N (h - k) 0‖ + 2 * k := by
  set f : ℕ → ℂ := fun m => z (m + (h - k)) * (starRingEnd ℂ) (z m) with hf
  have hf1 : ∀ m, ‖f m‖ ≤ 1 := by
    intro m
    simp only [hf, norm_mul, Complex.norm_conj]
    exact mul_le_one₀ (hz _) (norm_nonneg _) (hz _)
  have e1 : corr2 z N h k = ∑ n ∈ range N, f (n + k) := by
    unfold corr2
    refine Finset.sum_congr rfl (fun n _ => ?_)
    simp only [hf]
    congr 2
    omega
  have e2 : corr2 z N (h - k) 0 = ∑ n ∈ range N, f n := by
    unfold corr2
    simp [hf]
  have := norm_sum_shift_sub_le f hf1 N k
  rw [← e1, ← e2] at this
  linarith [norm_le_norm_add_norm_sub' (corr2 z N h k) (corr2 z N (h - k) 0)]

lemma norm_corr2_self_le (z : ℕ → ℂ) (hz : ∀ n, ‖z n‖ ≤ 1) (N h : ℕ) :
    ‖corr2 z N h h‖ ≤ N := by
  unfold corr2
  refine (norm_sum_le _ _).trans ?_
  have : ∀ n ∈ range N, ‖z (n + h) * (starRingEnd ℂ) (z (n + h))‖ ≤ 1 := by
    intro n _
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_one₀ (hz _) (norm_nonneg _) (hz _)
  simpa using Finset.sum_le_sum this

/-- Expansion of `sum_(n<N) |sum_(h<H) z(n+h)|^2` into correlation sums. -/
lemma sum_norm_sq_window (z : ℕ → ℂ) (N H : ℕ) :
    ((∑ n ∈ range N, ‖∑ h ∈ range H, z (n + h)‖ ^ 2 : ℝ) : ℂ)
      = ∑ h ∈ range H, ∑ k ∈ range H, corr2 z N h k := by
  push_cast
  have e : ∀ n, ((‖∑ h ∈ range H, z (n + h)‖ : ℂ)) ^ 2
      = ∑ h ∈ range H, ∑ k ∈ range H, z (n + h) * (starRingEnd ℂ) (z (n + k)) := by
    intro n
    rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
  simp_rw [e]
  unfold corr2
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.sum_comm]

/-- The finite differencing inequality.  Let `S = sum_(n<N) z n` and
`W = sum_(n<N) |sum_(h<H) z (n + h)|`.  If `|corr2 z N r 0| <= c` for `1 <= r < H`, then
`W^2 <= N (H N + H^2 (c + 2 H))` and `H |S| <= W + 2 H^2`. -/
lemma norm_sum_le_of_corr (z : ℕ → ℂ) (hz : ∀ n, ‖z n‖ ≤ 1) (N H : ℕ) (c : ℝ) (hc0 : 0 ≤ c)
    (hc : ∀ r, 1 ≤ r → r < H → ‖corr2 z N r 0‖ ≤ c) :
    ∃ W : ℝ, 0 ≤ W ∧ W ^ 2 ≤ N * (H * N + H * H * (c + 2 * H)) ∧
      H * ‖∑ n ∈ range N, z n‖ ≤ W + 2 * H * H := by
  set w : ℕ → ℂ := fun n => ∑ h ∈ range H, z (n + h) with hw
  refine ⟨∑ n ∈ range N, ‖w n‖, Finset.sum_nonneg fun _ _ => norm_nonneg _, ?_, ?_⟩
  · have cs := sq_sum_le_card_mul_sum_sq (s := range N) (f := fun n => ‖w n‖)
    rw [Finset.card_range] at cs
    refine cs.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
    have e := sum_norm_sq_window z N H
    have hre : (∑ n ∈ range N, ‖w n‖ ^ 2 : ℝ)
        = ‖∑ h ∈ range H, ∑ k ∈ range H, corr2 z N h k‖ := by
      rw [← e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
      exact Finset.sum_nonneg fun _ _ => sq_nonneg _
    rw [hre]
    refine (norm_sum_le _ _).trans ?_
    have hrow : ∀ h ∈ range H, ‖∑ k ∈ range H, corr2 z N h k‖ ≤ N + H * (c + 2 * H) := by
      intro h hh
      have hh' := Finset.mem_range.mp hh
      refine (norm_sum_le _ _).trans ?_
      have hent : ∀ k ∈ range H,
          ‖corr2 z N h k‖ ≤ (if k = h then (N : ℝ) else 0) + (c + 2 * H) := by
        intro k hk
        have hk' := Finset.mem_range.mp hk
        rcases lt_trichotomy k h with hlt | heq | hgt
        · rw [if_neg hlt.ne]
          have := norm_corr2_le_of_le z hz N h k hlt.le
          have := hc (h - k) (by omega) (by omega)
          have : (k : ℝ) ≤ H := by exact_mod_cast hk'.le
          linarith
        · subst heq
          rw [if_pos rfl]
          have := norm_corr2_self_le z hz N k
          have : (0 : ℝ) ≤ H := Nat.cast_nonneg _
          linarith [hc0]
        · rw [if_neg hgt.ne', corr2_swap, Complex.norm_conj]
          have := norm_corr2_le_of_le z hz N k h hgt.le
          have := hc (k - h) (by omega) (by omega)
          have : (h : ℝ) ≤ H := by exact_mod_cast hh'.le
          linarith
      refine (Finset.sum_le_sum hent).trans ?_
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq' (range H) h, if_pos hh]
      simp only [Finset.card_range, Finset.sum_const, nsmul_eq_mul]
      exact le_of_eq (by ring)
    refine (Finset.sum_le_sum hrow).trans ?_
    simp only [Finset.card_range, Finset.sum_const, nsmul_eq_mul]
    nlinarith [Nat.cast_nonneg (α := ℝ) H, Nat.cast_nonneg (α := ℝ) N]
  · have h1 := norm_window_sub_le z hz N H
    have h2 : ‖∑ n ∈ range N, w n‖ ≤ ∑ n ∈ range N, ‖w n‖ := norm_sum_le _ _
    have h3 : ‖(H : ℂ) * ∑ n ∈ range N, z n‖ = H * ‖∑ n ∈ range N, z n‖ := by
      rw [norm_mul, Complex.norm_natCast]
    have := norm_le_norm_add_norm_sub' ((H : ℂ) * ∑ n ∈ range N, z n) (∑ n ∈ range N, w n)
    simp only [hw] at h2 this
    linarith

/-- Differencing: if every shifted correlation of `z` has averages tending to zero, then the
averages of `z` tend to zero. -/
theorem tendsto_avg_zero_of_corr (z : ℕ → ℂ) (hz : ∀ n, ‖z n‖ ≤ 1)
    (hc : ∀ r : ℕ, 1 ≤ r →
      Tendsto (fun N : ℕ => (∑ n ∈ range N, z (n + r) * (starRingEnd ℂ) (z n)) / N)
        atTop (nhds 0)) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, z n) / N) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨H, hH⟩ := exists_nat_gt (16 / ε ^ 2)
  have hHpos : (0 : ℝ) < H := lt_trans (by positivity) hH
  have hH1 : 1 ≤ H := by exact_mod_cast hHpos
  have hδ : (0 : ℝ) < 1 / H := by positivity
  have hev : ∀ᶠ N : ℕ in atTop, ∀ r ∈ Finset.Ico 1 H,
      ‖(∑ n ∈ range N, z (n + r) * (starRingEnd ℂ) (z n)) / N‖ < 1 / H := by
    rw [Filter.eventually_all_finset]
    intro r hr
    have := (hc r (Finset.mem_Ico.mp hr).1)
    exact (Metric.tendsto_nhds.mp this) _ hδ |>.mono fun N hN => by simpa using hN
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨N2, hN2⟩ := exists_nat_gt (2 * (H : ℝ) * H + 4 * H / ε)
  refine ⟨max N1 N2, fun N hN => ?_⟩
  have hNN1 : N1 ≤ N := le_of_max_le_left hN
  have hNN2 : (N2 : ℝ) ≤ N := by exact_mod_cast le_of_max_le_right hN
  have hNpos : (0 : ℝ) < N := by
    have : (0 : ℝ) ≤ 2 * (H : ℝ) * H + 4 * H / ε := by positivity
    linarith
  have hcorr : ∀ r, 1 ≤ r → r < H → ‖corr2 z N r 0‖ ≤ N / H := by
    intro r hr1 hr2
    have := hN1 N hNN1 r (Finset.mem_Ico.mpr ⟨hr1, hr2⟩)
    rw [norm_div, Complex.norm_natCast, div_lt_iff₀ hNpos] at this
    unfold corr2
    simp only [add_zero]
    rw [div_eq_mul_one_div (N : ℝ)]
    linarith
  obtain ⟨W, hW0, hW2, hS⟩ := norm_sum_le_of_corr z hz N H (N / H) (by positivity) hcorr
  rw [dist_zero_right, norm_div, Complex.norm_natCast, div_lt_iff₀ hNpos]
  -- bound `W`
  have hHN : 2 * (H : ℝ) * H ≤ N := by
    have : (0 : ℝ) ≤ 4 * H / ε := by positivity
    linarith
  have hW2' : W ^ 2 ≤ 3 * H * N ^ 2 := by
    refine hW2.trans ?_
    have e : (H : ℝ) * H * (N / H + 2 * H) = H * N + 2 * H * H * H := by
      field_simp
    rw [e]
    have := mul_le_mul_of_nonneg_left hHN (by positivity : (0 : ℝ) ≤ H * N)
    nlinarith
  have hεH : 12 < ε ^ 2 * H := by
    have := (div_lt_iff₀ (by positivity : (0 : ℝ) < ε ^ 2)).mp hH
    linarith
  have hWlt : W < ε * H * N / 2 := by
    by_contra hcon
    push Not at hcon
    have h0 : 0 ≤ ε * H * N / 2 := by positivity
    have := pow_le_pow_left₀ h0 hcon 2
    have key : 12 * (H * N ^ 2 / 4) < ε ^ 2 * H * (H * N ^ 2 / 4) :=
      mul_lt_mul_of_pos_right hεH (by positivity)
    nlinarith
  have hHlt : 2 * (H : ℝ) * H < ε * H * N / 2 := by
    have h4 : 4 * (H : ℝ) / ε < N := by linarith [show (0 : ℝ) ≤ 2 * H * H by positivity]
    rw [div_lt_iff₀ hε] at h4
    nlinarith
  have : (H : ℝ) * ‖∑ n ∈ range N, z n‖ < H * (ε * N) := by linarith
  have := lt_of_mul_lt_mul_left this hHpos.le
  linarith

end TuringTask
