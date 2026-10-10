import Mathlib
import TuringTask.Weyl

/-!
# Weyl's equidistribution theorem

We prove: if `P : ℝ[X]` has `natDegree ≤ d` and the coefficient of `X^d` is irrational
(with `d ≥ 1`), then the Weyl sums `(1/N) ∑_{n<N} e (P(n))` tend to `0`.

The proof is by induction on `d` using van der Corput's inequality.
-/

open Finset Filter Complex Polynomial

namespace TuringTask

noncomputable section

/-- The normalized Weyl sum associated to a real sequence `g`. -/
def weylAvg (g : ℕ → ℝ) (N : ℕ) : ℂ := (∑ n ∈ Finset.range N, e (g n)) / N

/-- The property that the Weyl sums of the sequence `g` tend to zero. -/
def WeylNull (g : ℕ → ℝ) : Prop := Tendsto (weylAvg g) atTop (nhds 0)


lemma weylAvg_mul (g : ℕ → ℝ) (N : ℕ) :
    (N : ℂ) * weylAvg g N = ∑ n ∈ Finset.range N, e (g n) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [weylAvg]
  · rw [weylAvg, mul_div_cancel₀]
    exact_mod_cast hN.ne'

lemma norm_weylAvg_le_one (g : ℕ → ℝ) (N : ℕ) : ‖weylAvg g N‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [weylAvg]
  · rw [weylAvg, norm_div, Complex.norm_natCast, div_le_one (by exact_mod_cast hN)]
    calc ‖∑ n ∈ Finset.range N, e (g n)‖ ≤ ∑ n ∈ Finset.range N, ‖e (g n)‖ := norm_sum_le _ _
      _ = N := by simp

/-- The correlation sums of `n ↦ e (P n)` are the Weyl sums of the difference polynomial. -/
lemma corr_eq_weylAvg (P : ℝ[X]) (k N : ℕ) :
    corr (fun n => e (P.eval (n : ℝ))) N k
      = ((N - k : ℕ) : ℂ) * weylAvg (fun n => (diffPoly P (k : ℝ)).eval (n : ℝ)) (N - k) := by
  rw [weylAvg_mul, corr]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← e_sub, eval_diffPoly]
  congr 1
  push_cast
  ring

/-- Base case of Weyl's theorem: linear polynomials with irrational slope. -/
lemma weylNull_linear (P : ℝ[X]) (hdeg : P.natDegree ≤ 1) (hirr : Irrational (P.coeff 1)) :
    WeylNull (fun n => P.eval (n : ℝ)) := by
  set α := P.coeff 1 with hα
  set β := P.coeff 0 with hβ
  have hev : ∀ n : ℕ, P.eval (n : ℝ) = α * n + β := by
    intro n
    conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hdeg]
    simp [hα, hβ]
  have hz : e α ≠ 1 := e_ne_one_of_irrational hirr
  have hzne : e α - 1 ≠ 0 := sub_ne_zero.2 hz
  set C : ℝ := 2 / ‖e α - 1‖ with hC
  have hCpos : 0 < ‖e α - 1‖ := norm_pos_iff.2 hzne
  have hbound : ∀ N : ℕ, ‖∑ n ∈ Finset.range N, e (P.eval (n : ℝ))‖ ≤ C := by
    intro N
    have : ∑ n ∈ Finset.range N, e (P.eval (n : ℝ))
        = e β * ∑ n ∈ Finset.range N, (e α) ^ n := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [hev n, e_add, e_nat_mul, mul_comm (α:ℝ) (n:ℝ), mul_comm]
    rw [this, norm_mul, norm_e, one_mul, geom_sum_eq hz, norm_div, hC]
    gcongr
    calc ‖(e α) ^ N - 1‖ ≤ ‖(e α) ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by simp [norm_pow]; norm_num
  rw [WeylNull, NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨N0, hN0⟩ := exists_nat_gt (C / ε)
  filter_upwards [eventually_ge_atTop (max N0 1)] with N hN
  have hN1 : 1 ≤ N := le_trans (le_max_right N0 1) hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  rw [weylAvg, norm_div, Complex.norm_natCast, div_lt_iff₀ hNR]
  have hCN : C < ε * N := by
    have : (N0 : ℝ) ≤ N := by exact_mod_cast le_trans (le_max_left N0 1) hN
    have h2 : C / ε < N := lt_of_lt_of_le hN0 this
    rw [div_lt_iff₀ hε] at h2
    linarith
  exact lt_of_le_of_lt (hbound N) hCN


/-- The key quantitative van der Corput step. -/
lemma weyl_step (P : ℝ[X]) (H : ℕ) (hH : 0 < H)
    (hind : ∀ k ∈ Finset.Ico 1 H, Tendsto
      (fun M => weylAvg (fun n => (diffPoly P (k:ℝ)).eval (n:ℝ)) M) atTop (nhds 0)) :
    ∀ ε > 0, ∀ᶠ N in atTop, ‖weylAvg (fun n => P.eval (n:ℝ)) N‖^2 ≤ 2/H + ε := by
  intro ε hε
  set u : ℕ → ℂ := fun n => e (P.eval (n:ℝ)) with hu
  have hub : ∀ n, ‖u n‖ ≤ 1 := fun n => le_of_eq (norm_e _)
  have hHR : (0:ℝ) < H := by exact_mod_cast hH
  -- choose δ small
  set δ : ℝ := ε / 8 with hδ
  have hδpos : 0 < δ := by positivity
  -- for each k ∈ [1,H), eventually ‖weylAvg diff M‖ < δ
  have hev : ∀ k ∈ Finset.Ico 1 H, ∀ᶠ M in atTop,
      ‖weylAvg (fun n => (diffPoly P (k:ℝ)).eval (n:ℝ)) M‖ < δ := by
    intro k hk
    have := (hind k hk)
    rw [NormedAddGroup.tendsto_nhds_zero] at this
    exact this δ hδpos
  -- combine: ∃ M0, ∀ M ≥ M0, ∀ k ∈ [1,H), ‖...‖ < δ
  have hall : ∀ᶠ M in atTop, ∀ k ∈ Finset.Ico 1 H,
      ‖weylAvg (fun n => (diffPoly P (k:ℝ)).eval (n:ℝ)) M‖ < δ :=
    (eventually_all_finset _).2 hev
  obtain ⟨M0, hM0⟩ := eventually_atTop.1 hall
  -- Choose N large: N ≥ M0 + H, and (N+H)/N ≤ 2, and H/N small etc
  obtain ⟨N1, hN1⟩ := exists_nat_gt (max ((H:ℝ)) (8 * H / ε))
  filter_upwards [eventually_ge_atTop (max (M0 + H) (max N1 1))] with N hN
  have hNM : M0 + H ≤ N := le_trans (le_max_left _ _) hN
  have hNN1 : N1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right (M0+H) _)) hN
  have hN1' : 1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right (M0+H) _)) hN
  have hNR : (0:ℝ) < N := by exact_mod_cast hN1'
  have hHN : (H:ℝ) ≤ N := by
    have : (N1:ℝ) ≤ N := by exact_mod_cast hNN1
    have := lt_of_le_of_lt (le_max_left (H:ℝ) (8*H/ε)) hN1
    linarith
  have hepsN : 8 * (H:ℝ) / ε ≤ N := by
    have : (N1:ℝ) ≤ N := by exact_mod_cast hNN1
    have := lt_of_le_of_lt (le_max_right (H:ℝ) (8*H/ε)) hN1
    linarith
  -- bound corr norms
  have hcorr : ∀ k ∈ Finset.Ico 1 H, ‖corr u N k‖ ≤ (N:ℝ) * δ := by
    intro k hk
    simp only [Finset.mem_Ico] at hk
    rw [hu, corr_eq_weylAvg, norm_mul, Complex.norm_natCast]
    have hle : ((N - k : ℕ) : ℝ) ≤ N := by
      have : (N - k : ℕ) ≤ N := Nat.sub_le _ _
      exact_mod_cast this
    have hge : M0 ≤ N - k := by omega
    have := hM0 (N - k) hge k (Finset.mem_Ico.2 ⟨hk.1, hk.2⟩)
    exact mul_le_mul hle (le_of_lt this) (norm_nonneg _) (le_of_lt hNR)
  have hsum : ∑ k ∈ Finset.Ico 1 H, ‖corr u N k‖ ≤ (H:ℝ) * ((N:ℝ) * δ) := by
    calc ∑ k ∈ Finset.Ico 1 H, ‖corr u N k‖ ≤ ∑ _k ∈ Finset.Ico 1 H, ((N:ℝ) * δ) :=
          Finset.sum_le_sum hcorr
      _ = ((H - 1 : ℕ) : ℝ) * ((N:ℝ) * δ) := by rw [Finset.sum_const, Nat.card_Ico]; simp
      _ ≤ (H:ℝ) * ((N:ℝ) * δ) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have h : (H - 1 : ℕ) ≤ H := Nat.sub_le _ _
          exact_mod_cast h
  -- van der Corput
  have vdc := van_der_corput N H hH u hub
  have hS : ∑ n ∈ Finset.range N, u n = (N:ℂ) * weylAvg (fun n => P.eval (n:ℝ)) N := by
    rw [weylAvg_mul]
  rw [hS, norm_mul, Complex.norm_natCast, mul_pow] at vdc
  -- so H * N^2 * ‖A‖^2 ≤ (N+H)(N + 2 H N δ)
  set A := ‖weylAvg (fun n => P.eval (n:ℝ)) N‖ with hA
  have hA0 : 0 ≤ A := norm_nonneg _
  have step : (H:ℝ) * ((N:ℝ)^2 * A^2) ≤ ((N:ℝ) + H) * ((N:ℝ) + 2 * ((H:ℝ) * ((N:ℝ) * δ))) := by
    refine le_trans vdc ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith
  -- now deduce A^2 ≤ 1/H + ε
  -- (N+H) ≤ 2N  since H ≤ N
  have step2 : (H:ℝ) * ((N:ℝ)^2 * A^2) ≤ 2 * (N:ℝ) * ((N:ℝ) + 2 * (H:ℝ) * (N:ℝ) * δ) := by
    refine le_trans step ?_
    have h1 : (N:ℝ) + H ≤ 2 * N := by linarith
    have h2 : (0:ℝ) ≤ (N:ℝ) + 2 * ((H:ℝ) * ((N:ℝ) * δ)) := by positivity
    calc ((N:ℝ) + H) * ((N:ℝ) + 2 * ((H:ℝ) * ((N:ℝ) * δ)))
        ≤ (2 * N) * ((N:ℝ) + 2 * ((H:ℝ) * ((N:ℝ) * δ))) := by nlinarith
      _ = 2 * (N:ℝ) * ((N:ℝ) + 2 * (H:ℝ) * (N:ℝ) * δ) := by ring
  -- divide by H N^2
  -- H N^2 A^2 ≤ 2N^2 (1 + 2 H δ)
  have step3 : (H:ℝ) * ((N:ℝ)^2 * A^2) ≤ (N:ℝ)^2 * (2 * (1 + 2 * (H:ℝ) * δ)) := by
    refine le_trans step2 ?_
    have : 2 * (N:ℝ) * ((N:ℝ) + 2 * (H:ℝ) * (N:ℝ) * δ)
        = (N:ℝ)^2 * (2 * (1 + 2 * (H:ℝ) * δ)) := by ring
    linarith [this]
  have hN2 : (0:ℝ) < (N:ℝ)^2 := by positivity
  have step4 : (H:ℝ) * A^2 ≤ 2 * (1 + 2 * (H:ℝ) * δ) := by
    have h : (N:ℝ)^2 * ((H:ℝ) * A^2) ≤ (N:ℝ)^2 * (2 * (1 + 2 * (H:ℝ) * δ)) := by
      calc (N:ℝ)^2 * ((H:ℝ) * A^2) = (H:ℝ) * ((N:ℝ)^2 * A^2) := by ring
        _ ≤ _ := step3
    exact le_of_mul_le_mul_left h hN2
  rw [div_add' _ _ _ (ne_of_gt hHR), le_div_iff₀ hHR]
  have : (H:ℝ) * A^2 ≤ 2 + 4 * (H:ℝ) * δ := by linarith [step4]
  have h4 : 4 * (H:ℝ) * δ ≤ (H:ℝ) * ε := by
    rw [hδ]; nlinarith [hHR, hε]
  linarith



/-- **Weyl's equidistribution criterion** for polynomial sequences. -/
theorem weylNull_main : ∀ d : ℕ, 1 ≤ d → ∀ P : ℝ[X], P.natDegree ≤ d → Irrational (P.coeff d) →
    WeylNull (fun n => P.eval (n:ℝ)) := by
  intro d
  induction d with
  | zero => intro h; omega
  | succ d ih =>
    intro _ P hdeg hirr
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · -- d+1 = 1: base case
      exact weylNull_linear P hdeg hirr
    · -- inductive step
      -- for each k ≥ 1, the difference polynomial has degree ≤ d and coeff d = (d+1)*k*P.coeff(d+1), irrational
      have hkey : ∀ k : ℕ, 1 ≤ k → WeylNull (fun n => (diffPoly P (k:ℝ)).eval (n:ℝ)) := by
        intro k hk
        refine ih hd _ ?_ ?_
        · have := natDegree_diffPoly_le P hdeg (by omega) (k:ℝ)
          simpa using this
        · have := coeff_diffPoly_top P hdeg (by omega) (k:ℝ)
          simp only [Nat.add_sub_cancel] at this
          rw [this]
          -- ((d+1) * k) * P.coeff (d+1) is irrational
          have heq : ((d:ℝ)+1) * (k:ℝ) = (((d+1)*k : ℕ) : ℝ) := by push_cast; ring
          rw [show (((d:ℕ)+1:ℕ):ℝ) * (k:ℝ) * P.coeff (d+1)
              = ((((d+1)*k : ℕ)) : ℝ) * P.coeff (d+1) by push_cast; ring]
          exact hirr.natCast_mul (by positivity)
      -- combine using weyl_step
      rw [WeylNull, NormedAddGroup.tendsto_nhds_zero]
      intro ε hε
      -- choose H with 2/H < ε^2/2
      obtain ⟨H, hH⟩ := exists_nat_gt (8 / ε^2)
      have hHpos : 0 < H := by
        by_contra hc
        have h0 : H = 0 := by omega
        subst h0
        simp only [Nat.cast_zero] at hH
        nlinarith [div_pos (by norm_num : (0:ℝ) < 8) (by positivity : (0:ℝ) < ε^2)]
      have hHR : (0:ℝ) < H := by exact_mod_cast hHpos
      have h2H : 2/(H:ℝ) < ε^2/2 := by
        rw [div_lt_div_iff₀ hHR (by norm_num)]
        rw [div_lt_iff₀ (by positivity)] at hH
        nlinarith
      have hind : ∀ k ∈ Finset.Ico 1 H, Tendsto
          (fun M => weylAvg (fun n => (diffPoly P (k:ℝ)).eval (n:ℝ)) M) atTop (nhds 0) := by
        intro k hk
        simp only [Finset.mem_Ico] at hk
        exact hkey k hk.1
      have := weyl_step P H hHpos hind (ε^2/4) (by positivity)
      filter_upwards [this] with N hN
      have hA0 : 0 ≤ ‖weylAvg (fun n => P.eval (n:ℝ)) N‖ := norm_nonneg _
      nlinarith [hN, hA0, h2H]

end

end TuringTask
