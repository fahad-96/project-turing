import TuringTask.Thm1
import TuringTask.Thm2
import TuringTask.Stirling

namespace TuringTask

open Finset Filter Topology Real

/-- `4/√N → 0`. -/
lemma tendsto_four_div_sqrt : Tendsto (fun N : ℕ => 4 / Real.sqrt N) atTop (nhds 0) := by
  have h1 : Tendsto (fun N : ℕ => Real.sqrt N) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  exact Filter.Tendsto.div_atTop tendsto_const_nhds h1

lemma four_sqrt_div (N : ℕ) (hN : 1 ≤ N) : 4 * Real.sqrt N / N = 4 / Real.sqrt N := by
  have h : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr h
  rw [div_eq_div_iff h.ne' hs.ne', mul_assoc, Real.mul_self_sqrt h.le]

/-- `(log N + 1)/N → 0`. -/
lemma tendsto_log_add_one_div : Tendsto (fun N : ℕ => (Real.log N + 1) / N) atTop (nhds 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log N / N) atTop (nhds 0) :=
    (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp tendsto_natCast_atTop_atTop
  have hone : Tendsto (fun N : ℕ => (1 : ℝ) / N) atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hsum := hlog.add hone
  rw [add_zero] at hsum
  exact hsum.congr fun N => by ring

/-- **Theorem 3.** -/
theorem tendsto_three :
    Tendsto (fun N : ℕ => ((∑ n ∈ Icc 1 N, (n.divisors.card : ℝ)) - (N : ℝ) * Real.log N) / N)
      atTop (nhds (2 * eulerMascheroniConstant - 1)) := by
  rw [← zero_add (2 * eulerMascheroniConstant - 1)]
  have hmain : Tendsto (fun N : ℕ =>
      ((∑ n ∈ Icc 1 N, (n.divisors.card : ℝ)) - (N : ℝ) * Real.log N) / N -
        (2 * eulerMascheroniConstant - 1)) atTop (nhds 0) := by
    apply squeeze_zero_norm' (a := fun N : ℕ => 4 / Real.sqrt N) _ tendsto_four_div_sqrt
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have hest := main_estimate N hN
    have hrw : ((∑ n ∈ Icc 1 N, (n.divisors.card : ℝ)) - (N : ℝ) * Real.log N) / N -
        (2 * eulerMascheroniConstant - 1)
        = ((∑ n ∈ Icc 1 N, (n.divisors.card : ℝ)) - (N : ℝ) * Real.log N -
            (2 * eulerMascheroniConstant - 1) * N) / N := by
      field_simp
    rw [hrw, Real.norm_eq_abs, abs_div, abs_of_pos hNR, ← four_sqrt_div N hN]
    exact (div_le_div_iff_of_pos_right hNR).mpr hest
  simpa using hmain.add_const (2 * eulerMascheroniConstant - 1)

/-- **Theorem 4.** -/
theorem tendsto_four_thm :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, ((n.divisors.card : ℝ) - Real.log n)) / N)
      atTop (nhds (2 * eulerMascheroniConstant)) := by
  rw [← zero_add (2 * eulerMascheroniConstant)]
  have hmain : Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, ((n.divisors.card : ℝ) - Real.log n)) / N -
        2 * eulerMascheroniConstant) atTop (nhds 0) := by
    apply squeeze_zero_norm' (a := fun N : ℕ => 4 / Real.sqrt N + (Real.log N + 1) / N) _
      (by simpa using tendsto_four_div_sqrt.add tendsto_log_add_one_div)
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have hest := main_estimate N hN
    obtain ⟨hs0, hs1⟩ := log_factorial_bounds N hN
    have hsplit : ∑ n ∈ Icc 1 N, ((n.divisors.card : ℝ) - Real.log n)
        = (∑ n ∈ Icc 1 N, (n.divisors.card : ℝ)) - ∑ n ∈ Icc 1 N, Real.log n :=
      Finset.sum_sub_distrib _ _
    have hrw : (∑ n ∈ Icc 1 N, ((n.divisors.card : ℝ) - Real.log n)) / N -
        2 * eulerMascheroniConstant
        = (((∑ n ∈ Icc 1 N, (n.divisors.card : ℝ)) - (N : ℝ) * Real.log N -
              (2 * eulerMascheroniConstant - 1) * N)
            - ((∑ n ∈ Icc 1 N, Real.log n) - ((N : ℝ) * Real.log N - N + 1)) - 1) / N := by
      rw [hsplit]
      field_simp
      ring
    rw [hrw, Real.norm_eq_abs, abs_div, abs_of_pos hNR]
    have habs2 : |(∑ n ∈ Icc 1 N, Real.log n) - ((N : ℝ) * Real.log N - N + 1)|
        ≤ Real.log N := by rw [abs_of_nonneg hs0]; exact hs1
    have hnum : |((∑ n ∈ Icc 1 N, (n.divisors.card : ℝ)) - (N : ℝ) * Real.log N -
          (2 * eulerMascheroniConstant - 1) * N)
        - ((∑ n ∈ Icc 1 N, Real.log n) - ((N : ℝ) * Real.log N - N + 1)) - 1|
        ≤ 4 * Real.sqrt N + (Real.log N + 1) := by
      have hstep1 := abs_sub ((∑ n ∈ Icc 1 N, (n.divisors.card : ℝ)) - (N : ℝ) * Real.log N -
          (2 * eulerMascheroniConstant - 1) * N -
          ((∑ n ∈ Icc 1 N, Real.log n) - ((N : ℝ) * Real.log N - N + 1))) (1 : ℝ)
      have hstep2 := abs_sub ((∑ n ∈ Icc 1 N, (n.divisors.card : ℝ)) - (N : ℝ) * Real.log N -
          (2 * eulerMascheroniConstant - 1) * N)
          ((∑ n ∈ Icc 1 N, Real.log n) - ((N : ℝ) * Real.log N - N + 1))
      rw [abs_one] at hstep1
      linarith
    have hsplit2 : 4 / Real.sqrt N + (Real.log N + 1) / N
        = (4 * Real.sqrt N + (Real.log N + 1)) / N := by
      rw [← four_sqrt_div N hN, ← add_div]
    rw [hsplit2]
    exact (div_le_div_iff_of_pos_right hNR).mpr hnum
  simpa using hmain.add_const (2 * eulerMascheroniConstant)

/-! ### Theorem 5 -/

lemma sum_sqrt_le (N : ℕ) : ∑ n ∈ Icc 1 N, Real.sqrt n ≤ (N : ℝ) * Real.sqrt N := by
  calc ∑ n ∈ Icc 1 N, Real.sqrt n ≤ ∑ _n ∈ Icc 1 N, Real.sqrt N := by
        apply Finset.sum_le_sum
        intro n hn
        rw [mem_Icc] at hn
        exact Real.sqrt_le_sqrt (by exact_mod_cast hn.2)
    _ = (N : ℝ) * Real.sqrt N := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        simp

lemma sum_cast_id (N : ℕ) : ∑ n ∈ Icc 1 N, (n : ℝ) = (N : ℝ) * ((N : ℝ) + 1) / 2 := by
  induction N with
  | zero => simp
  | succ k ih => rw [Finset.sum_Icc_succ_top (by omega)]; push_cast; rw [ih]; ring

/-- Decomposition of `∑_{n ≤ N} D(n)`. -/
lemma sum_sum_decomp (N : ℕ) :
    ∃ E : ℝ, |E| ≤ 4 * (N : ℝ) * Real.sqrt N ∧
      ∑ n ∈ Icc 1 N, (∑ m ∈ Icc 1 n, (m.divisors.card : ℝ))
        = (∑ n ∈ Icc 1 N, (n : ℝ) * Real.log n)
          + (2 * eulerMascheroniConstant - 1) * ((N : ℝ) * ((N : ℝ) + 1) / 2) + E := by
  refine ⟨∑ n ∈ Icc 1 N, ((∑ m ∈ Icc 1 n, (m.divisors.card : ℝ)) - (n : ℝ) * Real.log n -
    (2 * eulerMascheroniConstant - 1) * n), ?_, ?_⟩
  · calc |∑ n ∈ Icc 1 N, ((∑ m ∈ Icc 1 n, (m.divisors.card : ℝ)) - (n : ℝ) * Real.log n -
            (2 * eulerMascheroniConstant - 1) * n)|
        ≤ ∑ n ∈ Icc 1 N, |(∑ m ∈ Icc 1 n, (m.divisors.card : ℝ)) - (n : ℝ) * Real.log n -
            (2 * eulerMascheroniConstant - 1) * n| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Icc 1 N, 4 * Real.sqrt n := by
          apply Finset.sum_le_sum
          intro n hn
          rw [mem_Icc] at hn
          exact main_estimate n hn.1
      _ = 4 * ∑ n ∈ Icc 1 N, Real.sqrt n := by rw [Finset.mul_sum]
      _ ≤ 4 * ((N : ℝ) * Real.sqrt N) := by
          exact mul_le_mul_of_nonneg_left (sum_sqrt_le N) (by norm_num)
      _ = 4 * (N : ℝ) * Real.sqrt N := by ring
  · rw [← sum_cast_id N, Finset.mul_sum]
    rw [eq_comm, ← sub_eq_zero]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_eq_zero
    intro n _
    ring

/-- The combined error bound for Theorem 5 tends to `0`. -/
lemma tendsto_thm5_bound :
    Tendsto (fun N : ℕ => 4 / Real.sqrt N + ((Real.log N + 1) / N
      + (|2 * eulerMascheroniConstant - 1| / 2 + 1) / N)) atTop (nhds 0) := by
  have h1 := tendsto_four_div_sqrt
  have h2 := tendsto_log_add_one_div
  have h3 : Tendsto (fun N : ℕ =>
      (|2 * eulerMascheroniConstant - 1| / 2 + 1) / N) atTop (nhds 0) := by
    simpa using tendsto_const_nhds (x := |2 * eulerMascheroniConstant - 1| / 2 + 1)
      (f := (atTop : Filter ℕ)) |>.div_atTop tendsto_natCast_atTop_atTop
  simpa using h1.add (h2.add h3)

lemma four_N_sqrt_div (N : ℕ) (hN : 1 ≤ N) :
    4 * (N : ℝ) * Real.sqrt N / (N : ℝ) ^ 2 = 4 / Real.sqrt N := by
  have h : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr h
  rw [div_eq_div_iff (by positivity) hs.ne', mul_assoc, Real.mul_self_sqrt h.le]
  ring

/-- **Theorem 5.** -/
theorem tendsto_five :
    Tendsto (fun N : ℕ => ((∑ n ∈ Icc 1 N, (∑ m ∈ Icc 1 n, (m.divisors.card : ℝ))) -
        (N : ℝ) ^ 2 * Real.log N / 2) / (N : ℝ) ^ 2) atTop
      (nhds (eulerMascheroniConstant - 3 / 4)) := by
  rw [← zero_add (eulerMascheroniConstant - 3 / 4)]
  have hmain : Tendsto (fun N : ℕ => ((∑ n ∈ Icc 1 N, (∑ m ∈ Icc 1 n, (m.divisors.card : ℝ))) -
      (N : ℝ) ^ 2 * Real.log N / 2) / (N : ℝ) ^ 2 -
        (eulerMascheroniConstant - 3 / 4)) atTop (nhds 0) := by
    apply squeeze_zero_norm' (a := fun N : ℕ => 4 / Real.sqrt N + ((Real.log N + 1) / N
      + (|2 * eulerMascheroniConstant - 1| / 2 + 1) / N)) _ tendsto_thm5_bound
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
    obtain ⟨E, hE, hEeq⟩ := sum_sum_decomp N
    obtain ⟨hR0, hR1⟩ := sum_xlogx_bounds N hN
    -- write the whole expression over `N²`
    have hrw : ((∑ n ∈ Icc 1 N, (∑ m ∈ Icc 1 n, (m.divisors.card : ℝ))) -
        (N : ℝ) ^ 2 * Real.log N / 2) / (N : ℝ) ^ 2 - (eulerMascheroniConstant - 3 / 4)
        = (E + ((∑ n ∈ Icc 1 N, (n : ℝ) * Real.log n)
              - ((N : ℝ) ^ 2 * Real.log N / 2 - (N : ℝ) ^ 2 / 4 + 1 / 4))
            + 1 / 4 + (2 * eulerMascheroniConstant - 1) * (N : ℝ) / 2) / (N : ℝ) ^ 2 := by
      rw [hEeq, eq_div_iff hN2.ne', sub_mul, div_mul_cancel₀ _ hN2.ne']
      ring
    rw [hrw, Real.norm_eq_abs, abs_div, abs_of_pos hN2]
    -- bound the numerator
    have hRabs : |(∑ n ∈ Icc 1 N, (n : ℝ) * Real.log n)
        - ((N : ℝ) ^ 2 * Real.log N / 2 - (N : ℝ) ^ 2 / 4 + 1 / 4)| ≤ (N : ℝ) * Real.log N := by
      rw [abs_of_nonneg hR0]; exact hR1
    have hlast : |(2 * eulerMascheroniConstant - 1) * (N : ℝ) / 2|
        = |2 * eulerMascheroniConstant - 1| / 2 * (N : ℝ) := by
      rw [abs_div, abs_mul, abs_of_pos hNR]
      simp
      ring
    have hnum : |E + ((∑ n ∈ Icc 1 N, (n : ℝ) * Real.log n)
          - ((N : ℝ) ^ 2 * Real.log N / 2 - (N : ℝ) ^ 2 / 4 + 1 / 4))
        + 1 / 4 + (2 * eulerMascheroniConstant - 1) * (N : ℝ) / 2|
        ≤ 4 * (N : ℝ) * Real.sqrt N + ((N : ℝ) * Real.log N + (N : ℝ))
          + (|2 * eulerMascheroniConstant - 1| / 2 + 1) * (N : ℝ) := by
      have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have t1 := abs_add_le (E + ((∑ n ∈ Icc 1 N, (n : ℝ) * Real.log n)
          - ((N : ℝ) ^ 2 * Real.log N / 2 - (N : ℝ) ^ 2 / 4 + 1 / 4)) + 1 / 4)
        ((2 * eulerMascheroniConstant - 1) * (N : ℝ) / 2)
      have t2 := abs_add_le (E + ((∑ n ∈ Icc 1 N, (n : ℝ) * Real.log n)
          - ((N : ℝ) ^ 2 * Real.log N / 2 - (N : ℝ) ^ 2 / 4 + 1 / 4))) ((1 : ℝ) / 4)
      have t3 := abs_add_le E ((∑ n ∈ Icc 1 N, (n : ℝ) * Real.log n)
          - ((N : ℝ) ^ 2 * Real.log N / 2 - (N : ℝ) ^ 2 / 4 + 1 / 4))
      rw [hlast] at t1
      have habs14 : |(1 : ℝ) / 4| = 1 / 4 := by norm_num
      rw [habs14] at t2
      nlinarith [hE, hRabs, hN1]
    have hdenom : 4 * (N : ℝ) * Real.sqrt N + ((N : ℝ) * Real.log N + (N : ℝ))
          + (|2 * eulerMascheroniConstant - 1| / 2 + 1) * (N : ℝ)
        = ((4 / Real.sqrt N) + ((Real.log N + 1) / N
            + (|2 * eulerMascheroniConstant - 1| / 2 + 1) / N)) * (N : ℝ) ^ 2 := by
      have hs : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr hNR
      have hNsq : (N : ℝ) = Real.sqrt N * Real.sqrt N := (Real.mul_self_sqrt hNR.le).symm
      have e1 : 4 / Real.sqrt N * (N : ℝ) ^ 2 = 4 * (N : ℝ) * Real.sqrt N := by
        rw [sq]
        nth_rewrite 2 [hNsq]
        field_simp
      have e2 : (Real.log N + 1) / (N : ℝ) * (N : ℝ) ^ 2
          = (N : ℝ) * Real.log N + (N : ℝ) := by
        field_simp
      have e3 : (|2 * eulerMascheroniConstant - 1| / 2 + 1) / (N : ℝ) * (N : ℝ) ^ 2
          = (|2 * eulerMascheroniConstant - 1| / 2 + 1) * (N : ℝ) := by
        field_simp
      have hdist : ((4 / Real.sqrt N) + ((Real.log N + 1) / N
            + (|2 * eulerMascheroniConstant - 1| / 2 + 1) / N)) * (N : ℝ) ^ 2
          = 4 / Real.sqrt N * (N : ℝ) ^ 2 + ((Real.log N + 1) / (N : ℝ) * (N : ℝ) ^ 2
            + (|2 * eulerMascheroniConstant - 1| / 2 + 1) / (N : ℝ) * (N : ℝ) ^ 2) := by
        ring
      rw [hdist, e1, e2, e3]
      ring
    rw [div_le_iff₀ hN2]
    calc |E + ((∑ n ∈ Icc 1 N, (n : ℝ) * Real.log n)
            - ((N : ℝ) ^ 2 * Real.log N / 2 - (N : ℝ) ^ 2 / 4 + 1 / 4))
          + 1 / 4 + (2 * eulerMascheroniConstant - 1) * (N : ℝ) / 2|
        ≤ 4 * (N : ℝ) * Real.sqrt N + ((N : ℝ) * Real.log N + (N : ℝ))
          + (|2 * eulerMascheroniConstant - 1| / 2 + 1) * (N : ℝ) := hnum
      _ = _ := hdenom
  simpa using hmain.add_const (eulerMascheroniConstant - 3 / 4)

end TuringTask
