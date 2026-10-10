import TuringTask.Second

namespace TuringTask.Limits

open Filter
open scoped BigOperators Topology

noncomputable section

private abbrev D (N : ℕ) : ℝ :=
  (Finset.Icc 1 N).sum fun n => (n.divisors.card : ℝ)

private abbrev c : ℝ := 2 * Real.eulerMascheroniConstant - 1

lemma tendsto_sqrt_nat_div_nat :
    Tendsto (fun N : ℕ => 4 * Real.sqrt N / N) atTop (nhds 0) := by
  have hsqrt : Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun N : ℕ => (Real.sqrt (N : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hsqrt
  convert tendsto_const_nhds.mul hinv using 1
  · funext N
    rw [mul_div_assoc, Real.sqrt_div_self]
  · norm_num

lemma tendsto_divisor_error_div :
    Tendsto (fun N : ℕ => (D N - (N : ℝ) * Real.log N - c * N) / N)
      atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hmajor := (Metric.tendsto_atTop.1 tendsto_sqrt_nat_div_nat) ε hε
  obtain ⟨N₀, hN₀⟩ := hmajor
  refine ⟨max 1 N₀, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_left 1 N₀) hN
  have hNN₀ : N₀ ≤ N := le_trans (le_max_right 1 N₀) hN
  rw [Real.dist_eq, sub_zero, abs_div]
  have hden : 0 ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
  calc
    |D N - (N : ℝ) * Real.log N - c * N| / |(N : ℝ)|
        ≤ (4 * Real.sqrt N) / |(N : ℝ)| :=
      div_le_div_of_nonneg_right (TuringTask.sum_card_divisors_sub_le_aux N hN1) (abs_nonneg _)
    _ = 4 * Real.sqrt N / N := by rw [abs_of_nonneg hden]
    _ < ε := by
      simpa [Real.dist_eq, abs_of_nonneg (Real.sqrt_nonneg _)] using hN₀ N hNN₀

/-- A proof of the first of the three limit statements in `Basic.lean`. -/
theorem tendsto_sum_card_divisors_aux :
    Tendsto (fun N : Nat => ((Finset.Icc 1 N).sum (fun n => (n.divisors.card : Real)) -
        (N : Real) * Real.log N) / N) atTop
      (nhds (2 * Real.eulerMascheroniConstant - 1)) := by
  have hc : Tendsto (fun _ : ℕ => c) atTop (nhds c) := tendsto_const_nhds
  have h := tendsto_divisor_error_div.add hc
  have heq :
      (fun N : ℕ => (D N - (N : ℝ) * Real.log N) / N) =ᶠ[atTop]
        (fun N : ℕ => (D N - (N : ℝ) * Real.log N - c * N) / N + c) := by
    filter_upwards [eventually_atTop.2 ⟨1, fun _ hN => hN⟩] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    field_simp
    ring
  simpa only [D, c, zero_add] using h.congr' heq.symm

private def logIncrement (n : ℕ) : ℝ :=
  (n : ℝ) * Real.log (1 + 1 / (n : ℝ))

lemma tendsto_logIncrement : Tendsto logIncrement atTop (nhds 1) := by
  change Tendsto (fun n : ℕ => (n : ℝ) * Real.log (1 + 1 / (n : ℝ))) atTop (nhds 1)
  simpa [Function.comp_def, one_div] using
    (Real.tendsto_mul_log_one_add_div_atTop 1).comp tendsto_natCast_atTop_atTop

lemma sum_range_logIncrement (N : ℕ) :
    (Finset.range N).sum logIncrement =
      (N : ℝ) * Real.log N - (Finset.range N).sum (fun n => Real.log (n + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
      by_cases hN : N = 0
      · simp [hN, logIncrement]
      · have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN
        have hNsR : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        have hlog : Real.log (1 + 1 / (N : ℝ)) =
            Real.log (N + 1 : ℕ) - Real.log N := by
          rw [← Real.log_div hNsR hNR]
          congr 1
          field_simp
          norm_num
        rw [logIncrement, hlog]
        push_cast
        ring

lemma sum_range_log_eq_sum_Icc (N : ℕ) :
    (Finset.range N).sum (fun n => Real.log (n + 1)) =
      (Finset.Icc 1 N).sum (fun n => Real.log n) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega) _]
      simpa using congrArg (fun x => x + Real.log (N + 1)) ih

lemma tendsto_sum_log_div_sub_log :
    Tendsto (fun N : ℕ =>
      (Finset.Icc 1 N).sum (fun n => Real.log n) / N - Real.log N)
      atTop (nhds (-1)) := by
  have h := tendsto_logIncrement.cesaro
  have heq :
      (fun N : ℕ => (Finset.Icc 1 N).sum (fun n => Real.log n) / N - Real.log N) =ᶠ[atTop]
        (fun N : ℕ => -((N : ℝ)⁻¹ * (Finset.range N).sum logIncrement)) := by
    filter_upwards [eventually_atTop.2 ⟨1, fun _ hN => hN⟩] with N hN
    rw [sum_range_logIncrement, sum_range_log_eq_sum_Icc]
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    field_simp
    ring
  simpa using h.neg.congr' heq.symm

/-- A proof of the second of the three limit statements in `Basic.lean`. -/
theorem tendsto_sum_card_divisors_sub_log_aux :
    Tendsto (fun N : Nat => (Finset.Icc 1 N).sum (fun n => (n.divisors.card : Real) -
      Real.log n) / N) atTop (nhds (2 * Real.eulerMascheroniConstant)) := by
  have h := tendsto_sum_card_divisors_aux.sub tendsto_sum_log_div_sub_log
  have heq :
      (fun N : ℕ => (Finset.Icc 1 N).sum (fun n => (n.divisors.card : ℝ) -
        Real.log n) / N) =ᶠ[atTop]
      (fun N : ℕ => (D N - (N : ℝ) * Real.log N) / N -
        ((Finset.Icc 1 N).sum (fun n => Real.log n) / N - Real.log N)) := by
    filter_upwards [eventually_atTop.2 ⟨1, fun _ hN => hN⟩] with N hN
    rw [Finset.sum_sub_distrib]
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    field_simp
    ring
  have hh := h.congr' heq.symm
  convert hh using 1
  · ring_nf

private def xlogx (x : ℝ) : ℝ := x * Real.log x

private def xlogxPrimitive (x : ℝ) : ℝ :=
  x ^ 2 * Real.log x / 2 - x ^ 2 / 4

lemma monotoneOn_xlogx : MonotoneOn xlogx (Set.Ici 1) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hlog : Real.log x ≤ Real.log y :=
    Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.2 hx0) (Set.mem_Ioi.2 hy0) hxy
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  calc
    xlogx x = x * Real.log x := rfl
    _ ≤ y * Real.log x := mul_le_mul_of_nonneg_right hxy hlog0
    _ ≤ y * Real.log y := mul_le_mul_of_nonneg_left hlog (le_of_lt hy0)
    _ = xlogx y := rfl

lemma hasDerivAt_xlogxPrimitive {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt xlogxPrimitive (xlogx x) x := by
  have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa only [Nat.cast_ofNat, pow_one, Nat.reduceSub] using hasDerivAt_pow 2 x
  have h := (hsq.mul (Real.hasDerivAt_log hx)).div_const 2 |>.sub (hsq.div_const 4)
  change HasDerivAt (fun y : ℝ => y ^ 2 * Real.log y / 2 - y ^ 2 / 4)
    (x * Real.log x) x
  apply h.congr_deriv
  field_simp [hx]
  ring

lemma integral_xlogx (N : ℕ) (hN : 1 ≤ N) :
    (∫ x : ℝ in 1..N, xlogx x) = xlogxPrimitive N - xlogxPrimitive 1 := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    have hab : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    rw [Set.uIcc_of_le hab] at hx
    have hx1 : 1 ≤ x := by
      exact hx.1
    exact hasDerivAt_xlogxPrimitive (ne_of_gt (lt_of_lt_of_le zero_lt_one hx1))
  · apply ContinuousOn.intervalIntegrable
    intro x hx
    have hab : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    rw [Set.uIcc_of_le hab] at hx
    have hx1 : 1 ≤ x := by
      exact hx.1
    exact (continuousAt_id.mul
      (Real.continuousAt_log (ne_of_gt (lt_of_lt_of_le zero_lt_one hx1)))).continuousWithinAt

lemma integral_xlogx_between (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ x : ℝ in a..b, xlogx x) = xlogxPrimitive b - xlogxPrimitive a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    have habR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    rw [Set.uIcc_of_le habR] at hx
    have hx1 : 1 ≤ x := le_trans (by exact_mod_cast ha) hx.1
    exact hasDerivAt_xlogxPrimitive (ne_of_gt (lt_of_lt_of_le zero_lt_one hx1))
  · apply ContinuousOn.intervalIntegrable
    intro x hx
    have habR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    rw [Set.uIcc_of_le habR] at hx
    have hx1 : 1 ≤ x := le_trans (by exact_mod_cast ha) hx.1
    exact (continuousAt_id.mul
      (Real.continuousAt_log (ne_of_gt (lt_of_lt_of_le zero_lt_one hx1)))).continuousWithinAt

lemma sum_range_add_one_eq_sum_Icc (g : ℕ → ℝ) (N : ℕ) :
    (Finset.range N).sum (fun n => g (n + 1)) = (Finset.Icc 1 N).sum g := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega) _]
      simpa using congrArg (fun x => x + g (N + 1)) ih

lemma sum_range_xlogx_two (M : ℕ) :
    (Finset.range M).sum (fun i => xlogx (1 + (i + 1 : ℕ))) =
      (Finset.Icc 1 (M + 1)).sum (fun n => xlogx n) := by
  induction M with
  | zero => simp [xlogx]
  | succ M ih =>
      rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega) _]
      rw [ih]
      congr 1
      congr 1
      push_cast
      ring

lemma sum_xlogx_bounds (N : ℕ) (hN : 1 ≤ N) :
    xlogxPrimitive N - xlogxPrimitive 1 ≤
        (Finset.Icc 1 N).sum (fun n => (n : ℝ) * Real.log n) ∧
      (Finset.Icc 1 N).sum (fun n => (n : ℝ) * Real.log n) ≤
        xlogxPrimitive (N + 1) - xlogxPrimitive 1 := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le hN
  have hmonoLower : MonotoneOn xlogx (Set.Icc 1 (1 + (M : ℝ))) :=
    monotoneOn_xlogx.mono fun _ hx => hx.1
  have hmonoUpper : MonotoneOn xlogx (Set.Icc 1 (1 + ((1 + M : ℕ) : ℝ))) :=
    monotoneOn_xlogx.mono fun _ hx => hx.1
  constructor
  · rw [← integral_xlogx (1 + M) (by omega)]
    have h := hmonoLower.integral_le_sum
    rw [sum_range_xlogx_two M] at h
    simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm, xlogx] using h
  · have h := hmonoUpper.sum_le_integral
    have hsum : (Finset.range (1 + M)).sum (fun i => xlogx (1 + (i : ℝ))) =
        (Finset.Icc 1 (1 + M)).sum (fun n => xlogx n) := by
      simpa [Nat.cast_add, Nat.cast_one, add_comm] using
        sum_range_add_one_eq_sum_Icc (fun n => xlogx n) (1 + M)
    rw [hsum] at h
    have hi := integral_xlogx ((1 + M) + 1) (by omega)
    calc
      (Finset.Icc 1 (1 + M)).sum (fun n => (n : ℝ) * Real.log n) ≤
          ∫ x : ℝ in 1..((1 + M : ℕ) : ℝ) + 1, xlogx x := by
        simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm, xlogx] using h
      _ = xlogxPrimitive ((1 + M : ℕ) + 1) - xlogxPrimitive 1 := by
        convert hi using 1 <;> norm_num

lemma tendsto_inv_nat : Tendsto (fun N : ℕ => ((N : ℝ))⁻¹) atTop (nhds 0) :=
  tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

lemma tendsto_log_nat_div_nat :
    Tendsto (fun N : ℕ => Real.log N / N) atTop (nhds 0) := by
  simpa [Function.comp_def, id_eq] using
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop

lemma tendsto_succ_atTop : Tendsto (fun N : ℕ => N + 1) atTop atTop := by
  refine Filter.tendsto_atTop.2 ?_
  intro b
  exact eventually_atTop.2 ⟨b, fun a ha => by omega⟩

lemma tendsto_log_succ_div_nat :
    Tendsto (fun N : ℕ => Real.log (N + 1) / N) atTop (nhds 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N + 1) / (N + 1 : ℕ)) atTop (nhds 0) :=
    by simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      tendsto_log_nat_div_nat.comp tendsto_succ_atTop
  have hratio : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ) / N) atTop (nhds 1) := by
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
    have h := hone.add tendsto_inv_nat
    have heq : (fun N : ℕ => ((N + 1 : ℕ) : ℝ) / N) =ᶠ[atTop]
        (fun N : ℕ => 1 + ((N : ℝ))⁻¹) := by
      filter_upwards [eventually_atTop.2 ⟨1, fun _ hN => hN⟩] with N hN
      have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
      push_cast
      field_simp
    simpa using h.congr' heq.symm
  have h := hlog.mul hratio
  have heq : (fun N : ℕ => Real.log (N + 1) / N) =ᶠ[atTop]
      (fun N : ℕ => (Real.log (N + 1) / (N + 1 : ℕ)) * (((N + 1 : ℕ) : ℝ) / N)) := by
    filter_upwards [eventually_atTop.2 ⟨1, fun _ hN => hN⟩] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    have hNs0 : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  simpa using h.congr' heq.symm

lemma tendsto_normalized_xlogx_lower :
    Tendsto (fun N : ℕ =>
      (xlogxPrimitive N - xlogxPrimitive 1 - (N : ℝ) ^ 2 * Real.log N / 2) /
        (N : ℝ) ^ 2) atTop (nhds (-1 / 4)) := by
  have hzero := (tendsto_inv_nat.pow 2).const_mul (1 / 4 : ℝ)
  have heq :
      (fun N : ℕ =>
        (xlogxPrimitive N - xlogxPrimitive 1 - (N : ℝ) ^ 2 * Real.log N / 2) /
          (N : ℝ) ^ 2) =ᶠ[atTop]
      (fun N : ℕ => -1 / 4 + (1 / 4 : ℝ) * ((N : ℝ)⁻¹) ^ 2) := by
    filter_upwards [eventually_atTop.2 ⟨1, fun _ hN => hN⟩] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    simp only [xlogxPrimitive, Real.log_one, mul_zero, one_pow, zero_div]
    field_simp
    ring
  simpa using (tendsto_const_nhds.add hzero).congr' heq.symm

lemma tendsto_normalized_xlogx_gap :
    Tendsto (fun N : ℕ => (xlogxPrimitive (N + 1) - xlogxPrimitive N) / (N : ℝ) ^ 2)
      atTop (nhds 0) := by
  have hmajor : Tendsto (fun N : ℕ =>
      (((N + 1 : ℕ) : ℝ) * Real.log (N + 1)) / (N : ℝ) ^ 2) atTop (nhds 0) := by
    have hratio : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ) / N) atTop (nhds 1) := by
      have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
      have h := hone.add tendsto_inv_nat
      have heq : (fun N : ℕ => ((N + 1 : ℕ) : ℝ) / N) =ᶠ[atTop]
          (fun N : ℕ => 1 + ((N : ℝ))⁻¹) := by
        filter_upwards [eventually_atTop.2 ⟨1, fun _ hN => hN⟩] with N hN
        have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
        push_cast
        field_simp
      simpa using h.congr' heq.symm
    have h := hratio.mul tendsto_log_succ_div_nat
    convert h using 1
    · funext N
      ring
    · norm_num
  apply squeeze_zero'
  · filter_upwards [eventually_atTop.2 ⟨1, fun _ hN => hN⟩] with N hN
    have hint : (∫ x : ℝ in N..(N + 1 : ℕ), xlogx x) =
        xlogxPrimitive (N + 1) - xlogxPrimitive N := by
      simpa [Nat.cast_add, Nat.cast_one] using integral_xlogx_between N (N + 1) hN (by omega)
    rw [← hint]
    exact div_nonneg (intervalIntegral.integral_nonneg (by exact_mod_cast (Nat.le_succ N)) fun x hx =>
      mul_nonneg (le_trans (by exact_mod_cast (Nat.zero_le N)) hx.1)
        (Real.log_nonneg (le_trans (by exact_mod_cast hN) hx.1)))
      (sq_nonneg _)
  · filter_upwards [eventually_atTop.2 ⟨1, fun _ hN => hN⟩] with N hN
    have hmono : MonotoneOn xlogx
        (Set.Icc (N : ℝ) ((N : ℝ) + ((1 : ℕ) : ℝ))) :=
      monotoneOn_xlogx.mono fun _ hx => le_trans (by exact_mod_cast hN) hx.1
    have hsum := MonotoneOn.integral_le_sum (f := xlogx) hmono (x₀ := (N : ℝ)) (a := 1)
    have hint : (∫ x : ℝ in N..(N + 1 : ℕ), xlogx x) =
        xlogxPrimitive (N + 1) - xlogxPrimitive N := by
      simpa [Nat.cast_add, Nat.cast_one] using integral_xlogx_between N (N + 1) hN (by omega)
    have hgap : xlogxPrimitive (N + 1) - xlogxPrimitive N ≤ xlogx (N + 1) := by
      rw [← hint]
      simpa [xlogx, Nat.cast_add, Nat.cast_one, add_assoc] using hsum
    exact div_le_div_of_nonneg_right (by simpa [xlogx] using hgap) (sq_nonneg _)
  · simpa [Nat.cast_add, Nat.cast_one] using hmajor

lemma tendsto_normalized_sum_xlogx :
    Tendsto (fun N : ℕ =>
      ((Finset.Icc 1 N).sum (fun n => (n : ℝ) * Real.log n) -
        (N : ℝ) ^ 2 * Real.log N / 2) / (N : ℝ) ^ 2)
      atTop (nhds (-1 / 4)) := by
  have hlower := tendsto_normalized_xlogx_lower
  have hupper := tendsto_normalized_xlogx_lower.add tendsto_normalized_xlogx_gap
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower (by simpa using hupper)
  · filter_upwards [eventually_atTop.2 ⟨1, fun _ hN => hN⟩] with N hN
    exact div_le_div_of_nonneg_right (sub_le_sub_right (sum_xlogx_bounds N hN).1 _)
      (sq_nonneg _)
  · filter_upwards [eventually_atTop.2 ⟨1, fun _ hN => hN⟩] with N hN
    have h := sub_le_sub_right (sum_xlogx_bounds N hN).2 ((N : ℝ) ^ 2 * Real.log N / 2)
    have hden : 0 ≤ (N : ℝ) ^ 2 := sq_nonneg _
    calc
      ((Finset.Icc 1 N).sum (fun n => (n : ℝ) * Real.log n) -
          (N : ℝ) ^ 2 * Real.log N / 2) / (N : ℝ) ^ 2
          ≤ (xlogxPrimitive (N + 1) - xlogxPrimitive 1 -
            (N : ℝ) ^ 2 * Real.log N / 2) / (N : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right h hden
      _ = (xlogxPrimitive N - xlogxPrimitive 1 -
            (N : ℝ) ^ 2 * Real.log N / 2) / (N : ℝ) ^ 2 +
          (xlogxPrimitive (N + 1) - xlogxPrimitive N) / (N : ℝ) ^ 2 := by ring

private def divisorError (n : ℕ) : ℝ :=
  D n - (n : ℝ) * Real.log n - c * n

lemma sum_divisorError_bound (N : ℕ) (_hN : 1 ≤ N) :
    |(Finset.Icc 1 N).sum divisorError| ≤ (N : ℝ) * (4 * Real.sqrt N) := by
  calc
    |(Finset.Icc 1 N).sum divisorError| ≤
        (Finset.Icc 1 N).sum (fun n => |divisorError n|) :=
      Finset.abs_sum_le_sum_abs divisorError (Finset.Icc 1 N)
    _ ≤ (Finset.Icc 1 N).sum (fun _ => 4 * Real.sqrt N) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
      calc
        |divisorError n| ≤ 4 * Real.sqrt n :=
          TuringTask.sum_card_divisors_sub_le_aux n hn1
        _ ≤ 4 * Real.sqrt N := by
          gcongr
    _ = (N : ℝ) * (4 * Real.sqrt N) := by
      simp

lemma tendsto_sum_divisorError :
    Tendsto (fun N : ℕ => (Finset.Icc 1 N).sum divisorError / (N : ℝ) ^ 2)
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (g := fun N : ℕ => 4 * Real.sqrt N / N)
  · exact Filter.Eventually.of_forall fun _ => norm_nonneg _
  · filter_upwards [eventually_atTop.2 ⟨1, fun _ hN => hN⟩] with N hN
    rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_nonneg (by positivity : 0 ≤ (N : ℝ))]
    have hden : 0 ≤ (N : ℝ) ^ 2 := sq_nonneg _
    calc
      |(Finset.Icc 1 N).sum divisorError| / (N : ℝ) ^ 2 ≤
          ((N : ℝ) * (4 * Real.sqrt N)) / (N : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right (sum_divisorError_bound N hN) hden
      _ = 4 * Real.sqrt N / N := by
        have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
        field_simp
  · exact tendsto_sqrt_nat_div_nat

lemma sum_cast_Icc_formula (N : ℕ) :
    (Finset.Icc 1 N).sum (fun n => (n : ℝ)) = (N : ℝ) * (N + 1) / 2 := by
  rw [← sum_range_add_one_eq_sum_Icc (fun n => (n : ℝ)) N]
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

lemma tendsto_sum_cast_Icc_div_sq :
    Tendsto (fun N : ℕ => (Finset.Icc 1 N).sum (fun n => (n : ℝ)) / (N : ℝ) ^ 2)
      atTop (nhds (1 / 2)) := by
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have h := (hone.add tendsto_inv_nat).div_const 2
  have heq :
      (fun N : ℕ => (Finset.Icc 1 N).sum (fun n => (n : ℝ)) / (N : ℝ) ^ 2) =ᶠ[atTop]
      (fun N : ℕ => (1 + ((N : ℝ))⁻¹) / 2) := by
    filter_upwards [eventually_atTop.2 ⟨1, fun _ hN => hN⟩] with N hN
    rw [sum_cast_Icc_formula]
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    field_simp
  simpa using h.congr' heq.symm

/-- A proof of the last limit statement in `Basic.lean`. -/
theorem tendsto_sum_sum_card_divisors_aux :
    Tendsto (fun N : Nat => ((Finset.Icc 1 N).sum (fun n =>
        (Finset.Icc 1 n).sum (fun m => (m.divisors.card : Real))) -
        (N : Real) ^ 2 * Real.log N / 2) / (N : Real) ^ 2) atTop
      (nhds (Real.eulerMascheroniConstant - 3 / 4)) := by
  have hmain := tendsto_normalized_sum_xlogx
  have hlinear := tendsto_sum_cast_Icc_div_sq.const_mul c
  have herr := tendsto_sum_divisorError
  have h := (hmain.add hlinear).add herr
  have heq :
      (fun N : ℕ => ((Finset.Icc 1 N).sum (fun n => D n) -
        (N : ℝ) ^ 2 * Real.log N / 2) / (N : ℝ) ^ 2) =ᶠ[atTop]
      (fun N : ℕ =>
        ((Finset.Icc 1 N).sum (fun n => (n : ℝ) * Real.log n) -
          (N : ℝ) ^ 2 * Real.log N / 2) / (N : ℝ) ^ 2 +
        c * ((Finset.Icc 1 N).sum (fun n => (n : ℝ)) / (N : ℝ) ^ 2) +
        (Finset.Icc 1 N).sum divisorError / (N : ℝ) ^ 2) := by
    filter_upwards [eventually_atTop.2 ⟨1, fun _ hN => hN⟩] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    have hpoint (n : ℕ) : D n = (n : ℝ) * Real.log n + c * n + divisorError n := by
      simp only [divisorError]
      ring
    have hsum : (Finset.Icc 1 N).sum (fun n => D n) =
        (Finset.Icc 1 N).sum (fun n => (n : ℝ) * Real.log n + c * n + divisorError n) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact hpoint n
    rw [hsum]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [← Finset.mul_sum]
    field_simp
    ring
  have hh := h.congr' heq.symm
  have hv : -1 / 4 + c * (1 / 2) + 0 = Real.eulerMascheroniConstant - 3 / 4 := by
    simp only [c]
    ring
  rw [hv] at hh
  simpa only [D] using hh

end

end TuringTask.Limits
