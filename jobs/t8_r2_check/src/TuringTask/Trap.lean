import Mathlib

/-!
# Trapezoidal approximations to indicator functions

For `0 < d` we build a continuous "trapezoid" `trap d a b` which vanishes outside `(a, b)`,
equals `1` on `[a + d, b - d]`, takes values in `[0,1]`, and vanishes at `0` and `1`
whenever `0 ≤ a` and `b ≤ 1`.
-/

open MeasureTheory intervalIntegral

namespace TuringTask

noncomputable section

/-- The ramp which is `0` below `a`, rises linearly, and is `1` above `a + d`. -/
def ramp (d a x : ℝ) : ℝ := max 0 (min 1 ((x - a) / d))

lemma ramp_nonneg (d a x : ℝ) : 0 ≤ ramp d a x := le_max_left _ _

lemma ramp_le_one (d a x : ℝ) : ramp d a x ≤ 1 := by
  rw [ramp, max_le_iff]; exact ⟨zero_le_one, min_le_left _ _⟩

lemma ramp_continuous (d a : ℝ) (hd : 0 < d) : Continuous (ramp d a) := by
  unfold ramp; fun_prop (disch := assumption)

lemma ramp_eq_zero {d a x : ℝ} (hd : 0 < d) (h : x ≤ a) : ramp d a x = 0 := by
  rw [ramp, max_eq_left]
  exact min_le_of_right_le (div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le)

lemma ramp_eq_one {d a x : ℝ} (hd : 0 < d) (h : a + d ≤ x) : ramp d a x = 1 := by
  rw [ramp, min_eq_left, max_eq_right zero_le_one]
  rw [le_div_iff₀ hd]; linarith

lemma ramp_pos_imp {d a x : ℝ} (hd : 0 < d) (h : 0 < ramp d a x) : a < x := by
  by_contra hc
  rw [ramp_eq_zero hd (not_lt.1 hc)] at h
  exact lt_irrefl 0 h

/-- The trapezoid supported in `(a, b)`, equal to `1` on `[a + d, b - d]`. -/
def trap (d a b x : ℝ) : ℝ := max 0 (min (ramp d a x) (1 - ramp d (b - d) x))

lemma trap_nonneg (d a b x : ℝ) : 0 ≤ trap d a b x := le_max_left _ _

lemma trap_le_one (d a b x : ℝ) : trap d a b x ≤ 1 := by
  rw [trap, max_le_iff]
  exact ⟨zero_le_one, min_le_of_left_le (ramp_le_one _ _ _)⟩

lemma trap_continuous (d a b : ℝ) (hd : 0 < d) : Continuous (trap d a b) := by
  unfold trap
  exact continuous_const.max (((ramp_continuous d a hd).min
    (continuous_const.sub (ramp_continuous d (b - d) hd))))

lemma trap_eq_zero_left {d a b x : ℝ} (hd : 0 < d) (h : x ≤ a) : trap d a b x = 0 := by
  rw [trap, ramp_eq_zero hd h, max_eq_left]
  exact min_le_of_left_le le_rfl

lemma trap_eq_zero_right {d a b x : ℝ} (hd : 0 < d) (h : b ≤ x) : trap d a b x = 0 := by
  have h1 : ramp d (b - d) x = 1 := ramp_eq_one hd (by linarith)
  rw [trap, h1, max_eq_left]
  exact min_le_of_right_le (by norm_num)

lemma trap_eq_one {d a b x : ℝ} (hd : 0 < d) (h1 : a + d ≤ x) (h2 : x ≤ b - d) :
    trap d a b x = 1 := by
  rw [trap, ramp_eq_one hd h1, ramp_eq_zero hd h2]
  norm_num

/-- `trap` vanishes at the endpoints of the unit interval. -/
lemma trap_zero {d a b : ℝ} (hd : 0 < d) (ha : 0 ≤ a) : trap d a b 0 = 0 :=
  trap_eq_zero_left hd ha

lemma trap_one {d a b : ℝ} (hd : 0 < d) (hb : b ≤ 1) : trap d a b 1 = 0 :=
  trap_eq_zero_right hd hb

lemma trap_intervalIntegrable (d a b : ℝ) (hd : 0 < d) (p q : ℝ) :
    IntervalIntegrable (trap d a b) volume p q :=
  (trap_continuous d a b hd).intervalIntegrable p q

/-- The integral of the trapezoid is at least `b - a - 2d`. -/
lemma trap_integral_ge {d a b : ℝ} (hd : 0 < d) (ha : 0 ≤ a) (hb : b ≤ 1) :
    b - a - 2 * d ≤ ∫ x in (0:ℝ)..1, trap d a b x := by
  rcases le_or_gt (b - d) (a + d) with hle | hlt
  · -- degenerate case: the lower bound is nonpositive
    have hnn : (0:ℝ) ≤ ∫ x in (0:ℝ)..1, trap d a b x :=
      intervalIntegral.integral_nonneg zero_le_one fun x _ => trap_nonneg d a b x
    linarith
  · have h0 : (0:ℝ) ≤ a + d := by linarith
    have h1 : b - d ≤ 1 := by linarith
    have hI := trap_intervalIntegrable d a b hd
    have hA := intervalIntegral.integral_add_adjacent_intervals (hI 0 (a + d)) (hI (a + d) (b - d))
    have hB := intervalIntegral.integral_add_adjacent_intervals (hI 0 (b - d)) (hI (b - d) 1)
    have e1 : (0:ℝ) ≤ ∫ x in (0:ℝ)..(a + d), trap d a b x :=
      intervalIntegral.integral_nonneg h0 fun x _ => trap_nonneg d a b x
    have e3 : (0:ℝ) ≤ ∫ x in (b - d:ℝ)..1, trap d a b x :=
      intervalIntegral.integral_nonneg h1 fun x _ => trap_nonneg d a b x
    have e2 : ∫ x in (a + d:ℝ)..(b - d), trap d a b x = b - a - 2 * d := by
      rw [intervalIntegral.integral_congr (g := fun _ => (1:ℝ)) ?_]
      · simp; ring
      · intro x hx
        rw [Set.uIcc_of_le hlt.le] at hx
        exact trap_eq_one hd hx.1 hx.2
    rw [← hB, ← hA, e2]
    linarith


/-- `trap` bounds the indicator of `[a, b)` from below. -/
lemma trap_le_indicator {d a b x : ℝ} (hd : 0 < d) (h : ¬ (a ≤ x ∧ x < b)) :
    trap d a b x = 0 := by
  rcases not_and_or.1 h with h1 | h1
  · exact trap_eq_zero_left hd (le_of_not_ge h1)
  · exact trap_eq_zero_right hd (not_lt.1 h1)

/-- The "outer" approximation: `1 - trap` of the complement.  We use the function
`outer d a b = 1 - trap d 0 a - trap d b 1` restricted appropriately.  Instead, we use
the simpler bound via the two intervals `[0, a)` and `[b, 1)`. -/
def outer (d a b x : ℝ) : ℝ := 1 - trap d 0 a x - trap d b 1 x

lemma outer_continuous (d a b : ℝ) (hd : 0 < d) : Continuous (outer d a b) :=
  (continuous_const.sub (trap_continuous d 0 a hd)).sub (trap_continuous d b 1 hd)

/-- `outer` takes the same value at the two endpoints of `[0,1]`. -/
lemma outer_endpoints {d a b : ℝ} (hd : 0 < d) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    outer d a b 0 = outer d a b 1 := by
  have e1 : trap d 0 a 0 = 0 := trap_eq_zero_left hd le_rfl
  have e2 : trap d b 1 0 = 0 := trap_eq_zero_left hd (by linarith)
  have e3 : trap d 0 a 1 = 0 := trap_eq_zero_right hd (by linarith)
  have e4 : trap d b 1 1 = 0 := trap_eq_zero_right hd le_rfl
  rw [outer, outer, e1, e2, e3, e4]

lemma outer_le_one (d a b x : ℝ) : outer d a b x ≤ 1 := by
  rw [outer]
  have := trap_nonneg d 0 a x
  have := trap_nonneg d b 1 x
  linarith

/-- The indicator of `[a, b)` is at most `outer`. -/
lemma indicator_le_outer {d a b x : ℝ} (hd : 0 < d) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (h : a ≤ x ∧ x < b) : (1:ℝ) ≤ outer d a b x := by
  rw [outer]
  have h1 : trap d 0 a x = 0 := trap_eq_zero_right hd h.1
  have h2 : trap d b 1 x = 0 := trap_eq_zero_left hd h.2.le
  rw [h1, h2]; ring_nf; rfl

/-- The integral of `outer` is at most `b - a + 4 d`. -/
lemma outer_integral_le {d a b : ℝ} (hd : 0 < d) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (∫ x in (0:ℝ)..1, outer d a b x) ≤ b - a + 4 * d := by
  have hI1 := trap_intervalIntegrable d 0 a hd
  have hI2 := trap_intervalIntegrable d b 1 hd
  have hsub : ∫ x in (0:ℝ)..1, outer d a b x
      = 1 - (∫ x in (0:ℝ)..1, trap d 0 a x) - ∫ x in (0:ℝ)..1, trap d b 1 x := by
    simp only [outer]
    rw [intervalIntegral.integral_sub
      ((intervalIntegrable_const).sub (hI1 0 1)) (hI2 0 1),
      intervalIntegral.integral_sub (intervalIntegrable_const) (hI1 0 1)]
    simp
  rw [hsub]
  have g1 : a - 0 - 2 * d ≤ ∫ x in (0:ℝ)..1, trap d 0 a x :=
    trap_integral_ge hd le_rfl (by linarith)
  have g2 : (1:ℝ) - b - 2 * d ≤ ∫ x in (0:ℝ)..1, trap d b 1 x :=
    trap_integral_ge hd (by linarith) le_rfl
  linarith


/-- `trap d 0 a` and `trap d b 1` have disjoint supports when `a ≤ b`. -/
lemma outer_nonneg {d a b : ℝ} (hd : 0 < d) (hab : a ≤ b) (x : ℝ) : 0 ≤ outer d a b x := by
  rw [outer]
  rcases le_or_gt (trap d 0 a x) 0 with h | h
  · have h0 : trap d 0 a x = 0 := le_antisymm h (trap_nonneg _ _ _ _)
    rw [h0]
    have := trap_le_one d b 1 x
    linarith
  · -- trap d 0 a x > 0 forces x < a ≤ b, so trap d b 1 x = 0
    have hxa : x < a := by
      by_contra hc
      rw [trap_eq_zero_right hd (not_lt.1 hc)] at h
      exact lt_irrefl 0 h
    have h2 : trap d b 1 x = 0 := trap_eq_zero_left hd (by linarith)
    rw [h2]
    have := trap_le_one d 0 a x
    linarith

/-- Pointwise lower bound: `trap ≤ 1_{[a,b)}`. -/
lemma trap_le_ind {d a b : ℝ} (hd : 0 < d) (x : ℝ) :
    trap d a b x ≤ (if a ≤ x ∧ x < b then (1:ℝ) else 0) := by
  split_ifs with h
  · exact trap_le_one _ _ _ _
  · exact le_of_eq (trap_le_indicator hd h)

/-- Pointwise upper bound: `1_{[a,b)} ≤ outer`. -/
lemma ind_le_outer {d a b : ℝ} (hd : 0 < d) (hab : a ≤ b) (x : ℝ) :
    (if a ≤ x ∧ x < b then (1:ℝ) else 0) ≤ outer d a b x := by
  split_ifs with h
  · rw [outer, trap_eq_zero_right hd h.1, trap_eq_zero_left hd h.2.le]
    norm_num
  · exact outer_nonneg hd hab x

end

end TuringTask
