import TuringTask.Equidistribution

namespace TuringTask

open Filter

/-- Uniform interval frequencies for the quadratic sequence `n^2 x` modulo one. -/
theorem freq_sq_unif_aux (x : Real) (hx : Irrational x) (e : Real) (he : 0 < e) :
    exists N0 : Nat, forall N : Nat, N0 <= N -> forall a b : Real, 0 <= a -> a <= b -> b <= 1 ->
      abs ((((Finset.range N).filter (fun n : Nat =>
        a <= Int.fract ((n : Real) ^ 2 * x) /\ Int.fract ((n : Real) ^ 2 * x) < b)).card : Real)
        / N - (b - a)) < e := by
  classical
  let P : Polynomial Real := Polynomial.C x * Polynomial.X ^ 2
  have hP : Irrational P.leadingCoeff := by
    simpa [P, Polynomial.leadingCoeff_C_mul_X_pow] using hx
  have hdeg : 1 <= P.natDegree := by
    change 1 <= (Polynomial.C x * Polynomial.X ^ 2).natDegree
    rw [Polynomial.natDegree_C_mul_X_pow 2 x hx.ne_zero]
    norm_num
  let F : Nat -> Real -> Real := fun N t =>
    (((Finset.range N).filter (fun n : Nat =>
      Int.fract ((n : Real) ^ 2 * x) < t)).card : Real) / N

  obtain ⟨m, hm⟩ := exists_nat_gt (4 / e)
  have hm0r : 0 < (m : Real) := by
    have hfour : 0 < 4 / e := div_pos (by norm_num) he
    exact lt_trans hfour hm
  have hm0 : 0 < m := by exact_mod_cast hm0r
  have hmesh : 2 / (m : Real) < e / 2 := by
    have hfour : 4 < (m : Real) * e := (div_lt_iff₀ he).mp hm
    apply (div_lt_iff₀ hm0r).2
    nlinarith

  have hfixed (k : Nat) (hk : k <= m) :
      Tendsto (fun N => F N ((k : Real) / m)) atTop
        (nhds ((k : Real) / m)) := by
    have hq0 : 0 <= (k : Real) / m := div_nonneg (Nat.cast_nonneg _) hm0r.le
    have hq1 : (k : Real) / m <= 1 := by
      apply (div_le_iff₀ hm0r).2
      have : (k : Real) <= (m : Real) := by exact_mod_cast hk
      simpa using this
    have heval (n : Nat) : Polynomial.eval (n : Real) P = (n : Real) ^ 2 * x := by
      simp [P]
      ring
    simpa only [F, heval, Int.fract_nonneg, true_and, zero_add, sub_zero] using
      (Equidistribution.freq_poly P hP hdeg 0 ((k : Real) / m)
        (le_refl 0) hq0 hq1)

  have hthreshold : forall k : Fin (m + 1), exists M : Nat, forall N : Nat, M <= N ->
      abs (F N ((k : Nat) / (m : Real)) - (k : Real) / m) < e / 4 := by
    intro k
    have hk : (k : Nat) <= m := Nat.lt_succ_iff.mp k.isLt
    obtain ⟨M, hM⟩ := (Metric.tendsto_atTop.mp (hfixed k hk)) (e / 4) (by positivity)
    refine ⟨M, fun N hN => ?_⟩
    simpa [Real.dist_eq] using hM N hN
  choose M hM using hthreshold
  let N0 := Finset.univ.sup M
  refine ⟨N0, fun N hN => ?_⟩

  have hgrid (k : Nat) (hk : k <= m) :
      abs (F N ((k : Real) / m) - (k : Real) / m) < e / 4 := by
    let k' : Fin (m + 1) := ⟨k, Nat.lt_succ_of_le hk⟩
    apply hM k' N
    exact (Finset.le_sup (f := M) (Finset.mem_univ k')).trans hN

  have hmono {s t : Real} (hst : s <= t) : F N s <= F N t := by
    have hcard :
        (((Finset.range N).filter (fun n : Nat =>
          Int.fract ((n : Real) ^ 2 * x) < s)).card : Real) <=
        (((Finset.range N).filter (fun n : Nat =>
          Int.fract ((n : Real) ^ 2 * x) < t)).card : Real) := by
      exact_mod_cast Finset.card_le_card (by
        intro n hn
        simp only [Finset.mem_filter] at hn ⊢
        exact ⟨hn.1, hn.2.trans_le hst⟩)
    exact div_le_div_of_nonneg_right hcard (Nat.cast_nonneg N)

  have hCDF (t : Real) (ht0 : 0 <= t) (ht1 : t <= 1) :
      abs (F N t - t) < e / 4 + 1 / (m : Real) := by
    by_cases ht : t = 1
    · subst t
      have hmm : (m : Real) / m = 1 := div_self (ne_of_gt hm0r)
      have h := hgrid m le_rfl
      rw [hmm] at h
      exact h.trans_le (le_add_of_nonneg_right (one_div_nonneg.mpr hm0r.le))
    · have htlt : t < 1 := lt_of_le_of_ne ht1 ht
      let k : Nat := ⌊(m : Real) * t⌋₊
      have hmt0 : 0 <= (m : Real) * t := mul_nonneg hm0r.le ht0
      have hklt : k < m := by
        change ⌊(m : Real) * t⌋₊ < m
        rw [Nat.floor_lt hmt0]
        nlinarith
      have hk : k <= m := hklt.le
      have hks : k + 1 <= m := hklt
      have hlow : (k : Real) / m <= t := by
        apply (div_le_iff₀ hm0r).2
        simpa [k, mul_comm] using (Nat.floor_le hmt0)
      have hupp : t < ((k + 1 : Nat) : Real) / m := by
        apply (lt_div_iff₀ hm0r).2
        simpa [k, mul_comm] using (Nat.lt_floor_add_one ((m : Real) * t))
      have hwidthLow : t - (k : Real) / m < 1 / (m : Real) := by
        have hid : (((k + 1 : Nat) : Real) / m) =
            (k : Real) / m + 1 / (m : Real) := by
          push_cast
          ring
        rw [hid] at hupp
        linarith
      have hwidthUpp : (((k + 1 : Nat) : Real) / m) - t <= 1 / (m : Real) := by
        have hid : (((k + 1 : Nat) : Real) / m) =
            (k : Real) / m + 1 / (m : Real) := by
          push_cast
          ring
        rw [hid]
        linarith
      have hgLow := (abs_lt.mp (hgrid k hk)).1
      have hgUpp := (abs_lt.mp (hgrid (k + 1) hks)).2
      have hmLow := hmono hlow
      have hmUpp := hmono hupp.le
      rw [abs_lt]
      constructor <;> linarith

  intro a b ha hab hb
  have hfa := hCDF a ha (hab.trans hb)
  have hfb := hCDF b (ha.trans hab) hb
  let A := (Finset.range N).filter (fun n : Nat =>
    Int.fract ((n : Real) ^ 2 * x) < a)
  let B := (Finset.range N).filter (fun n : Nat =>
    Int.fract ((n : Real) ^ 2 * x) < b)
  have hAB : A ⊆ B := by
    intro n hn
    simp only [A, B, Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, hn.2.trans_le hab⟩
  have hinter :
      (Finset.range N).filter (fun n : Nat =>
        a <= Int.fract ((n : Real) ^ 2 * x) /\
          Int.fract ((n : Real) ^ 2 * x) < b) = B \ A := by
    ext n
    simp only [A, B, Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨hn, hna, hnb⟩
      exact ⟨⟨hn, hnb⟩, fun h => not_lt_of_ge hna h.2⟩
    · rintro ⟨⟨hn, hnb⟩, hna⟩
      exact ⟨hn, le_of_not_gt (fun h => hna ⟨hn, h⟩), hnb⟩
  have hrewrite :
      ((((Finset.range N).filter (fun n : Nat =>
        a <= Int.fract ((n : Real) ^ 2 * x) /\
          Int.fract ((n : Real) ^ 2 * x) < b)).card : Real) / N - (b - a)) =
        (F N b - b) - (F N a - a) := by
    rw [hinter, Finset.card_sdiff, Finset.inter_eq_left.mpr hAB,
      Nat.cast_sub (Finset.card_le_card hAB)]
    simp only [F, A, B]
    ring
  rw [hrewrite]
  calc
    abs ((F N b - b) - (F N a - a)) <=
        abs (F N b - b) + abs (F N a - a) := abs_sub _ _
    _ < e := by
      have hmesh' : 2 * (1 / (m : Real)) < e / 2 := by
        simpa [div_eq_mul_inv] using hmesh
      linarith

end TuringTask
