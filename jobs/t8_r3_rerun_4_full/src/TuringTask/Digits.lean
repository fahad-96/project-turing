import TuringTask.Equidistribution

namespace TuringTask

open Filter

private theorem irrational_logb_ten_two : Irrational (Real.logb 10 2) := by
  rw [irrational_iff_ne_rational]
  intro a b hb hab
  have hlog10 : Real.log (10 : ℝ) ≠ 0 := by positivity
  have hxpos : 0 < Real.logb 10 2 := Real.logb_pos (by norm_num) (by norm_num)
  have habpos : 0 < (a : ℝ) / (b : ℝ) := hab ▸ hxpos
  let m := a.natAbs
  let k := b.natAbs
  have hk : k ≠ 0 := by
    simpa [k] using hb
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  have hmk : Real.logb 10 2 = (m : ℝ) / (k : ℝ) := by
    calc
      Real.logb 10 2 = (a : ℝ) / (b : ℝ) := hab
      _ = |(a : ℝ) / (b : ℝ)| := (abs_of_pos habpos).symm
      _ = |(a : ℝ)| / |(b : ℝ)| := abs_div _ _
      _ = (m : ℝ) / (k : ℝ) := by simp [m, k]
  have hmpos : 0 < m := by
    have : 0 < (m : ℝ) / (k : ℝ) := hmk ▸ hxpos
    have hmR : 0 < (m : ℝ) := by
      rcases div_pos_iff.mp this with h | h
      · exact h.1
      · exact False.elim ((not_lt_of_ge (Nat.cast_nonneg k)) h.2)
    exact_mod_cast hmR
  have hlogs : (k : ℝ) * Real.log 2 = (m : ℝ) * Real.log 10 := by
    rw [Real.logb] at hmk
    field_simp at hmk
    nlinarith
  have hpowsR : (2 : ℝ) ^ k = (10 : ℝ) ^ m := by
    calc
      (2 : ℝ) ^ k = Real.exp (Real.log ((2 : ℝ) ^ k)) :=
        (Real.exp_log (by positivity)).symm
      _ = Real.exp (Real.log ((10 : ℝ) ^ m)) := by
        congr 1
        simpa [Real.log_pow] using hlogs
      _ = (10 : ℝ) ^ m := Real.exp_log (by positivity)
  have hpows : 2 ^ k = 10 ^ m := by exact_mod_cast hpowsR
  have hfive : 5 ∣ 2 ^ k := by
    rw [hpows]
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hmpos)
    rw [hj, pow_succ]
    refine ⟨2 * 10 ^ j, by ring⟩
  have : 5 ∣ 2 := (by norm_num : Nat.Prime 5).dvd_of_dvd_pow hfive
  norm_num at this

private theorem leading_digit_iff (n d : ℕ) (hd : 1 ≤ d) :
    2 ^ (n ^ 2) / 10 ^ Nat.log 10 (2 ^ (n ^ 2)) = d ↔
      Real.logb 10 d ≤ Int.fract ((n : ℝ) ^ 2 * Real.logb 10 2) ∧
        Int.fract ((n : ℝ) ^ 2 * Real.logb 10 2) < Real.logb 10 (d + 1) := by
  let x : ℕ := 2 ^ (n ^ 2)
  let k : ℕ := Nat.log 10 x
  have hx : x ≠ 0 := by simp [x]
  have hxpos : 0 < (x : ℝ) := by positivity
  have hden : 0 < 10 ^ k := by positivity
  have hdenR : 0 < (10 : ℝ) ^ k := by positivity
  have ht : Real.logb 10 (x : ℝ) = (n : ℝ) ^ 2 * Real.logb 10 2 := by
    simp [x, Real.logb_pow]
  have hloNat : 10 ^ k ≤ x := Nat.pow_log_le_self 10 hx
  have hhiNat : x < 10 ^ (k + 1) := by
    simpa [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self (by norm_num : 1 < 10) x
  have hloR : (10 : ℝ) ^ k ≤ (x : ℝ) := by exact_mod_cast hloNat
  have hhiR : (x : ℝ) < (10 : ℝ) ^ (k + 1) := by exact_mod_cast hhiNat
  have hlo : (k : ℝ) ≤ Real.logb 10 (x : ℝ) := by
    have h := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 10)
      (by positivity : 0 < (10 : ℝ) ^ k) hxpos).2 hloR
    simpa [Real.logb_pow, Real.logb_self_eq_one] using h
  have hhi : Real.logb 10 (x : ℝ) < (k : ℝ) + 1 := by
    have h := (Real.logb_lt_logb_iff (by norm_num : (1 : ℝ) < 10)
      hxpos (by positivity : 0 < (10 : ℝ) ^ (k + 1))).2 hhiR
    simpa [Real.logb_pow, Real.logb_self_eq_one, Nat.cast_add, Nat.cast_one] using h
  have hfloor : ⌊Real.logb 10 (x : ℝ)⌋ = (k : ℤ) := by
    rw [Int.floor_eq_iff]
    exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩
  have hfract : Int.fract (Real.logb 10 (x : ℝ)) =
      Real.logb 10 ((x : ℝ) / (10 : ℝ) ^ k) := by
    rw [Real.logb_div (ne_of_gt hxpos) (ne_of_gt hdenR), Real.logb_pow]
    simp [Int.fract, hfloor, Real.logb_self_eq_one]
  have hquot : x / 10 ^ k = d ↔ d * 10 ^ k ≤ x ∧ x < (d + 1) * 10 ^ k := by
    constructor
    · intro h
      have hle : d ≤ x / 10 ^ k := by omega
      have hlt : x / 10 ^ k < d + 1 := by omega
      exact ⟨(Nat.le_div_iff_mul_le hden).mp hle,
        (Nat.div_lt_iff_lt_mul hden).mp hlt⟩
    · intro h
      have hle : d ≤ x / 10 ^ k := (Nat.le_div_iff_mul_le hden).mpr h.1
      have hlt : x / 10 ^ k < d + 1 := (Nat.div_lt_iff_lt_mul hden).mpr h.2
      omega
  have hreal : x / 10 ^ k = d ↔
      (d : ℝ) ≤ (x : ℝ) / (10 : ℝ) ^ k ∧
        (x : ℝ) / (10 : ℝ) ^ k < (d + 1 : ℕ) := by
    rw [hquot]
    constructor
    · intro h
      constructor
      · apply (le_div_iff₀ hdenR).2
        exact_mod_cast h.1
      · apply (div_lt_iff₀ hdenR).2
        exact_mod_cast h.2
    · intro h
      constructor
      · have := (le_div_iff₀ hdenR).1 h.1
        exact_mod_cast this
      · have := (div_lt_iff₀ hdenR).1 h.2
        exact_mod_cast this
  change x / 10 ^ k = d ↔ _
  rw [← ht, hfract, hreal]
  have hdR : 0 < (d : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  constructor
  · intro h
    refine ⟨(Real.logb_le_logb (by norm_num) hdR
      (div_pos hxpos hdenR)).2 h.1, ?_⟩
    apply (Real.logb_lt_logb_iff (by norm_num) (div_pos hxpos hdenR)
      (by positivity : 0 < (d : ℝ) + 1)).2
    simpa only [Nat.cast_add, Nat.cast_one] using h.2
  · intro h
    refine ⟨(Real.logb_le_logb (by norm_num) hdR
      (div_pos hxpos hdenR)).1 h.1, ?_⟩
    have h' := (Real.logb_lt_logb_iff (by norm_num) (div_pos hxpos hdenR)
      (by positivity : 0 < (d : ℝ) + 1)).1 h.2
    simpa only [Nat.cast_add, Nat.cast_one] using h'

theorem freq_lead_sq_aux (d : Nat) (hd : 1 <= d) (hd' : d <= 9) :
    Filter.Tendsto (fun N : Nat => (((Finset.range N).filter (fun n : Nat =>
      2 ^ (n ^ 2) / 10 ^ Nat.log 10 (2 ^ (n ^ 2)) = d)).card : Real) / N)
      Filter.atTop (nhds (Real.logb 10 (((d : Real) + 1) / d))) := by
  let P : Polynomial ℝ := Polynomial.monomial 2 (Real.logb 10 2)
  have hc : Real.logb 10 2 ≠ 0 := irrational_logb_ten_two.ne_zero
  have hP : Irrational P.leadingCoeff := by
    simpa [P, hc] using irrational_logb_ten_two
  have hdeg : 1 ≤ P.natDegree := by
    simp [P, hc]
  have hdpos : 0 < (d : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hd1pos : 0 < ((d + 1 : ℕ) : ℝ) := by positivity
  have ha : 0 ≤ Real.logb 10 (d : ℝ) :=
    (Real.logb_nonneg_iff (by norm_num : (1 : ℝ) < 10) hdpos).2 (by exact_mod_cast hd)
  have hab : Real.logb 10 (d : ℝ) ≤ Real.logb 10 ((d + 1 : ℕ) : ℝ) :=
    (Real.logb_le_logb (by norm_num) hdpos hd1pos).2 (by exact_mod_cast Nat.le_succ d)
  have hb : Real.logb 10 ((d + 1 : ℕ) : ℝ) ≤ 1 := by
    rw [← Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 10)]
    apply (Real.logb_le_logb (by norm_num) hd1pos (by norm_num)).2
    exact_mod_cast (Nat.add_le_add_right hd' 1)
  have hfreq := Equidistribution.freq_poly P hP hdeg
    (Real.logb 10 (d : ℝ)) (Real.logb 10 ((d + 1 : ℕ) : ℝ)) ha hab hb
  have hfilters (N : ℕ) :
      (Finset.range N).filter (fun n : ℕ =>
        2 ^ (n ^ 2) / 10 ^ Nat.log 10 (2 ^ (n ^ 2)) = d) =
      (Finset.range N).filter (fun n : ℕ =>
        Real.logb 10 (d : ℝ) ≤ Int.fract (Polynomial.eval (n : ℝ) P) ∧
          Int.fract (Polynomial.eval (n : ℝ) P) < Real.logb 10 ((d + 1 : ℕ) : ℝ)) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    apply and_congr_right
    intro hn
    simpa [P, mul_comm] using leading_digit_iff n d hd
  have hfun : (fun N : ℕ => (((Finset.range N).filter (fun n : ℕ =>
      2 ^ (n ^ 2) / 10 ^ Nat.log 10 (2 ^ (n ^ 2)) = d)).card : ℝ) / N) =
      (fun N : ℕ => (((Finset.range N).filter (fun n : ℕ =>
        Real.logb 10 (d : ℝ) ≤ Int.fract (Polynomial.eval (n : ℝ) P) ∧
          Int.fract (Polynomial.eval (n : ℝ) P) <
            Real.logb 10 ((d + 1 : ℕ) : ℝ))).card : ℝ) / N) := by
    funext N
    rw [hfilters N]
  rw [hfun]
  convert hfreq using 1
  rw [Real.logb_div]
  · norm_num
  · positivity
  · positivity

end TuringTask
