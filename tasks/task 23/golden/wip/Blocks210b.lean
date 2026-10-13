import Mathlib
import TuringTask.Blocks210a

/-!
# The units for `x ^ 2 - D y ^ 2 = 1`, part two

The same for `D = 21, 30, 35, 42, 70, 105, 210`.
-/

namespace TuringTask

/-- `x ^ 2 - 21 y ^ 2 = 1` with `y` smooth for `210`, unit `55 + 12 √21`. -/
lemma blk210_21 {x y : ℕ} (h : (x : ℤ) ^ 2 - 21 * y ^ 2 = 1) (hy : 0 < y)
    (hs : Smooth 210 y) : x ∈ ({55} : Finset ℕ) := by
  have hσ : ((55 : ℕ) : ℤ) ^ 2 - ((21 : ℕ) : ℤ) * ((12 : ℕ) : ℤ) ^ 2 = 1 := by norm_num
  obtain ⟨k, rfl, rfl⟩ := pell_descent hσ (Or.inl rfl) (by norm_num) (by norm_num)
    (hmin_of_sqrt (Or.inl rfl) (by intro y h1 h2; interval_cases y <;> norm_num))
    _ _ (Or.inl (by exact_mod_cast h))
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hy)
  have hp := smooth_index hσ (Or.inl rfl) (by norm_num) (by norm_num) (R := 7)
    (rank210 (r2 := 1) (r3 := 1) (r5 := 2) (r7 := 7)
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩)
    (by
      intro p hp hd
      have := Nat.le_of_dvd (by norm_num) hd
      interval_cases p <;> first | omega | (exfalso; norm_num at hp)) hs
  have e2 : ¬ 2 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 120) (m := 11)
    (by decide) (by norm_num) (by norm_num)
  have e3 : ¬ 3 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 36) (m := 4033)
    (by decide) (by norm_num) (by norm_num)
  have e5 : ¬ 5 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 12) (m := 146373701)
    (by decide) (by norm_num) (by norm_num)
  have e7 : ¬ 7 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 84) (m := 252975574657)
    (by decide) (by norm_num) (by norm_num)
  have e11 := not_dvd_of_gt (p := 11) (by norm_num) hp (by norm_num)
  have e13 := not_dvd_of_gt (p := 13) (by norm_num) hp (by norm_num)
  have hk1 : k = 1 := by
    have := dvd_of_bounds hk (le_13_of_le hp (by norm_num)) e2 e3 e5 e7 e11 e13
    simpa using this
  subst hk1
  decide

/-- `x ^ 2 - 30 y ^ 2 = 1` with `y` smooth for `210`, unit `11 + 2 √30`. -/
lemma blk210_30 {x y : ℕ} (h : (x : ℤ) ^ 2 - 30 * y ^ 2 = 1) (hy : 0 < y)
    (hs : Smooth 210 y) : x ∈ ({11} : Finset ℕ) := by
  have hσ : ((11 : ℕ) : ℤ) ^ 2 - ((30 : ℕ) : ℤ) * ((2 : ℕ) : ℤ) ^ 2 = 1 := by norm_num
  obtain ⟨k, rfl, rfl⟩ := pell_descent hσ (Or.inl rfl) (by norm_num) (by norm_num)
    (hmin_of_sqrt (Or.inl rfl) (by intro y h1 h2; obtain rfl : y = 1 := (by omega); norm_num))
    _ _ (Or.inl (by exact_mod_cast h))
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hy)
  have hp := smooth_index hσ (Or.inl rfl) (by norm_num) (by norm_num) (R := 5)
    (rank210 (r2 := 1) (r3 := 3) (r5 := 5) (r7 := 3)
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩)
    (bR_of_le (by norm_num) (by norm_num)) hs
  have e2 : ¬ 2 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 4) (m := 11)
    (by decide) (by norm_num) (by norm_num)
  have e3 : ¬ 3 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 42) (m := 23)
    (by decide) (by norm_num) (by norm_num)
  have e5 : ¬ 5 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 10) (m := 46561)
    (by decide) (by norm_num) (by norm_num)
  have e7 := not_dvd_of_gt (p := 7) (by norm_num) hp (by norm_num)
  have e11 := not_dvd_of_gt (p := 11) (by norm_num) hp (by norm_num)
  have e13 := not_dvd_of_gt (p := 13) (by norm_num) hp (by norm_num)
  have hk1 : k = 1 := by
    have := dvd_of_bounds hk (le_13_of_le hp (by norm_num)) e2 e3 e5 e7 e11 e13
    simpa using this
  subst hk1
  decide

/-- `x ^ 2 - 35 y ^ 2 = 1` with `y` smooth for `210`, unit `6 + 1 √35`. -/
lemma blk210_35 {x y : ℕ} (h : (x : ℤ) ^ 2 - 35 * y ^ 2 = 1) (hy : 0 < y)
    (hs : Smooth 210 y) : x ∈ ({6, 71} : Finset ℕ) := by
  have hσ : ((6 : ℕ) : ℤ) ^ 2 - ((35 : ℕ) : ℤ) * ((1 : ℕ) : ℤ) ^ 2 = 1 := by norm_num
  obtain ⟨k, rfl, rfl⟩ := pell_descent hσ (Or.inl rfl) (by norm_num) (by norm_num)
    (hmin_of_sqrt (Or.inl rfl) (by intro y h1 h2; omega))
    _ _ (Or.inl (by exact_mod_cast h))
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hy)
  have hp := smooth_index hσ (Or.inl rfl) (by norm_num) (by norm_num) (R := 7)
    (rank210 (r2 := 2) (r3 := 2) (r5 := 5) (r7 := 7)
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩)
    (bR_of_le (by norm_num) (by norm_num)) hs
  have e2 : ¬ 2 ^ (1 + 1) ∣ k := not_dvd_of_split hs (s := 24) (m := 71)
    (by decide) (by norm_num) (by norm_num)
  have e3 : ¬ 3 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 1) (m := 143)
    (by decide) (by norm_num) (by norm_num)
  have e5 : ¬ 5 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 5) (m := 4061)
    (by decide) (by norm_num) (by norm_num)
  have e7 : ¬ 7 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 7) (m := 411881)
    (by decide) (by norm_num) (by norm_num)
  have e11 := not_dvd_of_gt (p := 11) (by norm_num) hp (by norm_num)
  have e13 := not_dvd_of_gt (p := 13) (by norm_num) hp (by norm_num)
  have hL : k ∣ 2 := by
    have := dvd_of_bounds hk (le_13_of_le hp (by norm_num)) e2 e3 e5 e7 e11 e13
    norm_num at this
    exact this
  have key : ∀ d ∈ Nat.divisors 2, 
      pX 35 6 1 d ∈ ({6, 71} : Finset ℕ) := by
    decide
  exact key k (Nat.mem_divisors.mpr ⟨hL, by norm_num⟩) 

/-- `x ^ 2 - 42 y ^ 2 = 1` with `y` smooth for `210`, unit `13 + 2 √42`. -/
lemma blk210_42 {x y : ℕ} (h : (x : ℤ) ^ 2 - 42 * y ^ 2 = 1) (hy : 0 < y)
    (hs : Smooth 210 y) : x ∈ ({13, 8749} : Finset ℕ) := by
  have hσ : ((13 : ℕ) : ℤ) ^ 2 - ((42 : ℕ) : ℤ) * ((2 : ℕ) : ℤ) ^ 2 = 1 := by norm_num
  obtain ⟨k, rfl, rfl⟩ := pell_descent hσ (Or.inl rfl) (by norm_num) (by norm_num)
    (hmin_of_sqrt (Or.inl rfl) (by intro y h1 h2; obtain rfl : y = 1 := (by omega); norm_num))
    _ _ (Or.inl (by exact_mod_cast h))
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hy)
  have hp := smooth_index hσ (Or.inl rfl) (by norm_num) (by norm_num) (R := 7)
    (rank210 (r2 := 1) (r3 := 3) (r5 := 3) (r7 := 7)
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩)
    (bR_of_le (by norm_num) (by norm_num)) hs
  have e2 : ¬ 2 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 4) (m := 13)
    (by decide) (by norm_num) (by norm_num)
  have e3 : ¬ 3 ^ (1 + 1) ∣ k := not_dvd_of_split hs (s := 4050) (m := 102060001)
    (by decide) (by norm_num) (by norm_num)
  have e5 : ¬ 5 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 2) (m := 454949)
    (by decide) (by norm_num) (by norm_num)
  have e7 : ¬ 7 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 14) (m := 43804993)
    (by decide) (by norm_num) (by norm_num)
  have e11 := not_dvd_of_gt (p := 11) (by norm_num) hp (by norm_num)
  have e13 := not_dvd_of_gt (p := 13) (by norm_num) hp (by norm_num)
  have hL : k ∣ 3 := by
    have := dvd_of_bounds hk (le_13_of_le hp (by norm_num)) e2 e3 e5 e7 e11 e13
    norm_num at this
    exact this
  have key : ∀ d ∈ Nat.divisors 3, 
      pX 42 13 2 d ∈ ({13, 8749} : Finset ℕ) := by
    decide
  exact key k (Nat.mem_divisors.mpr ⟨hL, by norm_num⟩) 

/-- `x ^ 2 - 70 y ^ 2 = 1` with `y` smooth for `210`, unit `251 + 30 √70`. -/
lemma blk210_70 {x y : ℕ} (h : (x : ℤ) ^ 2 - 70 * y ^ 2 = 1) (hy : 0 < y)
    (hs : Smooth 210 y) : x ∈ ({251} : Finset ℕ) := by
  have hσ : ((251 : ℕ) : ℤ) ^ 2 - ((70 : ℕ) : ℤ) * ((30 : ℕ) : ℤ) ^ 2 = 1 := by norm_num
  obtain ⟨k, rfl, rfl⟩ := pell_descent hσ (Or.inl rfl) (by norm_num) (by norm_num)
    (hmin_of_sqrt (Or.inl rfl) (by intro y h1 h2; interval_cases y <;> norm_num))
    _ _ (Or.inl (by exact_mod_cast h))
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hy)
  have hp := smooth_index hσ (Or.inl rfl) (by norm_num) (by norm_num) (R := 7)
    (rank210 (r2 := 1) (r3 := 1) (r5 := 1) (r7 := 7)
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩)
    (by
      intro p hp hd
      have := Nat.le_of_dvd (by norm_num) hd
      interval_cases p <;> first | omega | (exfalso; norm_num at hp)) hs
  have e2 : ¬ 2 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 60) (m := 251)
    (by decide) (by norm_num) (by norm_num)
  have e3 : ¬ 3 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 90) (m := 84001)
    (by decide) (by norm_num) (by norm_num)
  have e5 : ¬ 5 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 150) (m := 12701052001)
    (by decide) (by norm_num) (by norm_num)
  have e7 : ¬ 7 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 210) (m := 2286207504504001)
    (by decide) (by norm_num) (by norm_num)
  have e11 := not_dvd_of_gt (p := 11) (by norm_num) hp (by norm_num)
  have e13 := not_dvd_of_gt (p := 13) (by norm_num) hp (by norm_num)
  have hk1 : k = 1 := by
    have := dvd_of_bounds hk (le_13_of_le hp (by norm_num)) e2 e3 e5 e7 e11 e13
    simpa using this
  subst hk1
  decide

/-- `x ^ 2 - 105 y ^ 2 = 1` with `y` smooth for `210`, unit `41 + 4 √105`. -/
lemma blk210_105 {x y : ℕ} (h : (x : ℤ) ^ 2 - 105 * y ^ 2 = 1) (hy : 0 < y)
    (hs : Smooth 210 y) : x ∈ ({41} : Finset ℕ) := by
  have hσ : ((41 : ℕ) : ℤ) ^ 2 - ((105 : ℕ) : ℤ) * ((4 : ℕ) : ℤ) ^ 2 = 1 := by norm_num
  obtain ⟨k, rfl, rfl⟩ := pell_descent hσ (Or.inl rfl) (by norm_num) (by norm_num)
    (hmin_of_sqrt (Or.inl rfl) (by intro y h1 h2; interval_cases y <;> norm_num))
    _ _ (Or.inl (by exact_mod_cast h))
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hy)
  have hp := smooth_index hσ (Or.inl rfl) (by norm_num) (by norm_num) (R := 7)
    (rank210 (r2 := 1) (r3 := 3) (r5 := 5) (r7 := 7)
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩)
    (bR_of_le (by norm_num) (by norm_num)) hs
  have e2 : ¬ 2 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 8) (m := 41)
    (by decide) (by norm_num) (by norm_num)
  have e3 : ¬ 3 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 324) (m := 83)
    (by decide) (by norm_num) (by norm_num)
  have e5 : ¬ 5 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 20) (m := 9038401)
    (by decide) (by norm_num) (by norm_num)
  have e7 : ¬ 7 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 28) (m := 43397235841)
    (by decide) (by norm_num) (by norm_num)
  have e11 := not_dvd_of_gt (p := 11) (by norm_num) hp (by norm_num)
  have e13 := not_dvd_of_gt (p := 13) (by norm_num) hp (by norm_num)
  have hk1 : k = 1 := by
    have := dvd_of_bounds hk (le_13_of_le hp (by norm_num)) e2 e3 e5 e7 e11 e13
    simpa using this
  subst hk1
  decide

/-- `x ^ 2 - 210 y ^ 2 = 1` with `y` smooth for `210`, unit `29 + 2 √210`. -/
lemma blk210_210 {x y : ℕ} (h : (x : ℤ) ^ 2 - 210 * y ^ 2 = 1) (hy : 0 < y)
    (hs : Smooth 210 y) : x ∈ ({29} : Finset ℕ) := by
  have hσ : ((29 : ℕ) : ℤ) ^ 2 - ((210 : ℕ) : ℤ) * ((2 : ℕ) : ℤ) ^ 2 = 1 := by norm_num
  obtain ⟨k, rfl, rfl⟩ := pell_descent hσ (Or.inl rfl) (by norm_num) (by norm_num)
    (hmin_of_sqrt (Or.inl rfl) (by intro y h1 h2; obtain rfl : y = 1 := (by omega); norm_num))
    _ _ (Or.inl (by exact_mod_cast h))
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hy)
  have hp := smooth_index hσ (Or.inl rfl) (by norm_num) (by norm_num) (R := 7)
    (rank210 (r2 := 1) (r3 := 3) (r5 := 5) (r7 := 7)
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩)
    (bR_of_le (by norm_num) (by norm_num)) hs
  have e2 : ¬ 2 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 4) (m := 29)
    (by decide) (by norm_num) (by norm_num)
  have e3 : ¬ 3 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 6) (m := 1121)
    (by decide) (by norm_num) (by norm_num)
  have e5 : ¬ 5 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 10) (m := 2261281)
    (by decide) (by norm_num) (by norm_num)
  have e7 : ¬ 7 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 14) (m := 5430304321)
    (by decide) (by norm_num) (by norm_num)
  have e11 := not_dvd_of_gt (p := 11) (by norm_num) hp (by norm_num)
  have e13 := not_dvd_of_gt (p := 13) (by norm_num) hp (by norm_num)
  have hk1 : k = 1 := by
    have := dvd_of_bounds hk (le_13_of_le hp (by norm_num)) e2 e3 e5 e7 e11 e13
    simpa using this
  subst hk1
  decide

end TuringTask
