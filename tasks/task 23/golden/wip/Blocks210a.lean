import Mathlib
import TuringTask.PellDescent

/-!
# The units for `x ^ 2 - D y ^ 2 = 1`, part one

For `D = 2, 3, 5, 6, 7, 10, 14, 15`: the unit `a + b √D` (minimal by a `Nat.sqrt` check), one
index per prime `q ∣ 210` with `q ∣ pY r`, and explicit factors prime to `210` of the excluded
`pY j`. Each lemma lists the values of `x` when `y` is smooth for `210`.
-/

namespace TuringTask

/-- `x ^ 2 - 2 y ^ 2 = 1` with `y` smooth for `210`, unit `3 + 2 √2`. -/
lemma blk210_2 {x y : ℕ} (h : (x : ℤ) ^ 2 - 2 * y ^ 2 = 1) (hy : 0 < y)
    (hs : Smooth 210 y) : x ∈ ({3, 17, 99} : Finset ℕ) := by
  have hσ : ((3 : ℕ) : ℤ) ^ 2 - ((2 : ℕ) : ℤ) * ((2 : ℕ) : ℤ) ^ 2 = 1 := by norm_num
  obtain ⟨k, rfl, rfl⟩ := pell_descent hσ (Or.inl rfl) (by norm_num) (by norm_num)
    (hmin_of_sqrt (Or.inl rfl) (by intro y h1 h2; obtain rfl : y = 1 := (by omega); norm_num))
    _ _ (Or.inl (by exact_mod_cast h))
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hy)
  have hp := smooth_index hσ (Or.inl rfl) (by norm_num) (by norm_num) (R := 3)
    (rank210 (r2 := 1) (r3 := 2) (r5 := 3) (r7 := 3)
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩)
    (bR_of_le (by norm_num) (by norm_num)) hs
  have e2 : ¬ 2 ^ (1 + 1) ∣ k := not_dvd_of_split hs (s := 24) (m := 17)
    (by decide) (by norm_num) (by norm_num)
  have e3 : ¬ 3 ^ (1 + 1) ∣ k := not_dvd_of_split hs (s := 70) (m := 39203)
    (by decide) (by norm_num) (by norm_num)
  have e5 := not_dvd_of_gt (p := 5) (by norm_num) hp (by norm_num)
  have e7 := not_dvd_of_gt (p := 7) (by norm_num) hp (by norm_num)
  have e11 := not_dvd_of_gt (p := 11) (by norm_num) hp (by norm_num)
  have e13 := not_dvd_of_gt (p := 13) (by norm_num) hp (by norm_num)
  have c6 : ¬ 6 ∣ k := not_dvd_of_split hs (s := 1260) (m := 11) (by decide) (by norm_num)
    (by norm_num)
  have hL : k ∣ 6 := by
    have := dvd_of_bounds hk (le_13_of_le hp (by norm_num)) e2 e3 e5 e7 e11 e13
    norm_num at this
    exact this
  have key : ∀ d ∈ Nat.divisors 6, ¬ 6 ∣ d → 
      pX 2 3 2 d ∈ ({3, 17, 99} : Finset ℕ) := by
    decide
  exact key k (Nat.mem_divisors.mpr ⟨hL, by norm_num⟩) c6

/-- `x ^ 2 - 3 y ^ 2 = 1` with `y` smooth for `210`, unit `2 + 1 √3`. -/
lemma blk210_3 {x y : ℕ} (h : (x : ℤ) ^ 2 - 3 * y ^ 2 = 1) (hy : 0 < y)
    (hs : Smooth 210 y) : x ∈ ({2, 7, 26, 97} : Finset ℕ) := by
  have hσ : ((2 : ℕ) : ℤ) ^ 2 - ((3 : ℕ) : ℤ) * ((1 : ℕ) : ℤ) ^ 2 = 1 := by norm_num
  obtain ⟨k, rfl, rfl⟩ := pell_descent hσ (Or.inl rfl) (by norm_num) (by norm_num)
    (hmin_of_sqrt (Or.inl rfl) (by intro y h1 h2; omega))
    _ _ (Or.inl (by exact_mod_cast h))
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hy)
  have hp := smooth_index hσ (Or.inl rfl) (by norm_num) (by norm_num) (R := 4)
    (rank210 (r2 := 2) (r3 := 3) (r5 := 3) (r7 := 4)
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩)
    (bR_of_le (by norm_num) (by norm_num)) hs
  have e2 : ¬ 2 ^ (2 + 1) ∣ k := not_dvd_of_split hs (s := 112) (m := 97)
    (by decide) (by norm_num) (by norm_num)
  have e3 : ¬ 3 ^ (1 + 1) ∣ k := not_dvd_of_split hs (s := 45) (m := 901)
    (by decide) (by norm_num) (by norm_num)
  have e5 := not_dvd_of_gt (p := 5) (by norm_num) hp (by norm_num)
  have e7 := not_dvd_of_gt (p := 7) (by norm_num) hp (by norm_num)
  have e11 := not_dvd_of_gt (p := 11) (by norm_num) hp (by norm_num)
  have e13 := not_dvd_of_gt (p := 13) (by norm_num) hp (by norm_num)
  have c6 : ¬ 6 ∣ k := not_dvd_of_split hs (s := 60) (m := 13) (by decide) (by norm_num)
    (by norm_num)
  have hL : k ∣ 12 := by
    have := dvd_of_bounds hk (le_13_of_le hp (by norm_num)) e2 e3 e5 e7 e11 e13
    norm_num at this
    exact this
  have key : ∀ d ∈ Nat.divisors 12, ¬ 6 ∣ d → 
      pX 3 2 1 d ∈ ({2, 7, 26, 97} : Finset ℕ) := by
    decide
  exact key k (Nat.mem_divisors.mpr ⟨hL, by norm_num⟩) c6

/-- `x ^ 2 - 5 y ^ 2 = 1` with `y` smooth for `210`, unit `9 + 4 √5`. -/
lemma blk210_5 {x y : ℕ} (h : (x : ℤ) ^ 2 - 5 * y ^ 2 = 1) (hy : 0 < y)
    (hs : Smooth 210 y) : x ∈ ({9, 161} : Finset ℕ) := by
  have hσ : ((9 : ℕ) : ℤ) ^ 2 - ((5 : ℕ) : ℤ) * ((4 : ℕ) : ℤ) ^ 2 = 1 := by norm_num
  obtain ⟨k, rfl, rfl⟩ := pell_descent hσ (Or.inl rfl) (by norm_num) (by norm_num)
    (hmin_of_sqrt (Or.inl rfl) (by intro y h1 h2; interval_cases y <;> norm_num))
    _ _ (Or.inl (by exact_mod_cast h))
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hy)
  have hp := smooth_index hσ (Or.inl rfl) (by norm_num) (by norm_num) (R := 5)
    (rank210 (r2 := 1) (r3 := 2) (r5 := 5) (r7 := 4)
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩)
    (bR_of_le (by norm_num) (by norm_num)) hs
  have e2 : ¬ 2 ^ (1 + 1) ∣ k := not_dvd_of_split hs (s := 1008) (m := 23)
    (by decide) (by norm_num) (by norm_num)
  have e3 : ¬ 3 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 4) (m := 323)
    (by decide) (by norm_num) (by norm_num)
  have e5 : ¬ 5 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 20) (m := 20801)
    (by decide) (by norm_num) (by norm_num)
  have e7 := not_dvd_of_gt (p := 7) (by norm_num) hp (by norm_num)
  have e11 := not_dvd_of_gt (p := 11) (by norm_num) hp (by norm_num)
  have e13 := not_dvd_of_gt (p := 13) (by norm_num) hp (by norm_num)
  have hL : k ∣ 2 := by
    have := dvd_of_bounds hk (le_13_of_le hp (by norm_num)) e2 e3 e5 e7 e11 e13
    norm_num at this
    exact this
  have key : ∀ d ∈ Nat.divisors 2, 
      pX 5 9 4 d ∈ ({9, 161} : Finset ℕ) := by
    decide
  exact key k (Nat.mem_divisors.mpr ⟨hL, by norm_num⟩) 

/-- `x ^ 2 - 6 y ^ 2 = 1` with `y` smooth for `210`, unit `5 + 2 √6`. -/
lemma blk210_6 {x y : ℕ} (h : (x : ℤ) ^ 2 - 6 * y ^ 2 = 1) (hy : 0 < y)
    (hs : Smooth 210 y) : x ∈ ({5, 49, 4801} : Finset ℕ) := by
  have hσ : ((5 : ℕ) : ℤ) ^ 2 - ((6 : ℕ) : ℤ) * ((2 : ℕ) : ℤ) ^ 2 = 1 := by norm_num
  obtain ⟨k, rfl, rfl⟩ := pell_descent hσ (Or.inl rfl) (by norm_num) (by norm_num)
    (hmin_of_sqrt (Or.inl rfl) (by intro y h1 h2; obtain rfl : y = 1 := (by omega); norm_num))
    _ _ (Or.inl (by exact_mod_cast h))
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hy)
  have hp := smooth_index hσ (Or.inl rfl) (by norm_num) (by norm_num) (R := 4)
    (rank210 (r2 := 1) (r3 := 3) (r5 := 2) (r7 := 4)
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩)
    (bR_of_le (by norm_num) (by norm_num)) hs
  have e2 : ¬ 2 ^ (2 + 1) ∣ k := not_dvd_of_split hs (s := 3920) (m := 4801)
    (by decide) (by norm_num) (by norm_num)
  have e3 : ¬ 3 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 18) (m := 11)
    (by decide) (by norm_num) (by norm_num)
  have e5 := not_dvd_of_gt (p := 5) (by norm_num) hp (by norm_num)
  have e7 := not_dvd_of_gt (p := 7) (by norm_num) hp (by norm_num)
  have e11 := not_dvd_of_gt (p := 11) (by norm_num) hp (by norm_num)
  have e13 := not_dvd_of_gt (p := 13) (by norm_num) hp (by norm_num)
  have hL : k ∣ 4 := by
    have := dvd_of_bounds hk (le_13_of_le hp (by norm_num)) e2 e3 e5 e7 e11 e13
    norm_num at this
    exact this
  have key : ∀ d ∈ Nat.divisors 4, 
      pX 6 5 2 d ∈ ({5, 49, 4801} : Finset ℕ) := by
    decide
  exact key k (Nat.mem_divisors.mpr ⟨hL, by norm_num⟩) 

/-- `x ^ 2 - 7 y ^ 2 = 1` with `y` smooth for `210`, unit `8 + 3 √7`. -/
lemma blk210_7 {x y : ℕ} (h : (x : ℤ) ^ 2 - 7 * y ^ 2 = 1) (hy : 0 < y)
    (hs : Smooth 210 y) : x ∈ ({8, 127} : Finset ℕ) := by
  have hσ : ((8 : ℕ) : ℤ) ^ 2 - ((7 : ℕ) : ℤ) * ((3 : ℕ) : ℤ) ^ 2 = 1 := by norm_num
  obtain ⟨k, rfl, rfl⟩ := pell_descent hσ (Or.inl rfl) (by norm_num) (by norm_num)
    (hmin_of_sqrt (Or.inl rfl) (by intro y h1 h2; interval_cases y <;> norm_num))
    _ _ (Or.inl (by exact_mod_cast h))
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hy)
  have hp := smooth_index hσ (Or.inl rfl) (by norm_num) (by norm_num) (R := 7)
    (rank210 (r2 := 2) (r3 := 1) (r5 := 3) (r7 := 7)
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩)
    (bR_of_le (by norm_num) (by norm_num)) hs
  have e2 : ¬ 2 ^ (1 + 1) ∣ k := not_dvd_of_split hs (s := 96) (m := 127)
    (by decide) (by norm_num) (by norm_num)
  have e3 : ¬ 3 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 45) (m := 17)
    (by decide) (by norm_num) (by norm_num)
  have e5 : ¬ 5 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 3) (m := 64769)
    (by decide) (by norm_num) (by norm_num)
  have e7 : ¬ 7 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 21) (m := 2350153)
    (by decide) (by norm_num) (by norm_num)
  have e11 := not_dvd_of_gt (p := 11) (by norm_num) hp (by norm_num)
  have e13 := not_dvd_of_gt (p := 13) (by norm_num) hp (by norm_num)
  have hL : k ∣ 2 := by
    have := dvd_of_bounds hk (le_13_of_le hp (by norm_num)) e2 e3 e5 e7 e11 e13
    norm_num at this
    exact this
  have key : ∀ d ∈ Nat.divisors 2, 
      pX 7 8 3 d ∈ ({8, 127} : Finset ℕ) := by
    decide
  exact key k (Nat.mem_divisors.mpr ⟨hL, by norm_num⟩) 

/-- `x ^ 2 - 10 y ^ 2 = 1` with `y` smooth for `210`, unit `19 + 6 √10`. -/
lemma blk210_10 {x y : ℕ} (h : (x : ℤ) ^ 2 - 10 * y ^ 2 = 1) (hy : 0 < y)
    (hs : Smooth 210 y) : x ∈ ({19} : Finset ℕ) := by
  have hσ : ((19 : ℕ) : ℤ) ^ 2 - ((10 : ℕ) : ℤ) * ((6 : ℕ) : ℤ) ^ 2 = 1 := by norm_num
  obtain ⟨k, rfl, rfl⟩ := pell_descent hσ (Or.inl rfl) (by norm_num) (by norm_num)
    (hmin_of_sqrt (Or.inl rfl) (by intro y h1 h2; interval_cases y <;> norm_num))
    _ _ (Or.inl (by exact_mod_cast h))
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hy)
  have hp := smooth_index hσ (Or.inl rfl) (by norm_num) (by norm_num) (R := 5)
    (rank210 (r2 := 1) (r3 := 1) (r5 := 5) (r7 := 4)
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩)
    (by
      intro p hp hd
      have := Nat.le_of_dvd (by norm_num) hd
      interval_cases p <;> first | omega | (exfalso; norm_num at hp)) hs
  have e2 : ¬ 2 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 12) (m := 19)
    (by decide) (by norm_num) (by norm_num)
  have e3 : ¬ 3 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 18) (m := 481)
    (by decide) (by norm_num) (by norm_num)
  have e5 : ¬ 5 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 30) (m := 416161)
    (by decide) (by norm_num) (by norm_num)
  have e7 := not_dvd_of_gt (p := 7) (by norm_num) hp (by norm_num)
  have e11 := not_dvd_of_gt (p := 11) (by norm_num) hp (by norm_num)
  have e13 := not_dvd_of_gt (p := 13) (by norm_num) hp (by norm_num)
  have hk1 : k = 1 := by
    have := dvd_of_bounds hk (le_13_of_le hp (by norm_num)) e2 e3 e5 e7 e11 e13
    simpa using this
  subst hk1
  decide

/-- `x ^ 2 - 14 y ^ 2 = 1` with `y` smooth for `210`, unit `15 + 4 √14`. -/
lemma blk210_14 {x y : ℕ} (h : (x : ℤ) ^ 2 - 14 * y ^ 2 = 1) (hy : 0 < y)
    (hs : Smooth 210 y) : x ∈ ({15, 449} : Finset ℕ) := by
  have hσ : ((15 : ℕ) : ℤ) ^ 2 - ((14 : ℕ) : ℤ) * ((4 : ℕ) : ℤ) ^ 2 = 1 := by norm_num
  obtain ⟨k, rfl, rfl⟩ := pell_descent hσ (Or.inl rfl) (by norm_num) (by norm_num)
    (hmin_of_sqrt (Or.inl rfl) (by intro y h1 h2; interval_cases y <;> norm_num))
    _ _ (Or.inl (by exact_mod_cast h))
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hy)
  have hp := smooth_index hσ (Or.inl rfl) (by norm_num) (by norm_num) (R := 7)
    (rank210 (r2 := 1) (r3 := 2) (r5 := 2) (r7 := 7)
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩)
    (bR_of_le (by norm_num) (by norm_num)) hs
  have e2 : ¬ 2 ^ (1 + 1) ∣ k := not_dvd_of_split hs (s := 240) (m := 449)
    (by decide) (by norm_num) (by norm_num)
  have e3 : ¬ 3 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 4) (m := 899)
    (by decide) (by norm_num) (by norm_num)
  have e5 : ¬ 5 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 4) (m := 807301)
    (by decide) (by norm_num) (by norm_num)
  have e7 : ¬ 7 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 28) (m := 103565057)
    (by decide) (by norm_num) (by norm_num)
  have e11 := not_dvd_of_gt (p := 11) (by norm_num) hp (by norm_num)
  have e13 := not_dvd_of_gt (p := 13) (by norm_num) hp (by norm_num)
  have hL : k ∣ 2 := by
    have := dvd_of_bounds hk (le_13_of_le hp (by norm_num)) e2 e3 e5 e7 e11 e13
    norm_num at this
    exact this
  have key : ∀ d ∈ Nat.divisors 2, 
      pX 14 15 4 d ∈ ({15, 449} : Finset ℕ) := by
    decide
  exact key k (Nat.mem_divisors.mpr ⟨hL, by norm_num⟩) 

/-- `x ^ 2 - 15 y ^ 2 = 1` with `y` smooth for `210`, unit `4 + 1 √15`. -/
lemma blk210_15 {x y : ℕ} (h : (x : ℤ) ^ 2 - 15 * y ^ 2 = 1) (hy : 0 < y)
    (hs : Smooth 210 y) : x ∈ ({4, 31, 244} : Finset ℕ) := by
  have hσ : ((4 : ℕ) : ℤ) ^ 2 - ((15 : ℕ) : ℤ) * ((1 : ℕ) : ℤ) ^ 2 = 1 := by norm_num
  obtain ⟨k, rfl, rfl⟩ := pell_descent hσ (Or.inl rfl) (by norm_num) (by norm_num)
    (hmin_of_sqrt (Or.inl rfl) (by intro y h1 h2; omega))
    _ _ (Or.inl (by exact_mod_cast h))
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hy)
  have hp := smooth_index hσ (Or.inl rfl) (by norm_num) (by norm_num) (R := 5)
    (rank210 (r2 := 2) (r3 := 3) (r5 := 5) (r7 := 3)
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩)
    (bR_of_le (by norm_num) (by norm_num)) hs
  have e2 : ¬ 2 ^ (1 + 1) ∣ k := not_dvd_of_split hs (s := 16) (m := 31)
    (by decide) (by norm_num) (by norm_num)
  have e3 : ¬ 3 ^ (1 + 1) ∣ k := not_dvd_of_split hs (s := 189) (m := 79381)
    (by decide) (by norm_num) (by norm_num)
  have e5 : ¬ 5 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 5) (m := 781)
    (by decide) (by norm_num) (by norm_num)
  have e7 := not_dvd_of_gt (p := 7) (by norm_num) hp (by norm_num)
  have e11 := not_dvd_of_gt (p := 11) (by norm_num) hp (by norm_num)
  have e13 := not_dvd_of_gt (p := 13) (by norm_num) hp (by norm_num)
  have c6 : ¬ 6 ∣ k := not_dvd_of_split hs (s := 504) (m := 61) (by decide) (by norm_num)
    (by norm_num)
  have hL : k ∣ 6 := by
    have := dvd_of_bounds hk (le_13_of_le hp (by norm_num)) e2 e3 e5 e7 e11 e13
    norm_num at this
    exact this
  have key : ∀ d ∈ Nat.divisors 6, ¬ 6 ∣ d → 
      pX 15 4 1 d ∈ ({4, 31, 244} : Finset ℕ) := by
    decide
  exact key k (Nat.mem_divisors.mpr ⟨hL, by norm_num⟩) c6

end TuringTask
