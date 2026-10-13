import Mathlib
import TuringTask.Blocks210b

/-!
# The units of norm `-1`

For `D = 2, 5, 10, 13, 26, 65, 130`: solutions of `x ^ 2 - D y ^ 2 = -1` with `y` smooth for `65`
(odd powers of the unit). Last, `x ^ 2 - 2 y ^ 2 = ±1` with `y` smooth for `30030`.
-/

namespace TuringTask

/-- `x ^ 2 - 2 y ^ 2 = -1` with `y` smooth for `65`, unit `1 + 1 √2`. -/
lemma blk65_2 {x y : ℕ} (h : (x : ℤ) ^ 2 - 2 * y ^ 2 = -1) (hs : Smooth 65 y) :
    x ∈ ({1, 7, 239} : Finset ℕ) := by
  have hσ : ((1 : ℕ) : ℤ) ^ 2 - ((2 : ℕ) : ℤ) * ((1 : ℕ) : ℤ) ^ 2 = -1 := by norm_num
  obtain ⟨k, rfl, rfl⟩ := pell_descent hσ (Or.inr rfl) (by norm_num) (by norm_num)
    (hmin_of_sqrt (Or.inr rfl) (by intro y h1 h2; omega))
    _ _ (Or.inr (by exact_mod_cast h))
  have e2 := not_two_dvd_of_norm hσ (by exact_mod_cast h)
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; exact e2 (dvd_zero _))
  have hp := smooth_index hσ (Or.inr rfl) (by norm_num) (by norm_num) (R := 7)
    (rank65 (r5 := 3) (r13 := 7)
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩)
    (bR_of_le (by norm_num) (by norm_num)) hs
  have e3 : ¬ 3 ^ (1 + 1) ∣ k := not_dvd_of_split hs (s := 5) (m := 197)
    (by decide) (by norm_num) (by norm_num)
  have e5 : ¬ 5 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 1) (m := 29)
    (by decide) (by norm_num) (by norm_num)
  have e7 : ¬ 7 ^ (1 + 1) ∣ k := not_dvd_of_split hs (s := 169) (m := 11928254138546089)
    (by decide) (by norm_num) (by norm_num)
  have e11 := not_dvd_of_gt (p := 11) (by norm_num) hp (by norm_num)
  have e13 := not_dvd_of_gt (p := 13) (by norm_num) hp (by norm_num)
  have c21 : ¬ 21 ∣ k := not_dvd_of_split hs (s := 845) (m := 45697) (by decide) (by norm_num)
    (by norm_num)
  have hL : k ∣ 21 := by
    have := dvd_of_bounds hk (le_13_of_le hp (by norm_num)) e2 e3 e5 e7 e11 e13
    norm_num at this
    exact this
  have key : ∀ d ∈ Nat.divisors 21, ¬ 2 ∣ d → ¬ 21 ∣ d → 
      pX 2 1 1 d ∈ ({1, 7, 239} : Finset ℕ) := by
    decide
  exact key k (Nat.mem_divisors.mpr ⟨hL, by norm_num⟩) (by simpa using e2) c21

/-- `x ^ 2 - 5 y ^ 2 = -1` with `y` smooth for `65`, unit `2 + 1 √5`. -/
lemma blk65_5 {x y : ℕ} (h : (x : ℤ) ^ 2 - 5 * y ^ 2 = -1) (hs : Smooth 65 y) :
    x ∈ ({2} : Finset ℕ) := by
  have hσ : ((2 : ℕ) : ℤ) ^ 2 - ((5 : ℕ) : ℤ) * ((1 : ℕ) : ℤ) ^ 2 = -1 := by norm_num
  obtain ⟨k, rfl, rfl⟩ := pell_descent hσ (Or.inr rfl) (by norm_num) (by norm_num)
    (hmin_of_sqrt (Or.inr rfl) (by intro y h1 h2; omega))
    _ _ (Or.inr (by exact_mod_cast h))
  have e2 := not_two_dvd_of_norm hσ (by exact_mod_cast h)
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; exact e2 (dvd_zero _))
  have hp := smooth_index hσ (Or.inr rfl) (by norm_num) (by norm_num) (R := 7)
    (rank65 (r5 := 5) (r13 := 7)
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩)
    (bR_of_le (by norm_num) (by norm_num)) hs
  have e3 : ¬ 3 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 1) (m := 17)
    (by decide) (by norm_num) (by norm_num)
  have e5 : ¬ 5 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 5) (m := 61)
    (by decide) (by norm_num) (by norm_num)
  have e7 : ¬ 7 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 13) (m := 421)
    (by decide) (by norm_num) (by norm_num)
  have e11 := not_dvd_of_gt (p := 11) (by norm_num) hp (by norm_num)
  have e13 := not_dvd_of_gt (p := 13) (by norm_num) hp (by norm_num)
  have hk1 : k = 1 := by
    have := dvd_of_bounds hk (le_13_of_le hp (by norm_num)) e2 e3 e5 e7 e11 e13
    simpa using this
  subst hk1
  decide

/-- `x ^ 2 - 10 y ^ 2 = -1` with `y` smooth for `65`, unit `3 + 1 √10`. -/
lemma blk65_10 {x y : ℕ} (h : (x : ℤ) ^ 2 - 10 * y ^ 2 = -1) (hs : Smooth 65 y) :
    x ∈ ({3} : Finset ℕ) := by
  have hσ : ((3 : ℕ) : ℤ) ^ 2 - ((10 : ℕ) : ℤ) * ((1 : ℕ) : ℤ) ^ 2 = -1 := by norm_num
  obtain ⟨k, rfl, rfl⟩ := pell_descent hσ (Or.inr rfl) (by norm_num) (by norm_num)
    (hmin_of_sqrt (Or.inr rfl) (by intro y h1 h2; omega))
    _ _ (Or.inr (by exact_mod_cast h))
  have e2 := not_two_dvd_of_norm hσ (by exact_mod_cast h)
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; exact e2 (dvd_zero _))
  have hp := smooth_index hσ (Or.inr rfl) (by norm_num) (by norm_num) (R := 6)
    (rank65 (r5 := 5) (r13 := 6)
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩)
    (bR_of_le (by norm_num) (by norm_num)) hs
  have e3 : ¬ 3 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 1) (m := 37)
    (by decide) (by norm_num) (by norm_num)
  have e5 : ¬ 5 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 5) (m := 281)
    (by decide) (by norm_num) (by norm_num)
  have e7 := not_dvd_of_gt (p := 7) (by norm_num) hp (by norm_num)
  have e11 := not_dvd_of_gt (p := 11) (by norm_num) hp (by norm_num)
  have e13 := not_dvd_of_gt (p := 13) (by norm_num) hp (by norm_num)
  have hk1 : k = 1 := by
    have := dvd_of_bounds hk (le_13_of_le hp (by norm_num)) e2 e3 e5 e7 e11 e13
    simpa using this
  subst hk1
  decide

/-- `x ^ 2 - 13 y ^ 2 = -1` with `y` smooth for `65`, unit `18 + 5 √13`. -/
lemma blk65_13 {x y : ℕ} (h : (x : ℤ) ^ 2 - 13 * y ^ 2 = -1) (hs : Smooth 65 y) :
    x ∈ ({18} : Finset ℕ) := by
  have hσ : ((18 : ℕ) : ℤ) ^ 2 - ((13 : ℕ) : ℤ) * ((5 : ℕ) : ℤ) ^ 2 = -1 := by norm_num
  obtain ⟨k, rfl, rfl⟩ := pell_descent hσ (Or.inr rfl) (by norm_num) (by norm_num)
    (hmin_of_sqrt (Or.inr rfl) (by intro y h1 h2; interval_cases y <;> norm_num))
    _ _ (Or.inr (by exact_mod_cast h))
  have e2 := not_two_dvd_of_norm hσ (by exact_mod_cast h)
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; exact e2 (dvd_zero _))
  have hp := smooth_index hσ (Or.inr rfl) (by norm_num) (by norm_num) (R := 13)
    (rank65 (r5 := 1) (r13 := 13)
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩)
    (bR_of_le (by norm_num) (by norm_num)) hs
  have e3 : ¬ 3 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 5) (m := 1297)
    (by decide) (by norm_num) (by norm_num)
  have e5 : ¬ 5 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 25) (m := 336701)
    (by decide) (by norm_num) (by norm_num)
  have e7 : ¬ 7 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 5) (m := 2185188193)
    (by decide) (by norm_num) (by norm_num)
  have e11 : ¬ 11 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 5) (m := 3681609437941489)
    (by decide) (by norm_num) (by norm_num)
  have e13 : ¬ 13 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 65) (m := 367594324159650901)
    (by decide) (by norm_num) (by norm_num)
  have hk1 : k = 1 := by
    have := dvd_of_bounds hk (le_13_of_le hp (by norm_num)) e2 e3 e5 e7 e11 e13
    simpa using this
  subst hk1
  decide

/-- `x ^ 2 - 26 y ^ 2 = -1` with `y` smooth for `65`, unit `5 + 1 √26`. -/
lemma blk65_26 {x y : ℕ} (h : (x : ℤ) ^ 2 - 26 * y ^ 2 = -1) (hs : Smooth 65 y) :
    x ∈ ({5} : Finset ℕ) := by
  have hσ : ((5 : ℕ) : ℤ) ^ 2 - ((26 : ℕ) : ℤ) * ((1 : ℕ) : ℤ) ^ 2 = -1 := by norm_num
  obtain ⟨k, rfl, rfl⟩ := pell_descent hσ (Or.inr rfl) (by norm_num) (by norm_num)
    (hmin_of_sqrt (Or.inr rfl) (by intro y h1 h2; omega))
    _ _ (Or.inr (by exact_mod_cast h))
  have e2 := not_two_dvd_of_norm hσ (by exact_mod_cast h)
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; exact e2 (dvd_zero _))
  have hp := smooth_index hσ (Or.inr rfl) (by norm_num) (by norm_num) (R := 13)
    (rank65 (r5 := 2) (r13 := 13)
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩)
    (bR_of_le (by norm_num) (by norm_num)) hs
  have e3 : ¬ 3 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 1) (m := 101)
    (by decide) (by norm_num) (by norm_num)
  have e5 : ¬ 5 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 1) (m := 10301)
    (by decide) (by norm_num) (by norm_num)
  have e7 : ¬ 7 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 1) (m := 1050601)
    (by decide) (by norm_num) (by norm_num)
  have e11 : ¬ 11 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 1) (m := 10928351501)
    (by decide) (by norm_num) (by norm_num)
  have e13 : ¬ 13 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 13) (m := 85737284777)
    (by decide) (by norm_num) (by norm_num)
  have hk1 : k = 1 := by
    have := dvd_of_bounds hk (le_13_of_le hp (by norm_num)) e2 e3 e5 e7 e11 e13
    simpa using this
  subst hk1
  decide

/-- `x ^ 2 - 65 y ^ 2 = -1` with `y` smooth for `65`, unit `8 + 1 √65`. -/
lemma blk65_65 {x y : ℕ} (h : (x : ℤ) ^ 2 - 65 * y ^ 2 = -1) (hs : Smooth 65 y) :
    x ∈ ({8} : Finset ℕ) := by
  have hσ : ((8 : ℕ) : ℤ) ^ 2 - ((65 : ℕ) : ℤ) * ((1 : ℕ) : ℤ) ^ 2 = -1 := by norm_num
  obtain ⟨k, rfl, rfl⟩ := pell_descent hσ (Or.inr rfl) (by norm_num) (by norm_num)
    (hmin_of_sqrt (Or.inr rfl) (by intro y h1 h2; omega))
    _ _ (Or.inr (by exact_mod_cast h))
  have e2 := not_two_dvd_of_norm hσ (by exact_mod_cast h)
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; exact e2 (dvd_zero _))
  have hp := smooth_index hσ (Or.inr rfl) (by norm_num) (by norm_num) (R := 13)
    (rank65 (r5 := 5) (r13 := 13)
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩)
    (bR_of_le (by norm_num) (by norm_num)) hs
  have e3 : ¬ 3 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 1) (m := 257)
    (by decide) (by norm_num) (by norm_num)
  have e5 : ¬ 5 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 5) (m := 13261)
    (by decide) (by norm_num) (by norm_num)
  have e7 : ¬ 7 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 1) (m := 17106433)
    (by decide) (by norm_num) (by norm_num)
  have e11 : ¬ 11 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 1) (m := 1138638393089)
    (by decide) (by norm_num) (by norm_num)
  have e13 : ¬ 13 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 13) (m := 22597253232581)
    (by decide) (by norm_num) (by norm_num)
  have hk1 : k = 1 := by
    have := dvd_of_bounds hk (le_13_of_le hp (by norm_num)) e2 e3 e5 e7 e11 e13
    simpa using this
  subst hk1
  decide

/-- `x ^ 2 - 130 y ^ 2 = -1` with `y` smooth for `65`, unit `57 + 5 √130`. -/
lemma blk65_130 {x y : ℕ} (h : (x : ℤ) ^ 2 - 130 * y ^ 2 = -1) (hs : Smooth 65 y) :
    x ∈ ({57} : Finset ℕ) := by
  have hσ : ((57 : ℕ) : ℤ) ^ 2 - ((130 : ℕ) : ℤ) * ((5 : ℕ) : ℤ) ^ 2 = -1 := by norm_num
  obtain ⟨k, rfl, rfl⟩ := pell_descent hσ (Or.inr rfl) (by norm_num) (by norm_num)
    (hmin_of_sqrt (Or.inr rfl) (by intro y h1 h2; interval_cases y <;> norm_num))
    _ _ (Or.inr (by exact_mod_cast h))
  have e2 := not_two_dvd_of_norm hσ (by exact_mod_cast h)
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; exact e2 (dvd_zero _))
  have hp := smooth_index hσ (Or.inr rfl) (by norm_num) (by norm_num) (R := 13)
    (rank65 (r5 := 1) (r13 := 13)
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩)
    (bR_of_le (by norm_num) (by norm_num)) hs
  have e3 : ¬ 3 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 5) (m := 12997)
    (by decide) (by norm_num) (by norm_num)
  have e5 : ¬ 5 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 25) (m := 33787001)
    (by decide) (by norm_num) (by norm_num)
  have e7 : ¬ 7 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 5) (m := 2195817181993)
    (by decide) (by norm_num) (by norm_num)
  have e11 : ¬ 11 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 5) (m := 370978925654987714989)
    (by decide) (by norm_num) (by norm_num)
  have e13 : ¬ 13 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 65) (m := 370921849778638365909001)
    (by decide) (by norm_num) (by norm_num)
  have hk1 : k = 1 := by
    have := dvd_of_bounds hk (le_13_of_le hp (by norm_num)) e2 e3 e5 e7 e11 e13
    simpa using this
  subst hk1
  decide

/-- `x ^ 2 - 2 y ^ 2 = ±1` with `y` smooth for `30030`, unit `1 + √2`. -/
lemma blk30030_2 {x y : ℕ}
    (h : (x : ℤ) ^ 2 - 2 * y ^ 2 = 1 ∨ (x : ℤ) ^ 2 - 2 * y ^ 2 = -1)
    (hy : 0 < y) (hs : Smooth 30030 y) : y ∈ ({1, 2, 5, 12, 70, 169, 13860} : Finset ℕ) := by
  have hσ : ((1 : ℕ) : ℤ) ^ 2 - ((2 : ℕ) : ℤ) * ((1 : ℕ) : ℤ) ^ 2 = -1 := by norm_num
  obtain ⟨k, rfl, rfl⟩ := pell_descent hσ (Or.inr rfl) (by norm_num) (by norm_num)
    (hmin_of_sqrt (Or.inr rfl) (by intro y h1 h2; omega))
    _ _ (h.imp (fun h => by exact_mod_cast h) (fun h => by exact_mod_cast h))
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hy)
  have hp := smooth_index hσ (Or.inr rfl) (by norm_num) (by norm_num) (R := 12)
    (rank30030 (r2 := 2) (r3 := 4) (r5 := 3) (r7 := 6) (r11 := 12) (r13 := 7)
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩
      ⟨by norm_num, by norm_num, by decide⟩)
    (bR_of_le (by norm_num) (by norm_num)) hs
  have e2 : ¬ 2 ^ (2 + 1) ∣ k := not_dvd_of_split hs (s := 24) (m := 17)
    (by decide) (by norm_num) (by norm_num)
  have e3 : ¬ 3 ^ (1 + 1) ∣ k := not_dvd_of_split hs (s := 5) (m := 197)
    (by decide) (by norm_num) (by norm_num)
  have e5 : ¬ 5 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 1) (m := 29)
    (by decide) (by norm_num) (by norm_num)
  have e7 : ¬ 7 ^ (1 + 1) ∣ k := not_dvd_of_split hs (s := 169) (m := 11928254138546089)
    (by decide) (by norm_num) (by norm_num)
  have e11 : ¬ 11 ^ (0 + 1) ∣ k := not_dvd_of_split hs (s := 1) (m := 5741)
    (by decide) (by norm_num) (by norm_num)
  have e13 := not_dvd_of_gt (p := 13) (by norm_num) hp (by norm_num)
  have c14 : ¬ 14 ∣ k := not_dvd_of_split hs (s := 338) (m := 239) (by decide) (by norm_num)
    (by norm_num)
  have c21 : ¬ 21 ∣ k := not_dvd_of_split hs (s := 845) (m := 45697) (by decide) (by norm_num)
    (by norm_num)
  have hL : k ∣ 84 := by
    have := dvd_of_bounds hk (le_13_of_le hp (by norm_num)) e2 e3 e5 e7 e11 e13
    norm_num at this
    exact this
  have key : ∀ d ∈ Nat.divisors 84, ¬ 14 ∣ d → ¬ 21 ∣ d → 
      pY 2 1 1 d ∈ ({1, 2, 5, 12, 70, 169, 13860} : Finset ℕ) := by
    decide
  exact key k (Nat.mem_divisors.mpr ⟨hL, by norm_num⟩) c14 c21

end TuringTask
