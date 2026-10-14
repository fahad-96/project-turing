import Mathlib
import TuringTask.Orders

/-!
# The five statements

* `sum_filter_four`: `∑_{d ∣ n, 4 ∣ d} f (d / 4) = ∑_{e ∣ n / 4} f e` when `4 ∣ n`, and `0`
  otherwise.
* `filter_odd_even`: for even `n` the divisors `d` with `d` odd and `n / d` even are the odd
  divisors, and for odd `n` there are none.
* For `x^2 + 3 y^2` and `x^2 + 7 y^2` the counts of `Orders.lean` and the recursions of
  `divSum_rec` at `p = 2` (with `J(2 | 3) = -1` and `J(2 | 7) = 1`) give the stated sums.
-/

namespace TuringTask

lemma sum_filter_four (f : ℕ → ℤ) {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors.filter (fun d => d % 4 = 0), f (d / 4) =
      if 4 ∣ n then ∑ e ∈ (n / 4).divisors, f e else 0 := by
  have e1 : n.divisors.filter (fun d => d % 4 = 0) = n.divisors.filter (fun d => 4 ∣ d) :=
    Finset.filter_congr fun d _ => by omega
  rw [e1]
  split_ifs with h4
  · rw [divisors_filter_dvd (show 0 < 4 by norm_num) h4 hn, Finset.sum_map]
    refine Finset.sum_congr rfl fun e _ => ?_
    show f (4 * e / 4) = f e
    rw [Nat.mul_div_cancel_left _ (by norm_num)]
  · rw [Finset.sum_eq_zero]
    intro d hd
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    exact absurd (hd.2.trans hd.1.1) h4

lemma filter_odd_even_odd {n : ℕ} (hn : n % 2 = 1) :
    n.divisors.filter (fun d => d % 2 = 1 ∧ n / d % 2 = 0) = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  intro d hd ⟨_, h2⟩
  have hd' := Nat.mem_divisors.mp hd
  have : n = d * (n / d) := (Nat.mul_div_cancel' hd'.1).symm
  have : n % 2 = d * (n / d) % 2 := by rw [← this]
  rw [Nat.mul_mod, h2] at this
  omega

lemma filter_odd_even_even {n : ℕ} (hn : n % 2 = 0) :
    n.divisors.filter (fun d => d % 2 = 1 ∧ n / d % 2 = 0) =
      n.divisors.filter (fun d => ¬ 2 ∣ d) := by
  apply Finset.filter_congr
  intro d hd
  have hd' := Nat.mem_divisors.mp hd
  have e : n = d * (n / d) := (Nat.mul_div_cancel' hd'.1).symm
  constructor
  · rintro ⟨h1, -⟩; omega
  · intro h1
    refine ⟨by omega, ?_⟩
    have : n % 2 = d * (n / d) % 2 := by rw [← e]
    rw [Nat.mul_mod] at this
    rcases Nat.mod_two_eq_zero_or_one (n / d) with h | h
    · exact h
    · rw [h, show d % 2 = 1 by omega] at this; omega

theorem main_one (n : Nat) (hn : 0 < n) :
    ((Finset.filter (fun v : Prod Int Int => v.1 ^ 2 + v.1 * v.2 + v.2 ^ 2 = (n : Int))
        (Finset.product (Finset.Icc (-(n : Int)) n) (Finset.Icc (-(n : Int)) n))).card : Int) =
      6 * Finset.sum (Nat.divisors n) (fun d => jacobiSym (d : Int) 3) := by
  have := cnt1 (n := n) hn
  rw [← card1_eq] at this
  exact this

theorem main_three (n : Nat) (hn : 0 < n) :
    ((Finset.filter (fun v : Prod Int Int => v.1 ^ 2 + 2 * v.2 ^ 2 = (n : Int))
        (Finset.product (Finset.Icc (-(n : Int)) n) (Finset.Icc (-(n : Int)) n))).card : Int) =
      2 * Finset.sum (Nat.divisors n) (fun d => jacobiSym (-2) d) := by
  have := cnt3 (n := n) hn
  rw [cnt_eq_cntF, cntF_congr (g := fun x y => x ^ 2 + 2 * y ^ 2) (fun x y => by ring)] at this
  exact this

theorem main_four (n : Nat) (hn : 0 < n) :
    ((Finset.filter (fun v : Prod Int Int => v.1 ^ 2 + v.1 * v.2 + 2 * v.2 ^ 2 = (n : Int))
        (Finset.product (Finset.Icc (-(n : Int)) n) (Finset.Icc (-(n : Int)) n))).card : Int) =
      2 * Finset.sum (Nat.divisors n) (fun d => jacobiSym (d : Int) 7) := by
  have := cnt4 (n := n) hn
  rw [cnt_eq_cntF, cntF_congr (g := fun x y => x ^ 2 + x * y + 2 * y ^ 2) (fun x y => by ring)]
    at this
  exact this

theorem main_two (n : Nat) (hn : 0 < n) :
    ((Finset.filter (fun v : Prod Int Int => v.1 ^ 2 + 3 * v.2 ^ 2 = (n : Int))
        (Finset.product (Finset.Icc (-(n : Int)) n) (Finset.Icc (-(n : Int)) n))).card : Int) =
      2 * Finset.sum (Nat.divisors n) (fun d => jacobiSym (d : Int) 3) +
        4 * Finset.sum (Finset.filter (fun d => d % 4 = 0) (Nat.divisors n))
          (fun d => jacobiSym ((d / 4 : Nat) : Int) 3) := by
  have hn0 : n ≠ 0 := by omega
  rw [sum_filter_four (fun e => jacobiSym (e : ℤ) 3) hn0]
  change (cntF (fun x y => x ^ 2 + 3 * y ^ 2) n : ℤ) =
    2 * divSum (fun d => jacobiSym (d : ℤ) 3) n +
      4 * if 4 ∣ n then divSum (fun d => jacobiSym (d : ℤ) 3) (n / 4) else 0
  have h1 : ∀ m, 1 ≤ m → (cntF (fun x y => x ^ 2 + x * y + y ^ 2) m : ℤ) =
      6 * divSum (fun d => jacobiSym (d : ℤ) 3) m := fun m hm => by
    rw [card1_eq]; exact cnt1 hm
  have hrec : 2 ∣ n → divSum (fun d => jacobiSym (d : ℤ) 3) n =
      if 2 ^ 2 ∣ n then divSum (fun d => jacobiSym (d : ℤ) 3) (n / 2 ^ 2) else 0 := fun h2 =>
    (divSum_rec (χ := fun d => jacobiSym (d : ℤ) 3) hmul1 Nat.prime_two h2 hn0).2.2
      (by norm_num)
  norm_num at hrec
  rcases Nat.mod_two_eq_zero_or_one n with h2 | h2
  · rcases (by omega : n % 4 = 0 ∨ n % 4 = 2) with h4 | h4
    · have h4' : 4 ∣ n := Nat.dvd_of_mod_eq_zero h4
      have hn4 : 1 ≤ n / 4 := Nat.div_pos (Nat.le_of_dvd hn h4') (by norm_num)
      rw [f2_four h4' hn, h1 _ hn4, if_pos h4', hrec (by omega), if_pos h4']
      ring
    · have h4' : ¬ 4 ∣ n := by omega
      rw [f2_two h4, if_neg h4', hrec (by omega), if_neg h4']
      simp
  · have h4' : ¬ 4 ∣ n := by omega
    rw [if_neg h4']
    have h3 := f2_odd h2
    have := h1 n hn
    omega

theorem main_five (n : Nat) (hn : 0 < n) :
    ((Finset.filter (fun v : Prod Int Int => v.1 ^ 2 + 7 * v.2 ^ 2 = (n : Int))
        (Finset.product (Finset.Icc (-(n : Int)) n) (Finset.Icc (-(n : Int)) n))).card : Int) =
      2 * Finset.sum (Nat.divisors n) (fun d => jacobiSym (d : Int) 7) -
        4 * Finset.sum (Finset.filter (fun d => d % 2 = 1 /\ n / d % 2 = 0)
          (Nat.divisors n)) (fun d => jacobiSym (d : Int) 7) := by
  have hn0 : n ≠ 0 := by omega
  rcases Nat.mod_two_eq_zero_or_one n with h2 | h2
  · rw [filter_odd_even_even h2]
    change (cntF (fun x y => x ^ 2 + 7 * y ^ 2) n : ℤ) =
      2 * divSum (fun d => jacobiSym (d : ℤ) 7) n -
        4 * divSumT (fun d => jacobiSym (d : ℤ) 7) 2 n
    have h2' : 2 ∣ n := Nat.dvd_of_mod_eq_zero h2
    have hsplit := divSum_split (χ := fun d => jacobiSym (d : ℤ) 7) hmul4 Nat.prime_two h2' hn0
    have hχ2 : jacobiSym ((2 : ℕ) : ℤ) 7 = 1 := by norm_num
    simp only [hχ2, one_mul] at hsplit
    have hr := (divSum_rec (χ := fun d => jacobiSym (d : ℤ) 7) hmul4 Nat.prime_two h2' hn0).1
      hχ2
    rcases (by omega : n % 4 = 0 ∨ n % 4 = 2) with h4 | h4
    · have h4' : 4 ∣ n := Nat.dvd_of_mod_eq_zero h4
      have hn4 : 1 ≤ n / 4 := Nat.div_pos (Nat.le_of_dvd hn h4') (by norm_num)
      rw [f5_four h4' hn, cnt4 hn4]
      rw [if_pos (by norm_num; exact h4')] at hr
      norm_num at hr
      linarith
    · rw [f5_two h4]
      rw [if_neg (by norm_num; omega)] at hr
      push_cast
      linarith
  · rw [filter_odd_even_odd h2, Finset.sum_empty]
    change (cntF (fun x y => x ^ 2 + 7 * y ^ 2) n : ℤ) =
      2 * divSum (fun d => jacobiSym (d : ℤ) 7) n - 4 * 0
    rw [f5_odd h2, cnt4 hn]
    ring

end TuringTask
