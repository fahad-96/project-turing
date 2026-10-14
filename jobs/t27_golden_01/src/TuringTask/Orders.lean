import Mathlib
import TuringTask.Types

/-!
# The counts for the five forms

* `cnt1`, `cnt3`, `cnt4`: `cnt_eq` with `type1`, `type3`, `type4` and the unit counts `6, 2, 2`.
* `card1_eq`: the prompt counts `x^2 + x y + y^2`, which is the norm of `x - y ω` in `R1`, so the
  map `(x, y) ↦ (x, -y)` matches the two counts. The forms `x^2 + 2 y^2` and
  `x^2 + x y + 2 y^2` are the norms of `R3` and `R4` as they stand.
* `x^2 + 7 y^2` (`f5_odd`, `f5_two`, `f5_four`): for odd `n` every solution of
  `x^2 + x y + 2 y^2 = n` has `y` even, and `(X, Y) ↦ (X - Y, 2 Y)` matches the two counts; for
  `n = 2 (mod 4)` there is no solution; for `4 ∣ n` the map `(X, Y) ↦ ((X - Y) / 2, Y)` matches
  the solutions with those of `x^2 + x y + 2 y^2 = n / 4`.
* `x^2 + 3 y^2` (`f2_odd`, `f2_two`, `f2_four`): the same maps with `x^2 + x y + y^2`. For odd
  `n` the solutions of `x^2 + x y + y^2 = n` fall into the three parity classes
  `(odd, even)`, `(even, odd)`, `(odd, odd)`, which the rotation `(x, y) ↦ (-y, x + y)` permutes,
  so they number three times the solutions of `x^2 + 3 y^2 = n`.
-/

namespace TuringTask

local notation "Nm" => QuadraticAlgebra.norm

/-- The count of the prompt for a form `f`. -/
noncomputable def cntF (f : ℤ → ℤ → ℤ) (n : ℕ) : ℕ :=
  ((box n).filter (fun v : ℤ × ℤ => f v.1 v.2 = n)).card

lemma cntF_congr {f g : ℤ → ℤ → ℤ} (h : ∀ x y, f x y = g x y) (n : ℕ) : cntF f n = cntF g n := by
  unfold cntF
  congr 1
  exact Finset.filter_congr fun v _ => by rw [h]

lemma cnt_eq_cntF (a b : ℤ) (n : ℕ) :
    cnt a b n = cntF (fun x y => x ^ 2 + b * x * y - a * y ^ 2) n := rfl

/-- `(x, y) ↦ (x, -y)` matches `x^2 + x y + y^2` with the norm `x^2 - x y + y^2` of `R1`. -/
lemma card1_eq (n : ℕ) : cntF (fun x y => x ^ 2 + x * y + y ^ 2) n = cnt (-1) (-1) n := by
  unfold cntF cnt
  apply Finset.card_bij' (fun v _ => (v.1, -v.2)) (fun v _ => (v.1, -v.2))
  case hi =>
    intro v hv
    simp only [Finset.mem_filter, mem_box] at hv ⊢
    exact ⟨⟨hv.1.1, by omega, by omega⟩, by linear_combination hv.2⟩
  case hj =>
    intro v hv
    simp only [Finset.mem_filter, mem_box] at hv ⊢
    exact ⟨⟨hv.1.1, by omega, by omega⟩, by linear_combination hv.2⟩
  all_goals intro v _; simp

lemma hmul1 : ∀ m n : ℕ, m ≠ 0 → n ≠ 0 →
    jacobiSym ((m * n : ℕ) : ℤ) 3 = jacobiSym (m : ℤ) 3 * jacobiSym (n : ℤ) 3 := by
  intro m n _ _
  push_cast
  exact jacobiSym.mul_left _ _ _

lemma hmul3 : ∀ m n : ℕ, m ≠ 0 → n ≠ 0 →
    jacobiSym (-2) (m * n) = jacobiSym (-2) m * jacobiSym (-2) n :=
  fun _ _ hm hn => jacobiSym.mul_right' _ hm hn

lemma hmul4 : ∀ m n : ℕ, m ≠ 0 → n ≠ 0 →
    jacobiSym ((m * n : ℕ) : ℤ) 7 = jacobiSym (m : ℤ) 7 * jacobiSym (n : ℤ) 7 := by
  intro m n _ _
  push_cast
  exact jacobiSym.mul_left _ _ _

theorem cnt1 {n : ℕ} (hn : 1 ≤ n) :
    (cnt (-1) (-1) n : ℤ) = 6 * divSum (fun d => jacobiSym (d : ℤ) 3) n := by
  rw [cnt_eq (by norm_num) (by norm_num) _ hmul1 (by simp [jacobiSym.one_left]) type1 n hn,
    show cnt (-1) (-1) 1 = 6 by decide]
  push_cast; ring

theorem cnt3 {n : ℕ} (hn : 1 ≤ n) :
    (cnt (-2) 0 n : ℤ) = 2 * divSum (fun d => jacobiSym (-2) d) n := by
  rw [cnt_eq (by norm_num) (by norm_num) _ hmul3 (jacobiSym.one_right _) type3 n hn,
    show cnt (-2) 0 1 = 2 by decide]
  push_cast; ring

theorem cnt4 {n : ℕ} (hn : 1 ≤ n) :
    (cnt (-2) 1 n : ℤ) = 2 * divSum (fun d => jacobiSym (d : ℤ) 7) n := by
  rw [cnt_eq (by norm_num) (by norm_num) _ hmul4 (by simp [jacobiSym.one_left]) type4 n hn,
    show cnt (-2) 1 1 = 2 by decide]
  push_cast; ring

/-! ### Boxes for `x^2 + 3 y^2` and `x^2 + 7 y^2` -/

lemma box_of_sq {x y : ℤ} {c : ℤ} {n : ℕ} (hc : 1 ≤ c) (h : x ^ 2 + c * y ^ 2 = n) :
    (x, y) ∈ box n := by
  rw [mem_box]
  have h1 : x ^ 2 ≤ n := by nlinarith [sq_nonneg y]
  have h2 : y ^ 2 ≤ n := by nlinarith [sq_nonneg x]
  have hx1 : -(n : ℤ) ≤ x ∧ x ≤ n := by
    constructor <;> nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1)]
  have hy1 : -(n : ℤ) ≤ y ∧ y ≤ n := by
    constructor <;> nlinarith [sq_nonneg (y + 1), sq_nonneg (y - 1)]
  exact ⟨hx1, hy1⟩

lemma box_of_norm {a b : ℤ} (ha : -2 ≤ a) (hD : b ^ 2 + 4 * a ≤ -3) {x y : ℤ} {n : ℕ}
    (h : x ^ 2 + b * x * y - a * y ^ 2 = n) (hn : 1 ≤ n) : (x, y) ∈ box n := by
  obtain ⟨b1, b2, b3, b4⟩ := in_box ha hD h hn
  exact mem_box.mpr ⟨⟨b1, b2⟩, b3, b4⟩

lemma even_of_sq_mod {x y : ℤ} (h : (x ^ 2 + 3 * y ^ 2) % 4 = 0 ∨ (x ^ 2 + 7 * y ^ 2) % 4 = 0) :
    (x - y) % 2 = 0 := by
  rcases Int.emod_two_eq_zero_or_one x with hx | hx <;>
    rcases Int.emod_two_eq_zero_or_one y with hy | hy
  · omega
  · exfalso
    obtain ⟨k, rfl⟩ : ∃ k, x = 2 * k := ⟨x / 2, by omega⟩
    obtain ⟨m, rfl⟩ : ∃ m, y = 2 * m + 1 := ⟨y / 2, by omega⟩
    rcases h with h | h <;> ring_nf at h <;> omega
  · exfalso
    obtain ⟨k, rfl⟩ : ∃ k, x = 2 * k + 1 := ⟨x / 2, by omega⟩
    obtain ⟨m, rfl⟩ : ∃ m, y = 2 * m := ⟨y / 2, by omega⟩
    rcases h with h | h <;> ring_nf at h <;> omega
  · omega

/-! ### `x^2 + 7 y^2` -/

lemma f5_four {n : ℕ} (h4 : 4 ∣ n) (hn : 1 ≤ n) :
    cntF (fun x y => x ^ 2 + 7 * y ^ 2) n = cnt (-2) 1 (n / 4) := by
  obtain ⟨m, rfl⟩ := h4
  have hm : 1 ≤ m := by omega
  rw [Nat.mul_div_cancel_left _ (by norm_num)]
  unfold cntF cnt
  apply Finset.card_bij' (fun v _ => ((v.1 - v.2) / 2, v.2)) (fun v _ => (2 * v.1 + v.2, v.2))
  case hi =>
    intro v hv
    simp only [Finset.mem_filter] at hv ⊢
    have he := even_of_sq_mod (x := v.1) (y := v.2) (Or.inr (by rw [hv.2]; push_cast; omega))
    obtain ⟨k, hk⟩ : ∃ k, v.1 - v.2 = 2 * k := ⟨(v.1 - v.2) / 2, by omega⟩
    rw [hk, Int.mul_ediv_cancel_left _ (by norm_num)]
    have hval : k ^ 2 + 1 * k * v.2 - (-2) * v.2 ^ 2 = (m : ℤ) := by
      have h1 := hv.2; push_cast at h1
      have : v.1 = 2 * k + v.2 := by omega
      rw [this] at h1; nlinarith
    exact ⟨box_of_norm (by norm_num) (by norm_num) hval hm, hval⟩
  case hj =>
    intro v hv
    simp only [Finset.mem_filter] at hv ⊢
    have hval : (2 * v.1 + v.2) ^ 2 + 7 * v.2 ^ 2 = ((4 * m : ℕ) : ℤ) := by
      push_cast; linear_combination 4 * hv.2
    exact ⟨box_of_sq (by norm_num) hval, hval⟩
  case left_inv =>
    intro v hv
    simp only [Finset.mem_filter] at hv
    have he := even_of_sq_mod (x := v.1) (y := v.2) (Or.inr (by rw [hv.2]; push_cast; omega))
    obtain ⟨k, hk⟩ : ∃ k, v.1 - v.2 = 2 * k := ⟨(v.1 - v.2) / 2, by omega⟩
    simp only [hk, Int.mul_ediv_cancel_left _ (show (2 : ℤ) ≠ 0 by norm_num)]
    refine Prod.ext ?_ rfl
    simp only
    omega
  case right_inv =>
    intro v _
    simp only [add_sub_cancel_right, Int.mul_ediv_cancel_left _ (show (2 : ℤ) ≠ 0 by norm_num)]

lemma f5_two {n : ℕ} (h2 : n % 4 = 2) : cntF (fun x y => x ^ 2 + 7 * y ^ 2) n = 0 := by
  unfold cntF
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro v _ hv
  rcases Int.emod_two_eq_zero_or_one v.1 with hx | hx <;>
    rcases Int.emod_two_eq_zero_or_one v.2 with hy | hy
  · obtain ⟨k, hk⟩ : ∃ k, v.1 = 2 * k := ⟨v.1 / 2, by omega⟩
    obtain ⟨m, hm⟩ : ∃ m, v.2 = 2 * m := ⟨v.2 / 2, by omega⟩
    rw [hk, hm] at hv; ring_nf at hv; omega
  · obtain ⟨k, hk⟩ : ∃ k, v.1 = 2 * k := ⟨v.1 / 2, by omega⟩
    obtain ⟨m, hm⟩ : ∃ m, v.2 = 2 * m + 1 := ⟨v.2 / 2, by omega⟩
    rw [hk, hm] at hv; ring_nf at hv; omega
  · obtain ⟨k, hk⟩ : ∃ k, v.1 = 2 * k + 1 := ⟨v.1 / 2, by omega⟩
    obtain ⟨m, hm⟩ : ∃ m, v.2 = 2 * m := ⟨v.2 / 2, by omega⟩
    rw [hk, hm] at hv; ring_nf at hv; omega
  · obtain ⟨k, hk⟩ : ∃ k, v.1 = 2 * k + 1 := ⟨v.1 / 2, by omega⟩
    obtain ⟨m, hm⟩ : ∃ m, v.2 = 2 * m + 1 := ⟨v.2 / 2, by omega⟩
    rw [hk, hm] at hv; ring_nf at hv; omega

lemma parity_cases (x y : ℤ) :
    (∃ k m, x = 2 * k ∧ y = 2 * m) ∨ (∃ k m, x = 2 * k ∧ y = 2 * m + 1) ∨
      (∃ k m, x = 2 * k + 1 ∧ y = 2 * m) ∨ (∃ k m, x = 2 * k + 1 ∧ y = 2 * m + 1) := by
  rcases Int.emod_two_eq_zero_or_one x with hx | hx <;>
    rcases Int.emod_two_eq_zero_or_one y with hy | hy
  · exact Or.inl ⟨x / 2, y / 2, by omega, by omega⟩
  · exact Or.inr (Or.inl ⟨x / 2, y / 2, by omega, by omega⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨x / 2, y / 2, by omega, by omega⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨x / 2, y / 2, by omega, by omega⟩))

lemma f4_even {x y : ℤ} {n : ℕ} (hn : n % 2 = 1) (h : x ^ 2 + 1 * x * y - (-2) * y ^ 2 = n) :
    y % 2 = 0 := by
  rcases parity_cases x y with ⟨k, m, rfl, rfl⟩ | ⟨k, m, rfl, rfl⟩ | ⟨k, m, rfl, rfl⟩ |
    ⟨k, m, rfl, rfl⟩ <;> ring_nf at h <;> omega

lemma f5_odd {n : ℕ} (hn : n % 2 = 1) :
    cntF (fun x y => x ^ 2 + 7 * y ^ 2) n = cnt (-2) 1 n := by
  have hn1 : 1 ≤ n := by omega
  unfold cntF cnt
  apply Finset.card_bij' (fun v _ => (v.1 - v.2, 2 * v.2)) (fun v _ => (v.1 + v.2 / 2, v.2 / 2))
  case hi =>
    intro v hv
    simp only [Finset.mem_filter] at hv ⊢
    have hval : (v.1 - v.2) ^ 2 + 1 * (v.1 - v.2) * (2 * v.2) - (-2) * (2 * v.2) ^ 2 = n := by
      linear_combination hv.2
    exact ⟨box_of_norm (by norm_num) (by norm_num) hval hn1, hval⟩
  case hj =>
    intro v hv
    simp only [Finset.mem_filter] at hv ⊢
    obtain ⟨k, hk⟩ : ∃ k, v.2 = 2 * k := ⟨v.2 / 2, by have := f4_even hn hv.2; omega⟩
    rw [hk, Int.mul_ediv_cancel_left _ (by norm_num)]
    have hval : (v.1 + k) ^ 2 + 7 * k ^ 2 = n := by
      have h1 := hv.2; rw [hk] at h1; linear_combination h1
    exact ⟨box_of_sq (by norm_num) hval, hval⟩
  case left_inv =>
    intro v _
    simp only [Int.mul_ediv_cancel_left _ (show (2 : ℤ) ≠ 0 by norm_num)]
    ext <;> simp
  case right_inv =>
    intro v hv
    simp only [Finset.mem_filter] at hv
    obtain ⟨k, hk⟩ : ∃ k, v.2 = 2 * k := ⟨v.2 / 2, by have := f4_even hn hv.2; omega⟩
    simp only [hk, Int.mul_ediv_cancel_left _ (show (2 : ℤ) ≠ 0 by norm_num)]
    ext
    · simp
    · simp only; omega

/-! ### `x^2 + 3 y^2` -/

lemma f2_four {n : ℕ} (h4 : 4 ∣ n) (hn : 1 ≤ n) :
    cntF (fun x y => x ^ 2 + 3 * y ^ 2) n = cntF (fun x y => x ^ 2 + x * y + y ^ 2) (n / 4) := by
  obtain ⟨m, rfl⟩ := h4
  have hm : 1 ≤ m := by omega
  rw [Nat.mul_div_cancel_left _ (by norm_num)]
  unfold cntF
  apply Finset.card_bij' (fun v _ => ((v.1 - v.2) / 2, v.2)) (fun v _ => (2 * v.1 + v.2, v.2))
  case hi =>
    intro v hv
    simp only [Finset.mem_filter] at hv ⊢
    have he := even_of_sq_mod (x := v.1) (y := v.2) (Or.inl (by rw [hv.2]; push_cast; omega))
    obtain ⟨k, hk⟩ : ∃ k, v.1 - v.2 = 2 * k := ⟨(v.1 - v.2) / 2, by omega⟩
    rw [hk, Int.mul_ediv_cancel_left _ (by norm_num)]
    have hval : k ^ 2 + 1 * k * v.2 - (-1) * v.2 ^ 2 = (m : ℤ) := by
      have h1 := hv.2; push_cast at h1
      have : v.1 = 2 * k + v.2 := by omega
      rw [this] at h1; nlinarith
    exact ⟨box_of_norm (by norm_num) (by norm_num) hval hm, by linear_combination hval⟩
  case hj =>
    intro v hv
    simp only [Finset.mem_filter] at hv ⊢
    have hval : (2 * v.1 + v.2) ^ 2 + 3 * v.2 ^ 2 = ((4 * m : ℕ) : ℤ) := by
      push_cast; linear_combination 4 * hv.2
    exact ⟨box_of_sq (by norm_num) hval, hval⟩
  case left_inv =>
    intro v hv
    simp only [Finset.mem_filter] at hv
    have he := even_of_sq_mod (x := v.1) (y := v.2) (Or.inl (by rw [hv.2]; push_cast; omega))
    obtain ⟨k, hk⟩ : ∃ k, v.1 - v.2 = 2 * k := ⟨(v.1 - v.2) / 2, by omega⟩
    simp only [hk, Int.mul_ediv_cancel_left _ (show (2 : ℤ) ≠ 0 by norm_num)]
    refine Prod.ext ?_ rfl
    simp only
    omega
  case right_inv =>
    intro v _
    simp only [add_sub_cancel_right, Int.mul_ediv_cancel_left _ (show (2 : ℤ) ≠ 0 by norm_num)]

lemma f2_two {n : ℕ} (h2 : n % 4 = 2) : cntF (fun x y => x ^ 2 + 3 * y ^ 2) n = 0 := by
  unfold cntF
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro v _ hv
  rcases parity_cases v.1 v.2 with ⟨k, m, hk, hm⟩ | ⟨k, m, hk, hm⟩ | ⟨k, m, hk, hm⟩ |
    ⟨k, m, hk, hm⟩ <;> rw [hk, hm] at hv <;> ring_nf at hv <;> omega

lemma f1_box {x y : ℤ} {n : ℕ} (hn : 1 ≤ n) (h : x ^ 2 + x * y + y ^ 2 = n) : (x, y) ∈ box n :=
  box_of_norm (a := -1) (b := 1) (by norm_num) (by norm_num) (by linear_combination h) hn

lemma f1_not_both_even {x y : ℤ} {n : ℕ} (hn : n % 2 = 1) (h : x ^ 2 + x * y + y ^ 2 = n) :
    x % 2 = 1 ∨ y % 2 = 1 := by
  rcases parity_cases x y with ⟨k, m, hk, hm⟩ | ⟨k, m, hk, hm⟩ | ⟨k, m, hk, hm⟩ |
    ⟨k, m, hk, hm⟩
  · rw [hk, hm] at h; ring_nf at h; omega
  all_goals omega

/-- For odd `n`, the solutions of `x^2 + x y + y^2 = n` fall into three parity classes of
equal size, permuted by `(x, y) ↦ (-y, x + y)`, and the class with `y` even matches the
solutions of `x^2 + 3 y^2 = n`. -/
lemma f2_odd {n : ℕ} (hn : n % 2 = 1) :
    3 * cntF (fun x y => x ^ 2 + 3 * y ^ 2) n = cntF (fun x y => x ^ 2 + x * y + y ^ 2) n := by
  have hn1 : 1 ≤ n := by omega
  set S := (box n).filter (fun v : ℤ × ℤ => v.1 ^ 2 + v.1 * v.2 + v.2 ^ 2 = n)
  set A := S.filter (fun v : ℤ × ℤ => v.2 % 2 = 0)
  set B := S.filter (fun v : ℤ × ℤ => v.1 % 2 = 0 ∧ v.2 % 2 = 1)
  set C := S.filter (fun v : ℤ × ℤ => v.1 % 2 = 1 ∧ v.2 % 2 = 1)
  have hS : S.card = A.card + B.card + C.card := by
    have h1 := Finset.card_filter_add_card_filter_not (s := S)
      (fun v : ℤ × ℤ => v.2 % 2 = 0)
    have h2 := Finset.card_filter_add_card_filter_not
      (s := S.filter (fun v : ℤ × ℤ => ¬ v.2 % 2 = 0)) (fun v : ℤ × ℤ => v.1 % 2 = 0)
    have eB : (S.filter (fun v : ℤ × ℤ => ¬ v.2 % 2 = 0)).filter
        (fun v : ℤ × ℤ => v.1 % 2 = 0) = B := by
      ext v
      simp only [Finset.mem_filter, B]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h3, by omega⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, by omega⟩, h2⟩
    have eC : (S.filter (fun v : ℤ × ℤ => ¬ v.2 % 2 = 0)).filter
        (fun v : ℤ × ℤ => ¬ v.1 % 2 = 0) = C := by
      ext v
      simp only [Finset.mem_filter, C]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, by omega, by omega⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, by omega⟩, by omega⟩
    rw [eB, eC] at h2
    have eA : S.filter (fun v : ℤ × ℤ => v.2 % 2 = 0) = A := rfl
    rw [eA] at h1
    omega
  have hA : A.card = cntF (fun x y => x ^ 2 + 3 * y ^ 2) n := by
    symm
    unfold cntF
    apply Finset.card_bij' (fun v _ => (v.1 - v.2, 2 * v.2))
      (fun v _ => (v.1 + v.2 / 2, v.2 / 2))
    case hi =>
      intro v hv
      simp only [Finset.mem_filter, A, S] at hv ⊢
      have hval : (v.1 - v.2) ^ 2 + (v.1 - v.2) * (2 * v.2) + (2 * v.2) ^ 2 = n := by
        linear_combination hv.2
      exact ⟨⟨f1_box hn1 hval, hval⟩, by omega⟩
    case hj =>
      intro v hv
      simp only [Finset.mem_filter, A, S] at hv ⊢
      obtain ⟨k, hk⟩ : ∃ k, v.2 = 2 * k := ⟨v.2 / 2, by omega⟩
      rw [hk, Int.mul_ediv_cancel_left _ (by norm_num)]
      have hval : (v.1 + k) ^ 2 + 3 * k ^ 2 = n := by
        have h1 := hv.1.2; rw [hk] at h1; linear_combination h1
      exact ⟨box_of_sq (by norm_num) hval, hval⟩
    case left_inv =>
      intro v _
      simp only [Int.mul_ediv_cancel_left _ (show (2 : ℤ) ≠ 0 by norm_num)]
      ext <;> simp
    case right_inv =>
      intro v hv
      simp only [Finset.mem_filter, A, S] at hv
      obtain ⟨k, hk⟩ : ∃ k, v.2 = 2 * k := ⟨v.2 / 2, by omega⟩
      simp only [hk, Int.mul_ediv_cancel_left _ (show (2 : ℤ) ≠ 0 by norm_num)]
      ext
      · simp
      · simp only; omega
  have hB : B.card = A.card := by
    apply Finset.card_bij' (fun v _ => (v.1 + v.2, -v.1)) (fun v _ => (-v.2, v.1 + v.2))
    case hi =>
      intro v hv
      simp only [Finset.mem_filter, B, A, S] at hv ⊢
      have hval : (v.1 + v.2) ^ 2 + (v.1 + v.2) * -v.1 + (-v.1) ^ 2 = n := by
        linear_combination hv.1.2
      exact ⟨⟨f1_box hn1 hval, hval⟩, by omega⟩
    case hj =>
      intro v hv
      simp only [Finset.mem_filter, B, A, S] at hv ⊢
      have hval : (-v.2) ^ 2 + -v.2 * (v.1 + v.2) + (v.1 + v.2) ^ 2 = n := by
        linear_combination hv.1.2
      have := f1_not_both_even hn hv.1.2
      exact ⟨⟨f1_box hn1 hval, hval⟩, by omega, by omega⟩
    case left_inv => intro v _; exact Prod.ext (by dsimp only; ring) (by dsimp only; ring)
    case right_inv => intro v _; exact Prod.ext (by dsimp only; ring) (by dsimp only; ring)
  have hC : C.card = A.card := by
    apply Finset.card_bij' (fun v _ => (v.2, -v.1 - v.2)) (fun v _ => (-v.1 - v.2, v.1))
    case hi =>
      intro v hv
      simp only [Finset.mem_filter, C, A, S] at hv ⊢
      have hval : v.2 ^ 2 + v.2 * (-v.1 - v.2) + (-v.1 - v.2) ^ 2 = n := by
        linear_combination hv.1.2
      exact ⟨⟨f1_box hn1 hval, hval⟩, by omega⟩
    case hj =>
      intro v hv
      simp only [Finset.mem_filter, C, A, S] at hv ⊢
      have hval : (-v.1 - v.2) ^ 2 + (-v.1 - v.2) * v.1 + v.1 ^ 2 = n := by
        linear_combination hv.1.2
      have := f1_not_both_even hn hv.1.2
      exact ⟨⟨f1_box hn1 hval, hval⟩, by omega, by omega⟩
    case left_inv => intro v _; exact Prod.ext (by dsimp only; ring) (by dsimp only)
    case right_inv => intro v _; exact Prod.ext (by dsimp only) (by dsimp only; ring)
  have hS' : cntF (fun x y => x ^ 2 + x * y + y ^ 2) n = S.card := rfl
  omega

end TuringTask
