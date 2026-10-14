import Mathlib
import TuringTask.Power

/-!
# The transposition of a rectangular array (theorem 5)

* `sign_eq_neg_one_pow_card`: for a permutation `σ` of `Fin N`, `sgn σ = (-1)^I`, where `I` is the
  number of inversions, the pairs `x < y` with `σ y < σ x` (from `Perm.sign_eq_prod_prod_Iio`).
* `card_lt_pairs`: `Fin m` has `m.choose 2` pairs `i < i'`.
* Position `j + n i` holds the entry `(i, j)`, and the transposition sends it to `i + m j`
  (`transpose_val`). Comparing positions is lexicographic (`lex_lt`), so `(i, j)` and `(i', j')`
  form an inversion exactly when `i < i'` and `j' < j`. These pairs correspond to a pair `i < i'`
  together with a pair `j' < j`, so `I = choose m 2 * choose n 2` (`card_inversions`).
-/

namespace TuringTask

open Equiv Finset

lemma sign_eq_neg_one_pow_card {N : ℕ} (σ : Perm (Fin N)) :
    (Perm.sign σ : ℤ) =
      (-1) ^ (univ.filter (fun q : Fin N × Fin N => q.1 < q.2 ∧ σ q.2 < σ q.1)).card := by
  rw [Perm.sign_eq_prod_prod_Iio]
  push_cast
  have h1 : ∀ j : Fin N, ∏ i ∈ Iio j, (((if σ i < σ j then 1 else -1 : ℤˣ)) : ℤ) =
      ∏ i, (if i < j ∧ σ j < σ i then (-1 : ℤ) else 1) := by
    intro j
    rw [← filter_gt_eq_Iio, prod_filter]
    apply prod_congr rfl
    intro i _
    by_cases hij : i < j
    · have hne : σ i ≠ σ j := fun h => (ne_of_lt hij) (σ.injective h)
      by_cases hs : σ i < σ j
      · rw [if_pos hij, if_pos hs, if_neg (fun h => absurd h.2 (not_lt.mpr hs.le))]
        rfl
      · rw [if_pos hij, if_neg hs, if_pos ⟨hij, lt_of_le_of_ne (not_lt.mp hs) (Ne.symm hne)⟩]
        rfl
    · rw [if_neg hij, if_neg (fun h => hij h.1)]
  rw [prod_congr rfl (fun j _ => h1 j), prod_comm,
    ← Fintype.prod_prod_type' (f := fun i j => if i < j ∧ σ j < σ i then (-1 : ℤ) else 1),
    prod_ite, prod_const, prod_const_one, mul_one]

lemma card_lt_pairs (m : ℕ) :
    (univ.filter (fun q : Fin m × Fin m => q.1 < q.2)).card = m.choose 2 := by
  rw [card_filter, Fintype.sum_prod_type, sum_comm]
  have h : ∀ j : Fin m, ∑ i : Fin m, (if i < j then 1 else 0) = (j : ℕ) := by
    intro j
    rw [← card_filter, filter_gt_eq_Iio, Fin.card_Iio]
  rw [sum_congr rfl (fun j _ => h j), Fin.sum_univ_eq_sum_range (fun i => i) m, sum_range_id,
    Nat.choose_two_right]

lemma card_gt_pairs (n : ℕ) :
    (univ.filter (fun q : Fin n × Fin n => q.2 < q.1)).card = n.choose 2 := by
  rw [← card_lt_pairs n]
  apply card_nbij' Prod.swap Prod.swap <;> intro q hq <;> simp_all

/-- Comparing positions `j + n i` is lexicographic in `(i, j)`. -/
lemma lex_lt {n i i' j j' : ℕ} (hj : j < n) (hj' : j' < n) :
    j + n * i < j' + n * i' ↔ i < i' ∨ (i = i' ∧ j < j') := by
  constructor
  · intro h
    rcases lt_trichotomy i i' with hi | hi | hi
    · exact Or.inl hi
    · subst hi
      exact Or.inr ⟨rfl, by omega⟩
    · exfalso
      have h2 : n * (i' + 1) ≤ n * i := Nat.mul_le_mul_left n hi
      rw [mul_add, mul_one] at h2
      omega
  · rintro (h | ⟨rfl, h⟩)
    · have h2 : n * (i + 1) ≤ n * i' := Nat.mul_le_mul_left n h
      rw [mul_add, mul_one] at h2
      omega
    · omega

/-- The transposition of the statement. -/
def transposePerm (m n : ℕ) : Perm (Fin (m * n)) :=
  (finProdFinEquiv.symm.trans (Equiv.prodComm (Fin m) (Fin n))).trans
    (finProdFinEquiv.trans (finCongr (Nat.mul_comm n m)))

lemma transpose_val (m n : ℕ) (a : Fin m × Fin n) :
    ((transposePerm m n) (finProdFinEquiv a) : ℕ) = a.1 + m * a.2 := by
  simp [transposePerm]

lemma finProd_val {m n : ℕ} (a : Fin m × Fin n) : ((finProdFinEquiv a : Fin (m * n)) : ℕ) =
    a.2 + n * a.1 := rfl

lemma inversion_iff (m n : ℕ) (a b : Fin m × Fin n) :
    (finProdFinEquiv a < finProdFinEquiv b ∧
      transposePerm m n (finProdFinEquiv b) < transposePerm m n (finProdFinEquiv a)) ↔
      (a.1 < b.1 ∧ b.2 < a.2) := by
  rw [Fin.lt_def, Fin.lt_def, finProd_val, finProd_val, transpose_val, transpose_val,
    lex_lt a.2.2 b.2.2, lex_lt b.1.2 a.1.2, Fin.lt_def, Fin.lt_def]
  have e1 : (a.1 : ℕ) = b.1 ↔ a.1 = b.1 := Fin.val_inj
  have e2 : (b.2 : ℕ) = a.2 ↔ b.2 = a.2 := Fin.val_inj
  omega

lemma card_inversions (m n : ℕ) :
    (univ.filter (fun q : Fin (m * n) × Fin (m * n) =>
      q.1 < q.2 ∧ transposePerm m n q.2 < transposePerm m n q.1)).card =
      m.choose 2 * n.choose 2 := by
  rw [← card_lt_pairs m, ← card_gt_pairs n, ← card_product, ← filter_product, univ_product_univ]
  let L : Fin m × Fin n ≃ Fin (m * n) := finProdFinEquiv
  apply card_nbij'
    (fun q => (((L.symm q.1).1, (L.symm q.2).1), ((L.symm q.1).2, (L.symm q.2).2)))
    (fun r => (L (r.1.1, r.2.1), L (r.1.2, r.2.2)))
  · rintro ⟨x, y⟩ h
    obtain ⟨a, rfl⟩ := L.surjective x
    obtain ⟨b, rfl⟩ := L.surjective y
    simp only [coe_filter, Set.mem_setOf_eq, mem_univ, true_and, Equiv.symm_apply_apply] at h ⊢
    exact (inversion_iff m n a b).mp h
  · rintro ⟨⟨i, i'⟩, ⟨j, j'⟩⟩ h
    simp only [coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at h ⊢
    exact (inversion_iff m n (i, j) (i', j')).mpr ⟨h.1, h.2⟩
  · rintro ⟨x, y⟩ _
    simp only [Prod.mk.eta, Equiv.apply_symm_apply]
  · rintro ⟨⟨i, i'⟩, ⟨j, j'⟩⟩ _
    simp only [Equiv.symm_apply_apply]

theorem sign_transpose' (m n : ℕ) :
    (Perm.sign (transposePerm m n) : ℤ) = (-1) ^ (m.choose 2 * n.choose 2) := by
  rw [sign_eq_neg_one_pow_card, card_inversions]

end TuringTask
