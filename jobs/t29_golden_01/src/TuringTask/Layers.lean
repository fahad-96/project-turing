import Mathlib
import TuringTask.Units

/-!
# Splitting multiplication maps on `ZMod n`

For `a` prime to `n`, write `μ_a` for `x ↦ a x` on `ZMod n` and `ν_a` for `u ↦ a u` on the unit
group.
* `sign_split`: a permutation that keeps a set `P` has sign `sign (on P) * sign (on not P)`.
* `sign_units_part`: on the units of `ZMod n`, `μ_a` is `ν_a`.
* `sign_layer`: for `n = p^(k + 1)` the non-units are `p y` with `y` in `ZMod (p^k)`, and on them
  `μ_a` is `μ_a` of `ZMod (p^k)`. So `sgn μ_a (p^(k+1)) = sgn ν_a (p^(k+1)) * sgn μ_a (p^k)`.
* `sign_crt`: for coprime `m, n` the Chinese remainder theorem turns `μ_a` on `ZMod (m n)` into
  `μ_a × μ_a` on `ZMod m × ZMod n`, so `sgn = sgn_m ^ n * sgn_n ^ m`.
-/

namespace TuringTask

open Equiv

lemma sign_split {α : Type*} [Fintype α] [DecidableEq α] (σ : Perm α) (P : α → Prop)
    [DecidablePred P] (h : ∀ x, P (σ x) ↔ P x) :
    Perm.sign σ = Perm.sign (σ.subtypePerm h) *
      Perm.sign (σ.subtypePerm (p := fun x => ¬ P x) (fun x => not_congr (h x))) := by
  rw [← Perm.sign_subtypeCongr]
  congr 1
  ext x
  by_cases hx : P x
  · rw [Perm.subtypeCongr.left_apply _ _ hx]; rfl
  · rw [Perm.subtypeCongr.right_apply _ _ hx]; rfl

lemma sign_subsingleton {α : Type*} [Fintype α] [DecidableEq α] [Subsingleton α] (σ : Perm α) :
    Perm.sign σ = 1 := by
  have : σ = 1 := Equiv.ext fun x => Subsingleton.elim _ _
  rw [this, map_one]

/-- The units of a monoid as a subtype. -/
noncomputable def unitsSubtypeEquiv (M : Type*) [Monoid M] : {x : M // IsUnit x} ≃ Mˣ where
  toFun x := x.2.unit
  invFun u := ⟨u, u.isUnit⟩
  left_inv x := Subtype.ext (IsUnit.unit_spec x.2)
  right_inv _ := Units.ext rfl

lemma isUnit_mul_iff {n : ℕ} (u : (ZMod n)ˣ) (x : ZMod n) :
    IsUnit ((Units.mulLeft u) x) ↔ IsUnit x := by
  change IsUnit ((u : ZMod n) * x) ↔ IsUnit x
  exact ⟨fun h => isUnit_of_mul_isUnit_right h, fun h => u.isUnit.mul h⟩

lemma sign_units_part {n : ℕ} [NeZero n] (u : (ZMod n)ˣ) :
    Perm.sign ((Units.mulLeft u).subtypePerm (isUnit_mul_iff u)) =
      Perm.sign (Equiv.mulLeft u) := by
  apply Perm.sign_eq_sign_of_equiv _ _ (unitsSubtypeEquiv (ZMod n))
  intro x
  apply Units.ext
  change ((Units.mulLeft u) x.1 : ZMod n) = u * x.1
  rfl

lemma not_isUnit_iff_dvd {p k : ℕ} (hp : p.Prime) (x : ZMod (p ^ (k + 1))) :
    ¬ IsUnit x ↔ p ∣ x.val := by
  haveI : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [← ZMod.natCast_zmod_val x, ZMod.isUnit_iff_coprime, ZMod.val_natCast,
    Nat.mod_eq_of_lt (ZMod.val_lt x), Nat.coprime_pow_right_iff (Nat.succ_pos k),
    Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp, not_not]

/-- The non-units of `ZMod (p^(k+1))` are the multiples of `p`, a copy of `ZMod (p^k)`. -/
noncomputable def layerEquiv (p k : ℕ) (hp : p.Prime) [NeZero (p ^ k)]
    [NeZero (p ^ (k + 1))] : ZMod (p ^ k) ≃ {x : ZMod (p ^ (k + 1)) // ¬ IsUnit x} where
  toFun y := ⟨((p * y.val : ℕ) : ZMod (p ^ (k + 1))), by
    rw [not_isUnit_iff_dvd hp, ZMod.val_cast_of_lt]
    · exact dvd_mul_right p _
    · rw [pow_succ']
      exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt y) hp.pos⟩
  invFun x := ((x.1.val / p : ℕ) : ZMod (p ^ k))
  left_inv y := by
    have hlt : p * y.val < p ^ (k + 1) := by
      rw [pow_succ']
      exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt y) hp.pos
    simp only
    rw [ZMod.val_cast_of_lt hlt, Nat.mul_div_cancel_left _ hp.pos, ZMod.natCast_zmod_val]
  right_inv x := by
    have hdvd : p ∣ x.1.val := (not_isUnit_iff_dvd hp x.1).mp x.2
    have hlt : x.1.val / p < p ^ k := by
      rw [Nat.div_lt_iff_lt_mul hp.pos, ← pow_succ]
      exact ZMod.val_lt x.1
    apply Subtype.ext
    simp only
    rw [ZMod.val_cast_of_lt hlt, Nat.mul_div_cancel' hdvd, ZMod.natCast_zmod_val]

lemma sign_layer (p k a : ℕ) (hp : p.Prime) [NeZero (p ^ k)] [NeZero (p ^ (k + 1))]
    (ha : a.Coprime (p ^ (k + 1))) (ha' : a.Coprime (p ^ k)) :
    Perm.sign (Units.mulLeft (ZMod.unitOfCoprime a ha)) =
      Perm.sign (Equiv.mulLeft (ZMod.unitOfCoprime a ha)) *
        Perm.sign (Units.mulLeft (ZMod.unitOfCoprime a ha')) := by
  rw [sign_split _ IsUnit (isUnit_mul_iff _), sign_units_part]
  congr 1
  symm
  apply Perm.sign_eq_sign_of_equiv _ _ (layerEquiv p k hp)
  intro y
  apply Subtype.ext
  change ((p * ((a : ZMod (p ^ k)) * y).val : ℕ) : ZMod (p ^ (k + 1))) =
    (a : ZMod (p ^ (k + 1))) * ((p * y.val : ℕ) : ZMod (p ^ (k + 1)))
  have hay : (a : ZMod (p ^ k)) * y = ((a * y.val : ℕ) : ZMod (p ^ k)) := by
    push_cast; rw [ZMod.natCast_zmod_val]
  rw [hay, ZMod.val_natCast, ← Nat.cast_mul, ZMod.natCast_eq_natCast_iff', pow_succ',
    Nat.mul_mod_mul_left, Nat.mod_mod, show a * (p * y.val) = p * (a * y.val) by ring,
    Nat.mul_mod_mul_left]

lemma sign_prodCongr {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (σ : Perm α) (τ : Perm β) :
    Perm.sign (Equiv.prodCongr σ τ) =
      Perm.sign σ ^ Fintype.card β * Perm.sign τ ^ Fintype.card α := by
  have : Equiv.prodCongr σ τ =
      (Equiv.prodCongrLeft fun _ : β => σ) * (Equiv.prodCongrRight fun _ : α => τ) := by
    ext ⟨x, y⟩ <;> simp [Perm.mul_apply]
  rw [this, map_mul, Perm.sign_prodCongrLeft, Perm.sign_prodCongrRight, Finset.prod_const,
    Finset.prod_const, Finset.card_univ, Finset.card_univ]
  rfl

lemma sign_crt (m n a : ℕ) (hmn : m.Coprime n) [NeZero m] [NeZero n] [NeZero (m * n)]
    (ha : a.Coprime (m * n)) (ham : a.Coprime m) (han : a.Coprime n) :
    Perm.sign (Units.mulLeft (ZMod.unitOfCoprime a ha)) =
      Perm.sign (Units.mulLeft (ZMod.unitOfCoprime a ham)) ^ n *
        Perm.sign (Units.mulLeft (ZMod.unitOfCoprime a han)) ^ m := by
  have hpc := sign_prodCongr (Units.mulLeft (ZMod.unitOfCoprime a ham))
    (Units.mulLeft (ZMod.unitOfCoprime a han))
  rw [ZMod.card, ZMod.card] at hpc
  rw [← hpc]
  apply Perm.sign_eq_sign_of_equiv _ _ (ZMod.chineseRemainder hmn).toEquiv
  intro x
  change (ZMod.chineseRemainder hmn) ((a : ZMod (m * n)) * x) =
    ((a : ZMod m) * ((ZMod.chineseRemainder hmn) x).1,
      (a : ZMod n) * ((ZMod.chineseRemainder hmn) x).2)
  rw [map_mul, map_natCast]
  rfl

end TuringTask
