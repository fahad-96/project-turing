import Mathlib
import TuringTask.Zolotarev

/-!
# The power map modulo a prime (theorem 4)

Let `x ↦ x^k` be a bijection of `ZMod p`. Then `k ≠ 0`, the map fixes `0` and permutes the
units. Write `m = |(ZMod p)ˣ| = p - 1` and fix an isomorphism `e` from `Multiplicative (ZMod m)`
onto the cyclic group `(ZMod p)ˣ` (`zmodCyclicMulEquiv`). Through `e` the power map becomes
`y ↦ k y` on `ZMod m`, so `k` is a unit modulo `m`, and the sign is `sgn μ_k` on `ZMod (p - 1)`.
Theorem 2 (`sign_even`) with `n = p - 1` finishes; for `p = 2` the group is trivial.
-/

namespace TuringTask

open Equiv

theorem sign_powMap (p k : ℕ) [NeZero p] (hp : p.Prime)
    (hk : Function.Bijective (fun x : ZMod p => x ^ k)) :
    (Perm.sign (Equiv.ofBijective (fun x : ZMod p => x ^ k) hk) : ℤ) =
      if p % 4 = 1 ∧ k % 4 = 3 then -1 else 1 := by
  haveI := Fact.mk hp
  have hk0 : k ≠ 0 := by
    rintro rfl
    have := hk.1 (a₁ := 0) (a₂ := 1) (by simp)
    exact zero_ne_one this
  set σ : Perm (ZMod p) := Equiv.ofBijective (fun x : ZMod p => x ^ k) hk
  have hσ : ∀ x, IsUnit (σ x) ↔ IsUnit x := fun x => isUnit_pow_iff hk0
  haveI : Subsingleton {x : ZMod p // ¬ IsUnit x} := by
    constructor
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    rw [isUnit_iff_ne_zero, not_not] at hx hy
    exact Subtype.ext (hx.trans hy.symm)
  rw [sign_split σ IsUnit hσ, sign_subsingleton (σ.subtypePerm (p := fun x => ¬ IsUnit x) _),
    mul_one]
  -- the cyclic group of units
  have hcyc := ZMod.isCyclic_units_prime hp
  set m := Nat.card (ZMod p)ˣ with hm
  have hm' : m = p - 1 := by
    rw [hm, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hp]
  have hp2 := hp.two_le
  haveI : NeZero m := ⟨by omega⟩
  let e : Multiplicative (ZMod m) ≃* (ZMod p)ˣ := zmodCyclicMulEquiv hcyc
  let E : {x : ZMod p // IsUnit x} ≃ ZMod m :=
    (unitsSubtypeEquiv (ZMod p)).trans (e.symm.toEquiv.trans Multiplicative.toAdd)
  have hE : ∀ x : {x : ZMod p // IsUnit x},
      E (σ.subtypePerm hσ x) = (k : ZMod m) * E x := by
    intro x
    have h1 : unitsSubtypeEquiv (ZMod p) (σ.subtypePerm hσ x) =
        (unitsSubtypeEquiv (ZMod p) x) ^ k := by
      apply Units.ext
      rfl
    change Multiplicative.toAdd (e.symm (unitsSubtypeEquiv (ZMod p) (σ.subtypePerm hσ x))) =
      (k : ZMod m) * Multiplicative.toAdd (e.symm (unitsSubtypeEquiv (ZMod p) x))
    rw [h1, map_pow, toAdd_pow, nsmul_eq_mul]
  -- `k` is a unit modulo `m`
  have hkm : k.Coprime m := by
    rw [← ZMod.isUnit_iff_coprime]
    obtain ⟨y, hy⟩ := hk.2 ((e (Multiplicative.ofAdd 1) : (ZMod p)ˣ) : ZMod p)
    have hy' : y ^ k = ((e (Multiplicative.ofAdd 1) : (ZMod p)ˣ) : ZMod p) := hy
    have hyu : IsUnit y := (isUnit_pow_iff hk0).mp (by rw [hy']; exact Units.isUnit _)
    refine IsUnit.of_mul_eq_one (E ⟨y, hyu⟩) ?_
    have h2 := hE ⟨y, hyu⟩
    rw [← h2]
    have h3 : unitsSubtypeEquiv (ZMod p) (σ.subtypePerm hσ ⟨y, hyu⟩) =
        e (Multiplicative.ofAdd 1) := by
      apply Units.ext
      exact hy'
    change Multiplicative.toAdd (e.symm (unitsSubtypeEquiv (ZMod p) (σ.subtypePerm hσ ⟨y, hyu⟩)))
      = 1
    rw [h3, MulEquiv.symm_apply_apply]
    rfl
  rw [Perm.sign_eq_sign_of_equiv _ (Units.mulLeft (ZMod.unitOfCoprime k hkm)) E hE]
  rcases Nat.lt_or_ge p 3 with hp3 | hp3
  · -- `p = 2`
    have hm1 : m = 1 := by omega
    haveI : Subsingleton (ZMod m) := by rw [hm1]; infer_instance
    rw [sign_subsingleton]
    have : p % 4 = 2 := by omega
    rw [if_neg (by omega)]
    rfl
  · have hpo : p % 2 = 1 := by
      rcases hp.eq_two_or_odd with h | h
      · omega
      · exact h
    rw [sign_even m (by omega) k hkm]
    have hkodd : k % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one k with h | h
      · exfalso
        have h2k : 2 ∣ Nat.gcd k m := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h) ⟨(p - 1) / 2, by omega⟩
        rw [hkm] at h2k
        omega
      · exact h
    split_ifs with h1 h2 h3 h3 <;> first | rfl | omega

end TuringTask
