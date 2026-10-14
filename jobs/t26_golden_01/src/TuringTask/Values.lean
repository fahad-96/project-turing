import Mathlib
import TuringTask.Forms

/-!
# Square roots of `-n` modulo `p`, and values of forms modulo `4 K`

* `sq_neg_of`: if `J(-n | p % 4 n) = 1` for an odd prime `p`, then `p ∣ t^2 + n` for some `t`.
  Mathlib's `jacobiSym.mod_right` reduces `J(-n | p)` to `J(-n | p % 4 n)`, and
  `ZMod.isSquare_of_jacobiSym_eq_one` gives the square root.
* `rep_mod_nat`: if `a x^2 + 2 b x y + c y^2 = p` with integers `x, y`, then `p mod 4 K`
  is the value of the form at some `x, y < 2 K`, because the value modulo `4 K` only depends on
  `x` and `y` modulo `2 K`.
-/

namespace TuringTask

lemma sq_neg_of {p : ℕ} (hp : p.Prime) (n M : ℕ) (hM : M = 4 * n) (hodd : p % 2 = 1)
    (h : jacobiSym (-(n : ℤ)) (p % M) = 1) : ∃ t : ℤ, (p : ℤ) ∣ t ^ 2 + n := by
  subst hM
  haveI := Fact.mk hp
  have hJ : jacobiSym (-(n : ℤ)) p = 1 := by
    rw [jacobiSym.mod_right _ (Nat.odd_iff.mpr hodd)]
    simpa using h
  obtain ⟨r, hr⟩ := ZMod.isSquare_of_jacobiSym_eq_one hJ
  refine ⟨(r.val : ℤ), (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp ?_⟩
  push_cast
  rw [ZMod.natCast_zmod_val, sq, ← hr]
  push_cast
  ring

lemma rep_mod_nat {A B C : ℤ} {a b c p K : ℕ} (hA : A = a) (hB : B = 2 * b) (hC : C = c)
    (hK : 0 < K) (h : FormRep A B C p) :
    ∃ x y : ℕ, x < 2 * K ∧ y < 2 * K ∧
      p % (4 * K) = (a * x ^ 2 + 2 * b * x * y + c * y ^ 2) % (4 * K) := by
  subst hA hB hC
  obtain ⟨X, Y, hXY⟩ := h
  have hK' : (0 : ℤ) < 2 * K := by positivity
  set x := X % (2 * K) with hx
  set y := Y % (2 * K) with hy
  have hx0 : 0 ≤ x := Int.emod_nonneg _ hK'.ne'
  have hy0 : 0 ≤ y := Int.emod_nonneg _ hK'.ne'
  have hx1 : x < 2 * K := Int.emod_lt_of_pos _ hK'
  have hy1 : y < 2 * K := Int.emod_lt_of_pos _ hK'
  have eX := Int.emod_add_mul_ediv X (2 * K)
  have eY := Int.emod_add_mul_ediv Y (2 * K)
  set u := X / (2 * K)
  set v := Y / (2 * K)
  refine ⟨x.toNat, y.toNat, by omega, by omega, ?_⟩
  have key : (p : ℤ) = a * x ^ 2 + 2 * b * x * y + c * y ^ 2 +
      4 * K * (a * x * u + a * K * u ^ 2 + b * (x * v + u * y) + 2 * b * K * u * v +
        c * y * v + c * K * v ^ 2) := by
    rw [← hXY, ← eX, ← eY]; ring
  have hxn : ((x.toNat : ℕ) : ℤ) = x := Int.toNat_of_nonneg hx0
  have hyn : ((y.toNat : ℕ) : ℤ) = y := Int.toNat_of_nonneg hy0
  have : ((p % (4 * K) : ℕ) : ℤ) =
      (((a * x.toNat ^ 2 + 2 * b * x.toNat * y.toNat + c * y.toNat ^ 2) % (4 * K) : ℕ) : ℤ) := by
    push_cast
    rw [hxn, hyn, key, Int.add_mul_emod_self_left]
  exact_mod_cast this

lemma prime_eq_of_mod {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : p % q = 0) : p = q :=
  ((Nat.prime_dvd_prime_iff_eq hq hp).mp (Nat.dvd_of_mod_eq_zero h)).symm

lemma natAbs_rep {p n : ℕ} {X Y : ℤ} (h : 1 * X ^ 2 + 0 * X * Y + (n : ℤ) * Y ^ 2 = p) :
    ∃ x y : ℕ, p = x ^ 2 + n * y ^ 2 := by
  refine ⟨X.natAbs, Y.natAbs, ?_⟩
  have : (p : ℤ) = ((X.natAbs ^ 2 + n * Y.natAbs ^ 2 : ℕ) : ℤ) := by
    push_cast
    rw [sq_abs, sq_abs]
    linarith
  exact_mod_cast this

end TuringTask
