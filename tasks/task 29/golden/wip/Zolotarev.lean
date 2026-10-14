import Mathlib
import TuringTask.Layers

/-!
# Zolotarev's and Lerch's theorems (theorems 1 and 2)

* `sign_units_odd_prime_pow`: for an odd prime `p` and `j ≥ 1`, `(ZMod (p^j))ˣ` is cyclic of even
  order `N = p^(j-1) (p - 1)`, so `sgn ν_a = -1` iff `a^(N/2) ≠ 1`. The element `a^(N/2)` is `±1`,
  and modulo `p` it equals `a^((p-1)/2) = J(a | p)` (Fermat and Euler). So `sgn ν_a = J(a | p)`.
* `sign_odd_prime_pow`: `sign_layer` and induction give `sgn μ_a (p^k) = J(a | p)^k = J(a | p^k)`.
* `sign_odd`: for odd `n`, induction over coprime prime powers with `sign_crt`.
* `sign_two_pow`: on the units of `ZMod 2`, `ZMod 4`, `ZMod (2^j)` (`j ≥ 3`) the signs are `1`,
  `(-1)^((a-1)/2)` and `1` (the last group is not cyclic), so `sgn μ_a (2^e)` is `1` for `e = 1`
  and `(-1)^((a-1)/2)` for `e ≥ 2`.
* `sign_even`: for `n = 2^e m` with `m` odd, `sign_crt` gives `sgn = sgn_(2^e)^m sgn_m^(2^e)`,
  which is `sgn_(2^e)`.
-/

namespace TuringTask

open Equiv

lemma units_pow_odd {u : ℤˣ} {m : ℕ} (hm : Odd m) : u ^ m = u := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact one_pow m
  · exact hm.neg_one_pow

lemma units_pow_even {u : ℤˣ} {m : ℕ} (hm : Even m) : u ^ m = 1 := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact one_pow m
  · exact hm.neg_one_pow

lemma sign_zmod_one (a : ℕ) (ha : a.Coprime 1) :
    Perm.sign (Units.mulLeft (ZMod.unitOfCoprime a ha)) = 1 :=
  sign_subsingleton _

lemma sign_units_odd_prime_pow (p j a : ℕ) (hp : p.Prime) (hp2 : p % 2 = 1) (hj : 0 < j)
    [NeZero (p ^ j)] (ha : a.Coprime (p ^ j)) :
    (Perm.sign (Equiv.mulLeft (ZMod.unitOfCoprime a ha)) : ℤ) = jacobiSym a p := by
  haveI := Fact.mk hp
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  haveI : IsCyclic (ZMod (p ^ j))ˣ := ZMod.isCyclic_units_of_prime_pow p hp (by omega) j
  set g := ZMod.unitOfCoprime a ha
  set N := Fintype.card (ZMod (p ^ j))ˣ with hN
  have hNt : N = p ^ (j - 1) * (p - 1) := by
    rw [hN, ZMod.card_units_eq_totient, Nat.totient_prime_pow hp hj]
  have hev : Even N := by
    rw [hNt]
    exact (hp.even_sub_one (by omega)).mul_left _
  have hN2 : N / 2 = p ^ (j - 1) * (p / 2) := by
    have h2 : p - 1 = 2 * (p / 2) := by omega
    rw [hNt, h2, mul_left_comm, Nat.mul_div_cancel_left _ two_pos]
  have hbig : 2 < p ^ j := lt_of_lt_of_le (by omega) (le_trans hp3 (Nat.le_self_pow hj.ne' p))
  haveI : Fact (2 < p ^ j) := ⟨hbig⟩
  have hneg : (-1 : (ZMod (p ^ j))ˣ) ≠ 1 := by
    intro h
    have := Units.ext_iff.mp h
    rw [Units.val_neg, Units.val_one] at this
    exact ZMod.neg_one_ne_one this
  -- `g^(N/2)` is `1` or `-1`
  have hpm : g ^ (N / 2) = 1 ∨ g ^ (N / 2) = -1 := by
    by_cases h1 : g ^ (N / 2) = 1
    · exact Or.inl h1
    · right
      apply eq_of_sq_eq_one_cyclic h1 hneg
      · rw [← pow_mul, show N / 2 * 2 = N by obtain ⟨t, ht⟩ := hev; omega, hN, pow_card_eq_one]
      · simp
  -- reduction modulo `p`
  have hdvd : p ∣ p ^ j := dvd_pow_self p hj.ne'
  have hcast : ZMod.castHom hdvd (ZMod p) ((g ^ (N / 2) : (ZMod (p ^ j))ˣ) : ZMod (p ^ j)) =
      ((jacobiSym a p : ℤ) : ZMod p) := by
    rw [Units.val_pow_eq_pow_val, map_pow, ZMod.coe_unitOfCoprime, map_natCast, hN2, pow_mul,
      ZMod.pow_card_pow, ← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_pow]
    push_cast
    rfl
  have hJ : jacobiSym a p = 1 ∨ jacobiSym a p = -1 := by
    apply jacobiSym.eq_one_or_neg_one
    rw [Int.gcd_natCast_natCast]
    exact Nat.Coprime.coprime_dvd_right hdvd ha
  have hp1 : (1 : ZMod p) ≠ -1 := by
    haveI : Fact (2 < p) := ⟨by omega⟩
    exact fun h => ZMod.neg_one_ne_one h.symm
  rcases hpm with h | h
  · have hs : Perm.sign (Equiv.mulLeft g) = 1 := by
      rcases sign_mulLeft_eq_one_or g with h' | h'
      · exact h'
      · exact absurd h ((sign_mulLeft_eq_neg_one_iff g).mp h').2
    rw [h, Units.val_one, map_one] at hcast
    rw [hs]
    rcases hJ with hJ | hJ
    · rw [hJ]; rfl
    · rw [hJ] at hcast; push_cast at hcast; exact absurd hcast hp1
  · have hs : Perm.sign (Equiv.mulLeft g) = -1 :=
      (sign_mulLeft_eq_neg_one_iff g).mpr ⟨hev, by rw [h]; exact hneg⟩
    rw [h, Units.val_neg, Units.val_one, map_neg, map_one] at hcast
    rw [hs]
    rcases hJ with hJ | hJ
    · rw [hJ] at hcast; push_cast at hcast; exact absurd hcast.symm hp1
    · rw [hJ]; rfl

lemma sign_odd_prime_pow (p a : ℕ) (hp : p.Prime) (hp2 : p % 2 = 1) :
    ∀ (k : ℕ) [NeZero (p ^ k)] (ha : a.Coprime (p ^ k)),
      (Perm.sign (Units.mulLeft (ZMod.unitOfCoprime a ha)) : ℤ) = jacobiSym a (p ^ k) := by
  intro k
  induction k with
  | zero =>
    intro _ ha
    have hJ : jacobiSym a (p ^ 0) = 1 := by rw [pow_zero, jacobiSym.one_right]
    haveI : Subsingleton (ZMod (p ^ 0)) := by rw [pow_zero]; infer_instance
    rw [hJ, sign_subsingleton]
    rfl
  | succ k ih =>
    intro _ ha
    haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
    have ha' : a.Coprime (p ^ k) := Nat.Coprime.coprime_dvd_right (pow_dvd_pow p k.le_succ) ha
    rw [sign_layer p k a hp ha ha', Units.val_mul,
      sign_units_odd_prime_pow p (k + 1) a hp hp2 (Nat.succ_pos k), ih ha', jacobiSym.pow_right,
      jacobiSym.pow_right, pow_succ, mul_comm]

/-- Theorem 1 (Zolotarev, Frobenius). -/
theorem sign_odd (n : ℕ) :
    ∀ [NeZero n], n % 2 = 1 → ∀ (a : ℕ) (ha : a.Coprime n),
      (Perm.sign (Units.mulLeft (ZMod.unitOfCoprime a ha)) : ℤ) = jacobiSym a n := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    intro _ hn a ha
    have hp2 : p % 2 = 1 := by
      rcases hp.eq_two_or_odd with h | h
      · subst h
        exfalso
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        rw [pow_succ] at hn
        omega
      · exact h
    exact sign_odd_prime_pow p a hp hp2 k ha
  | zero => intro h; exact absurd rfl (NeZero.ne 0)
  | one =>
    intro _ _ a ha
    rw [jacobiSym.one_right]
    have := sign_zmod_one a ha
    simpa using this
  | coprime m n hm hn hmn ihm ihn =>
    intro _ hmn2 a ha
    have hm2 : m % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one m with h | h
      · exfalso
        have : 2 ∣ m * n := Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero h) n
        omega
      · exact h
    have hn2 : n % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one n with h | h
      · exfalso
        have : 2 ∣ m * n := Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero h) m
        omega
      · exact h
    haveI : NeZero m := ⟨by omega⟩
    haveI : NeZero n := ⟨by omega⟩
    have ham : a.Coprime m := Nat.Coprime.coprime_dvd_right (dvd_mul_right m n) ha
    have han : a.Coprime n := Nat.Coprime.coprime_dvd_right (dvd_mul_left n m) ha
    rw [sign_crt m n a hmn ha ham han, units_pow_odd (Nat.odd_iff.mpr hn2),
      units_pow_odd (Nat.odd_iff.mpr hm2), Units.val_mul, ihm hm2 a ham, ihn hn2 a han,
      jacobiSym.mul_right]

lemma sign_units_two (a : ℕ) (ha : a.Coprime 2) :
    Perm.sign (Equiv.mulLeft (ZMod.unitOfCoprime a ha)) = 1 := by
  rcases sign_mulLeft_eq_one_or (ZMod.unitOfCoprime a ha) with h | h
  · exact h
  · exfalso
    have := ((sign_mulLeft_eq_neg_one_iff _).mp h).1
    rw [ZMod.card_units_eq_totient] at this
    exact Nat.not_even_one this

lemma sign_units_four (a : ℕ) (ha : a.Coprime 4) :
    (Perm.sign (Equiv.mulLeft (ZMod.unitOfCoprime a ha)) : ℤ) = if a % 4 = 1 then 1 else -1 := by
  have hcard : Fintype.card (ZMod 4)ˣ = 2 := by rw [ZMod.card_units_eq_totient]; rfl
  have key : ZMod.unitOfCoprime a ha = 1 ↔ a % 4 = 1 := by
    rw [Units.ext_iff, ZMod.coe_unitOfCoprime, Units.val_one,
      show (1 : ZMod 4) = ((1 : ℕ) : ZMod 4) by norm_num, ZMod.natCast_eq_natCast_iff']
  split_ifs with h4
  · rcases sign_mulLeft_eq_one_or (ZMod.unitOfCoprime a ha) with h | h
    · rw [h]; rfl
    · exfalso
      have := ((sign_mulLeft_eq_neg_one_iff _).mp h).2
      rw [hcard, pow_one] at this
      exact this (key.mpr h4)
  · have : Perm.sign (Equiv.mulLeft (ZMod.unitOfCoprime a ha)) = -1 := by
      rw [sign_mulLeft_eq_neg_one_iff, hcard, pow_one]
      exact ⟨even_two, fun h => h4 (key.mp h)⟩
    rw [this]; rfl

lemma sign_units_two_pow (j a : ℕ) (hj : 3 ≤ j) [NeZero (2 ^ j)] (ha : a.Coprime (2 ^ j)) :
    Perm.sign (Equiv.mulLeft (ZMod.unitOfCoprime a ha)) = 1 := by
  rcases sign_mulLeft_eq_one_or (ZMod.unitOfCoprime a ha) with h | h
  · exact h
  · exfalso
    have h8 : 8 ≤ 2 ^ j := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
    have := ((sign_units_iff (2 ^ j) _).mp h).1
    rw [← list_iff (2 ^ j) (by omega) (by omega) (by omega),
      ZMod.isCyclic_units_two_pow_iff] at this
    omega

/-- `sgn μ_a` on `ZMod (2^(k+1))`. -/
lemma sign_two_pow (a : ℕ) :
    ∀ (k : ℕ) [NeZero (2 ^ (k + 1))] (ha : a.Coprime (2 ^ (k + 1))),
      (Perm.sign (Units.mulLeft (ZMod.unitOfCoprime a ha)) : ℤ) =
        if k = 0 then 1 else if a % 4 = 1 then 1 else -1 := by
  intro k
  induction k with
  | zero =>
    intro _ ha
    haveI : NeZero (2 ^ 0) := ⟨by norm_num⟩
    have ha' : a.Coprime (2 ^ 0) := by simp
    rw [sign_layer 2 0 a Nat.prime_two ha ha', sign_units_two a ha, one_mul,
      sign_zmod_one a (by simp)]
    rfl
  | succ k ih =>
    intro _ ha
    haveI : NeZero (2 ^ (k + 1)) := ⟨by positivity⟩
    have ha' : a.Coprime (2 ^ (k + 1)) :=
      Nat.Coprime.coprime_dvd_right (pow_dvd_pow 2 (k + 1).le_succ) ha
    rw [sign_layer 2 (k + 1) a Nat.prime_two ha ha', Units.val_mul, ih ha']
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      have ha4 : a.Coprime 4 := ha
      rw [if_pos rfl, mul_one, if_neg (by norm_num)]
      exact sign_units_four a ha4
    · rw [sign_units_two_pow (k + 2) a (by omega) ha, Units.val_one, one_mul,
        if_neg (show k ≠ 0 by omega), if_neg (show k + 1 ≠ 0 by omega)]

/-- Theorem 2 (Lerch). -/
theorem sign_even (n : ℕ) [NeZero n] (hn : n % 2 = 0) (a : ℕ) (ha : a.Coprime n) :
    (Perm.sign (Units.mulLeft (ZMod.unitOfCoprime a ha)) : ℤ) =
      if n % 4 = 2 then 1 else if a % 4 = 1 then 1 else -1 := by
  obtain ⟨e, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (NeZero.ne n)
  have he : 0 < e := by
    rcases Nat.eq_zero_or_pos e with he | he
    · rw [he, pow_zero, one_mul] at hnm
      exfalso
      rw [hnm] at hn
      exact (Nat.not_even_iff_odd.mpr hm) (Nat.even_iff.mpr hn)
    · exact he
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  subst hnm
  have hm0 : m ≠ 0 := by rintro rfl; exact (Nat.not_odd_iff_even.mpr ⟨0, rfl⟩) hm
  haveI : NeZero m := ⟨hm0⟩
  haveI : NeZero (2 ^ (k + 1)) := ⟨by positivity⟩
  have hcop : (2 ^ (k + 1)).Coprime m :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hm)
  have ha1 : a.Coprime (2 ^ (k + 1)) := Nat.Coprime.coprime_dvd_right (dvd_mul_right _ m) ha
  have ha2 : a.Coprime m := Nat.Coprime.coprime_dvd_right (dvd_mul_left m _) ha
  rw [sign_crt _ m a hcop ha ha1 ha2, units_pow_odd hm,
    units_pow_even ((Nat.even_pow' (Nat.succ_ne_zero k)).mpr even_two), mul_one,
    sign_two_pow a k ha1]
  have hm4 : m % 4 = 1 ∨ m % 4 = 3 := by
    obtain ⟨t, ht⟩ := hm
    omega
  congr 1
  apply propext
  constructor
  · rintro rfl
    rcases hm4 with h | h <;> omega
  · intro h
    rcases Nat.eq_zero_or_pos k with hk | hk
    · exact hk
    · exfalso
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have : 2 ^ (k' + 1 + 1) * m = 4 * (2 ^ k' * m) := by ring
      omega

end TuringTask
