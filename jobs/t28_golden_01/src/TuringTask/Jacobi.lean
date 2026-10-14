import Mathlib
import TuringTask.Quartic

/-!
# The quartic character of `q` (theorem 4)

Let `p = 1 (mod 4)` be prime, `q = 2, 3 (mod 4)` and `p = c^2 + q d^2`.
* `parity_of_rep`: modulo `4`, `c` is odd and `d` is even.
* `quartic_q`: from `c^2 = -q d^2` in `ZMod p`, `core_u` gives
  `(-q) ^ ((p - 1) / 4) J(d | p) = J(c | p) = J(q | c)`. Write `d = 2^v d₀`. Then
  `J(d | p) = J(2 | p)^v`, and the sign `(-1) ^ ((p - 1) / 4) J(2 | p)^v` is `1`: for
  `p = 1 (mod 8)` both factors are `1`; for `p = 5 (mod 8)` the representation forces
  `d = 2 (mod 4)`, so `v = 1` and both factors are `-1`. Hence
  `q ^ ((p - 1) / 4) = J(q | c)`, and the quartic criterion finishes.
-/

namespace TuringTask

lemma parity_of_rep {p q c d : ℕ} (hp4 : p % 4 = 1) (hq : q % 4 = 2 ∨ q % 4 = 3)
    (h : p = c ^ 2 + q * d ^ 2) : c % 2 = 1 ∧ d % 2 = 0 := by
  have h4 : ((c % 4) ^ 2 + (q % 4) * (d % 4) ^ 2) % 4 = 1 := by
    rw [← hp4, h]
    simp [Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
  have ha := Nat.mod_lt c (show 4 > 0 by norm_num)
  have hb := Nat.mod_lt d (show 4 > 0 by norm_num)
  have hc2 : c % 2 = c % 4 % 2 := by omega
  have hd2 : d % 2 = d % 4 % 2 := by omega
  rw [hc2, hd2]
  generalize c % 4 = a at *
  generalize d % 4 = b at *
  rcases hq with hr | hr <;> rw [hr] at h4 <;>
    interval_cases a <;> interval_cases b <;> simp_all

/-- The sign `(-1) ^ ((p - 1) / 4) J(2 | p)^v` from the representation. -/
lemma quartic_sign {p q c d v d₀ : ℕ} (hp4 : p % 4 = 1) (h : p = c ^ 2 + q * d ^ 2)
    (hc : c % 2 = 1) (hd : d % 2 = 0) (hdv : d = 2 ^ v * d₀) (hd₀ : d₀ % 2 = 1) :
    ((-1 : ZMod p)) ^ ((p - 1) / 4) * ((jacobiSym 2 p ^ v : ℤ) : ZMod p) = 1 := by
  rcases (by omega : p % 8 = 1 ∨ p % 8 = 5) with h8 | h8
  · rw [J_two_p h8, one_pow, Even.neg_one_pow ⟨(p - 1) / 8, by omega⟩]
    simp
  · have hv : v = 1 := by
      have hv0 : v ≠ 0 := by
        rintro rfl
        rw [pow_zero, one_mul] at hdv
        omega
      by_contra hv1
      obtain ⟨w, rfl⟩ : ∃ w, v = w + 2 := ⟨v - 2, by omega⟩
      have hd4 : q * d ^ 2 = 16 * (q * (2 ^ w * d₀) ^ 2) := by
        rw [hdv, pow_add]; ring
      have := sq_mod8_odd hc
      omega
    rw [hv, pow_one, J_two_eq (by omega), if_neg (by omega),
      Odd.neg_one_pow ⟨(p - 1) / 8, by omega⟩]
    push_cast
    ring

theorem quartic_q {p q c d : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1)
    (hq : q % 4 = 2 ∨ q % 4 = 3) (h : p = c ^ 2 + q * d ^ 2) :
    (∃ x : ZMod p, x ^ 4 = (q : ZMod p)) ↔ jacobiSym (q : ℤ) c = 1 := by
  haveI := Fact.mk hp
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hc, hd⟩ := parity_of_rep hp4 hq h
  have hpz : (p : ℤ) = (c : ℤ) ^ 2 + (q : ℤ) * (d : ℤ) ^ 2 := by rw [h]; push_cast; ring
  have hcd : Nat.Coprime c d := coprime_of_rep hp hpz
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · exfalso
      rw [h0] at hcd
      have hc1 : c = 1 := (Nat.coprime_zero_right c).mp hcd
      rw [hc1, h0] at h
      have := hp.two_le
      norm_num at h
      omega
    · exact h0
  have hqd : q ≤ q * d ^ 2 := Nat.le_mul_of_pos_right q (by positivity)
  have hcc : c ≤ c ^ 2 := by nlinarith
  have hqp : q < p := by omega
  have hcp : c < p := by omega
  have hq0 : (q : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hqc : Nat.Coprime q c := by
    have hg : Nat.gcd q c ∣ p := by
      rw [h]
      exact dvd_add (dvd_pow (Nat.gcd_dvd_right q c) two_ne_zero)
        (dvd_mul_of_dvd_left (Nat.gcd_dvd_left q c) _)
    rcases (Nat.dvd_prime hp).mp hg with h1 | h1
    · exact h1
    · exfalso
      have : p ∣ c := h1 ▸ Nat.gcd_dvd_right q c
      have := Nat.le_of_dvd (by omega) this
      omega
  rw [pow4_iff hp hp4 hq0]
  have hsq : ((c : ℤ) : ZMod p) ^ 2 = (-(q : ZMod p)) * ((d : ℤ) : ZMod p) ^ 2 := by
    have : ((p : ℤ) : ZMod p) = 0 := by simp
    rw [hpz] at this; push_cast at this ⊢; linear_combination this
  have hcore := core_u hp hp4 hsq
  obtain ⟨v, d₀, hd₀, hdv⟩ := Nat.exists_eq_two_pow_mul_odd hd0.ne'
  rw [J_d hp4 hpz hcd hdv (Nat.odd_iff.mp hd₀), J_c hp4 hc hpz hcd] at hcore
  have hsign := quartic_sign hp4 h hc hd hdv (Nat.odd_iff.mp hd₀)
  have hk : (q : ZMod p) ^ ((p - 1) / 4) = ((jacobiSym (q : ℤ) c : ℤ) : ZMod p) := by
    rw [← hcore, neg_pow]
    linear_combination (-(q : ZMod p) ^ ((p - 1) / 4)) * hsign
  rw [hk, cast_pm_one hp hp2 (jacobiSym.eq_one_or_neg_one (int_gcd_one hqc))]

end TuringTask
