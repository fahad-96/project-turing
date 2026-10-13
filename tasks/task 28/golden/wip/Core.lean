import Mathlib
import TuringTask.Thue

/-!
# The Jacobi-symbol core

Let `p = 1 (mod 4)` be prime and `p = c^2 + q d^2` with natural `c` odd, `d > 0`.
* `core_u`: if `c^2 = u d^2` in `ZMod p`, then `u ^ ((p - 1) / 4) J(d | p) = J(c | p)`, by raising
  to the power `(p - 1) / 4` and Euler's criterion. With `u = -q` this computes the quartic
  character of `-q`.
* `J_c`: `J(c | p) = J(p | c) = J(q d^2 | c) = J(q | c)` (reciprocity for `p = 1 (mod 4)`).
* `J_d`: for `d = 2^v d₀` with `d₀` odd, `J(d | p) = J(2 | p)^v`, because
  `J(d₀ | p) = J(p | d₀) = J(c^2 | d₀) = 1`.
* `coprime_of_rep`: `p = c^2 + q d^2` forces `gcd(c, d) = 1`, since `gcd(c, d)^2 ∣ p`.
-/

namespace TuringTask

lemma core_u {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) {u : ZMod p} {c d : ℤ}
    (h : (c : ZMod p) ^ 2 = u * (d : ZMod p) ^ 2) :
    u ^ ((p - 1) / 4) * ((jacobiSym d p : ℤ) : ZMod p) = ((jacobiSym c p : ℤ) : ZMod p) := by
  have hp2 : p ≠ 2 := by omega
  rw [euler_J hp hp2, euler_J hp hp2, show (p - 1) / 2 = 2 * ((p - 1) / 4) by omega, pow_mul,
    pow_mul, h, mul_pow]

lemma coprime_of_rep {p c d : ℕ} {q : ℤ} (hp : p.Prime) (h : (p : ℤ) = c ^ 2 + q * d ^ 2) :
    Nat.Coprime c d := by
  set g := Nat.gcd c d
  obtain ⟨c', hc⟩ := Nat.gcd_dvd_left c d
  obtain ⟨d', hd⟩ := Nat.gcd_dvd_right c d
  have hg : ((g ^ 2 : ℕ) : ℤ) ∣ p := ⟨c' ^ 2 + q * d' ^ 2, by
    rw [h]; push_cast; rw [show (c : ℤ) = g * c' by exact_mod_cast hc,
      show (d : ℤ) = g * d' by exact_mod_cast hd]; ring⟩
  have hg' : g ^ 2 ∣ p := Int.natCast_dvd_natCast.mp hg
  rcases (Nat.dvd_prime hp).mp hg' with h1 | h1
  · exact Nat.pow_eq_one.mp h1 |>.resolve_right (by norm_num)
  · exfalso
    rw [sq] at h1
    rw [← h1] at hp
    rcases Nat.prime_mul_iff.mp hp with ⟨h2, h3⟩ | ⟨h2, h3⟩
    · rw [h3] at h2; exact Nat.not_prime_one h2
    · rw [h3] at h2; exact Nat.not_prime_one h2

lemma int_gcd_one {a b : ℕ} (h : Nat.Coprime a b) : Int.gcd (a : ℤ) b = 1 := by
  rw [Int.gcd_natCast_natCast]; exact h

lemma J_c {p c d : ℕ} {q : ℤ} (hp4 : p % 4 = 1) (hc : c % 2 = 1)
    (h : (p : ℤ) = c ^ 2 + q * d ^ 2) (hcd : Nat.Coprime c d) :
    jacobiSym (c : ℤ) p = jacobiSym q c := by
  rw [← jacobiSym.quadratic_reciprocity_one_mod_four hp4 (Nat.odd_iff.mpr hc), h]
  rw [jacobiSym.mod_left' (a₂ := q * (d : ℤ) ^ 2) (by
    rw [show (c : ℤ) ^ 2 + q * d ^ 2 = q * d ^ 2 + c * c by ring, Int.add_mul_emod_self_left])]
  rw [jacobiSym.mul_left, jacobiSym.sq_one' (int_gcd_one hcd.symm), mul_one]

lemma J_d {p c d : ℕ} {q : ℤ} (hp4 : p % 4 = 1) (h : (p : ℤ) = c ^ 2 + q * d ^ 2)
    (hcd : Nat.Coprime c d) {v d₀ : ℕ} (hd : d = 2 ^ v * d₀) (hd₀ : d₀ % 2 = 1) :
    jacobiSym (d : ℤ) p = jacobiSym 2 p ^ v := by
  have hd0 : jacobiSym (d₀ : ℤ) p = 1 := by
    rw [← jacobiSym.quadratic_reciprocity_one_mod_four hp4 (Nat.odd_iff.mpr hd₀), h]
    have hdd : (d₀ : ℤ) ∣ d := ⟨2 ^ v, by rw [hd]; push_cast; ring⟩
    rw [jacobiSym.mod_left' (a₂ := (c : ℤ) ^ 2) (by
      obtain ⟨k, hk⟩ := hdd
      rw [hk, show (c : ℤ) ^ 2 + q * (d₀ * k) ^ 2 = c ^ 2 + d₀ * (q * d₀ * k ^ 2) by ring,
        Int.add_mul_emod_self_left])]
    apply jacobiSym.sq_one'
    apply int_gcd_one
    exact Nat.Coprime.coprime_dvd_right ⟨2 ^ v, by rw [hd]; ring⟩ hcd
  rw [hd]
  push_cast
  rw [jacobiSym.mul_left, jacobiSym.pow_left, hd0, mul_one]

end TuringTask
