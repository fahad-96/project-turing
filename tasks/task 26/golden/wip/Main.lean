import Mathlib
import TuringTask.Classes

/-!
# Euler's product theorem and the five statements

* `rep_two_two_three`: a prime `p = 3, 7 (mod 20)` is `2 a^2 + 2 a b + 3 b^2`. As in `bwd_5`,
  `-5` is a square modulo `p` and some reduced form of discriminant `-20` represents `p`; the
  principal form takes no value `3` or `7` modulo `20`.
* `mul_rep_five`: the composition identity
  `(2 a^2 + 2 a b + 3 b^2) (2 c^2 + 2 c d + 3 d^2) = X^2 + 5 Y^2` with
  `X = 2 a c + a d + b c - 2 b d` and `Y = a d + b c + b d`.
* The five theorems of the task, stated as in `TuringTask/Basic.lean`.
-/

namespace TuringTask

lemma rep_two_two_three {p : ℕ} (hp : p.Prime) (h : p % 20 = 3 ∨ p % 20 = 7) :
    ∃ X Y : ℤ, 2 * X ^ 2 + 2 * X * Y + 3 * Y ^ 2 = p := by
  have hodd : p % 2 = 1 := by omega
  obtain ⟨t, ht⟩ := sq_neg_of hp 5 20 rfl hodd (by rcases h with h | h <;> rw [h] <;> norm_num)
  obtain ⟨c, hc, hr⟩ := lagrange (p := p) (5 : ℤ) t (by exact_mod_cast ht)
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  obtain ⟨a', b', c', h1, h2, hd, hr'⟩ :=
    reduce (-20) (by norm_num) _ p (2 * t) c p rfl hp0 (by linarith) hr
  rcases reduced_5 h1 h2 hd with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exfalso
    obtain ⟨u, v, hu, hv, hm⟩ := rep_mod_nat (a := 1) (b := 0) (c := 5) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num : 0 < 5) hr'
    have hval := vals_5_prin u hu v hv
    simp only at hval
    generalize (1 * u ^ 2 + 2 * 0 * u * v + 5 * v ^ 2) % (4 * 5) = r at hm hval
    omega
  · obtain ⟨X, Y, hXY⟩ := hr'
    exact ⟨X, Y, hXY⟩
  · obtain ⟨X, Y, hXY⟩ := rep_neg hr'
    exact ⟨X, Y, hXY⟩

lemma mul_rep_five {p q : ℕ} {a b c d : ℤ} (hp : 2 * a ^ 2 + 2 * a * b + 3 * b ^ 2 = p)
    (hq : 2 * c ^ 2 + 2 * c * d + 3 * d ^ 2 = q) : ∃ x y : ℕ, p * q = x ^ 2 + 5 * y ^ 2 := by
  refine ⟨(2 * a * c + a * d + b * c - 2 * b * d).natAbs, (a * d + b * c + b * d).natAbs, ?_⟩
  have : ((p * q : ℕ) : ℤ) = (((2 * a * c + a * d + b * c - 2 * b * d).natAbs ^ 2 +
      5 * (a * d + b * c + b * d).natAbs ^ 2 : ℕ) : ℤ) := by
    push_cast
    rw [sq_abs, sq_abs, ← hp, ← hq]
    ring
  exact_mod_cast this

theorem main_five (p : Nat) (hp : p.Prime) :
    (exists x y : Nat, p = x ^ 2 + 5 * y ^ 2) <->
      (p = 5 \/ Membership.mem ({1, 9} : Finset Nat) (p % 20)) := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨x, y, h⟩
    exact fwd_5 hp h
  · rintro (rfl | h)
    · exact ⟨0, 1, by norm_num⟩
    · exact bwd_5 hp h

theorem main_product (p q : Nat) (hp : p.Prime) (hq : q.Prime)
    (hp20 : Membership.mem ({3, 7} : Finset Nat) (p % 20))
    (hq20 : Membership.mem ({3, 7} : Finset Nat) (q % 20)) :
    exists x y : Nat, p * q = x ^ 2 + 5 * y ^ 2 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp20 hq20
  obtain ⟨a, b, hab⟩ := rep_two_two_three hp hp20
  obtain ⟨c, d, hcd⟩ := rep_two_two_three hq hq20
  exact mul_rep_five hab hcd

theorem main_six (p : Nat) (hp : p.Prime) :
    (exists x y : Nat, p = x ^ 2 + 6 * y ^ 2) <->
      Membership.mem ({1, 7} : Finset Nat) (p % 24) := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨x, y, h⟩
    exact fwd_6 hp h
  · exact bwd_6 hp

theorem main_thirteen (p : Nat) (hp : p.Prime) :
    (exists x y : Nat, p = x ^ 2 + 13 * y ^ 2) <->
      (p = 13 \/ Membership.mem ({1, 9, 17, 25, 29, 49} : Finset Nat) (p % 52)) := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨x, y, h⟩
    exact fwd_13 hp h
  · rintro (rfl | h)
    · exact ⟨0, 1, by norm_num⟩
    · exact bwd_13 hp h

theorem main_twenty_one (p : Nat) (hp : p.Prime) :
    (exists x y : Nat, p = x ^ 2 + 21 * y ^ 2) <->
      Membership.mem ({1, 25, 37} : Finset Nat) (p % 84) := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨x, y, h⟩
    exact fwd_21 hp h
  · exact bwd_21 hp

end TuringTask
