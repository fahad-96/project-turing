import Mathlib
import TuringTask.Quad

/-!
# Counting elements of a given norm

In `R = QuadraticAlgebra ℤ a b` (positive definite, see `Quad.lean`) let `p ∣ n` be a prime.
* `cnt_split`: if `p = N(π)` with `π` and `π̄ = star π` prime and `π ∤ π̄`, then every element of
  norm `n` is divisible by `π` or by `π̄`, and by both exactly when it is divisible by `p`. So
  `cnt n = 2 cnt (n / p) - cnt (n / p^2)`, the last term only when `p^2 ∣ n`.
* `cnt_ram`: if `p = N(π)` with `π` prime and `π ∣ π̄`, every element of norm `n` is a multiple
  of `π`, so `cnt n = cnt (n / p)`.
* `cnt_inert`: if `p` is prime in `R`, every element of norm `n` is a multiple of `p`, so
  `cnt n = cnt (n / p^2)` when `p^2 ∣ n` and `cnt n = 0` otherwise.
* `cnt_eq`: these are the recursions of `divSum_rec`, so induction on `n` gives
  `cnt n = w ∑_{d ∣ n} χ d` with `w = cnt 1`.
-/

namespace TuringTask

open scoped Classical

variable {a b : ℤ}

local notation "Nm" => QuadraticAlgebra.norm

lemma intCast_norm (z : QuadraticAlgebra ℤ a b) :
    ((Nm z : ℤ) : QuadraticAlgebra ℤ a b) = z * star z := by
  rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star, eq_intCast]

lemma star_dvd_of_dvd_star {c z : QuadraticAlgebra ℤ a b} (h : c ∣ star z) : star c ∣ z := by
  obtain ⟨u, hu⟩ := h
  refine ⟨star u, ?_⟩
  have := congrArg star hu
  rw [star_star, star_mul, mul_comm] at this
  exact this

/-- An element of norm `n` with `p ∣ n` has the factor `π` or `π̄` of `p = π π̄`. -/
lemma dvd_or_dvd_star {π z : QuadraticAlgebra ℤ a b} {p n : ℕ} (hπ : Nm π = p) (hpr : Prime π)
    (hz : Nm z = n) (hpn : p ∣ n) : π ∣ z ∨ star π ∣ z := by
  have h1 : π ∣ z * star z := by
    rw [← intCast_norm, hz]
    obtain ⟨m, rfl⟩ := hpn
    refine ⟨star π * (m : QuadraticAlgebra ℤ a b), ?_⟩
    rw [← mul_assoc, ← intCast_norm, hπ]; push_cast; ring
  rcases hpr.dvd_or_dvd h1 with h | h
  · exact Or.inl h
  · exact Or.inr (star_dvd_of_dvd_star h)

lemma norm_of_eq {v : ℤ × ℤ} {n : ℕ} (h : v.1 ^ 2 + b * v.1 * v.2 - a * v.2 ^ 2 = n) :
    Nm (⟨v.1, v.2⟩ : QuadraticAlgebra ℤ a b) = n := by
  rw [norm_mk, h]

/-- No element of norm `n` is a multiple of `p` when `p^2 ∤ n`. -/
lemma filter_dvd_empty {p n : ℕ} (h : ¬ p ^ 2 ∣ n) :
    ((box n).filter (fun v : ℤ × ℤ => v.1 ^ 2 + b * v.1 * v.2 - a * v.2 ^ 2 = n ∧
      ((p : ℤ) : QuadraticAlgebra ℤ a b) ∣ (⟨v.1, v.2⟩ : QuadraticAlgebra ℤ a b))).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro v - ⟨hv, hd⟩
  have := map_dvd QuadraticAlgebra.norm hd
  rw [norm_of_eq hv, QuadraticAlgebra.norm_intCast] at this
  have h' : ((p ^ 2 : ℕ) : ℤ) ∣ (n : ℤ) := by push_cast; exact this
  exact h (Int.natCast_dvd_natCast.mp h')

lemma cnt_dvd_p (ha : -2 ≤ a) (hD : b ^ 2 + 4 * a ≤ -3) {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) :
    ((box n).filter (fun v : ℤ × ℤ => v.1 ^ 2 + b * v.1 * v.2 - a * v.2 ^ 2 = n ∧
      ((p : ℤ) : QuadraticAlgebra ℤ a b) ∣ (⟨v.1, v.2⟩ : QuadraticAlgebra ℤ a b))).card =
      if p ^ 2 ∣ n then cnt a b (n / p ^ 2) else 0 := by
  split_ifs with h
  · exact cnt_dvd ha hD _ (by rw [QuadraticAlgebra.norm_intCast]; push_cast; ring)
      (Nat.one_le_pow _ _ hp.pos) h hn
  · exact filter_dvd_empty h

theorem cnt_split (ha : -2 ≤ a) (hD : b ^ 2 + 4 * a ≤ -3) {π : QuadraticAlgebra ℤ a b} {p n : ℕ}
    (hp : p.Prime) (hπ : Nm π = p) (hpr : Prime π) (hpr' : Prime (star π))
    (hna : ¬ π ∣ star π) (hpn : p ∣ n) (hn : 1 ≤ n) :
    (cnt a b n : ℤ) = 2 * cnt a b (n / p) - if p ^ 2 ∣ n then (cnt a b (n / p ^ 2) : ℤ) else 0 := by
  set F := (box n).filter (fun v : ℤ × ℤ => v.1 ^ 2 + b * v.1 * v.2 - a * v.2 ^ 2 = n)
  set A := (box n).filter (fun v : ℤ × ℤ => v.1 ^ 2 + b * v.1 * v.2 - a * v.2 ^ 2 = n ∧
    π ∣ (⟨v.1, v.2⟩ : QuadraticAlgebra ℤ a b))
  set B := (box n).filter (fun v : ℤ × ℤ => v.1 ^ 2 + b * v.1 * v.2 - a * v.2 ^ 2 = n ∧
    star π ∣ (⟨v.1, v.2⟩ : QuadraticAlgebra ℤ a b))
  set C := (box n).filter (fun v : ℤ × ℤ => v.1 ^ 2 + b * v.1 * v.2 - a * v.2 ^ 2 = n ∧
    ((p : ℤ) : QuadraticAlgebra ℤ a b) ∣ (⟨v.1, v.2⟩ : QuadraticAlgebra ℤ a b))
  have hp1 : 1 ≤ p := hp.pos
  have hA : A.card = cnt a b (n / p) := cnt_dvd ha hD π hπ hp1 hpn hn
  have hB : B.card = cnt a b (n / p) :=
    cnt_dvd ha hD (star π) (by rw [QuadraticAlgebra.norm_star, hπ]) hp1 hpn hn
  have hC := cnt_dvd_p (a := a) (b := b) ha hD hp hn
  have hU : A ∪ B = F := by
    ext v
    simp only [A, B, F, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h1, h2, -⟩ | ⟨h1, h2, -⟩) <;> exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      rcases dvd_or_dvd_star hπ hpr (norm_of_eq h2) hpn with h | h
      · exact Or.inl ⟨h1, h2, h⟩
      · exact Or.inr ⟨h1, h2, h⟩
  have hI : A ∩ B = C := by
    ext v
    simp only [A, B, C, Finset.mem_inter, Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, h2, ⟨w, hw⟩⟩, -, -, h4⟩
      refine ⟨h1, h2, ?_⟩
      rw [hw] at h4
      rcases hpr'.dvd_or_dvd h4 with h | h
      · exfalso
        apply hna
        have h' := star_dvd_of_dvd_star (c := star π) (z := star π) (by rwa [star_star])
        rwa [star_star] at h'
      · obtain ⟨u, rfl⟩ := h
        exact ⟨u, by rw [hw, ← mul_assoc, ← intCast_norm, hπ]⟩
    · rintro ⟨h1, h2, ⟨u, hu⟩⟩
      have hpe : ((p : ℤ) : QuadraticAlgebra ℤ a b) = π * star π := by
        rw [← hπ, intCast_norm]
      refine ⟨⟨h1, h2, ⟨star π * u, by rw [hu, hpe, mul_assoc]⟩⟩, h1, h2,
        ⟨π * u, by rw [hu, hpe]; ring⟩⟩
  have key := Finset.card_union_add_card_inter A B
  rw [hU, hI, hA, hB, hC] at key
  have hF : cnt a b n = F.card := rfl
  rw [hF]
  split_ifs at key ⊢ <;> omega

theorem cnt_ram (ha : -2 ≤ a) (hD : b ^ 2 + 4 * a ≤ -3) {π : QuadraticAlgebra ℤ a b} {p n : ℕ}
    (hp : p.Prime) (hπ : Nm π = p) (hpr : Prime π) (has : π ∣ star π) (hpn : p ∣ n)
    (hn : 1 ≤ n) : cnt a b n = cnt a b (n / p) := by
  rw [← cnt_dvd ha hD π hπ hp.pos hpn hn]
  unfold cnt
  congr 1
  ext v
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, h2, ?_⟩
    rcases dvd_or_dvd_star hπ hpr (norm_of_eq h2) hpn with h | h
    · exact h
    · exact has.trans h
  · rintro ⟨h1, h2, -⟩
    exact ⟨h1, h2⟩

theorem cnt_inert (ha : -2 ≤ a) (hD : b ^ 2 + 4 * a ≤ -3) {p n : ℕ} (hp : p.Prime)
    (hpr : Prime ((p : ℤ) : QuadraticAlgebra ℤ a b)) (hpn : p ∣ n) (hn : 1 ≤ n) :
    cnt a b n = if p ^ 2 ∣ n then cnt a b (n / p ^ 2) else 0 := by
  rw [← cnt_dvd_p (a := a) (b := b) ha hD hp hn]
  unfold cnt
  congr 1
  ext v
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, h2, ?_⟩
    have hpN : ((p : ℤ) : QuadraticAlgebra ℤ a b) ∣ (⟨v.1, v.2⟩ : QuadraticAlgebra ℤ a b) *
        star ⟨v.1, v.2⟩ := by
      rw [← intCast_norm, norm_of_eq h2]
      obtain ⟨m, rfl⟩ := hpn
      exact ⟨(m : QuadraticAlgebra ℤ a b), by push_cast; ring⟩
    rcases hpr.dvd_or_dvd hpN with h | h
    · exact h
    · have := star_dvd_of_dvd_star h
      rwa [show star ((p : ℤ) : QuadraticAlgebra ℤ a b) = ((p : ℤ) : QuadraticAlgebra ℤ a b) by
        ext <;> simp] at this
  · rintro ⟨h1, h2, -⟩
    exact ⟨h1, h2⟩

/-- The counting formula `cnt n = cnt 1 * ∑_{d ∣ n} χ d`, given the type of every prime. -/
theorem cnt_eq (ha : -2 ≤ a) (hD : b ^ 2 + 4 * a ≤ -3) (χ : ℕ → ℤ)
    (hmul : ∀ m n, m ≠ 0 → n ≠ 0 → χ (m * n) = χ m * χ n) (hχ1 : χ 1 = 1)
    (htype : ∀ p, p.Prime →
      (χ p = 1 ∧ ∃ π : QuadraticAlgebra ℤ a b, Nm π = p ∧ Prime π ∧ Prime (star π) ∧
        ¬ π ∣ star π) ∨
      (χ p = 0 ∧ ∃ π : QuadraticAlgebra ℤ a b, Nm π = p ∧ Prime π ∧ π ∣ star π) ∨
      (χ p = -1 ∧ Prime ((p : ℤ) : QuadraticAlgebra ℤ a b))) :
    ∀ n, 1 ≤ n → (cnt a b n : ℤ) = cnt a b 1 * divSum χ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.eq_or_lt_of_le hn with rfl | hn2
    · simp [divSum, hχ1]
    have hp := Nat.minFac_prime (show n ≠ 1 by omega)
    have hpn := Nat.minFac_dvd n
    set p := n.minFac
    have hn0 : n ≠ 0 := by omega
    have hlt : n / p < n := Nat.div_lt_self (by omega) hp.one_lt
    have hge : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpn) hp.pos
    have ih1 := ih (n / p) hlt hge
    have ih2 : p ^ 2 ∣ n → (cnt a b (n / p ^ 2) : ℤ) = cnt a b 1 * divSum χ (n / p ^ 2) := by
      intro h2
      have hp2 : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
      exact ih _ (Nat.div_lt_self (by omega) hp2)
        (Nat.div_pos (Nat.le_of_dvd (by omega) h2) (by positivity))
    obtain ⟨r1, r0, rm⟩ := divSum_rec hmul hp hpn hn0
    rcases htype p hp with ⟨hc, π, hπ, hpr, hpr', hna⟩ | ⟨hc, π, hπ, hpr, has⟩ | ⟨hc, hpr⟩
    · rw [cnt_split ha hD hp hπ hpr hpr' hna hpn hn, r1 hc, ih1]
      split_ifs with h2
      · rw [ih2 h2]; ring
      · ring
    · rw [cnt_ram ha hD hp hπ hpr has hpn hn, r0 hc, ih1]
    · rw [cnt_inert ha hD hp hpr hpn hn, rm hc]
      split_ifs with h2
      · rw [ih2 h2]
      · simp

end TuringTask
