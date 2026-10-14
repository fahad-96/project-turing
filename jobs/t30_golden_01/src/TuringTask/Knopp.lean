import Mathlib
import TuringTask.Criteria

/-!
# Knopp's identity (theorem 1)

`∑_{d ∣ n} ∑_{b < d} s(n/d · h + b k, d k) = σ(n) s(h, k)`.
* `sum_saw_mul`: with `g = gcd(r, d)`, `∑_{b < d} ((y + b r/d)) = g ((d/g · y))`, because
  `b ↦ b r mod d` takes each multiple of `g` exactly `g` times (multiplication formula).
* `sum_dsum_shift`: hence
  `∑_{b < d} s(x + b k, d k) = ∑_{r < d k} ((r/(d k))) g(r) ((x r/(g(r) k)))`.
* `sum_by_gcd`: grouping `r` by `g = gcd(r, d)` gives `∑_{g ∣ d} g C(d/g, x)`, where
  `C(e, x) = ∑_{r < e k, gcd(r, e) = 1} ((r/(e k))) ((x r/k))`.
* `coprimeSum_eq`: Möbius inversion of the coprimality condition and `dsum_scale` give
  `C(e, x) = ∑_{f ∣ e} μ(f) s(x f, k)`.
* `knopp`: the divisor sums collapse: `∑_{e ∣ N} ∑_{f ∣ e} μ(f) s((N/e) f h, k) = s(h, k)` for each
  `N`, so the total is `∑_{g ∣ n} g s(h, k) = σ(n) s(h, k)`.
-/

namespace TuringTask

open Finset

lemma sum_saw_mul (d r : ℕ) (hd : 0 < d) (y : ℚ) :
    ∑ b ∈ range d, saw (y + ((b * r : ℕ) : ℚ) / d) =
      (Nat.gcd r d : ℚ) * saw (((d / Nat.gcd r d : ℕ) : ℚ) * y) := by
  set g := Nat.gcd r d with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right r hd
  obtain ⟨e, he⟩ : g ∣ d := Nat.gcd_dvd_right r d
  obtain ⟨r', hr'⟩ : g ∣ r := Nat.gcd_dvd_left r d
  have he0 : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h0 | h0
    · rw [h0, mul_zero] at he; omega
    · exact h0
  have hde : d / g = e := by rw [he, Nat.mul_div_cancel_left _ hg0]
  have hcop : Nat.Coprime r' e := by
    have := Nat.coprime_div_gcd_div_gcd (m := r) (n := d) hg0
    rw [← hg] at this
    rwa [hr', he, Nat.mul_div_cancel_left _ hg0, Nat.mul_div_cancel_left _ hg0] at this
  have hg' : (g : ℚ) ≠ 0 := by exact_mod_cast hg0.ne'
  have he' : (e : ℚ) ≠ 0 := by exact_mod_cast he0.ne'
  rw [hde, show d = e * g by rw [he]; ring, sum_range_mul]
  have hinner : ∀ i ∈ range g, ∑ c ∈ range e, saw (y + (((c + e * i) * r : ℕ) : ℚ) /
      ((e * g : ℕ) : ℚ)) = saw ((e : ℚ) * y) := by
    intro i _
    have h1 : ∀ c ∈ range e, saw (y + (((c + e * i) * r : ℕ) : ℚ) / ((e * g : ℕ) : ℚ)) =
        saw (y + ((c * r' % e : ℕ) : ℚ) / e) := by
      intro c _
      have hsplit : (((c + e * i) * r : ℕ) : ℚ) / ((e * g : ℕ) : ℚ) =
          ((c * r' % e : ℕ) : ℚ) / e + ((c * r' / e + i * r' : ℕ) : ℚ) := by
        rw [hr']
        have := Nat.mod_add_div (c * r') e
        have h' : ((c * r' % e : ℕ) : ℚ) + e * ((c * r' / e : ℕ) : ℚ) = ((c * r' : ℕ) : ℚ) := by
          exact_mod_cast this
        push_cast at h' ⊢
        field_simp
        linear_combination (-1 : ℚ) * h'
      rw [hsplit, ← add_assoc, saw_add_nat]
    rw [sum_congr rfl h1, sum_range_mul_mod (fun c => saw (y + (c : ℚ) / e)) hcop,
      saw_mul_sum e he0]
  rw [sum_congr rfl hinner, sum_const, card_range, nsmul_eq_mul]

/-- `∑_{b < d} s(x + b k, d k)` as one sum over `r < d k`. -/
lemma sum_dsum_shift (d k x : ℕ) (hd : 0 < d) (hk : 0 < k) :
    ∑ b ∈ range d, dsum (x + b * k) (d * k) =
      ∑ r ∈ range (d * k), saw ((r : ℚ) / ((d * k : ℕ) : ℚ)) *
        ((Nat.gcd r d : ℚ) * saw (((d / Nat.gcd r d : ℕ) : ℚ) *
          (((x * r : ℕ) : ℚ) / ((d * k : ℕ) : ℚ)))) := by
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold dsum
  rw [sum_comm]
  apply sum_congr rfl
  intro r _
  rw [← mul_sum, ← sum_saw_mul d r hd]
  congr 1
  apply sum_congr rfl
  intro b _
  congr 1
  push_cast
  field_simp

/-- `s(y, k)` written over the modulus `e k`. -/
lemma dsum_lift (e k y : ℕ) (he : 0 < e) :
    ∑ r ∈ range (e * k), saw ((r : ℚ) / ((e * k : ℕ) : ℚ)) * saw (((y * r : ℕ) : ℚ) / k) =
      dsum y k := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp [dsum]
  have he' : (e : ℚ) ≠ 0 := by exact_mod_cast he.ne'
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [← dsum_scale e y k he]
  unfold dsum
  apply sum_congr rfl
  intro r _
  congr 2
  push_cast
  field_simp

/-- `C(e, x) = ∑_{r < e k, gcd(r, e) = 1} ((r/(e k))) ((x r/k))`. -/
def coprimeSum (e k x : ℕ) : ℚ :=
  ∑ r ∈ (range (e * k)).filter (fun r => Nat.Coprime r e),
    saw ((r : ℚ) / ((e * k : ℕ) : ℚ)) * saw (((x * r : ℕ) : ℚ) / k)

lemma sum_by_gcd (d k x : ℕ) (hd : 0 < d) (hk : 0 < k) :
    ∑ r ∈ range (d * k), saw ((r : ℚ) / ((d * k : ℕ) : ℚ)) *
        ((Nat.gcd r d : ℚ) * saw (((d / Nat.gcd r d : ℕ) : ℚ) *
          (((x * r : ℕ) : ℚ) / ((d * k : ℕ) : ℚ)))) =
      ∑ g ∈ d.divisors, (g : ℚ) * coprimeSum (d / g) k x := by
  rw [← sum_fiberwise_of_maps_to (g := fun r => Nat.gcd r d) (t := d.divisors)
    (fun r _ => Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right r d, hd.ne'⟩)]
  apply sum_congr rfl
  intro g hg
  have hgd : g ∣ d := Nat.dvd_of_mem_divisors hg
  have hg0 : 0 < g := Nat.pos_of_mem_divisors hg
  obtain ⟨e, he⟩ := hgd
  have he0 : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h0 | h0
    · rw [h0, mul_zero] at he; omega
    · exact h0
  have hde : d / g = e := by rw [he, Nat.mul_div_cancel_left _ hg0]
  have hg' : (g : ℚ) ≠ 0 := by exact_mod_cast hg0.ne'
  have he' : (e : ℚ) ≠ 0 := by exact_mod_cast he0.ne'
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [hde]
  unfold coprimeSum
  rw [mul_sum]
  symm
  apply sum_nbij' (fun r' => g * r') (fun r => r / g)
  · intro r' hr'
    simp only [mem_filter, mem_range] at hr' ⊢
    refine ⟨?_, ?_⟩
    · rw [he]
      calc g * r' < g * (e * k) := Nat.mul_lt_mul_of_pos_left hr'.1 hg0
        _ = g * e * k := by ring
    · rw [he, Nat.gcd_mul_left, hr'.2, mul_one]
  · intro r hr
    simp only [mem_filter, mem_range] at hr ⊢
    have hgr : g ∣ r := hr.2 ▸ Nat.gcd_dvd_left r d
    refine ⟨?_, ?_⟩
    · rw [Nat.div_lt_iff_lt_mul hg0]
      calc r < d * k := hr.1
        _ = e * k * g := by rw [he]; ring
    · have := Nat.coprime_div_gcd_div_gcd (m := r) (n := d) (by rw [hr.2]; exact hg0)
      rwa [hr.2, he, Nat.mul_div_cancel_left _ hg0] at this
  · intro r' _
    exact Nat.mul_div_cancel_left _ hg0
  · intro r hr
    simp only [mem_filter, mem_range] at hr
    have hgr : g ∣ r := hr.2 ▸ Nat.gcd_dvd_left r d
    exact Nat.mul_div_cancel' hgr
  · intro r' hr'
    simp only [mem_filter, mem_range] at hr'
    have hgcd : Nat.gcd (g * r') d = g := by rw [he, Nat.gcd_mul_left, hr'.2, mul_one]
    rw [hgcd, hde, he]
    push_cast
    have h1 : ((g : ℚ) * r') / (g * e * k) = (r' : ℚ) / (e * k) := by field_simp
    have h2 : (e : ℚ) * ((x : ℚ) * (g * r') / (g * e * k)) = (x : ℚ) * r' / k := by
      field_simp
    rw [h1, h2]
    ring

lemma sum_moebius_divisors (n : ℕ) :
    ∑ i ∈ n.divisors, ((ArithmeticFunction.moebius i : ℤ) : ℚ) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun F : ArithmeticFunction ℤ => F n)
    ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  have h' : ((∑ i ∈ n.divisors, (ArithmeticFunction.moebius i : ℤ) : ℤ) : ℚ) =
      ((if n = 1 then 1 else 0 : ℤ) : ℚ) := by rw [h]
  push_cast at h'
  rw [h']

lemma coprimeSum_eq (e k x : ℕ) (he : 0 < e) :
    coprimeSum e k x = ∑ f ∈ e.divisors,
      ((ArithmeticFunction.moebius f : ℤ) : ℚ) * dsum (x * f) k := by
  set G : ℕ → ℚ := fun r => saw ((r : ℚ) / ((e * k : ℕ) : ℚ)) * saw (((x * r : ℕ) : ℚ) / k)
    with hG
  have h1 : coprimeSum e k x = ∑ r ∈ range (e * k),
      ∑ f ∈ (Nat.gcd r e).divisors, ((ArithmeticFunction.moebius f : ℤ) : ℚ) * G r := by
    unfold coprimeSum
    rw [sum_filter]
    apply sum_congr rfl
    intro r _
    rw [← sum_mul, sum_moebius_divisors]
    by_cases hc : r.Coprime e
    · rw [if_pos hc, if_pos (Nat.coprime_iff_gcd_eq_one.mp hc), one_mul]
    · rw [if_neg hc, if_neg (fun h' => hc (Nat.coprime_iff_gcd_eq_one.mpr h')), zero_mul]
  have h2 : ∑ r ∈ range (e * k), ∑ f ∈ (Nat.gcd r e).divisors,
      ((ArithmeticFunction.moebius f : ℤ) : ℚ) * G r =
      ∑ f ∈ e.divisors, ∑ r ∈ (range (e * k)).filter (fun r => f ∣ r),
        ((ArithmeticFunction.moebius f : ℤ) : ℚ) * G r := by
    apply sum_comm'
    intro r f
    simp only [mem_range, Nat.mem_divisors, mem_filter, Nat.dvd_gcd_iff]
    have : Nat.gcd r e ≠ 0 := (Nat.gcd_pos_of_pos_right r he).ne'
    constructor
    · rintro ⟨hr, ⟨h1, h2⟩, -⟩; exact ⟨⟨hr, h1⟩, h2, he.ne'⟩
    · rintro ⟨⟨hr, h1⟩, h2, -⟩; exact ⟨hr, ⟨h1, h2⟩, this⟩
  rw [h1, h2]
  apply sum_congr rfl
  intro f hf
  have hfe : f ∣ e := Nat.dvd_of_mem_divisors hf
  have hf0 : 0 < f := Nat.pos_of_mem_divisors hf
  obtain ⟨e', he'⟩ := hfe
  have he'0 : 0 < e' := by
    rcases Nat.eq_zero_or_pos e' with h0 | h0
    · rw [h0, mul_zero] at he'; omega
    · exact h0
  rw [← mul_sum, ← dsum_lift e' k (x * f) he'0]
  congr 1
  apply sum_nbij' (fun r => r / f) (fun r'' => f * r'')
  · intro r hr
    simp only [mem_filter, mem_range] at hr ⊢
    rw [Nat.div_lt_iff_lt_mul hf0]
    calc r < e * k := hr.1
      _ = e' * k * f := by rw [he']; ring
  · intro r'' hr''
    simp only [mem_filter, mem_range] at hr'' ⊢
    refine ⟨?_, dvd_mul_right f r''⟩
    rw [he']
    calc f * r'' < f * (e' * k) := Nat.mul_lt_mul_of_pos_left hr'' hf0
      _ = f * e' * k := by ring
  · intro r hr
    simp only [mem_filter, mem_range] at hr
    exact Nat.mul_div_cancel' hr.2
  · intro r'' _
    exact Nat.mul_div_cancel_left _ hf0
  · intro r hr
    simp only [mem_filter, mem_range] at hr
    obtain ⟨r'', rfl⟩ := hr.2
    rw [Nat.mul_div_cancel_left _ hf0]
    have hf' : (f : ℚ) ≠ 0 := by exact_mod_cast hf0.ne'
    have he'' : (e' : ℚ) ≠ 0 := by exact_mod_cast he'0.ne'
    simp only [hG]
    rw [he']
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp
    have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
    congr 2
    · push_cast; field_simp
    · push_cast; ring_nf

/-- The pairs `(a, b)` with `a b ∣ N`. -/
def pairSet (N : ℕ) : Finset (ℕ × ℕ) :=
  (N.divisors ×ˢ N.divisors).filter (fun p => p.1 * p.2 ∣ N)

lemma sum_pairSet (N : ℕ) (F : ℕ → ℕ → ℚ) :
    ∑ e ∈ N.divisors, ∑ p ∈ e.divisorsAntidiagonal, F p.1 p.2 =
      ∑ p ∈ pairSet N, F p.1 p.2 := by
  rw [sum_comm' (t' := pairSet N) (s' := fun p => {p.1 * p.2})]
  · apply sum_congr rfl
    intro p _
    rw [sum_singleton]
  · intro e p
    simp only [Nat.mem_divisors, Nat.mem_divisorsAntidiagonal, mem_singleton, pairSet,
      mem_filter, mem_product]
    constructor
    · rintro ⟨⟨heN, hN⟩, hp, he⟩
      subst hp
      exact ⟨rfl, ⟨⟨Dvd.dvd.trans (dvd_mul_right _ _) heN, hN⟩,
        ⟨Dvd.dvd.trans (dvd_mul_left _ _) heN, hN⟩⟩, heN⟩
    · rintro ⟨rfl, ⟨⟨-, hN⟩, -⟩, hpN⟩
      refine ⟨⟨hpN, hN⟩, rfl, ?_⟩
      rintro h0
      rw [h0, zero_dvd_iff] at hpN
      exact hN hpN

lemma sum_pairSet_left (N : ℕ) (F : ℕ → ℕ → ℚ) :
    ∑ p ∈ pairSet N, F p.1 p.2 = ∑ a ∈ N.divisors, ∑ b ∈ (N / a).divisors, F a b := by
  apply sum_finset_product'
  intro p
  simp only [pairSet, mem_filter, mem_product, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨⟨ha, hN⟩, -⟩, hab⟩
    refine ⟨⟨ha, hN⟩, (Nat.dvd_div_iff_mul_dvd ha).mpr hab, ?_⟩
    exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) ha)
      (Nat.pos_of_dvd_of_pos ha (Nat.pos_of_ne_zero hN))).ne'
  · rintro ⟨⟨ha, hN⟩, hb, -⟩
    have hab := (Nat.dvd_div_iff_mul_dvd ha).mp hb
    exact ⟨⟨⟨ha, hN⟩, ⟨Dvd.dvd.trans (dvd_mul_left _ _) hab, hN⟩⟩, hab⟩

lemma sum_pairSet_right (N : ℕ) (F : ℕ → ℕ → ℚ) :
    ∑ p ∈ pairSet N, F p.1 p.2 = ∑ b ∈ N.divisors, ∑ a ∈ (N / b).divisors, F a b := by
  apply sum_finset_product_right'
  intro p
  simp only [pairSet, mem_filter, mem_product, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨-, ⟨hb, hN⟩⟩, hab⟩
    refine ⟨⟨hb, hN⟩, (Nat.dvd_div_iff_mul_dvd hb).mpr (by rwa [mul_comm]), ?_⟩
    exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hb)
      (Nat.pos_of_dvd_of_pos hb (Nat.pos_of_ne_zero hN))).ne'
  · rintro ⟨⟨hb, hN⟩, ha, -⟩
    have hab := (Nat.dvd_div_iff_mul_dvd hb).mp ha
    rw [mul_comm] at hab
    exact ⟨⟨⟨Dvd.dvd.trans (dvd_mul_right _ _) hab, hN⟩, ⟨hb, hN⟩⟩, hab⟩

/-- The divisor sums collapse. -/
lemma collapse (N : ℕ) (hN : 0 < N) (A : ℕ → ℚ) :
    ∑ e ∈ N.divisors, ∑ f ∈ e.divisors,
      ((ArithmeticFunction.moebius f : ℤ) : ℚ) * A (N / e * f) = A 1 := by
  have h1 : ∀ e ∈ N.divisors, ∑ f ∈ e.divisors,
      ((ArithmeticFunction.moebius f : ℤ) : ℚ) * A (N / e * f) =
      ∑ p ∈ e.divisorsAntidiagonal, ((ArithmeticFunction.moebius p.1 : ℤ) : ℚ) * A (N / p.2) := by
    intro e he
    obtain ⟨c, hc⟩ := Nat.dvd_of_mem_divisors he
    have he0 : 0 < e := Nat.pos_of_mem_divisors he
    rw [Nat.sum_divisorsAntidiagonal (fun a b => ((ArithmeticFunction.moebius a : ℤ) : ℚ) *
      A (N / b))]
    apply sum_congr rfl
    intro f hf
    obtain ⟨g, hg⟩ := Nat.dvd_of_mem_divisors hf
    have hf0 : 0 < f := Nat.pos_of_mem_divisors hf
    have hg0 : 0 < g := by
      rcases Nat.eq_zero_or_pos g with h0 | h0
      · rw [h0, mul_zero] at hg; omega
      · exact h0
    congr 2
    rw [hc, Nat.mul_div_cancel_left _ he0, hg, Nat.mul_div_cancel_left _ hf0,
      show f * g * c = f * c * g by ring, Nat.mul_div_cancel _ hg0, mul_comm]
  rw [sum_congr rfl h1, sum_pairSet N (fun a b => ((ArithmeticFunction.moebius a : ℤ) : ℚ) *
    A (N / b)), sum_pairSet_right N (fun a b => ((ArithmeticFunction.moebius a : ℤ) : ℚ) *
    A (N / b))]
  simp_rw [← sum_mul, sum_moebius_divisors]
  rw [sum_eq_single N]
  · rw [Nat.div_self hN, if_pos rfl, one_mul]
  · intro j hj hjN
    have hj0 := Nat.pos_of_mem_divisors hj
    have : N / j ≠ 1 := by
      intro h'
      have := Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hj)
      rw [h', one_mul] at this
      exact hjN this
    rw [if_neg this, zero_mul]
  · intro h'
    exact absurd (Nat.mem_divisors_self N hN.ne') h'

/-- Theorem 1 in the form used by `Main`. -/
theorem knopp (h k n : ℕ) :
    ∑ d ∈ n.divisors, ∑ b ∈ range d, dsum (n / d * h + b * k) (d * k) =
      (ArithmeticFunction.sigma 1 n : ℚ) * dsum h k := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp [dsum]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  set A : ℕ → ℚ := fun m => dsum (m * h) k with hA
  have step : ∀ d ∈ n.divisors, ∑ b ∈ range d, dsum (n / d * h + b * k) (d * k) =
      ∑ p ∈ d.divisorsAntidiagonal, (p.1 : ℚ) * ∑ f ∈ p.2.divisors,
        ((ArithmeticFunction.moebius f : ℤ) : ℚ) * A (n / (p.1 * p.2) * f) := by
    intro d hd
    have hd0 := Nat.pos_of_mem_divisors hd
    rw [sum_dsum_shift d k _ hd0 hk, sum_by_gcd d k _ hd0 hk,
      ← Nat.sum_divisorsAntidiagonal (fun a b => (a : ℚ) * coprimeSum b k (n / d * h))]
    apply sum_congr rfl
    intro p hp
    have hp' := Nat.mem_divisorsAntidiagonal.mp hp
    have hp2 : 0 < p.2 := by
      rcases Nat.eq_zero_or_pos p.2 with h0 | h0
      · rw [h0, mul_zero] at hp'; exact absurd hp'.1.symm hp'.2
      · exact h0
    rw [coprimeSum_eq _ _ _ hp2, hp'.1]
    congr 1
    apply sum_congr rfl
    intro f _
    simp only [hA]
    congr 2
    ring
  rw [sum_congr rfl step, sum_pairSet n (fun a b => (a : ℚ) * ∑ f ∈ b.divisors,
    ((ArithmeticFunction.moebius f : ℤ) : ℚ) * A (n / (a * b) * f)),
    sum_pairSet_left n (fun a b => (a : ℚ) * ∑ f ∈ b.divisors,
    ((ArithmeticFunction.moebius f : ℤ) : ℚ) * A (n / (a * b) * f)),
    ArithmeticFunction.sigma_one_apply, Nat.cast_sum, sum_mul]
  apply sum_congr rfl
  intro g hg
  have hg0 := Nat.pos_of_mem_divisors hg
  have hN : 0 < n / g := Nat.div_pos (Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hg)) hg0
  rw [← mul_sum]
  congr 1
  have := collapse (n / g) hN A
  simp only [hA, one_mul] at this
  rw [← this]
  apply sum_congr rfl
  intro e _
  apply sum_congr rfl
  intro f _
  rw [Nat.div_div_eq_div_mul]

end TuringTask
