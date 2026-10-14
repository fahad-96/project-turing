import Mathlib

/-!
# The sawtooth function and Dedekind sums

`saw q = ((q))` is `q - ⌊q⌋ - 1/2` for `q ∉ ℤ` and `0` for `q ∈ ℤ`.
* `saw_add_int`, `saw_neg`: period `1`, odd.
* `saw_natCast_div`: `((m / y)) = (m mod y)/y - 1/2`, or `0` when `y ∣ m`.
* `saw_mul_sum` (the multiplication formula): `∑_{j < d} ((q + j/d)) = ((d q))`. The difference
  of the two sides does not change under `q ↦ q + 1/d`, and it vanishes on `[0, 1/d)`.
* `sum_range_mul`: `∑_{r < k d} f r = ∑_{c < d} ∑_{t < k} f (t + k c)`.
* `sum_range_mul_mod`: for `c` prime to `e`, `j ↦ j c mod e` permutes `{0, …, e - 1}`.

`dsum h k = ∑_{r < k} ((r/k)) ((h r/k))`.
* `dsum_eq`: the hypothesis `hs` of the task says `s h k = dsum h k`.
* `dsum_mod`: `dsum h k` depends only on `h mod k`.
* `dsum_sub`: `dsum (k - h) k = - dsum h k` (`((-x)) = -((x))`).
* `dsum_inv`: if `h h' ≡ 1 (mod k)`, then `dsum h' k = dsum h k` (substitute `r ↦ h' r mod k`).
* `dsum_scale`: `dsum (d h) (d k) = dsum h k` (write `r = t + k c` and use the multiplication
  formula in `c`).
-/

namespace TuringTask

open Finset

/-- The sawtooth function `((q))`. -/
def saw (q : ℚ) : ℚ := if Int.fract q = 0 then 0 else Int.fract q - 1 / 2

lemma saw_add_int (q : ℚ) (z : ℤ) : saw (q + z) = saw q := by
  simp [saw, Int.fract_add_intCast]

lemma saw_add_nat (q : ℚ) (n : ℕ) : saw (q + n) = saw q := by
  have := saw_add_int q n
  simpa using this

lemma saw_int (z : ℤ) : saw z = 0 := by simp [saw]

lemma saw_nat (n : ℕ) : saw n = 0 := by simp [saw]

lemma saw_neg (q : ℚ) : saw (-q) = - saw q := by
  unfold saw
  by_cases h : Int.fract q = 0
  · rw [if_pos h, if_pos (Int.fract_neg_eq_zero.mpr h), neg_zero]
  · rw [if_neg h, if_neg (fun h' => h (Int.fract_neg_eq_zero.mp h')), Int.fract_neg h]
    ring

lemma saw_of_mem_Ioo {q : ℚ} (h0 : 0 < q) (h1 : q < 1) : saw q = q - 1 / 2 := by
  have hf : Int.fract q = q := Int.fract_eq_self.mpr ⟨h0.le, h1⟩
  unfold saw
  rw [hf, if_neg h0.ne']

lemma saw_natCast_div (m y : ℕ) (hy : 0 < y) :
    saw ((m : ℚ) / y) = if m % y = 0 then 0 else ((m % y : ℕ) : ℚ) / y - 1 / 2 := by
  unfold saw
  rw [Int.fract_div_natCast_eq_div_natCast_mod]
  have hy' : (y : ℚ) ≠ 0 := by exact_mod_cast hy.ne'
  by_cases h : m % y = 0
  · rw [if_pos (by rw [h]; simp), if_pos h]
  · rw [if_neg (by rw [div_eq_zero_iff]; push Not; exact ⟨by exact_mod_cast h, hy'⟩), if_neg h]

/-- The difference in the multiplication formula. -/
def sawDefect (d : ℕ) (q : ℚ) : ℚ := (∑ j ∈ range d, saw (q + j / d)) - saw (d * q)

lemma sawDefect_shift (d : ℕ) (hd : 0 < d) (q : ℚ) :
    sawDefect d (q + 1 / d) = sawDefect d q := by
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  unfold sawDefect
  have h1 : ∑ j ∈ range d, saw (q + 1 / d + j / d) =
      ∑ j ∈ range d, saw (q + ((j + 1 : ℕ) : ℚ) / d) := by
    apply sum_congr rfl
    intro j _
    congr 1
    push_cast
    ring
  have h2 : ∑ j ∈ range d, saw (q + ((j + 1 : ℕ) : ℚ) / d) =
      ∑ j ∈ range d, saw (q + (j : ℚ) / d) := by
    obtain ⟨c, rfl⟩ : ∃ c, d = c + 1 := ⟨d - 1, by omega⟩
    rw [sum_range_succ (fun j => saw (q + ((j + 1 : ℕ) : ℚ) / ((c + 1 : ℕ) : ℚ))),
      sum_range_succ' (fun j => saw (q + (j : ℚ) / ((c + 1 : ℕ) : ℚ)))]
    have e1 : saw (q + ((c + 1 : ℕ) : ℚ) / ((c + 1 : ℕ) : ℚ)) = saw q := by
      rw [div_self (by positivity), show q + 1 = q + ((1 : ℕ) : ℚ) by norm_num, saw_add_nat]
    have e2 : saw (q + ((0 : ℕ) : ℚ) / ((c + 1 : ℕ) : ℚ)) = saw q := by simp
    rw [e1, e2]
  have h3 : saw (d * (q + 1 / d)) = saw (d * q) := by
    rw [show (d : ℚ) * (q + 1 / d) = d * q + ((1 : ℕ) : ℚ) by field_simp; push_cast; ring,
      saw_add_nat]
  rw [h1, h2, h3]

lemma sawDefect_shift_nat (d : ℕ) (hd : 0 < d) (q : ℚ) (n : ℕ) :
    sawDefect d (q + n / d) = sawDefect d q := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show q + ((n + 1 : ℕ) : ℚ) / d = (q + n / d) + 1 / d by push_cast; ring,
      sawDefect_shift d hd, ih]

lemma sawDefect_base (d : ℕ) (hd : 0 < d) (q : ℚ) (h0 : 0 ≤ q) (h1 : q < 1 / d) :
    sawDefect d q = 0 := by
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  unfold sawDefect
  have hsum : ∑ j ∈ range d, (j : ℚ) = d * (d - 1) / 2 := by
    have := sum_range_id_mul_two d
    have h' : ((∑ j ∈ range d, j : ℕ) : ℚ) * 2 = (d * (d - 1) : ℕ) := by exact_mod_cast this
    rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_one, Nat.cast_sum] at h'
    linarith
  have hdq : (d : ℚ) * q < 1 := by
    have := mul_lt_mul_of_pos_left h1 hd'
    rwa [mul_one_div_cancel hd'.ne'] at this
  rcases h0.lt_or_eq with hq | hq
  · -- `0 < q`: every term is in `(0, 1)`
    have hterm : ∀ j ∈ range d, saw (q + j / d) = q + j / d - 1 / 2 := by
      intro j hj
      apply saw_of_mem_Ioo (by positivity)
      have hj' : (j : ℚ) + 1 ≤ d := by exact_mod_cast (mem_range.mp hj)
      have : (j : ℚ) / d + q < (j + 1) / d := by
        rw [add_div]; linarith
      calc q + j / d < (j + 1) / d := by linarith
        _ ≤ 1 := by rw [div_le_one hd']; exact hj'
    rw [sum_congr rfl hterm, saw_of_mem_Ioo (by positivity) hdq, sum_sub_distrib, sum_add_distrib,
      sum_const, card_range, ← sum_div, hsum, sum_const, card_range]
    field_simp
    ring
  · -- `q = 0`
    subst hq
    have hterm : ∀ j ∈ range d, saw (0 + j / d) = if j = 0 then 0 else (j : ℚ) / d - 1 / 2 := by
      intro j hj
      split_ifs with h
      · subst h; simp [saw]
      · rw [zero_add]
        apply saw_of_mem_Ioo
        · have : (0 : ℚ) < j := by exact_mod_cast Nat.pos_of_ne_zero h
          positivity
        · rw [div_lt_one hd']; exact_mod_cast mem_range.mp hj
    rw [sum_congr rfl hterm, mul_zero, show saw 0 = 0 by simp [saw]]
    obtain ⟨c, rfl⟩ : ∃ c, d = c + 1 := ⟨d - 1, by omega⟩
    rw [sum_range_succ']
    simp only [Nat.succ_ne_zero, if_false, if_true, add_zero, sub_zero]
    have hsum' : ∑ j ∈ range c, ((j + 1 : ℕ) : ℚ) = (c + 1) * c / 2 := by
      have := hsum
      rw [sum_range_succ'] at this
      push_cast at this ⊢
      linarith
    rw [sum_sub_distrib, ← sum_div, hsum', sum_const, card_range]
    push_cast
    field_simp
    ring

/-- The multiplication formula `∑_{j < d} ((q + j/d)) = ((d q))`. -/
lemma saw_mul_sum (d : ℕ) (hd : 0 < d) (q : ℚ) :
    ∑ j ∈ range d, saw (q + j / d) = saw (d * q) := by
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  -- write `q = q₀ + n/d` with `0 ≤ q₀ < 1/d` and an integer `n = ⌊d q⌋`
  set n := ⌊(d : ℚ) * q⌋ with hn
  set q₀ := q - n / d with hq₀
  have hq0 : 0 ≤ q₀ := by
    have := Int.floor_le ((d : ℚ) * q)
    rw [hq₀, sub_nonneg, div_le_iff₀ hd']
    linarith
  have hq1 : q₀ < 1 / d := by
    have := Int.lt_floor_add_one ((d : ℚ) * q)
    rw [hq₀, sub_lt_iff_lt_add, ← add_div, lt_div_iff₀ hd']
    linarith
  have key : sawDefect d q = sawDefect d q₀ := by
    rcases le_or_gt 0 n with hn0 | hn0
    · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hn0
      have : q = q₀ + (m : ℚ) / d := by rw [hq₀, hm]; push_cast; ring
      rw [this, sawDefect_shift_nat d hd]
    · obtain ⟨m, hm⟩ := Int.exists_eq_neg_ofNat hn0.le
      have : q₀ = q + (m : ℚ) / d := by rw [hq₀, hm]; push_cast; ring
      rw [this, sawDefect_shift_nat d hd]
  have h0 := sawDefect_base d hd q₀ hq0 hq1
  unfold sawDefect at key h0
  linarith

lemma sum_range_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (k d : ℕ) :
    ∑ r ∈ range (k * d), f r = ∑ c ∈ range d, ∑ t ∈ range k, f (t + k * c) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [mul_add, mul_one, sum_range_add, ih, sum_range_succ]
    congr 1
    apply sum_congr rfl
    intro t _
    rw [add_comm]

lemma sum_range_mul_mod {M : Type*} [AddCommMonoid M] (F : ℕ → M) {c e : ℕ}
    (hce : Nat.Coprime c e) :
    ∑ j ∈ range e, F (j * c % e) = ∑ j ∈ range e, F j := by
  rcases Nat.eq_zero_or_pos e with he | he
  · subst he; simp
  have hmaps : Set.MapsTo (fun j => j * c % e) (range e : Set ℕ) (range e : Set ℕ) := by
    intro j _
    simp only [coe_range, Set.mem_Iio]
    exact Nat.mod_lt _ he
  have hinj : Set.InjOn (fun j => j * c % e) (range e : Set ℕ) := by
    intro a ha b hb hab
    simp only [coe_range, Set.mem_Iio] at ha hb
    have h1 : a * c ≡ b * c [MOD e] := hab
    have h2 := Nat.ModEq.cancel_right_of_coprime (by rw [Nat.gcd_comm]; exact hce) h1
    rwa [Nat.ModEq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h2
  exact sum_nbij (fun j => j * c % e) (fun j hj => hmaps hj) hinj
    (surjOn_of_injOn_of_card_le _ hmaps hinj le_rfl) (fun _ _ => rfl)



/-- The Dedekind sum `s(h, k)`. -/
def dsum (h k : ℕ) : ℚ := ∑ r ∈ range k, saw ((r : ℚ) / k) * saw (((h * r : ℕ) : ℚ) / k)

lemma dsum_eq (s : ℕ → ℕ → ℚ)
    (hs : ∀ x y : ℕ, s x y = ∑ r ∈ range y, ((r : ℚ) / y - 1 / 2) *
      (if x * r % y = 0 then 0 else ((x * r % y : ℕ) : ℚ) / y - 1 / 2)) (h k : ℕ) :
    s h k = dsum h k := by
  rw [hs, dsum]
  apply sum_congr rfl
  intro r hr
  have hk : 0 < k := lt_of_le_of_lt (Nat.zero_le r) (mem_range.mp hr)
  have hk' : (0 : ℚ) < k := by exact_mod_cast hk
  rw [saw_natCast_div (h * r) k hk]
  rcases Nat.eq_zero_or_pos r with h0 | h0
  · subst h0; simp
  · rw [saw_of_mem_Ioo (by positivity) (by rw [div_lt_one hk']; exact_mod_cast mem_range.mp hr)]

lemma saw_natCast_div_mod (m k : ℕ) (hk : 0 < k) :
    saw (((m % k : ℕ) : ℚ) / k) = saw ((m : ℚ) / k) := by
  rw [saw_natCast_div _ _ hk, saw_natCast_div _ _ hk, Nat.mod_mod]

lemma saw_natCast_div_congr {m m' k : ℕ} (hk : 0 < k) (h : m % k = m' % k) :
    saw ((m : ℚ) / k) = saw ((m' : ℚ) / k) := by
  rw [← saw_natCast_div_mod m k hk, ← saw_natCast_div_mod m' k hk, h]

lemma dsum_mod (h k : ℕ) : dsum h k = dsum (h % k) k := by
  unfold dsum
  apply sum_congr rfl
  intro r hr
  have hk : 0 < k := lt_of_le_of_lt (Nat.zero_le r) (mem_range.mp hr)
  rw [saw_natCast_div_congr hk (Nat.mod_mul_mod h r k).symm]

lemma dsum_sub (h k : ℕ) (hhk : h ≤ k) : dsum (k - h) k = - dsum h k := by
  unfold dsum
  rw [← sum_neg_distrib]
  apply sum_congr rfl
  intro r hr
  have hk : 0 < k := lt_of_le_of_lt (Nat.zero_le r) (mem_range.mp hr)
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have : (((k - h) * r : ℕ) : ℚ) / k = -((((h * r : ℕ) : ℚ) / k)) + (r : ℕ) := by
    rw [Nat.cast_mul, Nat.cast_sub hhk, Nat.cast_mul]
    field_simp
    ring
  rw [this, saw_add_nat, saw_neg]
  ring

lemma dsum_inv (h h' k : ℕ) (hinv : h * h' % k = 1 % k) : dsum h' k = dsum h k := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp [dsum]
  have hcop : Nat.Coprime h' k :=
    Nat.coprime_of_mul_modEq_one h (by rw [mul_comm]; exact hinv)
  unfold dsum
  rw [← sum_range_mul_mod (fun r => saw ((r : ℚ) / k) * saw (((h * r : ℕ) : ℚ) / k)) hcop]
  apply sum_congr rfl
  intro t _
  rw [mul_comm]
  congr 1
  · exact saw_natCast_div_congr hk (by rw [Nat.mod_mod, mul_comm])
  · apply saw_natCast_div_congr hk
    calc t % k = t * (1 % k) % k := by rw [Nat.mul_mod_mod, mul_one]
      _ = t * (h * h' % k) % k := by rw [hinv]
      _ = h * (t * h' % k) % k := by rw [Nat.mul_mod_mod, Nat.mul_mod_mod]; ring_nf

lemma dsum_scale (d h k : ℕ) (hd : 0 < d) : dsum (d * h) (d * k) = dsum h k := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp [dsum]
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold dsum
  rw [show d * k = k * d by ring, sum_range_mul, sum_comm]
  apply sum_congr rfl
  intro t _
  have h2 : ∀ c ∈ range d, saw (((d * h * (t + k * c) : ℕ) : ℚ) / ((k * d : ℕ) : ℚ)) =
      saw (((h * t : ℕ) : ℚ) / k) := by
    intro c _
    rw [show (((d * h * (t + k * c) : ℕ) : ℚ) / ((k * d : ℕ) : ℚ)) =
      ((h * t : ℕ) : ℚ) / k + ((h * c : ℕ) : ℚ) by push_cast; field_simp, saw_add_nat]
  rw [sum_congr rfl (fun c hc => by rw [h2 c hc]), ← sum_mul]
  congr 1
  have h1 : ∀ c ∈ range d, saw (((t + k * c : ℕ) : ℚ) / ((k * d : ℕ) : ℚ)) =
      saw (((t : ℚ) / (k * d)) + (c : ℚ) / d) := by
    intro c _
    congr 1
    push_cast
    field_simp
  rw [sum_congr rfl h1, saw_mul_sum d hd]
  congr 1
  field_simp

end TuringTask
