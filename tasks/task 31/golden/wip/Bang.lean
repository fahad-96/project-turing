import TuringTask.Kaplan

/-!
# Bang's bound `|a_{pqr}(k)| ≤ p - 1`

In Kaplan's residue form `a_k = ∑_{m < p} D_m` with `D_m = B(f(m)) - B(f(m + q))`.
* `f(m)` and `f(m + q)` agree modulo `q`, so they have the same coordinate `alp`; the closed form
  of the binary coefficients then gives `|D_m| ≤ 1`.
* As `m` runs over `[0, p)`, `bet (f m)` and `bet (f (m + q))` both run over all of `[0, p)`.
  Hence the uncut differences `b(f m) - b(f(m + q))` sum to `0`.
* If every `D_m = 1`, each uncut difference is `≥ 0`, so all of them vanish. The index `m` with
  `bet (f m) = v - 1` then gives two points `f m < f(m + q)` of the positive region with the same
  `alp`, which forces `v - 1 < bet (f (m + q)) < v`. The case `D_m = -1` for all `m` is symmetric.
-/

namespace TuringTask

open Polynomial Finset

section

variable {p q u v : ℕ} (hp : p.Prime) (hq : q.Prime) (hu : u * p % q = 1) (hv : v * q % p = 1)
  (huq : u < q) (hvp : v < p)

include hp hq in
lemma nezero_pq : NeZero (p * q) := ⟨by have := hp.two_le; have := hq.two_le; positivity⟩

include hp hq in
lemma alp_fc (c k m : ℕ) :
    alp q u (fc (p * q) c k m) = ((c : ZMod q) * ((k : ZMod q) - m) * u).val := by
  haveI := nezero_pq hp hq
  have h : q ∣ p * q := dvd_mul_left q p
  unfold alp fc
  rw [← ZMod.val_natCast, Nat.cast_mul, ZMod.natCast_val, ZMod.cast_mul h, ZMod.cast_sub h,
    ZMod.cast_natCast h, ZMod.cast_natCast h, ZMod.cast_natCast h]

include hp hq in
lemma bet_fc (c k m : ℕ) :
    bet p v (fc (p * q) c k m) = ((c : ZMod p) * ((k : ZMod p) - m) * v).val := by
  haveI := nezero_pq hp hq
  have h : p ∣ p * q := dvd_mul_right p q
  unfold bet fc
  rw [← ZMod.val_natCast, Nat.cast_mul, ZMod.natCast_val, ZMod.cast_mul h, ZMod.cast_sub h,
    ZMod.cast_natCast h, ZMod.cast_natCast h, ZMod.cast_natCast h]

include hp hq in
lemma alp_fc_add (c k m : ℕ) : alp q u (fc (p * q) c k (m + q)) = alp q u (fc (p * q) c k m) := by
  rw [alp_fc hp hq, alp_fc hp hq, Nat.cast_add, ZMod.natCast_self, add_zero]

include hp hq in
lemma bet_fc_add (c k m : ℕ) : bet p v (fc (p * q) c k (m + p)) = bet p v (fc (p * q) c k m) := by
  rw [bet_fc hp hq, bet_fc hp hq, Nat.cast_add, ZMod.natCast_self, add_zero]

include hp hq in
lemma fc_lt (c k m : ℕ) : fc (p * q) c k m < p * q := by
  haveI := nezero_pq hp hq
  exact ZMod.val_lt _

lemma cast_inv_p {c w : ℕ} (hc : (c : ZMod (p * q)) * w = 1) : (c : ZMod p) * w = 1 := by
  have := congrArg (ZMod.castHom (dvd_mul_right p q) (ZMod p)) hc
  simpa using this

include hp hq hv in
lemma bet_fc_inj {c w : ℕ} (hc : (c : ZMod (p * q)) * w = 1) (k x : ℕ) :
    Set.InjOn (fun m => bet p v (fc (p * q) c k (m + x))) (range p) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  intro m hm m' hm' h
  simp only [coe_range, Set.mem_Iio] at hm hm'
  simp only [bet_fc hp hq] at h
  have hcp := cast_inv_p (p := p) hc
  have hvq : (v : ZMod p) * q = 1 := by
    rw [← Nat.cast_mul, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff', hv,
      Nat.mod_eq_of_lt hp.one_lt]
  have h2 := congrArg (fun z : ZMod p => z * w * q) (ZMod.val_injective p h)
  have h3 : ((m + x : ℕ) : ZMod p) = ((m' + x : ℕ) : ZMod p) := by
    have e : ∀ y : ZMod p, (c : ZMod p) * y * v * w * q = y := by
      intro y
      calc (c : ZMod p) * y * v * w * q = ((c : ZMod p) * w) * (v * q) * y := by ring
        _ = y := by rw [hcp, hvq, one_mul, one_mul]
    rw [e, e] at h2
    exact sub_right_injective h2
  push_cast at h3
  have h4 := add_right_cancel h3
  rwa [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hm'] at h4

include hp hq hv in
lemma image_bet_fc {c w : ℕ} (hc : (c : ZMod (p * q)) * w = 1) (k x : ℕ) :
    (range p).image (fun m => bet p v (fc (p * q) c k (m + x))) = range p := by
  apply eq_of_subset_of_card_le
  · intro τ hτ
    obtain ⟨m, -, rfl⟩ := mem_image.1 hτ
    exact mem_range.2 (Nat.mod_lt _ hp.pos)
  · rw [card_image_of_injOn (bet_fc_inj hp hq hv hc k x)]

include hp hq hv in
lemma sum_bet_fc {c w : ℕ} (hc : (c : ZMod (p * q)) * w = 1) (k x : ℕ) (F : ℕ → ℤ) :
    ∑ m ∈ range p, F (bet p v (fc (p * q) c k (m + x))) = ∑ τ ∈ range p, F τ := by
  conv_rhs => rw [← image_bet_fc hp hq hv hc k x]
  rw [sum_image (bet_fc_inj hp hq hv hc k x)]

include hp hq hv in
lemma exists_bet_fc {c w : ℕ} (hc : (c : ZMod (p * q)) * w = 1) (k x : ℕ) {τ : ℕ} (hτ : τ < p) :
    ∃ m < p, bet p v (fc (p * q) c k (m + x)) = τ := by
  rw [← mem_range, ← image_bet_fc hp hq hv hc k x] at hτ
  obtain ⟨m, hm, h⟩ := mem_image.1 hτ
  exact ⟨m, mem_range.1 hm, h⟩

/-- The indicator `[alp i < u]`. -/
def cA (q u i : ℕ) : ℤ := if alp q u i < u then 1 else 0

/-- The indicator `[bet i < v]`. -/
def cB (p v i : ℕ) : ℤ := if bet p v i < v then 1 else 0

include hp hq hu hv huq hvp in
lemma coeff_fc (c k m : ℕ) : (cyclotomic (p * q) ℤ).coeff (fc (p * q) c k m) =
    cA q u (fc (p * q) c k m) + cB p v (fc (p * q) c k m) - 1 :=
  coeff_binary_closed hp hq hu hv huq hvp (fc_lt hp hq c k m)

include hp hq hv in
lemma cB_sum_eq {c w : ℕ} (hc : (c : ZMod (p * q)) * w = 1) (k : ℕ) :
    ∑ m ∈ range p, cB p v (fc (p * q) c k m) = ∑ m ∈ range p, cB p v (fc (p * q) c k (m + q)) := by
  unfold cB
  have h := sum_bet_fc hp hq hv hc k 0 (fun τ => if τ < v then 1 else 0)
  simp only [add_zero] at h
  rw [h, sum_bet_fc hp hq hv hc k q (fun τ => if τ < v then 1 else 0)]

include hp hq hu hv huq hvp in
/-- The uncut differences sum to zero. -/
lemma uncut_sum {c w : ℕ} (hc : (c : ZMod (p * q)) * w = 1) (k : ℕ) :
    ∑ m ∈ range p, ((cyclotomic (p * q) ℤ).coeff (fc (p * q) c k m) -
      (cyclotomic (p * q) ℤ).coeff (fc (p * q) c k (m + q))) = 0 := by
  have h : ∀ m, (cyclotomic (p * q) ℤ).coeff (fc (p * q) c k m) -
      (cyclotomic (p * q) ℤ).coeff (fc (p * q) c k (m + q)) =
      cB p v (fc (p * q) c k m) - cB p v (fc (p * q) c k (m + q)) := by
    intro m
    rw [coeff_fc hp hq hu hv huq hvp, coeff_fc hp hq hu hv huq hvp]
    unfold cA; rw [alp_fc_add hp hq]; ring
  rw [sum_congr rfl fun m _ => h m, sum_sub_distrib, sub_eq_zero, cB_sum_eq hp hq hv hc k]

lemma cA_cases (q u i : ℕ) : cA q u i = 0 ∨ cA q u i = 1 := by unfold cA; split_ifs <;> simp

lemma cB_cases (p v i : ℕ) : cB p v i = 0 ∨ cB p v i = 1 := by unfold cB; split_ifs <;> simp

/-- If terms are at most `1` and their sum is at least the number of terms, all equal `1`. -/
lemma all_one {s : Finset ℕ} {f : ℕ → ℤ} (hle : ∀ m ∈ s, f m ≤ 1)
    (hs : (s.card : ℤ) ≤ ∑ m ∈ s, f m) : ∀ m ∈ s, f m = 1 := by
  have hnn : ∀ m ∈ s, 0 ≤ 1 - f m := fun m hm => by linarith [hle m hm]
  have h0 : ∑ m ∈ s, (1 - f m) = 0 := by
    refine le_antisymm ?_ (sum_nonneg hnn)
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one]
    linarith
  intro m hm
  have := (sum_eq_zero_iff_of_nonneg hnn).1 h0 m hm
  linarith

/-- The term `D_m` written with the indicators. -/
noncomputable def Dm (p q u v r c k m : ℕ) : ℤ :=
  (if r * fc (p * q) c k m ≤ k then
      cA q u (fc (p * q) c k m) + cB p v (fc (p * q) c k m) - 1 else 0) -
    (if r * fc (p * q) c k (m + q) ≤ k then
      cA q u (fc (p * q) c k m) + cB p v (fc (p * q) c k (m + q)) - 1 else 0)

include hp hq hu hv huq hvp in
lemma Gk_sub (r c k m : ℕ) : Gk p q r k (fc (p * q) c k m) - Gk p q r k (fc (p * q) c k (m + q)) =
    Dm p q u v r c k m := by
  unfold Gk Dm
  rw [coeff_fc hp hq hu hv huq hvp, coeff_fc hp hq hu hv huq hvp]
  unfold cA; rw [alp_fc_add hp hq]

lemma Dm_le (p q u v r c k m : ℕ) : Dm p q u v r c k m ≤ 1 ∧ -1 ≤ Dm p q u v r c k m := by
  unfold Dm
  rcases cA_cases q u (fc (p * q) c k m) with h1 | h1 <;>
    rcases cB_cases p v (fc (p * q) c k m) with h2 | h2 <;>
    rcases cB_cases p v (fc (p * q) c k (m + q)) with h3 | h3 <;>
    rw [h1, h2, h3] <;> split_ifs <;> norm_num

variable {r : ℕ} (hr : r.Prime) (hrp : r ≠ p) (hrq : r ≠ q)

include hp hq hu hv huq hvp hr hrp hrq in
/-- Bang's bound for distinct primes. -/
theorem bang {c : ℕ} (hc : (c : ZMod (p * q)) * r = 1) (k : ℕ) :
    |(cyclotomic (p * q * r) ℤ).coeff k| ≤ (p : ℤ) - 1 := by
  rw [kaplan_res hp hq hu hr hrp hrq hc,
    sum_congr rfl fun m _ => Gk_sub hp hq hu hv huq hvp r c k m]
  have hv0 : 1 ≤ v := by
    rcases Nat.eq_zero_or_pos v with rfl | h
    · simp at hv
    · exact h
  have hmono : ∀ x y, r * x ≤ k → ¬ r * y ≤ k → x < y := by
    intro x y h1 h2
    by_contra h3
    exact h2 (le_trans (Nat.mul_le_mul_left r (not_lt.1 h3)) h1)
  have hsum := cB_sum_eq hp hq hv hc k
  have hlt := fun m => fc_lt hp hq c k m
  rw [abs_le]
  constructor
  · by_contra hneg
    push Not at hneg
    have hall := all_one (s := range p) (f := fun m => -Dm p q u v r c k m)
      (fun m _ => by linarith [(Dm_le p q u v r c k m).2])
      (by rw [sum_neg_distrib, card_range]; linarith)
    have hle : ∀ m ∈ range p,
        0 ≤ cB p v (fc (p * q) c k (m + q)) - cB p v (fc (p * q) c k m) := by
      intro m hm
      have h := hall m hm
      simp only [Dm] at h
      rcases cA_cases q u (fc (p * q) c k m) with h1 | h1 <;>
        rcases cB_cases p v (fc (p * q) c k m) with h2 | h2 <;>
        rcases cB_cases p v (fc (p * q) c k (m + q)) with h3 | h3 <;>
        simp only [h1, h2, h3] at h ⊢ <;> split_ifs at h <;> omega
    have heq := (sum_eq_zero_iff_of_nonneg hle).1 (by rw [sum_sub_distrib, hsum, sub_self])
    obtain ⟨m, hm, hb⟩ := exists_bet_fc hp hq hv hc k q hvp
    have hY : cB p v (fc (p * q) c k (m + q)) = 0 := by unfold cB; rw [if_neg (by omega)]
    have hX : cB p v (fc (p * q) c k m) = 0 := by
      have := heq m (mem_range.2 hm); rw [hY] at this; linarith
    have hbX : v ≤ bet p v (fc (p * q) c k m) := by
      unfold cB at hX; split_ifs at hX with h; · simp at hX
      · omega
    have h := hall m (mem_range.2 hm)
    simp only [Dm, hX, hY] at h
    rcases cA_cases q u (fc (p * q) c k m) with hA | hA <;> rw [hA] at h
    · split_ifs at h with h1 h2 <;> try omega
      have ha : u ≤ alp q u (fc (p * q) c k m) := by
        unfold cA at hA; split_ifs at hA with h; · simp at hA
        · omega
      have ha' : u ≤ alp q u (fc (p * q) c k (m + q)) := by rw [alp_fc_add hp hq]; exact ha
      have e1 := E_eq_of_neg hp hq hu hv huq hvp (hlt m) ha hbX
      have e2 := E_eq_of_neg hp hq hu hv huq hvp (hlt (m + q)) ha' (le_of_eq hb.symm)
      rw [alp_fc_add hp hq, hb] at e2
      have h5 := hmono _ _ h1 h2
      have h6 : bet p v (fc (p * q) c k m) * q < v * q := by omega
      have := Nat.lt_of_mul_lt_mul_right h6
      omega
    · split_ifs at h <;> omega
  · by_contra hpos
    push Not at hpos
    have hall := all_one (s := range p) (f := fun m => Dm p q u v r c k m)
      (fun m _ => (Dm_le p q u v r c k m).1) (by rw [card_range]; linarith)
    have hle : ∀ m ∈ range p,
        0 ≤ cB p v (fc (p * q) c k m) - cB p v (fc (p * q) c k (m + q)) := by
      intro m hm
      have h := hall m hm
      simp only [Dm] at h
      rcases cA_cases q u (fc (p * q) c k m) with h1 | h1 <;>
        rcases cB_cases p v (fc (p * q) c k m) with h2 | h2 <;>
        rcases cB_cases p v (fc (p * q) c k (m + q)) with h3 | h3 <;>
        simp only [h1, h2, h3] at h ⊢ <;> split_ifs at h <;> omega
    have heq := (sum_eq_zero_iff_of_nonneg hle).1 (by rw [sum_sub_distrib, hsum, sub_self])
    obtain ⟨m, hm, hb⟩ := exists_bet_fc hp hq hv hc k 0 (show v - 1 < p by omega)
    rw [add_zero] at hb
    have hX : cB p v (fc (p * q) c k m) = 1 := by unfold cB; rw [if_pos (by omega)]
    have hY : cB p v (fc (p * q) c k (m + q)) = 1 := by
      have := heq m (mem_range.2 hm); rw [hX] at this; linarith
    have hbY : bet p v (fc (p * q) c k (m + q)) < v := by
      unfold cB at hY; split_ifs at hY with h; · exact h
      · simp at hY
    have h := hall m (mem_range.2 hm)
    simp only [Dm, hX, hY] at h
    rcases cA_cases q u (fc (p * q) c k m) with hA | hA <;> rw [hA] at h
    · split_ifs at h <;> omega
    · split_ifs at h with h1 h2 <;> try omega
      have ha : alp q u (fc (p * q) c k m) < u := by
        unfold cA at hA; split_ifs at hA with h; · exact h
        · simp at hA
      have ha' : alp q u (fc (p * q) c k (m + q)) < u := by rw [alp_fc_add hp hq]; exact ha
      have e1 := E_eq_of_pos hp hq hu hv huq hvp (hlt m) ha (by omega)
      have e2 := E_eq_of_pos hp hq hu hv huq hvp (hlt (m + q)) ha' hbY
      rw [alp_fc_add hp hq] at e2
      rw [hb] at e1
      have h5 := hmono _ _ h1 h2
      have h6 : (v - 1) * q < bet p v (fc (p * q) c k (m + q)) * q := by omega
      have := Nat.lt_of_mul_lt_mul_right h6
      omega

end

end TuringTask
