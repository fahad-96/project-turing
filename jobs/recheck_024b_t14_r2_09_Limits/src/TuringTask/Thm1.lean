import TuringTask.Divisors
import TuringTask.Floor

namespace TuringTask

open Finset Filter Topology Real

/-! ### Basic facts about `K = ⌊√N⌋` -/

lemma sqrt_nat_pos (N : ℕ) (hN : 1 ≤ N) : 1 ≤ Nat.sqrt N := by
  rw [Nat.le_sqrt]
  simpa using hN

lemma cast_sqrt_le (N : ℕ) : ((Nat.sqrt N : ℕ) : ℝ) ≤ Real.sqrt N := by
  rw [show ((Nat.sqrt N : ℕ) : ℝ) = Real.sqrt ((Nat.sqrt N : ℕ) ^ 2 : ℕ) by
    push_cast; rw [Real.sqrt_sq (by positivity)]]
  exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.sqrt_le' N)

lemma lt_cast_sqrt_succ (N : ℕ) : Real.sqrt N < (Nat.sqrt N : ℝ) + 1 := by
  have h : (N : ℝ) < ((Nat.sqrt N : ℝ) + 1) ^ 2 := by
    have := Nat.lt_succ_sqrt' N
    have : (N : ℝ) < ((Nat.sqrt N + 1 : ℕ) : ℝ) ^ 2 := by exact_mod_cast this
    push_cast at this
    linarith
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ N by positivity),
    Real.sqrt_nonneg (N : ℝ), show (0:ℝ) ≤ (Nat.sqrt N : ℝ) by positivity]

/-- `log N - 2 log K ≥ 0` where `K = ⌊√N⌋`. -/
lemma log_sub_two_log_nonneg (K N : ℕ) (hK : 1 ≤ K) (h1 : K * K ≤ N) :
    0 ≤ Real.log N - 2 * Real.log K := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hle : ((K : ℝ)) ^ 2 ≤ (N : ℝ) := by exact_mod_cast (by nlinarith [h1] : K ^ 2 ≤ N)
  have h := Real.log_le_log (by positivity) hle
  rw [Real.log_pow] at h
  push_cast at h
  linarith

/-- `log N - 2 log K ≤ (N - K²)/K²`. -/
lemma log_sub_two_log_le (K N : ℕ) (hK : 1 ≤ K) (h1 : K * K ≤ N) :
    Real.log N - 2 * Real.log K ≤ ((N : ℝ) - (K : ℝ) ^ 2) / (K : ℝ) ^ 2 := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hN1 : (1 : ℕ) ≤ N := le_trans (by nlinarith) h1
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have h2 : Real.log N - 2 * Real.log K = Real.log ((N : ℝ) / (K : ℝ) ^ 2) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow]
    push_cast; ring
  rw [h2]
  calc Real.log ((N : ℝ) / (K : ℝ) ^ 2) ≤ (N : ℝ) / (K : ℝ) ^ 2 - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
    _ = ((N : ℝ) - (K : ℝ) ^ 2) / (K : ℝ) ^ 2 := by field_simp

/-! ### Two elementary real inequalities -/

/-- If `K ≥ 1`, `0 ≤ r ≤ 2K` and `N = K² + r`, then `√N ≥ K + r/(2K+2)`. -/
lemma sqrt_ge_aux (K r : ℝ) (hK : 1 ≤ K) (hr0 : 0 ≤ r) (hr2 : r ≤ 2 * K) :
    (K : ℝ) + r / (2 * K + 2) ≤ Real.sqrt (K ^ 2 + r) := by
  have hKpos : (0 : ℝ) < K := by linarith
  have hd : (0 : ℝ) < 2 * K + 2 := by linarith
  have hnn : (0 : ℝ) ≤ K + r / (2 * K + 2) := by positivity
  rw [show (K : ℝ) + r / (2 * K + 2) = Real.sqrt ((K + r / (2 * K + 2)) ^ 2) from
    (Real.sqrt_sq hnn).symm]
  apply Real.sqrt_le_sqrt
  rw [← sub_nonneg]
  have hexp : (K ^ 2 + r) - (K + r / (2 * K + 2)) ^ 2
      = (r * ((2 * K + 2) ^ 2 - 2 * K * (2 * K + 2) - r)) / (2 * K + 2) ^ 2 := by
    field_simp
    ring
  rw [hexp]
  apply div_nonneg _ (by positivity)
  apply mul_nonneg hr0
  nlinarith [hK, hr2]

/-- If `K ≥ 1`, `0 ≤ r ≤ 2K` and `N = K² + r`, then `N·r/K² + 2(K-1) ≤ 4(K + r/(2K+2))`. -/
lemma main_ineq_aux (K r : ℝ) (hK : 1 ≤ K) (hr0 : 0 ≤ r) (hr2 : r ≤ 2 * K) :
    (K ^ 2 + r) * r / K ^ 2 + 2 * (K - 1) ≤ 4 * (K + r / (2 * K + 2)) := by
  have hKpos : (0 : ℝ) < K := by linarith
  have hd : (0 : ℝ) < 2 * K + 2 := by linarith
  rw [← sub_nonneg]
  have hexp : 4 * (K + r / (2 * K + 2)) - ((K ^ 2 + r) * r / K ^ 2 + 2 * (K - 1))
      = ((2 * K + 2) * (2 * K + 2) * K ^ 2 + 4 * r * K ^ 2
          - (r * K ^ 2 + r ^ 2) * (2 * K + 2)) / (K ^ 2 * (2 * K + 2)) := by
    field_simp
    ring
  rw [hexp]
  apply div_nonneg _ (by positivity)
  -- Exact decomposition with `A = 2K - r ≥ 0` and `K - 1 ≥ 0`.
  have hA : (0 : ℝ) ≤ 2 * K - r := by linarith
  have hK1 : (0 : ℝ) ≤ K - 1 := by linarith
  have hdecomp : (2 * K + 2) * (2 * K + 2) * K ^ 2 + 4 * r * K ^ 2
      - (r * K ^ 2 + r ^ 2) * (2 * K + 2)
      = 4 * (K ^ 2 * (K - 1)) + 2 * ((2 * K - r) * K ^ 2 * (K - 1))
        + 2 * ((2 * K - r) * (K + 1) * (2 * K + r)) := by ring
  rw [hdecomp]
  have t1 : (0 : ℝ) ≤ 4 * (K ^ 2 * (K - 1)) := by positivity
  have t2 : (0 : ℝ) ≤ 2 * ((2 * K - r) * K ^ 2 * (K - 1)) := by positivity
  have t3 : (0 : ℝ) ≤ 2 * ((2 * K - r) * (K + 1) * (2 * K + r)) := by positivity
  linarith

/-! ### The main estimate -/

/-- Real-valued form of the Dirichlet hyperbola identity. -/
lemma dirichlet_real (N : ℕ) :
    (∑ n ∈ Icc 1 N, (n.divisors.card : ℝ))
      = 2 * (∑ a ∈ Icc 1 (Nat.sqrt N), ((N / a : ℕ) : ℝ)) - ((Nat.sqrt N : ℝ)) ^ 2 := by
  have h := dirichlet_hyperbola N
  have h' : ((∑ n ∈ Icc 1 N, n.divisors.card : ℕ) : ℝ) + (Nat.sqrt N : ℝ) * (Nat.sqrt N : ℝ)
      = 2 * ((∑ a ∈ Icc 1 (Nat.sqrt N), (N / a : ℕ) : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  rw [sq]
  linarith

/-- The key bound: `|D(N) - N log N - (2γ-1)N| ≤ 4√N` for `N ≥ 1`. -/
theorem main_estimate (N : ℕ) (hN : 1 ≤ N) :
    |(∑ n ∈ Icc 1 N, (n.divisors.card : ℝ)) - (N : ℝ) * Real.log N -
      (2 * eulerMascheroniConstant - 1) * N| ≤ 4 * Real.sqrt N := by
  set K := Nat.sqrt N with hKdef
  have hK1 : 1 ≤ K := sqrt_nat_pos N hN
  have hKK : K * K ≤ N := Nat.sqrt_le N
  have hKN : N < (K + 1) * (K + 1) := Nat.lt_succ_sqrt N
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK1
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hsN : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr hNR
  have hKle : (K : ℝ) ≤ Real.sqrt N := cast_sqrt_le N
  have hslt : Real.sqrt N < (K : ℝ) + 1 := lt_cast_sqrt_succ N
  have hsq : Real.sqrt N ^ 2 = (N : ℝ) := Real.sq_sqrt hNR.le
  -- the floor sum
  obtain ⟨E, hE0, hE1, hEeq⟩ := sum_natDiv_eq N K hK1
  -- the harmonic estimate
  set θ := H K - Real.log K - eulerMascheroniConstant with hθdef
  have hθ0 : 0 < θ := H_error_pos K hK1
  have hθ1 : θ ≤ 1 / K := H_error_le K hK1
  have hHK : H K = Real.log K + eulerMascheroniConstant + θ := by rw [hθdef]; ring
  -- the logarithm comparison
  set L := Real.log N - 2 * Real.log K with hLdef
  have hL0 : 0 ≤ L := log_sub_two_log_nonneg K N hK1 hKK
  have hL1 : L ≤ ((N : ℝ) - (K : ℝ) ^ 2) / (K : ℝ) ^ 2 := log_sub_two_log_le K N hK1 hKK
  -- assemble
  have hmain : (∑ n ∈ Icc 1 N, (n.divisors.card : ℝ)) - (N : ℝ) * Real.log N -
      (2 * eulerMascheroniConstant - 1) * N
      = 2 * (N : ℝ) * θ - (N : ℝ) * L - 2 * E + ((N : ℝ) - (K : ℝ) ^ 2) := by
    rw [dirichlet_real N, hEeq, hHK, hLdef]
    ring
  rw [hmain, abs_le]
  -- set up the integer remainder `r = N - K²`
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = (N : ℝ) - (K : ℝ) ^ 2 := ⟨_, rfl⟩
  have hKsq : ((K : ℝ)) ^ 2 ≤ (N : ℝ) := by
    exact_mod_cast (by nlinarith [hKK] : K ^ 2 ≤ N)
  have hr0 : (0 : ℝ) ≤ r := by rw [hrdef]; linarith
  have hr2 : r ≤ 2 * (K : ℝ) := by
    -- integrality: `N < (K+1)² = K² + 2K + 1` in `ℕ` gives `N ≤ K² + 2K`
    have hNat : N ≤ K * K + 2 * K := by nlinarith [hKN]
    have hcast : (N : ℝ) ≤ (K : ℝ) * (K : ℝ) + 2 * (K : ℝ) := by exact_mod_cast hNat
    rw [hrdef]; nlinarith [hcast]
  have hKR1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK1
  have hNKr : (N : ℝ) = (K : ℝ) ^ 2 + r := by rw [hrdef]; ring
  -- `√N ≥ K + r/(2K+2)`
  have hsqrtge : (K : ℝ) + r / (2 * (K : ℝ) + 2) ≤ Real.sqrt N := by
    rw [hNKr]
    exact sqrt_ge_aux (K : ℝ) r hKR1 hr0 hr2
  constructor
  · -- lower bound
    have hNL : (N : ℝ) * L ≤ (N : ℝ) * (r / (K : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (by rw [hrdef]; exact hL1) hNR.le
    have hkey : (N : ℝ) * (r / (K : ℝ) ^ 2) + 2 * ((K : ℝ) - 1) ≤ 4 * Real.sqrt N := by
      have hbase := main_ineq_aux (K : ℝ) r hKR1 hr0 hr2
      have hrw : ((K : ℝ) ^ 2 + r) * r / (K : ℝ) ^ 2 = (N : ℝ) * (r / (K : ℝ) ^ 2) := by
        rw [← hNKr]; ring
      rw [hrw] at hbase
      linarith [hsqrtge, hbase]
    have hθpos : 0 < 2 * (N : ℝ) * θ := by positivity
    rw [hrdef] at hkey hNL
    linarith [hθpos, hE1, hNL, hkey]
  · -- upper bound
    have hθN : 2 * (N : ℝ) * θ ≤ 2 * (N : ℝ) / K := by
      calc 2 * (N : ℝ) * θ ≤ 2 * (N : ℝ) * (1 / (K : ℝ)) :=
            mul_le_mul_of_nonneg_left hθ1 (by positivity)
        _ = 2 * (N : ℝ) / K := by ring
    -- `N·L ≥ r`, via `log(N/K²) ≥ 1 - K²/N`
    have hLbig : r / (N : ℝ) ≤ L := by
      have hlog : Real.log ((K : ℝ) ^ 2 / (N : ℝ)) ≤ (K : ℝ) ^ 2 / (N : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have heq : Real.log ((K : ℝ) ^ 2 / (N : ℝ)) = 2 * Real.log K - Real.log N := by
        rw [Real.log_div (by positivity) (by positivity), Real.log_pow]
        push_cast; ring
      rw [heq] at hlog
      have heq2 : (K : ℝ) ^ 2 / (N : ℝ) - 1 = -(r / (N : ℝ)) := by
        rw [hrdef]
        field_simp
        ring
      rw [heq2] at hlog
      rw [hLdef]
      linarith
    have hNLge : r ≤ (N : ℝ) * L := by
      calc r = (N : ℝ) * (r / (N : ℝ)) := by field_simp
        _ ≤ (N : ℝ) * L := mul_le_mul_of_nonneg_left hLbig hNR.le
    -- `2N/K ≤ 4√N`: since `K ≤ √N` and `N = (√N)²`, this is `√N ≤ 2K`
    have hkey : 2 * (N : ℝ) / (K : ℝ) ≤ 4 * Real.sqrt N := by
      rw [div_le_iff₀ hKR]
      have hsK : Real.sqrt N ≤ 2 * (K : ℝ) := by linarith [hslt, hKR1]
      have hmm : Real.sqrt N * Real.sqrt N = (N : ℝ) := Real.mul_self_sqrt hNR.le
      nlinarith [hsN, hsK, hmm]
    rw [hrdef] at hNLge
    linarith [hE0, hθN, hkey, hNLge]

end TuringTask
