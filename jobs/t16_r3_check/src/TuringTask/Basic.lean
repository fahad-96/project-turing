import Mathlib

namespace TuringTask

private def lucasInt (n : Nat) : Int :=
  2 * Int.fib (n + 1) - Int.fib n

/-- The Pell identity underlying all four square classifications. -/
private theorem lucasInt_sq_sub_five_fib_sq (n : Nat) :
    lucasInt n ^ 2 - 5 * (Nat.fib n : Int) ^ 2 = 4 * (-1 : Int) ^ n := by
  have h := Int.fib_add_sq_sub_fib_mul_fib_add_two_mul (n : Int) 1
  rw [show (n : Int) + 1 = ((n + 1 : Nat) : Int) by omega] at h
  rw [show (n : Int) + 2 * 1 = ((n + 2 : Nat) : Int) by omega] at h
  simp only [Int.fib_natCast, Int.fib_one, one_pow, Int.natAbs_natCast] at h
  have hrec : (Nat.fib (n + 2) : Int) =
      (Nat.fib n : Int) + Nat.fib (n + 1) := by
    rw [Nat.fib_add_two]
    omega
  rw [hrec] at h
  have hn : Int.fib (n + 1) = (Nat.fib (n + 1) : Int) := by
    rw [show (n : Int) + 1 = ((n + 1 : Nat) : Int) by omega,
      Int.fib_natCast]
  have h0 : Int.fib n = (Nat.fib n : Int) := Int.fib_natCast n
  unfold lucasInt
  rw [hn, h0]
  nlinarith [h]

private theorem lucasInt_nonneg (n : Nat) : 0 <= lucasInt n := by
  have hf := Nat.fib_le_fib_succ (n := n)
  have hn : Int.fib (n + 1) = (Nat.fib (n + 1) : Int) := by
    rw [show (n : Int) + 1 = ((n + 1 : Nat) : Int) by omega,
      Int.fib_natCast]
  have h0 : Int.fib n = (Nat.fib n : Int) := Int.fib_natCast n
  unfold lucasInt
  rw [hn, h0]
  have hf' : (Nat.fib n : Int) <= (Nat.fib (n + 1) : Int) := by
    exact_mod_cast hf
  nlinarith [show (0 : Int) <= Nat.fib (n + 1) by positivity]

/-- Odd-sign Ljunggren equation needed by `fib_eq_sq`. -/
private def OddLjunggren : Prop :=
  forall (x : Nat) (y : Int), 0 <= y -> y ^ 2 + 4 = 5 * (x : Int) ^ 4 ->
    x = 1

/-- Even-sign Ljunggren equation needed by `fib_eq_sq`. -/
private def EvenLjunggren : Prop :=
  forall (x : Nat) (y : Int), 0 <= y -> y ^ 2 = 5 * (x : Int) ^ 4 + 4 ->
    x = 0 \/ x = 1 \/ x = 12

private theorem fib_eq_one_index {n : Nat} (h : Nat.fib n = 1) :
    n = 1 \/ n = 2 := by
  have hpos : 0 < n := Nat.fib_pos.mp (by omega)
  have hlt : n < 3 := by
    by_contra hnot
    have hm := Nat.fib_mono (show 3 <= n by omega)
    norm_num [h] at hm
  omega

private theorem fib_eq_144_index {n : Nat} (h : Nat.fib n = 144) : n = 12 := by
  have hn : 2 <= n := by
    by_contra hnot
    have : n = 0 \/ n = 1 := by omega
    rcases this with rfl | rfl <;> norm_num at h
  apply Nat.fib_strictMonoOn.injOn hn (by norm_num : 12 ∈ Set.Ici 2)
  simpa [h] using (show Nat.fib n = Nat.fib 12 by norm_num [h])

/-- Checked reduction of the first requested result to the two missing
Pocklington/Ljunggren quartic classifications. -/
private theorem fib_eq_sq_of_ljunggren
    (hodd : OddLjunggren) (heven : EvenLjunggren)
    (n x : Nat) (h : Nat.fib n = x ^ 2) :
    n = 0 \/ n = 1 \/ n = 2 \/ n = 12 := by
  have hcast : (Nat.fib n : Int) = (x : Int) ^ 2 := by exact_mod_cast h
  rcases Nat.even_or_odd n with hn | hn
  · have hp := lucasInt_sq_sub_five_fib_sq n
    rw [hn.neg_one_pow, hcast] at hp
    have hq : lucasInt n ^ 2 = 5 * (x : Int) ^ 4 + 4 := by
      nlinarith [sq_nonneg ((x : Int) ^ 2)]
    rcases heven x (lucasInt n) (lucasInt_nonneg n) hq with hx | hx | hx
    · subst x
      norm_num at h
      exact Or.inl h
    · subst x
      rcases fib_eq_one_index h with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    · subst x
      exact Or.inr (Or.inr (Or.inr (fib_eq_144_index (by simpa using h))))
  · have hp := lucasInt_sq_sub_five_fib_sq n
    rw [hn.neg_one_pow, hcast] at hp
    have hq : lucasInt n ^ 2 + 4 = 5 * (x : Int) ^ 4 := by
      nlinarith [sq_nonneg ((x : Int) ^ 2)]
    have hx := hodd x (lucasInt n) (lucasInt_nonneg n) hq
    subst x
    rcases fib_eq_one_index h with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · have hnot : ¬ Odd 2 := by norm_num
      exact (hnot hn).elim

theorem fib_eq_sq (n x : Nat) (h : Nat.fib n = x ^ 2) :
    n = 0 \/ n = 1 \/ n = 2 \/ n = 12 := by
  sorry

theorem lucas_eq_sq (n x : Nat) (hn : 1 <= n) (h : Nat.fib (n - 1) + Nat.fib (n + 1) = x ^ 2) :
    n = 1 \/ n = 3 := by
  sorry

theorem fib_eq_two_mul_sq (n x : Nat) (h : Nat.fib n = 2 * x ^ 2) :
    n = 0 \/ n = 3 \/ n = 6 := by
  sorry

theorem lucas_eq_two_mul_sq (n x : Nat) (hn : 1 <= n)
    (h : Nat.fib (n - 1) + Nat.fib (n + 1) = 2 * x ^ 2) :
    n = 6 := by
  sorry

theorem fib_eq_two_pow (n k : Nat) (h : Nat.fib n = 2 ^ k) :
    n = 1 \/ n = 2 \/ n = 3 \/ n = 6 := by
  sorry

end TuringTask
