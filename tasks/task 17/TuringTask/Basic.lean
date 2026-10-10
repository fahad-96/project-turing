import Mathlib

namespace TuringTask

theorem card_squarefree_sub_le (N : Nat) (hN : 1 <= N) :
    abs ((((Finset.Icc 1 N).filter (fun n : Nat => Squarefree n)).card : Real) -
        6 / Real.pi ^ 2 * N) <= 3 * Real.sqrt N := by
  sorry

theorem card_coprime_sub_le (N : Nat) (hN : 1 <= N) :
    abs ((((Finset.product (Finset.Icc 1 N) (Finset.Icc 1 N)).filter
        (fun p : Prod Nat Nat => Nat.Coprime p.1 p.2)).card : Real) - 6 / Real.pi ^ 2 * N ^ 2) <=
      6 * N * (Real.log N + 1) := by
  sorry

theorem sum_totient_sub_le (N : Nat) (hN : 1 <= N) :
    abs ((Finset.Icc 1 N).sum (fun n => (Nat.totient n : Real)) - 3 / Real.pi ^ 2 * N ^ 2) <=
      4 * N * (Real.log N + 1) := by
  sorry

theorem sum_totient_div_sub_le (N : Nat) (hN : 1 <= N) :
    abs ((Finset.Icc 1 N).sum (fun n => (Nat.totient n : Real) / n) - 6 / Real.pi ^ 2 * N) <=
      Real.log N + 2 := by
  sorry

theorem tendsto_card_squarefree_div :
    Filter.Tendsto (fun N : Nat => (((Finset.Icc 1 N).filter (fun n : Nat => Squarefree n)).card :
        Real) / N) Filter.atTop (nhds (6 / Real.pi ^ 2)) := by
  sorry

end TuringTask
