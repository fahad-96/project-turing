import Mathlib
import TuringTask.Main

namespace TuringTask

theorem freq_sq_unif (x : Real) (hx : Irrational x) (e : Real) (he : 0 < e) :
    exists N0 : Nat, forall N : Nat, N0 <= N -> forall a b : Real, 0 <= a -> a <= b -> b <= 1 ->
      abs ((((Finset.range N).filter (fun n : Nat =>
        a <= Int.fract ((n : Real) ^ 2 * x) /\ Int.fract ((n : Real) ^ 2 * x) < b)).card : Real)
        / N - (b - a)) < e := by
  exact uniform_freq_sq_mul x hx e he

theorem freq_poly (P : Polynomial Real) (hP : Irrational P.leadingCoeff) (hdeg : 1 <= P.natDegree)
    (a b : Real) (ha : 0 <= a) (hab : a <= b) (hb : b <= 1) :
    Filter.Tendsto (fun N : Nat => (((Finset.range N).filter (fun n : Nat =>
      a <= Int.fract (Polynomial.eval (n : Real) P) /\
        Int.fract (Polynomial.eval (n : Real) P) < b)).card : Real) / N)
      Filter.atTop (nhds (b - a)) := by
  exact tendsto_freq_eval P hP hdeg a b ha hab hb

theorem freq_lead_sq (d : Nat) (hd : 1 <= d) (hd' : d <= 9) :
    Filter.Tendsto (fun N : Nat => (((Finset.range N).filter (fun n : Nat =>
      2 ^ (n ^ 2) / 10 ^ Nat.log 10 (2 ^ (n ^ 2)) = d)).card : Real) / N)
      Filter.atTop (nhds (Real.logb 10 (((d : Real) + 1) / d))) := by
  exact tendsto_freq_lead_digit d hd hd'

theorem mean_abs_sin_sq :
    Filter.Tendsto (fun N : Nat =>
      Finset.sum (Finset.range N) (fun n : Nat => abs (Real.sin ((n : Real) ^ 2))) / N)
      Filter.atTop (nhds (2 / Real.pi)) := by
  exact tendsto_avg_abs_sin_sq

theorem mean_cos_sq (x : Real) (hx : Irrational (x / Real.pi)) :
    Filter.Tendsto (fun N : Nat =>
      Finset.sum (Finset.range N) (fun n : Nat => Real.cos ((n : Real) ^ 2 * x)) / N)
      Filter.atTop (nhds 0) := by
  exact tendsto_avg_cos_sq_mul x hx

end TuringTask
