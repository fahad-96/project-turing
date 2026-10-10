import Mathlib

namespace TuringTask

noncomputable def ex (x : Real) : Complex :=
  Complex.exp (2 * (Real.pi : Complex) * Complex.I * (x : Complex))

noncomputable def rt (n : Nat) : Complex :=
  if n % 4 = 1 then ((Real.sqrt (n : Real) : Real) : Complex)
  else Complex.I * ((Real.sqrt (n : Real) : Real) : Complex)

theorem sum_sq (n : Nat) (hn : n % 2 = 1) :
    Finset.sum (Finset.range n) (fun k : Nat => ex ((k : Real) ^ 2 / (n : Real))) = rt n := by
  sorry

theorem sum_tri (n : Nat) (hn : n % 2 = 1) :
    Finset.sum (Finset.range n) (fun k : Nat =>
        ex ((k : Real) * ((k : Real) + 1) / (2 * (n : Real)))) =
      ex (((n : Real) - 1) / (8 * (n : Real))) * ((Real.sqrt (n : Real) : Real) : Complex) := by
  sorry

theorem sum_legendre (p : Nat) [Fact p.Prime] (hp : p % 2 = 1) (a : Int) :
    Finset.sum (Finset.range p) (fun k : Nat =>
        ((legendreSym p (k : Int) : Int) : Complex) *
          ex ((a : Real) * (k : Real) / (p : Real))) =
      ((legendreSym p a : Int) : Complex) * rt p := by
  sorry

theorem sum_sq_mul (p q : Nat) [Fact p.Prime] [Fact q.Prime]
    (hp : p % 2 = 1) (hq : q % 2 = 1) (hpq : Not (p = q)) :
    Finset.sum (Finset.range p) (fun j : Nat =>
        ex ((q : Real) * (j : Real) ^ 2 / (p : Real))) *
      Finset.sum (Finset.range q) (fun k : Nat =>
        ex ((p : Real) * (k : Real) ^ 2 / (q : Real))) = rt (p * q) := by
  sorry

theorem sum_cot (p : Nat) [Fact p.Prime] (hp : p % 4 = 3) :
    Real.sqrt (p : Real) * Finset.sum (Finset.range p) (fun k : Nat =>
        ((legendreSym p (k : Int) : Int) : Real) *
          Real.cot (Real.pi * (k : Real) / (p : Real))) =
      -2 * Finset.sum (Finset.range p) (fun k : Nat =>
        (k : Real) * ((legendreSym p (k : Int) : Int) : Real)) := by
  sorry

end TuringTask
