import Mathlib

namespace TuringTask

theorem exists_iff_not_exists_sub (a b n : Nat) (ha : 2 <= a) (hb : 2 <= b) (hab : Nat.Coprime a b)
    (hn : n <= a * b - a - b) :
    (exists x y : Nat, n = a * x + b * y) <->
      Not (exists x y : Nat, a * b - a - b - n = a * x + b * y) := by
  sorry

theorem frobenius_mul_mul (a b c d G : Nat) (hdc : Nat.Coprime d c)
    (hG : Not (exists x y z : Nat, G = a * x + b * y + c * z))
    (hG' : forall n, G < n -> exists x y z : Nat, n = a * x + b * y + c * z) :
    Not (exists x y z : Nat, d * G + (d - 1) * c = d * a * x + d * b * y + c * z) /\
      forall n, d * G + (d - 1) * c < n ->
        exists x y z : Nat, n = d * a * x + d * b * y + c * z := by
  sorry

theorem frobenius_arith_seq (a d s : Nat) (ha : 2 <= a) (hs : 1 <= s) (had : Nat.Coprime a d) :
    Not (exists x : Fin (s + 1) -> Nat,
        ((a - 2) / s + 1) * a + (d - 1) * (a - 1) - 1 =
          Finset.sum Finset.univ (fun i => x i * (a + i * d))) /\
      forall n, ((a - 2) / s + 1) * a + (d - 1) * (a - 1) - 1 < n ->
        exists x : Fin (s + 1) -> Nat, n = Finset.sum Finset.univ (fun i => x i * (a + i * d)) := by
  sorry

theorem ncard_not_arith_seq (a d s : Nat) (hs : 1 <= s) (had : Nat.Coprime a d) :
    Set.ncard {n : Nat | Not (exists x : Fin (s + 1) -> Nat,
        n = Finset.sum Finset.univ (fun i => x i * (a + i * d)))} =
      Finset.sum (Finset.range a) (fun m => (m + s - 1) / s) + (d - 1) * (a - 1) / 2 := by
  sorry

theorem symmetric_iff (a b c g : Nat)
    (ha : Not (exists x y : Nat, a = b * x + c * y))
    (hb : Not (exists x y : Nat, b = a * x + c * y))
    (hc : Not (exists x y : Nat, c = a * x + b * y))
    (hg : Not (exists x y z : Nat, g = a * x + b * y + c * z))
    (hg' : forall n, g < n -> exists x y z : Nat, n = a * x + b * y + c * z) :
    (forall n, n <= g ->
      ((exists x y z : Nat, n = a * x + b * y + c * z) <->
        Not (exists x y z : Nat, g - n = a * x + b * y + c * z))) <->
      (1 < Nat.gcd a b /\
          exists x y : Nat, c = a / Nat.gcd a b * x + b / Nat.gcd a b * y) \/
        (1 < Nat.gcd a c /\
          exists x y : Nat, b = a / Nat.gcd a c * x + c / Nat.gcd a c * y) \/
        (1 < Nat.gcd b c /\
          exists x y : Nat, a = b / Nat.gcd b c * x + c / Nat.gcd b c * y) := by
  sorry

end TuringTask
