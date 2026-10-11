import Mathlib

namespace TuringTask

theorem card_gaps_le_three (r a N : Nat) :
    let T := insert r ((Finset.range N).image (fun k => k * a % r))
    let G := ((Finset.product T T).filter (fun xy => xy.1 < xy.2 /\
        T.filter (fun z => xy.1 < z /\ z < xy.2) = {})).image (fun xy => xy.2 - xy.1)
    G.card <= 3 /\ (G.card = 3 -> exists u v : Nat, u < v /\ G = {u, v, u + v}) := by
  sorry

theorem ncard_return_times_le_three (r a b : Nat) :
    let D := {d : Nat | 0 < d /\ exists k : Nat, k * a % r < b /\ (k + d) * a % r < b /\
      forall e : Nat, 0 < e -> e < d -> b <= (k + e) * a % r}
    D.ncard <= 3 /\ (D.ncard = 3 -> exists u v : Nat, u < v /\ D = {u, v, u + v}) := by
  sorry

theorem terminal_iff (r a b c : Nat) (hr : 0 < r) (ha : Nat.Coprime a r)
    (hb : Nat.Coprime b r) (hc : Nat.Coprime c r) :
    (forall k : Nat, 1 <= k -> k < r -> r < k * a % r + k * b % r + k * c % r) <->
      (a + b) % r = 0 \/ (a + c) % r = 0 \/ (b + c) % r = 0 := by
  sorry

theorem empty_tetrahedron_iff (r : Nat) (a b : Int) (hr : 0 < r) :
    (forall x y z : Int, 0 <= z -> z <= r -> z * a <= r * x -> z * b <= r * y ->
        r * x - z * a + (r * y - z * b) + z <= r ->
        (x = 0 /\ y = 0 /\ z = 0) \/ (x = 1 /\ y = 0 /\ z = 0) \/
          (x = 0 /\ y = 1 /\ z = 0) \/ (x = a /\ y = b /\ z = r)) <->
      ((a - 1) % r = 0 /\ Int.gcd b r = 1) \/ ((b - 1) % r = 0 /\ Int.gcd a r = 1) \/
        ((a + b) % r = 0 /\ Int.gcd a r = 1) := by
  sorry

theorem pair_of_canonical (r a b c : Nat) (hs : Nat.Coprime (a + b + c) r)
    (h : forall k : Nat, 1 <= k -> k < r -> r <= k * a % r + k * b % r + k * c % r) :
    (a + b) % r = 0 \/ (a + c) % r = 0 \/ (b + c) % r = 0 := by
  sorry

end TuringTask
