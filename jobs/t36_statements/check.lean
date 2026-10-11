import TuringTask.Basic

open TuringTask

example (s : Nat -> Nat) (h1 : s 1 = 1)
    (he : forall n, s (2 * n) = s n) (ho : forall n, s (2 * n + 1) = s n + s (n + 1)) :
    (forall n, 0 < n -> Nat.Coprime (s n) (s (n + 1))) /\
      forall a b, 0 < a -> 0 < b -> Nat.Coprime a b ->
        ExistsUnique (fun n => 0 < n /\ s n = a /\ s (n + 1) = b) :=
  TuringTask.coprime_and_existsUnique_eq s h1 he ho

example (s : Nat -> Nat) (h1 : s 1 = 1)
    (he : forall n, s (2 * n) = s n) (ho : forall n, s (2 * n + 1) = s n + s (n + 1))
    (k n : Nat) (hn : n <= 2 ^ (k + 1)) :
    s n <= Nat.fib (k + 2) /\
      (s n = Nat.fib (k + 2) <->
        (3 * n : Int) = 4 * 2 ^ k - (-1) ^ k \/ (3 * n : Int) = 5 * 2 ^ k + (-1) ^ k) :=
  TuringTask.le_fib_and_eq_fib_iff s h1 he ho k n hn

example (s : Nat -> Nat) (h1 : s 1 = 1)
    (he : forall n, s (2 * n) = s n) (ho : forall n, s (2 * n + 1) = s n + s (n + 1))
    (t k : Nat) (htk : t <= k + 1) :
    (Finset.filter (fun n => s n = t) (Finset.Ico (2 ^ k) (2 ^ (k + 1)))).card =
      Nat.totient t :=
  TuringTask.card_filter_eq_totient s h1 he ho t k htk

example (s : Nat -> Nat) (h1 : s 1 = 1)
    (he : forall n, s (2 * n) = s n) (ho : forall n, s (2 * n + 1) = s n + s (n + 1))
    (n : Nat) :
    s (n + 1) =
      (Finset.filter
        (fun c : Fin (n + 1) -> Fin 3 =>
          Finset.sum Finset.univ (fun i => (c i : Nat) * 2 ^ (i : Nat)) = n)
        Finset.univ).card :=
  TuringTask.eq_card_hyperbinary s h1 he ho n

example (s : Nat -> Nat)
    (he : forall n, s (2 * n) = s n) (ho : forall n, s (2 * n + 1) = s n + s (n + 1))
    (n : Nat) (hn : n % 2 = 1) :
    s (Nat.ofDigits 2 (Nat.digits 2 n).reverse) = s n :=
  TuringTask.eq_of_reverse_digits s he ho n hn

#print axioms TuringTask.coprime_and_existsUnique_eq
#print axioms TuringTask.le_fib_and_eq_fib_iff
#print axioms TuringTask.card_filter_eq_totient
#print axioms TuringTask.eq_card_hyperbinary
#print axioms TuringTask.eq_of_reverse_digits
