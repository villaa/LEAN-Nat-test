theorem succ_in_nat (n : Nat) : ∃ m : Nat, m = Nat.succ n := by
  refine ⟨n + 1, ?_⟩
  rfl

theorem my_succ_add (n m : Nat) : Nat.succ n + m = Nat.succ (n + m) := by
  induction m with
   | zero => rw[Nat.add_zero (Nat.succ n), Nat.add_zero n]
   | succ k ih =>
     rw[Nat.add_succ (Nat.succ n) k, Nat.add_succ n k]
     rw[ih]



theorem zero_add_explicit (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rw [Nat.add_zero]          -- 0 + 0 = 0
  | succ k ih =>                       -- ih : 0 + k = k
    rw [Nat.add_succ]                  -- goal becomes succ (0 + k) = k + 1
    rw [ih]                            -- goal becomes succ k = k + 1, true by definition
