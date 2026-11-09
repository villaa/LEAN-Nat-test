/-- The sum of an array of natural numbers. -/
def sum (a : Array Nat) : Nat :=
  a.foldl (· + ·) 0

#eval sum #[1, 2, 3, 4]   -- 10

/-- The sum of an array of natural numbers. -/
def sum (a : Array Nat) : Nat :=
  a.foldl (· + ·) 0

#eval sum #[1, 2, 3, 4]   -- 10

theorem sum_push (a : Array Nat) (x : Nat) :
    sum (a.push x) = sum a + x := by
  simp [sum]
