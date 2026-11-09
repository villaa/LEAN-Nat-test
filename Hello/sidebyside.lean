/-
  Informal proof vs. fully explicit Lean proof, side by side.
  Works in a plain Lean 4 project (no Mathlib needed).

  The only facts about addition we are allowed to use are its two
  defining equations (these play the role of the Peano axioms for +):

    Nat.add_zero : n + 0 = n                    -- "adding zero does nothing"
    Nat.add_succ : n + succ m = succ (n + m)    -- "adding one more"

  Note: these are about the RIGHT argument. That is why `n + 0 = n`
  is free, but `0 + n = n` needs a proof by induction.
-/

namespace Demo

/-
=====================================================================
  Example 1.  Theorem: for every natural number n, 0 + n = n.
=====================================================================

  INFORMAL (undergrad) PROOF.
    Induction on n.
    Base case: 0 + 0 = 0 by definition of addition.
    Inductive step: assume 0 + n = n. Then
        0 + (n+1) = (0 + n) + 1   (definition of addition)
                  = n + 1         (inductive hypothesis).  ∎
-/

-- (A) Fully explicit tactic proof: every step names the rule it uses.
theorem zero_add_explicit (n : Nat) : 0 + n = n := by
  induction n with
  | zero =>
    -- Goal: 0 + 0 = 0
    rw [Nat.add_zero]              -- axiom: x + 0 = x   (goal becomes 0 = 0, closed by rfl)
  | succ k ih =>
    -- ih   : 0 + k = k
    -- Goal : 0 + (k + 1) = k + 1
    rw [Nat.add_succ]              -- axiom: x + succ y = succ (x + y)
                                   -- goal: succ (0 + k) = k + 1
    rw [ih]                        -- use the inductive hypothesis
                                   -- goal: succ k = k + 1, which is true by definition

-- (B) Even more explicit: no tactics at all. This is the raw proof object.
--     `Nat.rec` IS the induction axiom; `congrArg` is "equals in, equals out";
--     `Eq.trans` chains equalities. Nothing else is used.
theorem zero_add_term (n : Nat) : 0 + n = n :=
  Nat.rec
    (motive := fun m => 0 + m = m)
    -- base case: 0 + 0 = 0
    (Nat.add_zero 0)
    -- inductive step: from ih : 0 + k = k, build 0 + succ k = succ k
    (fun k ih =>
      Eq.trans
        (Nat.add_succ 0 k)          -- 0 + succ k = succ (0 + k)
        (congrArg Nat.succ ih))     -- succ (0 + k) = succ k
    n

#print axioms Demo.zero_add_term

-- (C) The short version: let automation find it.
theorem zero_add_short (n : Nat) : 0 + n = n := by
  omega

#print axioms Demo.zero_add_short
/-
=====================================================================
  Example 2.  Theorem: the sum of two even numbers is even.
=====================================================================

  INFORMAL PROOF.
    Let m = 2a and n = 2b. Then m + n = 2a + 2b = 2(a + b),
    so m + n is even.  ∎

  Core Lean has no `Even`, so we define it: n is even if n = k + k.
-/

def IsEven (n : Nat) : Prop := ∃ k, n = k + k

-- (A) Fully explicit: unpack the witnesses, then rearrange the sum
--     one named algebra law at a time.
theorem even_add_explicit (m n : Nat) (hm : IsEven m) (hn : IsEven n) :
    IsEven (m + n) := by
  -- hm : ∃ a, m = a + a.  Take the witness a.
  obtain ⟨a, ha⟩ := hm
  -- hn : ∃ b, n = b + b.  Take the witness b.
  obtain ⟨b, hb⟩ := hn
  -- Claim: the witness for m + n is a + b.
  refine ⟨a + b, ?_⟩
  -- Goal: m + n = (a + b) + (a + b)
  rw [ha, hb]
  -- Goal: (a + a) + (b + b) = (a + b) + (a + b)
  calc (a + a) + (b + b)
      = a + (a + (b + b)) := Nat.add_assoc a a (b + b)
    _ = a + ((a + b) + b) := by rw [Nat.add_assoc a b b]
    _ = a + ((b + a) + b) := by rw [Nat.add_comm a b]
    _ = a + (b + (a + b)) := by rw [Nat.add_assoc b a b]
    _ = (a + b) + (a + b) := (Nat.add_assoc a b (a + b)).symm

-- (C) The short version.
theorem even_add_short (m n : Nat) (hm : IsEven m) (hn : IsEven n) :
    IsEven (m + n) := by
  obtain ⟨a, rfl⟩ := hm
  obtain ⟨b, rfl⟩ := hn
  exact ⟨a + b, by omega⟩

end Demo

-- Ask Lean exactly which axioms each proof depends on.
#print axioms Demo.zero_add_term
#print axioms Demo.even_add_explicit
