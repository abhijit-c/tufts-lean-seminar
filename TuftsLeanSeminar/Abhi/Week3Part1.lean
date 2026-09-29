import Mathlib

/-!
# Quantifiers: `∀` and `∃`

Tactic reference:

| Goal / hypothesis              | Tactic                      |
|--------------------------------|-----------------------------|
| Goal `∀ x, P x`                | `intro x`                   |
| Hyp `h : ∀ x, P x`, want `P a` | `h a` (pf of `∀` is a fun!) |
| Goal `∃ x, P x`                | `use a` (or `⟨a, proof⟩`)   |
| Hyp `h : ∃ x, P x`             | `rcases h with ⟨x,hx⟩`      |
|                                |    or `obtain ⟨x, hx⟩ := h` |

Usually: the outermost quantifier tells you the tactic you should use.
-/

/- first a quick example of the `apply` tactic  -/

example (p q r s : Prop) (x : p) (f : p ∨ q → r) (g : q ∨ r → s) : s := by
  sorry

/-! ## proving a `∀` statement -/

-- use `intro` to turn the goal `∀ n, ...` into a goal about a single (arbitrary) `n`.

example : ∀ n : ℕ, n + 0 = n := by
  sorry

/-! ## Using a `∀` hypothesis -/

-- A hypothesis `h : ∀ n, P n` is literally a function: `h a : P a`.
-- No tactic needed to "apply" it, just apply it like a function.
example (t : Type) (x0 : t) (P : t → Prop) (h : ∀ x, P x) : P x0 := by
  sorry 

/-! ## proving an `∃` statement -/

-- `use` lets you supply the witness directly; you'll then need to supply the required proof.
example : ∃ n : ℕ, n > 3 := 
  sorry 

/-! ## Using an `∃` hypothesis -/

-- use `rcases` to "unpack" a `∃` hypothesis; remember that `rcases` will return
-- a value together with a proof. The syntax is `rcases h with ⟨x,hx⟩`.
example (P : ℕ → Prop) (h : ∃ n, P n) : ∃ n, P n ∨ n = 0 := by
  sorry 

/-! ## ★ Negating a quantifier -/

example (P : ℕ → Prop) (h : ∃ n, ¬ P n) : ¬ ∀ n, P n := by
  sorry
  
-- Classically, `¬∀` and `∃¬` say the same thing. 
-- This uses "classical logic" -- i.e. the law of excluded middle. Frequently, this boils down
-- to using a classical tactic in Lean; in this case, use the `by_contra` tactic.
-- (The statement `import Mathlib` at the top of this file already "allowed" the use of classical 
-- logic.)
example (P : ℕ → Prop) (h : ¬ ∀ n, P n) : ∃ n, ¬ P n := by
  by_contra h'
  apply h
  intro x
  by_contra h''
  exact h' ⟨x,h''⟩ 

/-! ## ★★ A statement with both -/

-- This is the shape you'll see constantly in elementary analysis statements.
example : ∀ n : ℕ, ∃ m : ℕ, m > n := by  
  sorry
  
  -- after you produce a natural number to `use` to satisfy the existentially quantified goal,
  -- try  using the `apply?` to ask for a hint for completing the proof.
  
  -- Or: the `linarith` tactic is good at supply proofs for numerical inequalities.
