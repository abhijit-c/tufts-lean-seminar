import Mathlib.Tactic

/-!
# Homework following the Week3 set-theory session

Target completion date: Oct 6.

To work on these problems, first copy this file into the `Work/`
directory in your copy of the repository before editing it, so that
you don't later have problems with merge conflicts -- i.e. so that
`git pull` doesn't collide with your changes.

## What to do

1. Finish any exercises from the problem set distributed in the lecture that 
   weren't finished.

2. **Main problem.**  A function is injective exactly when taking images
   respects intersections -- see below  Prove it.

3. *(Example)* Injectivity is really needed: exhibit a function in
   Lean and two sets for which the inclusion fails.

If you get stuck, note *where* you got stuck (which goal, which step) and
bring that to the meeting.  Being stuck at a specific place is useful
information for everyone.

As before, once you have a proof by hand you are welcome to see what
`aesop` or `ext x; simp; tauto` make of the easier pieces, but the main
problem needs an idea, so don't expect automation to finish it for you.
-/

open Set

variable {α β : Type*}

/-! ## Main problem -/

-- Hint for `←`: suppose `f x = f y`.  Apply the hypothesis to the
-- singletons `S = {x}` and `T = {y}`.  Then `f x` lies in
-- `f '' {x} ∩ f '' {y}`, hence in `f '' ({x} ∩ {y})`, and so
-- `{x} ∩ {y}` is nonempty.
--
-- Hint for `→`: `ext y`, then `constructor`.  One direction is the
-- inclusion you proved in class; the other is where injectivity gets used.
example (f : β → α) :
    Function.Injective f ↔ ∀ S T : Set β, f '' (S ∩ T) = f '' S ∩ f '' T := by
  sorry

/-! ## Example -/

-- Hint: take `g := fun _ => 0`, `S := {0}`, `T := {1}`.
-- To refute an inclusion, you need a point in the left side that is not in
-- the right side; here that point is `0`.
example : ∃ (g : ℕ → ℕ) (S T : Set ℕ),
    ¬ (g '' S ∩ g '' T ⊆ g '' (S ∩ T)) := by
  sorry
