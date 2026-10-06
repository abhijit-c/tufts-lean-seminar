import Mathlib.Tactic


/-!
# Tufts Lean seminar: Week 4
-/

-- Recall las week we proved the following, and I said it used "classical" math
-- i.e. law of the excluded middle
example (P : ℕ → Prop) (h : ¬ ∀ n, P n) : ∃ n, ¬ P n := by
  by_contra h'
  apply h
  intro x
  by_contra h''
  exact h' ⟨x,h''⟩ 

-- you can use the `#print axioms` command to see what axioms a particular construction depends on
-- But: that construction needs to have a *name*. So let's restate the above example:

lemma negation (P : ℕ → Prop) (h : ¬ ∀ n, P n) : ∃ n, ¬ P n := by
  by_contra h'
  apply h
  intro x
  by_contra h''
  exact h' ⟨x,h''⟩ 

#check Quot.sound
#print axioms negation 
-- Messages here:
-- 27:0:
-- 'negation' depends on axioms: [propext, Classical.choice, Quot.sound]

-- basically everything that was used here was already used by "excluded middle"
#print axioms Classical.em
#check Classical.em


/-!
# proving elementary set-theoretic statements 
-/

/- a predicate on a type `α : Type` is just a function
   `P : α → Prop`.
   
   In Mathlib, one speaks of a set as term `S` of type `Set α` for some type α.
   
   For a given term `x : α`, membership in `S` is viewed as a proposition.
   
   Thus `S` is really `{ x | P x }` for some predicate `P : α → Prop`.
   
   For `y : α`, the proposition `y ∈ S` is then defined to be the same as the 
   proposition `P y`.
   
   -/

open Set

variable {α β : Type*}


/- 
Theme: a statement about sets is a statement of logic in disguise,
and the outermost connective tells you which tactic to use.

| goal or hypothesis        | tactic                                  |
|---------------------------|-----------------------------------------|
| goal  `A ⊆ B`, `∀`, `→`   | `intro x hx`                            |
| goal  `A = B` (sets)      | `ext x`, then usually `constructor`     |
| goal  `P ∧ Q`, `P ↔ Q`    | `constructor`  (or `⟨_, _⟩`)            |
| goal  `P ∨ Q`             | `left`  /  `right`                      |
| goal  `∃ x, P x`          | `use a`  (or `⟨a, _⟩`)                  |
| hyp   `h : P ∧ Q`         | `obtain ⟨h₁, h₂⟩ := h`   (or `h.1`, `h.2`) |
| hyp   `h : P ∨ Q`         | `rcases h with h | h`                   |
| hyp   `h : ∃ x, P x`      | `obtain ⟨a, ha⟩ := h`                   |
| goal  `False`-ish, `¬`    | `intro h`  /  `by_contra h`             |

`rintro` combines `intro` and `rcases`, e.g. `rintro x ⟨hA, hB | hC⟩`.

Useful when stuck:
* `show ...` restates the goal in an equivalent (definitionally equal) form.
* `exact?` or `apply?` asks Lean to search for a closing term.
* `simp only [Set.mem_inter_iff]` unfolds membership if you prefer explicit steps.
* `rfl` will sometimes work when both sides unfold to the same thing.

Replace each `sorry` with a proof.  Starred exercises (★) are harder.
Once you have a proof by hand, feel free to see what `aesop` or
`ext x; simp; tauto` do with the same statement.
-/


/-  ## intro membership is just the predicate -/

example (p : α → Prop) (a : α) : a ∈ {x | p x} ↔ p a := Iff.rfl

example (A B : Set α) (x : α) : x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B := Iff.rfl

example (A B : Set α) (x : α) : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B := Iff.rfl

example (A B : Set α) : A ⊆ B ↔ ∀ x, x ∈ A → x ∈ B := Iff.rfl

example : (Set.univ : Set α) = {_x:α | True} := rfl

example (p q : α → Prop) (h : (s : α) → p s → q s)
    : { s | p s } ⊆ { s | q s }   := by 
  sorry

-- Worked example.  Read it, step through it, see how the goal changes.
example (A B : Set α) : A ∩ B ⊆ A := by
  -- exact inter_subset_left
  rintro x ⟨ha,gb⟩
  exact ha
  -- intro x hx
  -- rcases hx with ⟨ha,hb⟩
  -- exact ha


/-! =======================================================================
    Part 1: subsets are `∀` (`intro`) 
    =======================================================================
-/

theorem my_inter_sub_left (A B : Set α) : A ∩ B ⊆ A := by
  rintro x ⟨ha, hb⟩
  exact ha


theorem my_sub_union_left (A B : Set α) : A ⊆ A ∪ B := by
  rintro x hx
  exact Or.inl hx

theorem my_sub_trans (A B C : Set α) (hAB : A ⊆ B) (hBC : B ⊆ C) : A ⊆ C := by
  rintro x hx
  apply hBC
  apply hAB
  exact hx

-- let's prove `A ∩ B ⊆ A ∪ B` using our intermediate results

-- first, as a term without using tactics
example (A B : Set α) : A ∩ B ⊆ A ∪ B :=
  my_sub_trans _ _ _ (my_inter_sub_left A B) (my_sub_union_left A B)
  
-- second, in tactics mode using `have`
example (A B : Set α) : A ∩ B ⊆ A ∪ B := by
  sorry

-- third, in tactics mode using `apply`
example (A B : Set α) : A ∩ B ⊆ A ∪ B := by
  sorry  

example (A B C : Set α) (hB : A ⊆ B) (hC : A ⊆ C) : A ⊆ B ∩ C := by
  intro x hx
  exact ⟨hB hx, hC hx⟩

-- Hint: the hypothesis `x ∈ A ∪ B` is an `∨`; split on it.
example (A B C : Set α) (hA : A ⊆ C) (hB : B ⊆ C) : A ∪ B ⊆ C := by
  rintro x (ha | hb)
  · exact hA ha
  · exact hB hb

-- ★ Note `x ∈ A \ B` means `x ∈ A ∧ x ∉ B`.
example (A B C : Set α) : (A \ B) \ C ⊆ A \ (B ∪ C) := by
  intro a ⟨ ⟨h0,h1⟩, h2 ⟩
  constructor
  · exact h0
  · rintro (hb | hc)
    · exact absurd hb h1
    · exact absurd hc h2


/-  =======================================================================
    Part 2: equality is two inclusions (use `ext`, `constructor`)
    =======================================================================
-/

-- Worked example.
example (A B : Set α) : A ∩ B = B ∩ A := by
  ext x
  constructor
  · rintro ⟨hA, hB⟩
    exact ⟨hB, hA⟩
  · rintro ⟨hB, hA⟩
    exact ⟨hA, hB⟩

example (A B : Set α) : A ∪ B = B ∪ A := by
  ext
  constructor
  · rintro (hA | hB)
    · exact Or.inr hA
    · exact Or.inl hB
  · rintro (hB | hA)
    · exact Or.inr hB
    · exact Or.inl hA

-- The first real case split.
example (A B C : Set α) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  sorry

example (A B C : Set α) : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  sorry

-- ★ This one needs classical logic: try `by_cases hA : x ∈ A`.
example (A B : Set α) : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  sorry

-- ★ Inclusion can be expressed with an equation.
example (A B : Set α) : A ⊆ B ↔ A ∩ B = A := by
  sorry


/-! ## Act 3: functions enter (`⁻¹'` and `''`) -/

variable (f : β → α)

/- for `X : Set α`, we get the pre-image `f⁻¹'(X) : Set β`.

   And for `Y : Set β`, we get the image `f''(Y) : Set α`.
   
-/   

-- Hint: The next three actually are true by definition. One says that
-- that the terms in the equalities are `defeq`
-- so you can solve them with `rfl`

example (A B : Set α) : f ⁻¹' (A ∩ B) = f ⁻¹' A ∩ f ⁻¹' B := rfl

-- by
--   sorry
  
example (A B : Set α) : f ⁻¹' (A ∪ B) = f ⁻¹' A ∪ f ⁻¹' B := by
  sorry

example (A : Set α) : f ⁻¹' Aᶜ = (f ⁻¹' A)ᶜ := by
  sorry

-- Membership in an image is existential: `y ∈ f '' S ↔ ∃ x, x ∈ S ∧ f x = y`.
-- So: `rcases ⟨x, hx, rfl⟩` to use it, `⟨x, hx, rfl⟩` or `use x` to prove it.
example (S T : Set β) : f '' (S ∪ T) = f '' S ∪ f '' T := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    rcases hx with hxs | hxt 
    · apply Or.inl
      exact mem_image_of_mem f hxs 
    · apply Or.inr
      exact mem_image_of_mem f hxt 
  · rintro (⟨y,hy,rfl⟩  | ⟨y,hy,rfl⟩)
    · exact ⟨y,Or.inl hy, rfl⟩
    · exact ⟨y,Or.inr hy, rfl⟩

example (S T : Set β) : f '' (S ∩ T) ⊆ f '' S ∩ f '' T := by
  sorry

-- The reverse inclusion is false in general.  Where does a proof get stuck?
-- Then add the hypothesis and finish.
example (hf : Function.Injective f) (S T : Set β) :
    f '' S ∩ f '' T ⊆ f '' (S ∩ T) := by
  sorry

-- ★ A counterexample without injectivity.
-- Hint: take `f := fun _ => 0`, `S := {0}`, `T := {1}`.
example : ∃ (g : ℕ → ℕ) (S T : Set ℕ),
    ¬ (g '' S ∩ g '' T ⊆ g '' (S ∩ T)) := by
  sorry

/-! ## Capstone: image and preimage are adjoint -/

example (S : Set β) (B : Set α) : f '' S ⊆ B ↔ S ⊆ f ⁻¹' B := by
  sorry

-- ★★ Injectivity, characterized by a property of sets.
-- Hint for `←`: given `f x = f y`, apply the hypothesis to `S = {x}`, `T = {y}`,
-- and show `f x ∈ f '' {x} ∩ f '' {y}`.
example : Function.Injective f ↔ ∀ S T : Set β, f '' (S ∩ T) = f '' S ∩ f '' T := by
  sorry
