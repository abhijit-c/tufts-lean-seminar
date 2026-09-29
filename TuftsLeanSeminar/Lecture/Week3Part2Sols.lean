import Mathlib.Tactic


/-!
# Lean seminar: proving elementary set-theoretic statements 
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


/-  ## rintro membership is just the predicate -/

example (p : α → Prop) (a : α) : a ∈ {x | p x} ↔ p a := Iff.rfl

example (A B : Set α) (x : α) : x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B := Iff.rfl

example (A B : Set α) (x : α) : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B := Iff.rfl

example (A B : Set α) : A ⊆ B ↔ ∀ x, x ∈ A → x ∈ B := Iff.rfl

example : (Set.univ : Set α) = { _x:α | True} := rfl

example (p q : α → Prop) (h : (s : α) → p s → q s)
    : { s | p s } ⊆ { s | q s }   := by 
  rintro s ks
  exact h s ks

-- Worked example.  Read it, step through it, see how the goal changes.
example (A B : Set α) : A ∩ B ⊆ A := by
  rintro x hx
  rcases hx with ⟨ha,hb⟩
  exact ha


/-! =======================================================================
    Part 1: subsets are `∀` (`intro`) 
    =======================================================================
-/

example (A B : Set α) : A ⊆ A ∪ B := by
  rintro _ ha
  apply Or.inl
  exact ha

example (A B : Set α) : A ∩ B ⊆ B := by
  rintro x ⟨ha,hb⟩
  exact hb

example (A B : Set α) : A ∩ B ⊆ A ∪ B := by
  rintro x ⟨ha,_⟩
  apply Or.inl
  exact ha

example (A B C : Set α) (hAB : A ⊆ B) (hBC : B ⊆ C) : A ⊆ C := by
  rintro _ ha
  apply hBC 
  apply hAB
  exact ha

example (A B C : Set α) (hB : A ⊆ B) (hC : A ⊆ C) : A ⊆ B ∩ C := by
  rintro a ha
  exact ⟨hB ha,hC ha⟩

-- Hint: the hypothesis `x ∈ A ∪ B` is an `∨`; split on it.
example (A B C : Set α) (hA : A ⊆ C) (hB : B ⊆ C) : A ∪ B ⊆ C := by
  rintro a (haA | haB) 
  · exact hA haA
  · exact hB haB
  

-- ★ Note `x ∈ A \ B` means `x ∈ A ∧ x ∉ B`.
example (A B C : Set α) : (A \ B) \ C ⊆ A \ (B ∪ C) := by
  intro a ⟨ ⟨h0,h1⟩ , h2 ⟩
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
  ext x
  constructor
  · rintro (ha | hb)
    · exact Or.inr ha
    · exact Or.inl hb
  · rintro (hb | ha)
    · exact Or.inr hb
    · exact Or.inl ha

-- The first real case split.
example (A B C : Set α) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  ext x
  constructor
  · rintro ⟨ha, hbc⟩
    rcases hbc with kb | kc
    · exact Or.inl ⟨ ha,kb ⟩
    · exact Or.inr ⟨ ha,kc ⟩
  · rintro (hab | hac)
    · constructor
      · exact hab.1
      · exact Or.inl hab.2 
    · constructor
      · exact hac.1
      · exact Or.inr hac.2
  
  
example (A B C : Set α) : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  ext x
  constructor
  · rintro (ha | ⟨hb, hc⟩)
    · exact ⟨ Or.inl ha, Or.inl ha⟩ 
    · exact ⟨ Or.inr hb, Or.inr hc⟩
  · rintro  ⟨ (ha1 | hb), (ha2 | hc) ⟩
    · exact Or.inl ha1
    · exact Or.inl ha1
    · exact Or.inl ha2
    · exact Or.inr ⟨hb,hc⟩
    

-- ★ This one needs classical logic: try `by_cases hA : x ∈ A`.
example (A B : Set α) : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  ext x
  constructor
  · rintro h
    by_cases hA : x ∈ A
    · apply Or.inr 
      intro hB
      exact h ⟨hA,hB⟩
    · apply Or.inl 
      intro k
      exact hA k
  · rintro (hA | hB) ⟨ka,kb⟩ 
    · exact hA ka
    · exact hB kb


-- ★ Inclusion can be expressed with an equation.
example (A B : Set α) : A ⊆ B ↔ A ∩ B = A := by
  constructor
  · intro h
    ext x
    constructor
    · rintro ⟨hxA,_⟩
      exact hxA
    · rintro k
      exact ⟨k, h k⟩
  · intro h x hxA
    have hx : x ∈ A ∩ B := by
      rw [h]
      exact hxA
    exact hx.2 
    

/-! ## Act 3: functions enter (`⁻¹'` and `''`) -/

variable (f : β → α)

/- for `X : Set α`, we get the pre-image `f⁻¹'(X) : Set β`.

   And for `Y : Set β`, we get the image `f''(Y) : Set α`.
   
-/   

-- Hint: The next three actually are true by definition. One says that
-- that the terms in the equalities are `defeq`
-- so you can solve them with `rfl`

example (A B : Set α) : f ⁻¹' (A ∩ B) = f ⁻¹' A ∩ f ⁻¹' B := rfl

example (A B : Set α) : f ⁻¹' (A ∪ B) = f ⁻¹' A ∪ f ⁻¹' B := rfl

example (A : Set α) : f ⁻¹' Aᶜ = (f ⁻¹' A)ᶜ := rfl


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
  rintro x hx
  rcases hx with ⟨y,hy,rfl⟩
  exact ⟨⟨y,hy.1,rfl⟩,⟨y,hy.2,rfl⟩⟩

  
--  sorry

-- The reverse inclusion is false in general.  It is interesting to look where a proof gets stuck.
-- One possibility to get a correct statement is to insist that `f` be injective.

-- The hypothesis `Function.Injective` is as follows

#print Function.Injective
/- 

   def Function.Injective.{u_1, u_2} : {α : Sort u_1} → {β : Sort u_2} → (α → β) → Prop :=
     fun {α} {β} f ↦ ∀ ⦃a₁ a₂ : α⦄, f a₁ = f a₂ → a₁ = a₂    

   Thus `Function.Injective f` is the `Prop` that `f` is injective.
   So we can assume injectivity by providing a `proof` to our theorem -- i.e. including an argument
   of the form
   
   `hf : Function.Injective f`

   Now we can *use* `hf` by applying it to an equality `f a₁ = f a₂`.
-/


-- solution 1
example (hf : Function.Injective f) (S T : Set β) :
    f '' S ∩ f '' T ⊆ f '' (S ∩ T) := by
  rintro x ⟨hy,hz⟩
  rcases hy with ⟨s,hs⟩
  rcases hz with ⟨t,ht⟩
  have : f s = f t := by 
    rw [ hs.2 , ht.2] 
  have : s = t := hf this
  use s
  constructor
  · constructor  
    · exact hs.1
    · rw [this]
      exact ht.1
  · exact hs.2

-- solution 2
example (hf : Function.Injective f) (S T : Set β) :
    f '' S ∩ f '' T ⊆ f '' (S ∩ T) := by
  rintro x ⟨⟨s,hs,rfl⟩,⟨t,ht,htx⟩⟩
  have : t = s := hf htx
  use t
  subst this 
  exact ⟨⟨hs,ht⟩, htx⟩
  

-- ★ A counterexample without injectivity.
-- Hint: take `f := fun _ => 0`, `S := {0}`, `T := {1}`.

-- solution 1
example : ∃ (g : ℕ → ℕ) (S T : Set ℕ),
    ¬ (g '' S ∩ g '' T ⊆ g '' (S ∩ T)) := by
  let f : ℕ → ℕ := fun _ => 0
  let S : Set ℕ := {0}
  let T : Set ℕ := {1}
  use f,S,T
  rintro h
  have h0S : 0 ∈ f '' S := by
    exact ⟨0,rfl,rfl⟩ 
  have h0T : 0 ∈ f '' T := by
    exact ⟨1,rfl,rfl⟩
  have h0ST : 0 ∈ f '' (S ∩ T) := by
    exact h ⟨h0S,h0T⟩ 
  have empty : S ∩ T = ∅ := by 
    unfold S
    unfold T
    simp
  have image_empty : f '' (S ∩ T) = ∅ := by
    rw [ empty ] 
    exact image_empty f
  rw [image_empty] at h0ST 
  exact h0ST 
    
    
-- solution 2
example : ∃ (g : ℕ → ℕ) (S T : Set ℕ),
    ¬ (g '' S ∩ g '' T ⊆ g '' (S ∩ T)) := by
  refine ⟨fun _ => 0, {0}, {1}, ?_⟩
  rintro h 
  rcases h ⟨⟨0,rfl,rfl⟩, ⟨1,rfl,rfl⟩⟩ with ⟨n,⟨hn0,hn1⟩,_⟩
  have : 0 = 1 := hn0.symm.trans hn1
  exact absurd this (by decide)
  
  

/-! ## Capstone: image and preimage are adjoint -/

example (S : Set β) (B : Set α) : f '' S ⊆ B ↔ S ⊆ f ⁻¹' B := by
  sorry

-- ★★ Injectivity, characterized by a property of sets.
-- Hint for `←`: given `f x = f y`, apply the hypothesis to `S = {x}`, `T = {y}`,
-- and show `f x ∈ f '' {x} ∩ f '' {y}`.
example : Function.Injective f ↔ ∀ S T : Set β, f '' (S ∩ T) = f '' S ∩ f '' T := by
  sorry
