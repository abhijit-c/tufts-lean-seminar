theorem my_inter_sub_left (A B : Set α) : A ∩ B ⊆ A := by
  intro x hx
  rcases hx with ⟨ha, hb⟩
  exact ha

theorem my_sub_union_left (A B : Set α) : A ⊆ A ∪ B := by
  intro x hx
  exact Or.inl hx

theorem my_sub_trans (A B C : Set α) (hAB : A ⊆ B) (hBC : B ⊆ C) : A ⊆ C := by
  intro x hx
  exact hBC (hAB hx)

-- term-mode reuse
example (A B : Set α) : A ∩ B ⊆ A ∪ B :=
  my_sub_trans _ _ _ (my_inter_sub_left A B) (my_sub_union_left A B)

-- tactic-mode reuse: `have`, then `exact`
example (A B : Set α) : A ∩ B ⊆ A ∪ B := by
  have h1 := my_inter_sub_left A B
  have h2 := my_sub_union_left A B
  exact my_sub_trans _ _ _ h1 h2

-- `apply` leaves the hypotheses as new goals
example (A B : Set α) : A ∩ B ⊆ A ∪ B := by
  apply my_sub_trans (A ∩ B) A (A ∪ B)
  · exact my_inter_sub_left A B
  · exact my_sub_union_left A B
