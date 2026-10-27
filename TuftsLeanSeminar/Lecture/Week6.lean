import Mathlib

/-!
# Filters and limits in Mathlib
-/

/- Design decision: how to deal with limits and continuity efficiently?

Here is an excerpt from `Mathematics in Lean`:

  Let `f : ℝ → ℝ` be any function. We can consider the limit of `f x`
  as `x` approaches some value `x₀`, but we can also consider the
  limit of `f x` as `x` approaches infinity or negative infinity. We
  can moreover consider the limit of `f x` as `x` approaches `x₀` from
  the right, conventionally written `x₀⁺`, or from the left, written
  `x₀⁻`. There are variations where `x` approaches `x₀` or `x₀⁺` or
  `x₀⁻` but is not allowed to take on the value `x₀` itself. This
  results in at least eight ways that `x` can approach something. We
  can also restrict to rational values of `x` or place other
  constraints on the domain, but let’s stick to those 8 cases.

  We have a similar variety of options on the codomain: we can specify
  that `f x` approaches a value from the left or right, or that it
  approaches positive or negative infinity, and so on. For example, we
  may wish to say that `f x` tends to `+∞` when `x` tends to `x₀` from
  the right without being equal to `x₀`. This results in 64 different
  kinds of limit statements, and we haven’t even begun to deal with
  limits of sequences [...]

So there is a need for a more uniform approach, and mathlib uses
Bourbaki's notion of `filters`.

-/

/- Overview A filter on a type `X` will be a collection of sets of
`X` satisfying some conditions that we'll indicate soon. Goals of the
definition:

- account for limits

- account for the notion of something happening "eventually": e.g. for
  "large enough `n : ℕ`" or for "points sufficiently near `x : X`"
  ...

So we have a type `Filter X`. 

- `atTop : Filter ℕ` will be made of sets of ℕ containing { n | n ≥ N } for some N.

- `𝓝 x : Filter X` will be neighborhoods of `x : X` where `[TopologicalSpace X]`
  you can type `𝓝` via `\nbhds` (or `\nhds`)

- `𝓤 X : Filter X` will be something called entourages of a uniform
  space (a generalization of a metric space)
  
  you can type `𝓤` via `\MCU`
  
- `μ.ae` sets whose complement has measure 0 wrt a measure μ.  
  
The type `Filter X` will be a *structure*, and have
a field `Filter.sets`. So if `F : Filter X` then `F.sets : Set (Set X)`
  
Remaining fields of `F : Filter X` are conditions:

- `F.univ_sets : univ ∈ F.sets`

- `F.sets_of_superset : ∀ {U V}, U ∈ F.sets → U ⊆ V → V ∈ F.sets`

- `F.inter_sets : ∀ {U V}, U ∈ F.sets → V ∈ F.sets → U ∩ V ∈ F.sets`

Note that the only *data-carrying* field of a filter is `sets`. So
there is an abbreviation:

`U ∈ F` really means `U ∈ F.sets` for `U : Set X`.
  
-/

-- Perspective: think of a filter on `X` as a generalized element of `Set X`
-- e.g. `atTop` is the set of "very large natural numbers".

-- to a fixed `S : Set X` we can associate the so-called `principal
-- filter` of all sets containing S.

#print Filter

/-
def principal {α : Type*} (s : Set α) : Filter α
    where
  sets := { t | s ⊆ t }
  univ_sets := by sorry
  sets_of_superset := by sorry
  inter_sets := by sorry

-/

def principal {α : Type*} (s : Set α) : Filter α
    where
  sets := { t | s ⊆ t }
  univ_sets := by 
    intro _ _
    tauto    
  sets_of_superset := by
    intro x y hx hxy z hz
    change s ⊆ x at hx
    apply hxy 
    exact hx hz 
  inter_sets := by
    intro x y hx hy z hz 
    exact ⟨hx hz, hy hz⟩
    
        
-- this `principal` construction already lives in Mathlib, and is
-- invoked via `𝓟`. Thus for `S : Set X`, `𝓟 S : Filter X` is the
-- corresponding principal filter.

        
/- We can also consider the filter 𝓝 x of neighborhoods of any
   x : ℝ. In the real numbers, a neighborhood of x is a set containing
   an open interval , defined in Mathlib as 
   
   `Ioo (x₀ - ε) (x₀ + ε)`
   
   (This notion of a neighborhood is only a special case of a more
   general construction in Mathlib.)  -/

-- We can now define what it means for `f:X → Y` to converge to some `G : Filter Y` along
-- some `F : Filter X`

def Tendsto₁ {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :=
  ∀ V ∈ G, f ⁻¹' V ∈ F

-- So here is what it means for a real sequence to converge:

open Filter Topology Set

variable (u : ℕ → ℝ) (x : ℝ)
in
#check Tendsto₁ u atTop (𝓝 x)

/- The notion Tendsto₁ above is definitionally equivalent to the
   notion Tendsto that is defined in Mathlib, but the latter is
   defined more abstractly. The problem with the definition of
   Tendsto₁ is that it exposes a quantifier and elements of G, and it
   hides the intuition that we get by viewing filters as generalized
   sets. -/

-- to reformulate, we first need the pushforward operation `f_*` associated
-- to a map `f:X → Y` denoted `Filter.map f` in Mathlib.


-- Let's recall what other flavors of `map` do:

#eval List.map (fun x => x*x) [1, 2, 3, 4]

#eval Option.map (fun x => x*x) (Option.some 2)
#eval Option.map (fun x => x*x) (Option.none : Option ℕ)

-- Given `F : Filter X`, `Filter.map f F : Filter Y` is defined so that
-- `V ∈ Filter.map f F ↔ f⁻¹' V ∈ F` holds "definitionally".

-- Since we've opened the `Filter` namespace, we can just invoke `map`.

/- The other tool is a partial order on filters:
  for `G H : Filter X` we have `G ≤ H ↔ ∀ V : Set X, V ∈ H → V ∈ G`
  
  Notice that the inclusion is reversed for the order!!
  
  The "inclusion" 
  
  `𝓟 : Set X → Filter X`
  
  is order preserving *with this reversed order*.
  
  Moreover, this principal operation is compatible with images
  
  `map f (𝓟 S) = 𝓟 (f'' S)`
-/


def Tendsto₂ {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :=
  map f F ≤ G

example {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :
    Tendsto₂ f F G ↔ Tendsto₁ f F G :=
  Iff.rfl

-- this definition of `Tendsto₂` is essentially Mathlib's `Filter.Tendsto`

/- We can now understand intuitively why a sequence `u : ℕ → ℝ`
   converges to a point `x₀` if and only if we have 
   
   `map u atTop ≤ 𝓝 x₀` 
   
   The inequality means the “direct image under u” of “the set of very
   big natural numbers” is “included” in “the set of points very close
   to x₀.”

-/


-- properties!

#check (@Filter.map_mono : ∀ {α β} {m : α → β}, Monotone (map m))

#check
  (@Filter.map_map :
    ∀ {α β γ} {F : Filter α} {m : α → β} {m' : β → γ}, map m' (map m F) = map (m' ∘ m) F)

/- Together these two properties allow us to prove that limits
   compose, yielding in one shot all variants of the composition
   lemma described in the introduction, and lots more. -/

example {X Y Z : Type*} {F : Filter X} {G : Filter Y} {H : Filter Z}
    {f : X → Y} {g : Y → Z}
    (hf : Tendsto₂ f F G)
    (hg : Tendsto₂ g G H)
  : Tendsto₂ (g ∘ f) F H := by
  calc map (g ∘ f) F = map g (map f F) := by rw [map_map]
    _ ≤ map g G := map_mono hf
    _ ≤ H := hg


#check Metric.tendsto_atTop


/- "Eventually"

  We now show how filters facilitate working with properties that hold
  e.g. for sufficiently large numbers

  For a predicate `P : ℕ → Prop`
  we use the suggestive notation `∀ᶠ n in atTop, P n`. 
  
  Here the superscripted f stands for “Filter.” You can think of the
  notation as saying that for all `n` in the “set of very large
  numbers,” `P n` holds. The `∀ᶠ` notation stands for `Filter.Eventually`,
  and the lemma `Filter.Eventually.and` uses the intersection property
  of filters:
  
  The point here is to prove “if P n holds for n ≥ N₁ and Q n holds
  for n ≥ N₂, then both hold for n ≥ max N₁ N₂” without a lot of fuss.

-/


#print Filter.Eventually

-- protected def Filter.Eventually.{u_1} : {α : Type u_1} → (α → Prop) → Filter α → Prop :=
-- fun {α} p f ↦ {x | p x} ∈ f

example (P Q : ℕ → Prop)
   (hP : ∀ᶠ n in atTop, P n)
   (hQ : ∀ᶠ n in atTop, Q n) :
    ∀ᶠ n in atTop, P n ∧ Q n :=
  inter_mem hP hQ
