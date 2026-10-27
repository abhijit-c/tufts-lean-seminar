import Mathlib

/-!
# Type classes: a quick tour
-/

/-! ## 1. Warm-up: `ToString` -/

structure Point where
  x : ℚ
  y : ℚ

-- Lean uses the function `toString` to produce string representations of various data types
-- eg integers, or lists of rational numbers
#eval toString (5 : ℤ)        -- "5"
#eval toString ([1, 2, 1/3] : List ℚ)        -- "[1, 2, 1/3]"


-- we can create a term of type `Point` as follows:

#eval Point.mk 1 2

-- but a priori we can't use `toString` to produce a string representation for the
-- type `Point` we just defined

-- Uncomment to show the error: failed to synthesize ToString Point
-- #eval toString (Point.mk 1 2)

-- to fix this, we must define the string representating function for
-- this type.  But we do this in a special way; one says that we
-- define an `instance` of the `ToString` typeclass.

instance : ToString Point where
  toString p := s!"({p.x}, {p.y})"

#eval toString (Point.mk 1 2)   -- "(1, 2)"

/-! ## 2. More about `Structure`s

We want to try to give a definition of a metric space, which I want first to introduce
as `a structure`. But lets give first some simpler examples of `structure`s.

We had an example of a `Structure` above, namely `Point`. Here is an
example that includes a proof obligation.  -/

-- points in the Upper Half Plane
@[ext] structure UHPPoint where
  x : ℚ
  y : ℚ
  y_pos : 0 < y


-- Building a point means supplying both the data *and* the proof.

def UHPPoint.i : UHPPoint := ⟨0, 1, one_pos⟩   -- uses the "anonymous constructor"

-- or

example : UHPPoint := UHPPoint.mk 0 1 (by norm_num)  -- using the "mk" constructor

-- or even

example : UHPPoint := {
  x := 0
  y := 1
  y_pos := by norm_num
  }

instance : ToString UHPPoint where
  toString p := toString (Point.mk p.x p.y)

-- Let's even define some `UHPPoint` valued functions:

def my_point (n : ℕ) (h : n > 0) : UHPPoint := by
  exact ⟨n,n,by positivity⟩

def my_point' (n : ℕ) : UHPPoint := by
  exact ⟨n,n+1,by positivity⟩

#eval  my_point' 13

#eval my_point 3 (by norm_num)

-- Uncomment to show the failure: the proof obligation is real.
-- def bad : UHPPoint := ⟨0, -1, by norm_num⟩

-- Operations must preserve the constraint, so they carry proofs too.
def UHPPoint.translate (a : ℚ) (p : UHPPoint) : UHPPoint :=
  ⟨p.x + a, p.y, p.y_pos⟩

def UHPPoint.dilate (c : ℚ) (hc : 0 < c) (p : UHPPoint) : UHPPoint :=
--  ⟨c * p.x, c * p.y, mul_pos hc p.y_pos⟩
  ⟨c * p.x, c * p.y, by have := p.y_pos; positivity⟩


-- Two points are equal when their data agree; the proof field takes care of itself.
theorem UHPPoint.translate_zero (p : UHPPoint) : p.translate 0 = p := by
  ext <;> simp [UHPPoint.translate]

#print UHPPoint.translate_zero

/-!

--------------------------------------------------------------------------------

A metric on `X` is a real valued function plus some axioms. A `structure` is exactly a record
of data and proofs. So we can use a structure to encode that a particular type is equipped with
suitable function.

(Here we include the redundant axiom `mdist_nonneg`  even though it is
derivable from `mdist_self` and `mdist_triangle`, to keep the proofs shorter.) -/

structure MyMetric (X : Type) where
  mdist : X → X → ℝ
  mdist_self : ∀ x, mdist x x = 0
  mdist_symm : ∀ x y, mdist x y = mdist y x
  mdist_nonneg : ∀ x y, 0 ≤ mdist x y
  mdist_triangle : ∀ x y z, mdist x z ≤ mdist x y + mdist y z
  eq_of_mdist_eq_zero : ∀ x y, mdist x y = 0 → x = y

-- The usual metric on ℝ, built as a *value* of the structure.
def realMetric : MyMetric ℝ where
  mdist x y := |x - y|
  mdist_self x := by
    have : x - x = 0 := by exact sub_self x
    exact abs_eq_zero.mpr this
  mdist_symm x y := abs_sub_comm x y
  mdist_nonneg x y := abs_nonneg _
  mdist_triangle x y z := abs_sub_le x y z
  eq_of_mdist_eq_zero x y h := sub_eq_zero.mp (abs_eq_zero.mp h)

-- We are going to formulate a theorem about any metric space: the metric `d` is an explicit
-- argument.

def ball {X : Type} (d : MyMetric X) (x : X) (r : ℝ) : Set X :=
  { z | d.mdist x z < r }

theorem mem_ball {X : Type} (d : MyMetric X) (x z : X) (r : ℝ) :
    z ∈ ball d x r ↔ d.mdist x z < r := Iff.rfl

theorem ball_subset {X : Type} (d : MyMetric X) {x y : X} {r s : ℝ}
    (h : d.mdist x y + s ≤ r) :
  ball d y s ⊆ ball d x r := by
    intro z hz
    rw [ mem_ball ] at hz ⊢
    have h1 := d.mdist_triangle x y z
    linarith

-- The general theorem, applied to ℝ with its usual metric:
example (x y : ℝ) (h : realMetric.mdist x y + 1 ≤ 3) :
    ball realMetric y 1 ⊆ ball realMetric x 3 :=
  ball_subset realMetric h

/-! 
It works, but:
* every statement carries `d.mdist` where `d` is the "metric space structure on `X`";
  there is no plain `dist x y` notation;
* every definition needs the metrics as arguments (see e.g. the definition of
  continuity just below: with two spaces
  we need two of metric space structures, and every use site must supply them);
* to get a metric on `ℝ × ℝ` we would have to build, name, and pass around a
  product metric by hand every time. -/

def MyContinuousAt {X Y : Type} (dX : MyMetric X) (dY : MyMetric Y)
    (f : X → Y) (x : X) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x', dX.mdist x' x < δ → dY.mdist (f x') (f x) < ε

#check MyContinuousAt realMetric realMetric (fun t => t) 0

/-! ## 4. Same structure, declared as a `class`

The only change: `structure` becomes `class`, and *values* become *instances*.
Look at the type of `mdist` afterwards: the structure argument is now in square
brackets, which means "Lean, find it yourself". -/

class MyMetricSpace (X : Type) where
  mdist : X → X → ℝ
  mdist_self : ∀ x, mdist x x = 0
  mdist_symm : ∀ x y, mdist x y = mdist y x
  mdist_nonneg : ∀ x y, 0 ≤ mdist x y
  mdist_triangle : ∀ x y z, mdist x z ≤ mdist x y + mdist y z
  eq_of_mdist_eq_zero : ∀ x y, mdist x y = 0 → x = y

#check @MyMetricSpace.mdist      -- note `[self : MyMetricSpace X]`

open MyMetricSpace

instance : MyMetricSpace ℝ where
  mdist x y := |x - y|
  mdist_self x := by simp
  mdist_symm x y := abs_sub_comm x y
  mdist_nonneg x y := abs_nonneg _
  mdist_triangle x y z := abs_sub_le x y z
  eq_of_mdist_eq_zero x y h := sub_eq_zero.mp (abs_eq_zero.mp h)


-- ball, again

def ball₁ {X : Type} [MyMetricSpace X] (x : X) (r : ℝ) : Set X :=
  { z : X | mdist x z < r }

theorem mem_ball₁ {X : Type} [MyMetricSpace X] (x z : X) (r : ℝ) :
  z ∈ ball₁ x r ↔ mdist x z < r := Iff.rfl

-- somewhat less cluttered statement and proof
theorem ball_subset₁ {X : Type} [MyMetricSpace X] {x y : X} {r s : ℝ}
    (h : mdist x y + s ≤ r) :
  ball₁ y s ⊆ ball₁ x r := by
    intro z hz
    rw [ mem_ball₁ ] at hz ⊢
    have h1 := mdist_triangle x y z
    linarith

-- The general theorem, applied to ℝ using the typeclass
example (x y : ℝ) (h : mdist x y + 1 ≤ 3) :
    ball₁ y 1 ⊆ ball₁ x 3 :=
  ball_subset₁ h



/-! ## 5. Instances compose

Here we *teach* Lean one general fact: if `X` and `Y` have metrics, then so does
`X × Y` (with the max metric). Writing this instance is ordinary work, and we
supply the axiom proofs ourselves. After that, Lean uses the instance
automatically wherever a `MyMetricSpace (X × Y)` is needed, so the work is done
once for all `X` and `Y`. With explicit structures we'd have had to build and pass
the product metric by hand at every use. -/



instance {X Y : Type} [MyMetricSpace X] [MyMetricSpace Y] : MyMetricSpace (X × Y) where
  mdist p q := max (mdist p.1 q.1) (mdist p.2 q.2)
  mdist_self p := by simp [mdist_self]
  mdist_symm p q := by rw [mdist_symm p.1 q.1, mdist_symm p.2 q.2]
  mdist_nonneg p q := le_trans (mdist_nonneg p.1 q.1) (le_max_left _ _)
  mdist_triangle p q r := by
    apply max_le
    · calc mdist p.1 r.1 ≤ mdist p.1 q.1 + mdist q.1 r.1 := mdist_triangle _ _ _
        _ ≤ _ := add_le_add (le_max_left _ _) (le_max_left _ _)
    · calc mdist p.2 r.2 ≤ mdist p.2 q.2 + mdist q.2 r.2 := mdist_triangle _ _ _
        _ ≤ _ := add_le_add (le_max_right _ _) (le_max_right _ _)
  eq_of_mdist_eq_zero p q h := by
    have h1 := le_max_left (mdist p.1 q.1) (mdist p.2 q.2)
    have h2 := le_max_right (mdist p.1 q.1) (mdist p.2 q.2)
    rw [h] at h1 h2
    exact Prod.ext
      (eq_of_mdist_eq_zero _ _ (le_antisymm h1 (mdist_nonneg _ _)))
      (eq_of_mdist_eq_zero _ _ (le_antisymm h2 (mdist_nonneg _ _)))



-- The general theorem, applied to ℝ × ℝ using the typeclass
example (x y : ℝ × ℝ) (h : mdist x y + 1 ≤ 3) :
    ball₁ y 1 ⊆ ball₁ x 3 :=
  ball_subset₁ h


-- A definition that mentions two spaces, with no metric arguments in sight.
def MyContinuousAt' {X Y : Type} [MyMetricSpace X] [MyMetricSpace Y]
    (f : X → Y) (x : X) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x', mdist x' x < δ → mdist (f x') (f x) < ε

#check MyContinuousAt' (fun p : ℝ × ℝ => p.1) (0, 0)

-- an instance for R^n

instance {n : ℕ} {X : Type} [MyMetricSpace X] : MyMetricSpace (Fin n → X) where
  mdist f g := ∑ i, mdist (f i) (g i)
  mdist_self f := Finset.sum_eq_zero (fun i _ => mdist_self (f i))
  mdist_symm f g := Finset.sum_congr rfl (fun i _ => mdist_symm (f i) (g i))
  mdist_nonneg f g := Finset.sum_nonneg (fun i _ => mdist_nonneg (f i) (g i))
  mdist_triangle f g h := by
    calc ∑ i, mdist (f i) (h i)
        ≤ ∑ i, (mdist (f i) (g i) + mdist (g i) (h i)) :=
          Finset.sum_le_sum (fun i _ => mdist_triangle (f i) (g i) (h i))
      _ = _ := Finset.sum_add_distrib
  eq_of_mdist_eq_zero f g hfg := by
    funext i
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mdist_nonneg (f j) (g j))).mp hfg i (Finset.mem_univ i)
    exact eq_of_mdist_eq_zero _ _ h0


-- used without further work
example (x y : Fin 5 → ℝ) (h : mdist x y + 1 ≤ 3) :
    ball₁ y 1 ⊆ ball₁ x 3 :=
  ball_subset₁ h


-- Caveat: a class picks *one* structure per type. When you
-- need two metrics on the same set, that is where structures (or type synonyms)
-- are still the right tool.

/-! ## 6. Mathlib's real thing: `MetricSpace` and `dist` -/

#print MetricSpace      -- the same idea, with more fields

#check (dist : ℝ → ℝ → ℝ)
#check (dist : ℂ → ℂ → ℝ)
#check (dist : ℝ × ℝ → ℝ × ℝ → ℝ)

--here is how to get R^n
variable (n : ℕ) in
 #check (dist : (Fin n → ℝ) → (Fin n → ℝ) → ℝ)

#synth MetricSpace ℝ
#synth MetricSpace ℂ
#synth MetricSpace (ℝ × ℝ)       -- the sup metric on a product

variable (n : ℕ) in
  #synth MetricSpace (Fin n → ℝ)   -- sup metric on ℝⁿ

#synth MetricSpace ℕ
#synth MetricSpace ℚ

def ball₂ {X : Type} [MetricSpace X] (x : X) (r : ℝ) : Set X :=
  { z : X | dist x z < r }

theorem mem_ball₂ {X : Type} [MetricSpace X] (x z : X) (r : ℝ) :
  z ∈ ball₂ x r ↔ dist x z < r := Iff.rfl


-- somewhat less cluttered statement and proof
theorem ball_subset₂ {X : Type} [MetricSpace X] {x y : X} {r s : ℝ}
    (h : dist x y + s ≤ r) :
  ball₂ y s ⊆ ball₂ x r := by
    intro z hz
    rw [ mem_ball₂ ] at hz ⊢
    have h1 := dist_triangle x y z
    linarith


#check @ball_subset₂ ℝ
#check @ball_subset₂ ℂ
#check @ball_subset₂ (ℝ × ℝ)

variable (n : ℕ) in
  #check @ball_subset₂ (Fin n → ℝ)

-- A failure that is mathematics: unbounded functions have no sup metric, so there
-- is no `MetricSpace` instance on `ℝ → ℝ`.
-- Uncomment to show "failed to synthesize":
-- #synth MetricSpace (ℝ → ℝ)

-- By contrast, bounded continuous functions do form a metric space:
#synth MetricSpace (BoundedContinuousFunction ℝ ℝ)

/-! The hierarchy: structure from structure. A metric space automatically has a
topology, and nobody wrote that for ℝ^n by hand. -/

variable (n : ℕ) in
  #synth TopologicalSpace (Fin n → ℝ)

example {X : Type*} [MetricSpace X] : TopologicalSpace X := inferInstance

-- So lemmas about topological spaces apply to metric spaces for free.
example {X : Type*} [MetricSpace X] (x : X) :
    Continuous (fun y => dist x y) :=
  continuous_const.dist continuous_id

#check @NormedAddCommGroup
#check @InnerProductSpace
#check @CompleteSpace


/-! ## 7. Structure on a type constructor: `Functor` -/

-- So far a class was structure on a type `X`. Here it is structure on a
-- type *constructor* `F : Type → Type`.
#check (Functor : (Type → Type) → Type 1)
#check @Functor.map    -- (α → β) → F α → F β

-- `<$>` is infix notation for `Functor.map`
#eval (· + 1) <$> [1, 2, 3]               -- [2, 3, 4]
#eval (· + 1) <$> some 5                  -- some 6
#eval (· + 1) <$> (none : Option Nat)     -- none

-- Now let's define a binary tree data type -- really a type transformer!
-- (data lives at the nodes; the leaves are empty)

inductive MyTree (α : Type) where
  | leaf : MyTree α
  | node : MyTree α → α → MyTree α → MyTree α
deriving Repr

-- We would like to be able to use `Functor.map` for data of type `MyTree`.

-- Let's examine the `Functor` typeclass to see what is required to
-- define an instance

#print Functor

/- We see:

class Functor.{u, v} (f : Type u → Type v) : Type (max (u + 1) v)
number of parameters: 1
fields:
  Functor.map : {α β : Type u} → (α → β) → f α → f β
  Functor.mapConst : {α β : Type u} → α → f β → f α :=
    fun {α β} ↦ Functor.map ∘ Function.const β
constructor:
  Functor.mk.{u, v} {f : Type u → Type v} (map : {α β : Type u} → (α → β) → f α → f β)
    (mapConst : {α β : Type u} → α → f β → f α) : Functor f

Note that Functor.mapConst is (by default) defined in terms of Functor.map, so we aren't
required to implement that field to define an instance.
-/

def MyTree.map {α β : Type} (f : α → β) : MyTree α → MyTree β
  | .leaf => .leaf
  | .node l a r => .node (l.map f) (f a) (r.map f)

instance : Functor MyTree where
  map := MyTree.map

def testMyTree : MyTree String :=
.node (.node (.node .leaf "Jim" .leaf) "Fred"
  (.node .leaf "Sheila" .leaf)) "Alice"
  (.node .leaf "Bob" (.node .leaf "Eve" .leaf))

#eval testMyTree

#eval testMyTree.map String.toLower

-- or equivalently

#eval String.toLower <$> testMyTree

/-! `Functor` only asks for `map`. The functor *laws* live in a second class. -/

#print LawfulFunctor    -- id_map, comp_map (and a technical map_const)

/-
class LawfulFunctor.{u, v} (f : Type u → Type v) [Functor f] : Prop
number of parameters: 2
fields:
  LawfulFunctor.map_const : ∀ {α β : Type u}, Functor.mapConst = Functor.map ∘ Function.const β
  LawfulFunctor.id_map : ∀ {α : Type u} (x : f α), id <$> x = x
  LawfulFunctor.comp_map : ∀ {α β γ : Type u} (g : α → β) (h : β → γ) (x : f α),
    (h ∘ g) <$> x = h <$> g <$> x
constructor:
  LawfulFunctor.mk.{u, v} {f : Type u → Type v} [Functor f]
    (map_const : ∀ {α β : Type u}, Functor.mapConst = Functor.map ∘ Function.const β)
    (id_map : ∀ {α : Type u} (x : f α), id <$> x = x)
    (comp_map : ∀ {α β γ : Type u} (g : α → β) (h : β → γ) (x : f α),
      (h ∘ g) <$> x = h <$> g <$> x) : LawfulFunctor f

-/


theorem MyTree.map_id {α : Type} (t : MyTree α) : t.map id = t := by
  induction t with
  | leaf => rfl
  | node l a r ihl ihr => simp [MyTree.map, ihl, ihr]

theorem MyTree.map_comp {α β γ : Type} (g : α → β) (h : β → γ) (t : MyTree α) :
    t.map (h ∘ g) = (t.map g).map h := by
  induction t with
  | leaf => rfl
  | node l a r ihl ihr => simp [MyTree.map, ihl, ihr]

instance : LawfulFunctor MyTree where
  map_const := rfl
  id_map := MyTree.map_id
  comp_map := MyTree.map_comp

-- Why the laws are worth stating: this is a perfectly legal `Functor` instance.
structure Twice (α : Type) where
  a : α
  b : α

instance : Functor Twice where
  map f t := ⟨f t.a, f t.a⟩

-- But for this "functor", mapping the identity does not behave as expected.

#eval (id <$> Twice.mk 1 2).b    -- 1, not 2: `map id ≠ id`, so no `LawfulFunctor`
