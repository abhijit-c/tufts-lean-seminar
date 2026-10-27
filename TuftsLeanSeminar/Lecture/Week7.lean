/-!
# Inductive types and "induction"
-/

-- Let's define our own version of the natural numbers, via Peano.

inductive MyNat where
| zero : MyNat
| succ : MyNat → MyNat
deriving Repr


def two : MyNat := .succ (.succ .zero)

-- when you define an inductive type, lean automatically creates
-- something called a _recursor_ for the type.

-- In our case, the recursor is named `MyNat.rec`

-- Let's see its signature:

#check @MyNat.rec

/- results in the following (after adding some line-breaks for readability...)

  {motive : MyNat → Sort u_1} 
  → motive MyNat.zero 
  → ((a : MyNat) → motive a → motive a.succ) 
  → (t : MyNat) 
  → motive t
  
  
Note that `Sort u_1` here ranges over both `Type` and `Prop`; this
lets one recursor handle both recursion *and* induction.
  
-/

-- This recursor will enable us to do "proofs by induction" as well as 
-- "constructions by recursion".

-- let's do some examples.

-- here we define a doubling function by "pattern matching"

def double : MyNat → MyNat
  | .zero   => .zero
  | .succ n => .succ (.succ (double n))

-- Now let's instead use the recursor to define the doubling function


-- Look at the signature of `MyNat.rec` above. The result is `motive t` 

-- `motive t` is the *type* of the thing we want to produce at `t`.
-- Here the answer is: we want to produce a natural number regardless
-- of what `t` is, so the motive is the constant function 

-- `fun _ = MyNat`.

-- The next argument to MyNat.rec requires us to give a term of type
-- `motive MyNat.zero`.

def doubleZero : MyNat := .zero

-- and we need a term of type `((a : MyNat) → motive a → motive a.succ)`

def doubleStep (_ : MyNat) (doubleN : MyNat) : MyNat := .succ (.succ doubleN)

-- note that we don't use the first argument. The recursor still
-- expects it to be part of the signature though.

#check (doubleZero : (fun _ => MyNat) MyNat.zero)
#check (doubleStep : (a : MyNat) → (fun _ => MyNat) a → (fun _ => MyNat) a.succ)

-- Now we can give a definition of `double` using the recursor:

noncomputable def double' : MyNat → MyNat :=
  MyNat.rec (motive := fun _ => MyNat) doubleZero doubleStep
  
  
-- let's use our function(s)

#reduce double' two

#reduce double two

#eval double two
-- #eval double' two


/- Now let's observe some general theorems about this recursor -/

section

variable {α : Type} 
         (a : α) 
         (g : MyNat → α → α)

-- existence: the recursor gives a solution, and the equations hold by computation
example : 
    MyNat.rec (motive := fun _ => α) a g .zero = a := 
  rfl

example (n : MyNat) :
    MyNat.rec (motive := fun _ => α) a g n.succ 
    = g n (MyNat.rec (motive := fun _ => α) a g n) := 
  rfl

-- uniqueness: any two solutions agree, by induction
theorem rec_unique (f₁ f₂ : MyNat → α)
    (hf₁ : f₁ .zero = a) (hf₁s : ∀ n, f₁ n.succ = g n (f₁ n))
    (hf₂ : f₂ .zero = a) (hf₂s : ∀ n, f₂ n.succ = g n (f₂ n)) :
    ∀ n, f₁ n = f₂ n := by
  intro n
  induction n with
  | zero => rw [hf₂, hf₁]
  | succ n ih => rw [hf₁s, hf₂s, ih]


end  -- end the `section`


-- --------------------------------------------------------------------------------


-- we can define addition for our `MyNat` type.


def add (m : MyNat) : MyNat → MyNat
  | .zero   => m
  | .succ n => .succ (add m n)

-- we are going to give a few proofs that `0 + n = n`.

-- we can use the recursor:

theorem zero_add (n : MyNat) : add .zero n = n :=
  MyNat.rec (motive := fun n => add .zero n = n)
    rfl
    (fun _ ih => congrArg MyNat.succ ih)
    n


#check congrArg

-- this essentially boils down to:

-- congrArg f : a = b → f a = f b

-- we can also use pattern matching and "recursion"

theorem zero_add' (n : MyNat) : add .zero n = n := by
  match n with
  | .zero => rfl
  | .succ n => 
      have ih : add .zero n = n :=  zero_add' n
      exact congrArg MyNat.succ ih

-- notice: `congrArg MyNat.succ ih` has type
--   .succ (add .zero n) = .succ n
-- while the goal is
--   add .zero n.succ = n.succ
-- These are definitionally equal (unfold one step of `add`), though not
-- syntactically equal, and that's all `exact` requires.

#print zero_add
#print zero_add'

-- Pattern matching lets you recurse on any smaller piece, not just
-- the predecessor (think Fibonacci). So Lean compiles it using a
-- derived recursor, `brecOn`, which carries a table of all earlier
-- values. It’s built from MyNat.rec by the same trick you use to
-- prove strong induction from ordinary induction.

-- that is what you see in `#print zero_add'`

-- finally, let's use the `induction` tactic:

theorem zero_add'' (n : MyNat) : add .zero n = n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg MyNat.succ ih

#print zero_add''  -- essentially what we wrote by hand, above.


/-!
## Why does Lean bother with recursors at all?

Why can't we just write any recursive definition?

A `def` is not just code: it's an *equation* that Lean's logic will
believe. So a "definition" had better actually define something.
-/

-- Consider this "definition":
--
--   def bad (n : Nat) : Nat := bad n + 1
--
-- If Lean accepted it, we'd have the equation `bad 0 = bad 0 + 1`,
-- and subtracting `bad 0` from both sides gives `0 = 1`.
--
-- We can simulate what would happen by *assuming* such a function as a hypothesis:

section

variable (bad : Nat → Nat) 
         (bad_eq : ∀ n, bad n = bad n + 1)
         
include bad_eq  -- this forces lean to add `bad_eq` to the context of every subsequent
                -- theorem in the section

theorem oops : False := by
  have := bad_eq 0
  omega
  -- or use: exact Nat.succ_ne_self (bad 0) (bad_eq 0).symm

#print oops

-- the output is:
-- theorem oops : ∀ (bad : Nat → Nat), (∀ (n : Nat), bad n = bad n + 1) → False :=
-- fun bad bad_eq ↦
--   have this := bad_eq 0;
--   oops._proof_1_1 bad this


#print oops._proof_1_1


-- theorem loopy : False := loopy   -- rejected: not structurally decreasing
-- Termination checking is what rules out circular proofs.


end

-- The mathematician's version: "let x be the number with x = x + 1"
-- isn't a definition, because no such x exists. A recursive
-- definition is an equation in an unknown function, and we need to
-- know it has a (unique) solution.

-- For ℕ (here: `MyNat`), that guarantee is the Recursion Theorem: for any type `α`,
-- given `a : α` and `g : MyNat → α → α`, there is a unique
-- `f : MyNat → α` with
--     f 0 = a,    f (n+1) = g n (f n).
-- Now:
-- - the existence assertion is `MyNat.rec` with a constant motive
--   (recursion);
-- - the uniqueness assertion is a proof by induction, i.e. `MyNat.rec`
--   with a Prop motive.
--
-- Lean builds this in as a primitive, and insists that every recursive
-- definition be reducible to it.

-- (`MyNat.rec` is the "dependent" version: the target type may vary
-- with `n`, i.e. 

-- `a : motive .zero` and 
-- `g : (n : MyNat) → motive n → motive n.succ`.  

-- Taking `motive n` to be a proposition `P n` -- i.e. taking `motive`
-- to be a predicate `P` - is exactly mathematical induction.)



-- ================================================================================-

/- A more complicated inductive type, still permits induction. -/

-- (binary) Trees

inductive Tree where
  | leaf : Tree 
  | node : Tree → Tree → Tree
deriving Repr, DecidableEq

-- let's make some utility functions for construction of certain kinds
-- of trees:

def leftSpine (n : Nat) : Tree := 
  match n with
  | 0 => .leaf 
  | n + 1 => .node (leftSpine n) .leaf


def rightSpine (n : Nat) : Tree :=
  match n with
  | 0 => .leaf 
  | n + 1 => .node .leaf (rightSpine n)


def fullTree (n : Nat) : Tree :=
  match n with
  | 0 => .leaf
  | n + 1 => .node (fullTree n) (fullTree n)

def ex : Tree := .node (leftSpine 2) (rightSpine 3)

#eval ex

-- output:
-- Tree.node
--   (Tree.node (Tree.node (Tree.leaf) (Tree.leaf)) (Tree.leaf))
--   (Tree.node (Tree.leaf) 
--              (Tree.node (Tree.leaf) 
--                (Tree.node (Tree.leaf) (Tree.leaf)))) 

#check @Tree.rec

-- {motive : Tree → Sort u}
--   → motive leaf
--   → ((l r : Tree) → motive l → motive r → motive (node l r))
--   → (t : Tree) → motive t

-- swap left and right everywhere
def mirror : Tree → Tree
  | .leaf => .leaf
  | .node l r => .node (mirror r) (mirror l)

example : mirror (mirror ex) = ex := by decide
example : mirror ex != ex := by decide

example : mirror (fullTree 50) = fullTree 50 := by decide

theorem mirror_mirror (t : Tree) : mirror (mirror t) = t := by
  induction t with
  | leaf => rfl
  | node l r ihl ihr => simp [mirror, ihl, ihr]


theorem mirror_left (n : Nat) : mirror (leftSpine n) = rightSpine n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [leftSpine, rightSpine, mirror, ih]

theorem mirror_fulltree (n : Nat) : mirror (fullTree n) = fullTree n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ fullTree, mirror, ih ]


def size_of (t : Tree) : Nat := 
  match t with
  | .leaf => 1
  | .node l r => (size_of l) + (size_of r) + 1

#eval size_of (fullTree 1)

theorem fullSize (n : Nat) : size_of (fullTree n) + 1 = 2 ^ (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc size_of (fullTree (n + 1)) + 1
        = (size_of (fullTree n) + 1) + (size_of (fullTree n) + 1) := by
            simp only [fullTree, size_of]; ac_rfl
      _ = 2 ^ (n + 1) + 2 ^ (n + 1) := by rw [ih]
      _ = 2 ^ (n + 1 + 1) := by omega



theorem fullSize' (n : Nat) : size_of (fullTree n) + 1 = 2^(n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [ fullTree, size_of]
                 omega
                 
