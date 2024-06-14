import Mathlib
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
open BigOperators
open Finset
open Finset.antidiagonal

-- THE SMALL TASKS

-- 1. formalize the recursive definition of the Catalan numbers
-- C_0 = 1, C_{n+1} = ∑_{i=0}^n C_i C_{n-i}

def my_catalan : ℕ → ℕ
| 0 => 1
| (n+1) => ∑ i : Fin (n+1), my_catalan i * my_catalan (n-i)

#eval my_catalan 3 -- returns 5


-- 2. formalize the concept of plane trees
-- a plane tree is a rooted tree where the children of each node are linearly ordered

inductive plane_tree : Type
| node : List plane_tree → plane_tree
deriving Repr

-- 3. formalize the concept of full binary trees
-- a full binary tree is a rooted tree where each node has either 0 or 2 children

inductive full_binary_tree : Type
| leaf : full_binary_tree
| node : full_binary_tree → full_binary_tree → full_binary_tree
deriving Repr

-- 4. construct the type of full binary trees with n nodes, not counting the leaves

inductive full_binary_tree_of_size : (n : ℕ) → Type
| leaf : full_binary_tree_of_size 0
| node : full_binary_tree_of_size n → full_binary_tree_of_size m → full_binary_tree_of_size (n+m+1)
deriving Repr

-- 5. define the type of ballot sequences of length n
-- a ballot sequence is a sequence of +1 and -1 such that the partial sums are always non-negative

inductive ballot : (sum n : ℕ ) → Type
| nil : ballot 0 0
| plus : ballot sum n → ballot (sum+1) (n+1)
| minus : ballot (sum_pred+1) n → ballot (sum_pred) (n+1)

#check (ballot.minus (ballot.plus (ballot.plus ballot.nil))) --   plus, plus, minus OK
-- #check (ballot.minus (ballot.minus (ballot.minus ballot.nil))) --   minus, minus, minus  NOT OK





-- functions from lab exercises

-- inductive binary_tree : Type
-- | leaf : binary_tree
-- | node₁ : binary_tree → binary_tree
-- | node₂ : binary_tree → binary_tree → binary_tree

-- def binary_tree.height : binary_tree → ℕ
-- | .leaf => 1
-- | (binary_tree.node₁ t) => 1 + t.height
-- | (binary_tree.node₂ t₁ t₂) => 1 + max t₁.height t₂.height

-- def binary_tree.number_of_nodes : binary_tree → ℕ
-- | .leaf => 1
-- | (binary_tree.node₁ t) => 1 + t.number_of_nodes
-- | (binary_tree.node₂ t₁ t₂) => 1 + t₁.number_of_nodes + t₂.number_of_nodes

-- def full_binary_tree.height : full_binary_tree → ℕ
-- | .leaf => 1
-- | (full_binary_tree.node t₁ t₂) => 1 + max t₁.height t₂.height

-- def full_binary_tree.number_of_nodes : full_binary_tree → ℕ
-- | .leaf => 1
-- | (full_binary_tree.node t₁ t₂) => 1 + t₁.number_of_nodes + t₂.number_of_nodes

-- def binary_tree_of_full_binary_tree : full_binary_tree → binary_tree
-- | full_binary_tree.leaf => binary_tree.leaf
-- | (full_binary_tree.node t₁ t₂) => binary_tree.node₂ (binary_tree_of_full_binary_tree t₁) (binary_tree_of_full_binary_tree t₂)

-- theorem full_binary_tree_height_eq_binary_tree_of_full_binary_tree :
--   (T : full_binary_tree) →
--   T.height = (binary_tree_of_full_binary_tree T).height := by
-- intro T
-- induction T with
-- | leaf => rfl
-- | node t₁ t₂ ih₁ ih₂ =>
--   simp [full_binary_tree.height, binary_tree.height]
--   rw [ih₁, ih₂]

-- theorem full_binary_tree_no_nodes_eq_binary_tree_of_full_binary_tree :
--   (T : full_binary_tree) →
--   T.number_of_nodes = (binary_tree_of_full_binary_tree T).number_of_nodes := by
--   intro T
--   induction T with
--   | leaf => rfl
--   | node t₁ t₂ ih₁ ih₂ =>
--     simp [full_binary_tree.number_of_nodes, binary_tree.number_of_nodes]
--     rw [ih₁, ih₂]

-- inductive binary_tree_with_nodes : (n : ℕ) → Type
-- | leaf : binary_tree_with_nodes 1
-- | node₁ : binary_tree_with_nodes n → binary_tree_with_nodes (n+1)
-- | node₂ : binary_tree_with_nodes n → binary_tree_with_nodes m → binary_tree_with_nodes (n+m+1)


-- inductive vector (A : Type) : (n : ℕ) → Type
-- | nil : vector A 0
-- | cons : vector A n → vector A (n+1)

-- def vector.length {A : Type} : (n : ℕ) → vector A n → ℕ
-- | n, _ => n

-- def my_vector : vector ℕ 2 :=
--   vector.cons ( vector.cons ( vector.nil ))


-- def plane_tree_to_full_binary_tree : plane_tree → full_binary_tree
-- | (plane_tree.node []) => full_binary_tree.leaf
-- -- | (plane_tree.node []) => full_binary_tree.node  (full_binary_tree.leaf) (full_binary_tree.leaf) ????????
-- | (plane_tree.node (T::l)) => full_binary_tree.node (plane_tree_to_full_binary_tree T) (plane_tree_to_full_binary_tree (plane_tree.node l))

-- def full_binary_tree_to_plane_tree : full_binary_tree → plane_tree
-- | full_binary_tree.leaf => plane_tree.node []
-- | (full_binary_tree.node T₁ T₂) => plane_tree.node [full_binary_tree_to_plane_tree T₁, full_binary_tree_to_plane_tree T₂]
