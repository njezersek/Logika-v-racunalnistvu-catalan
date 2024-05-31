import Mathlib
import Mathlib.Data.Set.Basic
open BigOperators
open Finset
open Finset.antidiagonal

#eval 1 + 1

inductive binary_tree : Type
| leaf : binary_tree
| node₁ : binary_tree → binary_tree
| node₂ : binary_tree → binary_tree → binary_tree

def binary_tree.height : binary_tree → ℕ
| .leaf => 1
| (binary_tree.node₁ t) => 1 + t.height
| (binary_tree.node₂ t₁ t₂) => 1 + max t₁.height t₂.height

def binary_tree.number_of_nodes : binary_tree → ℕ
| .leaf => 1
| (binary_tree.node₁ t) => 1 + t.number_of_nodes
| (binary_tree.node₂ t₁ t₂) => 1 + t₁.number_of_nodes + t₂.number_of_nodes

inductive full_binary_tree : Type
| leaf : full_binary_tree
| node : full_binary_tree → full_binary_tree → full_binary_tree

def full_binary_tree.height : full_binary_tree → ℕ
| .leaf => 1
| (full_binary_tree.node t₁ t₂) => 1 + max t₁.height t₂.height

def full_binary_tree.number_of_nodes : full_binary_tree → ℕ
| .leaf => 1
| (full_binary_tree.node t₁ t₂) => 1 + t₁.number_of_nodes + t₂.number_of_nodes

def binary_tree_of_full_binary_tree : full_binary_tree → binary_tree
| full_binary_tree.leaf => binary_tree.leaf
| (full_binary_tree.node t₁ t₂) => binary_tree.node₂ (binary_tree_of_full_binary_tree t₁) (binary_tree_of_full_binary_tree t₂)


theorem full_binary_tree_height_eq_binary_tree_of_full_binary_tree :
  (T : full_binary_tree) →
  T.height = (binary_tree_of_full_binary_tree T).height := by
intro T
induction T with
| leaf => rfl
| node t₁ t₂ ih₁ ih₂ =>
  simp [full_binary_tree.height, binary_tree.height]
  rw [ih₁, ih₂]

theorem full_binary_tree_no_nodes_eq_binary_tree_of_full_binary_tree :
  (T : full_binary_tree) →
  T.number_of_nodes = (binary_tree_of_full_binary_tree T).number_of_nodes := by
  intro T
  induction T with
  | leaf => rfl
  | node t₁ t₂ ih₁ ih₂ =>
    simp [full_binary_tree.number_of_nodes, binary_tree.number_of_nodes]
    rw [ih₁, ih₂]

inductive binary_tree_with_nodes : (n : ℕ) → Type
| leaf : binary_tree_with_nodes 1
| node₁ : binary_tree_with_nodes n → binary_tree_with_nodes (n+1)
| node₂ : binary_tree_with_nodes n → binary_tree_with_nodes m → binary_tree_with_nodes (n+m+1)


inductive vector (A : Type) : (n : ℕ) → Type
| nil : vector A 0
| cons : vector A n → vector A (n+1)

def vector.length {A : Type} : (n : ℕ) → vector A n → ℕ
| n, _ => n

def my_vector : vector ℕ 2 :=
  vector.cons ( vector.cons ( vector.nil ))

#eval my_vector.length


-- The type of full binary trees

inductive plane_tree : Type
| node : List plane_tree → plane_tree

-- -- plane tree ≅ list plane tree
-- theorem plane_tree_to_list_plane_tree : ∀ (t : plane_tree), ∃ (l : List plane_tree) , t = plane_tree.node l := by
--   intro t
--   cases t
--   apply Exists.intro
--   apply rfl

-- -- list A ≅ 1 + A × list A

-- -- abstraktni način
-- -- plane_tree ≅ 1 + plane_tree × list plane_tree
-- --            ≅ 1 + plane_tree ^ 2
-- -- X |-> 1 + X^2
-- -- bin_tree ≅ 1 + bin_tree^2


-- drug način
-- from plain trees to full binary trees direction(other direction similar)
-- | node nil => leaf
-- | node (T::l) =>

def plane_tree_to_full_binary_tree : plane_tree → full_binary_tree
| (plane_tree.node []) => full_binary_tree.leaf
-- | (plane_tree.node []) => full_binary_tree.node  (full_binary_tree.leaf) (full_binary_tree.leaf) ????????
| (plane_tree.node (T::l)) => full_binary_tree.node (plane_tree_to_full_binary_tree T) (plane_tree_to_full_binary_tree (plane_tree.node l))

def full_binary_tree_to_plane_tree : full_binary_tree → plane_tree
| full_binary_tree.leaf => plane_tree.node []
| (full_binary_tree.node T₁ T₂) => plane_tree.node [full_binary_tree_to_plane_tree T₁, full_binary_tree_to_plane_tree T₂]



-- Catalan numbers
-- C_0 = 1
-- C_{n+1} = Σ_{i=0}^{n} C_i * C_{n-i}

def my_catalan : ℕ → ℕ
| 0 => 1
| (n+1) => ∑ i : Fin (n+1), my_catalan i * my_catalan (n-i)

#eval my_catalan 3


-- The finite set of all full binary trees with n nodes
-- def FBSn : ℕ → finset full_binary_tree :=
def S : Set ℕ := {n : ℕ | n ≤ 4}
def FBS : Set full_binary_tree := {T : full_binary_tree | T.number_of_nodes ≤ 4}
#check S
