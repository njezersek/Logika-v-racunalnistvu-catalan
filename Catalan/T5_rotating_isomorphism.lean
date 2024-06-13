import Mathlib
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
open BigOperators
open Finset
open Finset.antidiagonal

inductive plane_tree : Type
| node : List plane_tree → plane_tree
deriving Repr

open plane_tree

inductive full_binary_tree : Type
| leaf : full_binary_tree
| node : full_binary_tree → full_binary_tree → full_binary_tree
deriving Repr

open full_binary_tree

def example1 : full_binary_tree :=
  node (node leaf leaf) (node leaf leaf)

def example2 : full_binary_tree :=
  node (node leaf (node leaf leaf)) (node leaf leaf)

def example_plane_tree_1 : plane_tree :=
  node [node [], node [node []]]

def example_plane_tree_2 : plane_tree :=
  node [node [node []], node [node [node []], node []]]

def blptapt_toFun : List plane_tree → plane_tree
| N => .node N

def blptapt_invFun : plane_tree → List plane_tree
| .node N => N

def fun : plane_tree → List plane_tree
.node N => N


def bijection_list_plane_tree_and_plane_tree : List plane_tree ≃ plane_tree :=
  {
    toFun := blptapt_toFun --fun N => .node N -- Function that maps from List plane tree to plane tree
    invFun := blptapt_invFun --fun (.node N) => N -- Function that maps from plane tree to List plane tree
    left_inv := by -- Proof, one direction
      intro x
      cases x
      case nil => rfl
      case cons h t => rfl,
    right_inv := by -- Proof, other direction
      intro t
      cases t
      case node N => rfl
      }

def plane_tree_to_full_binary_tree : plane_tree → full_binary_tree
| plane_tree.node [] => leaf
| plane_tree.node (c :: cs) =>
    node (plane_tree_to_full_binary_tree c)
         (plane_tree_to_full_binary_tree (node cs))

-- def full_binary_tree_to_plane_tree : full_binary_tree → plane_tree
-- | leaf => plane_tree.node []
-- | full_binary_tree.node l r =>
--     match full_binary_tree_to_plane_tree r with
--       | plane_tree.node rs => node (full_binary_tree_to_plane_tree l :: rs)

def full_binary_tree_to_plane_tree : full_binary_tree → plane_tree
| full_binary_tree.leaf => plane_tree.node []
| full_binary_tree.node l r => 
  let l' := blptapt_invFun (full_binary_tree_to_plane_tree l)
  let r' := blptapt_invFun (full_binary_tree_to_plane_tree r)
  blptapt_toFun (plane_tree.node l' :: r')
  
#eval example1
#eval full_binary_tree_to_plane_tree example1
#eval plane_tree_to_full_binary_tree (full_binary_tree_to_plane_tree example1)

#eval example2
#eval full_binary_tree_to_plane_tree example2
#eval plane_tree_to_full_binary_tree (full_binary_tree_to_plane_tree example2)


#eval example_plane_tree_1
#eval plane_tree_to_full_binary_tree example_plane_tree_1
#eval full_binary_tree_to_plane_tree (plane_tree_to_full_binary_tree example_plane_tree_1)

#eval example_plane_tree_2
#eval plane_tree_to_full_binary_tree example_plane_tree_2
#eval full_binary_tree_to_plane_tree (plane_tree_to_full_binary_tree example_plane_tree_2)








def rotating_isomorphism : plane_tree ≃ full_binary_tree :=
  { toFun := plane_tree_to_full_binary_tree,
    invFun := full_binary_tree_to_plane_tree,
    left_inv := by
      sorry
      -- intro x
      -- induction x
      -- case node xs ih =>
      --   cases xs
      --   case nil => rfl
      --   case cons h t =>
      --     simp [plane_tree_to_full_binary_tree, full_binary_tree_to_plane_tree]
      --     have h_inv := ih h
      --     have t_inv := ih (node t)
      --     rw [h_inv, t_inv],

      -- intro x
      -- induction x with
      -- | node xs ih =>
      --   cases xs
      --   case nil => rfl
      --   case cons h t =>
      --     simp [plane_tree_to_full_binary_tree, full_binary_tree_to_plane_tree]
      --     have h_inv := ih h
      --     have t_inv := ih (node t)
      --     rw [h_inv, t_inv],

      -- intro x
      -- have aux : ∀ t : plane_tree, full_binary_tree_to_plane_tree (plane_tree_to_full_binary_tree t) = t :=
      --   fun t =>
      --     match t with
      --     | node [] => rfl
      --     | node (h :: t') =>
      --       have h_inv := aux h
      --       have t_inv := aux (node t')
      --       show full_binary_tree_to_plane_tree (plane_tree_to_full_binary_tree (node (h :: t'))) = node (h :: t') from
      --         calc
      --           full_binary_tree_to_plane_tree (plane_tree_to_full_binary_tree (node (h :: t')))
      --           = full_binary_tree_to_plane_tree (full_binary_tree.node (plane_tree_to_full_binary_tree h) (plane_tree_to_full_binary_tree (node t'))) : rfl
      --           ... = node (full_binary_tree_to_plane_tree (plane_tree_to_full_binary_tree h) :: match full_binary_tree_to_plane_tree (plane_tree_to_full_binary_tree (node t')) with | node rs => rs) : rfl
      --           ... = node (full_binary_tree_to_plane_tree (plane_tree_to_full_binary_tree h) :: full_binary_tree_to_plane_tree (plane_tree_to_full_binary_tree (node t')) |>.cases_on (λ rs => rs)) : rfl
      --           ... = node (h :: t') : by rw [h_inv, t_inv]
      -- exact aux x,

    right_inv := by
      intro x
      induction x
      case leaf => 
        simp [full_binary_tree_to_plane_tree]
        simp [plane_tree_to_full_binary_tree]
      case node l r ih_l ih_r =>
        simp [full_binary_tree_to_plane_tree]
        -- simp [blptapt_invFun]
        simp [blptapt_toFun]
        simp [plane_tree_to_full_binary_tree]
        simp [blptapt_invFun]

        
        rw [ih_l, ih_r]
        }



