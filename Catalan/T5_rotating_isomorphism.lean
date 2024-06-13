import Mathlib

-- plane trees definition
inductive plane_tree : Type
| node : List plane_tree → plane_tree
deriving Repr

open plane_tree

-- full binary trees definition
inductive full_binary_tree : Type
| leaf : full_binary_tree
| node : full_binary_tree → full_binary_tree → full_binary_tree
deriving Repr

open full_binary_tree
      
def blptpt_toFun : List plane_tree → plane_tree -- T4 bijection list plane trees and plane trees (blptpt) toFun
| N => .node N

def blptpt_invFun : plane_tree → List plane_tree -- T4 bijection list plane trees and plane trees (blptpt) invFun
| .node N => N

-- function from plane trees to full binary trees
def plane_tree_to_full_binary_tree : plane_tree → full_binary_tree
| plane_tree.node [] => leaf
| plane_tree.node (c :: cs) =>
    node (plane_tree_to_full_binary_tree c)
         (plane_tree_to_full_binary_tree (node cs))

-- function from full binary trees to plane trees
def full_binary_tree_to_plane_tree : full_binary_tree → plane_tree
| full_binary_tree.leaf => plane_tree.node []
| full_binary_tree.node l r => 
  let l' := blptpt_invFun (full_binary_tree_to_plane_tree l)
  let r' := blptpt_invFun (full_binary_tree_to_plane_tree r)
  blptpt_toFun (plane_tree.node l' :: r')

theorem left_inverse : ∀ (t : plane_tree), full_binary_tree_to_plane_tree (plane_tree_to_full_binary_tree t) = t := by
  rintro ⟨⟨ ⟩ | ⟨t, l⟩⟩

  -- case plane_tree.node []
  { simp [plane_tree_to_full_binary_tree]
    simp [full_binary_tree_to_plane_tree]
    } 

  -- case plane_tree.node (t :: l)
  { simp [plane_tree_to_full_binary_tree]
    simp [full_binary_tree_to_plane_tree]
    simp [blptpt_toFun]

    rw [left_inverse, left_inverse] -- recursive call on subproblems
    match t with
    | plane_tree.node l => 
      simp [blptpt_invFun]
  }

lemma helper_right_inv : plane_tree.node (blptpt_invFun (full_binary_tree_to_plane_tree t)) = (full_binary_tree_to_plane_tree t) := by  
  induction t
  case leaf => rfl
  case node l r _ _ =>
    simp [full_binary_tree_to_plane_tree]
    rw [blptpt_toFun]
    rfl

theorem right_inverse : ∀ (t : full_binary_tree), plane_tree_to_full_binary_tree (full_binary_tree_to_plane_tree t) = t := by
  intro x
  induction x
  case leaf => 
    simp [full_binary_tree_to_plane_tree]
    simp [plane_tree_to_full_binary_tree]
  case node l r ih_l ih_r =>
    simp [full_binary_tree_to_plane_tree]
    simp [blptpt_toFun]
    simp [plane_tree_to_full_binary_tree]
    rw [helper_right_inv, helper_right_inv]
    rw [ih_l, ih_r]
    simp  

def rotating_isomorphism : plane_tree ≃ full_binary_tree :=
  { toFun := plane_tree_to_full_binary_tree,
    invFun := full_binary_tree_to_plane_tree,
    left_inv := left_inverse,
    right_inv := right_inverse
  }
