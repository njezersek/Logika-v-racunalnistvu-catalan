import Mathlib
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic

inductive plane_tree : Type
| node : List plane_tree → plane_tree

def bijection_list_plane_tree_and_plane_tree : List plane_tree ≃ plane_tree :=
  {
    toFun := fun N => .node N -- Function that maps from List plane tree to plane tree
    invFun := fun (.node N) => N -- Function that maps from plane tree to List plane tree
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
