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


-- 3. formalize the concept of full binary trees
-- a full binary tree is a rooted tree where each node has either 0 or 2 children

inductive full_binary_tree : Type
| leaf : full_binary_tree
| node : full_binary_tree → full_binary_tree → full_binary_tree


-- 4. construct the type of full binary trees with n nodes, not counting the leaves

inductive full_binary_tree_of_size : (n : ℕ) → Type
| leaf : full_binary_tree_of_size 0
| node : full_binary_tree_of_size n → full_binary_tree_of_size m → full_binary_tree_of_size (n+m+1)


-- 5. define the type of ballot sequences of length n
-- a ballot sequence is a sequence of +1 and -1 such that the partial sums are always non-negative

inductive ballot : (sum n : ℕ ) → Type
| nil : ballot 0 0
| plus : ballot sum n → ballot (sum+1) (n+1)
| minus : ballot (sum_pred+1) n → ballot (sum_pred) (n+1)

#check (ballot.minus (ballot.plus (ballot.plus ballot.nil))) --   plus, plus, minus OK
-- #check (ballot.minus (ballot.minus (ballot.minus ballot.nil))) --   minus, minus, minus  NOT OK


-- THE BIG TASKS

-- 1. construct a bijection
-- Fin ( ∑_{i < n} k_i ) ≃ Σ_{i: Fin n} Fin k_i
-- for every k: Fin n -> ℕ

-- 2. construct a bijection
-- Fin C_{n+1} ≃ Σ_{i=0}^n (Fin C_i) × (Fin C_{n-i})

-- 3. construct a bijection between full binary trees (with n nodes) and the type Fin C_n

-- 7. prove that C_n = 1/(n+1) * (2n choose n)

theorem catalan_alt (n : ℕ) : my_catalan n * (n+1) = Nat.choose (2*n) n := by
sorry

-- 8. construct an isomorphism Fin C_n ≃ DyckPath 2n

-- dyck path of length
inductive dyck_path : (sum len : ℕ) → Type
| nil : dyck_path 0 0
| up : dyck_path sum len → dyck_path (sum+1) (len+1)
| down : dyck_path (sum+1) len → dyck_path sum (len+1)

-- example : dyck_path 0 4 := (dyck_path.down (dyck_path.down (dyck_path.up (dyck_path.up dyck_path.nil)))) -- OK
-- example : dyck_path 0 4 := (dyck_path.up (dyck_path.down (dyck_path.up (dyck_path.up dyck_path.nil)))) -- NOT OK


example (n : ℕ) : Fin 1 ≃ dyck_path 0 0 := by
  let fwd : Fin 1 → dyck_path 0 0 := fun i => dyck_path.nil
  let bwd : dyck_path 0 0 → Fin 1 := fun i => 0
  apply Equiv.mk fwd bwd
  intro p


example (n : ℕ) : Fin 1 ≃ Fin 1 := by
  let fwd : Fin 1 → Fin 1 := fun i => i
  let bwd : Fin 1 → Fin 1 := fun i => i
  apply Equiv.mk fwd bwd
  intro




theorem catalan_dyck (n : ℕ) : Fin (my_catalan n) ≃ dyck_path 0 (2*n) := by
  induction n with
  | zero =>
    simp
    rw [my_catalan]
    let fwd : Fin 1 → dyck_path 0 0 := fun i => dyck_path.nil
    let bwd : dyck_path 0 0 → Fin 1 := fun i => ⟨0, Nat.zero_lt_succ 0⟩
    apply Equiv.mk fwd bwd




--
-- EXAMPLE proof of equivalence between Bool and Fin 2
--
def bool_to_fin (b : Bool) : Fin 2 := if b then 1 else 0
def fin_to_bool (i : Fin 2) : Bool := i.val == 1

#eval bool_to_fin true -- returns 1
#eval fin_to_bool 1 -- returns true

example : Bool ≃ Fin 2 := by
  -- construct the equivalence
  apply Equiv.mk bool_to_fin fin_to_bool
  {
    intro b
    rw[bool_to_fin]
    rw[fin_to_bool]
    cases b with
    | false => simp
    | true => simp
  }
  {
    intro n
    rw[fin_to_bool]
    rw[bool_to_fin]
    fin_cases n
    repeat simp
  }
