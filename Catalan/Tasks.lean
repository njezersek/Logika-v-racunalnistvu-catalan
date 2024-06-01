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
