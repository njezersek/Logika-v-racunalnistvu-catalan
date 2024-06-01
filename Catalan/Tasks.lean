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



-- 6. prove that C(2n, n) is divisible by (n+1) for every n

theorem n_factorial_n_dec_eq_factorial_n (n : ℕ) (h : 0 < n) : n * Nat.factorial (n - 1) = Nat.factorial n := by
  induction n with
  | zero => contradiction
  | succ =>
    rw [Nat.succ_sub_one]
    rw [Nat.factorial_succ]

theorem n_eq_2n_minus_n (n : ℕ) : n = 2*n - n := by
  rw [Nat.two_mul]
  rw [Nat.add_sub_cancel]

theorem eq_from_catalan_def (n : ℕ) (h : 0 < n): (n+1) * Nat.choose (2*n) (n+1) = n * Nat.choose (2*n) n := by
  have h2 : 0 < Nat.factorial (n+1) * Nat.factorial (2*n - (n+1)) := by
    apply Nat.mul_pos
    exact Nat.factorial_pos (n+1)
    exact Nat.factorial_pos (2*n - (n+1))
  -- multiply both sides by (n+1)! (2n-(n+1))!
  apply Nat.eq_of_mul_eq_mul_right h2
  nth_rw 1 [Nat.mul_assoc]
  nth_rw 2 [← Nat.mul_assoc]
  -- expand binomial by definition
  rw [Nat.choose_mul_factorial_mul_factorial]
  -- simplify 2n - (n+1) = n-1
  nth_rw 3 [Nat.two_mul]
  rw [Nat.add_sub_add_left]
  -- expand (n+1)! = (n+1) n!
  rw [Nat.factorial_succ]
  -- rearange the equation to cancel (n+1)
  nth_rw 3 [Nat.mul_comm]
  rw [Nat.mul_assoc]
  rw [Nat.mul_assoc]
  rw [Nat.mul_right_inj] -- cancel (n+1) on both sides
  -- apply equality n (n-1)! = n!
  nth_rw 2 [← Nat.mul_assoc]
  nth_rw 4 [Nat.mul_comm ]
  rw [n_factorial_n_dec_eq_factorial_n]
  -- transform the right side to (choose 2n n) n! n!
  rw [← Nat.mul_assoc]
  nth_rw 2 [Nat.mul_comm]
  -- transform the last factorial from n! to (2n-n)!
  nth_rw 5 [n_eq_2n_minus_n n]
  rw [← Nat.mul_assoc]
  rw [Nat.choose_mul_factorial_mul_factorial]
  -- finsih remaining goals (inequalities)
  rw [Nat.two_mul]
  apply Nat.le_add_right
  exact h
  rw[Nat.add_one]
  apply Nat.succ_ne_zero
  omega

-- get from not n = 0 to 0 < n
theorem not_eq_zero_imp_zero_ge (n : ℕ) : ¬ n = 0 → 0 < n := by
  intro h
  cases n with
  | zero => contradiction
  | succ m => exact Nat.zero_lt_succ m

theorem choose_eq (n : ℕ) : Nat.choose (2*n) n = (n+1) * (Nat.choose (2*n) n - Nat.choose (2*n) (n+1)) := by
  by_cases h : n = 0
  case pos =>
    rw[h]
    rw[Nat.choose_zero_right]
    rw[Nat.one_eq_succ_zero]
    rw[Nat.choose_zero_succ]
  case neg =>
    have h2 : 0 < n := not_eq_zero_imp_zero_ge n h -- we need the 0 < n to multiply both sides by n
    apply Nat.eq_of_mul_eq_mul_left h2 -- multipyl both sides by n
    rw [← Nat.mul_assoc]
    nth_rw 2 [Nat.mul_comm n]
    rw [Nat.mul_sub_left_distrib]
    rw [Nat.mul_assoc]
    nth_rw 2 [← eq_from_catalan_def]
    rw [Nat.mul_assoc]
    rw [← Nat.mul_sub_left_distrib]
    rw [← Nat.mul_sub_right_distrib]
    rw [Nat.add_comm, Nat.add_sub_cancel, Nat.one_mul, Nat.add_comm]
    rw [eq_from_catalan_def n]
    repeat exact h2

theorem choose_2n_n_divisible_by_n_plus_1 (n : ℕ) : (n+1) ∣ Nat.choose (2*n) n := by
  rw [choose_eq]
  apply dvd_mul_right
