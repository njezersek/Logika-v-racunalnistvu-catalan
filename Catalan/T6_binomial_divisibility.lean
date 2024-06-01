import Mathlib
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import «Catalan».Tasks -- import the smaller tasks
open BigOperators
open Finset
open Finset.antidiagonal

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
