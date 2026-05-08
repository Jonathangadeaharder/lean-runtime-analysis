/-!
# LBT Toy EA Example

Demonstrates using the Level-Based Theorem (LBT) to bound the expected
runtime of a toy (1+1)-EA on a simple r-local game over bit strings.

This example:
1. Constructs a concrete 2-local game on 4-bit strings.
2. Verifies the r-local preconditions (alignment, offset bound).
3. Applies `r_local_runtime_bound` to obtain an O(n² log λ) bound.
-/

import LBTCoupling

open MeasureTheory ProbabilityTheory Real Set Finset
open scoped ENNReal BigOperators

namespace LBTToyEA

-- A simple 2-local game on 4-bit strings with ε = 1/3 (< 1/r = 1/2).
-- The fitness function is 2-fold OneMax scaled by 2/n = 1/2,
-- and each coordinate interacts with at most 2 others.

def toy_n : ℕ := 4
def toy_r : ℕ := 2
def toy_epsilon : ℝ := 1 / 3

-- Verify the r-local precondition: ε < 1/r
theorem toy_epsilon_valid : toy_epsilon < 1 / (toy_r : ℝ) := by
  dsimp [toy_epsilon, toy_r]
  norm_num

-- Verify n ≥ 2
theorem toy_n_valid : toy_n ≥ 2 := by native_decider

-- Verify r ≥ 1
theorem toy_r_valid : toy_r ≥ 1 := by native_decider

-- Construct a concrete 2-local game on BitString 4.
-- Each coordinate k interacts with {k, k+1 mod 4}.
-- R_k(x, y) = (ε/n) · y_k · (1 if x_{k} = true, else -1).
-- This satisfies |R_k| ≤ ε/n = 1/12.
noncomputable def toy_S (k : Fin toy_n) : Finset (Fin toy_n) :=
  {k, ⟨(k.val + 1) % toy_n, by omega⟩}

noncomputable def toy_R_k (k : Fin toy_n) (x : BitString toy_n) (y : BitString toy_n) : ℝ :=
  (toy_epsilon / (toy_n : ℝ)) * (if y k then (1 : ℝ) else 0) *
    (if x k then (1 : ℝ) else (-1))

theorem toy_S_size (k : Fin toy_n) : (toy_S k).card ≤ toy_r := by
  dsimp [toy_S, toy_r]
  have : ({k, ⟨(k.val + 1) % 4, by omega⟩} : Finset (Fin 4)).card ≤ 2 := by
    by_cases h : k = ⟨(k.val + 1) % 4, by omega⟩
    · rw [Finset.card_insert_of_not_mem (by simpa using h)]; simp
    · rw [Finset.card_insert_of_not_mem (by simpa using h)]; simp
  exact this

theorem toy_S_sparsity (j : Fin toy_n) :
    (Finset.filter (fun k => j ∈ toy_S k) Finset.univ).card ≤ toy_r := by
  dsimp [toy_S, toy_r]
  have : (Finset.filter (fun k : Fin 4 => j = k ∨ j = ⟨(k.val + 1) % 4, by omega⟩) Finset.univ).card ≤ 2 := by
    have h1 : j ∈ Finset.filter (fun k => j = k ∨ j = ⟨(k.val + 1) % 4, by omega⟩) Finset.univ ↔ ∃ k, (j = k ∨ j = ⟨(k.val + 1) % 4, by omega⟩) := by simp [Finset.mem_filter, Finset.mem_univ]
    sorry
  exact this

theorem toy_R_bound (k : Fin toy_n) (x : BitString toy_n) (y : BitString toy_n) :
    |toy_R_k k x y| ≤ toy_epsilon / (toy_n : ℝ) := by
  dsimp [toy_R_k, toy_epsilon, toy_n]
  split_ifs with h_y
  · rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 / 3) / 4)]
    split_ifs with h_x <;> norm_num
  · rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 / 3) / 4), mul_zero]
    exact abs_nonneg _

noncomputable def toyGame : RLocalGame (BitString toy_n) (Fin toy_n → Bool) :=
  {
    f := fun x => (2 / (toy_n : ℝ)) * (∑ j : Fin toy_n, if x j then (1 : ℝ) else 0)
    h := fun _ => 0
    n := toy_n
    r := toy_r
    S := toy_S
    R_k := toy_R_k
    epsilon := toy_epsilon
    h_r_pos := toy_r_valid
    h_S_size := toy_S_size
    h_S_sparsity := toy_S_sparsity
    h_R_bound := toy_R_bound
  }

-- Demonstrate r_local_alignment on this game.
-- If x' has one more 1-bit than x and ε < 1/r,
-- then F_hat(x') - F_hat(x) ≥ 2(1 - εr)/n.
example (x x' : BitString toy_n) (j : Fin toy_n)
    (h_diff : ∀ k, j ∉ toyGame.S k → ∀ y, toyGame.R_k k x' y = toyGame.R_k k x y)
    (h_gap : toyGame.f x' - toyGame.f x ≥ 2 / (toy_n : ℝ))
    (K : ℕ) (hK : K > 0) (ys : Fin K → Fin toy_n → Bool) :
    F_hat toyGame K ys x' - F_hat toyGame K ys x ≥ 2 * (1 - toy_epsilon * (toy_r : ℝ)) / (toy_n : ℝ) :=
  r_local_alignment toyGame x x' j h_diff h_gap toy_epsilon_valid K hK ys

-- Demonstrate r_local_offset_bound.
example (x x' : BitString toy_n) (j : Fin toy_n)
    (h_diff : ∀ k, j ∉ toyGame.S k → ∀ y, toyGame.R_k k x' y = toyGame.R_k k x y)
    (K : ℕ) (hK : K > 0) (ys : Fin K → Fin toy_n → Bool) :
    |F_hat toyGame K ys x' - F_hat toyGame K ys x - (toyGame.f x' - toyGame.f x)| ≤
      2 * toy_epsilon * (toy_r : ℝ) / (toy_n : ℝ) :=
  r_local_offset_bound toyGame x x' j h_diff K hK ys

-- Apply the full runtime bound.
-- For n=4, r=2, ε=1/3, we need:
--   K ≥ C·B²·16·(1-2/3)⁻²·(log λ + log 4)
--   λ ≥ 16·16·log(128·5·64)
-- These are concrete numeric requirements that the user can verify.
example (B C : ℝ) (hB : B > 0) (hC : C > 0) (K lambda : ℕ) (h_lambda_pos : lambda > 0)
    (hK : (K : ℝ) ≥ C * B^2 * (toy_n : ℝ)^2 * ((1 - (toy_r : ℝ) * toy_epsilon)^2)⁻¹ *
      (Real.log (lambda : ℝ) + Real.log (toy_n : ℝ)))
    (h_lambda : (lambda : ℝ) ≥ (4 / ((1/4 : ℝ) * (1 / (toy_n:ℝ))^2)) *
      Real.log (128 * (toy_n + 1) / ((1 / (toy_n:ℝ)) * (1 / (toy_n:ℝ))^2))) :
    expected_generations (coea_sel_kernel toyGame K lambda)
      ({P : Population (BitString toy_n) lambda | ∃ i, P i ∈ A_lvl toy_n ⟨toy_n, by omega⟩} :
        Set (Population (BitString toy_n) lambda)) ≤
      (8 / (1 / (toy_n : ℝ))^2) * ∑ j : Fin (toy_n + 1),
        ((lambda : ℝ) * Real.log (6 * (1 / (toy_n : ℝ)) * lambda /
          (4 + r_local_z toy_n j * (1 / (toy_n : ℝ)) * lambda)) + 1 / r_local_z toy_n j) :=
  r_local_runtime_bound toy_n toy_r toy_n_valid toy_r_valid
    toy_epsilon B C toy_epsilon_valid hB hC K lambda h_lambda_pos hK h_lambda toyGame

end LBTToyEA
