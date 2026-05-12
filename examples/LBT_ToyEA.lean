import LBTCoupling

/-!
# LBT Toy EA Example

Demonstrates using the Level-Based Theorem (LBT) to bound the expected
runtime of a toy (1+1)-EA on a simple r-local game over bit strings.

This example:
1. Constructs a concrete r-local game on 4-bit strings.
2. Verifies the r-local preconditions (alignment, offset bound).
3. Applies `r_local_runtime_bound` to obtain an O(n² log λ) bound.
-/

open MeasureTheory ProbabilityTheory Real Set Finset
open scoped ENNReal BigOperators

namespace LBTToyEA

-- A simple r-local game on 4-bit strings with ε = 1/3 < 1/2 = 1/r.
-- Each coordinate interacts only with itself (S_k = ∅).
-- This is the simplest valid r-local game: all residuals are zero.

noncomputable def toyGame : RLocalGame (BitString 4) (Fin 4 → Bool) :=
  {
    f := fun x => (2 / 4) * (∑ j : Fin 4, if x j then (1 : ℝ) else 0)
    h := fun _ => 0
    n := 4
    r := 2
    S := fun _ => ∅
    R_k := fun _ _ _ => 0
    epsilon := 1 / 3
    h_r_pos := by omega
    h_S_size := fun _ => by simp
    h_S_sparsity := fun j => by simp [Finset.notMem_empty, Finset.filter_false]
    h_R_bound := fun _ _ _ => by rw [abs_zero]; exact div_nonneg (by norm_num) (by norm_num)
  }

theorem toy_epsilon_valid : (1 / 3 : ℝ) < 1 / (2 : ℝ) := by norm_num

-- Demonstrate r_local_alignment: F̂(x') - F̂(x) ≥ 2(1 - εr)/n
-- when f(x') - f(x) ≥ 2/n and ε < 1/r.
example (x x' : BitString 4) (j : Fin 4)
    (h_diff : ∀ k, j ∉ toyGame.S k → ∀ y, toyGame.R_k k x' y = toyGame.R_k k x y)
    (h_gap : toyGame.f x' - toyGame.f x ≥ 2 / 4)
    (K : ℕ) (hK : K > 0) (ys : Fin K → Fin 4 → Bool) :
    F_hat toyGame K ys x' - F_hat toyGame K ys x ≥ 2 * (1 - (1 / 3) * 2) / 4 :=
  r_local_alignment toyGame x x' j h_diff h_gap toy_epsilon_valid K hK ys

-- Demonstrate r_local_offset_bound: |F̂(x') - F̂(x) - (f(x') - f(x))| ≤ 2εr/n.
example (x x' : BitString 4) (j : Fin 4)
    (h_diff : ∀ k, j ∉ toyGame.S k → ∀ y, toyGame.R_k k x' y = toyGame.R_k k x y)
    (K : ℕ) (hK : K > 0) (ys : Fin K → Fin 4 → Bool) :
    |F_hat toyGame K ys x' - F_hat toyGame K ys x - (toyGame.f x' - toyGame.f x)| ≤
      2 * (1 / 3) * 2 / 4 :=
  r_local_offset_bound toyGame x x' j h_diff K hK ys

-- Apply the full runtime bound (Theorem 8).
-- For n=4, r=2, ε=1/3, the population and batch requirements are:
--   K ≥ C·B²·16·(1-2/3)⁻²·(log λ + log 4)
--   λ ≥ 16·16·log(128·5·64)
example (B C : ℝ) (hB : B > 0) (hC : C > 0) (K lambda : ℕ) (h_lambda_pos : lambda > 0)
    (hK : (K : ℝ) ≥ C * B^2 * (4 : ℝ)^2 * ((1 - (2 : ℝ) * (1 / 3 : ℝ))^2)⁻¹ *
      (Real.log (lambda : ℝ) + Real.log 4))
    (h_lambda : (lambda : ℝ) ≥ (4 / ((1/4 : ℝ) * (1 / (4 : ℝ))^2)) *
      Real.log (128 * (4 + 1) / ((1 / (4 : ℝ)) * (1 / (4 : ℝ))^2))) :
    expected_generations (coea_sel_kernel toyGame K lambda)
      ({P : Population (BitString 4) lambda | ∃ i, P i ∈ A_lvl 4 ⟨4, by omega⟩} :
        Set (Population (BitString 4) lambda)) ≤
      (8 / (1 / (4 : ℝ))^2) * ∑ j : Fin 5,
        ((lambda : ℝ) * Real.log (6 * (1 / (4 : ℝ)) * lambda /
          (4 + r_local_z 4 j * (1 / (4 : ℝ)) * lambda)) + 1 / r_local_z 4 j) :=
  r_local_runtime_bound 4 2 (by omega) (by omega)
    (1 / 3) B C toy_epsilon_valid hB hC K lambda h_lambda_pos hK h_lambda toyGame

end LBTToyEA
