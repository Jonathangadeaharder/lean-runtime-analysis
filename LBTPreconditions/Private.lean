import Mathlib.Probability.Kernel.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Probability.Process.HittingTime

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Classical

/-!
# LBT Private Helpers

Internal definitions used by the Level-Based Theorem preconditions.
These are implementation details; the public API is in `LBTPreconditions.lean`.
-/

namespace LBT.Private

variable {X : Type} [Fintype X] [Nonempty X] [MeasurableSpace X] [DiscreteMeasurableSpace X]
variable {m : ℕ} (hm : m > 0)
variable (lambda_pop : ℕ) (h_lambda : lambda_pop > 0)
variable (A : Fin m → Set X)

def A_geq (j : Fin m) : Set X :=
  ⋃ (k : Fin m) (_ : k.val ≥ j.val), A k

abbrev Population (X : Type) (lambda_pop : ℕ) := Fin lambda_pop → X

noncomputable def pop_count (P : Population X lambda_pop) (S : Set X) : ℕ :=
  (Finset.univ.filter (fun i => P i ∈ S)).card

end LBT.Private
