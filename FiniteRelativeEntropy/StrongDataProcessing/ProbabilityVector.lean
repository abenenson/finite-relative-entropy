/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import FiniteRelativeEntropy.Basic
public import FiniteMarkovKernels.DobrushinCoefficient
public import FiniteRelativeEntropy.StrongDataProcessing.FiniteDivergence

/-!
# Strong KL contraction on finite probability vectors

Applying a stochastic kernel to both laws preserves admissibility. Its existing maximum
pairwise row total variation bounds the relative entropy of the resulting pair.
-/

@[expose] public section

open FiniteMarkovKernels InformationTheory
open scoped BigOperators

namespace FiniteRelativeEntropy

open StrongDataProcessing

variable {A B : Type*} [Fintype A] [Fintype B]

/-- Apply the same stochastic kernel to both probability vectors. A zero output
reference mass forces each contributing reference-row product to vanish. -/
noncomputable def AdmissiblePair.mapKernel (pair : AdmissiblePair A)
    (kernel : FiniteMarkovKernel A B) : AdmissiblePair B where
  numerator := kernel.apply pair.numerator
  reference := kernel.apply pair.reference
  absolutelyContinuous := by
    intro b hb
    change (∑ a, pair.reference a * kernel a b) = 0 at hb
    change (∑ a, pair.numerator a * kernel a b) = 0
    have hproducts := (Fintype.sum_eq_zero_iff_of_nonneg
      fun a ↦ mul_nonneg (pair.reference.nonneg a) ((kernel a).nonneg b)).mp hb
    exact Finset.sum_eq_zero fun a _ ↦ mul_eq_zero.mpr
      ((mul_eq_zero.mp (congrFun hproducts a)).imp (pair.absolutelyContinuous a) id)

/-- Output KL is at most the maximal pairwise row total variation times input KL,
including for admissible pairs on the simplex boundary. -/
theorem finiteKL.applyKernel_le_rowContractionCoefficient (pair : AdmissiblePair A)
    (kernel : FiniteMarkovKernel A B) :
    finiteKL (pair.mapKernel kernel) ≤ kernel.rowContractionCoefficient * finiteKL pair := by
  rw [finiteKL.eq_sum_klFun (pair.mapKernel kernel), finiteKL.eq_sum_klFun pair]
  let output := pair.mapKernel kernel
  refine FiniteDivergence.of_centered_hinges klFun convexOn_klFun klFun_one
    pair.numerator pair.reference output.numerator output.reference
    pair.numerator.nonneg pair.reference.nonneg output.numerator.nonneg output.reference.nonneg
    pair.numerator.sum_eq_one pair.reference.sum_eq_one output.numerator.sum_eq_one
    output.reference.sum_eq_one pair.absolutelyContinuous output.absolutelyContinuous ?_
  intro t
  apply HockeyStick.centered_hockeyStick_le pair.numerator pair.reference t
    (fun a b ↦ kernel a b) (fun a ↦ (kernel a).nonneg) (fun a ↦ (kernel a).sum_eq_one)
  intro a a'
  calc
    (∑ b, |kernel a b - kernel a' b|) / 2 =
        ProbabilityVector.totalVariation (kernel a) (kernel a') := by
      unfold ProbabilityVector.totalVariation
      ring
    _ ≤ kernel.rowContractionCoefficient :=
      kernel.rowTotalVariation_le_rowContractionCoefficient a a'

end FiniteRelativeEntropy
