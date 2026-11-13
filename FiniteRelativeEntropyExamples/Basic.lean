/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import FiniteRelativeEntropy

/-!
# Exact boundary and Gibbs examples

The examples use the probability vectors shared with `FiniteMarkovKernels`. A point mass
against a fair coin has KL equal to `log 2`. Exponential tilting of a fair coin by energies
`0` and `log 3` gives masses `3/4` and `1/4`; the Gibbs equality characterizes this law.
The characterization example also includes a zero numerator coordinate.
-/

@[expose] public section

namespace FiniteRelativeEntropy.Examples

open FiniteMarkovKernels
open scoped BigOperators

/-- The fair probability law on two outcomes. -/
noncomputable def fair : ProbabilityVector Bool :=
  ProbabilityVector.boolBinary (1 / 2) (by norm_num)

/-- A boundary numerator compared with a strictly positive reference. -/
noncomputable def boundaryPair : AdmissiblePair Bool where
  numerator := ProbabilityVector.dirac false
  reference := fair
  absolutelyContinuous := by
    intro b hb
    cases b <;> norm_num [fair, ProbabilityVector.boolBinary] at hb

/-- The boundary numerator has an exactly zero coordinate. -/
theorem boundary_numerator_true : boundaryPair.numerator true = 0 := by
  simp [boundaryPair, ProbabilityVector.dirac_apply]

/-- A point mass against a fair reference has divergence `log 2`. -/
theorem boundary_kl : finiteKL boundaryPair = Real.log 2 := by
  norm_num [finiteKL, boundaryPair, fair, Fintype.sum_bool,
    ProbabilityVector.dirac_apply, ProbabilityVector.boolBinary]

/-- Diagonal vanishing also holds when both laws have a zero reference coordinate. -/
theorem boundary_diagonal :
    finiteKL (AdmissiblePair.diagonal (ProbabilityVector.dirac false)) = 0 :=
  finiteKL.diagonal _

/-- Energies whose exponential weights are `1` and `1/3` at inverse temperature one. -/
noncomputable def logarithmicEnergy (b : Bool) : ℝ :=
  if b then Real.log 3 else 0

/-- The partition function for the nonconstant energy example is exactly `2/3`. -/
theorem logarithmic_partition : fair.partitionFunction logarithmicEnergy 1 = 2 / 3 := by
  norm_num [ProbabilityVector.partitionFunction, fair, logarithmicEnergy, Fintype.sum_bool,
    ProbabilityVector.boolBinary, Real.exp_neg, Real.exp_log]

/-- The lower-energy outcome has Gibbs probability `3/4`. -/
theorem logarithmic_tilt_false : fair.gibbsTilt logarithmicEnergy 1 false = 3 / 4 := by
  rw [ProbabilityVector.gibbsTilt_apply, logarithmic_partition]
  norm_num [fair, logarithmicEnergy, ProbabilityVector.boolBinary]

/-- The higher-energy outcome has Gibbs probability `1/4`. -/
theorem logarithmic_tilt_true : fair.gibbsTilt logarithmicEnergy 1 true = 1 / 4 := by
  rw [ProbabilityVector.gibbsTilt_apply, logarithmic_partition]
  norm_num [fair, logarithmicEnergy, ProbabilityVector.boolBinary, Real.exp_neg, Real.exp_log]

/-- The tilted law is an admissible numerator for its original reference. -/
noncomputable def minimizingPair : AdmissiblePair Bool where
  numerator := fair.gibbsTilt logarithmicEnergy 1
  reference := fair
  absolutelyContinuous := fair.gibbsTilt_absolutelyContinuous logarithmicEnergy 1

/-- The exact Gibbs lower bound is attained by the tilted law. -/
theorem logarithmic_minimum :
    finiteKL minimizingPair + ∑ b, minimizingPair.numerator b * logarithmicEnergy b =
      -Real.log (2 / 3) := by
  have h := (finiteKL.gibbsTilt_unique_minimizer minimizingPair logarithmicEnergy 1).2.mpr rfl
  simpa [minimizingPair, logarithmic_partition] using h

/-- Equality in the same objective determines both coordinates of every minimizer. -/
theorem logarithmic_unique (pair : AdmissiblePair Bool) (hreference : pair.reference = fair)
    (hminimum : finiteKL pair + ∑ b, pair.numerator b * logarithmicEnergy b =
      -Real.log (2 / 3)) :
    pair.numerator false = 3 / 4 ∧ pair.numerator true = 1 / 4 := by
  have h := (finiteKL.gibbsTilt_unique_minimizer pair logarithmicEnergy 1).2.mp
    (by simpa [hreference, logarithmic_partition] using hminimum)
  rw [h, hreference]
  exact ⟨logarithmic_tilt_false, logarithmic_tilt_true⟩

/-- Tilting cannot create mass at an outcome excluded by the reference support. -/
theorem tilt_preserves_zero (energy : Bool → ℝ) (beta : ℝ) :
    (ProbabilityVector.dirac false).gibbsTilt energy beta true = 0 := by
  simp [ProbabilityVector.gibbsTilt_apply, ProbabilityVector.dirac_apply]

/-- Leinster's conclusion applies to the boundary pair with the same global scalar. -/
theorem characterized_boundary (family : RelativeEntropyFamily) :
    family boundaryPair = family.probeScale * Real.log 2 := by
  rw [family.characterization, boundary_kl]

/-- A nonnegative family has a nonnegative scalar under the additional explicit hypothesis. -/
theorem characterized_scale_nonnegative (family : RelativeEntropyFamily)
    (h : family.Nonnegative) : 0 ≤ family.probeScale :=
  family.probeScale_nonneg h

end FiniteRelativeEntropy.Examples
