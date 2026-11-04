/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteRelativeEntropy.Basic

/-!
# Gibbs variational identity on a finite probability simplex

This file constructs the exponential tilt of a finite reference law and identifies every
entropy-regularized objective with a KL regret against that tilt.

## Main results

- `ProbabilityVector.gibbsTilt`: the normalized exponential tilt of a finite reference law.
- `finiteKL.gibbs_regret`: the exact finite Gibbs variational identity.
- `finiteKL.gibbsTilt_unique_minimizer`: uniqueness of the tilted minimizer.
-/

namespace FiniteMarkovKernels

open scoped BigOperators

universe u

namespace ProbabilityVector

variable {A : Type u} [Fintype A]

/-- The normalizing partition function for a finite exponential tilt. -/
noncomputable def partitionFunction (reference : ProbabilityVector A) (energy : A → ℝ)
    (beta : ℝ) : ℝ :=
  ∑ a, reference a * Real.exp (-beta * energy a)

/-- A finite exponential-tilt partition function is strictly positive. -/
theorem partitionFunction_pos (reference : ProbabilityVector A) (energy : A → ℝ)
    (beta : ℝ) : 0 < partitionFunction reference energy beta := by
  classical
  let a : reference.Support := Classical.choice inferInstance
  apply Finset.sum_pos'
  · intro x _hx
    exact mul_nonneg (reference.nonneg x) (Real.exp_pos _).le
  · exact ⟨a.1, Finset.mem_univ _, mul_pos a.2 (Real.exp_pos _)⟩

/-- The normalized exponential tilt of a finite reference law. -/
noncomputable def gibbsTilt (reference : ProbabilityVector A) (energy : A → ℝ)
    (beta : ℝ) : ProbabilityVector A where
  prob a := reference a * Real.exp (-beta * energy a) /
    partitionFunction reference energy beta
  nonneg a := div_nonneg (mul_nonneg (reference.nonneg a) (Real.exp_pos _).le)
    (partitionFunction_pos reference energy beta).le
  sum_eq_one := by
    rw [← Finset.sum_div]
    exact div_self (partitionFunction_pos reference energy beta).ne'

/-- A tilted mass is its reference mass times the exponential weight, divided by the partition. -/
@[simp]
theorem gibbsTilt_apply (reference : ProbabilityVector A) (energy : A → ℝ)
    (beta : ℝ) (a : A) :
    gibbsTilt reference energy beta a =
      reference a * Real.exp (-beta * energy a) /
        partitionFunction reference energy beta :=
  rfl

/-- Exponential tilting preserves every positive coordinate of the reference law. -/
theorem gibbsTilt_pos_iff (reference : ProbabilityVector A) (energy : A → ℝ)
    (beta : ℝ) (a : A) :
    0 < gibbsTilt reference energy beta a ↔ 0 < reference a := by
  rw [gibbsTilt_apply]
  constructor
  · intro h
    by_contra href
    have : reference a = 0 :=
      le_antisymm (not_lt.mp href) (reference.nonneg a)
    simp [this] at h
  · intro h
    exact div_pos (mul_pos h (Real.exp_pos _))
      (partitionFunction_pos reference energy beta)

/-- Absolute continuity with respect to a reference law is preserved by its exponential tilt. -/
theorem absolutelyContinuous_gibbsTilt {numerator reference : ProbabilityVector A}
    (h : numerator.AbsolutelyContinuous reference) (energy : A → ℝ) (beta : ℝ) :
    numerator.AbsolutelyContinuous (gibbsTilt reference energy beta) := by
  intro a hzero
  apply h a
  by_contra href
  have hrefPos := lt_of_le_of_ne (reference.nonneg a) fun hEq ↦ href hEq.symm
  exact (gibbsTilt_pos_iff reference energy beta a).mpr hrefPos |>.ne' hzero

/-- The Gibbs tilt is absolutely continuous with respect to its original reference. -/
theorem gibbsTilt_absolutelyContinuous (reference : ProbabilityVector A) (energy : A → ℝ)
    (beta : ℝ) : (reference.gibbsTilt energy beta).AbsolutelyContinuous reference := by
  intro a hzero
  simp [gibbsTilt_apply, hzero]

end ProbabilityVector

end FiniteMarkovKernels

namespace FiniteRelativeEntropy

open FiniteMarkovKernels
open scoped BigOperators

universe u

namespace finiteKL

variable {A : Type u} [Fintype A]

/-- The admissible pair comparing a numerator with the Gibbs tilt of its reference law. -/
noncomputable def gibbsPair (pair : AdmissiblePair A) (energy : A → ℝ) (beta : ℝ) :
    AdmissiblePair A where
  numerator := pair.numerator
  reference := pair.reference.gibbsTilt energy beta
  absolutelyContinuous :=
    ProbabilityVector.absolutelyContinuous_gibbsTilt pair.absolutelyContinuous energy beta

private theorem log_ratio_gibbsTilt (pair : AdmissiblePair A) (energy : A → ℝ)
    (beta : ℝ) (a : A) (ha : pair.numerator a ≠ 0) :
    Real.log (pair.numerator a / pair.reference.gibbsTilt energy beta a) =
      Real.log (pair.numerator a / pair.reference a) + beta * energy a +
        Real.log (ProbabilityVector.partitionFunction pair.reference energy beta) := by
  have href : pair.reference a ≠ 0 := fun hzero ↦
    ha (pair.absolutelyContinuous a hzero)
  have hpartition :
      ProbabilityVector.partitionFunction pair.reference energy beta ≠ 0 :=
    (ProbabilityVector.partitionFunction_pos pair.reference energy beta).ne'
  have hexp : Real.exp (-beta * energy a) ≠ 0 := (Real.exp_pos _).ne'
  rw [ProbabilityVector.gibbsTilt_apply]
  rw [Real.log_div ha (div_ne_zero (mul_ne_zero href hexp) hpartition)]
  rw [Real.log_div (mul_ne_zero href hexp) hpartition]
  rw [Real.log_mul href hexp, Real.log_exp]
  rw [Real.log_div ha href]
  ring

/-- Exact Gibbs regret identity for a finite entropy-regularized expectation. -/
theorem gibbs_regret (pair : AdmissiblePair A) (energy : A → ℝ) (beta : ℝ) :
    finiteKL pair + beta * ∑ a, pair.numerator a * energy a =
      finiteKL (gibbsPair pair energy beta) -
        Real.log (ProbabilityVector.partitionFunction pair.reference energy beta) := by
  unfold finiteKL
  rw [Finset.mul_sum]
  calc
    (∑ a, pair.numerator a * Real.log (pair.numerator a / pair.reference a)) +
        ∑ a, beta * (pair.numerator a * energy a) =
      ∑ a, pair.numerator a *
        (Real.log (pair.numerator a / pair.reference a) + beta * energy a) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro a _ha
          ring
    _ = ∑ a, pair.numerator a *
        (Real.log (pair.numerator a / pair.reference.gibbsTilt energy beta a) -
          Real.log (ProbabilityVector.partitionFunction pair.reference energy beta)) := by
          apply Finset.sum_congr rfl
          intro a _ha
          by_cases ha : pair.numerator a = 0
          · simp [ha]
          · rw [log_ratio_gibbsTilt pair energy beta a ha]
            ring
    _ = (∑ a, pair.numerator a *
          Real.log (pair.numerator a / pair.reference.gibbsTilt energy beta a)) -
        Real.log (ProbabilityVector.partitionFunction pair.reference energy beta) := by
          simp only [mul_sub]
          rw [Finset.sum_sub_distrib, ← Finset.sum_mul, pair.numerator.sum_eq_one, one_mul]

/-- The Gibbs tilt uniquely minimizes finite KL plus the scaled expected energy. -/
theorem gibbsTilt_unique_minimizer (pair : AdmissiblePair A) (energy : A → ℝ)
    (beta : ℝ) :
    finiteKL pair + beta * ∑ a, pair.numerator a * energy a ≥
      -Real.log (ProbabilityVector.partitionFunction pair.reference energy beta) ∧
    (finiteKL pair + beta * ∑ a, pair.numerator a * energy a =
        -Real.log (ProbabilityVector.partitionFunction pair.reference energy beta) ↔
      pair.numerator = pair.reference.gibbsTilt energy beta) := by
  rw [gibbs_regret]
  constructor
  · linarith [nonneg (gibbsPair pair energy beta)]
  · constructor
    · intro h
      apply (eq_zero_iff (gibbsPair pair energy beta)).mp
      linarith
    · intro h
      have hzero : finiteKL (gibbsPair pair energy beta) = 0 :=
        (eq_zero_iff (gibbsPair pair energy beta)).mpr h
      linarith

end finiteKL

end FiniteRelativeEntropy
