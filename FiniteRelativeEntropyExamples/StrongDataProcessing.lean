/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import FiniteRelativeEntropy.StrongDataProcessing.Measure
public import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Tactic.NormNum

/-!
# Two finite channels for strong data processing

A binary symmetric channel flips each bit with probability one quarter. Its maximum difference
in row-event probability is one half. A constant channel sends two singular Dirac inputs to
the same output law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory
open FiniteRelativeEntropy
open scoped ENNReal

namespace FiniteRelativeEntropy.Examples

/-- The binary symmetric channel that flips each input bit with probability one quarter. -/
noncomputable def quarterFlip : Kernel Bool Bool :=
  let keep : unitInterval := ⟨3 / 4, by constructor <;> norm_num⟩
  Kernel.boolKernel (bernoulliMeasure false true keep) (bernoulliMeasure true false keep)

/-- Both rows of the quarter-flip channel are probability laws. -/
instance quarterFlip.isMarkovKernel : IsMarkovKernel quarterFlip := by
  unfold quarterFlip
  infer_instance

private theorem quarterFlip_rows (x x' : Bool) (s : Set Bool) (_hs : MeasurableSet s) :
    (quarterFlip x).real s - (quarterFlip x').real s ≤ 1 / 2 := by
  classical
  cases x <;> cases x' <;> by_cases hf : false ∈ s <;> by_cases ht : true ∈ s <;>
    norm_num [quarterFlip, *]

/-- The event consisting of `false` attains the one-half row bound. -/
theorem quarterFlip_singleton_gap :
    (quarterFlip false).real {false} - (quarterFlip true).real {false} = 1 / 2 := by
  norm_num [quarterFlip]

/-- Applying the quarter-flip channel bounds output KL by one half of input KL. -/
theorem quarterFlip_klDiv_le_half (μ ν : Measure Bool)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    klDiv (quarterFlip ∘ₘ μ) (quarterFlip ∘ₘ ν) ≤ ENNReal.ofReal (1 / 2) * klDiv μ ν :=
  klDiv_comp_le_of_row_oscillation quarterFlip μ ν (by norm_num) quarterFlip_rows

/-- Mutually singular bit inputs have infinite KL. Sending both through a constant
channel yields zero KL, even for the zero coefficient times infinite input divergence. -/
theorem constant_channel_singular_inputs :
    klDiv (Measure.dirac false) (Measure.dirac true) = ∞ ∧
      klDiv (Kernel.const Bool (Measure.dirac false) ∘ₘ Measure.dirac false)
        (Kernel.const Bool (Measure.dirac false) ∘ₘ Measure.dirac true) = 0 := by
  have input : klDiv (Measure.dirac false) (Measure.dirac true) = ∞ := by
    apply klDiv_of_not_ac
    intro h
    have hzero : Measure.dirac true ({false} : Set Bool) = 0 := by simp
    have impossible : Measure.dirac false ({false} : Set Bool) = 0 := h hzero
    simp at impossible
  refine ⟨input, le_antisymm ?_ bot_le⟩
  have bound := klDiv_comp_le_of_row_oscillation (Kernel.const Bool (Measure.dirac false))
    (Measure.dirac false) (Measure.dirac true) (η := 0) le_rfl (fun _ _ _ _ ↦ by simp)
  simpa only [input, ENNReal.ofReal_zero, zero_mul] using bound

end FiniteRelativeEntropy.Examples
