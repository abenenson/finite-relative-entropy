/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import FiniteRelativeEntropy.StrongDataProcessing.FiniteDivergence
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Strong data processing for finite Markov kernels

For any two probability measures on a finite alphabet, the output KL divergence is at most
the input KL divergence times any common upper bound on row-event oscillation. The output
is the same for all inputs at coefficient zero, including when the input divergence is
infinite. All measure-level conclusions use Mathlib's extended-valued KL divergence.

The strong inequality is classical. See Y. Polyanskiy and Y. Wu, *Information Theory:
From Coding to Learning*, Theorem 33.6(a), and J. E. Cohen, J. H. B. Kemperman and
G. Zbăganu, *Comparisons of Stochastic Matrices* (1998).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace FiniteRelativeEntropy

open StrongDataProcessing StrongDataProcessing.HockeyStick

section FiniteAtoms

variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
  {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- The real form of native KL on finite atoms, valid also for unequal finite masses.
The outer weight removes null atoms without imposing full support. -/
theorem toReal_klDiv_eq_sum_klFun (hac : μ ≪ ν) :
    (klDiv μ ν).toReal = ∑ x, ν.real {x} * klFun (μ.real {x} / ν.real {x}) := by
  rw [toReal_klDiv_eq_integral_klFun hac, integral_fintype Integrable.of_finite]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  by_cases hν : ν.real {x} = 0
  · simp [hν]
  have h := Measure.setLIntegral_rnDeriv hac ({x} : Set α)
  rw [lintegral_singleton] at h
  have hratio : (μ.rnDeriv ν x).toReal = μ.real {x} / ν.real {x} := by
    apply (eq_div_iff hν).2
    simpa only [measureReal_def, ENNReal.toReal_mul] using congrArg ENNReal.toReal h
  rw [smul_eq_mul, hratio]

/-- The native extended value equals the ordinary finite nonnegative sum, embedded in ENNReal. -/
theorem klDiv_eq_ofReal_sum_klFun (hac : μ ≪ ν) :
    klDiv μ ν = ENNReal.ofReal (∑ x, ν.real {x} * klFun (μ.real {x} / ν.real {x})) := by
  calc
    klDiv μ ν = ENNReal.ofReal (klDiv μ ν).toReal :=
      (ENNReal.ofReal_toReal (klDiv_ne_top hac Integrable.of_finite)).symm
    _ = _ := congrArg ENNReal.ofReal (toReal_klDiv_eq_sum_klFun hac)

end FiniteAtoms

section Kernel

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- On a finite input alphabet, the output probability of an event is the weighted
sum of the row probabilities. Finite measures and finite kernels suffice. -/
theorem real_comp_apply [Fintype X] [MeasurableSingletonClass X]
    (κ : Kernel X Y) [IsFiniteKernel κ] (μ : Measure X) [IsFiniteMeasure μ]
    {s : Set Y} (hs : MeasurableSet s) :
    (κ ∘ₘ μ).real s = ∑ x, μ.real {x} * (κ x).real s := by
  rw [measureReal_def, Measure.bind_apply hs κ.aemeasurable, lintegral_fintype,
    ENNReal.toReal_sum (by finiteness)]
  simp only [ENNReal.toReal_mul, measureReal_def, mul_comm]

/-- A common bound of zero on every ordered row difference makes the output laws
of any two probability inputs coincide. This applies to singular inputs as well. -/
theorem comp_eq_of_zero_row_oscillation (κ : Kernel X Y) [IsMarkovKernel κ]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hrows : ∀ x x' (s : Set Y), MeasurableSet s → (κ x).real s - (κ x').real s ≤ 0) :
    κ ∘ₘ μ = κ ∘ₘ ν := by
  obtain ⟨i⟩ := nonempty_of_isProbabilityMeasure μ
  have hconst : κ = Kernel.const X (κ i) := by
    apply Kernel.ext_iff'.2
    intro x s hs
    change κ x s = κ i s
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
    exact le_antisymm (sub_nonpos.mp (hrows x i s hs)) (sub_nonpos.mp (hrows i x s hs))
  rw [hconst, Measure.const_comp, Measure.const_comp, measure_univ, measure_univ]

end Kernel

private theorem sum_real_atoms {A : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (μ : Measure A) [IsProbabilityMeasure μ] :
    ∑ x, μ.real {x} = 1 := by
  simpa only [Finset.coe_univ, probReal_univ] using
    (sum_measureReal_singleton (μ := μ) (Finset.univ : Finset A))

private theorem real_atom_ac {A : Type*} [MeasurableSpace A] {μ ν : Measure A}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hac : μ ≪ ν) (x : A)
    (h : ν.real {x} = 0) : μ.real {x} = 0 :=
  (measureReal_eq_zero_iff (measure_ne_top μ {x})).mpr
    (hac ((measureReal_eq_zero_iff (measure_ne_top ν {x})).mp h))

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
  [MeasurableSpace Y] [MeasurableSingletonClass Y]

private theorem excess_comp_le [Fintype X] [Fintype Y]
    (κ : Kernel X Y) [IsMarkovKernel κ]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {η : ℝ}
    (hrows : ∀ x x' (s : Set Y), MeasurableSet s → (κ x).real s - (κ x').real s ≤ η) (t : ℝ) :
    excess (fun y ↦ (κ ∘ₘ μ).real {y} - t * (κ ∘ₘ ν).real {y}) ≤
      η * excess (fun x ↦ μ.real {x} - t * ν.real {x}) := by
  let K := fun x y ↦ (κ x).real {y}
  have h (y : Y) : push (fun x ↦ μ.real {x} - t * ν.real {x}) K y =
      (κ ∘ₘ μ).real {y} - t * (κ ∘ₘ ν).real {y} := by
    simp only [push, K, real_comp_apply κ μ (measurableSet_singleton y),
      real_comp_apply κ ν (measurableSet_singleton y), sub_mul,
      Finset.sum_sub_distrib, mul_assoc, Finset.mul_sum]
  simp_rw [← h]
  refine excess_push_le _ K (fun _ _ ↦ measureReal_nonneg) (fun x ↦ sum_real_atoms (κ x)) ?_
  intro x x' s
  simpa only [K, sum_measureReal_singleton] using hrows x x' s s.measurableSet

/-- A finite Markov kernel with row-event oscillation bounded by `η` sends any two
probability laws to laws with KL divergence at most `η` times the input KL. -/
theorem klDiv_comp_le_of_row_oscillation [Finite X] [Finite Y]
    (κ : Kernel X Y) [IsMarkovKernel κ]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {η : ℝ}
    (hη : 0 ≤ η)
    (hrows : ∀ x x' (s : Set Y), MeasurableSet s → (κ x).real s - (κ x').real s ≤ η) :
    klDiv (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ ENNReal.ofReal η * klDiv μ ν := by
  classical
  by_cases hac : μ ≪ ν
  · let := Fintype.ofFinite X
    let := Fintype.ofFinite Y
    have hout := hac.comp_right κ
    rw [klDiv_eq_ofReal_sum_klFun hout, klDiv_eq_ofReal_sum_klFun hac,
      ← ENNReal.ofReal_mul hη]
    apply ENNReal.ofReal_le_ofReal
    exact FiniteDivergence.of_centered_hinges klFun convexOn_klFun klFun_one
      (fun x ↦ μ.real {x}) (fun x ↦ ν.real {x})
      (fun y ↦ (κ ∘ₘ μ).real {y}) (fun y ↦ (κ ∘ₘ ν).real {y})
      (fun _ ↦ measureReal_nonneg) (fun _ ↦ measureReal_nonneg)
      (fun _ ↦ measureReal_nonneg) (fun _ ↦ measureReal_nonneg)
      (sum_real_atoms μ) (sum_real_atoms ν) (sum_real_atoms _) (sum_real_atoms _)
      (real_atom_ac hac) (real_atom_ac hout) (excess_comp_le κ μ ν hrows)
  · by_cases hzero : η = 0
    · subst η
      rw [comp_eq_of_zero_row_oscillation κ μ ν hrows, klDiv_self]
      exact bot_le
    · have hpos : 0 < η := lt_of_le_of_ne hη (Ne.symm hzero)
      rw [klDiv_of_not_ac hac, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr hpos)]
      exact le_top

end FiniteRelativeEntropy
