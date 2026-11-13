/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import FiniteMarkovKernels.ProbabilityVector

/-!
# Relative entropy on finite probability vectors

This file defines real-valued Kullback--Leibler divergence on the closed finite simplex. Its
domain records absolute continuity explicitly, so boundary distributions are supported without
using extended-real values. Relabeling, diagonal vanishing, measurability, and the dependent
chain rule are proved directly.

## Main results

- `AdmissiblePair`: a finite probability pair `p ≪ r`.
- `finiteKL`: the finite real sum `∑ a, p a * log (p a / r a)`.
- `finiteKL.relabel`: simultaneous permutation invariance.
- `finiteKL.compound`: the full dependent block-composition chain rule.
- `finiteKL.nonneg`: Gibbs' inequality on the closed finite simplex.
-/

@[expose] public section

namespace FiniteRelativeEntropy

open FiniteMarkovKernels

open scoped BigOperators ENNReal

universe u v

/-- A pair of finite probability vectors on which real-valued relative entropy is finite. -/
structure AdmissiblePair (A : Type u) [Fintype A] where
  /-- The numerator distribution. -/
  numerator : ProbabilityVector A
  /-- The reference distribution. -/
  reference : ProbabilityVector A
  /-- The numerator is absolutely continuous with respect to the reference. -/
  absolutelyContinuous : numerator.AbsolutelyContinuous reference

namespace AdmissiblePair

variable {A : Type u} {B : Type v} [Fintype A] [Fintype B]

/-- Admissible pairs are equal when their numerator and reference vectors agree. -/
@[ext]
theorem ext {P Q : AdmissiblePair A} (hnumerator : P.numerator = Q.numerator)
    (hreference : P.reference = Q.reference) : P = Q := by
  cases P
  cases Q
  simp_all

attribute [inherit_doc FiniteRelativeEntropy.AdmissiblePair.ext]
  FiniteRelativeEntropy.AdmissiblePair.ext_iff

/-- The diagonal admissible pair `(p,p)`. -/
def diagonal (p : ProbabilityVector A) : AdmissiblePair A :=
  ⟨p, p, ProbabilityVector.absolutelyContinuous_refl p⟩

/-- Simultaneously relabel both entries of an admissible pair. -/
noncomputable def relabel (e : A ≃ B) (P : AdmissiblePair A) : AdmissiblePair B where
  numerator := P.numerator.relabel e
  reference := P.reference.relabel e
  absolutelyContinuous :=
    (ProbabilityVector.absolutelyContinuous_relabel_iff e _ _).mpr P.absolutelyContinuous

variable {C : A → Type v} [∀ a, Fintype (C a)]

/-- Form the admissible pair of dependent compound distributions. -/
noncomputable def compound (outer : AdmissiblePair A)
    (inner : ∀ a, AdmissiblePair (C a)) : AdmissiblePair (Σ a, C a) where
  numerator := ProbabilityVector.compound outer.numerator fun a ↦ (inner a).numerator
  reference := ProbabilityVector.compound outer.reference fun a ↦ (inner a).reference
  absolutelyContinuous := ProbabilityVector.compound_absolutelyContinuous
    outer.absolutelyContinuous fun a ↦ (inner a).absolutelyContinuous

end AdmissiblePair

/-- The admissible references for one fixed numerator distribution. -/
abbrev AdmissibleReference {A : Type u} [Fintype A] (p : ProbabilityVector A) :=
  {r : ProbabilityVector A // p.AbsolutelyContinuous r}

/-- Real-valued Kullback--Leibler divergence on a finite admissible probability pair. -/
noncomputable def finiteKL {A : Type u} [Fintype A] (P : AdmissiblePair A) : ℝ :=
  ∑ a, P.numerator a * Real.log (P.numerator a / P.reference a)

end FiniteRelativeEntropy

namespace FiniteMarkovKernels.ProbabilityVector

open scoped BigOperators ENNReal

universe u

open MeasureTheory

/-- The discrete measure whose atom masses are the coordinates of a probability vector. -/
noncomputable def toMeasure {A : Type u} [Fintype A] [MeasurableSpace A]
    (p : ProbabilityVector A) : Measure A :=
  Measure.count.withDensity fun a ↦ ENNReal.ofReal (p a)

/-- A finite probability vector induces a finite measure. -/
noncomputable instance toMeasure.isFiniteMeasure {A : Type u} [Fintype A]
    [MeasurableSpace A] [MeasurableSingletonClass A] (p : ProbabilityVector A) :
    IsFiniteMeasure p.toMeasure := by
  unfold toMeasure
  exact isFiniteMeasure_withDensity_ofReal Integrable.of_finite.hasFiniteIntegral

/-- The discrete measure of a probability vector has the expected singleton masses. -/
theorem toMeasure_apply_singleton {A : Type u} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (p : ProbabilityVector A) (a : A) :
    p.toMeasure {a} = ENNReal.ofReal (p a) := by
  simp [toMeasure]

/-- The discrete-measure representation of a finite probability vector is injective. -/
theorem toMeasure_injective {A : Type u} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] :
    Function.Injective (toMeasure : ProbabilityVector A → Measure A) := by
  intro p q hmeasure
  apply ProbabilityVector.ext
  intro a
  have hmass := congrArg (fun measure : Measure A ↦ measure {a}) hmeasure
  rw [toMeasure_apply_singleton, toMeasure_apply_singleton] at hmass
  have hreal := congrArg ENNReal.toReal hmass
  simpa [p.nonneg a, q.nonneg a] using hreal

end FiniteMarkovKernels.ProbabilityVector

namespace FiniteRelativeEntropy

open FiniteMarkovKernels
open scoped BigOperators ENNReal

universe u v

namespace finiteKL

variable {A : Type u} {B : Type v} [Fintype A] [Fintype B]

open MeasureTheory

/-- Finite KL vanishes on diagonal pairs, including at zero coordinates. -/
@[simp]
theorem diagonal (p : ProbabilityVector A) : finiteKL (AdmissiblePair.diagonal p) = 0 := by
  unfold finiteKL AdmissiblePair.diagonal
  apply Finset.sum_eq_zero
  intro a _ha
  by_cases ha : p a = 0
  · simp [ha]
  · simp [ha]

/-- Finite KL is invariant under simultaneous relabeling of the alphabet. -/
theorem relabel (e : A ≃ B) (P : AdmissiblePair A) :
    finiteKL (P.relabel e) = finiteKL P := by
  unfold finiteKL AdmissiblePair.relabel
  symm
  exact Fintype.sum_equiv e _ _ fun a ↦ by simp

/-- The `p log (p/r)` formula agrees with Mathlib's `klFun` formula on admissible pairs. -/
theorem eq_sum_klFun (P : AdmissiblePair A) :
    finiteKL P =
      ∑ a, P.reference a *
        _root_.InformationTheory.klFun (P.numerator a / P.reference a) := by
  calc
    finiteKL P =
        ∑ a, (P.reference a *
            _root_.InformationTheory.klFun (P.numerator a / P.reference a) +
          (P.numerator a - P.reference a)) := by
      unfold finiteKL
      apply Finset.sum_congr rfl
      intro a _ha
      by_cases hra : P.reference a = 0
      · have hpa := P.absolutelyContinuous a hra
        simp [hra, hpa, _root_.InformationTheory.klFun_apply]
      · rw [_root_.InformationTheory.klFun_apply]
        field_simp
        ring
    _ = (∑ a, P.reference a *
          _root_.InformationTheory.klFun (P.numerator a / P.reference a)) +
        ((∑ a, P.numerator a) - ∑ a, P.reference a) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = ∑ a, P.reference a *
        _root_.InformationTheory.klFun (P.numerator a / P.reference a) := by
      rw [P.numerator.sum_eq_one, P.reference.sum_eq_one, sub_self, add_zero]

/-- Finite KL is measurable in the reference distribution for a fixed numerator. -/
theorem measurable_reference (p : ProbabilityVector A) :
    Measurable fun r : AdmissibleReference p ↦
      finiteKL ⟨p, r.1, r.2⟩ := by
  unfold finiteKL
  apply Finset.measurable_sum
  intro a _ha
  have hcoord : Measurable fun r : AdmissibleReference p ↦ r.1 a :=
    (ProbabilityVector.measurable_apply a).comp measurable_subtype_coe
  change Measurable fun r : AdmissibleReference p ↦
    p a * Real.log (p a / r.1 a)
  exact measurable_const.mul (hcoord.const_div (p a)).log

private theorem integrand_mul
    {p q r s : ℝ} (hpr : r = 0 → p = 0) (hqs : s = 0 → q = 0) :
    (p * q) * Real.log ((p * q) / (r * s)) =
      q * (p * Real.log (p / r)) + p * (q * Real.log (q / s)) := by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hq0 : q = 0
  · simp [hq0]
  have hr0 : r ≠ 0 := fun hr ↦ hp0 (hpr hr)
  have hs0 : s ≠ 0 := fun hs ↦ hq0 (hqs hs)
  rw [mul_div_mul_comm, Real.log_mul (div_ne_zero hp0 hr0) (div_ne_zero hq0 hs0)]
  ring

variable {C : A → Type v} [∀ a, Fintype (C a)]

/-- Finite KL obeys the full dependent block-composition chain rule. -/
theorem compound (outer : AdmissiblePair A) (inner : ∀ a, AdmissiblePair (C a)) :
    finiteKL (outer.compound inner) =
      finiteKL outer + ∑ a, outer.numerator a * finiteKL (inner a) := by
  unfold finiteKL AdmissiblePair.compound
  rw [Fintype.sum_sigma]
  simp only [ProbabilityVector.compound_apply]
  calc
    (∑ a, ∑ c,
        (outer.numerator a * (inner a).numerator c) *
          Real.log ((outer.numerator a * (inner a).numerator c) /
            (outer.reference a * (inner a).reference c))) =
        ∑ a, ∑ c,
          ((inner a).numerator c *
              (outer.numerator a * Real.log (outer.numerator a / outer.reference a)) +
            outer.numerator a *
              ((inner a).numerator c *
                Real.log ((inner a).numerator c / (inner a).reference c))) := by
      apply Finset.sum_congr rfl
      intro a _ha
      apply Finset.sum_congr rfl
      intro c _hc
      exact integrand_mul (outer.absolutelyContinuous a) ((inner a).absolutelyContinuous c)
    _ = finiteKL outer + ∑ a, outer.numerator a * finiteKL (inner a) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      unfold finiteKL
      congr 1
      apply Finset.sum_congr rfl
      intro a _ha
      rw [← Finset.sum_mul, (inner a).numerator.sum_eq_one, one_mul]

/-- Finite KL is nonnegative. -/
theorem nonneg (P : AdmissiblePair A) : 0 ≤ finiteKL P := by
  rw [eq_sum_klFun]
  exact Finset.sum_nonneg fun a _ha ↦
    mul_nonneg (P.reference.nonneg a)
      (_root_.InformationTheory.klFun_nonneg
        (div_nonneg (P.numerator.nonneg a) (P.reference.nonneg a)))

section MathlibBridge

variable [MeasurableSpace A] [MeasurableSingletonClass A]

private theorem density_measurable (p : ProbabilityVector A) :
    Measurable fun a ↦ ENNReal.ofReal (p a) :=
  measurable_of_finite _

private theorem toMeasure_eq_withDensity (P : AdmissiblePair A) :
    P.numerator.toMeasure =
      P.reference.toMeasure.withDensity fun a ↦
        ENNReal.ofReal (P.numerator a) / ENNReal.ofReal (P.reference a) := by
  let f : A → ℝ≥0∞ := fun a ↦ ENNReal.ofReal (P.numerator a)
  let g : A → ℝ≥0∞ := fun a ↦ ENNReal.ofReal (P.reference a)
  let h : A → ℝ≥0∞ := fun a ↦ f a / g a
  have hfg : g * h = f := by
    funext a
    exact ENNReal.mul_div_cancel'
      (fun hga ↦ by
        have hle : P.reference a ≤ 0 :=
          ENNReal.ofReal_eq_zero.mp (by simpa [g] using hga)
        have hra : P.reference a = 0 := le_antisymm hle (P.reference.nonneg a)
        simp [f, P.absolutelyContinuous a hra])
      (fun hga ↦ by simp [g] at hga)
  change Measure.count.withDensity f = (Measure.count.withDensity g).withDensity h
  rw [← withDensity_mul Measure.count (density_measurable P.reference)
    (measurable_of_finite h), hfg]

private theorem toMeasure_absolutelyContinuous (P : AdmissiblePair A) :
    P.numerator.toMeasure ≪ P.reference.toMeasure := by
  rw [toMeasure_eq_withDensity P]
  exact withDensity_absolutelyContinuous _ _

/-- Finite KL is Mathlib's measure-theoretic KL on the associated discrete measures. -/
theorem eq_toReal_klDiv (P : AdmissiblePair A) :
    finiteKL P =
      (_root_.InformationTheory.klDiv
        P.numerator.toMeasure P.reference.toMeasure).toReal := by
  let h : A → ℝ≥0∞ := fun a ↦
    ENNReal.ofReal (P.numerator a) / ENNReal.ofReal (P.reference a)
  have hrn :
      P.numerator.toMeasure.rnDeriv P.reference.toMeasure =ᵐ[P.reference.toMeasure] h := by
    rw [toMeasure_eq_withDensity P]
    exact Measure.rnDeriv_withDensity _ (measurable_of_finite h)
  rw [_root_.InformationTheory.toReal_klDiv_eq_integral_klFun
    (toMeasure_absolutelyContinuous P)]
  symm
  calc
    ∫ a, _root_.InformationTheory.klFun
          (P.numerator.toMeasure.rnDeriv P.reference.toMeasure a).toReal
        ∂P.reference.toMeasure =
        ∫ a, _root_.InformationTheory.klFun (h a).toReal ∂P.reference.toMeasure := by
      apply integral_congr_ae
      filter_upwards [hrn] with a ha
      rw [ha]
    _ = ∫ a, P.reference a *
          _root_.InformationTheory.klFun (P.numerator a / P.reference a)
        ∂Measure.count := by
      unfold ProbabilityVector.toMeasure
      rw [integral_withDensity_eq_integral_toReal_smul
        (density_measurable P.reference)]
      · apply integral_congr_ae
        exact ae_of_all _ fun a ↦ by
          simp [h, ENNReal.toReal_div, P.numerator.nonneg a, P.reference.nonneg a]
      · exact ae_of_all _ fun a ↦ ENNReal.ofReal_lt_top
    _ = ∑ a, P.reference a *
        _root_.InformationTheory.klFun (P.numerator a / P.reference a) := by
      exact integral_count _
    _ = finiteKL P := (eq_sum_klFun P).symm

/-- The measure-theoretic KL associated to an admissible finite pair is finite. -/
theorem klDiv_ne_top (P : AdmissiblePair A) :
    _root_.InformationTheory.klDiv
        P.numerator.toMeasure P.reference.toMeasure ≠ ⊤ := by
  rw [_root_.InformationTheory.klDiv_ne_top_iff]
  exact ⟨toMeasure_absolutelyContinuous P, Integrable.of_finite⟩

end MathlibBridge

/-- Finite KL vanishes exactly when its numerator and reference vectors agree. -/
theorem eq_zero_iff (P : AdmissiblePair A) :
    finiteKL P = 0 ↔ P.numerator = P.reference := by
  let : MeasurableSpace A := ⊤
  let : MeasurableSingletonClass A := ⟨fun _ ↦ trivial⟩
  rw [eq_toReal_klDiv, ENNReal.toReal_eq_zero_iff]
  simp only [klDiv_ne_top P, or_false, _root_.InformationTheory.klDiv_eq_zero_iff]
  exact ProbabilityVector.toMeasure_injective.eq_iff

end finiteKL

end FiniteRelativeEntropy
