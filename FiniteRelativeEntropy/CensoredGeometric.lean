/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import FiniteRelativeEntropy.Basic
public import Mathlib.Probability.Distributions.Geometric

import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Exact relative entropy loss from censoring a geometric waiting time

Mathlib's geometric law counts failures before the first success. With a cap of `n` attempts,
a success is recorded with its failure count `k < n`. If all `n` attempts fail, the observer
records a separate tail outcome. At `n = 0`, every observation is a tail outcome.

The finite probability vector agrees with the pushforward of `ProbabilityTheory.geometricMeasure`.
For hazards `p, q ∈ (0, 1)`, the KL loss is exactly the numerator's tail probability
`(1 - p)^n` times the full geometric KL.
-/

@[expose] public section

open FiniteMarkovKernels InformationTheory MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace FiniteRelativeEntropy

/-- A success with fewer than `n` preceding failures, or a censored tail. -/
abbrev CensoredWaitingTime (n : ℕ) : Type := Fin n ⊕ PUnit

namespace CensoredWaitingTime

/-- Every individual observation in the finite outcome space is measurable. -/
instance instMeasurableSingletonClass (n : ℕ) :
    MeasurableSingletonClass (CensoredWaitingTime n) :=
  ⟨fun _ ↦ measurableSet_sum_iff.mpr ⟨.of_discrete, .of_discrete⟩⟩

/-- Keep an observed failure count below the cap and send every remaining count to the tail. -/
def censor (n k : ℕ) : CensoredWaitingTime n :=
  if h : k < n then Sum.inl ⟨k, h⟩ else Sum.inr PUnit.unit

private theorem preimage_event (n : ℕ) (k : Fin n) :
    censor n ⁻¹' {Sum.inl k} = {(k : ℕ)} := by
  ext j
  by_cases h : j < n
  · simp [censor, h, Fin.ext_iff]
  · have hne : j ≠ (k : ℕ) := fun he ↦ h (he ▸ k.isLt)
    simp [censor, h, hne]

private theorem preimage_tail (n : ℕ) :
    censor n ⁻¹' {Sum.inr PUnit.unit} = Ici n := by
  ext k
  by_cases h : k < n
  · simp [censor, h, not_le.mpr h]
  · simp [censor, h, le_of_not_gt h]

end CensoredWaitingTime

open CensoredWaitingTime

private theorem geometricMeasure_real_tail {p : unitInterval} (hp : p ≠ 0) (n : ℕ) :
    (geometricMeasure p).real (Ici n) = (1 - (p : ℝ)) ^ n := by
  have hhead : Iio n = (↑(Finset.range n) : Set ℕ) := by ext k; simp
  rw [← compl_Iio, measureReal_compl .of_discrete, hhead, ← sum_measureReal_singleton]
  simp_rw [geometricMeasure_real_singleton hp]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one]
  rw [← Finset.sum_mul]
  have hsum := geom_sum_mul_neg (1 - (p : ℝ)) n
  rw [sub_sub_cancel] at hsum
  rw [hsum, sub_sub_cancel]

/-- The finite law of the observed success index or tail outcome of a geometric waiting time.
For a positive success hazard this is the capped waiting law. At `p = 0` it inherits Mathlib's
convention `geometricMeasure 0 = Measure.dirac 0`. -/
noncomputable def censoredGeometric (n : ℕ) (p : unitInterval) :
    ProbabilityVector (CensoredWaitingTime n) where
  prob a := ((geometricMeasure p).map (censor n)).real {a}
  nonneg _ := measureReal_nonneg
  sum_eq_one := by
    have : IsProbabilityMeasure ((geometricMeasure p).map (censor n)) :=
      (Measure.isProbabilityMeasure_map_iff Measurable.of_discrete.aemeasurable).mpr inferInstance
    simp

/-- The finite censored law induces the pushforward of the complete geometric law. -/
theorem censoredGeometric_toMeasure (n : ℕ) (p : unitInterval) :
    (censoredGeometric n p).toMeasure = (geometricMeasure p).map (censor n) := by
  have : IsProbabilityMeasure ((geometricMeasure p).map (censor n)) :=
    (Measure.isProbabilityMeasure_map_iff Measurable.of_discrete.aemeasurable).mpr inferInstance
  apply Measure.ext_of_singleton
  intro a
  rw [ProbabilityVector.toMeasure_apply_singleton]
  exact ENNReal.ofReal_toReal (measure_ne_top _ _)

/-- A success after `k < n` failures retains its full geometric mass. -/
theorem censoredGeometric_event (n : ℕ) {p : unitInterval} (hp : p ≠ 0) (k : Fin n) :
    censoredGeometric n p (Sum.inl k) = (1 - (p : ℝ)) ^ (k : ℕ) * p := by
  change (((geometricMeasure p).map (censor n)) {Sum.inl k}).toReal = _
  rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton _), preimage_event]
  exact geometricMeasure_real_singleton hp k

/-- The tail coordinate is the probability of `n` consecutive failures. -/
theorem censoredGeometric_tail (n : ℕ) {p : unitInterval} (hp : p ≠ 0) :
    censoredGeometric n p (Sum.inr PUnit.unit) = (1 - (p : ℝ)) ^ n := by
  change (((geometricMeasure p).map (censor n)) {Sum.inr PUnit.unit}).toReal = _
  rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton _), preimage_tail]
  exact geometricMeasure_real_tail hp n

private theorem survival_pos {p : unitInterval} (hp : p ≠ 1) : 0 < 1 - (p : ℝ) :=
  sub_pos.mpr (lt_of_le_of_ne p.2.2 (unitInterval.coe_ne_one.mpr hp))

/-- The finite comparison has full reference support when the reference hazard is interior. -/
noncomputable def censoredGeometricPair (n : ℕ) (p q : unitInterval)
    (hq : q ≠ 0) (hq' : q ≠ 1) : AdmissiblePair (CensoredWaitingTime n) where
  numerator := censoredGeometric n p
  reference := censoredGeometric n q
  absolutelyContinuous a ha := by
    exfalso
    cases a with
    | inl k =>
      rw [censoredGeometric_event n hq] at ha
      exact (geometricMeasure_pos hq hq' k).ne' ha
    | inr u =>
      cases u
      rw [censoredGeometric_tail n hq] at ha
      exact (pow_pos (survival_pos hq') n).ne' ha

private theorem log_mass_ratio {p q : unitInterval} (hp : p ≠ 0) (hp' : p ≠ 1)
    (hq : q ≠ 0) (hq' : q ≠ 1) (k : ℕ) :
    Real.log (((1 - (p : ℝ)) ^ k * p) / ((1 - (q : ℝ)) ^ k * q)) =
      Real.log ((p : ℝ) / q) + k * Real.log ((1 - (p : ℝ)) / (1 - (q : ℝ))) := by
  rw [mul_div_mul_comm, ← div_pow,
    Real.log_mul (pow_ne_zero _ (div_ne_zero (survival_pos hp').ne' (survival_pos hq').ne'))
      (div_ne_zero (unitInterval.coe_ne_zero.mpr hp) (unitInterval.coe_ne_zero.mpr hq)),
    Real.log_pow, add_comm]

private theorem geometricMeasure_density {q : unitInterval} (p : unitInterval)
    (hq : q ≠ 0) (hq' : q ≠ 1) :
    geometricMeasure p = (geometricMeasure q).withDensity
      (fun k ↦ geometricMeasure p {k} / geometricMeasure q {k}) := by
  apply Measure.ext_of_singleton
  intro k
  rw [withDensity_apply _ (measurableSet_singleton k), lintegral_singleton]
  symm
  exact ENNReal.div_mul_cancel
    (by rw [geometricMeasure_singleton hq]; exact (ENNReal.ofReal_pos.mpr
      (geometricMeasure_pos hq hq' k)).ne')
    (measure_ne_top _ _)

private theorem geometricMeasure_log_likelihood {p q : unitInterval} (hp : p ≠ 0) (hp' : p ≠ 1)
    (hq : q ≠ 0) (hq' : q ≠ 1) :
    geometricMeasure p ≪ geometricMeasure q ∧
      llr (geometricMeasure p) (geometricMeasure q) =ᵐ[geometricMeasure p]
        fun k ↦ Real.log ((p : ℝ) / q) + k * Real.log ((1 - (p : ℝ)) / (1 - (q : ℝ))) := by
  have hac : geometricMeasure p ≪ geometricMeasure q := by
    rw [geometricMeasure_density p hq hq']
    exact withDensity_absolutelyContinuous _ _
  refine ⟨hac, ?_⟩
  have hrn : (geometricMeasure p).rnDeriv (geometricMeasure q) =ᵐ[geometricMeasure q]
      fun k ↦ geometricMeasure p {k} / geometricMeasure q {k} := by
    conv_lhs => rw [geometricMeasure_density p hq hq']
    exact Measure.rnDeriv_withDensity _ Measurable.of_discrete
  filter_upwards [hac.ae_le hrn] with k hk
  change Real.log (((geometricMeasure p).rnDeriv (geometricMeasure q) k).toReal) = _
  rw [hk, ENNReal.toReal_div]
  change Real.log ((geometricMeasure p).real {k} / (geometricMeasure q).real {k}) = _
  rw [geometricMeasure_real_singleton hp, geometricMeasure_real_singleton hq]
  exact log_mass_ratio hp hp' hq hq' k

private theorem hasSum_geometric_log_likelihood {p : unitInterval} (hp : p ≠ 0) (a b : ℝ) :
    HasSum (fun k : ℕ ↦ (1 - (p : ℝ)) ^ k * p * (a + k * b))
      (a + (1 - (p : ℝ)) / p * b) := by
  have hp0 : (p : ℝ) ≠ 0 := unitInterval.coe_ne_zero.mpr hp
  have hnorm : ‖1 - (p : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr p.2.2)]
    exact sub_lt_self _ (lt_of_le_of_ne p.2.1 hp0.symm)
  have hweighted : HasSum (fun k : ℕ ↦ (1 - (p : ℝ)) ^ k * p * k) ((1 - (p : ℝ)) / p) := by
    convert (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).mul_left (p : ℝ) using 1
    · ext k
      ring
    · field_simp [hp0]
      ring
  convert ((hasSum_one_geometricMeasure hp).mul_right a).add (hweighted.mul_right b) using 1
  · ext k
    ring
  · ring

/-- For two interior hazards the complete geometric relative entropy is finite. -/
theorem klDiv_geometricMeasure_ne_top {p q : unitInterval} (hp : p ≠ 0) (hp' : p ≠ 1)
    (hq : q ≠ 0) (hq' : q ≠ 1) : klDiv (geometricMeasure p) (geometricMeasure q) ≠ ∞ := by
  obtain ⟨hac, hllr⟩ := geometricMeasure_log_likelihood hp hp' hq hq'
  apply InformationTheory.klDiv_ne_top hac
  refine (Integrable.congr ?_ hllr.symm)
  rw [integrable_geometricMeasure_iff hp]
  simpa only [norm_mul, Real.norm_of_nonneg (geometricMeasure_nonneg p _)] using
    (hasSum_geometric_log_likelihood hp (Real.log ((p : ℝ) / q))
      (Real.log ((1 - (p : ℝ)) / (1 - (q : ℝ))))).summable.norm

/-- Closed form for Mathlib's relative entropy between geometric laws of two interior hazards. -/
theorem toReal_klDiv_geometricMeasure {p q : unitInterval} (hp : p ≠ 0) (hp' : p ≠ 1)
    (hq : q ≠ 0) (hq' : q ≠ 1) :
    (klDiv (geometricMeasure p) (geometricMeasure q)).toReal = Real.log ((p : ℝ) / q) +
      (1 - (p : ℝ)) / p * Real.log ((1 - (p : ℝ)) / (1 - (q : ℝ))) := by
  obtain ⟨hac, hllr⟩ := geometricMeasure_log_likelihood hp hp' hq hq'
  rw [InformationTheory.toReal_klDiv_of_measure_eq hac (by simp), integral_congr_ae hllr,
    integral_geometricMeasure hp]
  simp only [smul_eq_mul]
  exact (hasSum_geometric_log_likelihood hp _ _).tsum_eq

private theorem censored_log_likelihood_sum {p : unitInterval} (hp : p ≠ 0)
    (a b : ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, (1 - (p : ℝ)) ^ k * p * (a + k * b)) +
        (1 - (p : ℝ)) ^ n * (n * b) =
      (1 - (1 - (p : ℝ)) ^ n) * (a + (1 - (p : ℝ)) / p * b) := by
  have hp0 : (p : ℝ) ≠ 0 := unitInterval.coe_ne_zero.mpr hp
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← add_sub_cancel_right (∑ k ∈ Finset.range n,
        (1 - (p : ℝ)) ^ k * p * (a + k * b)) ((1 - (p : ℝ)) ^ n * (n * b)), ih, pow_succ]
    push_cast
    field_simp
    ring

/-- A retry cap retains the fraction `1 - (1 - p)^n` of the complete geometric KL. -/
theorem finiteKL_censoredGeometricPair (n : ℕ) {p q : unitInterval} (hp : p ≠ 0) (hp' : p ≠ 1)
    (hq : q ≠ 0) (hq' : q ≠ 1) :
    finiteKL (censoredGeometricPair n p q hq hq') =
      (1 - (1 - (p : ℝ)) ^ n) * (klDiv (geometricMeasure p) (geometricMeasure q)).toReal := by
  unfold finiteKL censoredGeometricPair
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_unique, censoredGeometric_event n hp, censoredGeometric_event n hq,
    censoredGeometric_tail n hp, censoredGeometric_tail n hq]
  simp_rw [log_mass_ratio hp hp' hq hq']
  rw [← div_pow, Real.log_pow, toReal_klDiv_geometricMeasure hp hp' hq hq']
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ ↦ (1 - (p : ℝ)) ^ k * p *
    (Real.log ((p : ℝ) / q) + k * Real.log ((1 - (p : ℝ)) / (1 - (q : ℝ))))) n]
  exact censored_log_likelihood_sum hp _ _ n

/-- The loss of real KL from censoring is the tail probability under the numerator
times the complete geometric relative entropy. -/
theorem toReal_klDiv_sub_finiteKL_censoredGeometricPair (n : ℕ) {p q : unitInterval}
    (hp : p ≠ 0) (hp' : p ≠ 1) (hq : q ≠ 0) (hq' : q ≠ 1) :
    (klDiv (geometricMeasure p) (geometricMeasure q)).toReal -
      finiteKL (censoredGeometricPair n p q hq hq') =
      (1 - (p : ℝ)) ^ n * (klDiv (geometricMeasure p) (geometricMeasure q)).toReal := by
  rw [finiteKL_censoredGeometricPair n hp hp' hq hq']
  ring

/-- The same exact loss for the measure-theoretic KL of the two pushforward laws. -/
theorem toReal_klDiv_sub_censoredGeometric_map (n : ℕ) {p q : unitInterval}
    (hp : p ≠ 0) (hp' : p ≠ 1) (hq : q ≠ 0) (hq' : q ≠ 1) :
    (klDiv (geometricMeasure p) (geometricMeasure q)).toReal -
      (klDiv ((geometricMeasure p).map (censor n)) ((geometricMeasure q).map (censor n))).toReal =
      (1 - (p : ℝ)) ^ n * (klDiv (geometricMeasure p) (geometricMeasure q)).toReal := by
  rw [← censoredGeometric_toMeasure n p, ← censoredGeometric_toMeasure n q]
  let pair := censoredGeometricPair n p q hq hq'
  change _ - (klDiv pair.numerator.toMeasure pair.reference.toMeasure).toReal = _
  rw [← finiteKL.eq_toReal_klDiv]
  exact toReal_klDiv_sub_finiteKL_censoredGeometricPair n hp hp' hq hq'

end FiniteRelativeEntropy
