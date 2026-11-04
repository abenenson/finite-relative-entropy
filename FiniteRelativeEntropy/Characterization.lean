/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import FiniteRelativeEntropy.Basic

/-!
# Characterization of finite relative entropy

This file formalizes Theorem II.1 of Tom Leinster, *A short characterization of relative entropy*
(2019). A real-valued family on finite absolutely-continuous probability pairs is a common scalar
multiple of finite KL when it is measurable in the reference, invariant under relabeling, vanishes
on the diagonal, and obeys the dependent chain rule.

## Main results

- `RelativeEntropyFamily`: the four hypotheses of Leinster's theorem.
- `RelativeEntropyFamily.zeroTail`: support normalization (Leinster Lemma II.2).
- `RelativeEntropyFamily.probe_mul`: the multiplicative Cauchy equation (Lemma II.3).
- `RelativeEntropyFamily.probe_eq_neg_mul_log`: identification of the probe (Lemma II.4).
- `RelativeEntropyFamily.eq_mul_finiteKL_of_fullSupport`: the doubled construction (Lemma II.5).
- `RelativeEntropyFamily.characterization`: Leinster's characterization theorem.
-/

namespace FiniteRelativeEntropy

open FiniteMarkovKernels

open scoped BigOperators NNReal

/-- A finite relative-information family satisfying Leinster's four exact hypotheses. -/
structure RelativeEntropyFamily where
  /-- The value on an admissible pair over any finite alphabet. -/
  value : ∀ {A : Type} [Fintype A], AdmissiblePair A → ℝ
  /-- Measurability in the reference distribution for each fixed numerator. -/
  measurable_reference : ∀ {A : Type} [Fintype A] (p : ProbabilityVector A),
    Measurable fun r : AdmissibleReference p ↦ value ⟨p, r.1, r.2⟩
  /-- Invariance under simultaneous relabeling of the two distributions. -/
  permutation_invariant : ∀ {A B : Type} [Fintype A] [Fintype B]
    (e : A ≃ B) (P : AdmissiblePair A), value (P.relabel e) = value P
  /-- Vanishing on diagonal pairs. -/
  vanishing : ∀ {A : Type} [Fintype A] (p : ProbabilityVector A),
    value (AdmissiblePair.diagonal p) = 0
  /-- The full dependent block-composition chain rule. -/
  chain_rule : ∀ {A : Type} [Fintype A] {C : A → Type}
    [∀ a, Fintype (C a)] (outer : AdmissiblePair A) (inner : ∀ a, AdmissiblePair (C a)),
    value (outer.compound inner) =
      value outer + ∑ a, outer.numerator a * value (inner a)

namespace RelativeEntropyFamily

instance : CoeFun RelativeEntropyFamily fun _ ↦
    ∀ {A : Type} [Fintype A], AdmissiblePair A → ℝ :=
  ⟨RelativeEntropyFamily.value⟩

/-- Finite KL itself satisfies Leinster's four hypotheses. -/
noncomputable def finiteKLFamily : RelativeEntropyFamily where
  value := finiteKL
  measurable_reference := finiteKL.measurable_reference
  permutation_invariant := finiteKL.relabel
  vanishing := finiteKL.diagonal
  chain_rule := finiteKL.compound

/-- The admissible binary pair used to probe a relative-information family. -/
noncomputable def probePair (a : ℝ) (ha : a ∈ Set.Ioc (0 : ℝ) 1) : AdmissiblePair Bool where
  numerator := ProbabilityVector.dirac false
  reference := ProbabilityVector.boolBinary a ⟨ha.1.le, ha.2⟩
  absolutelyContinuous := by
    intro b hb
    cases b
    · change a = 0 at hb
      exact (ha.1.ne' hb).elim
    · simp [ProbabilityVector.dirac_apply]

/-- Leinster's binary probe `L(a) = I((1,0) || (a,1-a))`. -/
noncomputable def probe (I : RelativeEntropyFamily)
    (a : ℝ) (ha : a ∈ Set.Ioc (0 : ℝ) 1) : ℝ :=
  I (probePair a ha)

/-- The binary probe, regarded as a function on `(0,1]`. -/
noncomputable def probeOnIoc (I : RelativeEntropyFamily) : Set.Ioc (0 : ℝ) 1 → ℝ :=
  fun a ↦ I.probe a.1 a.2

/-- The paper's reference-measurability hypothesis makes the binary probe measurable. -/
theorem measurable_probeOnIoc (I : RelativeEntropyFamily) : Measurable I.probeOnIoc := by
  let numerator : ProbabilityVector Bool := ProbabilityVector.dirac false
  let embed : Set.Ioc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1 :=
    fun a ↦ ⟨a.1, a.2.1.le, a.2.2⟩
  have hembed : Measurable embed := by
    exact Measurable.subtype_mk measurable_subtype_coe
  have href : Measurable fun a : Set.Ioc (0 : ℝ) 1 ↦
      ProbabilityVector.boolBinary a.1 ⟨a.2.1.le, a.2.2⟩ := by
    exact ProbabilityVector.measurable_boolBinary.comp hembed
  have hadmissible : ∀ a : Set.Ioc (0 : ℝ) 1,
      numerator.AbsolutelyContinuous
        (ProbabilityVector.boolBinary a.1 ⟨a.2.1.le, a.2.2⟩) := by
    intro a b hb
    cases b
    · change a.1 = 0 at hb
      exact (a.2.1.ne' hb).elim
    · simp [numerator, ProbabilityVector.dirac_apply]
  have hreference : Measurable fun a : Set.Ioc (0 : ℝ) 1 ↦
      (⟨ProbabilityVector.boolBinary a.1 ⟨a.2.1.le, a.2.2⟩, hadmissible a⟩ :
        AdmissibleReference numerator) :=
    href.subtype_mk
  exact (I.measurable_reference numerator).comp hreference

/-- Restrict an admissible pair to the positive support of its numerator and normalize the
reference there. -/
noncomputable def onSupportPair {A : Type} [Fintype A] (P : AdmissiblePair A) :
    AdmissiblePair P.numerator.Support where
  numerator := P.numerator.onSupport
  reference := ProbabilityVector.referenceOnSupport
    P.numerator P.reference P.absolutelyContinuous
  absolutelyContinuous := ProbabilityVector.onSupport_absolutelyContinuous
    P.absolutelyContinuous

/-- The two fibres separating the support of `p` from its complement. -/
abbrev SupportFiber {A : Type} [Fintype A] (p : ProbabilityVector A) (b : Bool) : Type :=
  Bool.rec p.Support p.SupportComplement b

/-- The original finite instances on the support and its complement, indexed by the bit. -/
noncomputable instance supportFiberFintype {A : Type} [Fintype A]
    (p : ProbabilityVector A) (b : Bool) : Fintype (SupportFiber p b) :=
  Bool.rec inferInstance inferInstance b

/-- The dependent binary support split is equivalent to the original alphabet. -/
noncomputable def supportSigmaEquiv {A : Type} [Fintype A] (p : ProbabilityVector A) :
    (Σ b, SupportFiber p b) ≃ A :=
  Equiv.ofBijective
    (fun z ↦ Bool.rec (fun a : p.Support ↦ a.1)
      (fun a : p.SupportComplement ↦ a.1) z.1 z.2)
    ⟨by
      rintro ⟨b, a⟩ ⟨c, d⟩ h
      cases b <;> cases c
      · change a.1 = d.1 at h
        cases Subtype.ext h
        rfl
      · change a.1 = d.1 at h
        exfalso
        apply d.2
        rw [← h]
        exact a.2
      · change a.1 = d.1 at h
        exfalso
        apply a.2
        rw [h]
        exact d.2
      · change a.1 = d.1 at h
        cases Subtype.ext h
        rfl,
      (by
        intro a
        by_cases h : 0 < p a
        · exact ⟨⟨false, ⟨a, h⟩⟩, rfl⟩
        · exact ⟨⟨true, ⟨a, h⟩⟩, rfl⟩)⟩

@[simp]
private theorem supportSigmaEquiv_symm_apply_of_pos {A : Type} [Fintype A]
    (p : ProbabilityVector A) {a : A} (ha : 0 < p a) :
    (supportSigmaEquiv p).symm a = ⟨false, ⟨a, ha⟩⟩ := by
  apply (supportSigmaEquiv p).injective
  rw [(supportSigmaEquiv p).apply_symm_apply]
  rfl

@[simp]
private theorem supportSigmaEquiv_symm_apply_of_not_pos {A : Type} [Fintype A]
    (p : ProbabilityVector A) {a : A} (ha : ¬0 < p a) :
    (supportSigmaEquiv p).symm a = ⟨true, ⟨a, ha⟩⟩ := by
  apply (supportSigmaEquiv p).injective
  rw [(supportSigmaEquiv p).apply_symm_apply]
  rfl

/-- The outer binary pair recording how much reference mass lies on numerator support. -/
noncomputable def supportOuterPair {A : Type} [Fintype A] (P : AdmissiblePair A) :
    AdmissiblePair Bool :=
  probePair (ProbabilityVector.supportMass P.numerator P.reference)
    ⟨ProbabilityVector.supportMass_pos P.absolutelyContinuous,
      ProbabilityVector.supportMass_le_one P.numerator P.reference⟩

/-- The inner pairs for the support/complement decomposition. -/
noncomputable def supportInnerPair {A : Type} [Fintype A] (P : AdmissiblePair A)
    [Nonempty P.numerator.SupportComplement] : ∀ b, AdmissiblePair (SupportFiber P.numerator b) :=
  fun b ↦ Bool.rec (onSupportPair P)
    (AdmissiblePair.diagonal <|
      ProbabilityVector.referenceOnSupportComplement P.numerator P.reference) b

private theorem support_reconstruction {A : Type} [Fintype A] (P : AdmissiblePair A)
    [Nonempty P.numerator.SupportComplement] :
    ((supportOuterPair P).compound (supportInnerPair P)).relabel
      (supportSigmaEquiv P.numerator) = P := by
  apply AdmissiblePair.ext
  · apply ProbabilityVector.ext
    intro a
    by_cases ha : 0 < P.numerator a
    · change ProbabilityVector.relabel (supportSigmaEquiv P.numerator)
          ((supportOuterPair P).compound (supportInnerPair P)).numerator a = P.numerator a
      rw [ProbabilityVector.relabel_apply,
        supportSigmaEquiv_symm_apply_of_pos P.numerator ha]
      simp only [AdmissiblePair.compound, ProbabilityVector.compound_apply]
      simp [supportOuterPair, supportInnerPair, probePair, onSupportPair,
        ProbabilityVector.dirac_apply]
    · have hpa : P.numerator a = 0 :=
        le_antisymm (not_lt.mp ha) (P.numerator.nonneg a)
      change ProbabilityVector.relabel (supportSigmaEquiv P.numerator)
          ((supportOuterPair P).compound (supportInnerPair P)).numerator a = P.numerator a
      rw [ProbabilityVector.relabel_apply,
        supportSigmaEquiv_symm_apply_of_not_pos P.numerator ha]
      simp only [AdmissiblePair.compound, ProbabilityVector.compound_apply]
      simp [supportOuterPair, supportInnerPair, probePair, hpa,
        ProbabilityVector.dirac_apply]
  · apply ProbabilityVector.ext
    intro a
    by_cases ha : 0 < P.numerator a
    · change ProbabilityVector.relabel (supportSigmaEquiv P.numerator)
          ((supportOuterPair P).compound (supportInnerPair P)).reference a = P.reference a
      rw [ProbabilityVector.relabel_apply,
        supportSigmaEquiv_symm_apply_of_pos P.numerator ha]
      simp only [AdmissiblePair.compound, ProbabilityVector.compound_apply]
      change ProbabilityVector.supportMass P.numerator P.reference *
          (P.reference a / ProbabilityVector.supportMass P.numerator P.reference) =
        P.reference a
      exact mul_div_cancel₀ (P.reference a) <|
        (ProbabilityVector.supportMass_pos P.absolutelyContinuous).ne'
    · change ProbabilityVector.relabel (supportSigmaEquiv P.numerator)
          ((supportOuterPair P).compound (supportInnerPair P)).reference a = P.reference a
      rw [ProbabilityVector.relabel_apply,
        supportSigmaEquiv_symm_apply_of_not_pos P.numerator ha]
      simp only [AdmissiblePair.compound, ProbabilityVector.compound_apply]
      change (1 - ProbabilityVector.supportMass P.numerator P.reference) *
          ProbabilityVector.referenceOnSupportComplement
            P.numerator P.reference ⟨a, ha⟩ = P.reference a
      exact ProbabilityVector.supportComplementMass_mul_referenceOnSupportComplement
        P.numerator P.reference ⟨a, ha⟩

/-- Support normalization, the type-indexed form of Leinster Lemma II.2. -/
theorem zeroTail (I : RelativeEntropyFamily) {A : Type} [Fintype A]
    (P : AdmissiblePair A) [Nonempty P.numerator.SupportComplement] :
    I P = I.probe (ProbabilityVector.supportMass P.numerator P.reference)
        ⟨ProbabilityVector.supportMass_pos P.absolutelyContinuous,
          ProbabilityVector.supportMass_le_one P.numerator P.reference⟩ +
      I (onSupportPair P) := by
  calc
    I P = I (((supportOuterPair P).compound (supportInnerPair P)).relabel
        (supportSigmaEquiv P.numerator)) := by rw [support_reconstruction P]
    _ = I ((supportOuterPair P).compound (supportInnerPair P)) :=
      I.permutation_invariant _ _
    _ = I (supportOuterPair P) +
        ∑ b, (supportOuterPair P).numerator b * I (supportInnerPair P b) :=
      I.chain_rule _ _
    _ = I.probe (ProbabilityVector.supportMass P.numerator P.reference)
          ⟨ProbabilityVector.supportMass_pos P.absolutelyContinuous,
            ProbabilityVector.supportMass_le_one P.numerator P.reference⟩ +
        I (onSupportPair P) := by
      rw [Fintype.sum_bool]
      change I (probePair _ _) +
          ((probePair _ _).numerator true * I (supportInnerPair P true) +
            (probePair _ _).numerator false * I (supportInnerPair P false)) = _
      unfold probe
      simp [probePair, supportInnerPair, ProbabilityVector.dirac_apply]

/-- The inner binary family used to evaluate the three-outcome experiment in two ways. -/
noncomputable def probeInnerPair (b : ℝ) (hb : b ∈ Set.Ioc (0 : ℝ) 1) :
    Bool → AdmissiblePair Bool :=
  fun x ↦ Bool.rec (probePair b hb)
    (AdmissiblePair.diagonal <| ProbabilityVector.dirac false) x

/-- The compound experiment in Leinster Lemma II.3. Its numerator is concentrated at
`(false, false)`, while its reference assigns that point mass `a * b`. -/
noncomputable def probeCompoundPair (a : ℝ) (ha : a ∈ Set.Ioc (0 : ℝ) 1)
    (b : ℝ) (hb : b ∈ Set.Ioc (0 : ℝ) 1) : AdmissiblePair (Σ _ : Bool, Bool) :=
  (probePair a ha).compound (probeInnerPair b hb)

private theorem probeCompound_support_eq (a : ℝ) (ha : a ∈ Set.Ioc (0 : ℝ) 1)
    (b : ℝ) (hb : b ∈ Set.Ioc (0 : ℝ) 1)
    (z : (probeCompoundPair a ha b hb).numerator.Support) :
    z.1 = ⟨false, false⟩ := by
  rcases z with ⟨⟨x, y⟩, hxy⟩
  cases x <;> cases y
  · rfl
  all_goals
    simp [probeCompoundPair, probeInnerPair, probePair, AdmissiblePair.compound,
      ProbabilityVector.dirac_apply] at hxy

private theorem probeCompound_supportMass (a : ℝ) (ha : a ∈ Set.Ioc (0 : ℝ) 1)
    (b : ℝ) (hb : b ∈ Set.Ioc (0 : ℝ) 1) :
    ProbabilityVector.supportMass (probeCompoundPair a ha b hb).numerator
      (probeCompoundPair a ha b hb).reference = a * b := by
  classical
  let z₀ : (probeCompoundPair a ha b hb).numerator.Support :=
    ⟨⟨false, false⟩, by
      simp [probeCompoundPair, probeInnerPair, probePair, AdmissiblePair.compound,
        ProbabilityVector.dirac_apply]⟩
  unfold ProbabilityVector.supportMass
  calc
    (∑ z : (probeCompoundPair a ha b hb).numerator.Support,
        (probeCompoundPair a ha b hb).reference z.1) =
        (probeCompoundPair a ha b hb).reference z₀.1 := by
      apply Finset.sum_eq_single z₀
      · intro z _hz hne
        exact (hne <| Subtype.ext <| probeCompound_support_eq a ha b hb z).elim
      · simp
    _ = a * b := by
      simp [z₀, probeCompoundPair, probeInnerPair, probePair, AdmissiblePair.compound,
        ProbabilityVector.boolBinary]

private theorem probeCompound_onSupport_eq_diagonal (a : ℝ)
    (ha : a ∈ Set.Ioc (0 : ℝ) 1) (b : ℝ) (hb : b ∈ Set.Ioc (0 : ℝ) 1) :
    onSupportPair (probeCompoundPair a ha b hb) =
      AdmissiblePair.diagonal (probeCompoundPair a ha b hb).numerator.onSupport := by
  apply AdmissiblePair.ext
  · rfl
  · apply ProbabilityVector.ext
    intro z
    have hz := probeCompound_support_eq a ha b hb z
    change (probeCompoundPair a ha b hb).reference z.1 /
        ProbabilityVector.supportMass (probeCompoundPair a ha b hb).numerator
          (probeCompoundPair a ha b hb).reference =
      (probeCompoundPair a ha b hb).numerator z.1
    rw [probeCompound_supportMass, hz]
    simp [probeCompoundPair, probeInnerPair, probePair, AdmissiblePair.compound,
      ProbabilityVector.dirac_apply, ProbabilityVector.boolBinary,
      div_self (mul_ne_zero ha.1.ne' hb.1.ne')]

/-- The binary probe satisfies the multiplicative Cauchy equation (Leinster Lemma II.3). -/
theorem probe_mul (I : RelativeEntropyFamily) (a : ℝ) (ha : a ∈ Set.Ioc (0 : ℝ) 1)
    (b : ℝ) (hb : b ∈ Set.Ioc (0 : ℝ) 1) :
    I.probe (a * b) ⟨mul_pos ha.1 hb.1, (mul_le_of_le_one_left hb.1.le ha.2).trans hb.2⟩ =
      I.probe a ha + I.probe b hb := by
  let P := probeCompoundPair a ha b hb
  let : Nonempty P.numerator.SupportComplement :=
    ⟨⟨⟨false, true⟩, by
      simp [P, probeCompoundPair, probeInnerPair, probePair, AdmissiblePair.compound,
        ProbabilityVector.dirac_apply]⟩⟩
  have htail := I.zeroTail P
  rw [probeCompound_onSupport_eq_diagonal, I.vanishing, add_zero] at htail
  have hmass : ProbabilityVector.supportMass P.numerator P.reference = a * b :=
    probeCompound_supportMass a ha b hb
  have htail' : I P = I.probe (a * b)
      ⟨mul_pos ha.1 hb.1, (mul_le_of_le_one_left hb.1.le ha.2).trans hb.2⟩ := by
    simpa only [hmass] using htail
  calc
    I.probe (a * b) _ = I P := htail'.symm
    _ = I (probePair a ha) +
        ∑ x, (probePair a ha).numerator x * I (probeInnerPair b hb x) :=
      I.chain_rule _ _
    _ = I.probe a ha + I.probe b hb := by
      rw [Fintype.sum_bool]
      unfold probe
      simp [probeInnerPair, probePair, ProbabilityVector.dirac_apply, I.vanishing]

/-- The binary probe vanishes at one. -/
theorem probe_one (I : RelativeEntropyFamily) :
    I.probe 1 ⟨zero_lt_one, le_rfl⟩ = 0 := by
  have h := I.probe_mul 1 ⟨zero_lt_one, le_rfl⟩ 1 ⟨zero_lt_one, le_rfl⟩
  have h' : I.probe 1 ⟨zero_lt_one, le_rfl⟩ =
      I.probe 1 ⟨zero_lt_one, le_rfl⟩ + I.probe 1 ⟨zero_lt_one, le_rfl⟩ := by
    simpa only [one_mul] using h
  linarith

/-- The exponential coordinate map from the nonnegative additive half-line to `(0,1]`. -/
noncomputable def expNegIoc (t : ℝ≥0) : Set.Ioc (0 : ℝ) 1 :=
  ⟨Real.exp (-(t : ℝ)), Real.exp_pos _, Real.exp_le_one_iff.mpr (neg_nonpos.mpr t.2)⟩

private theorem continuous_expNegIoc : Continuous expNegIoc := by
  apply Continuous.subtype_mk
  exact Real.continuous_exp.comp continuous_subtype_val.neg

/-- The probe in additive logarithmic coordinates on the nonnegative half-line. -/
noncomputable def logProbeHom (I : RelativeEntropyFamily) : ℝ≥0 →+ ℝ where
  toFun t := I.probeOnIoc (expNegIoc t)
  map_zero' := by
    simpa [probeOnIoc, expNegIoc] using I.probe_one
  map_add' x y := by
    have h := I.probe_mul (Real.exp (-(x : ℝ))) (expNegIoc x).2
      (Real.exp (-(y : ℝ))) (expNegIoc y).2
    simpa [probeOnIoc, expNegIoc, Real.exp_add, mul_comm] using h

private theorem measurable_logProbeHom (I : RelativeEntropyFamily) :
    Measurable I.logProbeHom := by
  exact I.measurable_probeOnIoc.comp continuous_expNegIoc.measurable

/-- Extend an additive map on nonnegative reals to its additive group completion on `ℝ`. -/
noncomputable def realAdditiveExtension (f : ℝ≥0 →+ ℝ) : ℝ →+ ℝ where
  toFun x := f (Real.toNNReal x) - f (Real.toNNReal (-x))
  map_zero' := by simp
  map_add' x y := by
    have hparts : Real.toNNReal (x + y) + Real.toNNReal (-x) + Real.toNNReal (-y) =
        Real.toNNReal x + Real.toNNReal y + Real.toNNReal (-(x + y)) := by
      apply NNReal.eq
      simp only [NNReal.coe_add, Real.coe_toNNReal']
      linarith [max_zero_sub_max_neg_zero_eq_self x,
        max_zero_sub_max_neg_zero_eq_self y,
        max_zero_sub_max_neg_zero_eq_self (x + y)]
    have hmap := congrArg f hparts
    simp only [map_add] at hmap
    linarith

private theorem measurable_realAdditiveExtension {f : ℝ≥0 →+ ℝ} (hf : Measurable f) :
    Measurable (realAdditiveExtension f) := by
  exact (hf.comp measurable_real_toNNReal).sub <|
    hf.comp (measurable_real_toNNReal.comp measurable_id.neg)

private theorem realAdditiveExtension_apply_eq_mul {f : ℝ≥0 →+ ℝ} (hf : Measurable f)
    (x : ℝ) : realAdditiveExtension f x = x * realAdditiveExtension f 1 := by
  have hcontinuous := MeasureTheory.Measure.AddMonoidHom.continuous_of_measurable
    (realAdditiveExtension f) (measurable_realAdditiveExtension hf)
  have hsmul := ((realAdditiveExtension f).toRealLinearMap hcontinuous).map_smul x (1 : ℝ)
  simpa [smul_eq_mul] using hsmul

/-- The common scalar selected by the measurable logarithmic probe. -/
noncomputable def probeScale (I : RelativeEntropyFamily) : ℝ :=
  realAdditiveExtension I.logProbeHom 1

private theorem logProbeHom_apply_eq_mul (I : RelativeEntropyFamily) (t : ℝ≥0) :
    I.logProbeHom t = (t : ℝ) * I.probeScale := by
  have h := realAdditiveExtension_apply_eq_mul I.measurable_logProbeHom (t : ℝ)
  have hneg : Real.toNNReal (-(t : ℝ)) = 0 :=
    Real.toNNReal_of_nonpos (neg_nonpos.mpr t.2)
  have hnegOne : Real.toNNReal (-1) = 0 := Real.toNNReal_of_nonpos (by norm_num)
  simpa [realAdditiveExtension, probeScale, hneg, hnegOne] using h

/-- Measurability identifies the multiplicative probe as a scalar logarithm
(Leinster Lemma II.4). -/
theorem probe_eq_neg_mul_log (I : RelativeEntropyFamily) (a : ℝ)
    (ha : a ∈ Set.Ioc (0 : ℝ) 1) :
    I.probe a ha = -I.probeScale * Real.log a := by
  let t : ℝ≥0 := ⟨-Real.log a, neg_nonneg.mpr <| Real.log_nonpos ha.1.le ha.2⟩
  have h := I.logProbeHom_apply_eq_mul t
  change I.probe (Real.exp (-(-Real.log a))) _ = (-Real.log a) * I.probeScale at h
  simpa only [neg_neg, Real.exp_log ha.1, neg_mul, mul_neg, mul_comm] using! h

/-- A uniformly admissible positive scale for Leinster's doubled-coordinate construction. -/
noncomputable def fullSupportScale {A : Type} [Fintype A] (P : AdmissiblePair A) : ℝ :=
  ∏ a, P.reference a

private theorem fullSupportScale_pos {A : Type} [Fintype A] (P : AdmissiblePair A)
    (hfull : P.numerator.FullSupport) : 0 < fullSupportScale P := by
  apply Finset.prod_pos
  intro a _ha
  exact hfull.reference P.absolutelyContinuous a

private theorem fullSupportScale_le_one {A : Type} [Fintype A] (P : AdmissiblePair A) :
    fullSupportScale P ≤ 1 := by
  apply Finset.prod_le_one₀
  · exact fun a _ha ↦ P.reference.nonneg a
  · exact fun a _ha ↦ P.reference.apply_le_one a

private theorem fullSupportScale_le_reference {A : Type} [Fintype A]
    (P : AdmissiblePair A) (a : A) : fullSupportScale P ≤ P.reference a := by
  classical
  let rest := ∏ x ∈ Finset.univ.erase a, P.reference x
  have hrest_nonneg : 0 ≤ rest :=
    Finset.prod_nonneg fun x _hx ↦ P.reference.nonneg x
  have hrest_le_one : rest ≤ 1 := by
    apply Finset.prod_le_one₀
    · exact fun x _hx ↦ P.reference.nonneg x
    · exact fun x _hx ↦ P.reference.apply_le_one x
  calc
    fullSupportScale P = P.reference a * rest := by
      exact (Finset.mul_prod_erase Finset.univ P.reference (Finset.mem_univ a)).symm
    _ ≤ P.reference a * 1 :=
      mul_le_mul_of_nonneg_left hrest_le_one (P.reference.nonneg a)
    _ = P.reference a := mul_one _

private theorem fullSupportScale_mul_numerator_le_reference {A : Type} [Fintype A]
    (P : AdmissiblePair A) (hfull : P.numerator.FullSupport) (a : A) :
    fullSupportScale P * P.numerator a ≤ P.reference a := by
  calc
    fullSupportScale P * P.numerator a ≤ fullSupportScale P * 1 :=
      mul_le_mul_of_nonneg_left (P.numerator.apply_le_one a) (fullSupportScale_pos P hfull).le
    _ = fullSupportScale P := mul_one _
    _ ≤ P.reference a := fullSupportScale_le_reference P a

private theorem fullSupportRatio_mem_Ioc {A : Type} [Fintype A]
    (P : AdmissiblePair A) (hfull : P.numerator.FullSupport) (a : A) :
    fullSupportScale P * P.numerator a / P.reference a ∈ Set.Ioc (0 : ℝ) 1 := by
  have href := hfull.reference P.absolutelyContinuous a
  exact ⟨div_pos (mul_pos (fullSupportScale_pos P hfull) (hfull a)) href,
    (div_le_one href).mpr (fullSupportScale_mul_numerator_le_reference P hfull a)⟩

/-- The coordinatewise binary experiments in Leinster Lemma II.5. -/
noncomputable def fullSupportInnerPair {A : Type} [Fintype A] (P : AdmissiblePair A)
    (hfull : P.numerator.FullSupport) (a : A) : AdmissiblePair Bool :=
  probePair (fullSupportScale P * P.numerator a / P.reference a)
    (fullSupportRatio_mem_Ioc P hfull a)

/-- The interleaved doubled-coordinate experiment used for the full-support case. -/
noncomputable def fullSupportCompoundPair {A : Type} [Fintype A] (P : AdmissiblePair A)
    (hfull : P.numerator.FullSupport) : AdmissiblePair (Σ _ : A, Bool) :=
  P.compound (fullSupportInnerPair P hfull)

private theorem fullSupportCompound_reference_eq_scale_mul_numerator
    {A : Type} [Fintype A] (P : AdmissiblePair A)
    (hfull : P.numerator.FullSupport)
    (z : (fullSupportCompoundPair P hfull).numerator.Support) :
    (fullSupportCompoundPair P hfull).reference z.1 =
      fullSupportScale P * (fullSupportCompoundPair P hfull).numerator z.1 := by
  rcases z with ⟨⟨a, b⟩, hz⟩
  cases b
  · have href := hfull.reference P.absolutelyContinuous a
    simp only [fullSupportCompoundPair, AdmissiblePair.compound,
      ProbabilityVector.compound_apply, fullSupportInnerPair, probePair,
      ProbabilityVector.boolBinary, ProbabilityVector.dirac_apply, ite_eq_left,
      Bool.false_eq_true, ite_false]
    field_simp
  · simp [fullSupportCompoundPair, fullSupportInnerPair, probePair,
      AdmissiblePair.compound, ProbabilityVector.dirac_apply] at hz

private theorem fullSupportCompound_supportMass {A : Type} [Fintype A]
    (P : AdmissiblePair A) (hfull : P.numerator.FullSupport) :
    ProbabilityVector.supportMass (fullSupportCompoundPair P hfull).numerator
      (fullSupportCompoundPair P hfull).reference = fullSupportScale P := by
  unfold ProbabilityVector.supportMass
  calc
    (∑ z : (fullSupportCompoundPair P hfull).numerator.Support,
        (fullSupportCompoundPair P hfull).reference z.1) =
        ∑ z, fullSupportScale P *
          (fullSupportCompoundPair P hfull).numerator.onSupport z := by
      apply Finset.sum_congr rfl
      intro z _hz
      exact fullSupportCompound_reference_eq_scale_mul_numerator P hfull z
    _ = fullSupportScale P *
        ∑ z, (fullSupportCompoundPair P hfull).numerator.onSupport z := by
      rw [Finset.mul_sum]
    _ = fullSupportScale P := by
      rw [(fullSupportCompoundPair P hfull).numerator.onSupport.sum_eq_one, mul_one]

private theorem fullSupportCompound_onSupport_eq_diagonal {A : Type} [Fintype A]
    (P : AdmissiblePair A) (hfull : P.numerator.FullSupport) :
    onSupportPair (fullSupportCompoundPair P hfull) =
      AdmissiblePair.diagonal (fullSupportCompoundPair P hfull).numerator.onSupport := by
  apply AdmissiblePair.ext
  · rfl
  · apply ProbabilityVector.ext
    intro z
    change (fullSupportCompoundPair P hfull).reference z.1 /
        ProbabilityVector.supportMass (fullSupportCompoundPair P hfull).numerator
          (fullSupportCompoundPair P hfull).reference =
      (fullSupportCompoundPair P hfull).numerator z.1
    rw [fullSupportCompound_supportMass,
      fullSupportCompound_reference_eq_scale_mul_numerator P hfull z]
    exact mul_div_cancel_left₀ _ (fullSupportScale_pos P hfull).ne'

private theorem fullSupport_probe_sum (I : RelativeEntropyFamily)
    {A : Type} [Fintype A] (P : AdmissiblePair A)
    (hfull : P.numerator.FullSupport) :
    (∑ a, P.numerator a * I (fullSupportInnerPair P hfull a)) =
      -I.probeScale * Real.log (fullSupportScale P) - I.probeScale * finiteKL P := by
  calc
    (∑ a, P.numerator a * I (fullSupportInnerPair P hfull a)) =
        ∑ a, P.numerator a *
          (-I.probeScale * Real.log
            (fullSupportScale P * P.numerator a / P.reference a)) := by
      apply Finset.sum_congr rfl
      intro a _ha
      change P.numerator a * I.probe
          (fullSupportScale P * P.numerator a / P.reference a) _ = _
      rw [I.probe_eq_neg_mul_log]
    _ = ∑ a, ((-I.probeScale * Real.log (fullSupportScale P)) * P.numerator a +
        (-I.probeScale) *
          (P.numerator a * Real.log (P.numerator a / P.reference a))) := by
      apply Finset.sum_congr rfl
      intro a _ha
      have href := hfull.reference P.absolutelyContinuous a
      rw [Real.log_div (mul_ne_zero (fullSupportScale_pos P hfull).ne' (hfull a).ne')
        href.ne', Real.log_mul (fullSupportScale_pos P hfull).ne' (hfull a).ne',
        Real.log_div (hfull a).ne' href.ne']
      ring
    _ = -I.probeScale * Real.log (fullSupportScale P) -
        I.probeScale * finiteKL P := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        P.numerator.sum_eq_one]
      unfold finiteKL
      ring

/-- The doubled-coordinate construction identifies the family on full-support numerators
(Leinster Lemma II.5). -/
theorem eq_mul_finiteKL_of_fullSupport (I : RelativeEntropyFamily)
    {A : Type} [Fintype A] (P : AdmissiblePair A)
    (hfull : P.numerator.FullSupport) : I P = I.probeScale * finiteKL P := by
  let α := fullSupportScale P
  let Q := fullSupportCompoundPair P hfull
  let a₀ : A := (Classical.choice (inferInstance : Nonempty P.numerator.Support)).1
  let : Nonempty Q.numerator.SupportComplement :=
    ⟨⟨⟨a₀, true⟩, by
      simp [Q, fullSupportCompoundPair, fullSupportInnerPair, probePair,
        AdmissiblePair.compound, ProbabilityVector.dirac_apply]⟩⟩
  have hα : α ∈ Set.Ioc (0 : ℝ) 1 :=
    ⟨fullSupportScale_pos P hfull, fullSupportScale_le_one P⟩
  have htail := I.zeroTail Q
  rw [fullSupportCompound_onSupport_eq_diagonal, I.vanishing, add_zero] at htail
  have hmass : ProbabilityVector.supportMass Q.numerator Q.reference = α :=
    fullSupportCompound_supportMass P hfull
  have htailProbe : I Q = I.probe α hα := by
    simpa only [hmass] using htail
  have htailValue : I Q = -I.probeScale * Real.log α :=
    htailProbe.trans (I.probe_eq_neg_mul_log α hα)
  have hchain : I Q = I P +
      ∑ a, P.numerator a * I (fullSupportInnerPair P hfull a) :=
    I.chain_rule P (fullSupportInnerPair P hfull)
  rw [I.fullSupport_probe_sum P hfull] at hchain
  linarith

private theorem finiteKL_probePair (a : ℝ) (ha : a ∈ Set.Ioc (0 : ℝ) 1) :
    finiteKL (probePair a ha) = -Real.log a := by
  unfold finiteKL
  rw [Fintype.sum_bool]
  simp [probePair, ProbabilityVector.dirac_apply, ProbabilityVector.boolBinary]

/-- **Leinster's characterization theorem**: every measurable, permutation-invariant,
diagonally vanishing family satisfying the dependent chain rule is one common real scalar multiple
of finite Kullback--Leibler divergence on every finite absolutely-continuous pair. -/
theorem characterization (I : RelativeEntropyFamily) {A : Type} [Fintype A]
    (P : AdmissiblePair A) : I P = I.probeScale * finiteKL P := by
  by_cases hfull : P.numerator.FullSupport
  · exact I.eq_mul_finiteKL_of_fullSupport P hfull
  · simp only [ProbabilityVector.FullSupport] at hfull
    push Not at hfull
    obtain ⟨a, ha⟩ := hfull
    let : Nonempty P.numerator.SupportComplement := ⟨⟨a, not_lt.mpr ha⟩⟩
    let s := ProbabilityVector.supportMass P.numerator P.reference
    have hs : s ∈ Set.Ioc (0 : ℝ) 1 :=
      ⟨ProbabilityVector.supportMass_pos P.absolutelyContinuous,
        ProbabilityVector.supportMass_le_one P.numerator P.reference⟩
    have honFull : (onSupportPair P).numerator.FullSupport := fun x ↦ x.2
    have hI := I.zeroTail P
    rw (transparency := .default)
      [I.probe_eq_neg_mul_log, I.eq_mul_finiteKL_of_fullSupport _ honFull] at hI
    have hKL := finiteKLFamily.zeroTail P
    change finiteKL P = finiteKL (probePair s hs) + finiteKL (onSupportPair P) at hKL
    rw [finiteKL_probePair] at hKL
    calc
      I P = -I.probeScale * Real.log s +
          I.probeScale * finiteKL (onSupportPair P) := hI
      _ = I.probeScale * finiteKL P := by rw [hKL]; ring

/-- Pointwise nonnegativity is an additional property, not one of Leinster's four axioms. -/
def Nonnegative (I : RelativeEntropyFamily) : Prop :=
  ∀ {A : Type} [Fintype A] (P : AdmissiblePair A), 0 ≤ I P

/-- The common scale is nonnegative only when pointwise nonnegativity is assumed separately. -/
theorem probeScale_nonneg (I : RelativeEntropyFamily) (hI : I.Nonnegative) :
    0 ≤ I.probeScale := by
  let a := Real.exp (-1)
  have ha : a ∈ Set.Ioc (0 : ℝ) 1 :=
    ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (by norm_num)⟩
  have hnonneg := hI (probePair a ha)
  change 0 ≤ I.probe a ha at hnonneg
  rw [I.probe_eq_neg_mul_log] at hnonneg
  simpa [a] using hnonneg

end RelativeEntropyFamily

end FiniteRelativeEntropy
