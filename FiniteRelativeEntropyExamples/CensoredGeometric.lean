/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import FiniteRelativeEntropy.CensoredGeometric

/-! # A capped retry observation

A client makes at most two independent attempts. It observes a first- or second-attempt success,
or a timeout after the second failure. A success hazard of `2/3` against a reference hazard of
`1/3` loses exactly `log 2 / 18` in KL when the client keeps only this record.
-/

@[expose] public section

open InformationTheory ProbabilityTheory

namespace FiniteRelativeEntropy.Examples

/-- Without any attempts the observation is always the tail. -/
theorem no_attempts_tail (k : ℕ) :
    CensoredWaitingTime.censor 0 k = Sum.inr PUnit.unit := by
  simp [CensoredWaitingTime.censor]

/-- With an empty observation window the finite comparison has zero KL. -/
theorem no_attempts_kl {p q : unitInterval} (hp : p ≠ 0) (hp' : p ≠ 1)
    (hq : q ≠ 0) (hq' : q ≠ 1) : finiteKL (censoredGeometricPair 0 p q hq hq') = 0 := by
  simp [finiteKL_censoredGeometricPair 0 hp hp' hq hq']

/-- Two equal hazards have no censoring loss at any cap. -/
theorem equal_hazard_loss (n : ℕ) (p : unitInterval) :
    (klDiv (geometricMeasure p) (geometricMeasure p)).toReal -
      (klDiv ((geometricMeasure p).map (CensoredWaitingTime.censor n))
        ((geometricMeasure p).map (CensoredWaitingTime.censor n))).toReal = 0 := by
  rw [klDiv_self, ← censoredGeometric_toMeasure, klDiv_self]
  simp

private noncomputable def twoThirds : unitInterval := ⟨2 / 3, by constructor <;> norm_num⟩
private noncomputable def oneThird : unitInterval := ⟨1 / 3, by constructor <;> norm_num⟩

private theorem twoThirds_ne_zero : twoThirds ≠ 0 :=
  unitInterval.coe_ne_zero.mp (by norm_num [twoThirds])

private theorem twoThirds_ne_one : twoThirds ≠ 1 :=
  unitInterval.coe_ne_one.mp (by norm_num [twoThirds])

private theorem oneThird_ne_zero : oneThird ≠ 0 :=
  unitInterval.coe_ne_zero.mp (by norm_num [oneThird])

private theorem oneThird_ne_one : oneThird ≠ 1 :=
  unitInterval.coe_ne_one.mp (by norm_num [oneThird])

/-- At success hazard `2/3`, the second-attempt success and timeout masses are `2/9` and `1/9`. -/
theorem two_attempt_masses :
    let p : unitInterval := ⟨2 / 3, by constructor <;> norm_num⟩
    censoredGeometric 2 p (Sum.inl ⟨1, by decide⟩) = 2 / 9 ∧
      censoredGeometric 2 p (Sum.inr PUnit.unit) = 1 / 9 := by
  change censoredGeometric 2 twoThirds (Sum.inl ⟨1, by decide⟩) = _ ∧
    censoredGeometric 2 twoThirds (Sum.inr PUnit.unit) = _
  rw [censoredGeometric_event 2 twoThirds_ne_zero, censoredGeometric_tail 2 twoThirds_ne_zero]
  norm_num [twoThirds]

/-- Two capped attempts lose exactly `log 2 / 18` for hazards `2/3` and `1/3`. -/
theorem two_attempt_loss :
    let p : unitInterval := ⟨2 / 3, by constructor <;> norm_num⟩
    let q : unitInterval := ⟨1 / 3, by constructor <;> norm_num⟩
    (klDiv (geometricMeasure p) (geometricMeasure q)).toReal -
      (klDiv ((geometricMeasure p).map (CensoredWaitingTime.censor 2))
        ((geometricMeasure q).map (CensoredWaitingTime.censor 2))).toReal = Real.log 2 / 18 := by
  change (klDiv (geometricMeasure twoThirds) (geometricMeasure oneThird)).toReal -
    (klDiv ((geometricMeasure twoThirds).map (CensoredWaitingTime.censor 2))
      ((geometricMeasure oneThird).map (CensoredWaitingTime.censor 2))).toReal = _
  rw [toReal_klDiv_sub_censoredGeometric_map 2 twoThirds_ne_zero twoThirds_ne_one
      oneThird_ne_zero oneThird_ne_one,
    toReal_klDiv_geometricMeasure twoThirds_ne_zero twoThirds_ne_one
      oneThird_ne_zero oneThird_ne_one]
  norm_num [twoThirds, oneThird]
  rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.log_inv]
  ring

end FiniteRelativeEntropy.Examples
