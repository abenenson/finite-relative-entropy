/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import FiniteRelativeEntropy.StrongDataProcessing.HockeyStick
public import FiniteRelativeEntropy.StrongDataProcessing.ConvexInterpolation
public import Mathlib.InformationTheory.KullbackLeibler.KLFun

/-!
# Finite convex divergences from one-sided discrepancies

For absolutely continuous finite probability laws, the likelihood ratios of the input and
output pairs and the number one form a finite grid. Convex interpolation on this grid writes
each normalized divergence as a nonnegative combination of centered hockey-stick excesses.
-/

@[expose] public section

namespace FiniteRelativeEntropy.StrongDataProcessing.FiniteDivergence

open scoped BigOperators
open HockeyStick ConvexInterpolation

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- The perspective sum on finite atom masses. For an absolutely continuous pair this is
the full convex divergence. The measure-level KL theorem treats singular inputs separately. -/
noncomputable def divergence (f : ℝ → ℝ) (p q : X → ℝ) : ℝ := ∑ x, q x * f (p x / q x)

/-- Evaluate the corresponding weighted sum of centered one-sided discrepancies. -/
private noncomputable def residualSum (p q : X → ℝ) (w : List (ℝ × ℝ)) : ℝ :=
  w.foldr (fun v total ↦ v.2 * excess (fun x ↦ p x - v.1 * q x) + total) 0

private theorem residualSum_cons (p q : X → ℝ) (t c : ℝ) (w : List (ℝ × ℝ)) :
    residualSum p q ((t, c) :: w) =
      c * excess (fun x ↦ p x - t * q x) + residualSum p q w := rfl

omit [Fintype X] in
/-- Absolute continuity recovers the numerator even at an atom of zero reference mass. -/
private theorem recover (p q : X → ℝ) (hac : ∀ x, q x = 0 → p x = 0) (x : X) :
    q x * (p x / q x) = p x := by
  by_cases h : q x = 0
  · simp [h, hac x h]
  · rw [mul_comm, div_mul_cancel₀ _ h]

omit [Fintype X] in
/-- A hinge in likelihood-ratio space is a positive part in signed-mass space. -/
private theorem recover_hinge (p q : X → ℝ) (hq : ∀ x, 0 ≤ q x)
    (hac : ∀ x, q x = 0 → p x = 0) (t : ℝ) (x : X) :
    q x * max (p x / q x - t) 0 = max (p x - t * q x) 0 := by
  rw [mul_max_of_nonneg _ _ (hq x), mul_zero, mul_sub, recover p q hac, mul_comm (q x) t]

/-- Integration of hinged functions centered at one is a sum of centered signed-mass excesses. -/
private theorem centered_hinges (p q : X → ℝ) (hq : ∀ x, 0 ≤ q x)
    (hp1 : ∑ x, p x = 1) (hq1 : ∑ x, q x = 1) (hac : ∀ x, q x = 0 → p x = 0)
    (w : List (ℝ × ℝ)) :
    (∑ x, q x * hinges w (p x / q x)) - hinges w 1 = residualSum p q w := by
  induction w with
  | nil => simp [hinges, residualSum]
  | cons v w ih =>
    obtain ⟨t, c⟩ := v
    have hmass : (∑ x, (p x - t * q x)) = 1 - t := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hp1, hq1, mul_one]
    have hpoint (x : X) :
        q x * (c * max (p x / q x - t) 0 + hinges w (p x / q x)) =
        c * max (p x - t * q x) 0 + q x * hinges w (p x / q x) := by
      rw [mul_add, mul_left_comm (q x) c, recover_hinge p q hq hac]
    simp only [hinges, residualSum_cons, hpoint, Finset.sum_add_distrib, ← Finset.mul_sum,
      excess, hmass, ← ih]
    ring

/-- An affine term cancels at unit mass. The remaining divergence is a weighted sum of excesses. -/
private theorem divergence_spline (f : ℝ → ℝ) (p q : X → ℝ) (hq : ∀ x, 0 ≤ q x)
    (hp1 : ∑ x, p x = 1) (hq1 : ∑ x, q x = 1) (hac : ∀ x, q x = 0 → p x = 0)
    {c d : ℝ} {w : List (ℝ × ℝ)} (hf1 : f 1 = c + d + hinges w 1)
    (hmatch : ∀ x, f (p x / q x) = c + d * (p x / q x) + hinges w (p x / q x)) :
    divergence f p q - f 1 = residualSum p q w := by
  have hpoint (x : X) :
      q x * f (p x / q x) = c * q x + d * p x + q x * hinges w (p x / q x) := by
    rw [hmatch, mul_add, mul_add, mul_left_comm (q x) d, recover p q hac, mul_comm (q x) c]
  unfold divergence
  simp only [hpoint, Finset.sum_add_distrib, ← Finset.mul_sum, hp1, hq1, mul_one, hf1]
  rw [← centered_hinges p q hq hp1 hq1 hac]
  ring

/-- Nonnegative linear combinations preserve the same contraction factor. -/
private theorem residualSum_le (p q : X → ℝ) (p' q' : Y → ℝ) {η : ℝ}
    (ht : ∀ t, excess (fun y ↦ p' y - t * q' y) ≤ η * excess (fun x ↦ p x - t * q x))
    (w : List (ℝ × ℝ)) (hw : ∀ v ∈ w, 0 ≤ v.2) :
    residualSum p' q' w ≤ η * residualSum p q w := by
  induction w with
  | nil => simp [residualSum]
  | cons v w ih =>
    obtain ⟨t, c⟩ := v
    have hc : 0 ≤ c := hw (t, c) (by simp)
    have hrest := ih (fun v hv ↦ hw v (List.mem_cons_of_mem _ hv))
    have hfirst := mul_le_mul_of_nonneg_left (ht t) hc
    simp only [residualSum_cons]
    linarith [mul_add η (c * excess (fun x ↦ p x - t * q x)) (residualSum p q w),
      mul_left_comm η c (excess (fun x ↦ p x - t * q x))]

/-- Centered hockey-stick inequalities imply every normalized convex finite divergence
inequality. One finite grid contains both sets of likelihood ratios and the point one. -/
theorem of_centered_hinges (f : ℝ → ℝ) (hf : ConvexOn ℝ (Set.Ici 0) f) (hf1 : f 1 = 0)
    (p q : X → ℝ) (p' q' : Y → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x) (hp' : ∀ y, 0 ≤ p' y) (hq' : ∀ y, 0 ≤ q' y)
    (hp1 : ∑ x, p x = 1) (hq1 : ∑ x, q x = 1) (hp1' : ∑ y, p' y = 1) (hq1' : ∑ y, q' y = 1)
    (hac : ∀ x, q x = 0 → p x = 0) (hac' : ∀ y, q' y = 0 → p' y = 0) {η : ℝ}
    (ht : ∀ t, excess (fun y ↦ p' y - t * q' y) ≤ η * excess (fun x ↦ p x - t * q x)) :
    divergence f p' q' ≤ η * divergence f p q := by
  classical
  let s := insert 1 ((Finset.univ.image fun x ↦ p x / q x) ∪
    (Finset.univ.image fun y ↦ p' y / q' y))
  have hs : ∀ t ∈ s, 0 ≤ t := by
    intro t h
    rcases Finset.mem_insert.mp h with h | h
    · rw [h]; exact zero_le_one
    · rcases Finset.mem_union.mp h with h | h
      · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp h
        exact div_nonneg (hp x) (hq x)
      · obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp h
        exact div_nonneg (hp' y) (hq' y)
  obtain ⟨c, d, w, hw, hmatch⟩ := exists_affine_hinges f hf s hs
  have hone : f 1 = c + d + hinges w 1 := by
    simpa only [mul_one] using hmatch 1 (Finset.mem_insert_self 1 _)
  have hinput (x : X) := hmatch (p x / q x) (Finset.mem_insert_of_mem <| Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩))
  have houtput (y : Y) := hmatch (p' y / q' y) (Finset.mem_insert_of_mem <| Finset.mem_union_right _
    (Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩))
  have hdiv := divergence_spline f p q hq hp1 hq1 hac hone hinput
  have hdiv' := divergence_spline f p' q' hq' hp1' hq1' hac' hone houtput
  rw [hf1, sub_zero] at hdiv hdiv'
  rw [hdiv, hdiv']
  exact residualSum_le p q p' q' ht w hw

end FiniteRelativeEntropy.StrongDataProcessing.FiniteDivergence
