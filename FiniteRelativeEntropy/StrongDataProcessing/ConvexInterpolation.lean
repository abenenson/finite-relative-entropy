/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Convex functions on a finite grid

On finitely many nonnegative knots a convex function agrees with an affine function plus a
finite sum of positive-part functions. Their weights are the successive increases in secant
slope. Empty and singleton grids are included.
-/

@[expose] public section

namespace FiniteRelativeEntropy.StrongDataProcessing.ConvexInterpolation

/-- Evaluate a finite weighted sum of positive-part hinges. Each pair records a knot and weight. -/
noncomputable def hinges : List (ℝ × ℝ) → ℝ → ℝ
  | [], _ => 0
  | (knot, weight) :: rest, x => weight * max (x - knot) 0 + hinges rest x

/-- The secant slope of `f` between two distinct grid points. -/
private noncomputable def secant (f : ℝ → ℝ) (a b : ℝ) : ℝ := (f b - f a) / (b - a)

/-- Evaluate one secant at the right endpoint. -/
private theorem secant_mul (f : ℝ → ℝ) {a b : ℝ} (hab : a < b) :
    secant f a b * (b - a) = f b - f a := div_mul_cancel₀ _ (sub_ne_zero.mpr hab.ne')

/-- Extend a secant line across a strictly ordered list using positive slope increments. -/
private theorem interpolate_tail (f : ℝ → ℝ) (hf : ConvexOn ℝ (Set.Ici 0) f)
    (tail : List ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hordered : (b :: tail).Pairwise (· < ·)) :
    ∃ w : List (ℝ × ℝ), (∀ v ∈ w, 0 ≤ v.2) ∧ (∀ x ≤ b, hinges w x = 0) ∧
      ∀ x ∈ tail, f x = f b + secant f a b * (x - b) + hinges w x := by
  induction tail generalizing a b with
  | nil => exact ⟨[], by simp, by simp [hinges], by simp⟩
  | cons z zs ih =>
    obtain ⟨hb, hzs⟩ := List.pairwise_cons.mp hordered
    have hbz : b < z := hb z (by simp)
    obtain ⟨w, hw, hzero, hinterp⟩ := ih (a := b) (b := z) (ha.trans hab.le) hbz hzs
    let changeSlope := secant f b z - secant f a b
    have hchange : 0 ≤ changeSlope :=
      sub_nonneg.mpr (hf.slope_mono_adjacent ha ((ha.trans hab.le).trans hbz.le) hab hbz)
    refine ⟨(b, changeSlope) :: w, ?_, ?_, ?_⟩
    · intro v hv
      rcases List.mem_cons.mp hv with hv | hv
      · simpa only [hv] using hchange
      · exact hw v hv
    · intro x hx
      simp only [hinges, max_eq_right (sub_nonpos.mpr hx), mul_zero,
        hzero x (hx.trans hbz.le), add_zero]
    · intro x hx
      have hsec := secant_mul f hbz
      rcases List.mem_cons.mp hx with hx | hx
      · subst x
        simp only [hinges, max_eq_left (sub_nonneg.mpr hbz.le), hzero z le_rfl, add_zero]
        dsimp only [changeSlope]
        linear_combination - hsec
      · have hzx : z < x := (List.pairwise_cons.mp hzs).1 x hx
        rw [hinterp x hx, hinges, max_eq_left (sub_nonneg.mpr (hbz.trans hzx).le)]
        dsimp only [changeSlope]
        linear_combination - hsec

/-- On a finite set of nonnegative knots, every real convex function agrees exactly with an
affine function plus finitely many nonnegative hinges. Empty and singleton grids are included. -/
theorem exists_affine_hinges (f : ℝ → ℝ) (hf : ConvexOn ℝ (Set.Ici 0) f)
    (s : Finset ℝ) (hs : ∀ x ∈ s, 0 ≤ x) :
    ∃ c d : ℝ, ∃ w : List (ℝ × ℝ), (∀ v ∈ w, 0 ≤ v.2) ∧
      ∀ x ∈ s, f x = c + d * x + hinges w x := by
  classical
  have ho := s.sortedLT_sort.pairwise
  have hmem (x : ℝ) : x ∈ s ↔ x ∈ s.sort := (s.mem_sort (· ≤ ·)).symm
  cases hl : s.sort with
  | nil =>
    refine ⟨0, 0, [], by simp, ?_⟩
    intro x hx
    have := (hmem x).mp hx
    simp [hl] at this
  | cons a tail =>
    cases tail with
    | nil =>
      refine ⟨f a, 0, [], by simp, ?_⟩
      intro x hx
      have hxa := (hmem x).mp hx
      simp only [hl, List.mem_singleton] at hxa
      simp [hxa, hinges]
    | cons b tail =>
      rw [hl] at ho
      obtain ⟨ha', ht⟩ := List.pairwise_cons.mp ho
      have hab : a < b := ha' b (by simp)
      have ha := hs a ((hmem a).mpr (by simp [hl]))
      obtain ⟨w, hw, hzero, htail⟩ := interpolate_tail f hf tail ha hab ht
      refine ⟨f b - secant f a b * b, secant f a b, w, hw, ?_⟩
      intro x hx
      have hx' := (hmem x).mp hx
      simp only [hl, List.mem_cons] at hx'
      rcases hx' with hxa | hxb | hx'
      · rw [hxa, hzero a hab.le]
        linear_combination secant_mul f hab
      · rw [hxb, hzero b le_rfl]
        ring
      · rw [htail x hx']
        ring

end FiniteRelativeEntropy.StrongDataProcessing.ConvexInterpolation
