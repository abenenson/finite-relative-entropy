/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Max
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Contraction of centered hockey-stick divergences

For signed masses, the excess above their total positive part can be tested on an event.
Bounding the oscillation of each row's probability of that event controls the excess after
applying the channel. The half-ℓ¹ row distance gives the usual total-variation coefficient.
-/

@[expose] public section

open scoped BigOperators

namespace FiniteRelativeEntropy.StrongDataProcessing.HockeyStick

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- A centered one-sided discrepancy. For `r = p - t*q`, this is the centered hockey stick. -/
noncomputable def excess (r : X → ℝ) : ℝ := (∑ x, max (r x) 0) - max (∑ x, r x) 0

/-- Applying a finite row-stochastic channel to signed weights. -/
noncomputable def push (r : X → ℝ) (K : X → Y → ℝ) (y : Y) : ℝ := ∑ x, r x * K x y

private theorem test_nonpositive [Nonempty X] (r f : X → ℝ) {η : ℝ}
    (hs : (∑ x, r x) ≤ 0) (hf : ∀ x, 0 ≤ f x) (hosc : ∀ x x', f x - f x' ≤ η) :
    (∑ x, r x * f x) ≤ η * ∑ x, max (r x) 0 := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
  have hmin (x : X) : 0 ≤ f x - f i := sub_nonneg.mpr (hi x (Finset.mem_univ _))
  have hcenter (x : X) : r x * (f x - f i) ≤ η * max (r x) 0 := by
    calc
      r x * (f x - f i) ≤ max (r x) 0 * (f x - f i) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (hmin x)
      _ ≤ max (r x) 0 * η := mul_le_mul_of_nonneg_left (hosc x i) (le_max_right _ _)
      _ = η * max (r x) 0 := mul_comm _ _
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun x _ ↦ hcenter x)
  simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum] at hsum
  linarith [mul_nonpos_of_nonpos_of_nonneg hs (hf i)]

private theorem test_bound [Nonempty X] (r f : X → ℝ) {η : ℝ}
    (hlo : ∀ x, 0 ≤ f x) (hhi : ∀ x, f x ≤ 1) (hosc : ∀ x x', f x - f x' ≤ η) :
    (∑ x, r x * f x) - max (∑ x, r x) 0 ≤ η * excess r := by
  unfold excess
  by_cases hs : (∑ x, r x) ≤ 0
  · simpa only [max_eq_right hs, sub_zero] using test_nonpositive r f hs hlo hosc
  · have hspos := lt_of_not_ge hs
    rw [max_eq_left hspos.le]
    have hneg : (∑ x, -(r x)) ≤ 0 := by rw [Finset.sum_neg_distrib]; linarith
    have hh := test_nonpositive (η := η) (fun x ↦ -r x) (fun x ↦ 1 - f x) hneg
      (fun x ↦ sub_nonneg.mpr (hhi x)) (fun x x' ↦ by linarith [hosc x' x])
    have hleft (x : X) : (-r x) * (1 - f x) = r x * f x - r x := by ring
    have hright (x : X) : max (-r x) 0 = max (r x) 0 - r x := by
      by_cases h : 0 ≤ r x
      · rw [max_eq_right (neg_nonpos.mpr h), max_eq_left h, sub_self]
      · have h' := le_of_not_ge h
        rw [max_eq_left (neg_nonneg.mpr h'), max_eq_right h', zero_sub]
    simpa only [hleft, hright, Finset.sum_sub_distrib] using hh

omit [Fintype Y] in
private theorem sum_push_on (r : X → ℝ) (K : X → Y → ℝ) (s : Finset Y) :
    (∑ y ∈ s, push r K y) = ∑ x, r x * ∑ y ∈ s, K x y := by
  unfold push
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

/-- The centered hockey stick contracts under a finite channel with row-event oscillation
at most `η`. Signed inputs of either total mass and zero rows of the input are included. -/
theorem excess_push_le (r : X → ℝ) (K : X → Y → ℝ) {η : ℝ}
    (h0 : ∀ x y, 0 ≤ K x y) (h1 : ∀ x, ∑ y, K x y = 1)
    (hrows : ∀ x x' (s : Finset Y), (∑ y ∈ s, K x y) - (∑ y ∈ s, K x' y) ≤ η) :
    excess (push r K) ≤ η * excess r := by
  classical
  cases isEmpty_or_nonempty X with
  | inl _ => simp [excess, push]
  | inr _ =>
    let s := Finset.univ.filter (fun y ↦ 0 < push r K y)
    let f := fun x ↦ ∑ y ∈ s, K x y
    have hf0 (x : X) : 0 ≤ f x := Finset.sum_nonneg (fun y _ ↦ h0 x y)
    have hf1 (x : X) : f x ≤ 1 := by
      rw [← h1 x]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) (fun y _ _ ↦ h0 x y)
    have hsum : (∑ y, push r K y) = ∑ x, r x := by
      simpa only [h1, mul_one] using sum_push_on r K Finset.univ
    have hpos : (∑ y, max (push r K y) 0) = ∑ y ∈ s, push r K y := by
      unfold s
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun y _ ↦ ?_
      split_ifs with hy
      · exact max_eq_left hy.le
      · exact max_eq_right (le_of_not_gt hy)
    change (∑ y, max (push r K y) 0) - max (∑ y, push r K y) 0 ≤ _
    rw [hpos, hsum, sum_push_on]
    exact test_bound r f hf0 hf1 (fun x x' ↦ hrows x x' s)

/-- Row-event oscillation is at most the usual half-ℓ¹ total-variation distance. -/
private theorem event_le_row_tv (a b : Y → ℝ) (ha : ∑ y, a y = 1) (hb : ∑ y, b y = 1)
    (s : Finset Y) :
    (∑ y ∈ s, a y) - (∑ y ∈ s, b y) ≤ (∑ y, |a y - b y|) / 2 := by
  have hsum : (∑ y, (a y - b y)) = 0 := by rw [Finset.sum_sub_distrib, ha, hb, sub_self]
  have hpoint (y : Y) : 2 * max (a y - b y) 0 = |a y - b y| + (a y - b y) := by
    rcases le_total 0 (a y - b y) with h | h
    · rw [max_eq_left h, abs_of_nonneg h]; ring
    · rw [max_eq_right h, abs_of_nonpos h]; ring
  have hdouble : 2 * ∑ y, max (a y - b y) 0 = ∑ y, |a y - b y| := by
    simp_rw [Finset.mul_sum, hpoint, Finset.sum_add_distrib, hsum, add_zero]
  have hpos : (∑ y ∈ s, max (a y - b y) 0) ≤ ∑ y, max (a y - b y) 0 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) (fun _ _ _ ↦ le_max_right _ _)
  rw [← Finset.sum_sub_distrib]
  have hle := Finset.sum_le_sum (s := s) (fun y _ ↦ le_max_left (a y - b y) 0)
  linarith

/-- Every centered hockey-stick excess contracts by the maximal row total-variation bound,
including thresholds below one, above one, and zero. -/
theorem centered_hockeyStick_le (p q : X → ℝ) (t : ℝ) (K : X → Y → ℝ) {η : ℝ}
    (h0 : ∀ x y, 0 ≤ K x y) (h1 : ∀ x, ∑ y, K x y = 1)
    (hTV : ∀ x x', (∑ y, |K x y - K x' y|) / 2 ≤ η) :
    excess (fun y ↦ push p K y - t * push q K y) ≤ η * excess (fun x ↦ p x - t * q x) := by
  have hlin (y : Y) : push (fun x ↦ p x - t * q x) K y = push p K y - t * push q K y := by
    simp only [push, sub_mul, Finset.sum_sub_distrib, mul_assoc, Finset.mul_sum]
  simp_rw [← hlin]
  exact excess_push_le _ K h0 h1 fun x x' s ↦
    (event_le_row_tv (K x) (K x') (h1 x) (h1 x') s).trans (hTV x x')

end FiniteRelativeEntropy.StrongDataProcessing.HockeyStick
