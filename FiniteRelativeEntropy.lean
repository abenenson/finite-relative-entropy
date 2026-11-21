/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import FiniteRelativeEntropy.Basic
public import FiniteRelativeEntropy.GibbsVariational
public import FiniteRelativeEntropy.Characterization
public import FiniteRelativeEntropy.StrongDataProcessing

/-!
# Finite relative entropy

Public import for finite KL on absolutely continuous probability pairs, the Gibbs variational
identity, Leinster's characterization, and strong contraction under finite Markov kernels.
The shared finite probability type comes from `FiniteMarkovKernels`.
-/

@[expose] public section
