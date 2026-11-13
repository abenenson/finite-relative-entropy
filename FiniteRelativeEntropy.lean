/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import FiniteRelativeEntropy.Basic
public import FiniteRelativeEntropy.GibbsVariational
public import FiniteRelativeEntropy.Characterization

/-!
# Finite relative entropy and Gibbs variational identities

Public import for finite KL on absolutely continuous probability pairs, its Gibbs variational
identity and minimizer, and Leinster's characterization. The shared finite probability type
comes from `FiniteMarkovKernels`; no the library or selection interface is imported.
-/

@[expose] public section
