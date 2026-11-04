/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
import FiniteRelativeEntropy.Basic
import FiniteRelativeEntropy.GibbsVariational
import FiniteRelativeEntropy.Characterization

/-!
# Finite relative entropy and Gibbs variational identities

Public import for finite KL on absolutely continuous probability pairs, its Gibbs variational
identity and minimizer, and Leinster's characterization. The shared finite probability type
comes from `FiniteMarkovKernels`; no SFT or selection interface is imported.
-/
