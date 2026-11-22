# Mathematical attribution and Mathlib overlap

[ORIGIN.json](../ORIGIN.json) lists the initial public package paths and SHA-256
digests for three mathematical files. The Apache 2.0 declaration applies to those
files and this package's authored material.

Finite KL nonnegativity, its chain rule, exponential tilting, and the Gibbs
variational principle are classical. The characterization formalizes Theorem
II.1 of Tom Leinster, *A short characterization of relative entropy* (2019),
[arXiv:1712.04903](https://arxiv.org/abs/1712.04903). The conclusion is a common
real scalar multiple; pointwise nonnegativity is a separate hypothesis if a
nonnegative scalar is desired. The source module documents the binary probe,
measurable Cauchy equation, full-support argument, and support reduction used by
the proof. The package claims neither a new mathematical theorem nor priority
among formalizations.

The initial release comparison below concerns Mathlib revision
`d13f23b723b8a846827a245b89c10fc7d3f11612`. It is a bounded source comparison of
the information-theory and probability trees, not an exhaustive novelty search.

| Existing Mathlib source | Relationship |
| --- | --- |
| [KullbackLeibler/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/InformationTheory/KullbackLeibler/Basic.lean) | Defines `InformationTheory.klDiv` for measures with extended nonnegative-real values, proves nonnegativity and equality-to-zero results. This package provides a real finite-simplex interface and proves equality with Mathlib KL on its explicitly admissible domain. |
| [KullbackLeibler/ChainRule.lean](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean) | Gives measure/kernel composition chain rules. This package's finite dependent composition uses the same shared probability-vector operations as its characterization hypotheses. |
| [KullbackLeibler/DataProcessing.lean](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/InformationTheory/KullbackLeibler/DataProcessing.lean) | Mathlib proves measure-theoretic data processing. The initial package scope covered finite KL, the Gibbs identity and characterization. |

The library's purpose is a coherent finite interface: support-bearing pairs,
exact real KL, admissible Gibbs tilts and their regret identity, and the four
hypotheses in Leinster's characterization. The KL bridge reuses Mathlib's
measure-theoretic results. The probability-vector representation and its
support, relabeling, and dependent-composition operations are reused from the
exact-pinned public `finite-markov-kernels` dependency.

The extraction changes package imports and namespaces, documents the generated
pair extensionality theorem and Gibbs evaluation lemma, and adds the direct
feasibility theorem that a Gibbs tilt is absolutely continuous with respect to
its original reference. Checked examples and build/verification infrastructure
are new package consumers. The original proof hypotheses are retained. Git
history and qualification source hashes record the final released form; the
initial public file hashes in `ORIGIN.json` identify the package baseline.

## Current compatibility pin

On Lean 4.35.0 and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`,
`InformationTheory.klDiv_comp_right_le` gives coefficient one. The strong finite-channel
inequality uses the maximum row total variation. The vector interface uses the
`rowContractionCoefficient` supplied by the package's pinned kernel library.
[Mathlib data processing](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/InformationTheory/KullbackLeibler/DataProcessing.lean#L185) · [Finite row coefficient](https://github.com/abenenson/finite-markov-kernels/blob/e37ed564fcc193ace7c48a94cf8f7090c2a31390/FiniteMarkovKernels/DobrushinCoefficient.lean)

The mathematical result is classical. See Y. Polyanskiy and Y. Wu, *Information Theory:
From Coding to Learning* (2025), Theorem 33.6(a), and J. E. Cohen, J. H. B. Kemperman and
G. Zbăganu, *Comparisons of Stochastic Matrices* (1998). This formalization uses a finite
grid containing the input and output likelihood ratios and one. A convex generator agrees
on that grid with an affine function plus nonnegative weighted positive-part functions.
Their centered discrepancies contract by the row bound. ATLAS lists the corresponding
measure-level statement using its own total-variation coefficient. [ATLAS statement](https://github.com/facebookresearch/atlas-lean/blob/6c7ff430b78648c8f8f1a447345d07b1fe88adb8/WantedExt/InformationTheory/StrongDataProcessingWanted.lean#L46)

### Censored geometric waiting times

The pinned Mathlib owns `ProbabilityTheory.geometricMeasure`, the geometric
law counting failures before the first success. Matthew W. Horn's Mathlib
proposals specify the head and tail masses and the pushforward onto `ℕ` under
`min · n`. Both proposals are open as of November 22, 2026. The finite entropy
API uses an explicit tail outcome. Encoding a recorded failure count as itself
and the tail as `n` gives the same observation map as `min · n`.
[Mathlib geometric law](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Probability/Distributions/Geometric.lean) · [Head and tail masses](https://github.com/leanprover-community/mathlib4/pull/45786) · [Censored law](https://github.com/leanprover-community/mathlib4/pull/42381)

Horn's Overload library independently models a capped retry by the index of
the last attempted operation. It uses a failure-probability parameter and
records `min K n` for a cap of `n + 1` attempts, where `K` is the number of
failures before the first success. The checked example here separately records
a timeout after two failures. The probability proposals and the retry model
provide context for the observation law. The package proves the exact
entropy loss as a geometric instance of the classical KL chain rule.
[Overload retry model](https://github.com/matt-w-horn/overload/blob/c45ea847cbde02e295fabae673e972607090e588/Overload/Retry/AttemptDist.lean#L41)
