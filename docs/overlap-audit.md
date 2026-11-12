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

The comparison below concerns the exact pinned Mathlib revision
`d13f23b723b8a846827a245b89c10fc7d3f11612`. It is a bounded source comparison of
the information-theory and probability trees, not an exhaustive novelty search.

| Existing Mathlib source | Relationship |
| --- | --- |
| [KullbackLeibler/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/InformationTheory/KullbackLeibler/Basic.lean) | Defines `InformationTheory.klDiv` for measures with extended nonnegative-real values, proves nonnegativity and equality-to-zero results. This package provides a real finite-simplex interface and proves equality with Mathlib KL on its explicitly admissible domain. |
| [KullbackLeibler/ChainRule.lean](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/InformationTheory/KullbackLeibler/ChainRule.lean) | Gives measure/kernel composition chain rules. This package's finite dependent composition uses the same shared probability-vector operations as its characterization hypotheses. |
| [KullbackLeibler/DataProcessing.lean](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/InformationTheory/KullbackLeibler/DataProcessing.lean) | Provides measure-theoretic data processing. This extraction adds no data-processing theorem and makes no replacement claim. |

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
