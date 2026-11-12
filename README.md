# finite-relative-entropy

Finite Kullback–Leibler divergence, Gibbs variational identities, and Leinster's
characterization of relative entropy in Lean and Mathlib.

The library uses the closed finite probability simplex from
[finite-markov-kernels](https://github.com/abenenson/finite-markov-kernels).
Zero coordinates are allowed. An `AdmissiblePair` carries the support condition
`p ≪ r`, so `finiteKL` is a finite real number, including at the boundary.

The public API proves:

- **Finite KL:** nonnegativity, equality to zero exactly on the diagonal,
  simultaneous relabeling invariance, reference measurability, and the dependent
  block-composition chain rule. A bridge identifies this real-valued divergence
  with Mathlib's measure-theoretic `InformationTheory.klDiv`.
- **Gibbs variational identity:** exponential tilting preserves the reference
  support. For every real `beta`, `KL(p ‖ r) + beta * E_p[energy]` equals the KL
  regret against the Gibbs tilt minus the log partition function. The tilt is
  admissible and uniquely attains the lower bound.
- **Leinster's characterization:** every family on all finite admissible pairs
  that is measurable in the reference, invariant under simultaneous relabeling,
  zero on the diagonal, and satisfies the full dependent chain rule is one common
  real scalar multiple of KL. The scalar is nonnegative when the family is
  separately assumed pointwise nonnegative.

```lean
import FiniteRelativeEntropy

open FiniteRelativeEntropy FiniteMarkovKernels
open scoped BigOperators

example {A : Type*} [Fintype A] (pair : AdmissiblePair A)
    (energy : A → ℝ) (beta : ℝ) :
    finiteKL pair + beta * ∑ a, pair.numerator a * energy a ≥
      -Real.log (pair.reference.partitionFunction energy beta) :=
  (finiteKL.gibbsTilt_unique_minimizer pair energy beta).1

example (family : RelativeEntropyFamily) {A : Type} [Fintype A]
    (pair : AdmissiblePair A) :
    family pair = family.probeScale * finiteKL pair :=
  family.characterization pair
```

[Checked examples](FiniteRelativeEntropyExamples/Basic.lean) evaluate the KL of a
point mass against a fair coin as `log 2`, include a zero reference coordinate,
and compute a nonconstant Gibbs tilt with probabilities `3/4` and `1/4`. They
prove attainment and uniqueness, preservation of excluded support, and the
characterization at a boundary pair. Import `FiniteRelativeEntropyExamples` to
use them.

Pinned toolchain: **Lean 4.34.1**, **Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`**. All direct and transitive
dependencies are exact-pinned in [lake-manifest.json](lake-manifest.json).

```bash
lake exe cache get
lake --rehash --wfail build
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/verify.py
```

Run these commands from the checkout root. Lake resolves the exact pinned
dependencies from their public GitHub repositories. CI uses the same public
dependency graph; see the [dependency notes](docs/overview.md#public-dependencies).

The verifier removes only authored module artifacts before rebuilding every
source and example, checks all 16 linters with warnings fatal, and audits each
explicit named public declaration's transitive axioms. Only `propext`,
`Classical.choice`, and `Quot.sound` are admitted. See the
[API and verification notes](docs/overview.md) and
[Mathlib overlap and attribution](docs/overlap-audit.md).

These are classical mathematical results. The characterization follows Tom
Leinster, *A short characterization of relative entropy* (2019), Theorem II.1;
the package makes no priority claim. Apache 2.0, copyright 2026 Adam Benenson.
See [LICENSE](LICENSE), [NOTICE](NOTICE), and [initial public file inventory](ORIGIN.json).
