# API and verification

The mathematical domain is a finite type `A` with a `Fintype` instance. The
shared `FiniteMarkovKernels.ProbabilityVector A` consists of nonnegative real
coordinates summing to one. The structure permits zeros and therefore cannot
exist on an empty alphabet. No separate positivity or nonempty instance is
required when a probability vector is already supplied.

`FiniteRelativeEntropy.AdmissiblePair A` contains two such laws and the explicit
condition `∀ a, reference a = 0 → numerator a = 0`. This restricts the domain to
pairs with finite KL. It does not require full support of either law. The
definition is the real sum `∑ a, p a * Real.log (p a / r a)`; zero numerator
coordinates contribute zero. Pairs with positive numerator mass outside the
reference support are outside this domain.

| Import | Public API |
| --- | --- |
| `FiniteRelativeEntropy.Basic` | `AdmissiblePair`, `AdmissibleReference`, `finiteKL`; diagonal, relabeling, dependent chain rule, measurability, nonnegativity, equality to zero, Mathlib KL bridge |
| `FiniteRelativeEntropy.GibbsVariational` | Partition function, normalized Gibbs tilt, support preservation, admissibility, exact regret identity, unique minimizer |
| `FiniteRelativeEntropy.Characterization` | `RelativeEntropyFamily`, its KL instance, global scalar characterization, optional nonnegative scalar theorem |
| `FiniteRelativeEntropy` | All three modules |
| `FiniteRelativeEntropyExamples` | Exact boundary and nonconstant Gibbs consumers |

The extensions `toMeasure`, `partitionFunction`, and `gibbsTilt` belong to
`FiniteMarkovKernels.ProbabilityVector`, the namespace that owns the shared
probability type. `AdmissiblePair`, `finiteKL`, and `RelativeEntropyFamily` belong
to `FiniteRelativeEntropy`. Consumers can open both namespaces. There is no
second probability-vector type or conversion requirement.

The partition function is strictly positive for every real `beta` and every
real energy on a finite alphabet. Tilting has exactly the original positive
support. The minimization theorem ranges over probability laws absolutely
continuous with respect to that reference; its equality clause determines the
tilted law. It covers `beta = 0` and negative `beta` as stated.

`RelativeEntropyFamily` quantifies over all finite alphabets in `Type`. Its four
fields are measurability in the reference for each fixed numerator, simultaneous
relabeling invariance, diagonal vanishing, and the full chain rule for dependent
finite fibers. The conclusion is `I P = I.probeScale * finiteKL P` with the same
real scalar for every alphabet and admissible pair. Neither positivity nor a
normalization is one of these four hypotheses. `probeScale_nonneg` requires the
separate `Nonnegative` property; strict positivity is not asserted.

The bridge in `Basic` places the discrete measures on a measurable alphabet
with measurable singletons. It proves that Mathlib's KL is finite on an
admissible pair and its `toReal` equals `finiteKL`. Probability-vector equality
is recovered from singleton masses. The Gibbs and characterization APIs
themselves require no measurable-space instance on the alphabet.

## Reproducible verification

`verification.json` is the complete authored source and explicit public-name
ledger. `scripts/verify.py` rejects holes, custom axioms, overlong Lean source
lines, undocumented source headers, unapproved imports, missing declarations,
dependency pin drift, and warning or error diagnostics. Its declaration scanner
includes explicitly named instances and skips private names; generated fields
and anonymous instances are audited transitively when used by a named public
declaration.

Before the exact `lake --rehash --wfail build`, the verifier removes the bounded
set of authored `.olean`, `.ilean`, `.ir`, and `.trace` outputs. It refuses linked
authored artifact directories and preserves dependency artifacts. The exact
source is then elaborated again with the full 16-linter `#lint docBlame
docBlameThm` set, with no global linter suppression. Finally it prints transitive
axioms for every ledger declaration and accepts only `propext`,
`Classical.choice`, and `Quot.sound`.

The Python rejection controls exercise malformed and zero-exit diagnostics,
import allowlists, bounded stale-artifact removal, linked-directory refusal, and
the end-to-end verifier using isolated mocked projects. The workflow pins each
GitHub Action by commit, runs these controls and the same verifier, and retains
`verification-artifacts/`. Local qualification and a hosted CI run are separate
results; only actual run evidence establishes either.

The [2026-11-04 local qualification](qualification.json) passed a fresh build of
all six authored source/example modules, all 16 linters for each source, the
transitive audit of all 74 explicit public names, and 14 verifier controls. The
receipt binds the exact source, verifier, configuration, dependencies and
provenance by hashes. The shared dependency checkout was clean at its pinned
commit; development links reused qualified local dependency caches. The first
attempt stopped before source elaboration because of Lake's escaped package-name
serialization, which was corrected with parser rejection controls before the
successful fresh replay. No Lean proof or check needed to be weakened.

This is local qualification. Creating the new remote repository returned GitHub
403 at this checkpoint, so a fresh remote clone and hosted CI run are not part
of this receipt.

## Packaging comparison

The local packaging baselines were `finite-markov-kernels` at
`ddbbb4d7a7582868052d6704697c61871d97f54d`, `measure-discrimination` at
`ce782da7524845c689bba5cee9eeb9d205e20c06`, and `berge-maximum` at
`db3295ceaabfa442d8fdb899a4a9f05045ad7f1d`. Their checked-out source, package
configuration, license, examples, and verification programs supplied the
comparison, including the coordinated stale-artifact verifier refinement.
This package retains the small public root, separate built examples, immutable
dependency and action pins, file-scoped provenance, warning-fatal source/full
lint, and named transitive axiom ledger. It adds only the explicitly declared
shared probability dependency to the focused Mathlib import boundary. This is a
comparison of packaging and verification practice, without a claim about the
relative mathematical merit of the libraries.

## Development with related libraries

The shipped Lake configuration and manifest use public GitHub dependencies at
exact commit hashes. During coordinated development before a dependency is
published, a local package checkout may be placed at
`.lake/packages/finite-markov-kernels` with its matching build outputs. Such a
checkout is an ignored development artifact. Keep the public URL and exact
revision in the tracked Lake files, update all three pin records
(`lakefile.lean`, `lake-manifest.json`, `verification.json`) together, and run the
strict verifier after the dependency commit is finalized. The final verifier
checks the dependency checkout's actual Git head against that exact pin.

## Private CI dependencies

The `vendor` Git bundles contain the exact private dependency commits pinned by Lake.
The setup script verifies bundle hashes, manifest URLs/revisions, checkout identity and
tracked cleanliness before Lean setup. CI needs no additional repository credential.
The mathematical sources and their qualification identities are unchanged.
