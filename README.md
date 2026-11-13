[![](logo.svg)](https://axiommath.ai/)

# Quantum Unique Ergodicity and the Critical Crossover for Band Matrices

This is a Lean formalization of Theorems 1.1, 1.3 and 1.4 of
[Quantum unique ergodicity and the critical crossover for 1-d Gaussian band matrices](https://arxiv.org/abs/2611.15085)
by Promit Ghosal and Guillaume Remy.

The results were obtained through a human–AI collaboration: the investigators, Promit Ghosal and Guillaume Remy,
directed the research and made the mathematical judgments. AxiomProver generated the Lean formalization. The work
was developed at Axiom Math.

## Main Results

The model is the complex Gaussian random band matrix of size `N = nW` with the periodic block structure of Yau
and Yin: `n` blocks of size `W` on a ring, with nonzero entries only inside a block and between adjacent blocks.

* **Theorem 1.1 (quantum unique ergodicity).** If `W² / N → ∞`, bulk eigenvectors at every deterministic rank
  are quantum uniquely ergodic, with no power or logarithmic separation between `W²` and `N`.
* **Theorem 1.3 (the critical law).** If `N / W² → τ ∈ (0, ∞)`, the rescaled bulk eigenvalues and the block-mass
  profiles of their eigenvectors converge jointly, as a marked point process, to a unique law. This law is
  determined by the construction of a random entire function.
* **Theorem 1.4 (the endpoints).** In the critical law, the profiles have strictly positive variance against every
  nonconstant smooth test function. As `τ → 0` the variance tends to zero and the local spectrum tends to the sine
  process; as `τ → ∞` the local spectrum tends to a Poisson process.

The formal proof uses only Lean's three standard axioms: `propext`, `Quot.sound`, and `Classical.choice`.

See [§Formal Challenge](#formal-challenge) for the formal statements and verification instructions.

## Dependencies

This project depends on [Mathlib](https://github.com/leanprover-community/mathlib4).

It also includes code adapted from [Tau Ceti](https://github.com/TauCetiProject/TauCeti) (sorted eigenvalues and
the Courant–Fischer theorem); see [NOTICE](NOTICE).

The proofs also formalize results from other papers, cited in the code by their authors' initials as in the paper's
bibliography: PSSS (Peled, Schenker, Shamis and Sodin), APSSS (Aizenman, Peled, Schenker, Shamis and Sodin), CEH
(Cipolloni, Erdős and Henheik) and ER (Erdős and Riabov).

## Formal Challenge

[Challenge/BlockBandChallenge.lean](Challenge/BlockBandChallenge.lean) states `BlockBand.que`,
`BlockBand.critical` and `BlockBand.endpoints` (Theorems 1.1, 1.3 and 1.4), with `sorry` as proof. The
definitions they use are in [BlockBand/Statements.lean](BlockBand/Statements.lean) and its imports:
`BlockBand/Prelude.lean`, `BlockBand/Model/{Parameters,GaussianRing,Observables}.lean`,
`BlockBand/Asymptotics/CriticalSequence.lean` and `BlockBand/PointProcess/{Vague,LawProperties,Specifications}.lean`.

[Solution/BlockBandSolution.lean](Solution/BlockBandSolution.lean) proves these three statements from the
library. It also proves `BlockBand.critical_construction`, which formalizes the last sentence of Theorem 1.3: the
critical law is determined by the construction of the random entire function. The comparator does not check this
companion theorem, since it is not a Challenge statement.

To build:

```sh
lake exe cache get
lake build
```

To run the comparator (Linux; install it following https://github.com/leanprover/comparator):

```sh
lake env comparator comparator.json
```

The comparator ([leanprover/comparator](https://github.com/leanprover/comparator) at tag v4.35.0-rc3, with
the landrun sandbox enforced) accepts the solution: the three statements match the Challenge, the proofs use only
`propext`, `Classical.choice` and `Quot.sound`, and Lean's kernel replays the whole exported environment. The run
takes about 16 minutes and 13 GB of memory on a 32-core machine.
