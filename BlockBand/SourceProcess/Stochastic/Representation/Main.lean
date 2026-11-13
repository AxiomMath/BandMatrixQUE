module
public import BlockBand.SourceProcess.Stochastic.Representation.PosDef
public import BlockBand.SourceProcess.Stochastic.Representation.PseudoInverse
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Weak-solution representation of martingale-problem solutions: summary

This module only imports the representation theory. Its results, proved in the imported modules:
* predictable processes are strongly progressive; congruence of `predVersion`; horizon gluing of
  martingales (`martingale_glue`);
* bounded predictable integrands `IsBddPred`, their classes `bpL2`, multipliers `predMul`;
* **`vecIntegral_assoc`**, **`vecCont_assoc`**: associativity
  `∫ K d(∫ H dZ) = ∫ (Kᵀ H) dZ` for bounded predictable `H`, `K`;
* **`exists_brownian_of_driver`**: a vector integral with identity bracket density, glued over
  horizons and made predictable, is a filtration Brownian motion on `[0, ∞)` (Lévy);
* **`exists_mp_integrator`**: the stopped compensated process of an `IsMPSolutionOn` solution is
  an `IsL2IntegratorVec` with density `σσᵀ(Y)1{· ≤ τ}`;
* `vecCont_unitStop`: the integral of a stopped unit coordinate, with matrix identities;
* **`exists_weak_solution_posDef`**: the assembled representation theorem for `σ(y)` invertible
  on `closure W` (the situation of `StoppedMartingaleProblemUniquenessPosDef`);
* **`pinv`**, `tendsto_tikhonov`, **`isMoorePenrose_pinv`**, **`measurable_pinv_comp`**: a Borel
  Moore–Penrose selector.
-/
