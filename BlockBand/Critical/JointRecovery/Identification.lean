module

public import BlockBand.Critical.JointRecovery.LimitSupport
public import BlockBand.Critical.JointRecovery.ExtractionLimit

/-!
# Identification of critical marked limit points through the entire law

* `tendsto_readoutLaplace`: `readoutLaplace q ((R j).markedLaw E) f → extractorLaplace E τ μ f`;
* `readoutLaplace_eq_of_mapClusterPt`: every cluster point `ν` of the physical marked laws
  (marked vague topology, weak convergence of laws) satisfies
  `readoutLaplace q ν f = extractorLaplace E τ μ f`.
Inputs: PSSS input `source` (two-point bound of the counting theorem, through
`limit_ae_goodEntire`). No uniformity.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Critical.JointRecovery

open Filter Topology Set MeasureTheory
open BlockBand.Critical.Entire
open BlockBand.Internal.Contracts.CriticalEntire

variable {k : ℕ}

/-- **Readout Laplace values converge to the extraction from the entire limit.** Law: physical marked laws `(R j).markedLaw E` along a
critical sequence `s` (`W → ∞`, `n/W → τ > 0`, any realizations), fixed `0 < b < 1/2`, bulk
`E` (`ρ(E) > 0`), finite profile family `q`, nonnegative `f ∈ C_c(ℝ × ℂ^{k+1})`, and any weak
limit `μ` (compact-open Borel) of the laws of `D_W`. Order of limits: `W → ∞` only; no
uniformity. Inputs: PSSS (`source`, through `limit_ae_goodEntire`). -/
theorem tendsto_readoutLaplace (source : BlockBand.External.PSSS.SourceContract.{0}) {τ : ℝ}
    (hτ : 0 < τ) (s : CriticalSequence τ) (b E : ℝ) (hb : 0 < b) (hb' : b < 1 / 2)
    (hρ : 0 < Parameters.semicircleDensity E)
    (R : ∀ j, FiniteRealization (s.parameters b hb hb' j)) (q : Fin k → C(Torus, ℝ))
    {μ : RandomEntire (k + 1)}
    (hμ : Tendsto (fun j => finiteEntireLaw (R j) E (fullProfile q)) atTop (𝓝 μ))
    (f : CompactlySupportedContinuousMap (ℝ × (Fin (k + 1) → ℂ)) ℝ) (hf : ∀ z, 0 ≤ f z) :
    Tendsto (fun j => readoutLaplace q ((R j).markedLaw E) f) atTop
      (𝓝 (extractorLaplace E τ μ f)) := by
  have heq : ∀ j, readoutLaplace q ((R j).markedLaw E) f =
      ∫ F, extractionValue E ((s.n j : ℝ) / s.W j) f F
        ∂(finiteEntireLaw (R j) E (fullProfile q) : Measure (EntireFunction (k + 1))) :=
    fun j => readoutLaplace_markedLaw_eq (R j) hρ q f hf
  simp_rw [heq]
  exact tendsto_extractorLaplace hρ hτ f hf hμ s.ratio_tendsto
    (fun j => div_pos (by have := s.n_ge_four j; positivity) (by exact_mod_cast s.W_pos j))
    (fun j => finiteEntireLaw_compl_goodEntire (R j) E q)
    (limit_ae_goodEntire source s b E hb hb' hρ R q hμ)

/-- A cluster point of a convergent sequence in a Hausdorff space is its limit. -/
theorem eq_of_mapClusterPt_of_tendsto {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {F : Filter ι} {u : ι → X} {x y : X} (hx : MapClusterPt x F u) (hy : Tendsto u F (𝓝 y)) :
    x = y :=
  eq_of_nhds_neBot (ClusterPt.mono hx hy)

/-- **Identification of cluster points.** Same setting as
`tendsto_readoutLaplace`; `ν` is any cluster point (weak topology on laws on the marked vague
space) of the physical marked laws along `s`. Then `readoutLaplace q ν f` equals
`extractorLaplace E τ μ f`. No uniformity; inputs: PSSS. -/
theorem readoutLaplace_eq_of_mapClusterPt (source : BlockBand.External.PSSS.SourceContract.{0})
    {τ : ℝ} (hτ : 0 < τ) (s : CriticalSequence τ) (b E : ℝ) (hb : 0 < b) (hb' : b < 1 / 2)
    (hρ : 0 < Parameters.semicircleDensity E)
    (R : ∀ j, FiniteRealization (s.parameters b hb hb' j)) (q : Fin k → C(Torus, ℝ))
    {μ : RandomEntire (k + 1)}
    (hμ : Tendsto (fun j => finiteEntireLaw (R j) E (fullProfile q)) atTop (𝓝 μ))
    (f : CompactlySupportedContinuousMap (ℝ × (Fin (k + 1) → ℂ)) ℝ) (hf : ∀ z, 0 ≤ f z)
    {ν : ProbabilityMeasure MarkedPointMeasure}
    (hν : MapClusterPt ν atTop (fun j => (R j).markedLaw E)) :
    readoutLaplace q ν f = extractorLaplace E τ μ f := by
  let Φ : ProbabilityMeasure MarkedPointMeasure → ℝ := fun ν' =>
    ∫ ξ, markedLaplaceBCF (readoutTest q f) (fun _ => hf _) ξ ∂(ν' : Measure MarkedPointMeasure)
  have hΦ : Continuous Φ :=
    ProbabilityMeasure.continuous_integral_boundedContinuousFunction _
  have hcl := hν.continuousAt_comp hΦ.continuousAt
  have hlim := tendsto_readoutLaplace source hτ s b E hb hb' hρ R q hμ f hf
  exact eq_of_mapClusterPt_of_tendsto hcl hlim

end BlockBand.Critical.JointRecovery
