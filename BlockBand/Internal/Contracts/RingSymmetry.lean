module

public import BlockBand.Internal.Contracts.Clocks
public import BlockBand.QUE.Invariance.CyclicLaw
public import BlockBand.Asymptotics.CriticalSequence

/-!
# Ring rotation invariance and the vanishing block atom

**`RingRotationInvariance`** (cyclic invariance: "the left side … does not depend on `k`",
"this averaged functional is invariant under cyclic rotation"). Finite `W`, every admissible
`p` and every exact physical law `model.law` (`GaussianRingModel`), every block shift
`s : ZMod p.n`. The rotation is the site reindexing
`H ↦ (x, y ↦ H (x.1 + s, x.2) (y.1 + s, y.2))` (`siteReindexMatrix (cyclicSiteEquiv s)`). The
proposition is the conjunction of:
* the law: `model.law` is invariant under the rotation;
* the spectral statement: almost surely, the rotation keeps every increasing eigenvalue
  `physicalOrderedEigenvalue` and shifts every selected eigenvector block mass
  `physicalOrderedBlockMass` by `s` (`p_{α k}(rot_s H) = p_{α, k+s}(H)`, every rank `α`, every
  block `k`);
* the integral identities: for **every** real (resp. `ℝ≥0∞`) functional `F` of the eigenvalue
  vector and the full block-mass matrix (no measurability or integrability assumed: the rotation
  is a measurable equivalence), `E F(λ, (p_{α,k+s})_{α,k}) = E F(λ, (p_{α k})_{α,k})`. With
  `F` reading one column this is the `k`-independence of `E Σ_α w(u_α)Φ(n p_{αk})`; with
  `F = Σ_α p_{α k} g(λ_α, p_α)`, `g` rotation-invariant, it is the invariance used for the
  block-`0` Palm law.

**`VanishingBlockAtom`** (the vanishing block atom, used in the physical lead-profile theorem
and in the microscopic tag comparison). `0 < b < 1/2` and a bulk energy `-2 < E < 2` first;
every continuous compactly supported real `w` (in particular every smooth one); every `τ > 0`,
critical sequence `n_j/W_j → τ` and exact physical models `R j`:
`E Σ_α |w(u_α)| Σ_k p_{α k}² → 0`, `u_α = Nρ(E)(λ_α - E)` (`Clocks.microCoord`), the
expectation under `(R j).law` (a Bochner integral of a bounded measurable function). Every rank
and every block are summed, with multiplicity; no cutoff, Palm weighting or limit
identification is part of the statement.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Internal.Contracts.RingSymmetry

open MeasureTheory Filter Topology
open BlockBand.Model.Construction BlockBand.Internal.Contracts.Clocks
open scoped ENNReal

/-- The block rotation of the ring by `s` blocks, `H ↦ H((·.1 + s, ·.2), (·.1 + s, ·.2))`
(`siteReindexMatrix (cyclicSiteEquiv s)`). -/
def ringRotation (p : Parameters) (s : ZMod p.n) (H : p.SiteMatrix) : p.SiteMatrix :=
  p.siteReindexMatrix (p.cyclicSiteEquiv s) H

/-- The increasing eigenvalue vector `(λ_α)_α`. -/
def eigenvalueVector (p : Parameters) (H : p.SiteMatrix) : Fin p.N → ℝ :=
  fun α => physicalOrderedEigenvalue p H α

/-- The block-mass matrix `(p_{α k})_{α, k}` of the selected eigenvectors. -/
def blockMassMatrix (p : Parameters) (H : p.SiteMatrix) : Fin p.N → ZMod p.n → ℝ :=
  fun α k => physicalOrderedBlockMass p H α k

/-- Finite-`W` ring rotation invariance of the exact physical law and of the selected
eigenvector block masses. See the module docstring. -/
def RingRotationInvariance : Prop :=
  ∀ (p : Parameters) (model : p.GaussianRingModel) (s : ZMod p.n),
    Measure.map (ringRotation p s) (model.law : Measure p.SiteMatrix) =
        (model.law : Measure p.SiteMatrix) ∧
    (∀ᵐ H ∂(model.law : Measure p.SiteMatrix),
        eigenvalueVector p (ringRotation p s H) = eigenvalueVector p H ∧
        ∀ (α : Fin p.N) (k : ZMod p.n),
          blockMassMatrix p (ringRotation p s H) α k = blockMassMatrix p H α (k + s)) ∧
    (∀ F : (Fin p.N → ℝ) → (Fin p.N → ZMod p.n → ℝ) → ℝ,
        (∫ H, F (eigenvalueVector p H) (fun α k => blockMassMatrix p H α (k + s))
            ∂(model.law : Measure p.SiteMatrix)) =
          ∫ H, F (eigenvalueVector p H) (blockMassMatrix p H)
            ∂(model.law : Measure p.SiteMatrix)) ∧
    (∀ F : (Fin p.N → ℝ) → (Fin p.N → ZMod p.n → ℝ) → ℝ≥0∞,
        (∫⁻ H, F (eigenvalueVector p H) (fun α k => blockMassMatrix p H α (k + s))
            ∂(model.law : Measure p.SiteMatrix)) =
          ∫⁻ H, F (eigenvalueVector p H) (blockMassMatrix p H)
            ∂(model.law : Measure p.SiteMatrix))

/-- The block-atom functional `Σ_α |w(u_α)| Σ_k p_{α k}²` at energy `E`,
`u_α = Nρ(E)(λ_α - E)`. -/
def blockAtomFunctional (p : Parameters) (E : ℝ) (w : ℝ → ℝ) (H : p.SiteMatrix) : ℝ :=
  ∑ α : Fin p.N, |w (microCoord p E (physicalOrderedEigenvalue p H α))| *
    ∑ k : ZMod p.n, physicalOrderedBlockMass p H α k ^ 2

/-- The vanishing block atom. See the module docstring. -/
def VanishingBlockAtom : Prop :=
  ∀ (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (E : ℝ), -2 < E → E < 2 →
    ∀ w : ℝ → ℝ, Continuous w → HasCompactSupport w →
    ∀ τ : ℝ, 0 < τ → ∀ (s : CriticalSequence τ)
      (R : ∀ j, (s.parameters b hb hb' j).GaussianRingModel),
      Tendsto (fun j => ∫ H, blockAtomFunctional (s.parameters b hb hb' j) E w H
          ∂((R j).law : Measure (s.parameters b hb hb' j).SiteMatrix)) atTop (𝓝 0)

end BlockBand.Internal.Contracts.RingSymmetry
