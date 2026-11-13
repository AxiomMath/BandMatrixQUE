module

public import BlockBand.Coarea.Native.BlockBand.Counting.ScaledPhysicalSchurCompletion
public import BlockBand.Coarea.Native.BlockBand.Analysis.BoundaryFatou

/-!
# Boundary projected-Wegner estimate at the physical Gaussian-ring scale

The projected Wegner lemma includes a boundary-value statement
obtained by sending the positive scalar regulator to zero.  This file performs
that Fatou passage for the concrete Gaussian-ring pencil.

The constant is displayed in the normalization of the paper.  A physical diagonal block is
`sqrt p.c` times a `GUE_W(1/W)` block, so the PSSS density constant is
`K_b = input.C / sqrt p.c`.  The result below therefore has the exact bound
`pi K_b W |B|`.  The deformation and absorber are deterministic here; the more
general statement allowing a jointly random `(D, Gamma)` independent of
the diagonal blocks is represented by `PhysicalBlockConditioning` and is not inferred
from this specialization.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open Filter Matrix MeasureTheory
open scoped BigOperators ComplexOrder ENNReal Topology

universe u w

/-- Fatou passage with an arbitrary one-block averaging constant.

This is the constant-parametric form of
`projectedWegner_boundary_of_singleBlockAveraging`; it is useful when physical
rescaling moves a scalar factor from the block width into the density constant. -/
theorem projectedWegner_boundary_of_singleBlockAveraging_constant
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
    {β : Type w} [Fintype β] [DecidableEq β]
    (g : ℕ → β → Ω → ℝ) (K W : ℝ)
    (havg : ∀ n, SingleBlockAveraging μ (g n) K W)
    (B : Finset β)
    (hproj : ∀ n, ProjectedTraceDecomposition (g n) B)
    (boundary : Ω → ℝ≥0∞)
    (htendsto : ∀ᵐ ω ∂μ, Tendsto
      (fun n => ENNReal.ofReal ((hproj n).projectedTrace ω))
      atTop (𝓝 (boundary ω))) :
    ∫⁻ ω, boundary ω ∂μ ≤
      ENNReal.ofReal (Real.pi * K * W * (B.card : ℝ)) := by
  have hint (n : ℕ) : Integrable (hproj n).projectedTrace μ :=
    (hproj n).integrable μ (havg n)
  have hnonneg (n : ℕ) : 0 ≤ᵐ[μ] (hproj n).projectedTrace := by
    have hall : ∀ᵐ ω ∂μ, ∀ j, 0 ≤ g n j ω :=
      ae_all_iff.mpr (havg n).nonneg
    filter_upwards [hall] with ω hω
    rw [(hproj n).eq_sum]
    exact Finset.sum_nonneg fun j _hj => hω j
  apply lintegral_boundary_le_of_tendsto μ
    (fun n ω => ENNReal.ofReal ((hproj n).projectedTrace ω))
    boundary
    (ENNReal.ofReal (Real.pi * K * W * (B.card : ℝ)))
  · intro n
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      (hint n).aestronglyMeasurable.aemeasurable
  · exact htendsto
  · intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hint n) (hnonneg n)]
    exact ENNReal.ofReal_le_ofReal
      (projectedWegner_of_singleBlock μ (g n) K W
        (havg n) B (hproj n))

namespace GaussianRing

local instance (p : Params) : NeZero p.n := p.neZero_n

/-- The regulated retained-block trace for a sequence of positive heights. -/
def physicalProjectedTrace
    {p : Params} (M : Law p)
    (V Γ : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (e : ℝ) (η : ℕ → ℝ) (B : Finset (ZMod p.n))
    (n : ℕ) (ω : M.Ω) : ℝ :=
  ∑ j ∈ B, blockNegativeImaginaryTrace
    (physicalDeformedAbsorbedResolvent M V Γ e (η n) ω) j

/-- Boundary form of the physical Gaussian-ring projected-Wegner estimate.

For deterministic Hermitian `V`, deterministic positive-semidefinite `Γ`, positive
regulator heights `η n`, and any almost-everywhere pointwise boundary limit of the
retained-block negative imaginary traces, Fatou preserves the sharp physical bound

`pi * (input.C / sqrt p.c) * W * |B|`.

Thus the constant of the paper is `K_b = input.C / sqrt p.c` in the normalization of
`GaussianRing.Law`.  No convergence of resolvents is hidden: it is exactly the
`htendsto` hypothesis. -/
theorem projectedWegner_gaussianRing_physical_boundary
    (input : PSSSInput.{0}) {p : Params} (M : Law.{0} p)
    (V Γ : Matrix (Site p.n p.W) (Site p.n p.W) ℂ)
    (hV : V.IsHermitian) (hΓ : Γ.PosSemidef)
    (e : ℝ) (η : ℕ → ℝ) (hη : ∀ n, 0 < η n)
    (B : Finset (ZMod p.n))
    (boundary : M.Ω → ℝ≥0∞)
    (htendsto : ∀ᵐ ω ∂M.P, Tendsto
      (fun n => ENNReal.ofReal
        (physicalProjectedTrace M V Γ e η B n ω))
      atTop (𝓝 (boundary ω))) :
    ∫⁻ ω, boundary ω ∂M.P ≤
      ENNReal.ofReal
        (Real.pi * (input.C / Real.sqrt p.c) *
          (p.W : ℝ) * (B.card : ℝ)) := by
  let g : ℕ → ZMod p.n → M.Ω → ℝ := fun n j ω =>
    blockNegativeImaginaryTrace
      (physicalDeformedAbsorbedResolvent M V Γ e (η n) ω) j
  have havg : ∀ n,
      SingleBlockAveraging M.P (g n)
        (input.C / Real.sqrt p.c) (p.W : ℝ) := by
    intro n
    exact (M.scaledPhysicalSchurMatrixData V Γ hV hΓ e (η n) (hη n)).singleBlockAveraging
      input M (hη n)
  let hproj : ∀ n, ProjectedTraceDecomposition (g n) B := fun _n =>
    { projectedTrace := fun ω => ∑ j ∈ B, g _n j ω
      eq_sum := rfl }
  apply projectedWegner_boundary_of_singleBlockAveraging_constant
    M.P g (input.C / Real.sqrt p.c) (p.W : ℝ) havg B hproj boundary
  simpa [physicalProjectedTrace, g, hproj] using htendsto

end GaussianRing
end CoareaNative.BlockBand
