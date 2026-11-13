module

public import BlockBand.Coarea.Native.BlockBand.Counting.NormalizedDiagonalBlockGUEOrdering
public import BlockBand.Coarea.Native.BlockBand.Counting.ProjectedWegnerPhysical

/-!
# Instantiating physical projected Wegner averaging for the Gaussian ring

The normalized diagonal block of `GaussianRing.Law` is now unconditionally a
standard singleton `BlockGUE`.  Consequently no exposed-block distribution or
ordering transport remains among the conditioning inputs.  This module
packages only the exterior-dependent Schur data: its Hermitian background,
positive-semidefinite absorber, joint measurability, and the final
identification of the physical projected trace with the Schur trace.

These fields are precisely the model-specific reconstruction statements that
depend on the deterministic Hamiltonian and absorber chosen by an application.
All Gaussian normalization, independence, PSSS averaging, exterior integration,
and finite retained-block summation are proved consequences.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators ComplexOrder ENNReal NNReal

universe v

namespace GaussianRing

local instance (p : Params) : NeZero p.n := p.neZero_n

/-- The remaining physical Schur data after the diagonal Gaussian block has
been constructed unconditionally from `GaussianRing.Law`.

The exterior may depend on the retained block.  Its law is a probability
measure.  `trace_identDistrib` is the final model-specific reconstruction
identity; unlike the earlier interface, the exposed `BlockGUE` law is fixed
canonically and is not supplied as an assumption. -/
structure PhysicalProjectedWegnerInstantiation
    {p : Params} (M : Law p)
    (g : ZMod p.n → M.Ω → ℝ) (η : ℝ) where
  Exterior : ZMod p.n → Type v
  [exteriorMeasurable : ∀ j, MeasurableSpace (Exterior j)]
  exteriorLaw : ∀ j, Measure (Exterior j)
  [exteriorProbability : ∀ j, IsProbabilityMeasure (exteriorLaw j)]
  background : ∀ j, Exterior j →
    HermitianMatrix (BlockGUE.Index (singletonBlockSize p.W))
  absorber : ∀ j, Exterior j →
    Matrix (BlockGUE.Index (singletonBlockSize p.W))
      (BlockGUE.Index (singletonBlockSize p.W)) ℂ
  absorber_pos : ∀ j ξ, (absorber j ξ).PosSemidef
  joint_measurable : ∀ j,
    Measurable (conditionedAbsorbedTrace p.W_pos
      (M.normalizedDiagonalBlockGUECoupling j).exposed
      (background j) (absorber j) η)
  trace_identDistrib : ∀ j,
    IdentDistrib (g j)
      (conditionedAbsorbedTrace p.W_pos
        (M.normalizedDiagonalBlockGUECoupling j).exposed
        (background j) (absorber j) η)
      M.P ((exteriorLaw j).prod
        (M.normalizedDiagonalBlockGUECoupling j).exposed.P)

attribute [instance]
  PhysicalProjectedWegnerInstantiation.exteriorMeasurable
  PhysicalProjectedWegnerInstantiation.exteriorProbability

/-- The reduced Schur data reconstructs the older per-block Gaussian coupling
interface.  The exposed law is the unconditional normalized diagonal block. -/
def PhysicalProjectedWegnerInstantiation.gaussianCoupling
    {p : Params} (M : Law p)
    {g : ZMod p.n → M.Ω → ℝ} {η : ℝ}
    (h : PhysicalProjectedWegnerInstantiation M g η) (j : ZMod p.n) :
    PhysicalConditioningGaussianCoupling M j (g := g j) (η := η) where
  exposed := (M.normalizedDiagonalBlockGUECoupling j).exposed
  Exterior := h.Exterior j
  exteriorLaw := h.exteriorLaw j
  background := h.background j
  absorber := h.absorber j
  absorber_pos := h.absorber_pos j
  joint_measurable := h.joint_measurable j
  trace_identDistrib := h.trace_identDistrib j

/-- Assemble the exact `PhysicalBlockConditioning` consumed by the proved
finite-block projected-Wegner theorem. -/
def PhysicalProjectedWegnerInstantiation.physicalBlockConditioning
    {p : Params} (M : Law p)
    {g : ZMod p.n → M.Ω → ℝ} {η : ℝ}
    (h : PhysicalProjectedWegnerInstantiation M g η) :
    PhysicalBlockConditioning M.P g p.W p.W_pos η
      h.Exterior h.exteriorLaw
      (fun j => (M.normalizedDiagonalBlockGUECoupling j).exposed) where
  background := h.background
  absorber := h.absorber
  absorber_pos := h.absorber_pos
  joint_measurable := h.joint_measurable
  identDistrib := h.trace_identDistrib

/-- The physical Schur instantiation supplies the sharp one-block averaging
bound `π C W` for every retained site. -/
theorem PhysicalProjectedWegnerInstantiation.singleBlockAveraging
    (input : PSSSInput.{0})
    {p : Params} (M : Law p)
    {g : ZMod p.n → M.Ω → ℝ} {η : ℝ} (hη : 0 < η)
    (h : PhysicalProjectedWegnerInstantiation M g η) :
    SingleBlockAveraging M.P g input.C (p.W : ℝ) :=
  (h.physicalBlockConditioning M).singleBlockAveraging input M.P g
    p.W_pos hη h.Exterior h.exteriorLaw
    (fun j => (M.normalizedDiagonalBlockGUECoupling j).exposed)

/-- Regulated projected-Wegner estimate for a Gaussian ring once the
application-specific Schur reconstruction data has been supplied.  All
probabilistic diagonal-block inputs are unconditional. -/
theorem projectedWegner_gaussianRing_of_schurInstantiation
    (input : PSSSInput.{0})
    {p : Params} (M : Law p)
    {g : ZMod p.n → M.Ω → ℝ} {η : ℝ} (hη : 0 < η)
    (h : PhysicalProjectedWegnerInstantiation M g η)
    (B : Finset (ZMod p.n)) (hproj : ProjectedTraceDecomposition g B) :
    ∫ ω, hproj.projectedTrace ω ∂M.P ≤
      Real.pi * input.C * (p.W : ℝ) * (B.card : ℝ) :=
  projectedWegner_physical_of_conditioning input M.P g p.W_pos hη
    h.Exterior h.exteriorLaw
    (fun j => (M.normalizedDiagonalBlockGUECoupling j).exposed)
    (h.physicalBlockConditioning M) B hproj

/-- Canonical block-trace form of the Gaussian-ring projected-Wegner estimate. -/
theorem projectedWegner_gaussianRing_blocks_of_schurInstantiation
    (input : PSSSInput.{0})
    {p : Params} (M : Law p) {η : ℝ} (hη : 0 < η)
    (R : M.Ω → Matrix (ZMod p.n × Fin p.W) (ZMod p.n × Fin p.W) ℂ)
    (h : PhysicalProjectedWegnerInstantiation M
      (fun j ω => blockNegativeImaginaryTrace (R ω) j) η)
    (B : Finset (ZMod p.n)) :
    ∫ ω, ∑ j ∈ B, blockNegativeImaginaryTrace (R ω) j ∂M.P ≤
      Real.pi * input.C * (p.W : ℝ) * (B.card : ℝ) :=
  projectedWegner_physical_blocks_of_conditioning input M.P p.W_pos hη R
    h.Exterior h.exteriorLaw
    (fun j => (M.normalizedDiagonalBlockGUECoupling j).exposed)
    (h.physicalBlockConditioning M) B

/-- Direct resolvent specialization.  Here the only input beyond
the Gaussian ring law is the Schur reconstruction of this displayed physical
Hamiltonian and absorber. -/
theorem projectedWegner_gaussianRing_resolvent_of_schurInstantiation
    (input : PSSSInput.{0})
    {p : Params} (M : Law p) (e : ℝ) {η : ℝ} (hη : 0 < η)
    (H Γ : M.Ω →
      Matrix (ZMod p.n × Fin p.W) (ZMod p.n × Fin p.W) ℂ)
    (h : PhysicalProjectedWegnerInstantiation M
      (fun j ω => blockNegativeImaginaryTrace
        (physicalAbsorbedResolvent H Γ e η ω) j) η)
    (B : Finset (ZMod p.n)) :
    ∫ ω, ∑ j ∈ B, blockNegativeImaginaryTrace
        (physicalAbsorbedResolvent H Γ e η ω) j ∂M.P ≤
      Real.pi * input.C * (p.W : ℝ) * (B.card : ℝ) :=
  projectedWegner_gaussianRing_blocks_of_schurInstantiation
    input M hη (physicalAbsorbedResolvent H Γ e η) h B

end GaussianRing
end CoareaNative.BlockBand
