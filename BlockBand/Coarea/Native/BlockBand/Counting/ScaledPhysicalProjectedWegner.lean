module

public import BlockBand.Coarea.Native.BlockBand.Counting.PhysicalSchurMatrixConstruction

/-!
# Scaled physical projected Wegner bound

The physical diagonal Gaussian block is `sqrt p.c • G`, with `G` in the standard
`GUE_W(1/W)` normalization consumed by PSSS.  Factoring `sqrt p.c` from the complete
Schur pencil multiplies the negative imaginary trace of its inverse by
`(sqrt p.c)⁻¹`, and changes the regulator from `η` to `η / sqrt p.c`.

This module packages the scaled interface and derives the sharp bound supplied by
the existing PSSS input:

`π * (input.C / sqrt p.c) * W * |B|`.

The constant carries the factor `(sqrt p.c)⁻¹`; it is not `π * input.C * W`.
The construction of the normalized deterministic Schur complement from a concrete
physical deformation and absorber remains an explicit `PhysicalSchurMatrixData`
field.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open Matrix MeasureTheory
open scoped BigOperators ComplexOrder ENNReal NNReal

namespace GaussianRing

local instance (p : Params) : NeZero p.n := p.neZero_n

/-- The physical one-block PSSS constant after extracting the diagonal amplitude
`sqrt p.c`. -/
def scaledPhysicalPSSSConstant (input : PSSSInput) (p : Params) : ℝ :=
  input.C / Real.sqrt p.c

/-- Dividing a positive scalar multiple of every block observable transfers a
`SingleBlockAveraging` estimate and divides its constant by that scalar. -/
theorem singleBlockAveraging_of_pos_smul
    {Ω β : Type*} [MeasurableSpace Ω] [Fintype β] [DecidableEq β]
    (μ : Measure Ω) (g : β → Ω → ℝ) {s : ℝ} (hs : 0 < s)
    (K W : ℝ)
    (h : SingleBlockAveraging μ (fun j ω => s * g j ω) K W) :
    SingleBlockAveraging μ g (K / s) W where
  integrable j := by
    have hi := (h.integrable j).const_mul s⁻¹
    simpa [hs.ne', inv_mul_cancel₀] using hi
  nonneg j := by
    filter_upwards [h.nonneg j] with ω hω
    change 0 ≤ s * g j ω at hω
    change 0 ≤ g j ω
    nlinarith
  oneBlock j := by
    have hi := h.oneBlock j
    rw [integral_const_mul] at hi
    have hinv : 0 ≤ s⁻¹ := inv_nonneg.mpr hs.le
    calc
      ∫ ω, g j ω ∂μ = s⁻¹ * (s * ∫ ω, g j ω ∂μ) := by
        rw [← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]
      _ ≤ s⁻¹ * (Real.pi * K * W) :=
        mul_le_mul_of_nonneg_left hi hinv
      _ = Real.pi * (K / s) * W := by
        field_simp [hs.ne']

/-- Correct physical Schur input.  The coefficient-one `PhysicalSchurMatrixData`
represents `sqrt p.c` times the raw physical trace and uses the normalized regulator
`η / sqrt p.c`.  This is exactly the factorization proved in
`physicalAbsorbedPencil_eq_sqrt_smul_normalized`. -/
structure ScaledPhysicalSchurMatrixData
    {p : Params} (M : Law.{0} p)
    (g : ZMod p.n → M.Ω → ℝ) (η : ℝ) where
  normalized : PhysicalSchurMatrixData M
    (fun j ω => Real.sqrt p.c * g j ω) (η / Real.sqrt p.c)

/-- The scaled physical Schur data supplies one-block averaging for the raw trace,
with constant `input.C / sqrt p.c`. -/
theorem ScaledPhysicalSchurMatrixData.singleBlockAveraging
    (input : PSSSInput.{0}) {p : Params} (M : Law.{0} p)
    {g : ZMod p.n → M.Ω → ℝ} {η : ℝ} (hη : 0 < η)
    (h : ScaledPhysicalSchurMatrixData M g η) :
    SingleBlockAveraging M.P g (scaledPhysicalPSSSConstant input p) (p.W : ℝ) := by
  have hs : 0 < Real.sqrt p.c := Real.sqrt_pos.2 p.c_pos
  have hηnorm : 0 < η / Real.sqrt p.c := div_pos hη hs
  have havg : SingleBlockAveraging M.P
      (fun j ω => Real.sqrt p.c * g j ω) input.C (p.W : ℝ) :=
    h.normalized.toProjectedWegnerInstantiation.singleBlockAveraging
      input M hηnorm
  exact singleBlockAveraging_of_pos_smul M.P g hs input.C (p.W : ℝ) havg

/-- Finite-union projected Wegner estimate for the raw physical block
traces.  The exact scalar loss is `1 / sqrt p.c`. -/
theorem projectedWegner_gaussianRing_of_scaledSchurMatrixData
    (input : PSSSInput.{0}) {p : Params} (M : Law.{0} p)
    {g : ZMod p.n → M.Ω → ℝ} {η : ℝ} (hη : 0 < η)
    (h : ScaledPhysicalSchurMatrixData M g η)
    (B : Finset (ZMod p.n)) (hproj : ProjectedTraceDecomposition g B) :
    ∫ ω, hproj.projectedTrace ω ∂M.P ≤
      Real.pi * scaledPhysicalPSSSConstant input p * (p.W : ℝ) *
        (B.card : ℝ) :=
  projectedWegner_of_singleBlock M.P g
    (scaledPhysicalPSSSConstant input p) (p.W : ℝ)
    (h.singleBlockAveraging input M hη) B hproj

/-- Expanded form of the scaled projected bound, displaying the
normalization loss explicitly. -/
theorem projectedWegner_gaussianRing_of_scaledSchurMatrixData_div_sqrt
    (input : PSSSInput.{0}) {p : Params} (M : Law.{0} p)
    {g : ZMod p.n → M.Ω → ℝ} {η : ℝ} (hη : 0 < η)
    (h : ScaledPhysicalSchurMatrixData M g η)
    (B : Finset (ZMod p.n)) (hproj : ProjectedTraceDecomposition g B) :
    ∫ ω, hproj.projectedTrace ω ∂M.P ≤
      Real.pi * (input.C / Real.sqrt p.c) * (p.W : ℝ) *
        (B.card : ℝ) := by
  exact projectedWegner_gaussianRing_of_scaledSchurMatrixData
    input M hη h B hproj

/-- Direct regulated-resolvent specialization with the scaled diagonal-variance
factor.  Supplying `ScaledPhysicalSchurMatrixData` amounts to proving the normalized
pointwise Schur factorization for this concrete physical pencil. -/
theorem projectedWegner_gaussianRing_resolvent_of_scaledSchurMatrixData
    (input : PSSSInput.{0}) {p : Params} (M : Law.{0} p)
    (e : ℝ) {η : ℝ} (hη : 0 < η)
    (H Γ : M.Ω → Matrix (ZMod p.n × Fin p.W) (ZMod p.n × Fin p.W) ℂ)
    (h : ScaledPhysicalSchurMatrixData M
      (fun j ω => blockNegativeImaginaryTrace
        (physicalAbsorbedResolvent H Γ e η ω) j) η)
    (B : Finset (ZMod p.n)) :
    ∫ ω, ∑ j ∈ B, blockNegativeImaginaryTrace
        (physicalAbsorbedResolvent H Γ e η ω) j ∂M.P ≤
      Real.pi * (input.C / Real.sqrt p.c) * (p.W : ℝ) *
        (B.card : ℝ) := by
  exact projectedWegner_gaussianRing_of_scaledSchurMatrixData_div_sqrt
    input M hη h B
      (projectedTraceDecomposition_of_blocks
        (physicalAbsorbedResolvent H Γ e η) B)

end GaussianRing
end CoareaNative.BlockBand
