module

public import BlockBand.Critical.BoundaryMean.Domination

/-!
# The kernel quadratic form through the collar form

* `dotProduct_expectedCollarKernel`: for `Y = -Im X ≻ 0` with integrable kernel entries,
  `q*E𝒫(Ur)q = η⁻¹ E_collar f_0`, `f_0 = -Im⟨ρ*q, ℋ_X⁻¹ρ*q⟩` (`regForm b e 0`), from
  `Collar.Kernel.collar_poissonKernel_quad` (a.s.: Hermitian blocks, invertible middle block).
* `poissonKernel_isHermitian`, `matrixExpect_isHermitian`: `E𝒫` is Hermitian, so its operator
  norm is controlled by its quadratic form (`NormBound`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.BoundaryMean

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open BlockBand.Critical.Collar.Density (collarMatrix collarRowVec collarRowConst)
open BlockBand.Critical.Collar.Kernel (topLift rePart)
open BlockBand.Critical.Collar (stdCauchy)
open scoped ComplexOrder ENNReal Matrix.Norms.L2Operator

variable {W : ℕ}

section Expect

variable {ι : Type*} {Ω : Type*} [MeasurableSpace Ω]

/-- `q*(E P)q = E q*Pq` for a random matrix with integrable entries. -/
theorem dotProduct_matrixExpect_mulVec [Fintype ι] {μ : Measure Ω} {P : Ω → Matrix ι ι ℂ}
    (hent : ∀ i j, Integrable (fun ω => P ω i j) μ) (q : ι → ℂ) :
    star q ⬝ᵥ (matrixExpect μ P *ᵥ q) = ∫ ω, star q ⬝ᵥ (P ω *ᵥ q) ∂μ := by
  simp only [dotProduct, mulVec, matrixExpect, Matrix.of_apply]
  rw [integral_finsetSum _ fun i _ => ((integrable_finsetSum _ fun j _ =>
    (hent i j).mul_const (q j)).const_mul (star q i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, integral_finsetSum _ fun j _ => (hent i j).mul_const (q j)]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_mul_const]

/-- The entrywise expectation of a pointwise Hermitian random matrix is Hermitian. -/
theorem matrixExpect_isHermitian {μ : Measure Ω} {P : Ω → Matrix ι ι ℂ}
    (hP : ∀ ω, (P ω).IsHermitian) : (matrixExpect μ P).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, matrixExpect, Matrix.of_apply]
  rw [Complex.star_def, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  exact (hP ω).apply i j

end Expect

/-- `𝒫(V) = (I-V)⁻¹ + (I-V*)⁻¹ - I` is Hermitian for every `V`. -/
theorem poissonKernel_isHermitian {ι : Type*} [Fintype ι] [DecidableEq ι] (V : Matrix ι ι ℂ) :
    (BlockBand.Internal.Contracts.Critical.poissonKernel V).IsHermitian := by
  rw [IsHermitian, BlockBand.Internal.Contracts.Critical.poissonKernel, conjTranspose_sub, conjTranspose_add, conjTranspose_one,
    conjTranspose_nonsing_inv, conjTranspose_nonsing_inv, conjTranspose_sub, conjTranspose_sub,
    conjTranspose_one, conjTranspose_conjTranspose]
  abel

/-- **The kernel quadratic form through the collar form** (`Y ≻ 0`, `t = 1`, zero height and
shift): `q*E𝒫(Ur)q = η⁻¹ E_collar f_0`, `f_0 = -Im⟨ρ*q, ℋ_X⁻¹ρ*q⟩`. -/
theorem dotProduct_expectedCollarKernel {b : ℝ} (hb : b < 1 / 2) (e : ℝ)
    (hη : 0 < (boundaryZ b e).im) {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hY : (-imPart X).PosDef) (hint : CollarKernelIntegrable b e 0 0 1 X)
    (q : Fin 2 × Fin W → ℂ) :
    star q ⬝ᵥ (expectedCollarKernel b e 0 0 1 X *ᵥ q) =
      (((boundaryZ b e).im⁻¹ * ∫ ω, regForm b e 0 X q ω ∂collarLaw W b : ℝ) : ℂ) := by
  rw [expectedCollarKernel, dotProduct_matrixExpect_mulVec hint q]
  have hae : ∀ᵐ ω ∂collarLaw W b, star q ⬝ᵥ (poissonKernel (((1 : ℝ) : ℂ) •
      (collarScattering b e 0 0 ω * oldScattering b e X)) *ᵥ q) =
        (((boundaryZ b e).im⁻¹ * regForm b e 0 X q ω : ℝ) : ℂ) := by
    filter_upwards [Collar.Density.ae_collarMatrix_isHermitian b e
        (Collar.Kernel.rePart_isHermitian X) (W := W),
      Collar.Kernel.ae_isUnit_det_middleBlock hb e 0 (W := W)] with ω hω hD
    rw [Complex.ofReal_one, one_smul,
      Collar.Kernel.collar_poissonKernel_quad b e 0 hη hω.2.1 hω.2.2 hD hY q,
      Collar.Kernel.collarRow_conjTranspose_mulVec b e 0 hω.2.1 q]
    simp [regForm]
  rw [integral_congr_ae hae, integral_complex_ofReal, integral_const_mul]

end BlockBand.Critical.BoundaryMean
