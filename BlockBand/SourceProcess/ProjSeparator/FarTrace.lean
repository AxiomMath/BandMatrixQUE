module

public import BlockBand.SourceProcess.ProjSeparator.Bounds
public import BlockBand.SourceProcess.TagBirth.FreshTrace
public import BlockBand.SourceProcess.FullSource.DeltaMoments

/-!
# The far part of the injection: deterministic bound

The far part of `C_+` has trace `O(g)`, because its weighted factors stay attached and
`Tr ℝ₁₂ℝ₁₂* = g/(4η²)`. Here `D₊ = [𝒢₁₂, 𝒢₁₁Kℝ₁₂]` (`freshD`) and `P = nearProjection W`.

* `trace_far_eq`: `Tr(D*D(I-P)) = frob(𝒢₁₁Kℝ₁₂)` (the far columns of `D₊`);
* `g11K_eq`: `𝒢₁₁K = I + RΔ` (passive `X`, from `𝒢₁₁ = R + RΔR`);
* `frob_mul_le`: `frob(AQ) ≤ ‖A‖² frob Q`;
* `norm_trace_far_le`: `|Tr(D*D(I-P))| ≤ (1 + η⁻¹‖Δ‖)² g/(4η²)` for every sample (Hermitian `𝕏`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ProjSeparator

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PassiveLayer
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `Tr(D*D(I-P)) = Σ_{x,y}|D_{x,(1,y)}|²`. -/
theorem trace_far_eq (D : Matrix (Fin W) (Fin 2 × Fin W) ℂ) :
    (Dᴴ * D * (1 - nearProjection W)).trace =
      ((frob (Matrix.of fun x y => D x ((1 : Fin 2), y)) : ℝ) : ℂ) := by
  have hP : (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - nearProjection W =
      Matrix.diagonal fun c => if c.1 = 0 then 0 else 1 := by
    rw [nearProjection, ← Matrix.diagonal_one, Matrix.diagonal_sub]
    congr 1; funext c; by_cases h : c.1 = 0 <;> simp [h]
  rw [hP, Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_diagonal, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [Fin.isValue, ↓reduceIte, mul_zero, Finset.sum_const_zero, zero_add, mul_one,
    one_ne_zero, frob, Matrix.of_apply, Matrix.mul_apply, conjTranspose_apply]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

/-- The far columns of `D₊` are `𝒢₁₁Kℝ₁₂`. -/
theorem freshD_far (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    (Matrix.of fun x y => freshD b E XX ω x ((1 : Fin 2), y)) =
      g11 E (boundaryZ b E) (nearSchur (boundaryZ b E) XX) ω *
        (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - nearSchur (boundaryZ b E) XX) *
        farQ b E XX := by
  ext x y
  simp only [Matrix.of_apply, freshD, Fin.isValue, one_ne_zero, ↓reduceIte]
  rfl

/-- `𝒢₁₁K = I + RΔ` at a passive `X`. -/
theorem g11K_eq {b E : ℝ} (hη : 0 < etaZ b E) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) (ω : LayerSample W .oneBlockOnePort) :
    g11 E (boundaryZ b E) X ω * (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X) =
      1 + passiveResolvent b E X * freshDelta b E X ω := by
  have hK := (isUnit_iff_isUnit_det _).mp (TagBirth.isUnit_pencil hη hY)
  have hRK : passiveResolvent b E X * (boundaryZ b E • 1 - X) = 1 := Matrix.nonsing_inv_mul _ hK
  rw [TagBirth.g11_eq_resolvent_add hη hY, Matrix.add_mul, hRK, Matrix.mul_assoc _ _
    (boundaryZ b E • 1 - X), hRK, Matrix.mul_one]

/-- `frob(AQ) ≤ ‖A‖² frob Q`. -/
theorem frob_mul_le (A Q : Matrix (Fin W) (Fin W) ℂ) : frob (A * Q) ≤ ‖A‖ ^ 2 * frob Q := by
  rw [← sum_vecNorm_colQ_sq (A * Q), ← sum_vecNorm_colQ_sq Q, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have e : colQ (A * Q) j = A *ᵥ colQ Q j := (mulVec_colQ A Q j).symm
  rw [e, ← mul_pow]
  exact pow_le_pow_left₀ (vecNorm_nonneg _) (vecNorm_mulVec_le A _) 2

/-- **`|Tr(D*D(I-P))| ≤ (1 + η⁻¹‖Δ‖)² g/(4η²)`.** -/
theorem norm_trace_far_le {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hXX : XX.IsHermitian)
    (ω : LayerSample W .oneBlockOnePort) :
    ‖((freshD b E XX ω)ᴴ * freshD b E XX ω * (1 - nearProjection W)).trace‖ ≤
      (1 + (etaZ b E)⁻¹ * ‖freshDelta b E (nearSchur (boundaryZ b E) XX) ω‖) ^ 2 *
        (conductanceOf (passiveTransmission b E (nearSchur (boundaryZ b E) XX)) /
          (4 * etaZ b E ^ 2)) := by
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hY := FullSource.nearSchur_passive (z := boundaryZ b E) hη hXX
  rw [trace_far_eq, freshD_far, g11K_eq hη hY, Complex.norm_real,
    Real.norm_of_nonneg (frob_nonneg _), ← frob_farQ hb0 hb h1 h2 hXX]
  refine (frob_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (frob_nonneg _))
  have hR := norm_passiveResolvent_le hb0 hb h1 h2 hY
  have hA : ‖(1 : Matrix (Fin W) (Fin W) ℂ) + passiveResolvent b E (nearSchur (boundaryZ b E) XX) *
      freshDelta b E (nearSchur (boundaryZ b E) XX) ω‖ ≤
      1 + (etaZ b E)⁻¹ * ‖freshDelta b E (nearSchur (boundaryZ b E) XX) ω‖ := by
    refine (norm_add_le _ _).trans (add_le_add norm_one_matrix_le ?_)
    exact (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right hR (norm_nonneg _))
  exact pow_le_pow_left₀ (norm_nonneg _) hA 2

end BlockBand.SourceProcess.ProjSeparator
