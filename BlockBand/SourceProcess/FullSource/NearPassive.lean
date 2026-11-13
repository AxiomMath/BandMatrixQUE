module

public import BlockBand.SourceProcess.FullSource.Measurability
public import BlockBand.Transmission.PassiveLayer.TMMain
public import BlockBand.Transmission.SchurPassivity

/-!
# Deterministic inputs of `FullSourceEstimates.moments`: passivity and block norms

For a Hermitian old two-port `𝕏` and `Im z > 0`:
* `nearSchur_passive`: `X = nearSchur z 𝕏` is passive, `-Im X = 𝕏₁₀ᴴ(-Im(z - 𝕏₁₁)⁻¹)𝕏₁₀ ⪰ 0`
  (the general version of the path statement `pathNearSchur_passive`; from
  `passiveSchurInput_negativeImaginary_posSemidef`);
* `norm_twoPortResolvent_le`: `‖ℝ‖ = ‖(z - 𝕏)⁻¹‖ ≤ η⁻¹`, `η = Im z`;
* `norm_freshTransport_le`: `‖N‖ ≤ ‖L‖ + ‖Δℝ₁₂‖ + 1` (block norms, `N = [[L, Δℝ₁₂],[0, I]]`);
* `norm_freshD_le`: `‖D₊‖ ≤ ‖𝒢₁₂‖ + ‖𝒢₁₁Kℝ₁₂‖` (`D₊ = [𝒢₁₂, 𝒢₁₁Kℝ₁₂]`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSource

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.Transmission.PassiveLayer BlockBand.Transmission.PassiveCovariance
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

theorem portBlock_conjTranspose (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i j : Fin 2) :
    (portBlock XX i j)ᴴ = portBlock XXᴴ j i := by
  ext x y; simp [portBlock, Matrix.conjTranspose_apply]

theorem portBlock_isHermitian {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hXX : XX.IsHermitian) (i : Fin 2) : (portBlock XX i i).IsHermitian := by
  rw [Matrix.IsHermitian, portBlock_conjTranspose, hXX.eq]

/-- **Passivity of the far-eliminated input** for every Hermitian `𝕏` and `Im z > 0`. -/
theorem nearSchur_passive {z : ℂ} (hz : 0 < z.im) {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hXX : XX.IsHermitian) : (passiveY (nearSchur z XX)).PosSemidef := by
  have h := BlockBand.Transmission.passiveSchurInput_negativeImaginary_posSemidef
    (portBlock XX 0 0) (portBlock_isHermitian hXX 0) (portBlock XX 1 0) (portBlock XX 1 1)
    (portBlock_isHermitian hXX 1) hz
  have e : BlockBand.Transmission.passiveSchurInput (portBlock XX 0 0) (portBlock XX 1 0)
      (portBlock XX 1 1) z = nearSchur z XX := by
    rw [BlockBand.Transmission.passiveSchurInput, nearSchur, portBlock_conjTranspose, hXX.eq]
    rfl
  rwa [e] at h

/-- `‖(z - 𝕏)⁻¹‖ ≤ η⁻¹` for Hermitian `𝕏`, `η = Im z_∂ > 0`. -/
theorem norm_twoPortResolvent_le (b E : ℝ) {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hXX : XX.IsHermitian) (hη : 0 < etaZ b E) :
    ‖twoPortResolvent b E XX‖ ≤ (etaZ b E)⁻¹ := by
  refine norm_inv_le_of_im _ 0 hη Matrix.PosSemidef.zero ?_
  have h := BlockBand.Transmission.matrixImaginaryPart_portPencil XX hXX (boundaryZ b E)
  rw [zero_add, etaZ]
  exact h

theorem norm_portBlock_le (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i j : Fin 2) :
    ‖portBlock M i j‖ ≤ ‖M‖ := by
  have hi : Function.Injective fun x : Fin W => (i, x) := fun _ _ h => by
    simpa using congrArg Prod.snd h
  have hj : Function.Injective fun x : Fin W => (j, x) := fun _ _ h => by
    simpa using congrArg Prod.snd h
  exact norm_submatrix_le M (f := fun x => (i, x)) (g := fun x => (j, x)) hi hj

/-- The reindexing `(i, x) ↦ inl x` (`i = 0`), `inr x` (`i = 1`). -/
def portSum (c : Fin 2 × Fin W) : Fin W ⊕ Fin W := if c.1 = 0 then Sum.inl c.2 else Sum.inr c.2

theorem portSum_injective : Function.Injective (portSum (W := W)) := by
  rintro ⟨i, x⟩ ⟨j, y⟩ h
  fin_cases i <;> fin_cases j <;> simp_all [portSum]

theorem freshTransport_eq_submatrix (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    freshTransport b E XX ω = (fromBlocks (freshL b E (nearSchur (boundaryZ b E) XX) ω)
      (freshDelta b E (nearSchur (boundaryZ b E) XX) ω * portBlock (twoPortResolvent b E XX) 0 1)
      0 1).submatrix portSum portSum := by
  ext ⟨i, x⟩ ⟨j, y⟩
  fin_cases i <;> fin_cases j <;> simp [freshTransport, portSum, Matrix.one_apply]

/-- `‖N‖ ≤ ‖L‖ + ‖Δℝ₁₂‖ + 1`. -/
theorem norm_freshTransport_le (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    ‖freshTransport b E XX ω‖ ≤ ‖freshL b E (nearSchur (boundaryZ b E) XX) ω‖ +
      ‖freshDelta b E (nearSchur (boundaryZ b E) XX) ω‖ * ‖twoPortResolvent b E XX‖ + 1 := by
  rw [freshTransport_eq_submatrix]
  refine (norm_submatrix_le _ portSum_injective portSum_injective).trans
    ((norm_fromBlocks_le _ _ _ _).trans ?_)
  have h1 := norm_mul_le (freshDelta b E (nearSchur (boundaryZ b E) XX) ω)
    (portBlock (twoPortResolvent b E XX) 0 1)
  have h2 := norm_portBlock_le (twoPortResolvent b E XX) 0 1
  have h3 : ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ 1 := norm_one_matrix_le
  have h4 := mul_le_mul_of_nonneg_left h2 (norm_nonneg (freshDelta b E (nearSchur (boundaryZ b E) XX) ω))
  simp only [norm_zero, add_zero]
  linarith

theorem freshD_eq_submatrix (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    freshD b E XX ω = (fromBlocks (freshBlock b E (nearSchur (boundaryZ b E) XX) ω true false)
      (freshBlock b E (nearSchur (boundaryZ b E) XX) ω true true *
        (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - nearSchur (boundaryZ b E) XX) *
        portBlock (twoPortResolvent b E XX) 0 1) (0 : Matrix (Fin W) (Fin W) ℂ)
        (0 : Matrix (Fin W) (Fin W) ℂ)).submatrix Sum.inl portSum := by
  ext x ⟨j, y⟩
  fin_cases j <;> simp [freshD, portSum]

/-- `‖D₊‖ ≤ ‖𝒢₁₂‖ + ‖𝒢₁₁K‖‖ℝ‖`. -/
theorem norm_freshD_le (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    ‖freshD b E XX ω‖ ≤ ‖freshBlock b E (nearSchur (boundaryZ b E) XX) ω true false‖ +
      ‖freshBlock b E (nearSchur (boundaryZ b E) XX) ω true true *
        (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - nearSchur (boundaryZ b E) XX)‖ *
        ‖twoPortResolvent b E XX‖ := by
  rw [freshD_eq_submatrix]
  refine (norm_submatrix_le _ Sum.inl_injective portSum_injective).trans
    ((norm_fromBlocks_le _ _ _ _).trans ?_)
  have h1 := norm_mul_le (freshBlock b E (nearSchur (boundaryZ b E) XX) ω true true *
    (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - nearSchur (boundaryZ b E) XX))
    (portBlock (twoPortResolvent b E XX) 0 1)
  have h2 := norm_portBlock_le (twoPortResolvent b E XX) 0 1
  have h4 := mul_le_mul_of_nonneg_left h2 (norm_nonneg (freshBlock b E
    (nearSchur (boundaryZ b E) XX) ω true true *
    (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - nearSchur (boundaryZ b E) XX)))
  simp only [norm_zero, add_zero]
  linarith

end BlockBand.SourceProcess.FullSource
