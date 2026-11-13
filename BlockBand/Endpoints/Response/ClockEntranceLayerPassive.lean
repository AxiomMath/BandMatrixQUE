module

public import BlockBand.Endpoints.Response.ClockEntranceLayerLogistic

/-!
# Passivity of the old path and measurability of the fresh one-port `L`

* `cel_passiveY_nearSchur` — for a Hermitian two-port Schur matrix `𝕏` and `Im z > 0`, the
  far-eliminated `X = 𝕏₀₀ + 𝕏₀₁(z - 𝕏₁₁)⁻¹𝕏₁₀` is passive:
  `-Im X = (Im z)(𝕏₀₁R)(𝕏₀₁R)* ⪰ 0`, `R = (z - 𝕏₁₁)⁻¹`.
* `cel_pathX_passive` — **the owed fact**: `pathX j ω` is passive for every sample with
  Hermitian GUE blocks, hence `growthPathLaw`-a.s. (`ae_growthPath_isHermitian`); this is what
  allows the `X`-uniform clauses to be applied at `X = X_j`. No invertibility is needed (the
  totalized inverse of the Hermitian `H_j - E` is Hermitian).
* `cel_measurable_freshL` — `ν ↦ freshL b E X ν` is measurable.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Matrix
open scoped ENNReal ComplexOrder
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Endpoints BlockBand.Internal.Contracts.Layers
open BlockBand.Transmission (matrixImaginaryPart)

variable {W : ℕ}

/-- **Far-port elimination preserves passivity**: for Hermitian `𝕏` and `Im z > 0`,
`-Im(nearSchur z 𝕏) = (Im z)(𝕏₀₁R)(𝕏₀₁R)* ⪰ 0`, `R = (z - 𝕏₁₁)⁻¹`. -/
theorem cel_passiveY_nearSchur {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hXX : XX.IsHermitian) {z : ℂ} (hz : 0 < z.im) : (passiveY (nearSchur z XX)).PosSemidef := by
  set X01 := portBlock XX 0 1
  have h10 : portBlock XX 1 0 = X01ᴴ := by
    ext a c
    simp only [X01, portBlock, conjTranspose_apply, of_apply]
    exact (hXX.apply _ _).symm
  have h00 : (portBlock XX 0 0)ᴴ = portBlock XX 0 0 := by
    ext a c
    simp only [portBlock, conjTranspose_apply, of_apply]
    exact hXX.apply _ _
  have h11 : (portBlock XX 1 1).IsHermitian := by
    ext a c
    simp only [portBlock, conjTranspose_apply, of_apply]
    exact hXX.apply _ _
  set N := z • (1 : Matrix (Fin W) (Fin W) ℂ) - portBlock XX 1 1
  have hNu : IsUnit N.det := isUnit_det_sub_hermitian h11 hz
  set R := N⁻¹
  have hRN : R * N = 1 := nonsing_inv_mul N hNu
  have hNh : Nᴴ - N = (star z - z) • (1 : Matrix (Fin W) (Fin W) ℂ) := by
    simp only [N, conjTranspose_sub, conjTranspose_smul, conjTranspose_one, h11.eq]
    rw [sub_smul]; abel
  have hRR : R - Rᴴ = (star z - z) • (R * Rᴴ) := by
    have e1 : R * Nᴴ * Rᴴ = R := by
      rw [Matrix.mul_assoc, ← conjTranspose_mul, hRN, conjTranspose_one, Matrix.mul_one]
    have e2 : R * N * Rᴴ = Rᴴ := by rw [hRN, Matrix.one_mul]
    calc R - Rᴴ = R * Nᴴ * Rᴴ - R * N * Rᴴ := by rw [e1, e2]
      _ = R * (Nᴴ - N) * Rᴴ := by rw [Matrix.mul_sub R Nᴴ N, Matrix.sub_mul]
      _ = _ := by rw [hNh, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  have hM : nearSchur z XX - (nearSchur z XX)ᴴ = X01 * (R - Rᴴ) * X01ᴴ := by
    simp only [nearSchur, h10]
    rw [conjTranspose_add, conjTranspose_mul, conjTranspose_mul, h00, conjTranspose_conjTranspose]
    simp only [R, N, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    abel
  have hscal : -(-Complex.I / 2 * (star z - z)) = ((z.im : ℝ) : ℂ) := by
    apply Complex.ext <;> simp; ring
  have hY : passiveY (nearSchur z XX) = ((z.im : ℝ) : ℂ) • ((X01 * R) * (X01 * R)ᴴ) := by
    rw [passiveY, matrixImaginaryPart, hM, hRR, ← hscal, neg_smul, conjTranspose_mul]
    congr 1
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]
  rw [hY]
  exact (posSemidef_self_mul_conjTranspose (X01 * R)).smul (Complex.zero_le_real.mpr hz.le)

/-- **`pathX j ω` is passive** for every sample with Hermitian GUE blocks: `-Im X_j ⪰ 0`. -/
theorem cel_pathX_passive {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) (j : ℕ)
    {ω : GrowthPath W} (hω : ∀ k, (ω.1 k).IsHermitian) :
    (passiveY (pathX b E W j ω)).PosSemidef := by
  rw [cec_pathX_eq]
  exact cel_passiveY_nearSchur (cec_portSchur_isHermitian (E := E) (r := j) hω)
    (pfi_boundaryZ_im_pos hb hE1 hE2)

/-- **`pathX j` is passive almost surely** under `growthPathLaw`. -/
theorem cel_ae_pathX_passive {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) (j : ℕ) :
    ∀ᵐ ω ∂growthPathLaw W b, (passiveY (pathX b E W j ω)).PosSemidef := by
  filter_upwards [ae_growthPath_isHermitian W b] with ω hω
  exact cel_pathX_passive hb hE1 hE2 j hω

/-- The fresh one-port layer matrix `[[A - E - X, B],[B*, zI]]` is measurable in the layer. -/
theorem cel_measurable_layerMatrix (E : ℝ) (z : ℂ)
    (X : Matrix (PhysSite W .oneBlockOnePort) (PhysSite W .oneBlockOnePort) ℂ) :
    Measurable fun ν : LayerSample W .oneBlockOnePort => layerMatrix .oneBlockOnePort E z X ν := by
  have hbond : Measurable fun ν : LayerSample W .oneBlockOnePort =>
      bondMatrix .oneBlockOnePort ν.2 := by
    refine Measurable.of_eval fun x => Measurable.of_eval fun y => ?_
    by_cases h : LayerShape.incident .oneBlockOnePort x.1 y.1 = true
    · simp only [bondMatrix, h, ite_true]
      exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp
        ((measurable_pi_apply _).comp ((measurable_pi_apply _).comp measurable_snd)))
    · simp only [bondMatrix, h]
      exact measurable_const
  unfold layerMatrix
  refine measurable_fromBlocks ?_ hbond ?_ measurable_const
  · refine Measurable.of_eval fun x => Measurable.of_eval fun y => ?_
    simp only [Matrix.sub_apply]
    refine Measurable.sub (Measurable.sub ?_ measurable_const) measurable_const
    by_cases h : x.1 = y.1
    · simp only [BlockBand.Internal.Contracts.Layers.blockDiag, h, ite_true]
      exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp
        ((measurable_pi_apply _).comp measurable_fst))
    · simp only [BlockBand.Internal.Contracts.Layers.blockDiag, h, ite_false]
      exact measurable_const
  · refine Measurable.of_eval fun x => Measurable.of_eval fun y => ?_
    simp only [conjTranspose_apply]
    exact continuous_star.measurable.comp
      ((measurable_pi_apply _).comp ((measurable_pi_apply _).comp hbond))

/-- `ν ↦ freshL b E X ν = K𝒢₁₂(X, ν)` is measurable. -/
theorem cel_measurable_freshL (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    Measurable fun ν : LayerSample W .oneBlockOnePort => freshL b E X ν := by
  have hinv : Measurable fun ν : LayerSample W .oneBlockOnePort => freshLayer b E X ν :=
    pfi_measurable_inv.comp (cel_measurable_layerMatrix E _ _)
  refine Measurable.of_eval fun x => Measurable.of_eval fun y => ?_
  simp only [freshL, Matrix.mul_apply, Matrix.of_apply]
  exact Finset.measurable_sum _ fun k _ => measurable_const.mul
    ((measurable_pi_apply _).comp ((measurable_pi_apply _).comp hinv))

end BlockBand.Endpoints
