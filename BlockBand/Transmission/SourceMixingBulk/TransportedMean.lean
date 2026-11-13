module

public import BlockBand.Transmission.SourceMixingBulk.ThreeBlock
public import BlockBand.Transmission.SourceMixing.TransportedMean

/-!
# The transported mean, uniformly on the bulk

The estimate `transportedF_mean` for `E(Lf₊L*)` with constants uniform in `E ∈ bulkInterval κ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.SourceMixingBulk

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.LengthUniform
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.PathScalar
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- The transported mean `E(Lf₊L*)` at the layer level.
The version of `transportedF_mean` with constants uniform on `bulkInterval κ`. -/
theorem transportedF_mean_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef →
        ‖matrixExpect (freshLaw W b) (freshTransportedF b E X) -
          ((thetaOf b E X * sOne b E X) • (kmOf b E X * mOf b E X * (kmOf b E X)ᴴ) +
            (rhoOf b E X - cZero b E * sOne b E X) • (kmOf b E X * (kmOf b E X)ᴴ))‖ ≤
          C / (W : ℝ) ^ 2 := by
  obtain ⟨C₃, W₃, hC₃, h3⟩ := threeBlock_bulk hA hb0 hb hκ
  obtain ⟨Cf, Wf, hCf, hF⟩ := freshU_mean_bulk hA hb0 hb hκ
  obtain ⟨Cw, Ww, -, hw⟩ := wordMean_bound_bulk hA hb0 hb hκ 3 1
  obtain ⟨CD, WD, -, hD⟩ := dressedBlocks_bulk hA hb0 hb hκ
  have h1b : 0 < 1 - b := by linarith
  refine ⟨C₃ + 1 / ((1 - b) * κ) * Cf, max (max W₃ Wf) (max Ww WD), by positivity,
    fun W hW E hEκ X hX => ?_⟩
  have h1 : -2 < E := by have := hEκ.1; linarith
  have h2 : E < 2 := by have := hEκ.2; linarith
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW₃, hWf⟩, hWw, hWD⟩ := hW
  obtain ⟨hW1, -⟩ := hD W hWD E hEκ X hX
  obtain ⟨-, -, hU⟩ := hF W hWf E hEκ X hX
  have hT3 := h3 W hW₃ E hEκ X hX
  set μ := layerLaw W b .oneBlockOnePort
  set Kh := kHat b E X
  set W3 : LayerSample W .oneBlockOnePort → LayerMat W := fun ω =>
    gRes b E X ω * (SourceMixing.pTwo * (gRes b E X ω * (SourceMixing.pTwo * (Kh * gRes b E X ω)ᴴ)))
  set W2 : LayerSample W .oneBlockOnePort → LayerMat W := fun ω =>
    gRes b E X ω * (SourceMixing.pTwo * (Kh * gRes b E X ω)ᴴ)
  have hi3 : ∀ α β, Integrable (fun ω => W3 ω α β) μ := fun α β => by
    have h := (hw W hWw E hEκ X hX.posSemidef 3 le_rfl ![0, 0, 3] ![1, SourceMixing.pTwo, SourceMixing.pTwo, 1] norm_ins4_le).1 α β
    have e : (fun ω => wordVal (kHat b E X) (gRes b E X ω) ![0, 0, 3] ![1, SourceMixing.pTwo, SourceMixing.pTwo, 1] α β) =
        fun ω => W3 ω α β := funext fun ω => by rw [wordVal_W3]
    rw [e] at h; exact h
  have hi2 : ∀ α β, Integrable (fun ω => W2 ω α β) μ := fun α β => by
    have h := (hw W hWw E hEκ X hX.posSemidef 2 (by norm_num) ![0, 3] ![1, SourceMixing.pTwo, 1] norm_ins_le).1 α β
    have e : (fun ω => wordVal (kHat b E X) (gRes b E X ω) ![0, 3] ![1, SourceMixing.pTwo, 1] α β) =
        fun ω => W2 ω α β := funext fun ω => by rw [wordVal_GPKGstar]
    rw [e] at h; exact h
  -- the a.e. identity `Lf₊L* = (K̂W₃)₀₀ - c₀(K̂W₂)₀₀`
  have hz : 0 < (boundaryZ b E).im := etaZ_pos b E (by linarith) h1 h2
  have hae : ∀ᵐ ω ∂μ, freshTransportedF b E X ω =
      blkAt (Kh * W3 ω) 0 0 - cZero b E • blkAt (Kh * W2 ω) 0 0 := by
    filter_upwards [ae_g22_eq_Rplus hb0 hb hW1 E hz hX.posSemidef] with ω hω
    rw [blkAt_three, blkAt_freshU, freshTransportedF, passiveF, passiveResolvent, ← hω, freshU]
    change lAt E (boundaryZ b E) X ω * (g22 E (boundaryZ b E) X ω - cZero b E • 1) *
      (lAt E (boundaryZ b E) X ω)ᴴ = _
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    rfl
  have hiA : ∀ x y, Integrable (fun ω => blkAt (Kh * W3 ω) 0 0 x y) μ := fun x y =>
    integrable_mul_entries Kh W3 hi3 _ _
  have hiB : ∀ x y, Integrable (fun ω => blkAt (Kh * W2 ω) 0 0 x y) μ := fun x y =>
    integrable_mul_entries Kh W2 hi2 _ _
  have hE : matrixExpect μ (freshTransportedF b E X) =
      blkAt (Kh * matrixExpect μ W3) 0 0 - cZero b E • matrixExpect μ (freshU b E X) := by
    rw [matrixExpect_congr_ae hae, matrixExpect_sub_smul _ _ _ hiA hiB, mul_matrixExpect' _ _ hi3,
      blkAt_matrixExpect]
    congr 2
    rw [← blkAt_matrixExpect (F := fun ω => Kh * W2 ω), ← mul_matrixExpect' _ _ hi2]
    rw [mul_matrixExpect' _ _ hi2, blkAt_matrixExpect]
    exact congrArg (matrixExpect μ) (funext fun ω => blkAt_freshU b E X ω)
  rw [hE]
  have e : blkAt (Kh * matrixExpect μ W3) 0 0 - cZero b E • matrixExpect μ (freshU b E X) -
      ((thetaOf b E X * sOne b E X) • (kmOf b E X * mOf b E X * (kmOf b E X)ᴴ) +
        (rhoOf b E X - cZero b E * sOne b E X) • (kmOf b E X * (kmOf b E X)ᴴ)) =
      (blkAt (Kh * matrixExpect μ W3) 0 0 -
        ((thetaOf b E X * sOne b E X) • (kmOf b E X * mOf b E X * (kmOf b E X)ᴴ) +
          rhoOf b E X • (kmOf b E X * (kmOf b E X)ᴴ))) -
      cZero b E • (matrixExpect μ (freshU b E X) - sOne b E X • (kmOf b E X * (kmOf b E X)ᴴ)) := by
    rw [sub_smul, smul_sub, smul_smul]; abel
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have hc := norm_cZero_le hb hκ hEκ
  have hCfW : 0 ≤ Cf / (W : ℝ) ^ 2 := by positivity
  calc _ ≤ C₃ / (W : ℝ) ^ 2 + ‖cZero b E‖ * (Cf / (W : ℝ) ^ 2) :=
        add_le_add hT3 ((norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left hU (norm_nonneg _)))
    _ ≤ C₃ / (W : ℝ) ^ 2 + 1 / ((1 - b) * κ) * (Cf / (W : ℝ) ^ 2) := by
        gcongr
    _ = _ := by ring

end BlockBand.Transmission.SourceMixingBulk
