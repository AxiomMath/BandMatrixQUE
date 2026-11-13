module

public import BlockBand.SourceProcess.FullSourceCovariance.Decomposition
public import BlockBand.Transmission.PassiveCovarianceBulk.Scalars

/-!
# The two letter forms `F = x*K𝒢₁₁y` and `H = y*𝒢₁₁Ky'` through `Δ`

* `K_mul_g11`: `K𝒢₁₁ = ΔR + I`; `g11_mul_K`: `𝒢₁₁K = RΔ + I` (from `Δ = K𝒢₁₁K - K`);
* `fForm_eq`: `F(x,y) = x*Δ(Ry) + x*y`; `hForm_eq`: `H(y,y') = (Rᴴy)*Δy' + y*y'`.

Hence (`rightForms_bulk hGA hLp`, uniform on `bulkInterval κ`, every passive `X`):
`‖F⁰‖_p, ‖H⁰‖_p ≤ C W^{-1/2}‖·‖‖·‖` (`deltaFluctuation_all`) and
`EF = x*y + x*EΔ(Ry)`, `EH = y*y' + (Rᴴy)*EΔy'` — so `EF, EH` are the identity forms up to
`η⁻¹‖EΔ‖ = O(δ₀ + W⁻²)` (`deltaMean_strict`). This is the README's "key shortcut".
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceCovariance

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

theorem isUnit_K {b E : ℝ} (hη : 0 < etaZ b E) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) :
    IsUnit (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X) := by
  apply isUnit_of_matrixImaginaryPart_posDef
  rw [matrixImaginaryPart_nearPencil]
  exact Matrix.PosDef.posSemidef_add hY (Matrix.PosDef.one.smul hη)

theorem R_mul_K {b E : ℝ} (hη : 0 < etaZ b E) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) :
    passiveResolvent b E X * (boundaryZ b E • 1 - X) = 1 :=
  Matrix.nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp (isUnit_K hη hY))

theorem K_mul_R {b E : ℝ} (hη : 0 < etaZ b E) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) :
    (boundaryZ b E • 1 - X) * passiveResolvent b E X = 1 :=
  Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp (isUnit_K hη hY))

theorem K_mul_g11 {b E : ℝ} (hη : 0 < etaZ b E) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) (ω : LayerSample W .oneBlockOnePort) :
    (boundaryZ b E • 1 - X) * g11 E (boundaryZ b E) X ω =
      freshDelta b E X ω * passiveResolvent b E X + 1 := by
  have h := K_mul_R hη hY
  rw [FullSource.freshDelta_eq]
  set K := boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X
  set g := g11 E (boundaryZ b E) X ω
  symm
  calc (K * g * K - K) * passiveResolvent b E X + 1 =
      K * g * (K * passiveResolvent b E X) - K * passiveResolvent b E X + 1 := by
        rw [Matrix.sub_mul, Matrix.mul_assoc]
    _ = K * g := by rw [h, Matrix.mul_one]; abel

theorem g11_mul_K {b E : ℝ} (hη : 0 < etaZ b E) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) (ω : LayerSample W .oneBlockOnePort) :
    g11 E (boundaryZ b E) X ω * (boundaryZ b E • 1 - X) =
      passiveResolvent b E X * freshDelta b E X ω + 1 := by
  have h := R_mul_K hη hY
  rw [FullSource.freshDelta_eq]
  set K := boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X
  set g := g11 E (boundaryZ b E) X ω
  symm
  calc passiveResolvent b E X * (K * g * K - K) + 1 =
      (passiveResolvent b E X * K) * g * K - passiveResolvent b E X * K + 1 := by
        rw [Matrix.mul_sub, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
    _ = g * K := by rw [h, Matrix.one_mul]; abel

theorem fForm_eq {b E : ℝ} (hη : 0 < etaZ b E) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) (x y : Fin W → ℂ) (ω : LayerSample W .oneBlockOnePort) :
    fForm b E X x y ω =
      bilinear x (freshDelta b E X ω) (passiveResolvent b E X *ᵥ y) + bilinear x 1 y := by
  rw [fForm, form_physVec, (SourceMixing.blkAt_kHat_mul_zero b E X _).1, blkAt_gRes_zero,
    K_mul_g11 hη hY, PassiveCovariance.bilinear_add, bilinear_mulVec_right]

theorem hForm_eq {b E : ℝ} (hη : 0 < etaZ b E) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) (y y' : Fin W → ℂ) (ω : LayerSample W .oneBlockOnePort) :
    hForm b E X y y' ω =
      bilinear ((passiveResolvent b E X)ᴴ *ᵥ y) (freshDelta b E X ω) y' + bilinear y 1 y' := by
  rw [hForm, mulVec_mulVec, form_physVec, blkAt_mul_kHat_zero, blkAt_gRes_zero,
    g11_mul_K hη hY, PassiveCovariance.bilinear_add, bilinear_conjT_left]

/-- `F`, `H` centred and in mean through `Δ` (every passive `X`, bulk-uniform). -/
theorem rightForms_bulk (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) {b κ : ℝ}
    (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ) (p : ℝ) (hp : 1 ≤ p) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef → ∀ u v : Fin W → ℂ,
        eLpNorm (fun ω => fForm b E X u v ω - ∫ ω', fForm b E X u v ω' ∂freshLaw W b)
            (ENNReal.ofReal p) (freshLaw W b) ≤
          ENNReal.ofReal (C / Real.sqrt W * vecNorm u * vecNorm v) ∧
        eLpNorm (fun ω => hForm b E X u v ω - ∫ ω', hForm b E X u v ω' ∂freshLaw W b)
            (ENNReal.ofReal p) (freshLaw W b) ≤
          ENNReal.ofReal (C / Real.sqrt W * vecNorm u * vecNorm v) ∧
        (∫ ω, fForm b E X u v ω ∂freshLaw W b) = bilinear u 1 v +
          bilinear u (matrixExpect (freshLaw W b) (freshDelta b E X)) (passiveResolvent b E X *ᵥ v) ∧
        (∫ ω, hForm b E X u v ω ∂freshLaw W b) = bilinear u 1 v +
          bilinear ((passiveResolvent b E X)ᴴ *ᵥ u) (matrixExpect (freshLaw W b) (freshDelta b E X)) v := by
  obtain ⟨C, W₁, hC⟩ := deltaFluctuation_all hGA hLp b hb0 hb κ hκ p hp
  obtain ⟨Ci, W₂, -, hint⟩ := FullSource.delta_integrable hGA b hb0 hb κ hκ
  set C' := max C 0 * (PathScalar.etaLow b κ)⁻¹
  have hηL := PathScalar.etaLow_pos (b := b) (by linarith) hκ
  refine ⟨C', max W₁ W₂, by positivity, fun W hW E hE X hY u v => ?_⟩
  obtain ⟨h1, h2⟩ := PathScalar.bulk_bounds hκ hE
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hR : ‖passiveResolvent b E X‖ ≤ (PathScalar.etaLow b κ)⁻¹ :=
    (norm_passiveResolvent_le hb0 hb h1 h2 hY).trans (CovarianceBulk.inv_etaZ_le_bulk hb hκ hE)
  obtain ⟨hent, -⟩ := hint W (le_of_max_le_right hW) E hE X hY
  set μ := freshLaw W b
  set D := matrixExpect μ (freshDelta b E X)
  set R := passiveResolvent b E X
  have hfl := fun (u v : Fin W → ℂ) => hC W (le_of_max_le_left hW) E hE X hY u v
  have hRv : vecNorm (R *ᵥ v) ≤ (PathScalar.etaLow b κ)⁻¹ * vecNorm v :=
    (vecNorm_mulVec_le' _ _).trans (by gcongr; exact PassiveCovariance.vecNorm_nonneg v)
  have hRu : vecNorm (Rᴴ *ᵥ u) ≤ (PathScalar.etaLow b κ)⁻¹ * vecNorm u :=
    (vecNorm_mulVec_le' _ _).trans (by
      rw [Matrix.l2_opNorm_conjTranspose]; gcongr; exact PassiveCovariance.vecNorm_nonneg u)
  have hmF : ∫ ω, fForm b E X u v ω ∂μ = bilinear u 1 v + bilinear u D (R *ᵥ v) := by
    simp only [fForm_eq hη hY]
    rw [integral_add _ (integrable_const _), integral_const, ← bilinear_matrixExpect _ _ _ hent]
    · simp; ring
    · simp only [bilinear, dotProduct, mulVec]
      exact integrable_finsetSum _ fun i _ => (integrable_finsetSum _ fun j _ =>
        (hent i j).mul_const _).const_mul _
  have hmH : ∫ ω, hForm b E X u v ω ∂μ = bilinear u 1 v + bilinear (Rᴴ *ᵥ u) D v := by
    simp only [hForm_eq hη hY]
    rw [integral_add _ (integrable_const _), integral_const, ← bilinear_matrixExpect _ _ _ hent]
    · simp; ring
    · simp only [bilinear, dotProduct, mulVec]
      exact integrable_finsetSum _ fun i _ => (integrable_finsetSum _ fun j _ =>
        (hent i j).mul_const _).const_mul _
  refine ⟨?_, ?_, hmF, hmH⟩
  · have e : (fun ω => fForm b E X u v ω - ∫ ω', fForm b E X u v ω' ∂μ) =
        fun ω => bilinear u (freshDelta b E X ω - D) (R *ᵥ v) := by
      funext ω; rw [hmF, fForm_eq hη hY, PassiveCovariance.bilinear_sub]; ring
    rw [e]
    refine (hfl u (R *ᵥ v)).trans (ENNReal.ofReal_le_ofReal ?_)
    have := PassiveCovariance.vecNorm_nonneg u; have := PassiveCovariance.vecNorm_nonneg v
    have := PassiveCovariance.vecNorm_nonneg (R *ᵥ v)
    calc C / Real.sqrt W * vecNorm u * vecNorm (R *ᵥ v) ≤
        max C 0 / Real.sqrt W * vecNorm u * vecNorm (R *ᵥ v) := by gcongr; exact le_max_left _ _
      _ ≤ max C 0 / Real.sqrt W * vecNorm u * ((PathScalar.etaLow b κ)⁻¹ * vecNorm v) := by gcongr
      _ = _ := by simp only [C']; ring
  · have e : (fun ω => hForm b E X u v ω - ∫ ω', hForm b E X u v ω' ∂μ) =
        fun ω => bilinear (Rᴴ *ᵥ u) (freshDelta b E X ω - D) v := by
      funext ω; rw [hmH, hForm_eq hη hY, PassiveCovariance.bilinear_sub]; ring
    rw [e]
    refine (hfl (Rᴴ *ᵥ u) v).trans (ENNReal.ofReal_le_ofReal ?_)
    have := PassiveCovariance.vecNorm_nonneg u; have := PassiveCovariance.vecNorm_nonneg v
    have := PassiveCovariance.vecNorm_nonneg (Rᴴ *ᵥ u)
    calc C / Real.sqrt W * vecNorm (Rᴴ *ᵥ u) * vecNorm v ≤
        max C 0 / Real.sqrt W * vecNorm (Rᴴ *ᵥ u) * vecNorm v := by gcongr; exact le_max_left _ _
      _ ≤ max C 0 / Real.sqrt W * ((PathScalar.etaLow b κ)⁻¹ * vecNorm u) * vecNorm v := by gcongr
      _ = _ := by simp only [C']; ring

end BlockBand.SourceProcess.FullSourceCovariance
