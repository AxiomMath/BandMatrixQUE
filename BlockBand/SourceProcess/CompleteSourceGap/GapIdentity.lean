module

public import BlockBand.SourceProcess.CompleteSourceGap.LayerIds
public import BlockBand.SourceProcess.FullSourceCovariance.WardTensor

/-!
# The complete-source gap identity

This is the closed form of the source-gap derivative. For a Hermitian `𝕏`, a sample with `A`
Hermitian, `B` invertible and `A - E - 𝕏₀₀` invertible:
* `nearRow_plus`: `ι*(z - 𝕏₊)⁻¹ = [𝒢₂₂, 𝒢₂₁𝕏₀₁D⁻¹]` (`𝕏₊ = freshTwoPortSchur`);
* `nearSel_scat_transport`: `ι*𝕊₊N* = 𝒢₂₁K ι*𝕊`;
* **`transportedSep_projS`**: `N P𝕊₊ N* = ι (L𝒢₂₁K) ι* 𝕊`; `L𝒢₂₁K = K𝒢₁₂𝒢₂₁K = -∂_wΔ` is
  `gapLetter`. This is the Wirtinger identity `2iη∂_w[N(w)N(w)*] = NP𝕊₊N*` with
  `F = -(2iη)⁻¹ι*𝕊` substituted, in closed form (no derivative is needed);
* **`transportedSep_projSProj`**: `N P𝕊₊P N* = ι L(1 - 2iη𝒢₂₂)L* ι*` (projected letter; with
  `𝒢₂₂ = R₊` a.s. this is `-2iη ι Lf₊L* ι*`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CompleteSourceGap

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.Transmission.PassiveLayer BlockBand.SourceProcess.FullSource
open scoped Matrix ComplexOrder

variable {W : ℕ}

/-- **The gap letter** `L𝒢₂₁K = K𝒢₁₂𝒢₂₁K` (`= -∂_wΔ` at `w = z`) of one fresh layer at `X`. -/
def gapLetter (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) :
    Matrix (Fin W) (Fin W) ℂ :=
  freshL b E X ω * g21 E (boundaryZ b E) X ω * (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X)

theorem layerSample_eta (ω : LayerSample W .oneBlockOnePort) :
    ω = ((fun _ => ω.1 0, fun _ _ => ω.2 0 0) : LayerSample W .oneBlockOnePort) := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => funext fun j => ?_)
  · rw [Subsingleton.elim i 0]
  · rw [Subsingleton.elim i 0, Subsingleton.elim j 0]

theorem scat_scalar (η : ℝ) : (((2 * η : ℝ) : ℂ) * Complex.I) = (2 * Complex.I) * (η : ℂ) := by
  push_cast; ring

theorem freshTwoPortSchur_isHermitian (E : ℝ) {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hXX : XX.IsHermitian) {ω : LayerSample W .oneBlockOnePort} (hA : (ω.1 0).IsHermitian) :
    (freshTwoPortSchur E XX ω).IsHermitian := by
  have hS : (ω.1 0 - (E : ℂ) • 1 - portBlock XX 0 0).IsHermitian := by
    refine (hA.sub ?_).sub (portBlock_isHermitian hXX 0)
    simp [Matrix.IsHermitian, conjTranspose_smul]
  have hG := hS.inv
  set G₀ := (ω.1 0 - (E : ℂ) • 1 - portBlock XX 0 0)⁻¹ with hG₀
  have h01 : (portBlock XX 0 1)ᴴ = portBlock XX 1 0 := by rw [portBlock_conjTranspose, hXX.eq]
  have h10 : (portBlock XX 1 0)ᴴ = portBlock XX 0 1 := by rw [portBlock_conjTranspose, hXX.eq]
  have hc : ∀ (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i k : Fin 2),
      portBlock Mᴴ i k = (portBlock M k i)ᴴ := fun M i k => by
    rw [portBlock_conjTranspose]
  have hGe : G₀ᴴ = G₀ := hG.eq
  apply portBlock_ext'
  intro i k
  rw [hc]
  simp only [freshTwoPortSchur, portBlock_ofPortBlocks, ← hG₀]
  fin_cases i <;> fin_cases k <;>
    simp [conjTranspose_mul, hGe, h01, h10, Matrix.mul_assoc, portBlock_isHermitian hXX 1 |>.eq]

/-- **Near row of the new resolvent**: `ι*(z - 𝕏₊)⁻¹ = [𝒢₂₂, 𝒢₂₁𝕏₀₁D⁻¹]`. -/
theorem nearRow_plus (b E : ℝ) {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hXX : XX.IsHermitian) (hη : 0 < etaZ b E) {ω : LayerSample W .oneBlockOnePort}
    (hA : (ω.1 0).IsHermitian) (hB : IsUnit (ω.2 0 0))
    (hS : IsUnit (ω.1 0 - (E : ℂ) • 1 - portBlock XX 0 0)) :
    nearSel W * twoPortResolvent b E (freshTwoPortSchur E XX ω) =
      rowOf (g22 E (boundaryZ b E) (nearSchur (boundaryZ b E) XX) ω)
        (g21 E (boundaryZ b E) (nearSchur (boundaryZ b E) XX) ω * portBlock XX 0 1 *
          (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - portBlock XX 1 1)⁻¹) := by
  set z := boundaryZ b E
  have hz : 0 < z.im := hη
  set X := nearSchur z XX
  have hY : (passiveY X).PosSemidef := nearSchur_passive hz hXX
  have hM : IsUnit (layerMatrix .oneBlockOnePort E z (liftX X) ω) := by
    rw [layerSample_eta ω]
    exact isUnit_layerMatrix_fresh b E X _ _ hA hY hη hB
  obtain ⟨-, -, -, -, -, -, r1, r2⟩ := layer_identities E z X ω hM
  have hG0 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hS)
  set D := z • (1 : Matrix (Fin W) (Fin W) ℂ) - portBlock XX 1 1
  have hD : IsUnit D := BlockBand.Transmission.portPencil_isUnit _ (portBlock_isHermitian hXX 1) hz
  have hDD : D⁻¹ * D = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hD)
  have hAX : ω.1 0 - (E : ℂ) • 1 - X =
      (ω.1 0 - (E : ℂ) • 1 - portBlock XX 0 0) - portBlock XX 0 1 * D⁻¹ * portBlock XX 1 0 := by
    simp only [X, nearSchur, D]; abel
  rw [hAX] at r1
  apply nearSel_mul_inv_eq _ _ (BlockBand.Transmission.portPencil_isUnit _
    (freshTwoPortSchur_isHermitian E hXX hA) hz)
  apply colBlock_ext
  intro k
  rw [colBlock_mul_two, colBlock_rowOf, colBlock_rowOf, colBlock_nearSel]
  change _ * portBlock (z • 1 - freshTwoPortSchur E XX ω) 0 k +
    _ * portBlock (z • 1 - freshTwoPortSchur E XX ω) 1 k = _
  rw [portBlock_smul_one_sub, portBlock_smul_one_sub]
  simp only [freshTwoPortSchur, portBlock_ofPortBlocks]
  fin_cases k
  · simpa [sub_neg_eq_add] using near_row_col0 _ _ _ _ _ _ _ _ (z • 1) hG0 r1 r2
  · have := near_row_col1 _ _ _ _ _ D _ _ _ hG0 hDD r1
    simpa [D, sub_neg_eq_add, sub_add_eq_sub_sub] using this

theorem colBlock_nearSel_scat (b E : ℝ) (Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i : Fin 2) :
    colBlock (nearSel W * twoPortScattering b E Y) i =
      colBlock (nearSel W) i -
        ((2 * Complex.I) * (etaZ b E : ℂ)) • colBlock (nearSel W * twoPortResolvent b E Y) i := by
  rw [twoPortScattering, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, colBlock_sub,
    colBlock_smul, scat_scalar]

theorem portBlock_conj_freshTransport (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) (i k : Fin 2) :
    portBlock (freshTransport b E XX ω)ᴴ i k =
      (if k = 0 ∧ i = 0 then freshL b E (nearSchur (boundaryZ b E) XX) ω
      else if k = 0 ∧ i = 1 then freshDelta b E (nearSchur (boundaryZ b E) XX) ω *
        portBlock (twoPortResolvent b E XX) 0 1
      else if k = 1 ∧ i = 1 then 1 else 0)ᴴ := by
  rw [← portBlock_freshTransport b E XX ω k i, portBlock_conjTranspose]

/-- **`ι*𝕊₊N* = 𝒢₂₁K ι*𝕊`** (the core of the Wirtinger identity, in closed form). -/
theorem nearSel_scat_transport (b E : ℝ) {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hXX : XX.IsHermitian) (hη : 0 < etaZ b E) {ω : LayerSample W .oneBlockOnePort}
    (hA : (ω.1 0).IsHermitian) (hB : IsUnit (ω.2 0 0))
    (hS : IsUnit (ω.1 0 - (E : ℂ) • 1 - portBlock XX 0 0)) :
    nearSel W * twoPortScattering b E (freshTwoPortSchur E XX ω) * (freshTransport b E XX ω)ᴴ =
      g21 E (boundaryZ b E) (nearSchur (boundaryZ b E) XX) ω *
        (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - nearSchur (boundaryZ b E) XX) *
        (nearSel W * twoPortScattering b E XX) := by
  set z := boundaryZ b E with hzdef
  have hz : 0 < z.im := hη
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  set X := nearSchur z XX with hXdef
  set η := etaZ b E
  have hY : (passiveY X).PosSemidef := nearSchur_passive hz hXX
  have hM : IsUnit (layerMatrix .oneBlockOnePort E z (liftX X) ω) := by
    rw [layerSample_eta ω]
    exact isUnit_layerMatrix_fresh b E X _ _ hA hY hη hB
  obtain ⟨-, -, hL3, hL4, -, hJ2, -, -⟩ := layer_identities E z X ω hM
  have hJ2' : g11 E z X ω * ω.2 0 0 = -(z • g12 E z X ω) := by
    rw [eq_neg_of_add_eq_zero_left hJ2, Matrix.mul_smul, Matrix.mul_one]
  have hzη : z - star z = 2 * Complex.I * (η : ℂ) := by
    rw [Complex.star_def, Complex.sub_conj]; simp only [η, etaZ, z]; push_cast; ring
  have hW := ward21 _ _ _ _ _ (passiveY X) z η hz0 hzη (im_g11 E hz hY hA hB) hJ2' hL3 hL4
  have hK : IsUnit (z • (1 : Matrix (Fin W) (Fin W) ℂ) - X) := by
    apply BlockBand.Transmission.isUnit_of_matrixImaginaryPart_posDef
    rw [BlockBand.Transmission.PassiveCovariance.matrixImaginaryPart_nearPencil]
    exact Matrix.PosDef.posSemidef_add hY (Matrix.PosDef.one.smul hη)
  have hKR : (z • (1 : Matrix (Fin W) (Fin W) ℂ) - X) * passiveResolvent b E X = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hK)
  have hrow := nearRow_twoPortResolvent b E hXX hη
  have hR01 : portBlock (twoPortResolvent b E XX) 0 1 = passiveResolvent b E X *
      portBlock XX 0 1 * (z • (1 : Matrix (Fin W) (Fin W) ℂ) - portBlock XX 1 1)⁻¹ := by
    have := congrArg (fun ρ => colBlock ρ 1) hrow
    simpa [colBlock_nearSel_mul, colBlock_rowOf] using this
  have hR00 : portBlock (twoPortResolvent b E XX) 0 0 = passiveResolvent b E X := by
    have := congrArg (fun ρ => colBlock ρ 0) hrow
    simpa [colBlock_nearSel_mul, colBlock_rowOf] using this
  have hKQ : (z • (1 : Matrix (Fin W) (Fin W) ℂ) - X) * portBlock (twoPortResolvent b E XX) 0 1 =
      portBlock XX 0 1 * (z • (1 : Matrix (Fin W) (Fin W) ℂ) - portBlock XX 1 1)⁻¹ := by
    rw [hR01, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hKR, Matrix.one_mul]
  have hfar : portBlock XX 0 1 * (z • (1 : Matrix (Fin W) (Fin W) ℂ) - portBlock XX 1 1)⁻¹ *
      (portBlock (twoPortResolvent b E XX) 0 1)ᴴ =
      (η : ℂ)⁻¹ • (passiveY X * (passiveResolvent b E X)ᴴ) := by
    have hfa := far_absorption b E hXX hη
    have he : (η : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hη.ne'
    rw [← hKQ, Matrix.mul_assoc, show portBlock (twoPortResolvent b E XX) 0 1 *
      (portBlock (twoPortResolvent b E XX) 0 1)ᴴ = (η : ℂ)⁻¹ • (passiveResolvent b E X *
        passiveY X * (passiveResolvent b E X)ᴴ) by rw [hfa, smul_smul, inv_mul_cancel₀ he, one_smul],
      Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hKR, Matrix.one_mul]
  have hc0 := gap_col0 (g11 E z X ω) (g12 E z X ω) (g21 E z X ω) (g22 E z X ω)
    (z • 1 - X) (passiveResolvent b E X) (passiveY X) (portBlock (twoPortResolvent b E XX) 0 1)
    (portBlock XX 0 1 * (z • (1 : Matrix (Fin W) (Fin W) ℂ) - portBlock XX 1 1)⁻¹) hη.ne' hW
    (pencil_sub_conj z X) hKR hfar
  have hplus := nearRow_plus b E hXX hη hA hB hS
  apply colBlock_ext
  intro k
  rw [colBlock_mul_two, colBlock_mul, colBlock_nearSel_scat, colBlock_nearSel_scat,
    colBlock_nearSel_scat, hplus, hrow, colBlock_rowOf, colBlock_rowOf, colBlock_rowOf,
    colBlock_nearSel, colBlock_nearSel, colBlock_nearSel, portBlock_conj_freshTransport,
    portBlock_conj_freshTransport]
  fin_cases k
  · simp only [Fin.zero_eta, Fin.isValue, ite_true, one_ne_zero, ite_false, and_self,
      and_false, zero_ne_one, false_and]
    have hL : freshL b E X ω = (z • 1 - X) * g12 E z X ω := rfl
    have hΔ : freshDelta b E X ω = (z • 1 - X) * g11 E z X ω * (z • 1 - X) - (z • 1 - X) := rfl
    rw [hL, hΔ, zero_sub, ← hc0]
    simp only [Matrix.neg_mul, Matrix.mul_assoc, sub_eq_add_neg]
    rfl
  · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ite_false, ite_true, and_self, and_false,
      zero_ne_one, false_and, conjTranspose_zero, conjTranspose_one, Matrix.mul_zero,
      Matrix.mul_one, zero_add, zero_sub, Matrix.mul_neg, Matrix.mul_smul]
    rw [← hzdef, ← hXdef, ← hR01, Matrix.mul_assoc (g21 E z X ω) (z • 1 - X), hKQ]
    simp only [Matrix.mul_assoc]

/-- `N ι = ι L`. -/
theorem freshTransport_mul_nearSel_conj (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    freshTransport b E XX ω * (nearSel W)ᴴ =
      (nearSel W)ᴴ * freshL b E (nearSchur (boundaryZ b E) XX) ω := by
  ext ⟨i, x⟩ y
  rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  fin_cases i <;> simp [freshTransport, nearSel, Matrix.conjTranspose_apply]

/-- **The complete-source gap identity** (`P𝕊`): `N P𝕊₊ N* = ι (L𝒢₂₁K) ι* 𝕊`. -/
theorem transportedSep_projS (b E : ℝ) {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hXX : XX.IsHermitian) (hη : 0 < etaZ b E) {ω : LayerSample W .oneBlockOnePort}
    (hA : (ω.1 0).IsHermitian) (hB : IsUnit (ω.2 0 0))
    (hS : IsUnit (ω.1 0 - (E : ℂ) • 1 - portBlock XX 0 0)) :
    transportedSep b E XX .projS ω =
      (nearSel W)ᴴ * gapLetter b E (nearSchur (boundaryZ b E) XX) ω *
        (nearSel W * twoPortScattering b E XX) := by
  rw [transportedSep, sepOf, ← FullSourceCovariance.nearSel_conj_mul_nearSel]
  calc freshTransport b E XX ω * ((nearSel W)ᴴ * nearSel W * twoPortScattering b E
        (freshTwoPortSchur E XX ω)) * (freshTransport b E XX ω)ᴴ
      = (freshTransport b E XX ω * (nearSel W)ᴴ) * (nearSel W * twoPortScattering b E
          (freshTwoPortSchur E XX ω) * (freshTransport b E XX ω)ᴴ) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [freshTransport_mul_nearSel_conj, nearSel_scat_transport b E hXX hη hA hB hS, gapLetter]
        simp only [Matrix.mul_assoc]

/-- **The projected letter** (`P𝕊P`): `N P𝕊₊P N* = ι L(1 - 2iη𝒢₂₂)L* ι*`. -/
theorem transportedSep_projSProj (b E : ℝ) {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hXX : XX.IsHermitian) (hη : 0 < etaZ b E) {ω : LayerSample W .oneBlockOnePort}
    (hA : (ω.1 0).IsHermitian) (hB : IsUnit (ω.2 0 0))
    (hS : IsUnit (ω.1 0 - (E : ℂ) • 1 - portBlock XX 0 0)) :
    transportedSep b E XX .projSProj ω =
      (nearSel W)ᴴ * (freshL b E (nearSchur (boundaryZ b E) XX) ω *
        (1 - ((2 * Complex.I) * (etaZ b E : ℂ)) •
          g22 E (boundaryZ b E) (nearSchur (boundaryZ b E) XX) ω) *
        (freshL b E (nearSchur (boundaryZ b E) XX) ω)ᴴ) * nearSel W := by
  have hplus := nearRow_plus b E hXX hη hA hB hS
  have h00 : nearSel W * twoPortScattering b E (freshTwoPortSchur E XX ω) * (nearSel W)ᴴ =
      1 - ((2 * Complex.I) * (etaZ b E : ℂ)) •
        g22 E (boundaryZ b E) (nearSchur (boundaryZ b E) XX) ω := by
    have e : ∀ ρ : Matrix (Fin W) (Fin 2 × Fin W) ℂ, ρ * (nearSel W)ᴴ = colBlock ρ 0 := by
      intro ρ; ext x y; simp [colBlock, nearSel, Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [e, colBlock_nearSel_scat, hplus, colBlock_rowOf, colBlock_nearSel]; rfl
  have hNc : nearSel W * (freshTransport b E XX ω)ᴴ =
      (freshL b E (nearSchur (boundaryZ b E) XX) ω)ᴴ * nearSel W := by
    have := congrArg conjTranspose (freshTransport_mul_nearSel_conj b E XX ω)
    simpa [conjTranspose_mul] using this
  rw [transportedSep, sepOf, ← FullSourceCovariance.nearSel_conj_mul_nearSel]
  calc freshTransport b E XX ω * ((nearSel W)ᴴ * nearSel W * twoPortScattering b E
        (freshTwoPortSchur E XX ω) * ((nearSel W)ᴴ * nearSel W)) * (freshTransport b E XX ω)ᴴ
      = (freshTransport b E XX ω * (nearSel W)ᴴ) * (nearSel W * twoPortScattering b E
          (freshTwoPortSchur E XX ω) * (nearSel W)ᴴ) * (nearSel W * (freshTransport b E XX ω)ᴴ) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [freshTransport_mul_nearSel_conj, h00, hNc]; simp only [Matrix.mul_assoc]

end BlockBand.SourceProcess.CompleteSourceGap
