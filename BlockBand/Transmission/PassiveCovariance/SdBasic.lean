module

public import BlockBand.Transmission.PassiveCovariance.SdVector
public import BlockBand.Transmission.PassiveCovariance.SdPoly

/-!
# The dressed first-letter identity `𝔊 = M̄ - M̄(V + S̄)𝔊` and polynomial bounds of the pieces

* `dressedSide adj`, `sbarSide adj`, `mbarSide adj`: `H₀ - S̄`, `S̄` and `M̄ = (H₀ - S̄)⁻¹`
  (`dressed`, `selfEnergy`), or their adjoints for the side `𝔊 = 𝒢ᴴ`.
* `dressedSide_mul_gSide`: at every Hermitian sample, `(H₀ - S̄)𝔊 = I - (V + S̄)𝔊`; for `𝒢ᴴ` the
  adjoint identity, using `V = Vᴴ`. `gSide_expand`: if `H₀ - S̄` is invertible,
  `𝔊 = M̄ - M̄(V + S̄)𝔊`.
* `star_dotProduct_mul_mulVec`: `x*(BA)c = (Bᴴx)*(Ac)`.
* Polynomial bounds in `B = 1 + btFun`: `polyBM_gSide` (`k = 1`), `polyBM_wordVal` (`k = L_w + 1`),
  `polyBM_sdiag_alpha_gamma` (`S[𝔊α_j]γ_j`, `k = L_w + 2`); continuity of `sdiag`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `H₀ - S̄` (side `𝒢`) or its adjoint (side `𝒢ᴴ`). -/
def dressedSide (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (adj : Bool) : LayerMat W :=
  if adj then (dressed b E X)ᴴ else dressed b E X

/-- `S̄` (side `𝒢`) or `S̄ᴴ` (side `𝒢ᴴ`). -/
def sbarSide (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (adj : Bool) : LayerMat W :=
  if adj then (selfEnergy b (meanTr b E X 0) (meanTr b E X 3))ᴴ
  else selfEnergy b (meanTr b E X 0) (meanTr b E X 3)

/-- `M̄ = (H₀ - S̄)⁻¹` or its adjoint. -/
def mbarSide (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (adj : Bool) : LayerMat W :=
  (dressedSide b E X adj)⁻¹

theorem dressedSide_mul_gSide {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} (hη : 0 < etaZ b E)
    (hX : (passiveY X).PosDef) (adj : Bool) (ω : LayerSample W .oneBlockOnePort)
    (hω : (ω.1 0).IsHermitian) :
    dressedSide b E X adj * gSide b E X adj ω =
      1 - (layerLin ω + sbarSide b E X adj) * gSide b E X adj ω := by
  set L := layerMatrix .oneBlockOnePort E (boundaryZ b E) (liftX X)
  have hU : IsUnit (L ω).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_layerMatrix_strict (E := E) hη hX ω hω)
  have hsplit : L ω = L 0 + layerLin ω := layerMatrix_eq_add b E X ω
  have hR : L ω * gRes b E X ω = 1 := Matrix.mul_nonsing_inv _ hU
  have hL : gRes b E X ω * L ω = 1 := Matrix.nonsing_inv_mul _ hU
  set S := selfEnergy (W := W) b (meanTr b E X 0) (meanTr b E X 3)
  have hd : dressed b E X = L 0 - S := rfl
  cases adj
  · show dressed b E X * gRes b E X ω = 1 - (layerLin ω + S) * gRes b E X ω
    rw [hd, ← hR, hsplit]
    simp only [Matrix.sub_mul, Matrix.add_mul]
    abel
  · show (dressed b E X)ᴴ * (gRes b E X ω)ᴴ = 1 - (layerLin ω + Sᴴ) * (gRes b E X ω)ᴴ
    have h1 : gRes b E X ω * dressed b E X = 1 - gRes b E X ω * (layerLin ω + S) := by
      rw [hd, ← hL, hsplit]
      simp only [Matrix.mul_sub, Matrix.mul_add]
      abel
    have hV : (layerLin ω)ᴴ = layerLin ω := (layerLin_isHermitian ω hω).eq
    rw [← conjTranspose_mul, h1, conjTranspose_sub, conjTranspose_one, conjTranspose_mul,
      conjTranspose_add, hV]

theorem isUnit_dressedSide {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} (hD : IsUnit (dressed b E X))
    (adj : Bool) : IsUnit (dressedSide b E X adj) := by
  cases adj
  · exact hD
  · show IsUnit (dressed b E X)ᴴ
    rw [Matrix.isUnit_iff_isUnit_det, det_conjTranspose, isUnit_star]
    exact (Matrix.isUnit_iff_isUnit_det _).mp hD

/-- **`𝔊 = M̄ - M̄(V + S̄)𝔊`** at every Hermitian sample. -/
theorem gSide_expand {b E : ℝ} {X : Matrix (Fin W) (Fin W) ℂ} (hη : 0 < etaZ b E)
    (hX : (passiveY X).PosDef) (hD : IsUnit (dressed b E X)) (adj : Bool)
    (ω : LayerSample W .oneBlockOnePort) (hω : (ω.1 0).IsHermitian) :
    gSide b E X adj ω = mbarSide b E X adj -
      mbarSide b E X adj * (layerLin ω + sbarSide b E X adj) * gSide b E X adj ω := by
  have hU := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_dressedSide hD adj)
  have h := congrArg (fun T => mbarSide b E X adj * T) (dressedSide_mul_gSide hη hX adj ω hω)
  simp only [mbarSide, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hU, Matrix.one_mul,
    Matrix.mul_sub, Matrix.mul_one] at h
  exact h

theorem star_dotProduct_mul_mulVec {n : Type*} [Fintype n] (B A : Matrix n n ℂ) (x c : n → ℂ) :
    star x ⬝ᵥ ((B * A) *ᵥ c) = star (Bᴴ *ᵥ x) ⬝ᵥ (A *ᵥ c) := by
  rw [← mulVec_mulVec, dotProduct_mulVec, star_mulVec, conjTranspose_conjTranspose]

theorem continuous_sdiag (b : ℝ) : Continuous (sdiag (W := W) b) := by
  unfold sdiag
  refine Continuous.matrix_diagonal (continuous_pi fun α => continuous_finsetSum _ fun γ _ => ?_)
  exact continuous_const.mul (continuous_id.matrix_elem γ γ)

theorem continuous_gSideOf (adj : Bool) :
    Continuous fun G : LayerMat W => if adj then Gᴴ else G := by
  cases adj
  · exact continuous_id
  · exact continuous_id.matrix_conjTranspose

theorem gSide_eq (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (adj : Bool) (ω : LayerSample W .oneBlockOnePort) :
    gSide b E X adj ω = (fun G : LayerMat W => if adj then Gᴴ else G) (gRes b E X ω) := rfl

/-!
## Polynomial bounds in `B = 1 + btFun`
-/

theorem polyBM_gSide (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (adj : Bool) :
    PolyBM (fun ω => 1 + btFun b E X ω) (gSide b E X adj) 1 :=
  ⟨1, zero_le_one, fun ω => by
    rw [norm_gSide, pow_one, one_mul]; exact norm_gRes_le_btFun b E X ω⟩

theorem polyBM_wordVal (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) {Kd : ℝ} (hKd : 0 ≤ Kd) {Lw ℓ : ℕ}
    (hℓ : ℓ ≤ Lw) (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → LayerMat W) (hD : ∀ j, ‖D j‖ ≤ Kd) :
    PolyBM (fun ω => 1 + btFun b E X ω) (fun ω => wordVal (kHat b E X) (gRes b E X ω) wd D)
      (Lw + 1) := by
  refine ⟨max Kd 1 ^ (Lw + 1), by positivity, fun ω => ?_⟩
  have hB := wBound_nonneg (kHat b E X) (gRes b E X ω)
  have hpb := (pow_bound_le hKd hB (show ℓ + 1 ≤ Lw + 1 by omega)).1
  have hmono : (1 + wBound (kHat b E X) (gRes b E X ω)) ^ (Lw + 1) ≤ (1 + btFun b E X ω) ^ (Lw + 1) :=
    pow_le_pow_left₀ (by linarith) (by linarith [wBound_kHat_le b E X ω]) _
  exact (norm_wordVal_le _ _ hKd wd D hD).trans (hpb.trans (mul_le_mul_of_nonneg_left hmono (by positivity)))

theorem polyBM_sdiag_alpha_gamma (b E : ℝ) (hb0 : 0 ≤ b) (hb : b < 1 / 2)
    (X : Matrix (Fin W) (Fin W) ℂ) (adj : Bool) {Kd : ℝ} (hKd : 0 ≤ Kd) {Lw ℓ : ℕ}
    (hℓ : ℓ ≤ Lw) (wd : Fin ℓ → Fin 4) (D : Fin (ℓ + 1) → LayerMat W) (hD : ∀ j, ‖D j‖ ≤ Kd)
    (j : Fin ℓ) :
    PolyBM (fun ω => 1 + btFun b E X ω) (fun ω => sdiag b (gSide b E X adj ω *
        wordAlpha (kHat b E X) (gRes b E X ω) ℓ wd D j) *
        wordGamma (kHat b E X) (gRes b E X ω) ℓ wd D j) (Lw + 2) := by
  refine ⟨2 * max Kd 1 ^ (Lw + 1), by positivity, fun ω => ?_⟩
  set G := gRes b E X ω
  set Kh := kHat b E X
  have hB := wBound_nonneg Kh G
  have hpb := (pow_bound_le hKd hB (show ℓ + 1 ≤ Lw + 1 by omega)).2
  have hmono : (1 + wBound Kh G) ^ (Lw + 1) ≤ (1 + btFun b E X ω) ^ (Lw + 1) :=
    pow_le_pow_left₀ (by linarith) (by linarith [wBound_kHat_le b E X ω]) _
  have hαγ := (norm_wordAlpha_mul_le Kh G hKd wd D hD j).trans
    (hpb.trans (mul_le_mul_of_nonneg_left hmono (by positivity)))
  have hS : ‖gSide b E X adj ω‖ ≤ 1 + btFun b E X ω := by
    rw [norm_gSide]; exact norm_gRes_le_btFun b E X ω
  have h1 : 1 ≤ 1 + btFun b E X ω := one_le_one_add_btFun b E X ω
  calc ‖sdiag b (gSide b E X adj ω * wordAlpha Kh G ℓ wd D j) * wordGamma Kh G ℓ wd D j‖
      ≤ 2 * (‖gSide b E X adj ω‖ * ‖wordAlpha Kh G ℓ wd D j‖) * ‖wordGamma Kh G ℓ wd D j‖ :=
        (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right
          ((norm_sdiag_le b hb0 hb _).trans (mul_le_mul_of_nonneg_left (Matrix.l2_opNorm_mul _ _)
            zero_le_two)) (norm_nonneg _))
    _ = 2 * ‖gSide b E X adj ω‖ * (‖wordAlpha Kh G ℓ wd D j‖ * ‖wordGamma Kh G ℓ wd D j‖) := by ring
    _ ≤ 2 * (1 + btFun b E X ω) * (max Kd 1 ^ (Lw + 1) * (1 + btFun b E X ω) ^ (Lw + 1)) := by
        gcongr
    _ = 2 * max Kd 1 ^ (Lw + 1) * (1 + btFun b E X ω) ^ (Lw + 2) := by ring

end BlockBand.Transmission.PassiveCovariance
