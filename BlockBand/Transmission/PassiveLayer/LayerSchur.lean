module

public import BlockBand.Transmission.PassiveLayer.Statement
public import BlockBand.Transmission.PassiveLayer.BlockAlgebra

/-!
# Schur inversion of the fresh one-port layer at a passive input

For `A` Hermitian, `B` invertible, `Im w > 0` and a passive `X` (`-Im X ⪰ 0`), the port Schur
complement `S = A - E - X - w⁻¹BB*` satisfies `Im x*Sx ≥ (Im w/|w|²)‖B*x‖² ≥ δ‖x‖²` with
`δ = schurDelta w ω = (Im w/|w|²)/(‖(B*)⁻¹‖²+1)` (`schurS_coercive`). Hence (`layer_schur`):

* the layer matrix is invertible and `𝒢 = schurInv` (explicit Schur blocks);
* `‖S⁻¹‖ ≤ δ⁻¹` and `‖𝒢‖ ≤ layerBound w δ⁻¹ ‖B‖`.

The bound depends on `ω` and `w` only, not on `X`; this is the boundedness on the closed upper
half-plane used by the Poisson step (`ζ ↦ X_h - ζY` stays passive for `Im ζ ≥ 0`). The lift
`liftX` to `Fin 1 × Fin W` is handled by `liftX_mul`, `norm_liftX_le`, `blockDiag_one_eq`,
`bondMatrix_one_eq`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveLayer

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.PassiveCovariance
open BlockBand.Transmission
open scoped Matrix.Norms.L2Operator ComplexOrder

variable {W : ℕ}

theorem liftX_eq_submatrix (M : Matrix (Fin W) (Fin W) ℂ) :
    liftX M = M.submatrix Prod.snd Prod.snd := rfl

theorem prodSnd_injective : Function.Injective (Prod.snd : Fin 1 × Fin W → Fin W) := by
  intro a b h; ext <;> simp_all [Subsingleton.elim a.1 b.1]

theorem norm_liftX_le (M : Matrix (Fin W) (Fin W) ℂ) : ‖liftX M‖ ≤ ‖M‖ :=
  norm_submatrix_le M prodSnd_injective prodSnd_injective

theorem liftX_mul (M N : Matrix (Fin W) (Fin W) ℂ) : liftX (M * N) = liftX M * liftX N := by
  ext u v; simp [liftX, Matrix.mul_apply, Fintype.sum_prod_type]

theorem liftX_conjTranspose (M : Matrix (Fin W) (Fin W) ℂ) : liftX Mᴴ = (liftX M)ᴴ := by
  ext u v; simp [liftX, Matrix.conjTranspose_apply]

theorem liftX_sub (M N : Matrix (Fin W) (Fin W) ℂ) : liftX (M - N) = liftX M - liftX N := by
  ext u v; simp [liftX]

theorem liftX_smul (c : ℂ) (M : Matrix (Fin W) (Fin W) ℂ) : liftX (c • M) = c • liftX M := by
  ext u v; simp [liftX]

theorem liftX_one : liftX (1 : Matrix (Fin W) (Fin W) ℂ) = 1 := by
  ext u v
  simp only [liftX, Matrix.of_apply, Matrix.one_apply, Prod.ext_iff, Subsingleton.elim u.1 v.1,
    true_and]

theorem blockDiag_one_eq (ω : LayerSample W .oneBlockOnePort) :
    BlockBand.Internal.Contracts.Layers.blockDiag ω.1 = liftX (ω.1 0) := by
  ext u v
  have hu : u.1 = 0 := Subsingleton.elim _ _
  have hv : v.1 = 0 := Subsingleton.elim _ _
  simp [BlockBand.Internal.Contracts.Layers.blockDiag, liftX, hu, hv]

theorem bondMatrix_one_eq (ω : LayerSample W .oneBlockOnePort) :
    bondMatrix .oneBlockOnePort ω.2 = liftX (ω.2 0 0) := by
  ext u v
  simp [bondMatrix, liftX, LayerShape.incident, Subsingleton.elim u.1 0, Subsingleton.elim v.1 0]

theorem liftX_posSemidef {M : Matrix (Fin W) (Fin W) ℂ} (hM : M.PosSemidef) :
    (liftX M).PosSemidef := hM.submatrix _

theorem liftX_isHermitian {M : Matrix (Fin W) (Fin W) ℂ} (hM : M.IsHermitian) :
    (liftX M).IsHermitian := hM.submatrix _

section QF
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
theorem qf_im_eq_zero {H : Matrix n n ℂ} (hH : H.IsHermitian) (x : n → ℂ) :
    (star x ⬝ᵥ (H *ᵥ x)).im = 0 := by
  have h := quad_conjTranspose H x
  rw [hH.eq] at h
  have := congrArg Complex.im h
  simp only [Complex.star_def, Complex.conj_im] at this
  linarith

omit [DecidableEq n] in
theorem qf_conjTranspose_mul (B : Matrix n n ℂ) (x : n → ℂ) :
    star x ⬝ᵥ ((B * Bᴴ) *ᵥ x) = ((vecNorm (Bᴴ *ᵥ x) ^ 2 : ℝ) : ℂ) := by
  rw [← star_self_eq, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec, conjTranspose_conjTranspose]

theorem vecNorm_le_of_isUnit {B : Matrix n n ℂ} (hB : IsUnit B) (x : n → ℂ) :
    vecNorm x ≤ ‖B⁻¹‖ * vecNorm (B *ᵥ x) := by
  have : x = B⁻¹ *ᵥ (B *ᵥ x) := by
    rw [mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det B).mp hB), one_mulVec]
  conv_lhs => rw [this]
  exact vecNorm_mulVec_le _ _

end QF

theorem matrixImaginaryPart_liftX (X : Matrix (Fin W) (Fin W) ℂ) :
    matrixImaginaryPart (liftX X) = liftX (matrixImaginaryPart X) := by
  ext u v; simp [matrixImaginaryPart, liftX, Matrix.conjTranspose_apply]

theorem qf_liftX_im_nonpos {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef)
    (x : Fin 1 × Fin W → ℂ) : (star x ⬝ᵥ (liftX X *ᵥ x)).im ≤ 0 := by
  have h := quad_im (liftX X) x
  rw [matrixImaginaryPart_liftX] at h
  have hp := Complex.nonneg_iff.mp ((liftX_posSemidef hY).dotProduct_mulVec_nonneg x)
  have hneg : liftX (matrixImaginaryPart X) = -liftX (passiveY X) := by
    ext u v; simp [liftX, passiveY]
  rw [hneg, neg_mulVec, dotProduct_neg] at h
  have := congrArg Complex.re h
  simp only [Complex.neg_re, Complex.ofReal_re] at this
  linarith [hp.1]

/-- The bond block of the one-port layer. -/
def bondL (ω : LayerSample W .oneBlockOnePort) : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ :=
  bondMatrix .oneBlockOnePort ω.2

/-- The Schur complement `S = A - E - X - w⁻¹BB*` of the port. -/
def schurS (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) :
    Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ :=
  BlockBand.Internal.Contracts.Layers.blockDiag ω.1 - (E : ℂ) • 1 - liftX X -
    w⁻¹ • (bondL ω * (bondL ω)ᴴ)

theorem layerMatrix_eq (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    layerMatrix .oneBlockOnePort E w (liftX X) ω =
      fromBlocks (BlockBand.Internal.Contracts.Layers.blockDiag ω.1 - (E : ℂ) • 1 - liftX X)
        (bondL ω) (bondL ω)ᴴ (w • 1) := rfl

theorem isUnit_bondL {ω : LayerSample W .oneBlockOnePort} (hB : IsUnit (ω.2 0 0)) :
    IsUnit (bondL ω) := by
  have h : bondL ω * liftX (ω.2 0 0)⁻¹ = 1 := by
    rw [bondL, bondMatrix_one_eq, ← liftX_mul,
      mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hB), liftX_one]
  exact (isUnit_iff_isUnit_det _).mpr (IsUnit.of_mul_eq_one _ (by rw [← det_mul, h, det_one]))

/-- The coercivity constant `δ = (Im w/|w|²)/(‖(B*)⁻¹‖² + 1)`. -/
def schurDelta (w : ℂ) (ω : LayerSample W .oneBlockOnePort) : ℝ :=
  (w.im / Complex.normSq w) / (‖((bondL ω)ᴴ)⁻¹‖ ^ 2 + 1)

theorem schurS_coercive (E : ℝ) {w : ℂ} (hw : 0 < w.im) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) {ω : LayerSample W .oneBlockOnePort}
    (hA : (ω.1 0).IsHermitian) (hB : IsUnit (ω.2 0 0)) (x : Fin 1 × Fin W → ℂ) :
    schurDelta w ω * vecNorm x ^ 2 ≤ (star x ⬝ᵥ (schurS E w X ω *ᵥ x)).im := by
  have hH : (BlockBand.Internal.Contracts.Layers.blockDiag ω.1 - (E : ℂ) • 1).IsHermitian := by
    rw [blockDiag_one_eq]
    refine (liftX_isHermitian hA).sub ?_
    ext u v; simp [Matrix.conjTranspose_apply, Matrix.one_apply]; split_ifs <;> simp_all [eq_comm]
  have hBu : IsUnit (bondL ω)ᴴ := by
    have := (isUnit_bondL hB).star; rwa [Matrix.star_eq_conjTranspose] at this
  set v := vecNorm ((bondL ω)ᴴ *ᵥ x)
  have hexp : (star x ⬝ᵥ (schurS E w X ω *ᵥ x)).im =
      (star x ⬝ᵥ ((BlockBand.Internal.Contracts.Layers.blockDiag ω.1 - (E : ℂ) • 1) *ᵥ x)).im -
      (star x ⬝ᵥ (liftX X *ᵥ x)).im - (w⁻¹ * ((v ^ 2 : ℝ) : ℂ)).im := by
    rw [schurS, sub_mulVec, sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_sub,
      dotProduct_smul, qf_conjTranspose_mul, smul_eq_mul]
    simp only [Complex.sub_im]; rfl
  rw [hexp, qf_im_eq_zero hH]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add,
    Complex.inv_im]
  have hq := qf_liftX_im_nonpos hY x
  have hns : 0 < Complex.normSq w := Complex.normSq_pos.mpr (fun h => by simp [h] at hw)
  have hx := vecNorm_le_of_isUnit hBu x
  set β := ‖((bondL ω)ᴴ)⁻¹‖
  have hx2 : vecNorm x ^ 2 ≤ (β ^ 2 + 1) * v ^ 2 := by
    have h0 := vecNorm_nonneg x
    have : vecNorm x ^ 2 ≤ (β * v) ^ 2 := pow_le_pow_left₀ h0 hx 2
    nlinarith [sq_nonneg v]
  have hc : 0 ≤ w.im / Complex.normSq w := by positivity
  have hd : schurDelta w ω * vecNorm x ^ 2 ≤ w.im / Complex.normSq w * v ^ 2 := by
    rw [schurDelta, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have : -(-w.im / Complex.normSq w * v ^ 2) = w.im / Complex.normSq w * v ^ 2 := by ring
  linarith

/-- The explicit Schur inverse of the layer matrix. -/
def schurInv (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) :
    Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ :=
  fromBlocks (schurS E w X ω)⁻¹ (-w⁻¹ • ((schurS E w X ω)⁻¹ * bondL ω))
    (-w⁻¹ • ((bondL ω)ᴴ * (schurS E w X ω)⁻¹))
    (w⁻¹ • 1 + (w⁻¹ ^ 2) • ((bondL ω)ᴴ * (schurS E w X ω)⁻¹ * bondL ω))

/-- `s + 2|w|⁻¹sβ + |w|⁻¹ + |w|⁻²β²s`, the block bound of the Schur inverse. -/
def layerBound (w : ℂ) (s β : ℝ) : ℝ := s + 2 * ‖w‖⁻¹ * s * β + ‖w‖⁻¹ + ‖w‖⁻¹ ^ 2 * β ^ 2 * s

theorem layer_schur (E : ℝ) {w : ℂ} (hw : 0 < w.im) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) {ω : LayerSample W .oneBlockOnePort}
    (hA : (ω.1 0).IsHermitian) (hB : IsUnit (ω.2 0 0)) :
    IsUnit (layerMatrix .oneBlockOnePort E w (liftX X) ω).det ∧
      layerResolvent .oneBlockOnePort E w (liftX X) ω = schurInv E w X ω ∧
      ‖(schurS E w X ω)⁻¹‖ ≤ (schurDelta w ω)⁻¹ ∧
      ‖layerResolvent .oneBlockOnePort E w (liftX X) ω‖ ≤
        layerBound w (schurDelta w ω)⁻¹ ‖bondL ω‖ := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  have hδ : 0 < schurDelta w ω := by
    have : 0 < Complex.normSq w := Complex.normSq_pos.mpr hw0
    unfold schurDelta; positivity
  obtain ⟨hSu, hSn⟩ := isUnit_and_norm_inv_le_of_coercive hδ (schurS_coercive E hw hY hA hB)
  have hmul : layerMatrix .oneBlockOnePort E w (liftX X) ω * schurInv E w X ω = 1 := by
    rw [layerMatrix_eq]
    exact fromBlocks_mul_schurInv _ _ hw0 hSu
  have hdet : IsUnit (layerMatrix .oneBlockOnePort E w (liftX X) ω).det :=
    IsUnit.of_mul_eq_one _ (by rw [← det_mul, hmul, det_one])
  have heq : layerResolvent .oneBlockOnePort E w (liftX X) ω = schurInv E w X ω :=
    inv_eq_right_inv hmul
  refine ⟨hdet, heq, hSn, ?_⟩
  rw [heq, schurInv]
  set s := ‖(schurS E w X ω)⁻¹‖
  set β := ‖bondL ω‖
  have hs : s ≤ (schurDelta w ω)⁻¹ := hSn
  have hs0 : 0 ≤ s := norm_nonneg _
  have hβ0 : 0 ≤ β := norm_nonneg _
  have hwi : ‖w⁻¹‖ = ‖w‖⁻¹ := norm_inv w
  have hβH : ‖(bondL ω)ᴴ‖ = β := Matrix.l2_opNorm_conjTranspose _
  refine (norm_fromBlocks_le _ _ _ _).trans ?_
  have h2 : ‖-w⁻¹ • ((schurS E w X ω)⁻¹ * bondL ω)‖ ≤ ‖w‖⁻¹ * (s * β) := by
    rw [norm_smul, norm_neg, hwi]; gcongr; exact norm_mul_le _ _
  have h3 : ‖-w⁻¹ • ((bondL ω)ᴴ * (schurS E w X ω)⁻¹)‖ ≤ ‖w‖⁻¹ * (β * s) := by
    rw [norm_smul, norm_neg, hwi]; gcongr; exact (norm_mul_le _ _).trans (by rw [hβH])
  have h4 : ‖w⁻¹ • (1 : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ) +
      (w⁻¹ ^ 2) • ((bondL ω)ᴴ * (schurS E w X ω)⁻¹ * bondL ω)‖ ≤
      ‖w‖⁻¹ + ‖w‖⁻¹ ^ 2 * (β * s * β) := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, hwi]
      exact (mul_le_of_le_one_right (by positivity) norm_one_matrix_le)
    · rw [norm_smul, norm_pow, hwi]
      gcongr
      refine (norm_mul_le _ _).trans ?_
      gcongr
      exact (norm_mul_le _ _).trans (by rw [hβH])
  have hfin : layerBound w s β ≤ layerBound w (schurDelta w ω)⁻¹ β := by
    unfold layerBound; gcongr
  refine le_trans ?_ hfin
  unfold layerBound
  have := h2; have := h3; have := h4
  nlinarith

end BlockBand.Transmission.PassiveLayer
