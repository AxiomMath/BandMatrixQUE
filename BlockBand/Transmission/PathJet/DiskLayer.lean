module

public import BlockBand.Transmission.PathScalar.MeanStepLimit
public import BlockBand.Transmission.PassiveLayer.LayerSchur
public import BlockBand.Transmission.SchurDerivative

/-!
# The fresh layer at a port parameter `w`: invertibility, a deterministic bound, holomorphy

For a passive old input `X` and `Im w > 0`, the layer matrix
`M(w) = [[A - E - X, B], [B*, w]]` has `Im M(w) = diag(Y, Im w)` at Hermitian `A`
(`im_layerMatrix_eq`). Hence:
* `isUnit_layerMatrix_w`: `M(w)` is invertible when `Y ≻ 0`;
* `norm_gW_le`: `‖M(w)⁻¹‖ ≤ (min ε (Im w))⁻¹` when `Y = Y₀ + ε`, `Y₀ ⪰ 0`, `ε > 0`
  (deterministic, uniform in `A, B`);
* `layerMatrix_eq_affine`: `M(w) = M(0) + w P`, `P` the port projection, so
  `∂_w M(w)⁻¹ = -M⁻¹PM⁻¹` (`hasDerivAt_gW`).

The sibling module proves `hasDerivAt_integral_gW` from these: for every continuous linear
functional `L`, the mean `w ↦ E L(𝒢(w))` is complex differentiable at every `w₀` with `Im w₀ > 0`,
with derivative `E L(-𝒢P𝒢)` (dominated differentiation, using the deterministic bound).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PathJet

open MeasureTheory Matrix Filter Topology Metric
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- The fresh layer resolvent `𝒢(w) = M(w)⁻¹` at port parameter `w`. -/
abbrev gW (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) :
    LayerMat W :=
  layerResolvent .oneBlockOnePort E w (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) ω

/-- The port projection `P = diag(0, I)`. -/
def portProj (W : ℕ) : LayerMat W := fromBlocks 0 0 0 1

theorem im_layerMatrix_eq (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) (hA : (ω.1 0).IsHermitian) :
    matrixImaginaryPart (layerMatrix .oneBlockOnePort E w
      (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) ω) =
      fromBlocks (Matrix.of fun (u v : Fin 1 × Fin W) => passiveY X u.2 v.2) 0 0
        (w.im • (1 : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ)) := by
  rw [layerMatrix, matrixImaginaryPart_fromBlocks_adj]
  congr 1
  · have hBD : (BlockBand.Internal.Contracts.Layers.blockDiag ω.1 - (E : ℂ) •
        (1 : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ)).IsHermitian := by
      refine IsHermitian.sub ?_ ?_
      · ext u v
        simp only [conjTranspose_apply, BlockBand.Internal.Contracts.Layers.blockDiag]
        have hu : u.1 = 0 := Subsingleton.elim _ _
        have hv : v.1 = 0 := Subsingleton.elim _ _
        simp only [hu, hv, ite_true]
        have h := congrFun (congrFun hA u.2) v.2
        simpa [conjTranspose_apply] using h
      · exact isHermitian_one.smul (Complex.conj_ofReal E)
    have h0 : matrixImaginaryPart (BlockBand.Internal.Contracts.Layers.blockDiag ω.1 -
        (E : ℂ) • (1 : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ)) = 0 := by
      rw [matrixImaginaryPart, hBD.eq, sub_self, smul_zero]
    rw [matrixImaginaryPart_sub, h0, zero_sub]
    ext u v; simp [matrixImaginaryPart, passiveY]
  · have h := matrixImaginaryPart_portPencil (0 : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ)
      isHermitian_zero w
    simp only [portPencil, sub_zero] at h
    exact h

/-- **Strictly passive inputs give an invertible layer at every `Im w > 0`** (Hermitian `A`). -/
theorem isUnit_layerMatrix_w (E : ℝ) {w : ℂ} (hw : 0 < w.im) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosDef) (ω : LayerSample W .oneBlockOnePort) (hA : (ω.1 0).IsHermitian) :
    IsUnit (layerMatrix .oneBlockOnePort E w (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) ω) :=
  isUnit_of_matrixImaginaryPart_posDef (by
    rw [im_layerMatrix_eq E w X ω hA]
    exact posDef_fromBlocks_diag (posDef_liftX hY) (Matrix.PosDef.one.smul hw))

theorem posSemidef_fromBlocks_diag {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] {P : Matrix m m ℂ} {Q : Matrix n n ℂ} (hP : P.PosSemidef)
    (hQ : Q.PosSemidef) : (fromBlocks P 0 0 Q).PosSemidef := by
  have hP0 := hP.dotProduct_mulVec_nonneg
  have hQ0 := hQ.dotProduct_mulVec_nonneg
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨IsHermitian.fromBlocks hP.1 (by simp) hQ.1, fun x => ?_⟩
  have key : star x ⬝ᵥ (fromBlocks P 0 0 Q *ᵥ x) =
      star (x ∘ Sum.inl) ⬝ᵥ (P *ᵥ (x ∘ Sum.inl)) + star (x ∘ Sum.inr) ⬝ᵥ (Q *ᵥ (x ∘ Sum.inr)) := by
    conv_lhs => rw [← Sum.elim_comp_inl_inr x]
    rw [fromBlocks_mulVec]
    simp only [zero_mulVec, add_zero, zero_add]
    rw [show star (Sum.elim (x ∘ Sum.inl) (x ∘ Sum.inr)) =
      Sum.elim (star (x ∘ Sum.inl)) (star (x ∘ Sum.inr)) by ext i; cases i <;> rfl]
    exact sumElim_dotProduct_sumElim _ _ _ _
  rw [key]
  exact add_nonneg (hP0 _) (hQ0 _)

/-- **Deterministic layer bound**: if `Y = Y₀ + ε`, `Y₀ ⪰ 0`, `ε > 0`, and `Im w > 0`, then at
every Hermitian `A` (and every `B`), `‖𝒢(w)‖ ≤ (min ε (Im w))⁻¹`. -/
theorem norm_gW_le (E : ℝ) {w : ℂ} (hw : 0 < w.im) {X Y₀ : Matrix (Fin W) (Fin W) ℂ} {ε : ℝ}
    (hε : 0 < ε) (hY₀ : Y₀.PosSemidef) (hYe : passiveY X = Y₀ + ε • (1 : Matrix (Fin W) (Fin W) ℂ))
    (ω : LayerSample W .oneBlockOnePort) (hA : (ω.1 0).IsHermitian) :
    ‖gW E w X ω‖ ≤ (min ε w.im)⁻¹ := by
  set m := min ε w.im
  have hm : 0 < m := lt_min hε hw
  have hlift : (Matrix.of fun (u v : Fin 1 × Fin W) => passiveY X u.2 v.2) =
      liftX Y₀ + ε • (1 : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ) := by
    rw [hYe, ← liftX_one]
    ext u v; simp [liftX]
  set Y' : LayerMat W := fromBlocks (liftX Y₀ + (ε - m) • 1) 0 0 ((w.im - m) • 1)
  have hY' : Y'.PosSemidef :=
    posSemidef_fromBlocks_diag ((liftX_posSemidef hY₀).add
      (Matrix.PosSemidef.one.smul (sub_nonneg.mpr (min_le_left _ _))))
      (Matrix.PosSemidef.one.smul (sub_nonneg.mpr (min_le_right _ _)))
  have him : matrixImaginaryPart (layerMatrix .oneBlockOnePort E w
      (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) ω) = Y' + m • (1 : LayerMat W) := by
    rw [im_layerMatrix_eq E w X ω hA, hlift, ← fromBlocks_one, fromBlocks_smul, fromBlocks_add]
    simp only [smul_zero, add_zero]
    congr 1
    · rw [add_assoc, ← add_smul]; congr 2; ring
    · rw [← add_smul]; congr 1; ring
  exact norm_inv_le_of_im _ Y' hm hY' him

/-- `M(w) = M(0) + wP`. -/
theorem layerMatrix_eq_affine (E : ℝ) (w : ℂ) (X' : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    layerMatrix .oneBlockOnePort E w X' ω =
      layerMatrix .oneBlockOnePort E 0 X' ω + w • portProj W := by
  rw [layerMatrix, layerMatrix, portProj, fromBlocks_smul, fromBlocks_add]
  simp

/-- `∂_w 𝒢(w) = -𝒢P𝒢` wherever `M(w)` is invertible. -/
theorem hasDerivAt_gW (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort)
    (hu : IsUnit (layerMatrix .oneBlockOnePort E w
      (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) ω)) :
    HasDerivAt (fun t => gW E t X ω) (-(gW E w X ω * portProj W * gW E w X ω)) w := by
  have hu' := hu
  rw [layerMatrix_eq_affine] at hu'
  have h := affineInverse_hasDerivAt _ (portProj W) w hu'
  have e : (fun t => gW E t X ω) = fun t =>
      (layerMatrix .oneBlockOnePort E 0 (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) ω +
        t • portProj W)⁻¹ := by
    funext t; rw [gW, layerResolvent, layerMatrix_eq_affine]
  rw [e]
  have e2 : gW E w X ω = (layerMatrix .oneBlockOnePort E 0
      (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) ω + w • portProj W)⁻¹ := by
    rw [gW, layerResolvent, layerMatrix_eq_affine]
  rw [e2]; exact h

end BlockBand.Transmission.PathJet
