module

public import BlockBand.Transmission.PathScalar.OneStep
public import BlockBand.Transmission.PassiveLayer.Statement

/-!
# The fresh port trace through the lead-augmented layer resolvent, and its absorption shift

The start of the absorbed recursion. The absorption perturbation uses the **lead-augmented**
layer resolvent `𝒢 = [[A - E - X, B], [B*, zI]]⁻¹` (port at `z`, `Im z > 0`), whose moments are
`PassiveBoundsStatement.moments`, rather than a bare core inverse `(A - E - X)⁻¹`.

* `freshPortTrace_eq_layer`: if `A - E - X` is invertible, `W⁻¹Tr R₊ = W⁻¹ Σ_x 𝒢₂₂(x,x)`;
* `norm_freshPortTrace_absorb_le`: if moreover the two layer matrices at `X` and `X - iε` and
  `A - E - X + iε` are invertible, `|W⁻¹Tr R₊(X - iε) - W⁻¹Tr R₊(X)| ≤ ε ‖𝒢(X - iε)‖ ‖𝒢(X)‖`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PathScalar

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PassiveLayer
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

theorem norm_entry_le_general {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) (i : n) :
    ‖M i i‖ ≤ ‖M‖ := by
  have hv : vecNorm (Pi.single i (1 : ℂ)) = 1 := by
    rw [vecNorm]
    have : ∑ j, ‖(Pi.single i (1 : ℂ) : n → ℂ) j‖ ^ 2 = 1 := by
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
      simp
    rw [this, Real.sqrt_one]
  have h := norm_bilinear_le (Pi.single i (1 : ℂ)) M (Pi.single i 1)
  rw [hv, mul_one, one_mul] at h
  have he : bilinear (Pi.single i (1 : ℂ)) M (Pi.single i 1) = M i i := by
    simp [bilinear, Matrix.col_apply]
  rwa [he] at h

/-- The physical block `A - E - X` of the one-port layer. -/
def layerF (E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) :
    Matrix (PhysSite W .oneBlockOnePort) (PhysSite W .oneBlockOnePort) ℂ :=
  BlockBand.Internal.Contracts.Layers.blockDiag ω.1 - (E : ℂ) • 1 - liftX X

/-- **`W⁻¹ Tr R₊` is the normalized port trace of the lead-augmented layer resolvent.** -/
theorem freshPortTrace_eq_layer (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) (hF : IsUnit (layerF E X ω)) :
    freshPortTrace b E X ω = (W : ℂ)⁻¹ *
      ∑ x : Fin W, layerAt E (boundaryZ b E) X ω (Sum.inr (0, x)) (Sum.inr (0, x)) := by
  have hblk : ((layerAt E (boundaryZ b E) X ω)).toBlocks₂₂ =
      (boundaryZ b E • (1 : Matrix (PortSite W .oneBlockOnePort) (PortSite W .oneBlockOnePort) ℂ) -
        layerSchur .oneBlockOnePort E (liftX X) ω)⁻¹ := by
    rw [layerAt, layerResolvent, layerMatrix]
    exact toBlocks₂₂_inv_fromBlocks _ _ _ _ hF
  let e : Fin W ≃ Fin 1 × Fin W := (Equiv.uniqueProd (Fin W) (Fin 1)).symm
  have hS : boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - freshSchur E X ω =
      (boundaryZ b E • (1 : Matrix (PortSite W .oneBlockOnePort) (PortSite W .oneBlockOnePort) ℂ) -
        layerSchur .oneBlockOnePort E (liftX X) ω).submatrix e e := by
    ext x y
    simp [e, freshSchur, liftX, Matrix.one_apply]
  rw [freshPortTrace, passiveResolvent, hS, Matrix.inv_submatrix_equiv, ← hblk]
  rfl

/-- The layer matrices at `X` and `X - iε` differ by `iε` on the physical block. -/
theorem layerMatrix_absorb_sub (E : ℝ) (z : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (ε : ℝ)
    (ω : LayerSample W .oneBlockOnePort) :
    layerMatrix .oneBlockOnePort E z (liftX X) ω -
        layerMatrix .oneBlockOnePort E z (liftX (X - (((ε : ℂ) * Complex.I)) • 1)) ω =
      Matrix.fromBlocks (-(((ε : ℂ) * Complex.I)) • 1) 0 0 0 := by
  ext (⟨i, u⟩ | ⟨i, u⟩) (⟨j, v⟩ | ⟨j, v⟩) <;> fin_cases i <;> fin_cases j <;>
    simp [layerMatrix, liftX, Matrix.one_apply]

theorem norm_fromBlocks_smul_one_le {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n]
    (c : ℂ) : ‖(Matrix.fromBlocks (c • (1 : Matrix m m ℂ)) 0 0 0 : Matrix (m ⊕ n) (m ⊕ n) ℂ)‖ ≤
      ‖c‖ := by
  refine opNorm_le_of_vec _ (norm_nonneg _) fun v => ?_
  have hmv : (Matrix.fromBlocks (c • (1 : Matrix m m ℂ)) 0 0 0 : Matrix (m ⊕ n) (m ⊕ n) ℂ) *ᵥ v =
      Sum.elim (fun i => c * v (Sum.inl i)) 0 := by
    funext k
    rcases k with i | i <;> simp [Matrix.mulVec, dotProduct, Matrix.fromBlocks, Matrix.one_apply,
      Fintype.sum_sum_type]
  rw [hmv, vecNorm, vecNorm, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, Finset.sum_const_zero, add_zero, norm_mul, mul_pow]
  rw [← Finset.mul_sum, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  gcongr
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- **The absorption shift of the fresh port trace**, through the lead-augmented resolvent. -/
theorem norm_freshPortTrace_absorb_le (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) {ε : ℝ}
    (hε : 0 ≤ ε) (ω : LayerSample W .oneBlockOnePort) (hF : IsUnit (layerF E X ω))
    (hF' : IsUnit (layerF E (X - (((ε : ℂ) * Complex.I)) • 1) ω))
    (hM : IsUnit (layerMatrix .oneBlockOnePort E (boundaryZ b E) (liftX X) ω).det)
    (hM' : IsUnit (layerMatrix .oneBlockOnePort E (boundaryZ b E)
      (liftX (X - (((ε : ℂ) * Complex.I)) • 1)) ω).det) :
    ‖freshPortTrace b E (X - (((ε : ℂ) * Complex.I)) • 1) ω - freshPortTrace b E X ω‖ ≤
      ε * ‖layerAt E (boundaryZ b E) (X - (((ε : ℂ) * Complex.I)) • 1) ω‖ *
        ‖layerAt E (boundaryZ b E) X ω‖ := by
  set X' := X - (((ε : ℂ) * Complex.I)) • (1 : Matrix (Fin W) (Fin W) ℂ)
  set M := layerMatrix .oneBlockOnePort E (boundaryZ b E) (liftX X) ω
  set M' := layerMatrix .oneBlockOnePort E (boundaryZ b E) (liftX X') ω
  set G := layerAt E (boundaryZ b E) X ω
  set G' := layerAt E (boundaryZ b E) X' ω
  have hG : G = M⁻¹ := rfl
  have hG' : G' = M'⁻¹ := rfl
  have hdiff : G' - G = G' * (M - M') * G := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hG, hG', Matrix.nonsing_inv_mul _ hM',
      Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hM, Matrix.one_mul, Matrix.mul_one]
  have hnD : ‖M - M'‖ ≤ ε := by
    rw [layerMatrix_absorb_sub]
    refine (norm_fromBlocks_smul_one_le _).trans_eq ?_
    rw [norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hε]
  have hnorm : ‖G' - G‖ ≤ ε * ‖G'‖ * ‖G‖ := by
    rw [hdiff]
    calc ‖G' * (M - M') * G‖ ≤ ‖G'‖ * ‖M - M'‖ * ‖G‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ ‖G'‖ * ε * ‖G‖ := by gcongr
      _ = ε * ‖G'‖ * ‖G‖ := by ring
  rw [freshPortTrace_eq_layer b E X' ω hF', freshPortTrace_eq_layer b E X ω hF, ← mul_sub,
    ← Finset.sum_sub_distrib]
  refine le_trans ?_ hnorm
  rcases Nat.eq_zero_or_pos W with rfl | hW
  · simp
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hsum : ‖∑ x : Fin W, (G' (Sum.inr (0, x)) (Sum.inr (0, x)) - G (Sum.inr (0, x)) (Sum.inr (0, x)))‖
      ≤ W * ‖G' - G‖ := by
    calc _ ≤ ∑ x : Fin W, ‖(G' - G) (Sum.inr (0, x)) (Sum.inr (0, x))‖ := norm_sum_le _ _
      _ ≤ ∑ _x : Fin W, ‖G' - G‖ :=
          Finset.sum_le_sum fun x _ => norm_entry_le_general (G' - G) (Sum.inr (0, x))
      _ = W * ‖G' - G‖ := by simp
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (W : ℝ)⁻¹ * _ ≤ (W : ℝ)⁻¹ * (W * ‖G' - G‖) := by gcongr
    _ = ‖G' - G‖ := by field_simp

end BlockBand.Transmission.PathScalar
