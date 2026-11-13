module

public import BlockBand.Transmission.PassiveLayer.PoissonLayer

/-!
# The weighted letters `K𝒢₁₁` and `L`

On the event `A` Hermitian, `B` invertible (`Im w > 0`, passive `X`):
* `g11_eq`, `g12_eq`: `𝒢₁₁ = S⁻¹`, `𝒢₁₂ = -w⁻¹S⁻¹B` (through `embed0 : x ↦ (0,x)`);
* `liftK_mul_schurS_inv`: `K S⁻¹ = I + [(w+E)I - A + w⁻¹BB*]S⁻¹`, `K = w - X`;
* `weighted_letters_le`: `‖K𝒢₁₁‖ ≤ weightBound = 1 + (|w|+|E|+‖A‖+|w|⁻¹‖B‖²)‖𝒢‖` and
  `‖L‖ ≤ |w|⁻¹ · weightBound · ‖B‖`.

No unweighted error is multiplied by the unbounded `K`: `K` enters only
through the exact identity above.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveLayer

open Matrix MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.PassiveCovariance
open scoped Matrix.Norms.L2Operator ComplexOrder ENNReal

open BlockBand.Transmission

variable {W : ℕ}

/-- The embedding `x ↦ (0, x)` of `Fin W` into `Fin 1 × Fin W`. -/
def embed0 (x : Fin W) : Fin 1 × Fin W := (0, x)

theorem embed0_injective : Function.Injective (embed0 (W := W)) := fun _ _ h => by
  simpa [embed0] using congrArg Prod.snd h

theorem mul_submatrix_embed0 (M : Matrix (Fin W) (Fin W) ℂ)
    (N : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ) :
    M * N.submatrix embed0 embed0 = (liftX M * N).submatrix embed0 embed0 := by
  ext x y
  simp [Matrix.mul_apply, liftX, embed0, Fintype.sum_prod_type, Subsingleton.elim _ (0 : Fin 1)]

theorem g11_eq {E : ℝ} {w : ℂ} {X : Matrix (Fin W) (Fin W) ℂ} {ω : LayerSample W .oneBlockOnePort}
    (h : layerAt E w X ω = schurInv E w X ω) :
    g11 E w X ω = (schurS E w X ω)⁻¹.submatrix embed0 embed0 := by
  ext x y; simp [g11, h, schurInv, embed0]

theorem g12_eq {E : ℝ} {w : ℂ} {X : Matrix (Fin W) (Fin W) ℂ} {ω : LayerSample W .oneBlockOnePort}
    (h : layerAt E w X ω = schurInv E w X ω) :
    g12 E w X ω = (-w⁻¹ • ((schurS E w X ω)⁻¹ * bondL ω)).submatrix embed0 embed0 := by
  ext x y; simp [g12, h, schurInv, embed0]

theorem norm_schurS_inv_le {E : ℝ} {w : ℂ} {X : Matrix (Fin W) (Fin W) ℂ}
    {ω : LayerSample W .oneBlockOnePort} (h : layerAt E w X ω = schurInv E w X ω) :
    ‖(schurS E w X ω)⁻¹‖ ≤ ‖layerAt E w X ω‖ := by
  have : (schurS E w X ω)⁻¹ = (layerAt E w X ω).submatrix Sum.inl Sum.inl := by
    rw [h, schurInv]; ext i j; simp
  rw [this]; exact norm_submatrix_le _ Sum.inl_injective Sum.inl_injective

/-- `K·S⁻¹ = I + [(w+E)I - A + w⁻¹BB*]S⁻¹` in the lifted coordinates. -/
theorem liftK_mul_schurS_inv {E : ℝ} {w : ℂ} {X : Matrix (Fin W) (Fin W) ℂ}
    {ω : LayerSample W .oneBlockOnePort} (hS : IsUnit (schurS E w X ω)) :
    liftX (w • 1 - X) * (schurS E w X ω)⁻¹ = 1 + ((w + E) • (1 : Matrix (Fin 1 × Fin W) _ ℂ) -
      liftX (ω.1 0) + w⁻¹ • (bondL ω * (bondL ω)ᴴ)) * (schurS E w X ω)⁻¹ := by
  have hSS := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hS)
  have hK : liftX (w • 1 - X) = schurS E w X ω + ((w + E) • (1 : Matrix (Fin 1 × Fin W) _ ℂ) -
      liftX (ω.1 0) + w⁻¹ • (bondL ω * (bondL ω)ᴴ)) := by
    rw [schurS, liftX_sub, liftX_smul, liftX_one, blockDiag_one_eq, add_smul]
    abel
  rw [hK, add_mul, hSS]

/-- The weighted bound `‖K S⁻¹‖ ≤ 1 + (|w| + |E| + ‖A‖ + |w|⁻¹‖B‖²)‖S⁻¹‖`. -/
theorem norm_liftK_mul_le {E : ℝ} {w : ℂ} {X : Matrix (Fin W) (Fin W) ℂ}
    {ω : LayerSample W .oneBlockOnePort} (hS : IsUnit (schurS E w X ω)) :
    ‖liftX (w • 1 - X) * (schurS E w X ω)⁻¹‖ ≤
      1 + (‖w‖ + |E| + ‖ω.1 0‖ + ‖w‖⁻¹ * ‖ω.2 0 0‖ ^ 2) * ‖(schurS E w X ω)⁻¹‖ := by
  rw [liftK_mul_schurS_inv hS]
  refine (norm_add_le _ _).trans (add_le_add norm_one_matrix_le ?_)
  refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  have hB : ‖bondL ω‖ ≤ ‖ω.2 0 0‖ := by rw [bondL, bondMatrix_one_eq]; exact norm_liftX_le _
  have hBH : ‖(bondL ω)ᴴ‖ ≤ ‖ω.2 0 0‖ := by rw [Matrix.l2_opNorm_conjTranspose]; exact hB
  refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · rw [norm_smul]
    calc ‖w + E‖ * ‖(1 : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ)‖ ≤ (‖w‖ + |E|) * 1 := by
          gcongr
          · exact (norm_add_le _ _).trans (by simp)
          · exact norm_one_matrix_le
      _ = ‖w‖ + |E| := mul_one _
  · exact norm_liftX_le _
  · rw [norm_smul, norm_inv]
    gcongr
    calc ‖bondL ω * (bondL ω)ᴴ‖ ≤ ‖bondL ω‖ * ‖(bondL ω)ᴴ‖ := norm_mul_le _ _
      _ ≤ ‖ω.2 0 0‖ * ‖ω.2 0 0‖ := mul_le_mul hB hBH (norm_nonneg _) (norm_nonneg _)
      _ = ‖ω.2 0 0‖ ^ 2 := (sq _).symm

/-- The weight polynomial `1 + (|w| + |E| + ‖A‖ + |w|⁻¹‖B‖²)‖𝒢‖`. -/
def weightBound (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) : ℝ :=
  1 + (‖w‖ + |E| + ‖ω.1 0‖ + ‖w‖⁻¹ * ‖ω.2 0 0‖ ^ 2) * ‖layerAt E w X ω‖

theorem norm_kG11_le {E : ℝ} {w : ℂ} {X : Matrix (Fin W) (Fin W) ℂ}
    {ω : LayerSample W .oneBlockOnePort} (hS : IsUnit (schurS E w X ω))
    (h : layerAt E w X ω = schurInv E w X ω) : ‖kG11 E w X ω‖ ≤ weightBound E w X ω := by
  rw [kG11, g11_eq h, mul_submatrix_embed0]
  refine (norm_submatrix_le _ embed0_injective embed0_injective).trans
    ((norm_liftK_mul_le hS).trans ?_)
  rw [weightBound]
  gcongr
  exact norm_schurS_inv_le h

theorem norm_lAt_le {E : ℝ} {w : ℂ} {X : Matrix (Fin W) (Fin W) ℂ}
    {ω : LayerSample W .oneBlockOnePort} (hS : IsUnit (schurS E w X ω))
    (h : layerAt E w X ω = schurInv E w X ω) :
    ‖lAt E w X ω‖ ≤ ‖w‖⁻¹ * weightBound E w X ω * ‖ω.2 0 0‖ := by
  rw [lAt, g12_eq h, mul_submatrix_embed0]
  refine (norm_submatrix_le _ embed0_injective embed0_injective).trans ?_
  rw [mul_smul_comm, norm_smul, norm_neg, norm_inv, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h1 : ‖liftX (w • 1 - X) * (schurS E w X ω)⁻¹‖ ≤ weightBound E w X ω := by
    refine (norm_liftK_mul_le hS).trans ?_
    rw [weightBound]; gcongr; exact norm_schurS_inv_le h
  have h2 : ‖bondL ω‖ ≤ ‖ω.2 0 0‖ := by rw [bondL, bondMatrix_one_eq]; exact norm_liftX_le _
  calc ‖liftX (w • 1 - X) * ((schurS E w X ω)⁻¹ * bondL ω)‖
      = ‖liftX (w • 1 - X) * (schurS E w X ω)⁻¹ * bondL ω‖ := by rw [mul_assoc]
    _ ≤ ‖liftX (w • 1 - X) * (schurS E w X ω)⁻¹‖ * ‖bondL ω‖ := norm_mul_le _ _
    _ ≤ weightBound E w X ω * ‖ω.2 0 0‖ :=
        mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)

theorem isUnit_schurS (E : ℝ) {w : ℂ} (hw : 0 < w.im) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) {ω : LayerSample W .oneBlockOnePort}
    (hA : (ω.1 0).IsHermitian) (hB : IsUnit (ω.2 0 0)) : IsUnit (schurS E w X ω) := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  have hδ : 0 < schurDelta w ω := by
    have : 0 < Complex.normSq w := Complex.normSq_pos.mpr hw0
    unfold schurDelta; positivity
  exact (isUnit_and_norm_inv_le_of_coercive hδ (schurS_coercive E hw hY hA hB)).1

/-- **Pointwise weighted bounds** on the event `A` Hermitian, `B` invertible:
`‖K𝒢₁₁‖ ≤ weightBound` and `‖L‖ ≤ |w|⁻¹ weightBound ‖B‖`. -/
theorem weighted_letters_le (E : ℝ) {w : ℂ} (hw : 0 < w.im) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) {ω : LayerSample W .oneBlockOnePort}
    (hA : (ω.1 0).IsHermitian) (hB : IsUnit (ω.2 0 0)) :
    ‖kG11 E w X ω‖ ≤ weightBound E w X ω ∧
      ‖lAt E w X ω‖ ≤ ‖w‖⁻¹ * weightBound E w X ω * ‖ω.2 0 0‖ := by
  have hS := isUnit_schurS E hw hY hA hB
  have h := (layer_schur E hw hY hA hB).2.1
  exact ⟨norm_kG11_le hS h, norm_lAt_le hS h⟩

end BlockBand.Transmission.PassiveLayer
