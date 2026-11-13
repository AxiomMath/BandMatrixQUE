module

public import BlockBand.SourceProcess.FullSource.NearPassive

/-!
# The right weighted letter `𝒢₁₁K` and `Δ = K𝒢₁₁V`

On the event `A` Hermitian, `B` invertible (`Im w > 0`, passive `X`), with the Schur complement
`S = A - E - X - w⁻¹BB*` (so `𝒢₁₁ = S⁻¹`), `K = w - X = S + V`,
`V = (w+E)I - A + w⁻¹BB*` (`letterV`):
* `schurS_inv_mul_liftK`: `S⁻¹K = I + S⁻¹V`, i.e. `𝒢₁₁K = I + 𝒢₁₁V`;
* `delta_eq`: `Δ = K𝒢₁₁K - K = K𝒢₁₁V`;
* `right_letters_le`: `‖𝒢₁₁K‖ ≤ weightBound` and `‖Δ‖ ≤ weightBound · v`,
  `v = |w| + |E| + ‖A‖ + |w|⁻¹‖B‖²`.

`K` enters only through these exact identities; no error term is multiplied by `K`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSource

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.PassiveLayer BlockBand.Transmission.PassiveCovariance
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

theorem submatrix_embed0_mul (N : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ)
    (M : Matrix (Fin W) (Fin W) ℂ) :
    N.submatrix embed0 embed0 * M = (N * liftX M).submatrix embed0 embed0 := by
  ext x y
  simp [Matrix.mul_apply, liftX, embed0, Fintype.sum_prod_type, Subsingleton.elim _ (0 : Fin 1)]

theorem liftX_submatrix_embed0 (M : Matrix (Fin W) (Fin W) ℂ) :
    (liftX M).submatrix embed0 embed0 = M := by
  ext x y; simp [liftX, embed0]

/-- `V = (w+E)I - A + w⁻¹BB*` (lifted), so that `K = S + V`. -/
def letterV (E : ℝ) (w : ℂ) (ω : LayerSample W .oneBlockOnePort) :
    Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ :=
  (w + E) • (1 : Matrix (Fin 1 × Fin W) _ ℂ) - liftX (ω.1 0) + w⁻¹ • (bondL ω * (bondL ω)ᴴ)

theorem liftK_eq (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    liftX (w • 1 - X) = schurS E w X ω + letterV E w ω := by
  rw [schurS, letterV, liftX_sub, liftX_smul, liftX_one, blockDiag_one_eq, add_smul]
  abel

/-- `𝒢₁₁K = I + 𝒢₁₁V` in the lifted coordinates (`S⁻¹K = I + S⁻¹V`). -/
theorem schurS_inv_mul_liftK {E : ℝ} {w : ℂ} {X : Matrix (Fin W) (Fin W) ℂ}
    {ω : LayerSample W .oneBlockOnePort} (hS : IsUnit (schurS E w X ω)) :
    (schurS E w X ω)⁻¹ * liftX (w • 1 - X) = 1 + (schurS E w X ω)⁻¹ * letterV E w ω := by
  rw [liftK_eq E w X ω, Matrix.mul_add,
    nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hS)]

/-- `v = |w| + |E| + ‖A‖ + |w|⁻¹‖B‖²` bounds `‖V‖`. -/
def letterVBound (E : ℝ) (w : ℂ) (ω : LayerSample W .oneBlockOnePort) : ℝ :=
  ‖w‖ + |E| + ‖ω.1 0‖ + ‖w‖⁻¹ * ‖ω.2 0 0‖ ^ 2

theorem norm_letterV_le (E : ℝ) (w : ℂ) (ω : LayerSample W .oneBlockOnePort) :
    ‖letterV E w ω‖ ≤ letterVBound E w ω := by
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

theorem letterVBound_nonneg (E : ℝ) (w : ℂ) (ω : LayerSample W .oneBlockOnePort) :
    0 ≤ letterVBound E w ω := (norm_nonneg _).trans (norm_letterV_le E w ω)

theorem g11_mul_K_eq {E : ℝ} {w : ℂ} {X : Matrix (Fin W) (Fin W) ℂ}
    {ω : LayerSample W .oneBlockOnePort} (h : layerAt E w X ω = schurInv E w X ω) :
    g11 E w X ω * (w • 1 - X) =
      ((schurS E w X ω)⁻¹ * liftX (w • 1 - X)).submatrix embed0 embed0 := by
  rw [g11_eq h, submatrix_embed0_mul]

/-- `‖𝒢₁₁K‖ ≤ weightBound`. -/
theorem norm_g11_mul_K_le {E : ℝ} {w : ℂ} {X : Matrix (Fin W) (Fin W) ℂ}
    {ω : LayerSample W .oneBlockOnePort} (hS : IsUnit (schurS E w X ω))
    (h : layerAt E w X ω = schurInv E w X ω) :
    ‖g11 E w X ω * (w • 1 - X)‖ ≤ weightBound E w X ω := by
  rw [g11_mul_K_eq h]
  refine (norm_submatrix_le _ embed0_injective embed0_injective).trans ?_
  rw [schurS_inv_mul_liftK hS, weightBound]
  refine (norm_add_le _ _).trans (add_le_add norm_one_matrix_le ?_)
  refine (norm_mul_le _ _).trans ?_
  rw [mul_comm]
  exact mul_le_mul (norm_letterV_le E w ω) (norm_schurS_inv_le h) (norm_nonneg _)
    (letterVBound_nonneg E w ω)

/-- **`Δ = K𝒢₁₁K - K = K𝒢₁₁V`**, lifted. -/
theorem delta_eq {E : ℝ} {w : ℂ} {X : Matrix (Fin W) (Fin W) ℂ}
    {ω : LayerSample W .oneBlockOnePort} (hS : IsUnit (schurS E w X ω))
    (h : layerAt E w X ω = schurInv E w X ω) :
    (w • 1 - X) * g11 E w X ω * (w • 1 - X) - (w • 1 - X) =
      (liftX (w • 1 - X) * (schurS E w X ω)⁻¹ * letterV E w ω).submatrix embed0 embed0 := by
  rw [Matrix.mul_assoc, g11_mul_K_eq h, mul_submatrix_embed0, schurS_inv_mul_liftK hS,
    Matrix.mul_add, Matrix.mul_one,
    show ∀ A B : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ, (A + B).submatrix embed0 embed0 =
      A.submatrix embed0 embed0 + B.submatrix embed0 embed0 from fun _ _ => rfl,
    liftX_submatrix_embed0, add_sub_cancel_left, Matrix.mul_assoc]

/-- `‖Δ‖ ≤ weightBound · v`. -/
theorem norm_delta_le {E : ℝ} {w : ℂ} {X : Matrix (Fin W) (Fin W) ℂ}
    {ω : LayerSample W .oneBlockOnePort} (hS : IsUnit (schurS E w X ω))
    (h : layerAt E w X ω = schurInv E w X ω) :
    ‖(w • 1 - X) * g11 E w X ω * (w • 1 - X) - (w • 1 - X)‖ ≤
      weightBound E w X ω * letterVBound E w ω := by
  rw [delta_eq hS h]
  refine (norm_submatrix_le _ embed0_injective embed0_injective).trans
    ((norm_mul_le _ _).trans ?_)
  have h1 : ‖liftX (w • 1 - X) * (schurS E w X ω)⁻¹‖ ≤ weightBound E w X ω := by
    refine (norm_liftK_mul_le hS).trans ?_
    rw [weightBound]; gcongr; exact norm_schurS_inv_le h
  exact mul_le_mul h1 (norm_letterV_le E w ω) (norm_nonneg _) ((norm_nonneg _).trans h1)

/-- **Pointwise right-letter bounds** on the event `A` Hermitian, `B` invertible. -/
theorem right_letters_le (E : ℝ) {w : ℂ} (hw : 0 < w.im) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) {ω : LayerSample W .oneBlockOnePort}
    (hA : (ω.1 0).IsHermitian) (hB : IsUnit (ω.2 0 0)) :
    ‖g11 E w X ω * (w • 1 - X)‖ ≤ weightBound E w X ω ∧
      ‖(w • 1 - X) * g11 E w X ω * (w • 1 - X) - (w • 1 - X)‖ ≤
        weightBound E w X ω * letterVBound E w ω := by
  have hS := isUnit_schurS E hw hY hA hB
  have h := (layer_schur E hw hY hA hB).2.1
  exact ⟨norm_g11_mul_K_le hS h, norm_delta_le hS h⟩

/-!
## The fresh-layer vocabulary of `TransmissionPath` at `w = z_∂`
-/

theorem freshBlock_tt_eq (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    BlockBand.Transmission.Bridge.freshBlock b E X ω true true = g11 E (boundaryZ b E) X ω := rfl

theorem freshBlock_tf_eq (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    BlockBand.Transmission.Bridge.freshBlock b E X ω true false = g12 E (boundaryZ b E) X ω := rfl

theorem freshL_eq_lAt (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) : freshL b E X ω = lAt E (boundaryZ b E) X ω := rfl

theorem freshDelta_eq (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    freshDelta b E X ω = (boundaryZ b E • 1 - X) * g11 E (boundaryZ b E) X ω *
      (boundaryZ b E • 1 - X) - (boundaryZ b E • 1 - X) := rfl

theorem norm_g12_le (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) : ‖g12 E w X ω‖ ≤ ‖layerAt E w X ω‖ := by
  have : g12 E w X ω = (layerAt E w X ω).submatrix (fun x => Sum.inl ((0 : Fin 1), x))
      (fun y => Sum.inr ((0 : Fin 1), y)) := by ext; rfl
  rw [this]
  exact norm_submatrix_le _ (fun _ _ h => by simpa using h) (fun _ _ h => by simpa using h)

end BlockBand.SourceProcess.FullSource
