module

public import BlockBand.Critical.Collar.Density.Window
public import BlockBand.Layers.MatchedScalar

/-!
# Deterministic Schur algebra of the conditional collar

The algebra behind the collar density lemma: conditional on `A, B`, put `D = A - e - X`,
`T = -D⁻¹B`, `F = -e - B*D⁻¹B` and `H = (z₀ - B*D⁻¹B)⁻¹`; then `K_X T H H* T* K_X* = L L*` with
`L = K_X 𝒢₁₂`.

Deterministic; no measure. Common-port layer sample `ω = (A, B)`, every `W`, real `e`, `b`, and
every matrix `X` (Hermitian where stated), no norm bound.

* `collarTopBlock e X ω = D = A - e - X`, `collarT = T = -D⁻¹B`, `collarF = F = -e - B*D⁻¹B`.
* `collarF_sub_eq`: `F - w = z₀ - B*D⁻¹B` with `w = collarShiftW b e = -z₀ - e` (`= c a` when
  `|e| ≤ 2`, `collarShiftW_eq`).
* `commonPortH_eq`, `commonPortResolvent_toBlocks12`: when `D` and `F - w` are
  invertible, `𝒢₂₂ = H = (F - w)⁻¹` and `𝒢₁₂ = T H` (Schur inversion of
  `layerMatrix .common e z₀ X ω`).
* `commonPortL_eq_mul`: `L = K T H` (`K = matchedLeadK b e X`).
* `portBlockTrace_commonPortResolvent`: `W⁻¹ Tr 𝒢_port = W⁻¹ Tr H`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Density

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open scoped ComplexOrder

variable {W : ℕ}

/-- `D = A - e - X`. -/
def collarTopBlock (e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : LayerSample W .common) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  blockDiag ω.1 - (e : ℂ) • 1 - X

/-- `T = -D⁻¹B`. -/
def collarT (e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : LayerSample W .common) : Matrix (Fin 2 × Fin W) (Fin 1 × Fin W) ℂ :=
  -((collarTopBlock e X ω)⁻¹ * bondMatrix .common ω.2)

/-- `F = -e - B*D⁻¹B`, on the port index `Fin 1 × Fin W`. -/
def collarF (e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : LayerSample W .common) : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ :=
  -((e : ℂ) • 1) - (bondMatrix .common ω.2)ᴴ * (collarTopBlock e X ω)⁻¹ * bondMatrix .common ω.2

/-- The scalar `w = -z₀ - e` with `F - w = z₀ - B*D⁻¹B`; it is `c a` for `|e| ≤ 2`. -/
def collarShiftW (b e : ℝ) : ℂ := -commonZ b e - (e : ℂ)

theorem collarShiftW_eq {b e : ℝ} (he : |e| ≤ 2) :
    collarShiftW b e = ((1 - 2 * b : ℝ) : ℂ) * matchedA e := by
  unfold collarShiftW
  rw [BlockBand.Layers.commonZ_eq he]
  push_cast
  ring

theorem collarF_sub_eq (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : LayerSample W .common) :
    collarF e X ω - collarShiftW b e • (1 : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ) =
      commonZ b e • 1 -
        (bondMatrix .common ω.2)ᴴ * (collarTopBlock e X ω)⁻¹ * bondMatrix .common ω.2 := by
  unfold collarF collarShiftW
  rw [sub_smul, neg_smul]
  abel

theorem collarTopBlock_isHermitian (e : ℝ) {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hX : X.IsHermitian) {ω : LayerSample W .common} (hA : ∀ k, (ω.1 k).IsHermitian) :
    (collarTopBlock e X ω).IsHermitian :=
  ((BlockBand.Critical.Collar.Kernel.blockDiag_isHermitian' hA).sub
    (isHermitian_one.smul (Complex.conj_ofReal e))).sub hX

theorem collarF_isHermitian (e : ℝ) {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hX : X.IsHermitian) {ω : LayerSample W .common} (hA : ∀ k, (ω.1 k).IsHermitian) :
    (collarF e X ω).IsHermitian := by
  have hD := collarTopBlock_isHermitian e hX hA
  have hDi : ((collarTopBlock e X ω)⁻¹).IsHermitian := hD.inv
  refine IsHermitian.sub ?_ ?_
  · exact (isHermitian_one.smul (Complex.conj_ofReal e)).neg
  · exact isHermitian_conjTranspose_mul_mul _ hDi

/-!
## Schur inversion of the common-port layer matrix
-/

/-- Schur inversion of `M = [[D, B], [B*, z]]` when `D` and `S = z - B*D⁻¹B` are invertible. -/
theorem inv_fromBlocks_schur {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
    [DecidableEq m] (D : Matrix n n ℂ) (B : Matrix n m ℂ) (Cm : Matrix m n ℂ) (Z : Matrix m m ℂ)
    (hD : IsUnit D.det) (hS : IsUnit (Z - Cm * D⁻¹ * B).det) :
    (fromBlocks D B Cm Z)⁻¹ =
      fromBlocks (D⁻¹ + D⁻¹ * B * (Z - Cm * D⁻¹ * B)⁻¹ * Cm * D⁻¹)
        (-(D⁻¹ * B * (Z - Cm * D⁻¹ * B)⁻¹)) (-((Z - Cm * D⁻¹ * B)⁻¹ * Cm * D⁻¹))
        (Z - Cm * D⁻¹ * B)⁻¹ := by
  set S := Z - Cm * D⁻¹ * B with hSdef
  have hDD : D * D⁻¹ = 1 := mul_nonsing_inv D hD
  have hSS : S * S⁻¹ = 1 := mul_nonsing_inv S hS
  have hZS : Z * S⁻¹ = 1 + Cm * D⁻¹ * B * S⁻¹ := by
    rw [show Z = S + Cm * D⁻¹ * B by rw [hSdef]; abel, Matrix.add_mul, hSS]
  refine inv_eq_right_inv ?_
  rw [fromBlocks_multiply, ← fromBlocks_one]
  congr 1
  · simp only [Matrix.mul_add, Matrix.mul_neg, ← Matrix.mul_assoc, hDD, Matrix.one_mul]
    abel
  · simp only [Matrix.mul_neg, ← Matrix.mul_assoc, hDD, Matrix.one_mul]
    abel
  · simp only [Matrix.mul_add, Matrix.mul_neg, ← Matrix.mul_assoc, hZS, Matrix.add_mul,
      Matrix.one_mul]
    abel
  · simp only [Matrix.mul_neg, ← Matrix.mul_assoc, hZS]
    abel

theorem layerMatrix_common_eq (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : LayerSample W .common) :
    layerMatrix .common e (commonZ b e) X ω =
      fromBlocks (collarTopBlock e X ω) (bondMatrix .common ω.2) (bondMatrix .common ω.2)ᴴ
        (commonZ b e • 1) := rfl

/-- `𝒢₂₂ = H = (F - w)⁻¹`. -/
theorem commonPortH_eq (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : LayerSample W .common) (hD : IsUnit (collarTopBlock e X ω).det)
    (hS : IsUnit (collarF e X ω - collarShiftW b e • 1).det) :
    commonPortH b e X ω = (collarF e X ω - collarShiftW b e • 1)⁻¹ := by
  rw [collarF_sub_eq] at hS ⊢
  unfold commonPortH commonPortResolvent layerResolvent
  rw [layerMatrix_common_eq, inv_fromBlocks_schur _ _ _ _ hD hS, toBlocks_fromBlocks₂₂]

/-- `𝒢₁₂ = T H`. -/
theorem commonPortResolvent_toBlocks12 (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : LayerSample W .common) (hD : IsUnit (collarTopBlock e X ω).det)
    (hS : IsUnit (collarF e X ω - collarShiftW b e • 1).det) :
    (commonPortResolvent b e X ω).toBlocks₁₂ =
      collarT e X ω * (collarF e X ω - collarShiftW b e • 1)⁻¹ := by
  rw [collarF_sub_eq] at hS ⊢
  unfold commonPortResolvent layerResolvent collarT
  rw [layerMatrix_common_eq, inv_fromBlocks_schur _ _ _ _ hD hS, toBlocks_fromBlocks₁₂,
    Matrix.neg_mul]

/-- **`L = K T H`**, so that `K_XTHH*T*K_X* = LL*`. -/
theorem commonPortL_eq_mul (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : LayerSample W .common) (hD : IsUnit (collarTopBlock e X ω).det)
    (hS : IsUnit (collarF e X ω - collarShiftW b e • 1).det) :
    commonPortL b e X ω =
      matchedLeadK b e X * collarT e X ω * (collarF e X ω - collarShiftW b e • 1)⁻¹ := by
  unfold commonPortL
  rw [commonPortResolvent_toBlocks12 b e X ω hD hS, Matrix.mul_assoc]

/-- `W⁻¹ Tr 𝒢_port = W⁻¹ Tr H`. -/
theorem portBlockTrace_commonPortResolvent (b e : ℝ)
    (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (ω : LayerSample W .common) :
    portBlockTrace (layerResolvent .common e (commonZ b e) X ω) 0 =
      (W : ℂ)⁻¹ * (commonPortH b e X ω).trace := by
  unfold portBlockTrace commonPortH commonPortResolvent
  congr 1
  rw [Matrix.trace, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_one, Matrix.diag, toBlocks₂₂]
  rfl

/-- `F - w` is invertible for Hermitian `F` when `Im w < 0` (`w = c a` in the bulk). -/
theorem isUnit_det_collarF_sub {b e : ℝ} {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hX : X.IsHermitian) {ω : LayerSample W .common} (hA : ∀ k, (ω.1 k).IsHermitian)
    (hw : (collarShiftW b e).im < 0) :
    IsUnit (collarF e X ω - collarShiftW b e • 1).det := by
  have h := isUnit_det_sub_star_smul_one (collarF_isHermitian e hX hA)
    (z := star (collarShiftW b e)) (by simpa using hw)
  rwa [star_star] at h

end BlockBand.Critical.Collar.Density
