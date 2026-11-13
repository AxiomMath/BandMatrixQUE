module

public import BlockBand.Critical.Collar.Kernel.RowForm
public import BlockBand.Critical.Collar.DilationVariance.Resolvent

/-!
# Scalar Cauchy dilation of the three-block collar resolvent

*Setting.* One collar sample `ω` with Hermitian `A_j, G`; energy `e'`; an old response
`X = X_h - iY` with `Y ⪰ 0`; `ε > 0`; `t ~ stdCauchy` (standard Cauchy law). Here
`X_t = X_h + tY` (the Cauchy law is symmetric).

## Results

* `collarMatrix_add_right`, `collarMatrix_eq_herm_add`: `ℋ_{X₁ + X₂} = ℋ_{X₁} - diag(X₂, 0)`;
  `ℋ_X = ℋ_{X_h} + i diag(Y, 0)`.
* `isCauchyMean_quad`: Cauchy means pass through quadratic forms.
* `neg_im_collarResolvent_eq_integral`: **dilation identity**
  `-Im⟨y, (ℋ_X + iε)⁻¹ y⟩ = E_t Im⟨y, (ℋ_{X_t} - iε)⁻¹ y⟩` (integrable integrand, every
  deterministic `y`), from `isCauchyMatrixMean_dilationResolvent`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Kernel

open MeasureTheory Matrix
open BlockBand.Internal.Contracts
open BlockBand.Internal.Contracts.Layers
open BlockBand.Critical.Collar.Density (collarMatrix)
open scoped ComplexOrder

variable {W : ℕ}

theorem topLift_add (Y Y' : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    topLift (Y + Y') = topLift Y + topLift Y' := by
  simp [topLift, fromBlocks_add]

theorem topLift_smul (c : ℂ) (Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    topLift (c • Y) = c • topLift Y := by
  simp [topLift, fromBlocks_smul]

theorem topLift_posSemidef {Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hY : Y.PosSemidef) :
    (topLift Y).PosSemidef := by
  rw [← topInclusion_sandwich]
  exact hY.mul_mul_conjTranspose_same _

/-- `ℋ_{X₁ + X₂} = ℋ_{X₁} - diag(X₂, 0)`. -/
theorem collarMatrix_add_right (e : ℝ) (X₁ X₂ : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : Critical.CollarSample W) :
    collarMatrix e (X₁ + X₂) ω = collarMatrix e X₁ ω - topLift X₂ := by
  simp only [collarMatrix, topLift, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add, neg_zero,
    add_zero]
  congr 1
  abel

/-- `ℋ_X = ℋ_{X_h} + i diag(Y, 0)`, `X = X_h - iY`, `Y = -Im X`. -/
theorem collarMatrix_eq_herm_add (e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : Critical.CollarSample W) :
    collarMatrix e X ω =
      collarMatrix e (rePart X) ω + Complex.I • topLift (-Critical.imPart X) := by
  conv_lhs => rw [← rePart_sub_I_smul_neg_imPart X]
  rw [sub_eq_add_neg, collarMatrix_add_right, ← neg_smul, topLift_smul, neg_smul, sub_neg_eq_add]

/-- `ℋ_X` is Hermitian for Hermitian `A_j`, `G` and `X`. -/
theorem collarMatrix_isHermitian (e : ℝ) {ω : Critical.CollarSample W}
    (hA : ∀ j, (ω.1.1 j).IsHermitian) (hG : ω.2.IsHermitian)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) :
    (collarMatrix e X ω).IsHermitian := by
  have hD := blockDiag_isHermitian' hA
  have hc : ((e : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)).IsHermitian := by
    simp [IsHermitian, conjTranspose_smul]
  have hc' : ((e : ℂ) • (1 : Matrix (PortSite W .common) (PortSite W .common) ℂ)).IsHermitian := by
    simp [IsHermitian, conjTranspose_smul]
  exact IsHermitian.fromBlocks ((hD.sub hc).sub hX) rfl (hG.sub hc')

/-- The dilated old response `X_t = X_h + tY` is Hermitian (`Y = -Im X`). -/
theorem dilatedOld_isHermitian (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (t : ℝ) :
    (rePart X + (t : ℂ) • (-Critical.imPart X)).IsHermitian := by
  refine (rePart_isHermitian X).add ?_
  have h := (imPart_isHermitian X).neg
  simp only [IsHermitian, conjTranspose_smul, Complex.star_def, Complex.conj_ofReal] at h ⊢
  rw [h]

/-- For Hermitian `H` and real `ε`: `⟨y, (H + iε)⁻¹ y⟩ = conj ⟨y, (H - iε)⁻¹ y⟩`. -/
theorem dotProduct_inv_add_I_smul {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (ε : ℝ) (y : ι → ℂ) :
    star y ⬝ᵥ ((H + ((ε : ℂ) * Complex.I) • 1)⁻¹ *ᵥ y) =
      star (star y ⬝ᵥ ((H - ((ε : ℂ) * Complex.I) • 1)⁻¹ *ᵥ y)) := by
  rw [← dotProduct_conjTranspose_mulVec, conjTranspose_nonsing_inv]
  congr 3
  rw [conjTranspose_sub, hH.eq, conjTranspose_smul, conjTranspose_one]
  simp [sub_eq_add_neg, ← neg_smul]

/-- Cauchy means pass through quadratic forms. -/
theorem isCauchyMean_quad {ι : Type*} [Fintype ι] [DecidableEq ι] {F : ℝ → Matrix ι ι ℂ}
    {M : Matrix ι ι ℂ} (h : IsCauchyMatrixMean F M) (y : ι → ℂ) :
    IsCauchyMean (fun t => star y ⬝ᵥ (F t *ᵥ y)) (star y ⬝ᵥ (M *ᵥ y)) := by
  simp only [dotProduct, mulVec]
  exact IsCauchyMean.sum _ fun i _ =>
    (IsCauchyMean.sum _ fun j _ => (h i j).mul_const (y j)).const_mul (star y i)

/-- **Dilation identity for the collar resolvent**. For one sample with
Hermitian `A_j`, `G`, every energy `e`, `X = X_h - iY` with `Y = -Im X ⪰ 0`, `ε > 0` and
deterministic `y`: `t ↦ Im⟨y, (ℋ_{X_h + tY} - iε)⁻¹ y⟩` is integrable for the standard Cauchy law
and `E_t Im⟨y, (ℋ_{X_h + tY} - iε)⁻¹ y⟩ = -Im⟨y, (ℋ_X + iε)⁻¹ y⟩`. -/
theorem neg_im_collarResolvent_eq_integral (e : ℝ) {ω : Critical.CollarSample W}
    (hA : ∀ j, (ω.1.1 j).IsHermitian) (hG : ω.2.IsHermitian)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hY : (-Critical.imPart X).PosSemidef)
    {ε : ℝ} (hε : 0 < ε) (y : LayerSite W .common → ℂ) :
    Integrable (fun t : ℝ => (star y ⬝ᵥ ((collarMatrix e (rePart X + (t : ℂ) •
        (-Critical.imPart X)) ω - ((ε : ℂ) * Complex.I) • 1)⁻¹ *ᵥ y)).im) stdCauchy ∧
    ∫ t, (star y ⬝ᵥ ((collarMatrix e (rePart X + (t : ℂ) • (-Critical.imPart X)) ω -
        ((ε : ℂ) * Complex.I) • 1)⁻¹ *ᵥ y)).im ∂stdCauchy =
      -(star y ⬝ᵥ ((collarMatrix e X ω + ((ε : ℂ) * Complex.I) • 1)⁻¹ *ᵥ y)).im := by
  set H₀ := collarMatrix e (rePart X) ω
  set Yh := topLift (-Critical.imPart X)
  set z : ℂ := (ε : ℂ) * Complex.I
  have hz : 0 < z.im := by simp [z, hε]
  have hH₀ : H₀.IsHermitian := collarMatrix_isHermitian e hA hG (rePart_isHermitian X)
  have h := isCauchyMatrixMean_dilationResolvent (Xh := -H₀) (Y := Yh) (z := z) hH₀.neg
    (topLift_posSemidef hY) hz
  have hdil : ∀ t : ℝ, dilationResolvent (-H₀) Yh z t =
      (collarMatrix e (rePart X + (t : ℂ) • (-Critical.imPart X)) ω + z • 1)⁻¹ := by
    intro t
    rw [dilationResolvent, collarMatrix_add_right, topLift_smul]
    congr 1
    abel
  have habs : absorbedResolvent (-H₀) Yh z = (collarMatrix e X ω + z • 1)⁻¹ := by
    rw [absorbedResolvent, collarMatrix_eq_herm_add e X ω]
    congr 1
    abel
  have hq := isCauchyMean_quad h y
  simp_rw [hdil, habs] at hq
  have hpt : ∀ t : ℝ, (star y ⬝ᵥ ((collarMatrix e (rePart X + (t : ℂ) • (-Critical.imPart X)) ω -
      z • 1)⁻¹ *ᵥ y)).im = -(star y ⬝ᵥ ((collarMatrix e (rePart X + (t : ℂ) •
        (-Critical.imPart X)) ω + z • 1)⁻¹ *ᵥ y)).im := by
    intro t
    rw [dotProduct_inv_add_I_smul (collarMatrix_isHermitian e hA hG (dilatedOld_isHermitian X t))]
    simp only [Complex.star_def, Complex.conj_im, neg_neg, z]
  simp_rw [hpt]
  refine ⟨hq.1.im.neg, ?_⟩
  rw [integral_neg]
  congr 1
  rw [← hq.2]
  exact integral_im hq.1

end BlockBand.Critical.Collar.Kernel
