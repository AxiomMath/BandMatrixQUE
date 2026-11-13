module

public import BlockBand.Critical.Collar.Kernel.BoundaryIdentity

/-!
# The weighted boundary identity for the collar

The deterministic weighted boundary identity applied to one collar sample: with the collar Schur
complement `collarSchur` (the inverse of `R_c`) and `Z = z_b - X`, `collar_poissonKernel_eq` gives
`𝒫(Ur) = η⁻¹ (I - ZR_c) Y (I - ZR_c)*` for `Y = -Im X ≻ 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Kernel

open Matrix
open BlockBand.Internal.Contracts
open BlockBand.Internal.Contracts.Layers
open scoped ComplexOrder

variable {W : ℕ}

/-- `diag(A_j)` is Hermitian when every block is. -/
theorem blockDiag_isHermitian' {k : ℕ} {A : Fin k → Matrix (Fin W) (Fin W) ℂ}
    (hA : ∀ j, (A j).IsHermitian) : (Layers.blockDiag A).IsHermitian := by
  ext ⟨j, a⟩ ⟨j', b⟩
  simp only [Matrix.conjTranspose_apply, Layers.blockDiag]
  by_cases h : j = j'
  · subst h
    simp only [ite_true]
    exact (hA j).apply a b
  · simp [h, Ne.symm h]

/-- The Hermitian part `X_h = (X + X*)/2`. -/
def rePart {ι : Type*} [Fintype ι] (X : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (2 : ℂ)⁻¹ • (X + Xᴴ)

theorem rePart_isHermitian {ι : Type*} [Fintype ι] (X : Matrix ι ι ℂ) :
    (rePart X).IsHermitian := by
  simp only [rePart, IsHermitian, conjTranspose_smul, conjTranspose_add,
    conjTranspose_conjTranspose, star_inv₀, Complex.star_def, map_ofNat]
  rw [add_comm]

theorem imPart_isHermitian {ι : Type*} [Fintype ι] (X : Matrix ι ι ℂ) :
    (Critical.imPart X).IsHermitian := by
  simp only [Critical.imPart, IsHermitian, conjTranspose_smul, conjTranspose_sub,
    conjTranspose_conjTranspose, star_inv₀, star_mul', Complex.star_def, Complex.conj_I,
    map_ofNat]
  rw [show (2 * -Complex.I)⁻¹ = -(2 * Complex.I)⁻¹ by rw [mul_neg, inv_neg], neg_smul,
    ← smul_neg, neg_sub]

/-- `X = X_h - i(-Im X)`: `X_h - iY` with `Y = -imPart X`. -/
theorem rePart_sub_I_smul_neg_imPart {ι : Type*} [Fintype ι] (X : Matrix ι ι ℂ) :
    rePart X - Complex.I • (-Critical.imPart X) = X := by
  simp only [rePart, Critical.imPart, smul_neg, sub_neg_eq_add, smul_smul]
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  rw [show Complex.I * (2 * Complex.I)⁻¹ = (2 : ℂ)⁻¹ by field_simp, ← smul_add]
  rw [show X + Xᴴ + (X - Xᴴ) = (2 : ℂ) • X by rw [two_smul]; abel, smul_smul,
    inv_mul_cancel₀ h2, one_smul]

/-- The collar Schur complement `A - (e+s) - X - B(G - (e+s))⁻¹B*` (inverse of `R_c`). -/
def collarSchur (e s : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : Critical.CollarSample W) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  Layers.blockDiag ω.1.1 - ((e + s : ℝ) : ℂ) • 1 - X -
    bondMatrix .common ω.1.2 * (ω.2 - ((e + s : ℝ) : ℂ) • 1)⁻¹ * (bondMatrix .common ω.1.2)ᴴ

theorem collarShift_zero_height (e s : ℝ) : Critical.collarShift e s 0 = ((e + s : ℝ) : ℂ) := by
  simp [Critical.collarShift]

/-- At zero height the collar reaction `K_c` is Hermitian (Hermitian `A_j`, `G`). -/
theorem collarReaction_isHermitian (b e s : ℝ) {ω : Critical.CollarSample W}
    (hA : ∀ j, (ω.1.1 j).IsHermitian) (hG : ω.2.IsHermitian) :
    (Critical.collarReaction b e s 0 ω).IsHermitian := by
  rw [Critical.collarReaction, collarShift_zero_height]
  have hD := blockDiag_isHermitian' hA
  have hc : ∀ r : ℝ, ((r : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)).IsHermitian :=
    fun r => by simp [IsHermitian, conjTranspose_smul]
  have hGi : ((ω.2 - ((e + s : ℝ) : ℂ) • 1)⁻¹).IsHermitian := by
    refine IsHermitian.inv (hG.sub ?_)
    simp [IsHermitian, conjTranspose_smul]
  have hBGB := isHermitian_mul_mul_conjTranspose (bondMatrix .common ω.1.2) hGi
  have : (((e + s : ℝ) : ℂ) + ((boundaryZ b e).re : ℂ)) = (((e + s + (boundaryZ b e).re : ℝ)) : ℂ) := by
    push_cast; ring
  rw [this]
  exact (hD.sub (hc _)).sub hBGB

/-- `K_c + H_o + iY = collarSchur`, with `H_o = ξ - X_h`, `X = X_h - iY`. -/
theorem collarReaction_add (b e s : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : Critical.CollarSample W) :
    Critical.collarReaction b e s 0 ω + (((boundaryZ b e).re : ℂ) • 1 - rePart X) +
        Complex.I • (-Critical.imPart X) = collarSchur e s X ω := by
  have hX := rePart_sub_I_smul_neg_imPart X
  rw [Critical.collarReaction, collarShift_zero_height, collarSchur]
  generalize rePart X = Xh at *
  generalize Critical.imPart X = Ym at *
  subst hX
  push_cast
  module

/-- `Z = H_o + i(ηI + Y) = z_b - X` (`H_o = ξ - X_h`, `Y = -Im X`). -/
theorem boundaryZMat_eq (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    boundaryZMat (((boundaryZ b e).re : ℂ) • 1 - rePart X) (-Critical.imPart X)
        (boundaryZ b e).im = boundaryZ b e • 1 - X := by
  have hX := rePart_sub_I_smul_neg_imPart X
  rw [boundaryZMat]
  generalize rePart X = Xh at *
  generalize Critical.imPart X = Ym at *
  subst hX
  conv_rhs => rw [← Complex.re_add_im (boundaryZ b e)]
  module

/-- **Weighted boundary identity for the collar.** Deterministic, for one collar sample with Hermitian `A_j`, `G` (`collarLaw`-a.s.),
energy `e` with `η = Im z_b > 0`, real shift `s`, zero height, and `X` with `Y = -Im X ≻ 0` (no
norm bound): `I - Ur` is invertible and
`𝒫(Ur) = η⁻¹ (I - (z_b - X)R_c) Y (I - (z_b - X)R_c)*`, `R_c = collarSchur⁻¹`. -/
theorem collar_poissonKernel_eq (b e s : ℝ) (hη : 0 < (boundaryZ b e).im)
    {ω : Critical.CollarSample W} (hA : ∀ j, (ω.1.1 j).IsHermitian) (hG : ω.2.IsHermitian)
    (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (hY : (-Critical.imPart X).PosDef) :
    IsUnit (1 - Critical.collarScattering b e s 0 ω * Critical.oldScattering b e X).det ∧
    Critical.poissonKernel (Critical.collarScattering b e s 0 ω * Critical.oldScattering b e X) =
      (((boundaryZ b e).im⁻¹ : ℝ) : ℂ) •
        ((1 - (boundaryZ b e • 1 - X) * (collarSchur e s X ω)⁻¹) * (-Critical.imPart X) *
          (1 - (boundaryZ b e • 1 - X) * (collarSchur e s X ω)⁻¹)ᴴ) ∧
    Critical.poissonKernel (Critical.collarScattering b e s 0 ω * Critical.oldScattering b e X) =
      (((boundaryZ b e).im⁻¹ : ℝ) : ℂ) •
        ((Critical.collarReaction b e s 0 ω - (((boundaryZ b e).im : ℂ) * Complex.I) • 1) *
          (collarSchur e s X ω)⁻¹ * (-Critical.imPart X) * ((collarSchur e s X ω)⁻¹)ᴴ *
          (Critical.collarReaction b e s 0 ω + (((boundaryZ b e).im : ℂ) * Complex.I) • 1)) := by
  set η := (boundaryZ b e).im
  set Kc := Critical.collarReaction b e s 0 ω
  set Ho : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ := ((boundaryZ b e).re : ℂ) • 1 - rePart X
  set Y := -Critical.imPart X
  have hKc : Kc.IsHermitian := collarReaction_isHermitian b e s hA hG
  have hHo : Ho.IsHermitian :=
    (by simp [IsHermitian, conjTranspose_smul] :
      (((boundaryZ b e).re : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)).IsHermitian).sub
      (rePart_isHermitian X)
  have hYh : Y.IsHermitian := hY.isHermitian
  have hZeq : boundaryZMat Ho Y η = boundaryZ b e • 1 - X := boundaryZMat_eq b e X
  have hMeq : Kc + Ho + Complex.I • Y = collarSchur e s X ω := collarReaction_add b e s X ω
  have hZ : IsUnit (boundaryZMat Ho Y η).det := by
    have hpd : ((η : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) + Y).PosDef :=
      (Matrix.PosDef.one.smul (by exact_mod_cast hη)).add_posSemidef hY.posSemidef
    exact isUnit_det_herm_add_I_smul_posDef hHo hpd
  have hM : IsUnit (Kc + Ho + Complex.I • Y).det :=
    isUnit_det_herm_add_I_smul_posDef (hKc.add hHo) hY
  have hU : cayleyOf Kc η = Critical.collarScattering b e s 0 ω := rfl
  have hr : scatteringOf (boundaryZMat Ho Y η) η = Critical.oldScattering b e X := by
    rw [hZeq]; rfl
  have h1 := weightedBoundaryIdentity hKc hHo hYh hη hZ hM
  have h2 := weightedBoundaryIdentity' hKc hHo hYh hη hZ hM
  rw [hU, hr, hZeq, hMeq] at h1
  rw [hU, hr, hMeq] at h2
  exact ⟨h1.1, h1.2, h2⟩

end BlockBand.Critical.Collar.Kernel
