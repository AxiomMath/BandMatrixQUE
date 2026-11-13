module

public import BlockBand.Critical.MatrixClosing.Statement
public import BlockBand.Critical.Collar.Kernel.Collar

/-!
# Matrix closing: the closing identity for the physical collar value

* `matrix_inv_neg`, `inv_sub_mul_inv_mul` (Woodbury for `D - BG'⁻¹B*`).
* `closing_identity`: the identity for generic finite blocks (deterministic linear algebra).
* `topBlock` (`D = A - e - X`), `portSchur` (`Q = G - e - B*D⁻¹B`), `collarConst`
  (`η⁻¹J*(KD⁻¹K* - H_o)J`), `collarFrame` (`J*KD⁻¹B`), and `closingMatrix_eq`: for one collar sample
  with Hermitian blocks, Hermitian `X` and invertible `D`, `G - (e+s)`, `Q - s`,
  `closingMatrix b e s X J ω = collarConst + η⁻¹ (J*KD⁻¹B)(Q - s)⁻¹(J*KD⁻¹B)*`. With
  `s = x/(Wρ(e))` this is the physical collar function `F_W(x)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.MatrixClosing

open Matrix

section Generic

variable {ι μ κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype μ] [DecidableEq μ]

/-- `(-A)⁻¹ = -A⁻¹` for square complex matrices (both sides vanish when `A` is singular). -/
theorem matrix_inv_neg {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) : (-A)⁻¹ = -A⁻¹ := by
  by_cases h : IsUnit A.det
  · exact Matrix.inv_eq_right_inv (by rw [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_nonsing_inv _ h])
  · have h' : ¬IsUnit (-A).det := by
      rw [det_neg]
      intro hu
      exact h ((IsUnit.mul_iff.1 hu).2)
    rw [nonsing_inv_apply_not_isUnit _ h, nonsing_inv_apply_not_isUnit _ h', neg_zero]

/-- Woodbury for the closed top matrix. -/
theorem inv_sub_mul_inv_mul (D : Matrix ι ι ℂ) (B : Matrix ι μ ℂ) (Gm : Matrix μ μ ℂ)
    (hD : IsUnit D.det) (hG : IsUnit Gm.det) (hQ : IsUnit (Gm - Bᴴ * D⁻¹ * B).det) :
    (D - B * Gm⁻¹ * Bᴴ)⁻¹ = D⁻¹ + D⁻¹ * B * (Gm - Bᴴ * D⁻¹ * B)⁻¹ * Bᴴ * D⁻¹ := by
  have hD' : IsUnit D := (Matrix.isUnit_iff_isUnit_det _).2 hD
  have hGi : IsUnit (-Gm⁻¹) := by
    exact (Matrix.isUnit_nonsing_inv_iff.2 ((Matrix.isUnit_iff_isUnit_det _).2 hG)).neg
  have hCinv : (-Gm⁻¹)⁻¹ = -Gm := by
    rw [matrix_inv_neg, Matrix.nonsing_inv_nonsing_inv _ hG]
  have hAC : IsUnit ((-Gm⁻¹)⁻¹ + Bᴴ * D⁻¹ * B) := by
    rw [hCinv, show -Gm + Bᴴ * D⁻¹ * B = -(Gm - Bᴴ * D⁻¹ * B) by abel]
    exact ((Matrix.isUnit_iff_isUnit_det _).2 hQ).neg
  have h := add_mul_mul_inv_eq_sub D B (-Gm⁻¹) Bᴴ hD' hGi hAC
  rw [hCinv, show -Gm + Bᴴ * D⁻¹ * B = -(Gm - Bᴴ * D⁻¹ * B) by abel, matrix_inv_neg] at h
  rw [show D - B * Gm⁻¹ * Bᴴ = D + B * -Gm⁻¹ * Bᴴ by
    rw [Matrix.mul_neg, Matrix.neg_mul, sub_eq_add_neg], h]
  simp only [Matrix.mul_neg, Matrix.neg_mul, sub_neg_eq_add]

open BlockBand.Critical.Collar.Kernel in
/-- **The closing identity** (generic finite form). For Hermitian `A'` (the
fresh top diagonal `A - e`), Hermitian `X`, Hermitian `G'` (the middle diagonal `G - (e+s)`),
`η > 0` and invertible `D = A' - X`, `G'`, `Q' = G' - B*D⁻¹B`: with
`K_c = A' - ξ - BG'⁻¹B*`, `K = (ξ + iη) - X`, `H_o = ξ - X`, `U = I - 2iη(K_c + iη)⁻¹`,
`𝔯 = I - 2iηK⁻¹`,
`-iJ*{2(I - U𝔯)⁻¹ - I}J = η⁻¹J*(KD⁻¹K* - H_o)J + η⁻¹(J*KD⁻¹B)Q'⁻¹(J*KD⁻¹B)*`. -/
theorem closing_identity (Atop X : Matrix ι ι ℂ) (B : Matrix ι μ ℂ) (Gm : Matrix μ μ ℂ)
    (ξ η : ℝ) (hA : Atop.IsHermitian) (hX : X.IsHermitian) (hG : Gm.IsHermitian) (hη : 0 < η)
    (hD : IsUnit (Atop - X).det) (hGu : IsUnit Gm.det)
    (hQ : IsUnit (Gm - Bᴴ * (Atop - X)⁻¹ * B).det) (J : Matrix ι κ ℂ) :
    (-Complex.I) • (Jᴴ * ((2 : ℂ) • (1 - cayleyOf (Atop - (ξ : ℂ) • 1 - B * Gm⁻¹ * Bᴴ) η *
        (1 - twoIEta η • (((ξ : ℂ) + (η : ℂ) * Complex.I) • (1 : Matrix ι ι ℂ) - X)⁻¹))⁻¹ - 1) * J) =
      ((η⁻¹ : ℝ) : ℂ) • (Jᴴ * ((((ξ : ℂ) + (η : ℂ) * Complex.I) • (1 : Matrix ι ι ℂ) - X) *
          (Atop - X)⁻¹ * (((ξ : ℂ) + (η : ℂ) * Complex.I) • (1 : Matrix ι ι ℂ) - X)ᴴ -
          ((ξ : ℂ) • 1 - X)) * J) +
      ((η⁻¹ : ℝ) : ℂ) • ((Jᴴ * (((ξ : ℂ) + (η : ℂ) * Complex.I) • (1 : Matrix ι ι ℂ) - X) *
          (Atop - X)⁻¹ * B) * (Gm - Bᴴ * (Atop - X)⁻¹ * B)⁻¹ *
        (Jᴴ * (((ξ : ℂ) + (η : ℂ) * Complex.I) • (1 : Matrix ι ι ℂ) - X) * (Atop - X)⁻¹ * B)ᴴ) := by
  set D := Atop - X with hDdef
  set Qm := Gm - Bᴴ * D⁻¹ * B with hQdef
  set Kc := Atop - (ξ : ℂ) • 1 - B * Gm⁻¹ * Bᴴ with hKcdef
  set Ho := (ξ : ℂ) • (1 : Matrix ι ι ℂ) - X with hHodef
  set K := ((ξ : ℂ) + (η : ℂ) * Complex.I) • (1 : Matrix ι ι ℂ) - X with hKdef
  have hHo : Ho.IsHermitian := by
    simp only [hHodef, IsHermitian, conjTranspose_sub, conjTranspose_smul, conjTranspose_one,
      hX.eq, Complex.star_def, Complex.conj_ofReal]
  have hDh : D.IsHermitian := hA.sub hX
  have hGi : (Gm⁻¹).IsHermitian := hG.inv
  have hKc : Kc.IsHermitian := by
    refine (hA.sub ?_).sub (isHermitian_mul_mul_conjTranspose B hGi)
    simp [IsHermitian, conjTranspose_smul]
  have hZ : boundaryZMat Ho 0 η = K := by
    simp only [boundaryZMat, add_zero, hHodef, hKdef, smul_smul, add_smul]
    module
  have hKu : IsUnit K.det := by
    have := isUnit_det_herm_add_I_smul hHo hη
    rw [← hZ]
    simp only [boundaryZMat, add_zero, smul_smul]
    rwa [mul_comm]
  have hM : Kc + Ho = D - B * Gm⁻¹ * Bᴴ := by
    simp only [hKcdef, hHodef, hDdef]; abel
  have hMinv : (Kc + Ho)⁻¹ = D⁻¹ + D⁻¹ * B * Qm⁻¹ * Bᴴ * D⁻¹ := by
    rw [hM]; exact inv_sub_mul_inv_mul D B Gm hD hGu hQ
  have hMu : IsUnit (Kc + Ho).det := by
    rw [hM]
    obtain ⟨iD⟩ := hD.nonempty_invertible
    obtain ⟨iG⟩ := hGu.nonempty_invertible
    let := Matrix.invertibleOfDetInvertible D
    let := Matrix.invertibleOfDetInvertible Gm
    have h1 := det_fromBlocks₁₁ D B Bᴴ Gm
    have h2 := det_fromBlocks₂₂ D B Bᴴ Gm
    rw [invOf_eq_nonsing_inv] at h1 h2
    have h3 : IsUnit (D.det * Qm.det) := hD.mul hQ
    rw [← h1, h2] at h3
    exact (IsUnit.mul_iff.1 h3).2
  set M := Kc + Ho with hMdef
  set P := Kc + ((η : ℂ) * Complex.I) • (1 : Matrix ι ι ℂ) with hPdef
  have hfac := one_sub_cayley_mul_scattering (Kc := Kc) (Ho := Ho) (Y := 0) hKc hη
    (by rw [hZ]; exact hKu)
  rw [hZ, smul_zero, add_zero] at hfac
  have hc : twoIEta η ≠ 0 := by
    simp only [twoIEta]
    exact mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast hη.ne')) Complex.I_ne_zero
  have hPu : IsUnit P.det := isUnit_det_herm_add_I_smul hKc hη
  have hinv : (1 - cayleyOf Kc η * scatteringOf K η)⁻¹ = (twoIEta η)⁻¹ • (K * M⁻¹ * P) := by
    rw [hfac]
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc, one_smul]
    calc P⁻¹ * M * K⁻¹ * (K * M⁻¹ * P) = P⁻¹ * (M * (K⁻¹ * K) * M⁻¹) * P := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [nonsing_inv_mul _ hKu, Matrix.mul_one, mul_nonsing_inv _ hMu, Matrix.mul_one,
            nonsing_inv_mul _ hPu]
  have hKh : Kᴴ = Ho - ((η : ℂ) * Complex.I) • 1 := by
    simp only [hKdef, hHodef, conjTranspose_sub, conjTranspose_smul, conjTranspose_one, hX.eq,
      star_add, star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
    module
  have hPM : P = M - Kᴴ := by
    rw [hKh, hPdef, hMdef]; abel
  have hK : K = Ho + ((η : ℂ) * Complex.I) • 1 := by
    simp only [hKdef, hHodef, add_smul]; abel
  have hinner : (-Complex.I) • ((2 : ℂ) • (1 - cayleyOf Kc η * scatteringOf K η)⁻¹ - 1) =
      ((η⁻¹ : ℝ) : ℂ) • (K * M⁻¹ * Kᴴ - Ho) := by
    rw [hinv, hPM, Matrix.mul_sub, nonsing_inv_mul_cancel_right _ _ hMu]
    set N := K * M⁻¹ * Kᴴ
    rw [hK]
    have hη' : (η : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
    simp only [twoIEta]
    push_cast
    match_scalars <;> (field_simp [Complex.I_ne_zero]; try ring_nf)
  change (-Complex.I) • (Jᴴ * ((2 : ℂ) • (1 - cayleyOf Kc η * scatteringOf K η)⁻¹ - 1) * J) = _
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, hinner, hMinv, conjTranspose_mul, conjTranspose_mul,
    conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, hDh.eq]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_assoc, smul_add, smul_sub]
  abel

end Generic

open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical

variable {W : ℕ}

/-- `D = A - e - X` on the two outer ports. -/
def topBlock (e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (ω : CollarSample W) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  blockDiag ω.1.1 - (e : ℂ) • 1 - X

/-- `Q = G + F = G - e - B*D⁻¹B` on the middle block (`F = -E - B*D⁻¹B`). -/
def portSchur (e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (ω : CollarSample W) :
    Matrix (PortSite W .common) (PortSite W .common) ℂ :=
  ω.2 - (e : ℂ) • 1 - (bondMatrix .common ω.1.2)ᴴ * (topBlock e X ω)⁻¹ * bondMatrix .common ω.1.2

/-- The constant `η⁻¹J*(KD⁻¹K* - H_o)J` of the physical collar function (`K = z_b - X`,
`H_o = ξ - X`). -/
def collarConst {r : ℕ} (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (J : Matrix (Fin 2 × Fin W) (Fin r) ℂ) (ω : CollarSample W) : Matrix (Fin r) (Fin r) ℂ :=
  (((boundaryZ b e).im⁻¹ : ℝ) : ℂ) • (Jᴴ * (matchedLeadK b e X * (topBlock e X ω)⁻¹ *
    (matchedLeadK b e X)ᴴ - (((boundaryZ b e).re : ℂ) • 1 - X)) * J)

/-- `J*KD⁻¹B` (`= -(T*K*J)*`, `T = -D⁻¹B`), so that `η⁻¹(J*KD⁻¹B)M(J*KD⁻¹B)* = V*MV`,
`V = η^{-1/2}T*K*J`. -/
def collarFrame {r : ℕ} (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (J : Matrix (Fin 2 × Fin W) (Fin r) ℂ) (ω : CollarSample W) :
    Matrix (Fin r) (PortSite W .common) ℂ :=
  Jᴴ * matchedLeadK b e X * (topBlock e X ω)⁻¹ * bondMatrix .common ω.1.2

open BlockBand.Critical.Collar.Kernel in
/-- **The physical collar function equals the physical collar value** for the collar
with a middle-only shift `s`. Deterministic, one collar sample with Hermitian blocks;
`X` Hermitian; `D`, `G - (e+s)` and `Q - s` invertible:
`-iJ*{2(I - U_s𝔯)⁻¹ - I}J = η⁻¹J*(KD⁻¹K* - H_o)J + η⁻¹(J*KD⁻¹B)(Q - s)⁻¹(J*KD⁻¹B)*`. -/
theorem closingMatrix_eq {r : ℕ} (b e s : ℝ) (hη : 0 < (boundaryZ b e).im)
    {ω : CollarSample W} (hA : ∀ j, (ω.1.1 j).IsHermitian) (hG : ω.2.IsHermitian)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian)
    (hD : IsUnit (topBlock e X ω).det) (hGs : IsUnit (ω.2 - ((e + s : ℝ) : ℂ) • 1).det)
    (hQ : IsUnit (portSchur e X ω - (s : ℂ) • 1).det) (J : Matrix (Fin 2 × Fin W) (Fin r) ℂ) :
    closingMatrix b e s X J ω = collarConst b e X J ω +
      (((boundaryZ b e).im⁻¹ : ℝ) : ℂ) • (collarFrame b e X J ω *
        (portSchur e X ω - (s : ℂ) • 1)⁻¹ * (collarFrame b e X J ω)ᴴ) := by
  set η := (boundaryZ b e).im
  set ξ := (boundaryZ b e).re
  set Atop := blockDiag ω.1.1 - (e : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
  set B := bondMatrix .common ω.1.2
  set Gm := ω.2 - ((e + s : ℝ) : ℂ) • (1 : Matrix (PortSite W .common) (PortSite W .common) ℂ)
  have hAt : Atop.IsHermitian := by
    refine (blockDiag_isHermitian' hA).sub ?_
    simp [IsHermitian, conjTranspose_smul]
  have hGm : Gm.IsHermitian := by
    refine hG.sub ?_
    simp [IsHermitian, conjTranspose_smul]
  have hDt : topBlock e X ω = Atop - X := rfl
  have hQt : portSchur e X ω - (s : ℂ) • 1 = Gm - Bᴴ * (Atop - X)⁻¹ * B := by
    simp only [portSchur, hDt, Gm, B]
    push_cast
    module
  have hz : boundaryZ b e = (ξ : ℂ) + (η : ℂ) * Complex.I := (Complex.re_add_im _).symm
  have hKc : middleReaction b e s ω = Atop - (ξ : ℂ) • 1 - B * Gm⁻¹ * Bᴴ := by
    simp only [middleReaction, Atop, B, Gm, add_smul]
    abel
  have hK : matchedLeadK b e X = ((ξ : ℂ) + (η : ℂ) * Complex.I) • 1 - X := by
    rw [matchedLeadK, hz]
  have key := closing_identity Atop X B Gm ξ η hAt hX hGm hη (hDt ▸ hD) hGs (hQt ▸ hQ) J
  rw [hQt]
  simp only [collarConst, collarFrame, hDt, hK]
  rw [← key]
  have hK' : boundaryZ b e • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X =
      ((ξ : ℂ) + (η : ℂ) * Complex.I) • 1 - X := hK
  simp only [closingMatrix, middleScattering, oldScattering, hKc, hK', cayleyOf, twoIEta]
  rfl

end BlockBand.Critical.MatrixClosing
