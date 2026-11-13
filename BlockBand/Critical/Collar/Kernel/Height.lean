module

public import BlockBand.Critical.Collar.Kernel.Universal

/-!
# The collar kernel at positive common height `ν > 0`

*Setting.* At height `ν > 0` the collar reaction `K_c` is not Hermitian: `Im K_c = ν(I + BD⁻¹D⁻*B*)`,
`D = G - (e + s) + iν`. The universal bound is proved directly, through the general weighted boundary identity
`𝒫(Ur) = η⁻¹[(I - ZR_c)Y(I - ZR_c)* + ZR_c Im(K_c) R_c* Z*]` (`weightedBoundaryIdentity_general`,
any `K_c` with `Im K_c ⪰ 0`), the three-block resolvent `𝓗_ν = ℋ_X + iν` and the fresh row
`ρ_ν = (z_b + e + s - iν - A, -B)`:
`q*𝒫(Ur)q ≤ η⁻¹[2(-Im⟨ρ_ν*q, 𝓗_ν⁻¹ ρ_ν*q⟩) + 2ν‖q‖²]` (`collar_poissonKernel_quad_le_height`),
then the scalar Cauchy dilation at `ε = ν` (no limit needed) and the fresh-row bound.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Kernel

open MeasureTheory Matrix Filter Topology
open BlockBand.Internal.Contracts
open BlockBand.Internal.Contracts.Layers
open BlockBand.Critical.Collar.Density (collarMatrix collarRowVec collarRowConst)
open scoped ComplexOrder ENNReal NNReal

/-!
## The general weighted boundary identity (`Im K_c ⪰ 0` allowed)
-/

section General

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Kc Ho Y : Matrix ι ι ℂ} {η : ℝ}

omit [DecidableEq ι] in
/-- `X = Re X + i Im X`. -/
theorem rePart_add_I_smul_imPart (X : Matrix ι ι ℂ) :
    rePart X + Complex.I • Critical.imPart X = X := by
  have h := rePart_sub_I_smul_neg_imPart X
  rw [smul_neg, sub_neg_eq_add] at h
  exact h

/-- `I - Ur = 2iη(K_c + iη)⁻¹(K_c + H_o + iY)Z⁻¹` for any `K_c` with `K_c + iη` invertible. -/
theorem one_sub_cayley_mul_scattering_of (hP : IsUnit (Kc + ((η : ℂ) * Complex.I) • 1).det)
    (hZ : IsUnit (boundaryZMat Ho Y η).det) :
    1 - cayleyOf Kc η * scatteringOf (boundaryZMat Ho Y η) η =
      twoIEta η • ((Kc + ((η : ℂ) * Complex.I) • 1)⁻¹ * (Kc + Ho + Complex.I • Y) *
        (boundaryZMat Ho Y η)⁻¹) := by
  set P := Kc + ((η : ℂ) * Complex.I) • (1 : Matrix ι ι ℂ) with hPdef
  set Z := boundaryZMat Ho Y η with hZdef
  have hQP : P⁻¹ * P = 1 := nonsing_inv_mul _ hP
  have hZZ : Z * Z⁻¹ = 1 := mul_nonsing_inv _ hZ
  have hM : Kc + Ho + Complex.I • Y = Z + P - twoIEta η • 1 := by
    simp only [hZdef, hPdef, boundaryZMat, twoIEta]
    module
  rw [hM]
  have r1 : P⁻¹ * (Z + P - twoIEta η • 1) * Z⁻¹ = P⁻¹ + Z⁻¹ - twoIEta η • (P⁻¹ * Z⁻¹) := by
    rw [Matrix.mul_sub, Matrix.mul_add, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_assoc P⁻¹ Z,
      hZZ, Matrix.mul_one, hQP, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul]
  rw [r1]
  simp only [cayleyOf, scatteringOf, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
    Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul]
  module

/-- **Cayley defect**: `I - UU* = 4η Q (Im K_c) Q*`, `Q = (K_c + iη)⁻¹`. -/
theorem one_sub_cayley_mul_conjTranspose_of (hP : IsUnit (Kc + ((η : ℂ) * Complex.I) • 1).det) :
    1 - cayleyOf Kc η * (cayleyOf Kc η)ᴴ =
      ((4 * η : ℝ) : ℂ) • ((Kc + ((η : ℂ) * Complex.I) • 1)⁻¹ * Critical.imPart Kc *
        ((Kc + ((η : ℂ) * Complex.I) • 1)⁻¹)ᴴ) := by
  set P := Kc + ((η : ℂ) * Complex.I) • (1 : Matrix ι ι ℂ)
  set Q := P⁻¹
  have hPhu : IsUnit Pᴴ.det := by rw [det_conjTranspose]; exact hP.star
  have hQh : Qᴴ = (Pᴴ)⁻¹ := by rw [conjTranspose_nonsing_inv]
  have e1 : Q * P = 1 := nonsing_inv_mul _ hP
  have e2 : Pᴴ * Qᴴ = 1 := by rw [hQh]; exact mul_nonsing_inv _ hPhu
  have hdiff : Q - Qᴴ = Q * (Pᴴ - P) * Qᴴ := by
    calc Q - Qᴴ = Q * (Pᴴ * Qᴴ) - (Q * P) * Qᴴ := by rw [e1, e2, Matrix.mul_one, Matrix.one_mul]
      _ = Q * (Pᴴ - P) * Qᴴ := by
        rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc]
  have hPP : Pᴴ - P = (-(2 * Complex.I)) • Critical.imPart Kc - twoIEta η • 1 := by
    simp only [P, conjTranspose_add, conjTranspose_smul, conjTranspose_one, star_mul',
      Complex.star_def, Complex.conj_ofReal, Complex.conj_I, twoIEta, Critical.imPart, smul_smul]
    rw [show -(2 * Complex.I) * (2 * Complex.I)⁻¹ = -1 by
      field_simp]
    module
  rw [cayleyOf, conjTranspose_sub, conjTranspose_one, conjTranspose_smul, star_twoIEta]
  change 1 - (1 - twoIEta η • Q) * (1 - (-twoIEta η) • Qᴴ) = _
  have hexp : 1 - (1 - twoIEta η • Q) * (1 - (-twoIEta η) • Qᴴ) =
      twoIEta η • (Q - Qᴴ) + (twoIEta η * twoIEta η) • (Q * Qᴴ) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul]
    module
  rw [hexp, hdiff, hPP]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  simp only [twoIEta]
  push_cast
  match_scalars
  all_goals ring_nf
  all_goals simp only [hI]
  all_goals ring

/-- **General weighted boundary identity** (`K_c` not necessarily Hermitian):
for Hermitian `H_o, Y`, `η > 0`, invertible `K_c + iη`, `Z = H_o + i(ηI + Y)` and
`M = K_c + H_o + iY`: `I - Ur` is invertible and
`𝒫(Ur) = η⁻¹[(I - ZM⁻¹) Y (I - ZM⁻¹)* + (ZM⁻¹) Im(K_c) (ZM⁻¹)*]`. Deterministic. -/
theorem weightedBoundaryIdentity_general (hHo : Ho.IsHermitian) (hY : Y.IsHermitian)
    (hη : 0 < η) (hP : IsUnit (Kc + ((η : ℂ) * Complex.I) • 1).det)
    (hZ : IsUnit (boundaryZMat Ho Y η).det) (hM : IsUnit (Kc + Ho + Complex.I • Y).det) :
    IsUnit (1 - cayleyOf Kc η * scatteringOf (boundaryZMat Ho Y η) η).det ∧
    Critical.poissonKernel (cayleyOf Kc η * scatteringOf (boundaryZMat Ho Y η) η) =
      ((η⁻¹ : ℝ) : ℂ) • ((1 - boundaryZMat Ho Y η * (Kc + Ho + Complex.I • Y)⁻¹) * Y *
        (1 - boundaryZMat Ho Y η * (Kc + Ho + Complex.I • Y)⁻¹)ᴴ +
        (boundaryZMat Ho Y η * (Kc + Ho + Complex.I • Y)⁻¹) * Critical.imPart Kc *
          (boundaryZMat Ho Y η * (Kc + Ho + Complex.I • Y)⁻¹)ᴴ) := by
  have hfac := one_sub_cayley_mul_scattering_of (Ho := Ho) (Y := Y) hP hZ
  set P := Kc + ((η : ℂ) * Complex.I) • (1 : Matrix ι ι ℂ) with hPdef
  set Z := boundaryZMat Ho Y η with hZdef
  set M := Kc + Ho + Complex.I • Y with hMdef
  set a := twoIEta η with hadef
  set U := cayleyOf Kc η with hUdef
  set r := scatteringOf Z η with hrdef
  have ha : a ≠ 0 := by
    simp only [hadef, twoIEta]
    exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr hη.ne'))
      Complex.I_ne_zero
  have hdet : IsUnit (1 - U * r).det := by
    rw [hfac, det_smul, det_mul, det_mul, det_nonsing_inv, det_nonsing_inv]
    exact ((isUnit_iff_ne_zero.mpr ha).pow _).mul (((hP.ringInverse).mul hM).mul
      hZ.ringInverse)
  refine ⟨hdet, ?_⟩
  set T := a⁻¹ • (Z * M⁻¹ * P) with hTdef
  have hT : (1 - U * r)⁻¹ = T := by
    refine Matrix.inv_eq_right_inv ?_
    rw [hfac]
    have e1 : Z⁻¹ * Z = 1 := nonsing_inv_mul _ hZ
    have e2 : M * M⁻¹ = 1 := mul_nonsing_inv _ hM
    have e3 : P⁻¹ * P = 1 := nonsing_inv_mul _ hP
    have : P⁻¹ * M * Z⁻¹ * (Z * M⁻¹ * P) = 1 := by
      calc P⁻¹ * M * Z⁻¹ * (Z * M⁻¹ * P) = P⁻¹ * (M * (Z⁻¹ * Z) * M⁻¹) * P := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [e1, Matrix.mul_one, e2, Matrix.mul_one, e3]
    rw [hTdef, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ ha, one_smul, this]
  have hU : 1 - U * Uᴴ = ((4 * η : ℝ) : ℂ) • (P⁻¹ * Critical.imPart Kc * (P⁻¹)ᴴ) :=
    one_sub_cayley_mul_conjTranspose_of hP
  have hr : r * rᴴ = 1 - ((4 * η : ℝ) : ℂ) • (Z⁻¹ * Y * (Z⁻¹)ᴴ) :=
    one_sub_scattering_mul_conjTranspose hZ (boundaryZMat_sub_conjTranspose hHo hY)
  have hdefect : 1 - (U * r) * (U * r)ᴴ = ((4 * η : ℝ) : ℂ) • (P⁻¹ * Critical.imPart Kc * (P⁻¹)ᴴ) +
      ((4 * η : ℝ) : ℂ) • (U * Z⁻¹ * Y * (U * Z⁻¹)ᴴ) := by
    rw [← hU, conjTranspose_mul, show U * r * (rᴴ * Uᴴ) = U * (r * rᴴ) * Uᴴ by
      simp only [Matrix.mul_assoc], hr, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.mul_smul, Matrix.smul_mul, conjTranspose_mul]
    simp only [Matrix.mul_assoc]
    abel
  have e1 : P * P⁻¹ = 1 := mul_nonsing_inv _ hP
  have hTQ : T * P⁻¹ = a⁻¹ • (Z * M⁻¹) := by
    rw [hTdef, Matrix.smul_mul, Matrix.mul_assoc, e1, Matrix.mul_one]
  have hTUZ : T * U * Z⁻¹ = a⁻¹ • (1 - Z * M⁻¹) := by
    have e2 : M⁻¹ * M = 1 := nonsing_inv_mul _ hM
    have e3 : Z * Z⁻¹ = 1 := mul_nonsing_inv _ hZ
    have hPa : P - a • 1 = M - Z := by
      simp only [hPdef, hMdef, hZdef, hadef, boundaryZMat, twoIEta]
      module
    have hPU : P * U = M - Z := by
      rw [hUdef, cayleyOf, ← hPdef, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, e1, ← hPa]
    rw [hTdef, Matrix.smul_mul, Matrix.smul_mul]
    congr 1
    calc Z * M⁻¹ * P * U * Z⁻¹ = Z * M⁻¹ * (P * U) * Z⁻¹ := by simp only [Matrix.mul_assoc]
      _ = Z * (M⁻¹ * M) * Z⁻¹ - Z * M⁻¹ * (Z * Z⁻¹) := by
          rw [hPU, Matrix.mul_sub, Matrix.sub_mul]; simp only [Matrix.mul_assoc]
      _ = 1 - Z * M⁻¹ := by rw [e2, e3, Matrix.mul_one, Matrix.mul_one, e3]
  have hTh : (1 - (U * r)ᴴ)⁻¹ = Tᴴ := by
    rw [show (1 : Matrix ι ι ℂ) - (U * r)ᴴ = (1 - U * r)ᴴ by simp, ← conjTranspose_nonsing_inv, hT]
  rw [poissonKernel_eq_sandwich _ hdet, hT, hTh, hdefect]
  clear_value T
  have hsplit : T * (((4 * η : ℝ) : ℂ) • (P⁻¹ * Critical.imPart Kc * (P⁻¹)ᴴ) +
      ((4 * η : ℝ) : ℂ) • (U * Z⁻¹ * Y * (U * Z⁻¹)ᴴ)) * Tᴴ =
      ((4 * η : ℝ) : ℂ) • ((T * P⁻¹) * Critical.imPart Kc * (T * P⁻¹)ᴴ) +
      ((4 * η : ℝ) : ℂ) • ((T * U * Z⁻¹) * Y * (T * U * Z⁻¹)ᴴ) := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.smul_mul]
    congr 2 <;> simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [hsplit, hTQ, hTUZ]
  simp only [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add]
  have hsc : ((4 * η : ℝ) : ℂ) * (star a⁻¹ * a⁻¹) = ((η⁻¹ : ℝ) : ℂ) := by
    rw [star_inv₀, hadef, star_twoIEta]
    simp only [twoIEta]
    have hη0 : (η : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hη.ne'
    field_simp
    push_cast
    ring_nf
    simp only [Complex.I_sq]
    field_simp
  rw [hsc, add_comm]

end General

/-!
## The collar at height `ν`
-/

section Collar

variable {W : ℕ}

/-- The middle block at height `ν`: `D_ν = G - (e + s - iν)`. -/
abbrev middleBlockH (e s ν : ℝ) (ω : Critical.CollarSample W) :
    Matrix (PortSite W .common) (PortSite W .common) ℂ := ω.2 - Critical.collarShift e s ν • 1

/-- The collar Schur complement at height `ν`: `S_ν = A - (e+s-iν) - X - B D_ν⁻¹ B*`. -/
def collarSchurH (e s ν : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : Critical.CollarSample W) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  Layers.blockDiag ω.1.1 - Critical.collarShift e s ν • 1 - X -
    bondMatrix .common ω.1.2 * (middleBlockH e s ν ω)⁻¹ * (bondMatrix .common ω.1.2)ᴴ

theorem isUnit_det_middleBlockH (e s : ℝ) {ν : ℝ} (hν : 0 < ν) {ω : Critical.CollarSample W}
    (hG : ω.2.IsHermitian) : IsUnit (middleBlockH e s ν ω).det := by
  have h : middleBlockH e s ν ω = (ω.2 - ((e + s : ℝ) : ℂ) • 1) + Complex.I • ((ν : ℂ) • 1) := by
    simp only [middleBlockH, Critical.collarShift, smul_smul, sub_smul]
    module
  rw [h]
  exact isUnit_det_herm_add_I_smul_posDef (hG.sub (by simp [IsHermitian, conjTranspose_smul]))
    (Matrix.PosDef.one.smul (by exact_mod_cast hν))

/-- `K_c + H_o + iY = S_ν` (`H_o = ξ - X_h`, `X = X_h - iY`). -/
theorem collarReaction_add_height (b e s ν : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : Critical.CollarSample W) :
    Critical.collarReaction b e s ν ω + (((boundaryZ b e).re : ℂ) • 1 - rePart X) +
        Complex.I • (-Critical.imPart X) = collarSchurH e s ν X ω := by
  have hX := rePart_sub_I_smul_neg_imPart X
  rw [Critical.collarReaction, collarSchurH]
  generalize rePart X = Xh at *
  generalize Critical.imPart X = Ym at *
  subst hX
  simp only [middleBlockH, add_smul]
  module

/-- `Im K_c = ν (I + B D_ν⁻¹ D_ν⁻* B*)` (Hermitian `A_j`, `G`; `D_ν` invertible). -/
theorem imPart_collarReaction (b e s ν : ℝ) {ω : Critical.CollarSample W}
    (hA : ∀ j, (ω.1.1 j).IsHermitian) (hG : ω.2.IsHermitian)
    (hD : IsUnit (middleBlockH e s ν ω).det) :
    Critical.imPart (Critical.collarReaction b e s ν ω) = (ν : ℂ) • (1 +
      bondMatrix .common ω.1.2 * (middleBlockH e s ν ω)⁻¹ * ((middleBlockH e s ν ω)⁻¹)ᴴ *
        (bondMatrix .common ω.1.2)ᴴ) := by
  set D := middleBlockH e s ν ω
  set B := bondMatrix .common ω.1.2
  have hDh : IsUnit Dᴴ.det := by rw [det_conjTranspose]; exact hD.star
  have e1 : D⁻¹ * D = 1 := nonsing_inv_mul _ hD
  have e2 : Dᴴ * (D⁻¹)ᴴ = 1 := by rw [conjTranspose_nonsing_inv]; exact mul_nonsing_inv _ hDh
  have hDD : Dᴴ - D = (-(2 * Complex.I * ν)) • (1 : Matrix (PortSite W .common) _ ℂ) := by
    simp only [D, middleBlockH, conjTranspose_sub, hG.eq, conjTranspose_smul, conjTranspose_one,
      Critical.collarShift, star_sub, star_mul', Complex.star_def, Complex.conj_ofReal,
      Complex.conj_I]
    module
  have hinv : D⁻¹ - (D⁻¹)ᴴ = (-(2 * Complex.I * ν)) • (D⁻¹ * (D⁻¹)ᴴ) := by
    calc D⁻¹ - (D⁻¹)ᴴ = D⁻¹ * (Dᴴ - D) * (D⁻¹)ᴴ := by
          rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, e2, Matrix.mul_one, e1,
            Matrix.one_mul]
      _ = _ := by rw [hDD, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  have hAd := blockDiag_isHermitian' hA
  have hK : Critical.collarReaction b e s ν ω - (Critical.collarReaction b e s ν ω)ᴴ =
      (2 * Complex.I * ν) • (1 + B * D⁻¹ * (D⁻¹)ᴴ * Bᴴ) := by
    have h1 : Critical.collarReaction b e s ν ω = Layers.blockDiag ω.1.1 -
        (Critical.collarShift e s ν + ((boundaryZ b e).re : ℂ)) • 1 - B * D⁻¹ * Bᴴ := rfl
    rw [h1]
    simp only [conjTranspose_sub, conjTranspose_smul, conjTranspose_one, hAd.eq,
      conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    have h2 : B * (D⁻¹ * Bᴴ) - B * ((D⁻¹)ᴴ * Bᴴ) = B * ((D⁻¹ - (D⁻¹)ᴴ) * Bᴴ) := by
      rw [Matrix.sub_mul, Matrix.mul_sub]
    have h3 : star (Critical.collarShift e s ν + ((boundaryZ b e).re : ℂ)) -
        (Critical.collarShift e s ν + ((boundaryZ b e).re : ℂ)) = 2 * Complex.I * ν := by
      simp only [Critical.collarShift, star_add, star_sub, star_mul', Complex.star_def,
        Complex.conj_ofReal, Complex.conj_I]
      ring
    have h4 : Layers.blockDiag ω.1.1 - (Critical.collarShift e s ν + ((boundaryZ b e).re : ℂ)) • 1 -
        B * (D⁻¹ * Bᴴ) - (Layers.blockDiag ω.1.1 - star (Critical.collarShift e s ν +
          ((boundaryZ b e).re : ℂ)) • 1 - B * ((D⁻¹)ᴴ * Bᴴ)) =
        (star (Critical.collarShift e s ν + ((boundaryZ b e).re : ℂ)) -
          (Critical.collarShift e s ν + ((boundaryZ b e).re : ℂ))) • 1 -
          (B * (D⁻¹ * Bᴴ) - B * ((D⁻¹)ᴴ * Bᴴ)) := by
      rw [sub_smul]; abel
    rw [h4, h2, h3, hinv, Matrix.smul_mul, Matrix.mul_smul]
    simp only [Matrix.mul_assoc, smul_add, neg_smul, sub_neg_eq_add]
  rw [Critical.imPart, hK, smul_smul]
  congr 1
  field_simp

theorem imPart_collarReaction_posSemidef (b e s : ℝ) {ν : ℝ} (hν : 0 ≤ ν)
    {ω : Critical.CollarSample W} (hA : ∀ j, (ω.1.1 j).IsHermitian) (hG : ω.2.IsHermitian)
    (hD : IsUnit (middleBlockH e s ν ω).det) :
    (Critical.imPart (Critical.collarReaction b e s ν ω)).PosSemidef := by
  rw [imPart_collarReaction b e s ν hA hG hD]
  refine PosSemidef.smul ?_ (Complex.zero_le_real.2 hν)
  refine PosSemidef.one.add ?_
  have := (PosSemidef.one (n := PortSite W .common) (R := ℂ)).mul_mul_conjTranspose_same
    (bondMatrix .common ω.1.2 * (middleBlockH e s ν ω)⁻¹)
  simpa [conjTranspose_mul, Matrix.mul_assoc] using this

/-- `K + iη` is invertible when `Im K ⪰ 0`, `η > 0`. -/
theorem isUnit_det_add_I_of_imPart {ι : Type} [Fintype ι] [DecidableEq ι] {K : Matrix ι ι ℂ}
    (hK : (Critical.imPart K).PosSemidef) {η : ℝ} (hη : 0 < η) :
    IsUnit (K + ((η : ℂ) * Complex.I) • 1).det := by
  have h : K + ((η : ℂ) * Complex.I) • (1 : Matrix ι ι ℂ) =
      rePart K + Complex.I • (Critical.imPart K + (η : ℂ) • 1) := by
    conv_lhs => rw [← rePart_add_I_smul_imPart K]
    module
  rw [h]
  exact isUnit_det_herm_add_I_smul_posDef (rePart_isHermitian K)
    ((Matrix.PosDef.one.smul (by exact_mod_cast hη)).posSemidef_add hK)

/-- `S_ν` is invertible for `ν > 0`, `Y ⪰ 0` (Hermitian `A_j`, `G`). -/
theorem isUnit_det_collarSchurH (b e s : ℝ) {ν : ℝ} (hν : 0 < ν) {ω : Critical.CollarSample W}
    (hA : ∀ j, (ω.1.1 j).IsHermitian) (hG : ω.2.IsHermitian)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hY : (-Critical.imPart X).PosSemidef) :
    IsUnit (collarSchurH e s ν X ω).det := by
  have hD := isUnit_det_middleBlockH e s hν hG
  have hS : collarSchurH e s ν X ω = (rePart (Critical.collarReaction b e s ν ω) +
      (((boundaryZ b e).re : ℂ) • 1 - rePart X)) +
      Complex.I • (Critical.imPart (Critical.collarReaction b e s ν ω) + -Critical.imPart X) := by
    have h0 := rePart_add_I_smul_imPart (Critical.collarReaction b e s ν ω)
    rw [← collarReaction_add_height b e s ν X ω]
    nth_rewrite 1 [← h0]
    module
  rw [hS]
  refine isUnit_det_herm_add_I_smul_posDef ((rePart_isHermitian _).add
    ((by simp [IsHermitian, conjTranspose_smul] :
      (((boundaryZ b e).re : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)).IsHermitian).sub
      (rePart_isHermitian X))) ?_
  rw [imPart_collarReaction b e s ν hA hG hD, smul_add, add_assoc]
  refine (Matrix.PosDef.one.smul (by exact_mod_cast hν)).add_posSemidef ?_
  refine PosSemidef.add ?_ hY
  refine PosSemidef.smul ?_ (Complex.zero_le_real.2 hν.le)
  have := (PosSemidef.one (n := PortSite W .common) (R := ℂ)).mul_mul_conjTranspose_same
    (bondMatrix .common ω.1.2 * (middleBlockH e s ν ω)⁻¹)
  simpa [conjTranspose_mul, Matrix.mul_assoc] using this

/-- **The collar kernel at height `ν > 0`** (any real shift `s`, `Y = -Im X ⪰ 0`, Hermitian
`A_j, G`): `𝒫(Ur) = η⁻¹[(I - ZS_ν⁻¹) Y (I - ZS_ν⁻¹)* + (ZS_ν⁻¹) Im(K_c) (ZS_ν⁻¹)*]`,
`Z = z_b - X`. -/
theorem collar_poissonKernel_eq_height (b e s : ℝ) {ν : ℝ} (hν : 0 < ν)
    (hη : 0 < (boundaryZ b e).im) {ω : Critical.CollarSample W}
    (hA : ∀ j, (ω.1.1 j).IsHermitian) (hG : ω.2.IsHermitian)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hY : (-Critical.imPart X).PosSemidef) :
    Critical.poissonKernel (Critical.collarScattering b e s ν ω * Critical.oldScattering b e X) =
      (((boundaryZ b e).im⁻¹ : ℝ) : ℂ) •
        ((1 - (boundaryZ b e • 1 - X) * (collarSchurH e s ν X ω)⁻¹) * (-Critical.imPart X) *
          (1 - (boundaryZ b e • 1 - X) * (collarSchurH e s ν X ω)⁻¹)ᴴ +
        ((boundaryZ b e • 1 - X) * (collarSchurH e s ν X ω)⁻¹) *
          Critical.imPart (Critical.collarReaction b e s ν ω) *
          ((boundaryZ b e • 1 - X) * (collarSchurH e s ν X ω)⁻¹)ᴴ) := by
  have hD := isUnit_det_middleBlockH e s hν hG
  set K := Critical.collarReaction b e s ν ω
  set Ho : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ := ((boundaryZ b e).re : ℂ) • 1 - rePart X
  have hHo : Ho.IsHermitian :=
    (by simp [IsHermitian, conjTranspose_smul] :
      (((boundaryZ b e).re : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)).IsHermitian).sub
      (rePart_isHermitian X)
  have hZeq : boundaryZMat Ho (-Critical.imPart X) (boundaryZ b e).im = boundaryZ b e • 1 - X :=
    boundaryZMat_eq b e X
  have hZ : IsUnit (boundaryZMat Ho (-Critical.imPart X) (boundaryZ b e).im).det := by
    have hpd : (((boundaryZ b e).im : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) +
        -Critical.imPart X).PosDef :=
      (Matrix.PosDef.one.smul (by exact_mod_cast hη)).add_posSemidef hY
    exact isUnit_det_herm_add_I_smul_posDef hHo hpd
  have hMeq : K + Ho + Complex.I • (-Critical.imPart X) = collarSchurH e s ν X ω :=
    collarReaction_add_height b e s ν X ω
  have hM : IsUnit (K + Ho + Complex.I • (-Critical.imPart X)).det := by
    rw [hMeq]; exact isUnit_det_collarSchurH b e s hν hA hG hY
  have hP := isUnit_det_add_I_of_imPart (imPart_collarReaction_posSemidef b e s hν.le hA hG hD) hη
  have h := (weightedBoundaryIdentity_general hHo (imPart_isHermitian X).neg hη hP hZ hM).2
  have hU : cayleyOf K (boundaryZ b e).im = Critical.collarScattering b e s ν ω := rfl
  have hr : scatteringOf (boundaryZMat Ho (-Critical.imPart X) (boundaryZ b e).im)
      (boundaryZ b e).im = Critical.oldScattering b e X := by
    rw [hZeq]; rfl
  rw [hU, hr, hZeq, hMeq] at h
  exact h

/-- The three-block matrix at height `ν`: `𝓗_ν = ℋ_X + iν` at energy `e + s`. -/
abbrev heightMatrix (e s ν : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : Critical.CollarSample W) : Matrix (LayerSite W .common) (LayerSite W .common) ℂ :=
  collarMatrix (e + s) X ω + ((ν : ℂ) * Complex.I) • 1

theorem heightMatrix_eq_fromBlocks (e s ν : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : Critical.CollarSample W) :
    heightMatrix e s ν X ω = Matrix.fromBlocks
      (Layers.blockDiag ω.1.1 - Critical.collarShift e s ν • 1 - X) (bondMatrix .common ω.1.2)
      (bondMatrix .common ω.1.2)ᴴ (middleBlockH e s ν ω) := by
  rw [heightMatrix, collarMatrix, ← fromBlocks_one, fromBlocks_smul, fromBlocks_add]
  simp only [smul_zero, add_zero, middleBlockH, Critical.collarShift]
  congr 1
  · rw [sub_smul]; push_cast; module
  · rw [sub_smul]; push_cast; module

theorem isUnit_det_heightMatrix (e s : ℝ) {ν : ℝ} (hν : 0 < ν) {ω : Critical.CollarSample W}
    (hA : ∀ j, (ω.1.1 j).IsHermitian) (hG : ω.2.IsHermitian)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hY : (-Critical.imPart X).PosSemidef) :
    IsUnit (heightMatrix e s ν X ω).det := by
  have h : heightMatrix e s ν X ω = collarMatrix (e + s) (rePart X) ω +
      Complex.I • (topLift (-Critical.imPart X) + (ν : ℂ) • 1) := by
    rw [heightMatrix, collarMatrix_eq_herm_add]
    module
  rw [h]
  have hpd : ((ν : ℂ) • (1 : Matrix (LayerSite W .common) (LayerSite W .common) ℂ)).PosDef :=
    Matrix.PosDef.one.smul (by exact_mod_cast hν)
  have hsum := hpd.posSemidef_add (topLift_posSemidef hY)
  refine isUnit_det_herm_add_I_smul_posDef
    (collarMatrix_isHermitian (e + s) hA hG (rePart_isHermitian X)) ?_
  exact hsum

/-- `⟨u, P M M* P* u⟩ = ‖M* P* u‖²` (as a dot product). -/
theorem dotProduct_mul_mul_conjTranspose_mul {k l : Type*} [Fintype k] [Fintype l]
    [DecidableEq l] (P : Matrix k l ℂ) (M : Matrix l l ℂ) (u : k → ℂ) :
    star u ⬝ᵥ ((P * M * Mᴴ * Pᴴ) *ᵥ u) = star (Mᴴ *ᵥ (Pᴴ *ᵥ u)) ⬝ᵥ (Mᴴ *ᵥ (Pᴴ *ᵥ u)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, dotProduct_mulVec,
    star_mulVec, star_mulVec, conjTranspose_conjTranspose, conjTranspose_conjTranspose,
    vecMul_vecMul]

/-- `‖a + b‖² ≤ 2‖a‖² + 2‖b‖²` for the `ℓ²` form. -/
theorem sum_norm_sq_add_le {κ : Type*} [Fintype κ] (a b : κ → ℂ) :
    ∑ i, ‖a i + b i‖ ^ 2 ≤ 2 * ∑ i, ‖a i‖ ^ 2 + 2 * ∑ i, ‖b i‖ ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := norm_add_le (a i) (b i)
  have h0 := norm_nonneg (a i + b i)
  nlinarith [sq_nonneg (‖a i‖ - ‖b i‖), norm_nonneg (a i), norm_nonneg (b i)]

/-- **Height-`ν` row bound** (deterministic; Hermitian `A_j`, `G`, `ν > 0`, real shift `s`,
`Y = -Im X ⪰ 0`): with the fresh row vector `y = ρ_ν* q`, `ρ_ν = (z_b + e + s - iν - A, -B)`,
`Re q*𝒫(Ur)q ≤ η⁻¹ [2 (-Im⟨y, 𝓗_ν⁻¹ y⟩) + 2ν ‖q‖²]`. -/
theorem collar_poissonKernel_quad_le_height (b e s : ℝ) {ν : ℝ} (hν : 0 < ν)
    (hη : 0 < (boundaryZ b e).im) {ω : Critical.CollarSample W}
    (hA : ∀ j, (ω.1.1 j).IsHermitian) (hG : ω.2.IsHermitian)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hY : (-Critical.imPart X).PosSemidef)
    (q : Fin 2 × Fin W → ℂ) :
    (star q ⬝ᵥ (Critical.poissonKernel (Critical.collarScattering b e s ν ω *
        Critical.oldScattering b e X) *ᵥ q)).re ≤
      (boundaryZ b e).im⁻¹ * (2 * (-(star (collarRowVec (star (boundaryZ b e +
        Critical.collarShift e s ν)) q ω) ⬝ᵥ ((heightMatrix e s ν X ω)⁻¹ *ᵥ
          collarRowVec (star (boundaryZ b e + Critical.collarShift e s ν)) q ω)).im) +
        2 * ν * ∑ x, ‖q x‖ ^ 2) := by
  set c := Critical.collarShift e s ν
  set Z : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ := boundaryZ b e • 1 - X
  set S := collarSchurH e s ν X ω
  set D := middleBlockH e s ν ω
  set B := bondMatrix .common ω.1.2
  set TL : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ := Layers.blockDiag ω.1.1 - c • 1 - X
  set H := heightMatrix e s ν X ω
  set Yo := -Critical.imPart X
  set y := collarRowVec (star (boundaryZ b e + c)) q ω
  have hD : IsUnit D.det := isUnit_det_middleBlockH e s hν hG
  have hS : IsUnit S.det := isUnit_det_collarSchurH b e s hν hA hG hY
  have hH : IsUnit H.det := isUnit_det_heightMatrix e s hν hA hG hY
  have hSh : IsUnit Sᴴ.det := by rw [det_conjTranspose]; exact hS.star
  have hDh : IsUnit Dᴴ.det := by rw [det_conjTranspose]; exact hD.star
  have hAd := blockDiag_isHermitian' hA
  have hHb : H = Matrix.fromBlocks TL B Bᴴ D := heightMatrix_eq_fromBlocks e s ν X ω
  have hHh : Hᴴ = Matrix.fromBlocks TLᴴ B Bᴴ Dᴴ := by
    rw [hHb, fromBlocks_conjTranspose, conjTranspose_conjTranspose]
  have hSdef : S = TL - B * D⁻¹ * Bᴴ := rfl
  have hShdef : Sᴴ = TLᴴ - B * (Dᴴ)⁻¹ * Bᴴ := by
    rw [hSdef, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
      conjTranspose_nonsing_inv, Matrix.mul_assoc]
  -- the solution `u` of `𝓗* u = (Z* q, 0)`
  set u₁ := (Sᴴ)⁻¹ *ᵥ (Zᴴ *ᵥ q)
  set u₂ := -((Dᴴ)⁻¹ *ᵥ (Bᴴ *ᵥ u₁))
  set u : LayerSite W .common → ℂ := Sum.elim u₁ u₂
  set qh : LayerSite W .common → ℂ := Sum.elim q 0
  set v := u - qh
  have hu : Hᴴ *ᵥ u = Sum.elim (Zᴴ *ᵥ q) 0 := by
    rw [hHh, fromBlocks_mulVec]
    have e1 : (u ∘ Sum.inl) = u₁ := rfl
    have e2 : (u ∘ Sum.inr) = u₂ := rfl
    rw [e1, e2]
    congr 1
    · have : Sᴴ *ᵥ u₁ = Zᴴ *ᵥ q := by
        simp only [u₁, mulVec_mulVec]
        rw [← Matrix.mul_assoc, mul_nonsing_inv _ hSh, Matrix.one_mul]
      rw [← this, hShdef, sub_mulVec]
      simp only [u₂, mulVec_neg, mulVec_mulVec, Matrix.mul_assoc]
      abel
    · simp only [u₂, mulVec_neg, mulVec_mulVec, ← Matrix.mul_assoc, mul_nonsing_inv _ hDh,
        Matrix.one_mul]
      abel
  have hy : y = Sum.elim (Zᴴ *ᵥ q) 0 - Hᴴ *ᵥ qh := by
    rw [hHh, fromBlocks_mulVec]
    have e1 : (qh ∘ Sum.inl) = q := rfl
    have e2 : (qh ∘ Sum.inr) = 0 := rfl
    rw [e1, e2, mulVec_zero, mulVec_zero, add_zero, add_zero]
    have htop : Zᴴ *ᵥ q - TLᴴ *ᵥ q = star (boundaryZ b e + c) • q - Layers.blockDiag ω.1.1 *ᵥ q := by
      rw [← sub_mulVec]
      have : Zᴴ - TLᴴ = (star (boundaryZ b e + c)) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
          Layers.blockDiag ω.1.1 := by
        simp only [Z, TL, conjTranspose_sub, conjTranspose_smul, conjTranspose_one, hAd.eq,
          star_add, add_smul]
        abel
      rw [this, sub_mulVec, smul_mulVec, one_mulVec]
    funext i
    rcases i with x | p
    · simp only [y, collarRowVec, Sum.elim_inl, Pi.sub_apply]
      rw [← Pi.sub_apply (Zᴴ *ᵥ q), htop]
      rfl
    · simp only [y, collarRowVec, Sum.elim_inr, Pi.sub_apply, Pi.zero_apply, zero_sub]
      rfl
  have hv : Hᴴ *ᵥ v = y := by rw [mulVec_sub, hu, hy]
  -- the kernel quadratic form
  have hK := collar_poissonKernel_eq_height b e s hν hη hA hG hY
  have hM1 : (1 - Z * S⁻¹)ᴴ *ᵥ q = -(v ∘ Sum.inl) := by
    have : (v ∘ Sum.inl) = u₁ - q := rfl
    rw [this, conjTranspose_sub, conjTranspose_one, conjTranspose_mul, conjTranspose_nonsing_inv,
      sub_mulVec, one_mulVec, ← mulVec_mulVec]
    abel
  have hM2 : (Z * S⁻¹)ᴴ *ᵥ q = u₁ := by
    rw [conjTranspose_mul, conjTranspose_nonsing_inv, ← mulVec_mulVec]
  have hImK : star u₁ ⬝ᵥ (Critical.imPart (Critical.collarReaction b e s ν ω) *ᵥ u₁) =
      (ν : ℂ) * (star u₁ ⬝ᵥ u₁ + star u₂ ⬝ᵥ u₂) := by
    rw [imPart_collarReaction b e s ν hA hG hD, smul_mulVec, dotProduct_smul, smul_eq_mul,
      add_mulVec, one_mulVec, dotProduct_add]
    congr 2
    rw [dotProduct_mul_mul_conjTranspose_mul, conjTranspose_nonsing_inv]
    simp only [u₂, star_neg, neg_dotProduct, dotProduct_neg, neg_neg]
    rfl
  -- the two quadratic forms
  set v₁ : Fin 2 × Fin W → ℂ := v ∘ Sum.inl
  have hv₁ : v₁ = u₁ - q := rfl
  have hv₂ : v ∘ Sum.inr = u₂ := by
    funext p; simp [v, u, qh]
  have hquad : star q ⬝ᵥ (Critical.poissonKernel (Critical.collarScattering b e s ν ω *
      Critical.oldScattering b e X) *ᵥ q) = ((boundaryZ b e).im⁻¹ : ℝ) *
        (star v₁ ⬝ᵥ (Yo *ᵥ v₁) + (ν : ℂ) * (star u₁ ⬝ᵥ u₁ + star u₂ ⬝ᵥ u₂)) := by
    rw [hK, smul_mulVec, dotProduct_smul, add_mulVec, dotProduct_add, dotProduct_sandwich,
      dotProduct_sandwich, hM1, hM2, hImK, smul_eq_mul]
    simp only [star_neg, neg_dotProduct, dotProduct_neg, mulVec_neg, neg_neg, Yo]
  have hHsplit : H = collarMatrix (e + s) (rePart X) ω +
      Complex.I • (topLift Yo + (ν : ℂ) • 1) := by
    simp only [H, heightMatrix, Yo]
    rw [collarMatrix_eq_herm_add]
    module
  have hres : -(star y ⬝ᵥ (H⁻¹ *ᵥ y)).im =
      (star v₁ ⬝ᵥ (Yo *ᵥ v₁)).re + ν * (star v ⬝ᵥ v).re := by
    have key : star (Hᴴ *ᵥ v) ⬝ᵥ (H⁻¹ *ᵥ (Hᴴ *ᵥ v)) = star v ⬝ᵥ (Hᴴ *ᵥ v) := by
      rw [star_mulVec, conjTranspose_conjTranspose, ← dotProduct_mulVec, mulVec_mulVec,
        mul_nonsing_inv _ hH, one_mulVec]
    rw [← hv, key, dotProduct_conjTranspose_mulVec]
    simp only [Complex.star_def, Complex.conj_im, neg_neg]
    rw [hHsplit, add_mulVec, dotProduct_add, smul_mulVec, dotProduct_smul, smul_eq_mul,
      Complex.add_im, BlockBand.Wegner.im_star_dotProduct_mulVec_hermitian
        (collarMatrix_isHermitian (e + s) hA hG (rePart_isHermitian X)), zero_add,
      Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add, add_mulVec,
      dotProduct_add, Complex.add_re, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    congr 1
    rw [topLift, fromBlocks_mulVec]
    simp only [zero_mulVec, add_zero, dotProduct, Fintype.sum_sum_type,
      Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, mul_zero, Finset.sum_const_zero, v₁]
    rfl
  -- real parts
  have ha : 0 ≤ (star v₁ ⬝ᵥ (Yo *ᵥ v₁)).re :=
    (Complex.nonneg_iff.1 (hY.dotProduct_mulVec_nonneg v₁)).1
  have hnv : (star v ⬝ᵥ v).re = ∑ x, ‖v₁ x‖ ^ 2 + ∑ p, ‖u₂ p‖ ^ 2 := by
    rw [BlockBand.Wegner.re_star_dotProduct_self, Fintype.sum_sum_type, ← hv₂]
    rfl
  have hnu₁ : (star u₁ ⬝ᵥ u₁).re = ∑ x, ‖u₁ x‖ ^ 2 := BlockBand.Wegner.re_star_dotProduct_self _
  have hnu₂ : (star u₂ ⬝ᵥ u₂).re = ∑ p, ‖u₂ p‖ ^ 2 := BlockBand.Wegner.re_star_dotProduct_self _
  have hle : ∑ x, ‖u₁ x‖ ^ 2 ≤ 2 * ∑ x, ‖v₁ x‖ ^ 2 + 2 * ∑ x, ‖q x‖ ^ 2 := by
    have := sum_norm_sq_add_le v₁ q
    simpa [hv₁] using this
  rw [hquad, hres, hnv]
  have hre : (((boundaryZ b e).im⁻¹ : ℝ) * (star v₁ ⬝ᵥ (Yo *ᵥ v₁) + (ν : ℂ) *
      (star u₁ ⬝ᵥ u₁ + star u₂ ⬝ᵥ u₂)) : ℂ).re = (boundaryZ b e).im⁻¹ *
        ((star v₁ ⬝ᵥ (Yo *ᵥ v₁)).re + ν * (∑ x, ‖u₁ x‖ ^ 2 + ∑ p, ‖u₂ p‖ ^ 2)) := by
    rw [← hnu₁, ← hnu₂]
    simp [Complex.mul_re]
  rw [hre]
  have hηi : 0 ≤ (boundaryZ b e).im⁻¹ := inv_nonneg.2 hη.le
  have hs2 : 0 ≤ ∑ p, ‖u₂ p‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  refine mul_le_mul_of_nonneg_left ?_ hηi
  nlinarith [mul_le_mul_of_nonneg_left hle hν.le]

/-- `𝒫(Ur)` is positive semidefinite almost surely at height `ν > 0` (`Y ⪰ 0`). -/
theorem ae_collarPoisson_posSemidef_height {b : ℝ} (e s : ℝ) {ν : ℝ} (hν : 0 < ν)
    (hη : 0 < (boundaryZ b e).im) {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hY : (-Critical.imPart X).PosSemidef) :
    ∀ᵐ ω ∂Critical.collarLaw W b, (Critical.poissonKernel
      (Critical.collarScattering b e s ν ω * Critical.oldScattering b e X)).PosSemidef := by
  filter_upwards [Density.ae_collarMatrix_isHermitian b e (rePart_isHermitian X) (W := W)]
    with ω hω
  rw [collar_poissonKernel_eq_height b e s hν hη hω.2.1 hω.2.2 hY]
  refine PosSemidef.smul ?_ (Complex.zero_le_real.2 (inv_nonneg.2 hη.le))
  exact (hY.mul_mul_conjTranspose_same _).add
    ((imPart_collarReaction_posSemidef b e s hν.le hω.2.1 hω.2.2
      (isUnit_det_middleBlockH e s hν hω.2.2)).mul_mul_conjTranspose_same _)

/-- **Universal quadratic-form bound at height `ν > 0`** (`Y = -Im X ⪰ 0`, every real shift):
`E_collar Re q*𝒫(Ur)q ≤ η⁻¹ (2 C_{b,w} √W + 2ν) ‖q‖²`, `w = conj(z_b + e + s - iν)`. The
dilation is applied at `ε = ν` (no limit). -/
theorem lintegral_collarKernel_quad_le_height {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hW : 0 < W) (e s : ℝ) {ν : ℝ} (hν : 0 < ν) (hη : 0 < (boundaryZ b e).im)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hY : (-Critical.imPart X).PosSemidef)
    (q : Fin 2 × Fin W → ℂ) :
    ∫⁻ ω, ENNReal.ofReal (star q ⬝ᵥ (Critical.poissonKernel (Critical.collarScattering b e s ν ω *
        Critical.oldScattering b e X) *ᵥ q)).re ∂Critical.collarLaw W b ≤
      ENNReal.ofReal ((boundaryZ b e).im⁻¹ * (2 * collarRowConst b
        (star (boundaryZ b e + Critical.collarShift e s ν)) * Real.sqrt W + 2 * ν) *
          ∑ x, ‖q x‖ ^ 2) := by
  set η := (boundaryZ b e).im
  set e' := e + s
  set w := star (boundaryZ b e + Critical.collarShift e s ν)
  set rv := collarRowVec w q
  set Sq := ∑ x, ‖q x‖ ^ 2
  have hSq : 0 ≤ Sq := Finset.sum_nonneg fun _ _ => by positivity
  set B := collarRowConst b w * Real.sqrt W * Sq
  set Y := -Critical.imPart X
  set Xh := rePart X
  set N : Critical.CollarSample W → ℝ := fun ω =>
    -(star (rv ω) ⬝ᵥ ((heightMatrix e s ν X ω)⁻¹ *ᵥ rv ω)).im
  set G : ℝ × Critical.CollarSample W → ℝ≥0∞ := fun p =>
    ENNReal.ofReal ((star (rv p.2) ⬝ᵥ ((collarMatrix e' (Xh + (p.1 : ℂ) • Y) p.2 -
      ((ν : ℂ) * Complex.I) • 1)⁻¹ *ᵥ rv p.2)).im)
  have hrv : Measurable rv := Density.measurable_collarRowVec w q
  have hG : Measurable G := by
    have hM : Measurable fun p : ℝ × Critical.CollarSample W =>
        collarMatrix e' (Xh + (p.1 : ℂ) • Y) p.2 - ((ν : ℂ) * Complex.I) • 1 := by
      have heq : (fun p : ℝ × Critical.CollarSample W =>
          collarMatrix e' (Xh + (p.1 : ℂ) • Y) p.2 - ((ν : ℂ) * Complex.I) • 1) =
          fun p => collarMatrix e' Xh p.2 - (p.1 : ℂ) • topLift Y - ((ν : ℂ) * Complex.I) • 1 := by
        funext p; rw [collarMatrix_add_right, topLift_smul]
      rw [heq]
      refine Measurable.of_eval_matrix _ fun i j => ?_
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      refine (((Matrix.measurable_apply).comp ((Density.measurable_collarMatrix e' Xh).comp
        measurable_snd)).sub ?_).sub measurable_const
      exact (Complex.continuous_ofReal.measurable.comp measurable_fst).mul measurable_const
    exact Density.measurable_ofReal_im_form hM (hrv.comp measurable_snd)
  have hHerm := Density.ae_collarMatrix_isHermitian b e' (rePart_isHermitian X) (W := W)
  -- pointwise bound
  have h1 : ∀ᵐ ω ∂Critical.collarLaw W b, ENNReal.ofReal (star q ⬝ᵥ (Critical.poissonKernel
      (Critical.collarScattering b e s ν ω * Critical.oldScattering b e X) *ᵥ q)).re ≤
      ENNReal.ofReal η⁻¹ * (2 * ENNReal.ofReal (N ω) + ENNReal.ofReal (2 * ν * Sq)) := by
    filter_upwards [hHerm] with ω hω
    have hb := collar_poissonKernel_quad_le_height b e s hν hη hω.2.1 hω.2.2 hY q
    have hN : 0 ≤ N ω := by
      obtain ⟨hint, heq⟩ := neg_im_collarResolvent_eq_integral e' hω.2.1 hω.2.2 hY hν (rv ω)
      simp only [N, heightMatrix]
      rw [← heq]
      refine integral_nonneg fun t => ?_
      exact Density.im_dotProduct_inv_mulVec_nonneg'
        (collarMatrix_isHermitian e' hω.2.1 hω.2.2 (dilatedOld_isHermitian X t)) (by simp [hν]) _
    refine (ENNReal.ofReal_le_ofReal hb).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (inv_nonneg.2 hη.le), ENNReal.ofReal_add (by positivity)
      (by positivity), ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  -- the `N` integral
  have h4 : ∫⁻ ω, ENNReal.ofReal (N ω) ∂Critical.collarLaw W b ≤ ENNReal.ofReal B := by
    have hpt : ∀ᵐ ω ∂Critical.collarLaw W b, ENNReal.ofReal (N ω) =
        ∫⁻ t, G (t, ω) ∂stdCauchy := by
      filter_upwards [hHerm] with ω hω
      obtain ⟨hint, heq⟩ := neg_im_collarResolvent_eq_integral e' hω.2.1 hω.2.2 hY hν (rv ω)
      simp only [N, G, heightMatrix]
      rw [← heq, ofReal_integral_eq_lintegral_ofReal hint]
      refine Filter.Eventually.of_forall fun t => ?_
      exact Density.im_dotProduct_inv_mulVec_nonneg'
        (collarMatrix_isHermitian e' hω.2.1 hω.2.2 (dilatedOld_isHermitian X t)) (by simp [hν]) _
    have hsw : AEMeasurable (Function.uncurry fun (ω : Critical.CollarSample W) (t : ℝ) =>
        G (t, ω)) ((Critical.collarLaw W b).prod stdCauchy) := (hG.comp measurable_swap).aemeasurable
    rw [lintegral_congr_ae hpt, lintegral_lintegral_swap hsw]
    calc ∫⁻ t, ∫⁻ ω, G (t, ω) ∂Critical.collarLaw W b ∂stdCauchy
        ≤ ∫⁻ _ : ℝ, ENNReal.ofReal B ∂stdCauchy := by
          refine lintegral_mono fun t => ?_
          exact Density.lintegral_im_resolvent_collarRow_le_sqrt hb0 hb hW e'
            (dilatedOld_isHermitian X t) (by simp [hν]) w q
      _ = ENNReal.ofReal B := by simp
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg (Density.collarRowConst_nonneg hb0.le _)
    (Real.sqrt_nonneg _)) hSq
  calc ∫⁻ ω, ENNReal.ofReal (star q ⬝ᵥ (Critical.poissonKernel (Critical.collarScattering b e s ν ω *
        Critical.oldScattering b e X) *ᵥ q)).re ∂Critical.collarLaw W b
      ≤ ∫⁻ ω, ENNReal.ofReal η⁻¹ * (2 * ENNReal.ofReal (N ω) + ENNReal.ofReal (2 * ν * Sq))
          ∂Critical.collarLaw W b := lintegral_mono_ae h1
    _ = ENNReal.ofReal η⁻¹ * (2 * ∫⁻ ω, ENNReal.ofReal (N ω) ∂Critical.collarLaw W b +
          ENNReal.ofReal (2 * ν * Sq)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_right _ measurable_const,
          lintegral_const_mul' _ _ (by simp), lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal η⁻¹ * (2 * ENNReal.ofReal B + ENNReal.ofReal (2 * ν * Sq)) := by
        gcongr
    _ = _ := by
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (inv_nonneg.2 hη.le)]
        congr 1
        simp only [B, η]
        ring

/-- **Universal collar kernel bound at height `ν > 0`** (`Y = -Im X ⪰ 0`, every real shift `s`):
the entries of `𝒫(Ur)` are integrable and `E_collar 𝒫(Ur) ⪯ η⁻¹(2 C_{b,w} √W + 2ν) I`. -/
theorem collarKernel_universal_height {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hW : 0 < W)
    (e s : ℝ) {ν : ℝ} (hν : 0 < ν) (hη : 0 < (boundaryZ b e).im)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hY : (-Critical.imPart X).PosSemidef) :
    Critical.CollarKernelIntegrable b e s ν 1 X ∧
      ((((boundaryZ b e).im⁻¹ * (2 * collarRowConst b
        (star (boundaryZ b e + Critical.collarShift e s ν)) * Real.sqrt W + 2 * ν) : ℝ) : ℂ) •
        (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
          Critical.expectedCollarKernel b e s ν 1 X).PosSemidef := by
  have hone : ∀ V : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, ((1 : ℝ) : ℂ) • V = V := by
    intro V; simp
  have hK : 0 ≤ (boundaryZ b e).im⁻¹ * (2 * collarRowConst b
      (star (boundaryZ b e + Critical.collarShift e s ν)) * Real.sqrt W + 2 * ν) :=
    mul_nonneg (inv_nonneg.2 hη.le) (add_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (Density.collarRowConst_nonneg hb0.le _)) (Real.sqrt_nonneg _)) (by linarith))
  have h := integrable_and_posSemidef_of_quad_le (μ := Critical.collarLaw W b)
    (P := fun ω => Critical.poissonKernel
      (Critical.collarScattering b e s ν ω * Critical.oldScattering b e X))
    (by simpa [hone] using measurable_collarPoisson b e s ν 1 X (W := W))
    (ae_collarPoisson_posSemidef_height e s hν hη hY) hK fun q =>
      lintegral_collarKernel_quad_le_height hb0 hb hW e s hν hη hY q
  refine ⟨fun x y => by simpa [hone] using h.1 x y, ?_⟩
  simpa [Critical.expectedCollarKernel, hone] using h.2

/-- **Universal clauses of the collar kernel bound, uniform in height and shift.** For
`b ∈ (0,1/2)`, `κ > 0`, a shift range `s₀` and a height range `ν₀` there is one constant `C ≥ 0`
such that, uniformly in `W ≥ 1`, `e ∈ bulkInterval κ`, `|s| ≤ s₀`, `0 ≤ ν ≤ ν₀` and every old
response `X` (no norm bound):
* `Y = -Im X ≻ 0`: entries of `𝒫(Ur)` integrable, `E_collar 𝒫(Ur) ⪯ C √W I`;
* `Y ⪰ 0`, every radial regulator `0 ≤ t < 1`: entries of `𝒫(tUr)` integrable,
  `E_collar 𝒫(tUr) ⪯ C √W I`.
These are the `C√W` clauses of `CollarKernelBounds`. -/
theorem collarKernel_universal_all {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {κ : ℝ}
    (hκ : 0 < κ) (s₀ ν₀ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (W : ℕ), 0 < W → ∀ e ∈ bulkInterval κ, ∀ s ∈ Set.Icc (-s₀) s₀,
      ∀ ν ∈ Set.Icc 0 ν₀, ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ,
        ((-Critical.imPart X).PosDef → Critical.CollarKernelIntegrable b e s ν 1 X ∧
          (((C * Real.sqrt W : ℝ) : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
            Critical.expectedCollarKernel b e s ν 1 X).PosSemidef) ∧
        ((-Critical.imPart X).PosSemidef → ∀ t : ℝ, 0 ≤ t → t < 1 →
          Critical.CollarKernelIntegrable b e s ν t X ∧
          (((C * Real.sqrt W : ℝ) : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
            Critical.expectedCollarKernel b e s ν t X).PosSemidef) := by
  set ηmin := (1 - b) * Real.sqrt (4 - (2 - κ) ^ 2) / 2
  set w' : ℂ := ((5 + |s₀| + |ν₀| : ℝ) : ℂ)
  set Cb := collarRowConst b w'
  have hCb : 0 ≤ Cb := Density.collarRowConst_nonneg hb0.le _
  have hηmin0 : 0 ≤ ηmin := by
    have : 0 ≤ 1 - b := by linarith
    positivity
  refine ⟨ηmin⁻¹ * (2 * Cb + 2 * |ν₀|), mul_nonneg (inv_nonneg.2 hηmin0) (by positivity), ?_⟩
  intro W hW e he s hs ν hνr X
  obtain ⟨hηmin, hηe⟩ := BlockBand.Layers.boundaryZ_im_pos_of_mem_bulkInterval (b := b)
    (by linarith) hκ he
  have hη : 0 < (boundaryZ b e).im := hηmin.trans_le hηe
  have he2 : |e| ≤ 2 := (BlockBand.Layers.abs_lt_two_of_mem_bulkInterval hκ he).le
  have hz3 := BlockBand.Layers.norm_boundaryZ_le hb0.le (by linarith) he2
  have hs' : |s| ≤ |s₀| :=
    abs_le.2 ⟨by linarith [hs.1, le_abs_self s₀], by linarith [hs.2, le_abs_self s₀]⟩
  have hν' : ν ≤ |ν₀| := hνr.2.trans (le_abs_self _)
  have hw'n : ‖w'‖ = 5 + |s₀| + |ν₀| := by
    simp only [w']
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hηi : (boundaryZ b e).im⁻¹ ≤ ηmin⁻¹ := inv_anti₀ hηmin hηe
  have hsq1 : 1 ≤ Real.sqrt W := by
    rw [Real.one_le_sqrt]; exact_mod_cast hW
  have hsq0 : 0 ≤ Real.sqrt W := Real.sqrt_nonneg _
  have hes : ‖((e + s : ℝ) : ℂ)‖ ≤ 2 + |s₀| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (abs_add_le e s).trans (by linarith)
  rcases hνr.1.eq_or_lt with hν0 | hνpos
  · -- zero height
    subst hν0
    have hw : ‖rowCoeff b e s‖ ≤ ‖w'‖ := by
      rw [rowCoeff, norm_star, hw'n]
      calc ‖boundaryZ b e + ((e + s : ℝ) : ℂ)‖ ≤ ‖boundaryZ b e‖ + ‖((e + s : ℝ) : ℂ)‖ :=
            norm_add_le _ _
        _ ≤ 3 + (2 + |s₀|) := add_le_add hz3 hes
        _ ≤ _ := by linarith [abs_nonneg ν₀]
    have hKK : (boundaryZ b e).im⁻¹ * collarRowConst b (rowCoeff b e s) * Real.sqrt W ≤
        ηmin⁻¹ * (2 * Cb + 2 * |ν₀|) * Real.sqrt W := by
      have h1 : collarRowConst b (rowCoeff b e s) ≤ 2 * Cb + 2 * |ν₀| := by
        have := Density.collarRowConst_mono b hw
        linarith [abs_nonneg ν₀]
      have h2 : 0 ≤ collarRowConst b (rowCoeff b e s) := Density.collarRowConst_nonneg hb0.le _
      have h3 := mul_le_mul hηi h1 h2 (inv_nonneg.2 hηmin0)
      exact mul_le_mul_of_nonneg_right h3 hsq0
    refine ⟨fun hY => ?_, fun hY t ht0 ht1 => ?_⟩
    · obtain ⟨h1, h2⟩ := collarKernel_universal_strict hb0 hb hW e s hη hY
      exact ⟨h1, posSemidef_smul_one_sub_mono h2 hKK⟩
    · obtain ⟨h1, h2⟩ := collarKernel_universal_radial hb0 hb hW e s hη hY ht0 ht1
      exact ⟨h1, posSemidef_smul_one_sub_mono h2 hKK⟩
  · -- positive height
    set wν := star (boundaryZ b e + Critical.collarShift e s ν)
    have hw : ‖wν‖ ≤ ‖w'‖ := by
      rw [norm_star, hw'n]
      have hsh : ‖Critical.collarShift e s ν‖ ≤ 2 + |s₀| + ν := by
        rw [Critical.collarShift]
        calc ‖((e + s : ℝ) : ℂ) - (ν : ℂ) * Complex.I‖ ≤ ‖((e + s : ℝ) : ℂ)‖ +
              ‖(ν : ℂ) * Complex.I‖ := norm_sub_le _ _
          _ ≤ 2 + |s₀| + ν := by
              simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg hνpos.le]
              linarith [abs_add_le e s]
      calc ‖boundaryZ b e + Critical.collarShift e s ν‖ ≤ ‖boundaryZ b e‖ +
            ‖Critical.collarShift e s ν‖ := norm_add_le _ _
        _ ≤ 3 + (2 + |s₀| + ν) := add_le_add hz3 hsh
        _ ≤ _ := by linarith
    have hKK : (boundaryZ b e).im⁻¹ * (2 * collarRowConst b wν * Real.sqrt W + 2 * ν) ≤
        ηmin⁻¹ * (2 * Cb + 2 * |ν₀|) * Real.sqrt W := by
      have h1 : 2 * collarRowConst b wν * Real.sqrt W + 2 * ν ≤
          (2 * Cb + 2 * |ν₀|) * Real.sqrt W := by
        have := Density.collarRowConst_mono b hw
        nlinarith
      have h2 : 0 ≤ 2 * collarRowConst b wν * Real.sqrt W + 2 * ν := by
        have := Density.collarRowConst_nonneg hb0.le wν
        positivity
      have h3 := mul_le_mul hηi h1 h2 (inv_nonneg.2 hηmin0)
      linarith [h3]
    refine ⟨fun hY => ?_, fun hY t ht0 ht1 => ?_⟩
    · obtain ⟨h1, h2⟩ := collarKernel_universal_height hb0 hb hW e s hνpos hη hY.posSemidef
      exact ⟨h1, posSemidef_smul_one_sub_mono h2 hKK⟩
    · have hY' := posDef_neg_imPart_radialOld b e hη hY ht0 ht1
      obtain ⟨h1, h2⟩ := collarKernel_universal_height hb0 hb hW e s hνpos hη hY'.posSemidef
      exact ⟨(collarKernelIntegrable_radial b e s ν hη hY ht0 ht1).2 h1,
        by rw [expectedCollarKernel_radial b e s ν hη hY ht0 ht1];
           exact posSemidef_smul_one_sub_mono h2 hKK⟩

end Collar

end BlockBand.Critical.Collar.Kernel
