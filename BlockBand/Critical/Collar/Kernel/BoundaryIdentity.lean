module

public import BlockBand.Internal.Contracts.Critical
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus

/-!
# The weighted boundary identity: the exact boundary-kernel identity

*Results.*
* `poissonKernel_eq_sandwich`: `𝒫(V) = (I-V)⁻¹(I - VV*)(I-V*)⁻¹` whenever `I - V` is invertible;
  `poissonKernel_posSemidef`: `𝒫(V) ⪰ 0` when moreover `VV* ⪯ I`.
* `cayley_mul_conjTranspose`: `UU* = I` for Hermitian `K_c` (Cayley transform).
* `one_sub_scattering_mul_conjTranspose`: `I - rr* = 4η Z⁻¹YZ⁻*` (no positivity needed).
* `weightedBoundaryIdentity`: both forms of the weighted boundary identity,
  `𝒫(Ur) = η⁻¹(I - ZR_c)Y(I - R_c*Z*) = η⁻¹(K_c - iη)R_cYR_c*(K_c + iη)`, with the
  factorization `I - Ur = 2iη(K_c + iη)⁻¹(K_c + H_o + iY)Z⁻¹` (`one_sub_cayley_mul_scattering`).
  Hypotheses: `K_c, H_o, Y` Hermitian, `η > 0`, `Z` and `K_c + H_o + iY` invertible (both hold
  when `Y ≻ 0`, see `isUnit_det_herm_add_I_smul_posDef`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Kernel

open Matrix
open BlockBand.Internal.Contracts
open scoped ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The scalar `2iη`. -/
abbrev twoIEta (η : ℝ) : ℂ := (2 * (η : ℂ) * Complex.I)

/-- `conj(2iη) = -2iη` for real `η`. -/
theorem star_twoIEta (η : ℝ) : star (twoIEta η) = -twoIEta η := by
  simp only [twoIEta, star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_I,
    map_ofNat]
  ring

/-- `H + iY` is invertible for Hermitian `H` and positive definite `Y` (finite index type):
`Im⟨v,(H+iY)v⟩ = ⟨v,Yv⟩ > 0` for `v ≠ 0`. -/
theorem isUnit_det_herm_add_I_smul_posDef {H Y : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (hY : Y.PosDef) : IsUnit (H + Complex.I • Y).det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  intro x y hxy
  rw [← sub_eq_zero]
  set v := x - y
  have hv : (H + Complex.I • Y) *ᵥ v = 0 := by
    simp only [v, mulVec_sub, hxy, sub_self]
  by_contra hne
  have hpos := hY.dotProduct_mulVec_pos hne
  have hq : star v ⬝ᵥ ((H + Complex.I • Y) *ᵥ v) = 0 := by rw [hv, dotProduct_zero]
  rw [add_mulVec, dotProduct_add, smul_mulVec, dotProduct_smul, smul_eq_mul] at hq
  have hHr : (star v ⬝ᵥ (H *ᵥ v)).im = 0 := by
    exact Complex.conj_eq_iff_im.mp (hH.star_dotProduct_mulVec_comm v v)
  have hYr := (RCLike.pos_iff.mp hpos)
  have him := congrArg Complex.im hq
  simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    zero_add, Complex.zero_im, hHr] at him
  simp only [RCLike.re_to_complex] at hYr
  linarith [hYr.1]

theorem isUnit_det_herm_add_I_smul {K : Matrix ι ι ℂ} (hK : K.IsHermitian) {η : ℝ}
    (hη : 0 < η) : IsUnit (K + ((η : ℂ) * Complex.I) • (1 : Matrix ι ι ℂ)).det := by
  have hpd : ((η : ℂ) • (1 : Matrix ι ι ℂ)).PosDef :=
    Matrix.PosDef.one.smul (by exact_mod_cast hη)
  have := isUnit_det_herm_add_I_smul_posDef hK hpd
  rwa [smul_smul, mul_comm] at this

/-- **Cayley transform is unitary**: `U = I - 2iη(K + iη)⁻¹` satisfies `UU* = I` for Hermitian
`K` and `η > 0` (the `U` of the collar). -/
theorem cayley_mul_conjTranspose {K : Matrix ι ι ℂ} (hK : K.IsHermitian) {η : ℝ} (hη : 0 < η) :
    (1 - twoIEta η • (K + ((η : ℂ) * Complex.I) • 1)⁻¹) *
      (1 - twoIEta η • (K + ((η : ℂ) * Complex.I) • 1)⁻¹)ᴴ = 1 := by
  set P := K + ((η : ℂ) * Complex.I) • (1 : Matrix ι ι ℂ)
  have hP := isUnit_det_herm_add_I_smul hK hη
  set Q := P⁻¹
  have hPP : Pᴴ - P = (-twoIEta η) • (1 : Matrix ι ι ℂ) := by
    simp only [P, conjTranspose_add, conjTranspose_smul, conjTranspose_one, hK.eq, star_mul',
      Complex.star_def, Complex.conj_ofReal, Complex.conj_I, twoIEta]
    rw [add_sub_add_left_eq_sub, ← sub_smul]
    congr 1; ring
  have hPhu : IsUnit Pᴴ.det := by rw [det_conjTranspose]; exact hP.star
  have hQh : Qᴴ = (Pᴴ)⁻¹ := by rw [conjTranspose_nonsing_inv]
  have hdiff : Q - Qᴴ = (-twoIEta η) • (Q * Qᴴ) := by
    have e1 : Q * P = 1 := nonsing_inv_mul _ hP
    have e2 : Pᴴ * Qᴴ = 1 := by rw [hQh]; exact mul_nonsing_inv _ hPhu
    calc Q - Qᴴ = Q * (Pᴴ * Qᴴ) - (Q * P) * Qᴴ := by rw [e1, e2, Matrix.mul_one, Matrix.one_mul]
      _ = Q * (Pᴴ - P) * Qᴴ := by
        rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = _ := by rw [hPP, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  rw [conjTranspose_sub, conjTranspose_one, conjTranspose_smul, star_twoIEta]
  have hexp : (1 - twoIEta η • Q) * (1 - (-twoIEta η) • Qᴴ) =
      1 - twoIEta η • (Q - Qᴴ) - (twoIEta η * twoIEta η) • (Q * Qᴴ) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul]
    module
  rw [hexp, hdiff, smul_smul, sub_sub, ← add_smul]
  have : twoIEta η * -twoIEta η + twoIEta η * twoIEta η = 0 := by ring
  rw [this, zero_smul, sub_zero]

/-- **Scattering defect**: for invertible `Z` with `Z - Z* = 2i(ηI + Y)`, `r = I - 2iηZ⁻¹`
satisfies `I - rr* = 4η Z⁻¹ Y Z⁻*` (no positivity hypothesis; with `Y ⪰ 0` it shows `r` is a
contraction). -/
theorem one_sub_scattering_mul_conjTranspose {Z Y : Matrix ι ι ℂ} {η : ℝ}
    (hZ : IsUnit Z.det)
    (hZZ : Z - Zᴴ = (2 * Complex.I) • ((η : ℂ) • (1 : Matrix ι ι ℂ) + Y)) :
    (1 - twoIEta η • Z⁻¹) * (1 - twoIEta η • Z⁻¹)ᴴ =
      1 - ((4 * η : ℝ) : ℂ) • (Z⁻¹ * Y * (Z⁻¹)ᴴ) := by
  have hZh : IsUnit Zᴴ.det := by rw [det_conjTranspose]; exact hZ.star
  have e1 : Z⁻¹ * Z = 1 := nonsing_inv_mul _ hZ
  have e2 : Zᴴ * (Z⁻¹)ᴴ = 1 := by rw [conjTranspose_nonsing_inv]; exact mul_nonsing_inv _ hZh
  have hdiff : Z⁻¹ - (Z⁻¹)ᴴ = Z⁻¹ * (Zᴴ - Z) * (Z⁻¹)ᴴ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, e2, Matrix.mul_one, e1,
      Matrix.one_mul]
  have hZZ' : Zᴴ - Z = (-(2 * Complex.I)) • ((η : ℂ) • (1 : Matrix ι ι ℂ) + Y) := by
    rw [neg_smul, ← hZZ, neg_sub]
  rw [conjTranspose_sub, conjTranspose_one, conjTranspose_smul, star_twoIEta]
  have hexp : (1 - twoIEta η • Z⁻¹) * (1 - (-twoIEta η) • (Z⁻¹)ᴴ) =
      1 - twoIEta η • (Z⁻¹ - (Z⁻¹)ᴴ) - (twoIEta η * twoIEta η) • (Z⁻¹ * (Z⁻¹)ᴴ) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul]
    module
  rw [hexp, hdiff, hZZ']
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one]
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  match_scalars
  all_goals first
    | (simp only [twoIEta]; done)
    | (simp only [twoIEta]; ring_nf; done)
    | (simp only [twoIEta]; ring_nf; simp only [hI]; ring_nf)

/-- `𝒫(V) = (I-V)⁻¹(I - VV*)(I-V*)⁻¹` whenever `I - V` is invertible (no norm hypothesis). -/
theorem poissonKernel_eq_sandwich (V : Matrix ι ι ℂ) (hV : IsUnit (1 - V).det) :
    Critical.poissonKernel V = (1 - V)⁻¹ * (1 - V * Vᴴ) * (1 - Vᴴ)⁻¹ := by
  have hVh : IsUnit (1 - Vᴴ).det := by
    rw [show (1 : Matrix ι ι ℂ) - Vᴴ = (1 - V)ᴴ by simp, det_conjTranspose]
    exact hV.star
  have h1 : (1 - V)⁻¹ * (1 - V) = 1 := nonsing_inv_mul _ hV
  have h2 : (1 - Vᴴ) * (1 - Vᴴ)⁻¹ = 1 := mul_nonsing_inv _ hVh
  have hsplit : (1 : Matrix ι ι ℂ) - V * Vᴴ =
      (1 - V) + (1 - Vᴴ) - (1 - V) * (1 - Vᴴ) := by noncomm_ring
  have hexp : (1 - V)⁻¹ * ((1 - V) + (1 - Vᴴ) - (1 - V) * (1 - Vᴴ)) * (1 - Vᴴ)⁻¹ =
      ((1 - V)⁻¹ * (1 - V)) * (1 - Vᴴ)⁻¹ + (1 - V)⁻¹ * ((1 - Vᴴ) * (1 - Vᴴ)⁻¹) -
        ((1 - V)⁻¹ * (1 - V)) * ((1 - Vᴴ) * (1 - Vᴴ)⁻¹) := by noncomm_ring
  rw [hsplit, hexp, h1, h2, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]
  unfold Critical.poissonKernel
  abel

/-- `𝒫(V) ⪰ 0` when `I - V` is invertible and `I - VV* ⪰ 0` (Loewner order of complex
matrices). -/
theorem poissonKernel_posSemidef (V : Matrix ι ι ℂ) (hV : IsUnit (1 - V).det)
    (hc : (1 - V * Vᴴ).PosSemidef) : (Critical.poissonKernel V).PosSemidef := by
  rw [poissonKernel_eq_sandwich V hV]
  have : (1 - Vᴴ)⁻¹ = ((1 - V)⁻¹)ᴴ := by
    rw [conjTranspose_nonsing_inv, conjTranspose_sub, conjTranspose_one]
  rw [this]
  exact hc.mul_mul_conjTranspose_same _

section Weighted

variable {Kc Ho Y : Matrix ι ι ℂ} {η : ℝ}

/-- `Z = H_o + i(ηI + Y)`. -/
abbrev boundaryZMat (Ho Y : Matrix ι ι ℂ) (η : ℝ) : Matrix ι ι ℂ :=
  Ho + Complex.I • ((η : ℂ) • (1 : Matrix ι ι ℂ) + Y)

/-- `r = I - 2iηZ⁻¹`. -/
abbrev scatteringOf (Z : Matrix ι ι ℂ) (η : ℝ) : Matrix ι ι ℂ := 1 - twoIEta η • Z⁻¹

/-- `U = I - 2iη(K_c + iη)⁻¹`. -/
abbrev cayleyOf (Kc : Matrix ι ι ℂ) (η : ℝ) : Matrix ι ι ℂ :=
  1 - twoIEta η • (Kc + ((η : ℂ) * Complex.I) • 1)⁻¹

omit [Fintype ι] in
/-- `Z - Z* = 2i(ηI + Y)` for Hermitian `H_o, Y`. -/
theorem boundaryZMat_sub_conjTranspose (hHo : Ho.IsHermitian) (hY : Y.IsHermitian) :
    boundaryZMat Ho Y η - (boundaryZMat Ho Y η)ᴴ =
      (2 * Complex.I) • ((η : ℂ) • (1 : Matrix ι ι ℂ) + Y) := by
  simp only [boundaryZMat, conjTranspose_add, conjTranspose_smul, conjTranspose_one, hHo.eq,
    hY.eq, Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
  module

/-- The factorization `I - Ur = 2iη(K_c + iη)⁻¹(K_c + H_o + iY)Z⁻¹`, for Hermitian
`K_c`, `η > 0` and invertible `Z`. -/
theorem one_sub_cayley_mul_scattering (hKc : Kc.IsHermitian) (hη : 0 < η)
    (hZ : IsUnit (boundaryZMat Ho Y η).det) :
    1 - cayleyOf Kc η * scatteringOf (boundaryZMat Ho Y η) η =
      twoIEta η • ((Kc + ((η : ℂ) * Complex.I) • 1)⁻¹ * (Kc + Ho + Complex.I • Y) *
        (boundaryZMat Ho Y η)⁻¹) := by
  set P := Kc + ((η : ℂ) * Complex.I) • (1 : Matrix ι ι ℂ) with hPdef
  set Z := boundaryZMat Ho Y η with hZdef
  have hP := isUnit_det_herm_add_I_smul hKc hη
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

/-- **Weighted boundary identity**, first form. Deterministic finite
linear algebra (no measure; arbitrary finite index type `ι`, no norm bound). Hypotheses: `K_c, H_o, Y`
Hermitian, `η > 0`, `Z = H_o + i(ηI + Y)` and `K_c + H_o + iY` invertible (both hold when `Y ≻ 0`,
`isUnit_det_herm_add_I_smul_posDef`). Conclusion: `I - Ur` is invertible and
`𝒫(Ur) = η⁻¹ (I - ZR_c) Y (I - ZR_c)*`, `R_c = (K_c + H_o + iY)⁻¹`. -/
theorem weightedBoundaryIdentity (hKc : Kc.IsHermitian) (hHo : Ho.IsHermitian)
    (hY : Y.IsHermitian) (hη : 0 < η) (hZ : IsUnit (boundaryZMat Ho Y η).det)
    (hM : IsUnit (Kc + Ho + Complex.I • Y).det) :
    IsUnit (1 - cayleyOf Kc η * scatteringOf (boundaryZMat Ho Y η) η).det ∧
    Critical.poissonKernel (cayleyOf Kc η * scatteringOf (boundaryZMat Ho Y η) η) =
      ((η⁻¹ : ℝ) : ℂ) • ((1 - boundaryZMat Ho Y η * (Kc + Ho + Complex.I • Y)⁻¹) * Y *
        (1 - boundaryZMat Ho Y η * (Kc + Ho + Complex.I • Y)⁻¹)ᴴ) := by
  have hfac := one_sub_cayley_mul_scattering (Ho := Ho) (Y := Y) hKc hη hZ
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
  have hP := isUnit_det_herm_add_I_smul hKc hη
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
  have hU : U * Uᴴ = 1 := cayley_mul_conjTranspose hKc hη
  have hr : r * rᴴ = 1 - ((4 * η : ℝ) : ℂ) • (Z⁻¹ * Y * (Z⁻¹)ᴴ) :=
    one_sub_scattering_mul_conjTranspose hZ (boundaryZMat_sub_conjTranspose hHo hY)
  have hdefect : 1 - (U * r) * (U * r)ᴴ = ((4 * η : ℝ) : ℂ) • (U * Z⁻¹ * Y * (U * Z⁻¹)ᴴ) := by
    rw [conjTranspose_mul, show U * r * (rᴴ * Uᴴ) = U * (r * rᴴ) * Uᴴ by
      simp only [Matrix.mul_assoc], hr, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU,
      sub_sub_cancel, Matrix.mul_smul, Matrix.smul_mul, conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  have hTUZ : T * U * Z⁻¹ = a⁻¹ • (1 - Z * M⁻¹) := by
    have e1 : P * P⁻¹ = 1 := mul_nonsing_inv _ hP
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
  have hsplit : T * (((4 * η : ℝ) : ℂ) • (U * Z⁻¹ * Y * (U * Z⁻¹)ᴴ)) * Tᴴ =
      ((4 * η : ℝ) : ℂ) • ((T * U * Z⁻¹) * Y * (T * U * Z⁻¹)ᴴ) := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [hsplit, hTUZ, conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, smul_smul]
  congr 1
  rw [star_inv₀, hadef, star_twoIEta]
  simp only [twoIEta]
  have hη0 : (η : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hη.ne'
  field_simp
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  field_simp

/-- **Weighted boundary identity**, second form:
`𝒫(Ur) = η⁻¹ (K_c - iη) R_c Y R_c* (K_c + iη)`; same setting and hypotheses as
`weightedBoundaryIdentity`. -/
theorem weightedBoundaryIdentity' (hKc : Kc.IsHermitian) (hHo : Ho.IsHermitian)
    (hY : Y.IsHermitian) (hη : 0 < η) (hZ : IsUnit (boundaryZMat Ho Y η).det)
    (hM : IsUnit (Kc + Ho + Complex.I • Y).det) :
    Critical.poissonKernel (cayleyOf Kc η * scatteringOf (boundaryZMat Ho Y η) η) =
      ((η⁻¹ : ℝ) : ℂ) • ((Kc - ((η : ℂ) * Complex.I) • 1) * (Kc + Ho + Complex.I • Y)⁻¹ * Y *
        ((Kc + Ho + Complex.I • Y)⁻¹)ᴴ * (Kc + ((η : ℂ) * Complex.I) • 1)) := by
  rw [(weightedBoundaryIdentity hKc hHo hY hη hZ hM).2]
  set M := Kc + Ho + Complex.I • Y with hMdef
  have e : M * M⁻¹ = 1 := mul_nonsing_inv _ hM
  have hMZ : M - boundaryZMat Ho Y η = Kc - ((η : ℂ) * Complex.I) • 1 := by
    simp only [hMdef, boundaryZMat]
    module
  have h1 : 1 - boundaryZMat Ho Y η * M⁻¹ = (Kc - ((η : ℂ) * Complex.I) • 1) * M⁻¹ := by
    rw [← hMZ, Matrix.sub_mul, e]
  have hKh : (Kc - ((η : ℂ) * Complex.I) • (1 : Matrix ι ι ℂ))ᴴ =
      Kc + ((η : ℂ) * Complex.I) • 1 := by
    simp only [conjTranspose_sub, conjTranspose_smul, conjTranspose_one, hKc.eq, star_mul',
      Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
    module
  rw [h1, conjTranspose_mul, hKh]
  simp only [Matrix.mul_assoc]

end Weighted

end BlockBand.Critical.Collar.Kernel
