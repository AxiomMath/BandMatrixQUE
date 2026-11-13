module

public import BlockBand.Critical.MatrixClosing.Statement
public import BlockBand.Critical.Collar.Density.BlockRankOne

/-!
# The entire law: the Woodbury / closing identity

Deterministic matrix algebra for the complete closing determinant and the closed source matrix.

* `port_closing_identity`: for Hermitian `X`, `Im z ≠ 0` and any `D` with `D - z̄`, `D - X`
  invertible, `(D - X)⁻¹ - Re (z - X)⁻¹ = Im z · R {-i(2(1 - US)⁻¹ - 1)} R*`, `R = (z - X)⁻¹`,
  `U = 1 - 2i Im z (D - z̄)⁻¹`, `S = 1 - 2i Im z R` (the port form of the closing identity;
  `1 - US = 2i Im z (D - z̄)⁻¹(D - X)R`).
* `leadResolvent_sub_conjTranspose`: `R - R* = -2i Im z R R*`.
* `toBlocks11_inv_fromBlocks`, `toBlocks11_inv_fromBlocks22`, **`toBlocks11_inv_closedRing`**: the
  old-path block of the closed ring inverse is `h⁻¹ + h⁻¹Γ(D - X)⁻¹Γ*h⁻¹`, `D = A' - BG'⁻¹C`
  (all source-free Schur factors cancel); the open lead inverse (`pathLeadInverse`) is the same
  with `D = z_b`.
* **`source_closing_identity`** (abstract closed source matrix) and **`imPart_lead_source`**
  (`V*V = -Im K/η`).
* `collarEndSchur` (`D = K_c + ξ = A - e - B(G - e)⁻¹B*`, `collarEndSchur_eq`),
  **`closedSource_eq_closedSourceMatrix`**: with an old orthonormal frame `F`, `V = F B^{1/2}`, the
  closed source matrix is `closedSourceMatrix b e K (closingMatrix b e 0 X F ω)`;
  **`probeGram_lead_source`**: `probeGram b e K = V*V`.

Not here: identification of these blocks with the physical ring (`rngAssemble`, `ringPathSample`,
the collar sample), the a.s. invertibility of the blocks, and a measurable choice of the frame `F`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

open Matrix
open scoped ComplexConjugate

namespace BlockBand.Critical.EntireLaw

section Abstract

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem port_closing_identity {z : ℂ} (hη : z.im ≠ 0) {X D : Matrix ι ι ℂ} (hX : X.IsHermitian)
    (hR : IsUnit (z • (1 : Matrix ι ι ℂ) - X).det) (hT : IsUnit (D - conj z • (1 : Matrix ι ι ℂ)).det)
    (hY : IsUnit (D - X).det) :
    (D - X)⁻¹ - (2 : ℂ)⁻¹ • ((z • 1 - X)⁻¹ + ((z • 1 - X)⁻¹)ᴴ) =
      (z.im : ℂ) • ((z • 1 - X)⁻¹ * ((-Complex.I) • ((2 : ℂ) •
        (1 - (1 - (2 * (z.im : ℂ) * Complex.I) • (D - conj z • 1)⁻¹) *
          (1 - (2 * (z.im : ℂ) * Complex.I) • (z • 1 - X)⁻¹))⁻¹ - 1)) * ((z • 1 - X)⁻¹)ᴴ) := by
  set R := (z • (1 : Matrix ι ι ℂ) - X)⁻¹ with hRdef
  set T := (D - conj z • (1 : Matrix ι ι ℂ))⁻¹ with hTdef
  set Y := (D - X)⁻¹ with hYdef
  set c : ℂ := 2 * (z.im : ℂ) * Complex.I with hc
  have hc0 : c ≠ 0 := by
    simp only [hc]
    exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr hη)) Complex.I_ne_zero
  have hR1 : (z • (1 : Matrix ι ι ℂ) - X) * R = 1 := Matrix.mul_nonsing_inv _ hR
  have hR2 : R * (z • (1 : Matrix ι ι ℂ) - X) = 1 := Matrix.nonsing_inv_mul _ hR
  have hT1 : (D - conj z • (1 : Matrix ι ι ℂ)) * T = 1 := Matrix.mul_nonsing_inv _ hT
  have hT2 : T * (D - conj z • (1 : Matrix ι ι ℂ)) = 1 := Matrix.nonsing_inv_mul _ hT
  have hY1 : (D - X) * Y = 1 := Matrix.mul_nonsing_inv _ hY
  have hY2 : Y * (D - X) = 1 := Matrix.nonsing_inv_mul _ hY
  have hstar : (z • (1 : Matrix ι ι ℂ) - X)ᴴ = conj z • (1 : Matrix ι ι ℂ) - X := by
    rw [conjTranspose_sub, conjTranspose_smul, conjTranspose_one, hX.eq]
    rfl
  have hRs : (conj z • (1 : Matrix ι ι ℂ) - X) * Rᴴ = 1 := by
    have := congrArg conjTranspose hR2
    rwa [conjTranspose_mul, hstar, conjTranspose_one] at this
  have hzz : z - conj z = c := by
    rw [Complex.sub_conj, hc]; push_cast; ring
  -- split `D - X` through `D - z̄` and `z - X`
  have hsplit : D - X = (D - conj z • (1 : Matrix ι ι ℂ)) + (z • (1 : Matrix ι ι ℂ) - X) -
      c • (1 : Matrix ι ι ℂ) := by
    rw [← hzz, sub_smul]; abel
  have h2 : T * (D - X) * R = T + R - c • (T * R) := by
    rw [hsplit, Matrix.mul_sub, Matrix.mul_add, Matrix.sub_mul, Matrix.add_mul, hT2,
      Matrix.mul_assoc T (z • 1 - X) R, hR1]
    simp
    abel
  -- `1 - US = c T (D - X) R`
  have h3 : 1 - (1 - c • T) * (1 - c • R) = c • (T * (D - X) * R) := by
    rw [h2]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, smul_sub, smul_smul, smul_add]
    abel
  -- invert `1 - US`
  have h4 : (1 - (1 - c • T) * (1 - c • R))⁻¹ = c⁻¹ • ((z • 1 - X) * Y * (D - conj z • 1)) := by
    rw [h3]
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc0, one_smul]
    calc T * (D - X) * R * ((z • 1 - X) * Y * (D - conj z • 1))
        = T * (D - X) * (R * (z • 1 - X)) * Y * (D - conj z • 1) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hR2, Matrix.mul_one, Matrix.mul_assoc T, hY1, Matrix.mul_one, hT2]
  -- the conjugate factor
  have h5 : Y * (D - conj z • (1 : Matrix ι ι ℂ)) * Rᴴ = Rᴴ - Y := by
    have : D - conj z • (1 : Matrix ι ι ℂ) = (D - X) - (conj z • 1 - X) := by abel
    rw [this, Matrix.mul_sub, hY2, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc Y, hRs,
      Matrix.mul_one]
  have h6 : R - Rᴴ = -c • (R * Rᴴ) := by
    have e1 : R = R * ((conj z • (1 : Matrix ι ι ℂ) - X) * Rᴴ) := by rw [hRs, Matrix.mul_one]
    have e2 : Rᴴ = (R * (z • (1 : Matrix ι ι ℂ) - X)) * Rᴴ := by rw [hR2, Matrix.one_mul]
    have : R * ((conj z • (1 : Matrix ι ι ℂ) - X) * Rᴴ) - (R * (z • (1 : Matrix ι ι ℂ) - X)) * Rᴴ =
        (conj z - z) • (R * Rᴴ) := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
        Matrix.one_mul, sub_smul, Matrix.mul_assoc]
      abel
    rw [← hzz]
    calc R - Rᴴ = R * ((conj z • (1 : Matrix ι ι ℂ) - X) * Rᴴ) -
          (R * (z • (1 : Matrix ι ι ℂ) - X)) * Rᴴ := by rw [← e1, ← e2]
      _ = _ := by rw [this]; congr 1; ring
  rw [h4]
  have hRY : R * (c⁻¹ • ((z • 1 - X) * Y * (D - conj z • 1))) * Rᴴ = c⁻¹ • (Rᴴ - Y) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, ← h5]
    congr 1
    simp only [← Matrix.mul_assoc]
    rw [hR2, Matrix.one_mul]
  have hRR : R * Rᴴ = -c⁻¹ • (R - Rᴴ) := by
    have hη' : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hη
    rw [h6, smul_smul]; field_simp; simp
  have hexp : R * ((-Complex.I) • ((2 : ℂ) • (c⁻¹ • ((z • 1 - X) * Y * (D - conj z • 1))) - 1)) * Rᴴ
      = (-Complex.I) • ((2 : ℂ) • (c⁻¹ • (Rᴴ - Y)) - R * Rᴴ) := by
    rw [← hRY]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
  rw [hexp, hRR]
  simp only [smul_sub, smul_smul, smul_add]
  have hη' : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hη
  have hI : (z.im : ℂ) * (-Complex.I * (2 * c⁻¹)) = -1 := by
    rw [hc]; field_simp
  have hI2 : (z.im : ℂ) * (-Complex.I * -c⁻¹) = 2⁻¹ := by
    rw [hc]; field_simp
  rw [hI, hI2]
  module

/-- The resolvent identity `R - R* = -2i Im z · R R*`, `R = (z - X)⁻¹`, `X` Hermitian. -/
theorem leadResolvent_sub_conjTranspose {z : ℂ} {X : Matrix ι ι ℂ} (hX : X.IsHermitian)
    (hR : IsUnit (z • (1 : Matrix ι ι ℂ) - X).det) :
    (z • 1 - X)⁻¹ - ((z • 1 - X)⁻¹)ᴴ =
      -(2 * (z.im : ℂ) * Complex.I) • ((z • 1 - X)⁻¹ * ((z • 1 - X)⁻¹)ᴴ) := by
  set R := (z • (1 : Matrix ι ι ℂ) - X)⁻¹
  have hR2 : R * (z • (1 : Matrix ι ι ℂ) - X) = 1 := Matrix.nonsing_inv_mul _ hR
  have hstar : (z • (1 : Matrix ι ι ℂ) - X)ᴴ = conj z • (1 : Matrix ι ι ℂ) - X := by
    rw [conjTranspose_sub, conjTranspose_smul, conjTranspose_one, hX.eq]
    rfl
  have hRs : (conj z • (1 : Matrix ι ι ℂ) - X) * Rᴴ = 1 := by
    have := congrArg conjTranspose hR2
    rwa [conjTranspose_mul, hstar, conjTranspose_one] at this
  have e1 : R = R * ((conj z • (1 : Matrix ι ι ℂ) - X) * Rᴴ) := by rw [hRs, Matrix.mul_one]
  have e2 : Rᴴ = (R * (z • (1 : Matrix ι ι ℂ) - X)) * Rᴴ := by rw [hR2, Matrix.one_mul]
  have hzz : conj z - z = -(2 * (z.im : ℂ) * Complex.I) := by
    rw [← neg_sub, Complex.sub_conj]; push_cast; ring
  calc R - Rᴴ = R * ((conj z • (1 : Matrix ι ι ℂ) - X) * Rᴴ) -
        (R * (z • (1 : Matrix ι ι ℂ) - X)) * Rᴴ := by rw [← e1, ← e2]
    _ = (conj z - z) • (R * Rᴴ) := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
          Matrix.mul_one, Matrix.one_mul, sub_smul, Matrix.mul_assoc]
        abel
    _ = _ := by rw [hzz]

end Abstract

section Blocks

variable {P Q M J : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  [Fintype M] [DecidableEq M]

/-- Top-left block of a 2×2 block inverse (Schur complement of the bottom-right block). -/
theorem toBlocks11_inv_fromBlocks (h : Matrix P P ℂ) (Γ : Matrix P Q ℂ) (C : Matrix Q P ℂ)
    (D : Matrix Q Q ℂ) (hh : IsUnit h.det) (hS : IsUnit (D - C * h⁻¹ * Γ).det) :
    (fromBlocks h Γ C D)⁻¹.toBlocks₁₁ = h⁻¹ + h⁻¹ * Γ * (D - C * h⁻¹ * Γ)⁻¹ * C * h⁻¹ := by
  let := h.invertibleOfIsUnitDet hh
  let : Invertible (D - C * ⅟h * Γ) :=
    (D - C * ⅟h * Γ).invertibleOfIsUnitDet (by rwa [invOf_eq_nonsing_inv])
  let := fromBlocks₁₁Invertible h Γ C D
  rw [← invOf_eq_nonsing_inv (fromBlocks h Γ C D), invOf_fromBlocks₁₁_eq]
  simp only [toBlocks_fromBlocks₁₁, invOf_eq_nonsing_inv]

/-- Top-left block of a 2×2 block inverse, via the Schur complement of the bottom-right
block. -/
theorem toBlocks11_inv_fromBlocks22 (A : Matrix Q Q ℂ) (B : Matrix Q M ℂ) (C : Matrix M Q ℂ)
    (G : Matrix M M ℂ) (hG : IsUnit G.det) (hS : IsUnit (A - B * G⁻¹ * C).det) :
    (fromBlocks A B C G)⁻¹.toBlocks₁₁ = (A - B * G⁻¹ * C)⁻¹ := by
  let := G.invertibleOfIsUnitDet hG
  let : Invertible (A - B * ⅟G * C) :=
    (A - B * ⅟G * C).invertibleOfIsUnitDet (by rwa [invOf_eq_nonsing_inv])
  let := fromBlocks₂₂Invertible A B C G
  rw [← invOf_eq_nonsing_inv (fromBlocks A B C G), invOf_fromBlocks₂₂_eq]
  simp only [toBlocks_fromBlocks₁₁, invOf_eq_nonsing_inv]

/-- **Two-level Schur complement of the closed ring** (all source-free Schur factors
cancel): the old-path block of the inverse of
`[[h, (Γ 0)], [(Γ* 0)ᵀ, [[A', B], [C, G']]]]` (path `h`, port coupling `Γ` to the collar ends only,
collar ends `A'`, bonds `B, C`, middle `G'`) is `h⁻¹ + h⁻¹Γ(D - X)⁻¹Γ*h⁻¹`, `D = A' - BG'⁻¹C`,
`X = Γ*h⁻¹Γ`. -/
theorem toBlocks11_inv_closedRing (h : Matrix P P ℂ) (Γ : Matrix P Q ℂ) (A' : Matrix Q Q ℂ)
    (B : Matrix Q M ℂ) (C : Matrix M Q ℂ) (G' : Matrix M M ℂ) (hh : IsUnit h.det)
    (hG : IsUnit G'.det) (hY : IsUnit (A' - B * G'⁻¹ * C - Γᴴ * h⁻¹ * Γ).det) :
    (fromBlocks h (fromCols Γ (0 : Matrix P M ℂ)) (fromRows Γᴴ (0 : Matrix M P ℂ))
        (fromBlocks A' B C G'))⁻¹.toBlocks₁₁ =
      h⁻¹ + h⁻¹ * Γ * (A' - B * G'⁻¹ * C - Γᴴ * h⁻¹ * Γ)⁻¹ * Γᴴ * h⁻¹ := by
  set X := Γᴴ * h⁻¹ * Γ
  have e1 : fromRows Γᴴ (0 : Matrix M P ℂ) * h⁻¹ * fromCols Γ (0 : Matrix P M ℂ) =
      fromBlocks X 0 0 0 := by
    rw [fromRows_mul, fromRows_mul_fromCols]
    simp [X]
  have e2 : fromBlocks A' B C G' - fromBlocks X 0 0 0 = fromBlocks (A' - X) B C G' := by
    rw [sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]; simp [sub_eq_add_neg]
  have hS : IsUnit (A' - X - B * G'⁻¹ * C).det := by
    have : A' - X - B * G'⁻¹ * C = A' - B * G'⁻¹ * C - X := by abel
    rwa [this]
  have hN : IsUnit (fromBlocks A' B C G' - fromRows Γᴴ (0 : Matrix M P ℂ) * h⁻¹ *
      fromCols Γ (0 : Matrix P M ℂ)).det := by
    rw [e1, e2]
    let := G'.invertibleOfIsUnitDet hG
    rw [det_fromBlocks₂₂, invOf_eq_nonsing_inv]
    exact hG.mul hS
  rw [toBlocks11_inv_fromBlocks h _ _ _ hh hN, e1, e2]
  have e3 : ∀ N : Matrix (Q ⊕ M) (Q ⊕ M) ℂ, fromCols Γ (0 : Matrix P M ℂ) * N *
      fromRows Γᴴ (0 : Matrix M P ℂ) = Γ * N.toBlocks₁₁ * Γᴴ := by
    intro N
    rw [← fromBlocks_toBlocks N, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
    simp
  have e4 : h⁻¹ * fromCols Γ (0 : Matrix P M ℂ) * (fromBlocks (A' - X) B C G')⁻¹ *
      fromRows Γᴴ (0 : Matrix M P ℂ) * h⁻¹ =
      h⁻¹ * (fromCols Γ (0 : Matrix P M ℂ) * (fromBlocks (A' - X) B C G')⁻¹ *
        fromRows Γᴴ (0 : Matrix M P ℂ)) * h⁻¹ := by
    simp only [Matrix.mul_assoc]
  rw [e4, e3, toBlocks11_inv_fromBlocks22 _ _ _ _ hG hS]
  have : A' - X - B * G'⁻¹ * C = A' - B * G'⁻¹ * C - X := by abel
  rw [this]
  simp only [Matrix.mul_assoc]

/-- `z - X` is invertible for Hermitian `X` and `Im z > 0`. -/
theorem isUnit_det_smul_one_sub_of_isHermitian {ι : Type} [Fintype ι] [DecidableEq ι] {X : Matrix ι ι ℂ}
    (hX : X.IsHermitian) {z : ℂ} (hz : 0 < z.im) : IsUnit (z • (1 : Matrix ι ι ℂ) - X).det := by
  have h := BlockBand.Critical.Collar.Density.isUnit_det_sub_smul_one' hX hz
  rw [← neg_sub, det_neg]
  exact (((isUnit_neg_one (α := ℂ)).pow _)).mul h

omit [DecidableEq Q] in
/-- `Z* (h⁻¹ + h⁻¹ Γ Y Γ* h⁻¹) Z = Z* h⁻¹ Z + L* Y L`, `L = Γ* h⁻¹ Z`, for Hermitian `h`. -/
theorem source_expand {h : Matrix P P ℂ} (hh : h.IsHermitian) (Γ : Matrix P Q ℂ)
    (Z : Matrix P J ℂ) (Y : Matrix Q Q ℂ) :
    Zᴴ * (h⁻¹ + h⁻¹ * Γ * Y * Γᴴ * h⁻¹) * Z =
      Zᴴ * h⁻¹ * Z + (Γᴴ * h⁻¹ * Z)ᴴ * Y * (Γᴴ * h⁻¹ * Z) := by
  have hi : (h⁻¹)ᴴ = h⁻¹ := hh.inv.eq
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hi]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

omit [DecidableEq Q] in
/-- `Re` of `Z* (h⁻¹ + h⁻¹ Γ R Γ* h⁻¹) Z`. -/
theorem rePart_source {h : Matrix P P ℂ} (hh : h.IsHermitian) (Γ : Matrix P Q ℂ)
    (Z : Matrix P J ℂ) (R : Matrix Q Q ℂ) :
    (2 : ℂ)⁻¹ • (Zᴴ * (h⁻¹ + h⁻¹ * Γ * R * Γᴴ * h⁻¹) * Z +
        (Zᴴ * (h⁻¹ + h⁻¹ * Γ * R * Γᴴ * h⁻¹) * Z)ᴴ) =
      Zᴴ * h⁻¹ * Z + (Γᴴ * h⁻¹ * Z)ᴴ * ((2 : ℂ)⁻¹ • (R + Rᴴ)) * (Γᴴ * h⁻¹ * Z) := by
  rw [source_expand hh]
  have hi : (h⁻¹)ᴴ = h⁻¹ := hh.inv.eq
  have h0 : (Zᴴ * h⁻¹ * Z)ᴴ = Zᴴ * h⁻¹ * Z := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hi, Matrix.mul_assoc]
  have h1 : ((Γᴴ * h⁻¹ * Z)ᴴ * R * (Γᴴ * h⁻¹ * Z))ᴴ = (Γᴴ * h⁻¹ * Z)ᴴ * Rᴴ * (Γᴴ * h⁻¹ * Z) := by
    set L := Γᴴ * h⁻¹ * Z
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [conjTranspose_add, h0, h1]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul]
  module

/-- **Closed-source identity**, abstract form. `h` Hermitian invertible (old interior), `Γ` its port coupling,
`X = Γ* h⁻¹ Γ` (old reaction, Hermitian), `Z` the source columns, `Im z > 0`; `D` any port matrix
with `D - z̄` and `D - X` invertible (the closing collar's terminating reaction plus `Re z`).
With `K = Z*(h⁻¹ + h⁻¹Γ(z - X)⁻¹Γ*h⁻¹)Z` (open lead source matrix), `V = (z - X)⁻* Γ* h⁻¹ Z`,
`U = 1 - 2i Im z (D - z̄)⁻¹`, `S = 1 - 2i Im z (z - X)⁻¹`:
`Z*(h⁻¹ + h⁻¹Γ(D - X)⁻¹Γ*h⁻¹)Z = Re K + Im z · V* {-i(2(1 - US)⁻¹ - 1)} V`. -/
theorem source_closing_identity {h : Matrix P P ℂ} (hh : h.IsHermitian) (Γ : Matrix P Q ℂ)
    (Z : Matrix P J ℂ) {z : ℂ} (hz : 0 < z.im) {D : Matrix Q Q ℂ}
    (hT : IsUnit (D - conj z • (1 : Matrix Q Q ℂ)).det) (hY : IsUnit (D - Γᴴ * h⁻¹ * Γ).det)
    (hR : IsUnit (z • (1 : Matrix Q Q ℂ) - Γᴴ * h⁻¹ * Γ).det) :
    Zᴴ * (h⁻¹ + h⁻¹ * Γ * (D - Γᴴ * h⁻¹ * Γ)⁻¹ * Γᴴ * h⁻¹) * Z =
      (2 : ℂ)⁻¹ • (Zᴴ * (h⁻¹ + h⁻¹ * Γ * (z • 1 - Γᴴ * h⁻¹ * Γ)⁻¹ * Γᴴ * h⁻¹) * Z +
        (Zᴴ * (h⁻¹ + h⁻¹ * Γ * (z • 1 - Γᴴ * h⁻¹ * Γ)⁻¹ * Γᴴ * h⁻¹) * Z)ᴴ) +
      (z.im : ℂ) • ((((z • 1 - Γᴴ * h⁻¹ * Γ)⁻¹)ᴴ * (Γᴴ * h⁻¹ * Z))ᴴ *
        ((-Complex.I) • ((2 : ℂ) •
          (1 - (1 - (2 * (z.im : ℂ) * Complex.I) • (D - conj z • 1)⁻¹) *
            (1 - (2 * (z.im : ℂ) * Complex.I) • (z • 1 - Γᴴ * h⁻¹ * Γ)⁻¹))⁻¹ - 1)) *
        (((z • 1 - Γᴴ * h⁻¹ * Γ)⁻¹)ᴴ * (Γᴴ * h⁻¹ * Z))) := by
  have hX : (Γᴴ * h⁻¹ * Γ).IsHermitian := by
    have := isHermitian_conjTranspose_mul_mul Γ hh.inv
    simpa [Matrix.mul_assoc] using this
  have hport := port_closing_identity hz.ne' hX hR hT hY
  rw [rePart_source hh, source_expand hh, eq_add_of_sub_eq hport]
  set L := Γᴴ * h⁻¹ * Z
  simp only [conjTranspose_mul, conjTranspose_conjTranspose]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc,
    add_assoc]
  abel

/-- **Ward form of the lead source matrix** (`V*V = -Im K/η`): for the open lead
source matrix `K`, `Im K = -Im z · V*V`, `V = (z - X)⁻* Γ* h⁻¹ Z`. -/
theorem imPart_lead_source [Fintype J] {h : Matrix P P ℂ} (hh : h.IsHermitian) (Γ : Matrix P Q ℂ)
    (Z : Matrix P J ℂ) {z : ℂ} (hR : IsUnit (z • (1 : Matrix Q Q ℂ) - Γᴴ * h⁻¹ * Γ).det) :
    BlockBand.Internal.Contracts.Critical.imPart
        (Zᴴ * (h⁻¹ + h⁻¹ * Γ * (z • 1 - Γᴴ * h⁻¹ * Γ)⁻¹ * Γᴴ * h⁻¹) * Z) =
      -((z.im : ℂ) • ((((z • 1 - Γᴴ * h⁻¹ * Γ)⁻¹)ᴴ * (Γᴴ * h⁻¹ * Z))ᴴ *
        (((z • 1 - Γᴴ * h⁻¹ * Γ)⁻¹)ᴴ * (Γᴴ * h⁻¹ * Z)))) := by
  have hX : (Γᴴ * h⁻¹ * Γ).IsHermitian := by
    have := isHermitian_conjTranspose_mul_mul Γ hh.inv
    simpa [Matrix.mul_assoc] using this
  have hi : (h⁻¹)ᴴ = h⁻¹ := hh.inv.eq
  have h0 : (Zᴴ * h⁻¹ * Z)ᴴ = Zᴴ * h⁻¹ * Z := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hi, Matrix.mul_assoc]
  have hd := leadResolvent_sub_conjTranspose hX hR
  unfold BlockBand.Internal.Contracts.Critical.imPart
  rw [source_expand hh]
  set L := Γᴴ * h⁻¹ * Z
  set R := (z • (1 : Matrix Q Q ℂ) - Γᴴ * h⁻¹ * Γ)⁻¹
  have h1 : (Lᴴ * R * L)ᴴ = Lᴴ * Rᴴ * L := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hsub : Zᴴ * h⁻¹ * Z + Lᴴ * R * L - (Zᴴ * h⁻¹ * Z + Lᴴ * R * L)ᴴ =
      Lᴴ * (R - Rᴴ) * L := by
    rw [conjTranspose_add, h0, h1, Matrix.mul_sub, Matrix.sub_mul]; abel
  rw [hsub, hd]
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_smul, Matrix.smul_mul,
    smul_smul, Matrix.mul_assoc]
  have hI : (2 * Complex.I)⁻¹ * -(2 * (z.im : ℂ) * Complex.I) = -(z.im : ℂ) := by
    field_simp
  rw [hI, neg_smul]

end Blocks

section Vocabulary

open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open BlockBand.Internal.Contracts.CriticalEntire BlockBand.Critical.MatrixClosing

variable {P : Type*} [Fintype P] [DecidableEq P] {W r : ℕ}

/-- The closing collar's terminating reaction plus `Re z_b`:
`D = A - e - B(G - e)⁻¹B* = K_c + ξ` (`middleReaction` at zero shift). -/
def collarEndSchur (b e : ℝ) (ω : CollarSample W) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  middleReaction b e 0 ω + (((boundaryZ b e).re : ℝ) : ℂ) • 1

theorem collarEndSchur_eq (b e : ℝ) (ω : CollarSample W) :
    collarEndSchur b e ω = blockDiag ω.1.1 - (e : ℂ) • 1 -
      bondMatrix .common ω.1.2 * (ω.2 - (e : ℂ) • 1)⁻¹ * (bondMatrix .common ω.1.2)ᴴ := by
  unfold collarEndSchur middleReaction
  simp only [add_zero, add_smul]
  abel

theorem collarEndSchur_sub_conj (b e : ℝ) (ω : CollarSample W) :
    collarEndSchur b e ω - conj (boundaryZ b e) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) =
      middleReaction b e 0 ω + (((boundaryZ b e).im : ℂ) * Complex.I) • 1 := by
  unfold collarEndSchur
  have hz : conj (boundaryZ b e) = ((boundaryZ b e).re : ℂ) - ((boundaryZ b e).im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [hz, sub_smul]
  abel

/-- **Closed-source identity.** Let `K = Z*(h⁻¹ + h⁻¹Γ(z_b - X)⁻¹Γ*h⁻¹)Z` be the open lead source
matrix, `X = Γ*h⁻¹Γ`, and `F` an old orthonormal frame with `V = F B^{1/2}`, `B = probeGram K`. If
`T + iη` and `D - X` are invertible (`D = collarEndSchur`), the closed source matrix
`Z*(h⁻¹ + h⁻¹Γ(D - X)⁻¹Γ*h⁻¹)Z` is `closedSourceMatrix b e K 𝒞_W`, with the physical closing matrix
`𝒞_W = closingMatrix b e 0 X F ω` in place of `𝖢_p(0)`. -/
theorem closedSource_eq_closedSourceMatrix {J : ℕ} (b e : ℝ) (hη : 0 < (boundaryZ b e).im)
    {h : Matrix P P ℂ} (hh : h.IsHermitian) (Γ : Matrix P (Fin 2 × Fin W) ℂ)
    (Z : Matrix P (Fin J) ℂ) (ω : CollarSample W)
    (hT : IsUnit (middleReaction b e 0 ω + (((boundaryZ b e).im : ℂ) * Complex.I) • 1).det)
    (hY : IsUnit (collarEndSchur b e ω - Γᴴ * h⁻¹ * Γ).det)
    (F : Matrix (Fin 2 × Fin W) (Fin J) ℂ)
    (hF : ((boundaryZ b e • 1 - Γᴴ * h⁻¹ * Γ)⁻¹)ᴴ * (Γᴴ * h⁻¹ * Z) =
      F * cfc Real.sqrt (probeGram b e
        (Zᴴ * (h⁻¹ + h⁻¹ * Γ * (boundaryZ b e • 1 - Γᴴ * h⁻¹ * Γ)⁻¹ * Γᴴ * h⁻¹) * Z))) :
    Zᴴ * (h⁻¹ + h⁻¹ * Γ * (collarEndSchur b e ω - Γᴴ * h⁻¹ * Γ)⁻¹ * Γᴴ * h⁻¹) * Z =
      closedSourceMatrix b e
        (Zᴴ * (h⁻¹ + h⁻¹ * Γ * (boundaryZ b e • 1 - Γᴴ * h⁻¹ * Γ)⁻¹ * Γᴴ * h⁻¹) * Z)
        (closingMatrix b e 0 (Γᴴ * h⁻¹ * Γ) F ω) := by
  have hX : (Γᴴ * h⁻¹ * Γ).IsHermitian := by
    have := isHermitian_conjTranspose_mul_mul Γ hh.inv
    simpa [Matrix.mul_assoc] using this
  have hR := isUnit_det_smul_one_sub_of_isHermitian hX hη
  have hT' : IsUnit (collarEndSchur b e ω - conj (boundaryZ b e) • (1 : Matrix _ _ ℂ)).det := by
    rwa [collarEndSchur_sub_conj]
  rw [source_closing_identity hh Γ Z hη hT' hY hR, hF]
  set K := Zᴴ * (h⁻¹ + h⁻¹ * Γ * (boundaryZ b e • 1 - Γᴴ * h⁻¹ * Γ)⁻¹ * Γᴴ * h⁻¹) * Z
  set S := cfc Real.sqrt (probeGram b e K)
  have hS : Sᴴ = S := (cfc_predicate (p := IsSelfAdjoint) Real.sqrt (probeGram b e K) :)
  unfold closedSourceMatrix closingMatrix matrixRePart middleScattering oldScattering
  rw [collarEndSchur_sub_conj]
  congr 1
  simp only [BlockBand.Internal.Contracts.TransmissionPath.etaZ, conjTranspose_mul, hS,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  rfl

/-- `B = probeGram K = V*V` for the open lead source matrix (Ward identity `V*V = -Im K/η`). -/
theorem probeGram_lead_source {J : ℕ} (b e : ℝ) (hη : 0 < (boundaryZ b e).im)
    {h : Matrix P P ℂ} (hh : h.IsHermitian) (Γ : Matrix P (Fin 2 × Fin W) ℂ)
    (Z : Matrix P (Fin J) ℂ) :
    probeGram b e (Zᴴ * (h⁻¹ + h⁻¹ * Γ * (boundaryZ b e • 1 - Γᴴ * h⁻¹ * Γ)⁻¹ * Γᴴ * h⁻¹) * Z) =
      (((boundaryZ b e • 1 - Γᴴ * h⁻¹ * Γ)⁻¹)ᴴ * (Γᴴ * h⁻¹ * Z))ᴴ *
        (((boundaryZ b e • 1 - Γᴴ * h⁻¹ * Γ)⁻¹)ᴴ * (Γᴴ * h⁻¹ * Z)) := by
  have hX : (Γᴴ * h⁻¹ * Γ).IsHermitian := by
    have := isHermitian_conjTranspose_mul_mul Γ hh.inv
    simpa [Matrix.mul_assoc] using this
  have hR := isUnit_det_smul_one_sub_of_isHermitian hX hη
  unfold probeGram
  rw [imPart_lead_source hh Γ Z hR]
  simp only [BlockBand.Internal.Contracts.TransmissionPath.etaZ, smul_neg, smul_smul]
  have : -((((boundaryZ b e).im)⁻¹ : ℝ) : ℂ) * ((boundaryZ b e).im : ℂ) = -1 := by
    rw [neg_mul, ← Complex.ofReal_mul, inv_mul_cancel₀ hη.ne', Complex.ofReal_one]
  rw [this, neg_one_smul, neg_neg]

end Vocabulary

end BlockBand.Critical.EntireLaw
