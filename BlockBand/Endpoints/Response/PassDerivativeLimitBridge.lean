module

public import BlockBand.Endpoints.Response.PassDerivativePhysical
public import BlockBand.Transmission.SchurPassivity

/-!
# The near-port defect of the absorbed path is the path transmission

`portDefect_absorbedScattering_zero`: for a sample with Hermitian blocks and positive absorption,
the near-port defect of the absorbed scattering matrix equals the path transmission matrix
`pathTransmission b E (κq) W n ω`. The proof eliminates the far port by Schur complements and
uses passivity of the near Schur pencil.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Layers
open BlockBand.Transmission
open scoped ComplexOrder

/-!
### Schur complements
-/

theorem toBlocks₂₂_inv_fromBlocks {m k : Type*} [Fintype m] [Fintype k] [DecidableEq m]
    [DecidableEq k] (A : Matrix m m ℂ) (B : Matrix m k ℂ) (C : Matrix k m ℂ) (D : Matrix k k ℂ)
    (hA : IsUnit A) (hS : IsUnit (D - C * A⁻¹ * B)) :
    ((fromBlocks A B C D)⁻¹).toBlocks₂₂ = (D - C * A⁻¹ * B)⁻¹ := by
  let : Invertible A := hA.invertible
  have hS' : IsUnit (D - C * ⅟A * B) := by simpa only [invOf_eq_nonsing_inv] using hS
  let : Invertible (D - C * ⅟A * B) := hS'.invertible
  let : Invertible (fromBlocks A B C D) := fromBlocks₁₁Invertible A B C D
  rw [← invOf_eq_nonsing_inv, invOf_fromBlocks₁₁_eq]
  simp only [toBlocks_fromBlocks₂₂, invOf_eq_nonsing_inv]

theorem toBlocks₁₁_inv_fromBlocks {m k : Type*} [Fintype m] [Fintype k] [DecidableEq m]
    [DecidableEq k] (A : Matrix m m ℂ) (B : Matrix m k ℂ) (C : Matrix k m ℂ) (D : Matrix k k ℂ)
    (hD : IsUnit D) (hS : IsUnit (A - B * D⁻¹ * C)) :
    ((fromBlocks A B C D)⁻¹).toBlocks₁₁ = (A - B * D⁻¹ * C)⁻¹ := by
  let : Invertible D := hD.invertible
  have hS' : IsUnit (A - B * ⅟D * C) := by simpa only [invOf_eq_nonsing_inv] using hS
  let : Invertible (A - B * ⅟D * C) := hS'.invertible
  let : Invertible (fromBlocks A B C D) := fromBlocks₂₂Invertible A B C D
  rw [← invOf_eq_nonsing_inv, invOf_fromBlocks₂₂_eq]
  simp only [toBlocks_fromBlocks₁₁, invOf_eq_nonsing_inv]

theorem isUnit_schur₂₂ {m k : Type*} [Fintype m] [Fintype k] [DecidableEq m] [DecidableEq k]
    (A : Matrix m m ℂ) (B : Matrix m k ℂ) (C : Matrix k m ℂ) (D : Matrix k k ℂ)
    (hD : IsUnit D) (hM : IsUnit (fromBlocks A B C D)) : IsUnit (A - B * D⁻¹ * C) := by
  let : Invertible D := hD.invertible
  have h := det_fromBlocks₂₂ A B C D
  rw [invOf_eq_nonsing_inv] at h
  rw [isUnit_iff_isUnit_det] at hM ⊢
  rw [h] at hM
  exact isUnit_of_mul_isUnit_right hM

/-!
### The port splitting `Fin 2 × Fin W ≃ Fin W ⊕ Fin W`
-/

/-- `inl a ↦ (0, a)` (near port), `inr a ↦ (1, a)` (far port). -/
def portSplit (W : ℕ) : Fin W ⊕ Fin W ≃ Fin 2 × Fin W where
  toFun := Sum.elim (fun a => (0, a)) (fun a => (1, a))
  invFun := fun p => if p.1 = 0 then Sum.inl p.2 else Sum.inr p.2
  left_inv := by intro x; cases x <;> simp
  right_inv := by
    rintro ⟨i, a⟩
    fin_cases i <;> simp

theorem submatrix_portSplit {W : ℕ} (K : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    K.submatrix (portSplit W) (portSplit W) =
      fromBlocks (portBlock K 0 0) (portBlock K 0 1) (portBlock K 1 0) (portBlock K 1 1) := by
  ext x y
  rcases x with a | a <;> rcases y with c | c <;> rfl

theorem portBlock_inv_00 {W : ℕ} (K : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (h11 : IsUnit (portBlock K 1 1)) (hK : IsUnit K) :
    portBlock K⁻¹ 0 0 = (portBlock K 0 0 - portBlock K 0 1 * (portBlock K 1 1)⁻¹ *
      portBlock K 1 0)⁻¹ := by
  have hsub : IsUnit (K.submatrix (portSplit W) (portSplit W)) := by
    rw [isUnit_iff_isUnit_det, det_submatrix_equiv_self]
    exact (isUnit_iff_isUnit_det _).1 hK
  rw [submatrix_portSplit] at hsub
  have hS := isUnit_schur₂₂ _ _ _ _ h11 hsub
  have h := toBlocks₁₁_inv_fromBlocks _ _ _ _ h11 hS
  rw [← submatrix_portSplit, inv_submatrix_equiv] at h
  rw [← h]
  rfl

/-!
### Passivity
-/

theorem posSemidef_neg_im_conj {m k : Type*} [Fintype m] [Fintype k] [DecidableEq m]
    (C : Matrix m k ℂ) {G : Matrix m m ℂ} (hG : (-matrixImaginaryPart G).PosSemidef) :
    (-matrixImaginaryPart (Cᴴ * G * C)).PosSemidef := by
  rw [matrixImaginaryPart_congruence]
  have : -(Cᴴ * matrixImaginaryPart G * C) = Cᴴ * (-matrixImaginaryPart G) * C := by
    simp only [Matrix.mul_neg, Matrix.neg_mul]
  rw [this]
  exact hG.conjTranspose_mul_mul_same C

theorem matrixImaginaryPart_smul_one_sub {m : Type*} [DecidableEq m] (z : ℂ)
    (X : Matrix m m ℂ) :
    matrixImaginaryPart (z • (1 : Matrix m m ℂ) - X) =
      (z.im : ℂ) • (1 : Matrix m m ℂ) + -matrixImaginaryPart X := by
  rw [matrixImaginaryPart_sub, sub_eq_add_neg]
  congr 1
  have h := matrixImaginaryPart_portPencil (0 : Matrix m m ℂ) isHermitian_zero z
  simpa [portPencil] using h

theorem isUnit_smul_one_sub {m : Type*} [Fintype m] [DecidableEq m] {z : ℂ} (hz : 0 < z.im)
    {X : Matrix m m ℂ} (hX : (-matrixImaginaryPart X).PosSemidef) :
    IsUnit (z • (1 : Matrix m m ℂ) - X) := by
  apply isUnit_of_matrixImaginaryPart_posDef
  rw [matrixImaginaryPart_smul_one_sub]
  refine PosDef.add_posSemidef ?_ hX
  have : (z.im : ℂ) • (1 : Matrix m m ℂ) = z.im • (1 : Matrix m m ℂ) := by
    ext i j; simp [Complex.real_smul]
  rw [this]
  exact PosDef.one.smul hz

theorem portInclusion_injective {W : ℕ} (i : Fin 2) :
    Function.Injective (portInclusion W i).mulVec := by
  intro v w h
  funext a
  have := congrFun h (i, a)
  simpa [portInclusion, mulVec, dotProduct, Prod.ext_iff] using this

theorem portBlock_eq_compression' {W : ℕ} (K : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (i : Fin 2) : portBlock K i i = (portInclusion W i)ᴴ * K * portInclusion W i :=
  (portBlock_eq_compression K i)

/-!
### Positivity of `η`
-/

theorem etaZ_pos {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) : 0 < etaZ b E := by
  have h4 : 0 < 4 - E ^ 2 := by nlinarith
  have hs := Real.sq_sqrt h4.le
  have hn : Complex.normSq (matchedA E) = 1 := by
    rw [Complex.normSq_apply]
    simp only [matchedA]
    nlinarith
  simp only [etaZ, boundaryZ, Complex.add_im, Complex.inv_im, hn,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  simp only [matchedA]
  have := Real.sqrt_pos.2 h4
  nlinarith

/-!
### The bridge
-/

variable {W n : ℕ}

/-- **Bridge.** With Hermitian blocks, bulk `E`, `b < 1` and `ε_i > 0` on every path block, the
near-port reflection defect of the absorbed full path is the `pathTransmission`.
-/
theorem portDefect_absorbedScattering_zero {b E κ : ℝ} {q : ℝ → ℝ} (hb : b < 1) (hE1 : -2 < E)
    (hE2 : E < 2) (hpos : ∀ i : Fin n, 0 < layerAbsorption W (fun t => κ * q t) n i)
    {ω : GrowthPath W} (hH : ∀ k, (ω.1 k).IsHermitian) :
    portDefect (absorbedScattering b E W n κ q ω) 0 =
      pathTransmission b E (fun t => κ * q t) W n ω := by
  set ε := layerAbsorption W (fun t => κ * q t) n
  set z := boundaryZ b E
  set η := etaZ b E
  have hη : 0 < η := etaZ_pos hb hE1 hE2
  have hz : 0 < z.im := hη
  set H := pathMatrix (pathAt W n ω) - (E : ℂ) • 1
  have hHh : H.IsHermitian := by
    have h0 := pathMatrix_isHermitian (W := W) (n := n) (ω := pathAt W n ω) fun i => hH _
    refine h0.sub ?_
    unfold IsHermitian
    rw [conjTranspose_smul, conjTranspose_one, Complex.star_def, Complex.conj_ofReal]
  set Γ : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ := diagonal fun x => ((ε x.1 : ℝ) : ℂ)
  have hΓ : Γ.PosDef := by
    rw [posDef_diagonal_iff]
    intro x
    exact_mod_cast hpos x.1
  have hAdiag : absorptionDiag W ε = Complex.I • Γ := by
    ext x y
    simp only [absorptionDiag, Γ, Matrix.smul_apply, diagonal_apply, smul_eq_mul]
    split_ifs <;> ring
  set A := H + absorptionDiag W ε
  have hA : IsUnit A.det := by
    rw [show A = H + Complex.I • Γ by rw [← hAdiag]]
    exact isUnit_det_add_I_smul_of_posDef hHh hΓ
  have hAinv : (-matrixImaginaryPart A⁻¹).PosSemidef := by
    rw [show A = H + Complex.I • Γ by rw [← hAdiag]]
    exact absorbedResolvent_negativeImaginary_posSemidef H Γ hHh hΓ.isHermitian hΓ.posSemidef
      (by rw [← hAdiag]; exact hA)
  set C := pathPortCoupling (pathAt W n ω)
  set X := absorbedPathSchur E ε (pathAt W n ω)
  have hX : X = Cᴴ * A⁻¹ * C := rfl
  have hXim : (-matrixImaginaryPart X).PosSemidef := by
    rw [hX]; exact posSemidef_neg_im_conj C hAinv
  set K := z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X
  have hK : IsUnit K := isUnit_smul_one_sub hz hXim
  -- port block of the inverse of the full matrix
  have hfull : (absorbedFullMatrix b E W n κ q ω)⁻¹.toBlocks₂₂ = K⁻¹ := by
    have e : absorbedFullMatrix b E W n κ q ω = fromBlocks A C Cᴴ (z • 1) := rfl
    have hS : IsUnit (z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - Cᴴ * A⁻¹ * C) := by
      rw [← hX]; exact hK
    rw [e, toBlocks₂₂_inv_fromBlocks A C Cᴴ (z • 1) ((isUnit_iff_isUnit_det _).2 hA) hS, ← hX]
  -- far port elimination
  have h11 : IsUnit (portBlock K 1 1) := by
    rw [portBlock_eq_compression']
    apply isUnit_of_matrixImaginaryPart_posDef
    rw [matrixImaginaryPart_congruence]
    refine PosDef.conjTranspose_mul_mul_same ?_ (portInclusion_injective 1)
    rw [matrixImaginaryPart_smul_one_sub]
    refine PosDef.add_posSemidef ?_ hXim
    have : (z.im : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) =
        z.im • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) := by
      ext i j; simp [Complex.real_smul]
    rw [this]
    exact PosDef.one.smul hz
  have hblk : ∀ i j : Fin 2, portBlock K i j =
      (if i = j then z • (1 : Matrix (Fin W) (Fin W) ℂ) else 0) - portBlock X i j := by
    intro i j
    ext a c
    by_cases hij : i = j
    · subst hij
      simp [portBlock, K, one_apply, Prod.ext_iff]
    · simp [portBlock, K, one_apply, Prod.ext_iff, hij]
  set N := nearSchur z X
  have hSchur : portBlock K 0 0 - portBlock K 0 1 * (portBlock K 1 1)⁻¹ * portBlock K 1 0 =
      z • (1 : Matrix (Fin W) (Fin W) ℂ) - N := by
    rw [hblk 0 0, hblk 0 1, hblk 1 0, hblk 1 1]
    simp only [ite_true, show (0 : Fin 2) ≠ 1 from by decide, show (1 : Fin 2) ≠ 0 from by decide,
      ite_false, zero_sub, Matrix.neg_mul, Matrix.mul_neg, neg_neg, N, nearSchur]
    abel
  have hR : portBlock K⁻¹ 0 0 = (z • (1 : Matrix (Fin W) (Fin W) ℂ) - N)⁻¹ := by
    rw [portBlock_inv_00 K h11 hK, hSchur]
  -- the near Schur pencil is invertible
  have hNu : IsUnit (z • (1 : Matrix (Fin W) (Fin W) ℂ) - N) := by
    rw [← hSchur]
    have hsub : IsUnit (K.submatrix (portSplit W) (portSplit W)) := by
      rw [isUnit_iff_isUnit_det, det_submatrix_equiv_self]
      exact (isUnit_iff_isUnit_det _).1 hK
    rw [submatrix_portSplit] at hsub
    exact isUnit_schur₂₂ _ _ _ _ h11 hsub
  set R := (z • (1 : Matrix (Fin W) (Fin W) ℂ) - N)⁻¹
  have hKR : (z • (1 : Matrix (Fin W) (Fin W) ℂ) - N) * R = 1 :=
    mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hNu)
  have hbal : (z • (1 : Matrix (Fin W) (Fin W) ℂ) - N) -
      star (z • (1 : Matrix (Fin W) (Fin W) ℂ) - N) =
      (2 * Complex.I * (η : ℂ)) • (1 : Matrix (Fin W) (Fin W) ℂ) +
        (2 * Complex.I) • passiveY N := by
    rw [star_eq_conjTranspose, conjTranspose_sub, conjTranspose_smul, conjTranspose_one,
      passiveY, matrixImaginaryPart]
    have hzc : z - star z = 2 * Complex.I * (η : ℂ) := by
      apply Complex.ext <;> simp [η, etaZ, z]
      ring
    have e1 : z • (1 : Matrix (Fin W) (Fin W) ℂ) - N - (star z • 1 - Nᴴ) =
        (z - star z) • (1 : Matrix (Fin W) (Fin W) ℂ) - (N - Nᴴ) := by
      rw [sub_smul]; abel
    rw [e1, hzc]
    have e2 : (2 * Complex.I) • -((-Complex.I / 2) • (N - Nᴴ)) = -(N - Nᴴ) := by
      rw [smul_neg, smul_smul]
      have : 2 * Complex.I * (-Complex.I / 2) = 1 := by
        field_simp; rw [Complex.I_sq]; ring
      rw [this, one_smul]
    rw [e2, sub_eq_add_neg]
  have hphys := passive_scattering_physical _ R (passiveY N) η hKR hbal
  -- assemble
  have hS00 : portBlock (absorbedScattering b E W n κ q ω) 0 0 =
      1 - (2 * Complex.I * (η : ℂ)) • R := by
    rw [absorbedScattering, hfull]
    have : portBlock (1 - (((2 * η : ℝ) : ℂ) * Complex.I) • K⁻¹) 0 0 =
        1 - (((2 * η : ℝ) : ℂ) * Complex.I) • portBlock K⁻¹ 0 0 := by
      ext a c
      simp [portBlock, one_apply, Prod.ext_iff]
    rw [this, hR]
    congr 2
    push_cast; ring
  rw [portDefect, hS00, ← star_eq_conjTranspose, hphys]
  simp only [pathTransmission, passiveTransmission, passiveQ, passiveResolvent, pathNearSchur]
  rw [star_eq_conjTranspose]
  push_cast
  rfl

end BlockBand.Endpoints
