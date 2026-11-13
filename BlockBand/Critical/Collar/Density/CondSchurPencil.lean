module

public import BlockBand.Critical.Collar.Density.SpectralSum
public import BlockBand.Critical.Collar.DilationVariance.Resolvent
public import BlockBand.Critical.WeightedDensity.Poisson
public import BlockBand.Critical.Collar.Density.SchurAlgebra

/-!
# Conditional Schur identity: the pencil

The conditional Schur pencil `[[D, B], [B*, G + w]]` of the collar (bottom scalar `w`), the
genericity condition `CsGeneric D B` (no eigenvector of `D` in `ker B*`), invertibility of the
dissipative pencil `w = θ - iη` under genericity, the Schur form of the top quadratic form at a
real energy, spectral sums, and the exact Cauchy mean in the bottom scalar
(`isCauchyMatrixMean_dilationResolvent`). Deterministic; every finite index type.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Density

open Matrix MeasureTheory
open BlockBand.Foundations.Spectral BlockBand.Model.Construction
open BlockBand.Internal.Contracts.CoareaPalm (quadForm)
open BlockBand.Critical.WeightedDensity (cauchyKernel cauchyKernel_eq_im_inv)
open scoped ComplexConjugate ComplexOrder

variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- The conditional collar pencil `[[D, B], [B*, G + w]]` (scalar `w` on the bottom block). -/
def csPencil (D : Matrix m m ℂ) (B : Matrix m n ℂ) (G : Matrix n n ℂ) (w : ℂ) :
    Matrix (m ⊕ n) (m ⊕ n) ℂ :=
  fromBlocks D B Bᴴ (G + w • 1)

/-- The bottom-block projection `Π = [[0, 0], [0, 1]]`. -/
def csPort : Matrix (m ⊕ n) (m ⊕ n) ℂ := fromBlocks 0 0 0 1

/-- **Genericity**: no eigenvector of `D` lies in `ker B*`. -/
def CsGeneric (D : Matrix m m ℂ) (B : Matrix m n ℂ) : Prop :=
  ∀ (x : ℝ) (v : m → ℂ), D *ᵥ v = (x : ℂ) • v → Bᴴ *ᵥ v = 0 → v = 0

/-- The Schur complement `S(x) = G - x - B*(D - x)⁻¹B`. -/
def csS (D : Matrix m m ℂ) (B : Matrix m n ℂ) (G : Matrix n n ℂ) (x : ℝ) : Matrix n n ℂ :=
  G - (x : ℂ) • 1 - Bᴴ * (D - (x : ℂ) • 1)⁻¹ * B

/-- The transferred vector `y(x) = B*(D - x)⁻¹u`. -/
def csY (D : Matrix m m ℂ) (B : Matrix m n ℂ) (u : m → ℂ) (x : ℝ) : n → ℂ :=
  (Bᴴ * (D - (x : ℂ) • 1)⁻¹) *ᵥ u

variable {D : Matrix m m ℂ} {B : Matrix m n ℂ} {G : Matrix n n ℂ}

theorem csPencil_add (D : Matrix m m ℂ) (B : Matrix m n ℂ) (G : Matrix n n ℂ) (w w' : ℂ) :
    csPencil D B G (w + w') = csPencil D B G w + w' • csPort := by
  unfold csPencil csPort
  rw [fromBlocks_smul, fromBlocks_add]
  simp [add_smul, add_assoc]

theorem csPencil_isHermitian (hD : D.IsHermitian) (hG : G.IsHermitian) (θ : ℝ) :
    (csPencil D B G θ).IsHermitian := by
  unfold csPencil
  refine IsHermitian.fromBlocks hD rfl ?_
  exact hG.add (isHermitian_one.smul (Complex.conj_ofReal θ))

theorem csPort_isHermitian : (csPort : Matrix (m ⊕ n) (m ⊕ n) ℂ).IsHermitian := by
  unfold csPort
  exact IsHermitian.fromBlocks isHermitian_zero (by simp) isHermitian_one

theorem csPort_mulVec (ψ : m ⊕ n → ℂ) :
    csPort *ᵥ ψ = Sum.elim (0 : m → ℂ) (fun j => ψ (Sum.inr j)) := by
  have hψ : ψ = Sum.elim (fun i => ψ (Sum.inl i)) (fun j => ψ (Sum.inr j)) := by
    funext x; cases x <;> rfl
  conv_lhs => rw [hψ]
  unfold csPort
  rw [fromBlocks_mulVec]
  simp

theorem star_dotProduct_csPort_mulVec (ψ : m ⊕ n → ℂ) :
    star ψ ⬝ᵥ (csPort *ᵥ ψ) = ((∑ j, ‖ψ (Sum.inr j)‖ ^ 2 : ℝ) : ℂ) := by
  rw [csPort_mulVec]
  simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
    mul_zero, Finset.sum_const_zero, zero_add, Pi.star_apply]
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_mul']
  push_cast; ring

theorem csPort_posSemidef : (csPort : Matrix (m ⊕ n) (m ⊕ n) ℂ).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg csPort_isHermitian fun ψ => ?_
  rw [star_dotProduct_csPort_mulVec]
  exact Complex.zero_le_real.2 (Finset.sum_nonneg fun j _ => sq_nonneg _)

/-- Under genericity, `csPencil (θ - iη) - z` is invertible for `η > 0` and `Im z ≥ 0`. -/
theorem isUnit_det_csPencil_sub (hD : D.IsHermitian) (hG : G.IsHermitian) (hgen : CsGeneric D B)
    {η : ℝ} (hη : 0 < η) (θ : ℝ) {z : ℂ} (hz : 0 ≤ z.im) :
    IsUnit (csPencil D B G ((θ : ℂ) - (η : ℂ) * Complex.I) - z • 1).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨ψ, hψ0, hψ⟩ := exists_mulVec_eq_zero_iff.2 hdet
  have hsplit : csPencil D B G ((θ : ℂ) - (η : ℂ) * Complex.I) - z • 1 =
      (csPencil D B G θ - (z.re : ℂ) • 1) -
        Complex.I • ((η : ℂ) • csPort + (z.im : ℂ) • 1) := by
    rw [sub_eq_add_neg (θ : ℂ), csPencil_add]
    conv_lhs => rw [← Complex.re_add_im z]
    simp only [smul_add, smul_smul, add_smul, neg_smul]
    have : Complex.I * (η : ℂ) = (η : ℂ) * Complex.I := mul_comm _ _
    rw [this, mul_comm Complex.I (z.im : ℂ)]
    abel
  have hH : (csPencil D B G θ - (z.re : ℂ) • 1).IsHermitian :=
    (csPencil_isHermitian hD hG θ).sub (isHermitian_one.smul (Complex.conj_ofReal _))
  have h0 : star ψ ⬝ᵥ ((csPencil D B G ((θ : ℂ) - (η : ℂ) * Complex.I) - z • 1) *ᵥ ψ) = 0 := by
    rw [hψ, dotProduct_zero]
  rw [hsplit, sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, add_mulVec,
    dotProduct_add, smul_mulVec, smul_mulVec, dotProduct_smul, dotProduct_smul, one_mulVec,
    star_dotProduct_csPort_mulVec] at h0
  have him := congrArg Complex.im h0
  have hre0 : (star ψ ⬝ᵥ ((csPencil D B G θ - (z.re : ℂ) • 1) *ᵥ ψ)).im = 0 :=
    Complex.conj_eq_iff_im.mp (hH.star_dotProduct_mulVec_comm ψ ψ)
  have hpsi : star ψ ⬝ᵥ ψ = ((∑ i, ‖ψ i‖ ^ 2 : ℝ) : ℂ) := by
    simp only [dotProduct, Pi.star_apply]
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
    push_cast; ring
  rw [hpsi] at him
  simp only [Complex.sub_im, Complex.zero_im, smul_eq_mul, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, hre0] at him
  set w2 := ∑ j, ‖ψ (Sum.inr j)‖ ^ 2
  set v2 := ∑ i, ‖ψ i‖ ^ 2
  have hw2 : 0 ≤ w2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hv2 : 0 ≤ v2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsum : η * w2 + z.im * v2 = 0 := by nlinarith
  have hw0 : w2 = 0 := by nlinarith [mul_nonneg hz hv2]
  have hzv : z.im * v2 = 0 := by nlinarith
  have hwz : ∀ j, ψ (Sum.inr j) = 0 := fun j => by
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ‖ψ (Sum.inr j)‖)).1 hw0 j
      (Finset.mem_univ j)
    simpa using this
  have hv2pos : 0 < v2 := by
    by_contra hle
    have hv0 : v2 = 0 := le_antisymm (not_lt.1 hle) hv2
    apply hψ0
    funext i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖ψ i‖)).1 hv0 i
      (Finset.mem_univ i)
    simpa using this
  have hzim : z.im = 0 := by
    rcases mul_eq_zero.1 hzv with h | h
    · exact h
    · exact absurd h hv2pos.ne'
  -- block equations
  set v : m → ℂ := fun i => ψ (Sum.inl i)
  have hψe : ψ = Sum.elim v 0 := by
    funext x; cases x with
    | inl i => rfl
    | inr j => simp [hwz j]
  rw [hψe] at hψ
  have hblk : csPencil D B G ((θ : ℂ) - (η : ℂ) * Complex.I) - z • 1 =
      fromBlocks (D - z • 1) B Bᴴ (G + ((θ : ℂ) - (η : ℂ) * Complex.I) • 1 - z • 1) := by
    unfold csPencil
    rw [← fromBlocks_one, fromBlocks_smul, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
    simp [sub_eq_add_neg]
  rw [hblk, fromBlocks_mulVec] at hψ
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, mulVec_zero, add_zero] at hψ
  have h1 := congrFun hψ
  have hz : z = (z.re : ℂ) := by
    conv_lhs => rw [← Complex.re_add_im z, hzim]
    simp
  have hDv : D *ᵥ v = (z.re : ℂ) • v := by
    funext i
    have := h1 (Sum.inl i)
    simp only [Sum.elim_inl, Pi.zero_apply, sub_mulVec, smul_mulVec, one_mulVec, Pi.sub_apply,
      Pi.smul_apply] at this
    rw [hz] at this
    simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
    linear_combination this
  have hBv : Bᴴ *ᵥ v = 0 := by
    funext j
    have := h1 (Sum.inr j)
    simpa using this
  apply hψ0
  rw [hψe, hgen z.re v hDv hBv]
  funext x; cases x <;> rfl

/-!
## The Schur value at a real energy
-/

theorem inv_neg_matrix {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) :
    (-M)⁻¹ = -M⁻¹ := by
  by_cases h : IsUnit M.det
  · exact inv_neg_of_isUnit_det h
  · have h' : ¬ IsUnit (-M).det := by
      rw [det_neg]
      intro hu
      exact h ((IsUnit.mul_iff.1 hu).2)
    rw [nonsing_inv_apply_not_isUnit _ h, nonsing_inv_apply_not_isUnit _ h', neg_zero]

theorem csPencil_sub_eq (D : Matrix m m ℂ) (B : Matrix m n ℂ) (G : Matrix n n ℂ) (w z : ℂ) :
    csPencil D B G w - z • 1 = fromBlocks (D - z • 1) B Bᴴ (G + w • 1 - z • 1) := by
  unfold csPencil
  rw [← fromBlocks_one, fromBlocks_smul, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
  simp [sub_eq_add_neg]

theorem csS_isHermitian (hD : D.IsHermitian) (hG : G.IsHermitian) (x : ℝ) :
    (csS D B G x).IsHermitian := by
  unfold csS
  have hDx : (D - (x : ℂ) • (1 : Matrix m m ℂ)).IsHermitian :=
    hD.sub (isHermitian_one.smul (Complex.conj_ofReal x))
  exact (hG.sub (isHermitian_one.smul (Complex.conj_ofReal x))).sub
    (isHermitian_conjTranspose_mul_mul B hDx.inv)

/-- **Schur form of the top quadratic form** at a real energy `x` off the spectrum of `D`. -/
theorem topForm_eq_schur (hD : D.IsHermitian) (u : m → ℂ) (w : ℂ) (x : ℝ)
    (hDx : IsUnit (D - (x : ℂ) • 1).det) (hS : IsUnit (csS D B G x + w • 1).det) :
    star (Sum.elim u (0 : n → ℂ)) ⬝ᵥ ((csPencil D B G w - (x : ℂ) • 1)⁻¹ *ᵥ Sum.elim u 0) =
      star u ⬝ᵥ ((D - (x : ℂ) • 1)⁻¹ *ᵥ u) +
        star (csY D B u x) ⬝ᵥ ((csS D B G x + w • 1)⁻¹ *ᵥ csY D B u x) := by
  have hSeq : G + w • 1 - (x : ℂ) • 1 - Bᴴ * (D - (x : ℂ) • 1)⁻¹ * B = csS D B G x + w • 1 := by
    unfold csS; abel
  rw [csPencil_sub_eq, inv_fromBlocks_schur _ _ _ _ hDx (by rwa [hSeq]), hSeq,
    ← star_dotProduct_toBlocks11_mulVec, toBlocks_fromBlocks₁₁, add_mulVec, dotProduct_add]
  congr 1
  have hDi : ((D - (x : ℂ) • (1 : Matrix m m ℂ))⁻¹).IsHermitian :=
    (hD.sub (isHermitian_one.smul (Complex.conj_ofReal x))).inv
  set Di := (D - (x : ℂ) • (1 : Matrix m m ℂ))⁻¹
  set S := csS D B G x + w • 1
  have hM : Di * B * S⁻¹ * Bᴴ * Di = (Bᴴ * Di)ᴴ * S⁻¹ * (Bᴴ * Di) := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose, hDi.eq]
    simp only [Matrix.mul_assoc]
  rw [hM, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]
  rfl

/-- `π⁻¹ Im y*(S(x) + t - iη)⁻¹y = y* P_η(S(x) + t) y` (`P_η` the Cauchy kernel). -/
theorem im_schurForm_eq_cfc (hD : D.IsHermitian) (hG : G.IsHermitian) (t : ℝ) {η : ℝ}
    (hη : 0 < η) (x : ℝ) (y : n → ℂ) :
    Real.pi⁻¹ * (star y ⬝ᵥ ((csS D B G x + ((t : ℂ) - (η : ℂ) * Complex.I) • 1)⁻¹ *ᵥ y)).im =
      quadForm (cfc (fun l => cauchyKernel η (l + t)) (csS D B G x)) y := by
  have hS := csS_isHermitian (B := B) hD hG x
  have hK : (csS D B G x + (t : ℂ) • (1 : Matrix n n ℂ)).IsHermitian :=
    hS.add (isHermitian_one.smul (Complex.conj_ofReal t))
  have hsplit : csS D B G x + ((t : ℂ) - (η : ℂ) * Complex.I) • 1 =
      (csS D B G x + (t : ℂ) • (1 : Matrix n n ℂ)) - ((η : ℂ) * Complex.I) • 1 := by
    rw [sub_smul]; abel
  have hz : ((η : ℂ) * Complex.I).im ≠ 0 := by simp [hη.ne']
  rw [hsplit, inv_sub_eq_specSum hK hz, dotProduct_specSum_mulVec, ← cfc_add_smul_one hS,
    cfc_eq_specSum hK]
  unfold quadForm
  rw [dotProduct_specSum_mulVec, Complex.im_sum, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  set l := increasingEigenvalue hK r
  rw [Complex.im_mul_ofReal, Complex.re_ofReal_mul]
  have hc := cauchyKernel_eq_im_inv hη 0 l
  have h0 : (⟨0, η⟩ : ℂ) = (η : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [h0] at hc
  have hev : cauchyKernel η (0 - l) = cauchyKernel η l := by
    unfold cauchyKernel; ring_nf
  rw [hev] at hc
  rw [← mul_assoc, ← hc]
  norm_cast

/-!
## Spectral sums at a real height
-/

/-- `π⁻¹ Im ψ*(H - x - iε)⁻¹ψ = Σ_r P_ε(x - μ_r)|b_r*ψ|²` for Hermitian `H`. -/
theorem im_resolventForm_eq_sum {ι : Type} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (x : ℝ) {ε : ℝ} (hε : 0 < ε) (ψ : ι → ℂ) :
    Real.pi⁻¹ * (star ψ ⬝ᵥ ((H - ((x : ℂ) + (ε : ℂ) * Complex.I) • 1)⁻¹ *ᵥ ψ)).im =
      ∑ r, cauchyKernel ε (x - increasingEigenvalue hH r) *
        ‖star (increasingEigenvector hH r) ⬝ᵥ ψ‖ ^ 2 := by
  have hz : ((x : ℂ) + (ε : ℂ) * Complex.I).im ≠ 0 := by simp [hε.ne']
  rw [inv_sub_eq_specSum hH hz, dotProduct_specSum_mulVec, Complex.im_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  have h0 : (⟨x, ε⟩ : ℂ) = (x : ℂ) + (ε : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [Complex.im_mul_ofReal, ← mul_assoc, cauchyKernel_eq_im_inv hε, h0]

/-- `u*(cfc f H)₁₁u = Σ_r f(μ_r)|b_r*ũ|²` for Hermitian `H` on `m ⊕ n`. -/
theorem quadForm_cfc_toBlocks11 {H : Matrix (m ⊕ n) (m ⊕ n) ℂ} (hH : H.IsHermitian)
    (f : ℝ → ℝ) (u : m → ℂ) :
    quadForm ((cfc f H).toBlocks₁₁) u = ∑ r, f (increasingEigenvalue hH r) *
      ‖star (increasingEigenvector hH r) ⬝ᵥ Sum.elim u (0 : n → ℂ)‖ ^ 2 := by
  unfold quadForm
  rw [star_dotProduct_toBlocks11_mulVec, cfc_eq_specSum hH, dotProduct_specSum_mulVec,
    Complex.re_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Complex.re_ofReal_mul]
  norm_cast

/-!
## The Cauchy mean in the scalar of the bottom block
-/

theorem csPencil_real_add (D : Matrix m m ℂ) (B : Matrix m n ℂ) (G : Matrix n n ℂ)
    (t η s : ℝ) :
    csPencil D B G ((t + η * s : ℝ) : ℂ) = csPencil D B G t + (s : ℂ) • ((η : ℂ) • csPort) := by
  rw [Complex.ofReal_add, csPencil_add, smul_smul, Complex.ofReal_mul, mul_comm]

/-- **Cauchy mean**: for `s ~ Cauchy(0,1)`,
`E ψ*(csPencil(t + ηs) - z)⁻¹ψ = ψ*(csPencil(t - iη) - z)⁻¹ψ`, `Im z > 0`. -/
theorem isCauchyMean_topForm (hD : D.IsHermitian) (hG : G.IsHermitian) (t : ℝ) {η : ℝ}
    (hη : 0 < η) {z : ℂ} (hz : 0 < z.im) (ψ : m ⊕ n → ℂ) :
    IsCauchyMean (fun s : ℝ => star ψ ⬝ᵥ
        ((csPencil D B G ((t + η * s : ℝ) : ℂ) - z • 1)⁻¹ *ᵥ ψ))
      (star ψ ⬝ᵥ ((csPencil D B G ((t : ℂ) - (η : ℂ) * Complex.I) - z • 1)⁻¹ *ᵥ ψ)) := by
  have hY : ((η : ℂ) • (csPort : Matrix (m ⊕ n) (m ⊕ n) ℂ)).PosSemidef := by
    have := (csPort_posSemidef (m := m) (n := n)).smul (a := η) hη.le
    rwa [← Complex.coe_smul] at this
  have h := isCauchyMatrixMean_dilationResolvent (Xh := csPencil D B G t)
    (Y := (η : ℂ) • csPort) (csPencil_isHermitian hD hG t) hY hz
  have hR : ∀ s : ℝ, (csPencil D B G ((t + η * s : ℝ) : ℂ) - z • 1)⁻¹ =
      -dilationResolvent (csPencil D B G t) ((η : ℂ) • csPort) z s := by
    intro s
    rw [dilationResolvent, csPencil_real_add, ← inv_neg_matrix]
    congr 1; abel
  have hA : (csPencil D B G ((t : ℂ) - (η : ℂ) * Complex.I) - z • 1)⁻¹ =
      -absorbedResolvent (csPencil D B G t) ((η : ℂ) • csPort) z := by
    rw [absorbedResolvent, ← inv_neg_matrix, sub_eq_add_neg (t : ℂ), csPencil_add]
    congr 1
    rw [smul_smul, mul_comm Complex.I (η : ℂ), neg_smul]
    abel
  simp_rw [hR, hA, neg_mulVec, dotProduct_neg]
  refine IsCauchyMean.neg ?_
  simp only [dotProduct, mulVec, Finset.mul_sum]
  refine IsCauchyMean.sum _ fun i _ => IsCauchyMean.sum _ fun j _ => ?_
  have := ((h i j).const_mul (star ψ i)).mul_const (ψ j)
  refine this.congr (fun s => by ring) (by ring)

end BlockBand.Critical.Collar.Density
