module

public import BlockBand.Critical.BoundaryMean.Statement

/-!
# Removing the collar-side regularization (strict old response `Y ≻ 0`)

The dilation identity `Collar.Kernel.neg_im_collarResolvent_eq_integral` needs a positive height
`ν` in the Hermitian resolvents. This file proves that the height can be removed on the collar side
**with equality**, not only by Fatou: `E f_ν → E f_0` as `ν ↓ 0`, where
`f_ν(ω) = -Im⟨ρ*q, (ℋ_X + iν)⁻¹ ρ*q⟩` (`regForm`) and `f_0 = η q*𝒫(Ur)q`.

*Domination.* For one sample (Hermitian `A_j, G`), `Y = -Im X ≻ 0` and `ν ≥ 0`, put `x = (ℋ_X + iν)⁻¹ y`,
`y = ρ*q`, `q̂ = (q, 0)` and `Λ = diag(Y, 0) + ν`. Then `f_ν = ⟨x, Λx⟩`; the shifted vector
`x' = x + q̂` solves `(ℋ_X + iν)x' = (m_ν, 0)` with the **deterministic** `m_ν = (conj z_b + iν)q - Xq`
(`domVec`); `⟨x', Λx'⟩ = Im⟨x'₁, m_ν⟩ ≤ ½(⟨x'₁,Yx'₁⟩ + ⟨Y⁻¹m_ν, m_ν⟩)` gives
`⟨x', Λx'⟩ ≤ ⟨Y⁻¹m_ν, m_ν⟩`, and `f_ν ≤ 2⟨Y⁻¹m_ν,m_ν⟩ + 2⟨q,(Y+ν)q⟩` (`neg_im_collarForm_le`).
For `ν ∈ [0, 1]` this is bounded by the sample-independent `domBound` (`domTerm_le_domBound`).
No norm bound on `X` is used.

Law: `collarLaw W b`, `b < 1/2`, deterministic `X`. No hypothesis is used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.BoundaryMean

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open BlockBand.Critical.Collar.Density (collarMatrix collarRowVec)
open BlockBand.Critical.Collar.Kernel (topLift rePart)
open scoped ComplexOrder

section Forms

variable {ι : Type*} [Fintype ι]

/-- `Re⟨a+b, P(a+b)⟩ ≤ 2Re⟨a,Pa⟩ + 2Re⟨b,Pb⟩` for `P ⪰ 0`. -/
theorem re_quad_add_le {P : Matrix ι ι ℂ} (hP : P.PosSemidef) (a b : ι → ℂ) :
    (star (a + b) ⬝ᵥ (P *ᵥ (a + b))).re ≤
      2 * (star a ⬝ᵥ (P *ᵥ a)).re + 2 * (star b ⬝ᵥ (P *ᵥ b)).re := by
  have h := (Complex.nonneg_iff.1 (hP.dotProduct_mulVec_nonneg (a - b))).1
  simp only [star_add, star_sub, mulVec_add, mulVec_sub, add_dotProduct, sub_dotProduct,
    dotProduct_add, dotProduct_sub, Complex.add_re, Complex.sub_re] at h ⊢
  linarith

/-- For `Y ⪰ 0` and `Yp = m`: `Im⟨a, m⟩ ≤ (Re⟨a,Ya⟩ + Re⟨p,Yp⟩)/2`. -/
theorem im_dotProduct_le_of_posSemidef {Y : Matrix ι ι ℂ} (hY : Y.PosSemidef) {p m : ι → ℂ}
    (hpm : Y *ᵥ p = m) (a : ι → ℂ) :
    (star a ⬝ᵥ m).im ≤ ((star a ⬝ᵥ (Y *ᵥ a)).re + (star p ⬝ᵥ (Y *ᵥ p)).re) / 2 := by
  have h := (Complex.nonneg_iff.1 (hY.dotProduct_mulVec_nonneg (a + Complex.I • p))).1
  have hc : star p ⬝ᵥ (Y *ᵥ a) = star (star a ⬝ᵥ (Y *ᵥ p)) :=
    (hY.isHermitian.star_dotProduct_mulVec_comm a p).symm
  have hexp : star (a + Complex.I • p) ⬝ᵥ (Y *ᵥ (a + Complex.I • p)) =
      star a ⬝ᵥ (Y *ᵥ a) + Complex.I * (star a ⬝ᵥ (Y *ᵥ p)) +
        (-Complex.I) * star (star a ⬝ᵥ (Y *ᵥ p)) + star p ⬝ᵥ (Y *ᵥ p) := by
    simp only [star_add, star_smul, mulVec_add, mulVec_smul, add_dotProduct, smul_dotProduct,
      dotProduct_add, dotProduct_smul, smul_eq_mul, hc, Complex.star_def, Complex.conj_I]
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hexp] at h
  rw [← hpm]
  set z := star a ⬝ᵥ (Y *ᵥ p)
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.neg_re,
    Complex.neg_im, Complex.star_def, Complex.conj_re, Complex.conj_im] at h
  linarith

end Forms

section Collar

variable {W : ℕ}

/-- The deterministic top vector `m_ν = (conj z_b + iν) q - X q`. -/
def domVec (b e ν : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (q : Fin 2 × Fin W → ℂ) :
    Fin 2 × Fin W → ℂ :=
  (star (boundaryZ b e) + (ν : ℂ) * Complex.I) • q - X *ᵥ q

theorem dotProduct_sum_elim_zero {α β : Type*} [Fintype α] [Fintype β] (v : α ⊕ β → ℂ)
    (m : α → ℂ) : star v ⬝ᵥ (Sum.elim m 0 : α ⊕ β → ℂ) = star (v ∘ Sum.inl) ⬝ᵥ m := by
  simp [dotProduct, Fintype.sum_sum_type]

theorem topLift_mulVec (Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (v : LayerSite W .common → ℂ) :
    topLift Y *ᵥ v = Sum.elim (Y *ᵥ (v ∘ Sum.inl)) 0 := by
  rw [topLift, fromBlocks_mulVec]
  simp only [zero_mulVec, add_zero]

/-- **Deterministic two-sided bound for the regularized collar form** (one sample with Hermitian
`A_j, G`; `Y = -Im X ≻ 0`; `ν ≥ 0` with `ℋ_X + iν` invertible): with `y = ρ*q`,
`0 ≤ -Im⟨y, (ℋ_X + iν)⁻¹ y⟩ ≤ 2Re⟨Y⁻¹m_ν, m_ν⟩ + 2Re⟨q, Yq⟩ + 2ν‖q‖²`, `m_ν = (conj z_b + iν)q - Xq`.
The bound does not depend on the sample. -/
theorem neg_im_collarForm_le (b e : ℝ) {ω : CollarSample W}
    (hA : ∀ j, (ω.1.1 j).IsHermitian) (hG : ω.2.IsHermitian)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hY : (-imPart X).PosDef) {ν : ℝ} (hν : 0 ≤ ν)
    (hH : IsUnit (collarMatrix e X ω + ((ν : ℂ) * Complex.I) • 1).det)
    (q : Fin 2 × Fin W → ℂ) :
    0 ≤ -(star (collarRowVec (Collar.Kernel.rowCoeff b e 0) q ω) ⬝ᵥ
        ((collarMatrix e X ω + ((ν : ℂ) * Complex.I) • 1)⁻¹ *ᵥ
          collarRowVec (Collar.Kernel.rowCoeff b e 0) q ω)).im ∧
    -(star (collarRowVec (Collar.Kernel.rowCoeff b e 0) q ω) ⬝ᵥ
        ((collarMatrix e X ω + ((ν : ℂ) * Complex.I) • 1)⁻¹ *ᵥ
          collarRowVec (Collar.Kernel.rowCoeff b e 0) q ω)).im ≤
      2 * (star ((-imPart X)⁻¹ *ᵥ domVec b e ν X q) ⬝ᵥ domVec b e ν X q).re +
        2 * (star q ⬝ᵥ ((-imPart X) *ᵥ q)).re + 2 * ν * ∑ x, ‖q x‖ ^ 2 := by
  set Y := -imPart X with hYdef
  set H := collarMatrix e X ω + ((ν : ℂ) * Complex.I) • 1 with hHdef
  set y := collarRowVec (Collar.Kernel.rowCoeff b e 0) q ω
  set m := domVec b e ν X q
  set Λ : Matrix (LayerSite W .common) (LayerSite W .common) ℂ := topLift Y + (ν : ℂ) • 1
  have hHs : H = collarMatrix e (rePart X) ω + Complex.I • Λ := by
    rw [hHdef, Collar.Kernel.collarMatrix_eq_herm_add e X ω]
    simp only [Λ, smul_add, smul_smul]
    rw [mul_comm Complex.I]
    abel
  have hHh : (collarMatrix e (rePart X) ω).IsHermitian :=
    Collar.Kernel.collarMatrix_isHermitian e hA hG (Collar.Kernel.rePart_isHermitian X)
  have hΛ : Λ.PosSemidef :=
    (Collar.Kernel.topLift_posSemidef hY.posSemidef).add
      (PosSemidef.one.smul (Complex.zero_le_real.2 hν))
  have F1 : ∀ v, (star v ⬝ᵥ (H *ᵥ v)).im = (star v ⬝ᵥ (Λ *ᵥ v)).re := by
    intro v
    rw [hHs, add_mulVec, dotProduct_add, smul_mulVec, dotProduct_smul, smul_eq_mul,
      Complex.add_im, BlockBand.Wegner.im_star_dotProduct_mulVec_hermitian hHh, zero_add,
      Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]
  set x := H⁻¹ *ᵥ y
  have hx : H *ᵥ x = y := by
    simp only [x, mulVec_mulVec, mul_nonsing_inv _ hH, one_mulVec]
  have F2 : -(star y ⬝ᵥ x).im = (star x ⬝ᵥ (Λ *ᵥ x)).re := by
    rw [← hx, star_dotProduct, Complex.star_def, Complex.conj_im, neg_neg, F1]
  set qh : LayerSite W .common → ℂ := Sum.elim q 0
  have F3 : y + H *ᵥ qh = Sum.elim m 0 := by
    have hcm : collarMatrix e X ω *ᵥ qh = Sum.elim
        ((blockDiag ω.1.1 - (e : ℂ) • 1 - X) *ᵥ q) ((bondMatrix .common ω.1.2)ᴴ *ᵥ q) := by
      rw [collarMatrix, fromBlocks_mulVec]
      simp only [qh]
      congr 1
      · funext i; simp [mulVec, dotProduct]
      · funext i; simp [mulVec, dotProduct]
    rw [hHdef, add_mulVec, hcm, smul_mulVec, one_mulVec]
    funext i
    rcases i with i | i
    · simp only [y, collarRowVec, Pi.add_apply, Sum.elim_inl, Pi.smul_apply, m, domVec,
        Pi.sub_apply, sub_mulVec, smul_mulVec, one_mulVec, smul_eq_mul, qh,
        Collar.Kernel.rowCoeff, star_add, Complex.star_def, Complex.conj_ofReal]
      push_cast
      ring
    · simp [y, collarRowVec, qh]
  set x' := x + qh
  have F3' : H *ᵥ x' = Sum.elim m 0 := by rw [mulVec_add, hx, F3]
  have F4 : ∀ v : LayerSite W .common → ℂ, (star v ⬝ᵥ (Λ *ᵥ v)).re =
      (star (v ∘ Sum.inl) ⬝ᵥ (Y *ᵥ (v ∘ Sum.inl))).re + ν * (star v ⬝ᵥ v).re := by
    intro v
    rw [add_mulVec, topLift_mulVec, dotProduct_add, dotProduct_sum_elim_zero, smul_mulVec,
      one_mulVec, dotProduct_smul, smul_eq_mul, Complex.add_re, Complex.re_ofReal_mul]
  have hQx' : (star x' ⬝ᵥ (Λ *ᵥ x')).re = (star (x' ∘ Sum.inl) ⬝ᵥ m).im := by
    rw [← F1, F3', dotProduct_sum_elim_zero]
  have hYu : IsUnit Y.det := isUnit_iff_ne_zero.2 hY.det_pos.ne'
  set p := Y⁻¹ *ᵥ m
  have hpm : Y *ᵥ p = m := by simp only [p, mulVec_mulVec, mul_nonsing_inv _ hYu, one_mulVec]
  have h5 := im_dotProduct_le_of_posSemidef hY.posSemidef hpm (x' ∘ Sum.inl)
  have hxx : 0 ≤ (star x' ⬝ᵥ x').re := by
    rw [BlockBand.Wegner.re_star_dotProduct_self]; positivity
  have hQ' : (star x' ⬝ᵥ (Λ *ᵥ x')).re ≤ (star p ⬝ᵥ m).re := by
    have h4 := F4 x'
    rw [hpm] at h5
    have : 0 ≤ ν * (star x' ⬝ᵥ x').re := mul_nonneg hν hxx
    linarith
  have hxdec : x = x' + -qh := by simp [x']
  have h6 := re_quad_add_le hΛ x' (-qh)
  have hqh : (star (-qh) ⬝ᵥ (Λ *ᵥ (-qh))).re = (star q ⬝ᵥ (Y *ᵥ q)).re + ν * ∑ x, ‖q x‖ ^ 2 := by
    rw [star_neg, mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg, F4,
      BlockBand.Wegner.re_star_dotProduct_self]
    simp [qh, Fintype.sum_sum_type]
  refine ⟨?_, ?_⟩
  · rw [F2]; exact (Complex.nonneg_iff.1 (hΛ.dotProduct_mulVec_nonneg x)).1
  · rw [F2, hxdec]
    rw [hqh] at h6
    linarith

/-- The sample-independent dominating constant (`ν ∈ [0, 1]`):
`2(2Re⟨m₀,Y⁻¹m₀⟩ + 2Re⟨q,Y⁻¹q⟩) + 2Re⟨q,Yq⟩ + 2‖q‖²`, `m₀ = conj(z_b) q - Xq`. -/
def domBound (b e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (q : Fin 2 × Fin W → ℂ) : ℝ :=
  2 * (2 * (star (domVec b e 0 X q) ⬝ᵥ ((-imPart X)⁻¹ *ᵥ domVec b e 0 X q)).re +
    2 * (star q ⬝ᵥ ((-imPart X)⁻¹ *ᵥ q)).re) + 2 * (star q ⬝ᵥ ((-imPart X) *ᵥ q)).re +
      2 * ∑ x, ‖q x‖ ^ 2

theorem domVec_eq (b e ν : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (q : Fin 2 × Fin W → ℂ) :
    domVec b e ν X q = domVec b e 0 X q + ((ν : ℂ) * Complex.I) • q := by
  simp only [domVec, add_smul, Complex.ofReal_zero, zero_mul, add_zero]
  abel

/-- The `ν`-dependent bound of `neg_im_collarForm_le` is at most `domBound` for `0 ≤ ν ≤ 1`. -/
theorem domTerm_le_domBound (b e : ℝ) {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hY : (-imPart X).PosDef) {ν : ℝ} (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) (q : Fin 2 × Fin W → ℂ) :
    2 * (star ((-imPart X)⁻¹ *ᵥ domVec b e ν X q) ⬝ᵥ domVec b e ν X q).re +
        2 * (star q ⬝ᵥ ((-imPart X) *ᵥ q)).re + 2 * ν * ∑ x, ‖q x‖ ^ 2 ≤ domBound b e X q := by
  set Y := -imPart X
  have hP : Y⁻¹.PosSemidef := hY.inv.posSemidef
  have hsym : ∀ v : Fin 2 × Fin W → ℂ, star (Y⁻¹ *ᵥ v) ⬝ᵥ v = star v ⬝ᵥ (Y⁻¹ *ᵥ v) := by
    intro v
    rw [star_dotProduct, hP.isHermitian.star_dotProduct_mulVec_comm]
  rw [hsym, domVec_eq]
  have h1 := re_quad_add_le hP (domVec b e 0 X q) (((ν : ℂ) * Complex.I) • q)
  have h2 : (star (((ν : ℂ) * Complex.I) • q) ⬝ᵥ (Y⁻¹ *ᵥ (((ν : ℂ) * Complex.I) • q))).re =
      ν ^ 2 * (star q ⬝ᵥ (Y⁻¹ *ᵥ q)).re := by
    rw [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      ← mul_assoc]
    have : star ((ν : ℂ) * Complex.I) * ((ν : ℂ) * Complex.I) = ((ν ^ 2 : ℝ) : ℂ) := by
      simp only [star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [this, Complex.re_ofReal_mul]
  have h3 : 0 ≤ (star q ⬝ᵥ (Y⁻¹ *ᵥ q)).re := (Complex.nonneg_iff.1 (hP.dotProduct_mulVec_nonneg q)).1
  have h4 : ν ^ 2 ≤ 1 := by nlinarith
  have h5 : 0 ≤ ∑ x, ‖q x‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  unfold domBound
  rw [h2] at h1
  nlinarith

/-- `ℋ_X + iν` is invertible for `ν > 0` (Hermitian `A_j, G`, `Y = -Im X ⪰ 0`). -/
theorem isUnit_det_collarMatrix_add (e : ℝ) {ω : CollarSample W}
    (hA : ∀ j, (ω.1.1 j).IsHermitian) (hG : ω.2.IsHermitian)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hY : (-imPart X).PosSemidef) {ν : ℝ}
    (hν : 0 < ν) : IsUnit (collarMatrix e X ω + ((ν : ℂ) * Complex.I) • 1).det := by
  have h : collarMatrix e X ω + ((ν : ℂ) * Complex.I) • 1 = collarMatrix e (rePart X) ω +
      Complex.I • (topLift (-imPart X) +
        (ν : ℂ) • (1 : Matrix (LayerSite W .common) (LayerSite W .common) ℂ)) := by
    rw [Collar.Kernel.collarMatrix_eq_herm_add]
    module
  rw [h]
  exact Collar.Kernel.isUnit_det_herm_add_I_smul_posDef
    (Collar.Kernel.collarMatrix_isHermitian e hA hG (Collar.Kernel.rePart_isHermitian X))
    ((PosDef.one.smul (by exact_mod_cast hν)).posSemidef_add (Collar.Kernel.topLift_posSemidef hY))

/-- The regularized collar form `f_ν(ω) = -Im⟨ρ*q, (ℋ_X + iν)⁻¹ ρ*q⟩` (`ν = 0`: unregularized). -/
def regForm (b e ν : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (q : Fin 2 × Fin W → ℂ)
    (ω : CollarSample W) : ℝ :=
  -(star (collarRowVec (Collar.Kernel.rowCoeff b e 0) q ω) ⬝ᵥ
    ((collarMatrix e X ω + ((ν : ℂ) * Complex.I) • 1)⁻¹ *ᵥ
      collarRowVec (Collar.Kernel.rowCoeff b e 0) q ω)).im

theorem measurable_neg_im_form {ι : Type} [Fintype ι] [DecidableEq ι] {Ω : Type*}
    [MeasurableSpace Ω] {M : Ω → Matrix ι ι ℂ} {v : Ω → ι → ℂ} (hM : Measurable M)
    (hv : Measurable v) :
    Measurable fun ω => -(star (v ω) ⬝ᵥ ((M ω)⁻¹ *ᵥ v ω)).im := by
  have hinv := (BlockBand.Wegner.measurable_matrix_inv (n := ι)).comp hM
  have hcont : Continuous fun p : Matrix ι ι ℂ × (ι → ℂ) => -(star p.2 ⬝ᵥ (p.1 *ᵥ p.2)).im :=
    (Complex.continuous_im.comp ((continuous_star.comp continuous_snd).dotProduct
      (continuous_fst.matrix_mulVec continuous_snd))).neg
  exact (hcont.measurable.comp (hinv.prodMk hv) :)

theorem measurable_collarMatrix_add (e : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (c : ℂ) : Measurable fun ω : CollarSample W =>
      collarMatrix e X ω + c • (1 : Matrix (LayerSite W .common) (LayerSite W .common) ℂ) := by
  have hMc := Collar.Density.measurable_collarMatrix e X (W := W)
  exact Measurable.of_eval_matrix _ fun i j => ((Matrix.measurable_apply).comp hMc).add
    measurable_const

theorem measurable_regForm (b e ν : ℝ) (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (q : Fin 2 × Fin W → ℂ) : Measurable (regForm b e ν X q) :=
  measurable_neg_im_form (measurable_collarMatrix_add e X _)
    (Collar.Density.measurable_collarRowVec (W := W) (Collar.Kernel.rowCoeff b e 0) q)

/-- Almost surely, `0 ≤ f_ν ≤ domBound` for every `ν ∈ [0, 1]` (`b < 1/2`, `Y ≻ 0`). -/
theorem ae_regForm_bound {b : ℝ} (hb : b < 1 / 2) (e : ℝ)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hY : (-imPart X).PosDef)
    (q : Fin 2 × Fin W → ℂ) :
    ∀ᵐ ω ∂collarLaw W b, IsUnit (collarMatrix e X ω).det ∧ ∀ ν ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ regForm b e ν X q ω ∧ regForm b e ν X q ω ≤ domBound b e X q := by
  filter_upwards [Collar.Density.ae_collarMatrix_isHermitian b e
      (Collar.Kernel.rePart_isHermitian X) (W := W),
    Collar.Kernel.ae_isUnit_det_middleBlock hb e 0 (W := W)] with ω hω hD
  have hH0 : IsUnit (collarMatrix e X ω).det := by
    simpa using Collar.Kernel.isUnit_det_collarMatrix b e 0 hω.2.1 hω.2.2 hD hY
  refine ⟨hH0, fun ν hν => ?_⟩
  have hH : IsUnit (collarMatrix e X ω + ((ν : ℂ) * Complex.I) • 1).det := by
    rcases hν.1.eq_or_lt with h0 | hpos
    · subst h0; simpa using hH0
    · exact isUnit_det_collarMatrix_add e hω.2.1 hω.2.2 hY.posSemidef hpos
  obtain ⟨h1, h2⟩ := neg_im_collarForm_le b e hω.2.1 hω.2.2 hY hν.1 hH q
  exact ⟨h1, h2.trans (domTerm_le_domBound b e hY hν.1 hν.2 q)⟩

theorem integrable_regForm {b : ℝ} (hb : b < 1 / 2) (e : ℝ)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hY : (-imPart X).PosDef)
    (q : Fin 2 × Fin W → ℂ) {ν : ℝ} (hν : ν ∈ Set.Icc (0 : ℝ) 1) :
    Integrable (regForm b e ν X q) (collarLaw W b) := by
  refine Integrable.of_bound (C := domBound b e X q)
    (measurable_regForm b e ν X q).aestronglyMeasurable ?_
  filter_upwards [ae_regForm_bound hb e hY q] with ω hω
  obtain ⟨h1, h2⟩ := hω.2 ν hν
  rw [Real.norm_of_nonneg h1]
  exact h2

/-- **Removing the regularization on the collar side** (dominated convergence, `Y ≻ 0`): for
`u_n ∈ (0, 1]`, `u_n → 0`, `E f_{u_n} → E f_0`. -/
theorem tendsto_integral_regForm {b : ℝ} (hb : b < 1 / 2) (e : ℝ)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hY : (-imPart X).PosDef)
    (q : Fin 2 × Fin W → ℂ) {u : ℕ → ℝ} (hu0 : ∀ n, 0 < u n) (hu1 : ∀ n, u n ≤ 1)
    (hu : Tendsto u atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, regForm b e (u n) X q ω ∂collarLaw W b) atTop
      (𝓝 (∫ ω, regForm b e 0 X q ω ∂collarLaw W b)) := by
  refine tendsto_integral_of_dominated_convergence (fun _ => domBound b e X q)
    (fun n => (measurable_regForm b e (u n) X q).aestronglyMeasurable) (integrable_const _)
    (fun n => ?_) ?_
  · filter_upwards [ae_regForm_bound hb e hY q] with ω hω
    obtain ⟨h1, h2⟩ := hω.2 (u n) ⟨(hu0 n).le, hu1 n⟩
    rw [Real.norm_of_nonneg h1]
    exact h2
  · filter_upwards [ae_regForm_bound hb e hY q] with ω hω
    have ht := Collar.Kernel.tendsto_inv_add_smul_I _ hω.1 hu
    have hc : Continuous fun M : Matrix (LayerSite W .common) (LayerSite W .common) ℂ =>
        -(star (collarRowVec (Collar.Kernel.rowCoeff b e 0) q ω) ⬝ᵥ
          (M *ᵥ collarRowVec (Collar.Kernel.rowCoeff b e 0) q ω)).im :=
      (Complex.continuous_im.comp (continuous_const.dotProduct
        (continuous_id.matrix_mulVec continuous_const))).neg
    have h0 : regForm b e 0 X q ω = -(star (collarRowVec (Collar.Kernel.rowCoeff b e 0) q ω) ⬝ᵥ
        ((collarMatrix e X ω)⁻¹ *ᵥ collarRowVec (Collar.Kernel.rowCoeff b e 0) q ω)).im := by
      simp [regForm]
    rw [h0]
    exact (hc.tendsto _).comp ht

end Collar

end BlockBand.Critical.BoundaryMean
