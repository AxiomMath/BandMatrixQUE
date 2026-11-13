module

public import BlockBand.Endpoints.Response.PassDerivativeNorms
public import BlockBand.DeterminantScore.PointwiseJacobi
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Normed.Ring.Units

/-!
# Determinant ratios on `0 ⪯ T ⪯ I`: first and second variations

* `IsUnitBand T`: `T` Hermitian with `0 ≤ Re⟨v,Tv⟩ ≤ |v|²`, i.e. `0 ⪯ T ⪯ I`; convex
  (`IsUnitBand.segment`).
* `ratioDetC x y T = det(I - yT)/det(I + xT)` (complex value; `ratioDet` is its real part, the
  paper's `F_{x,y}(T)`), and its first variation
  `ratioDetDeriv x y T D = F(T)·(Tr[(I-yT)⁻¹(-yD)] - Tr[(I+xT)⁻¹(xD)])`.
* For `x ≥ 0`, `0 ≤ y < 1`, `T, T' ⪯`-band and `‖D‖₁ ≤ r` (`TraceBound`):
  `‖ratioDetC T‖ ≤ 1` (`norm_ratioDetC_le_one`),
  `‖ratioDetDeriv T D‖ ≤ c₁ r` (`norm_ratioDetDeriv_le`),
  `‖F(T') - F(T) - ratioDetDeriv T (T' - T)‖ ≤ c₂ ‖T' - T‖₁²` (`ratioDetC_second_order`),
  with `c₁ = y/(1-y) + x` and `c₂ = c₁² + (y/(1-y))² + x²` (`ratioC1`, `ratioC2`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `0 ⪯ T ⪯ I`: `T` Hermitian with `0 ≤ Re⟨v, Tv⟩ ≤ |v|²` for all `v`. -/
def IsUnitBand (T : Matrix n n ℂ) : Prop :=
  T.IsHermitian ∧ ∀ v : n → ℂ, 0 ≤ (star v ⬝ᵥ (T *ᵥ v)).re ∧
    (star v ⬝ᵥ (T *ᵥ v)).re ≤ vecNormSq v

/-- `F_{x,y}(T) = det(I - yT)/det(I + xT)` as a complex number. -/
def ratioDetC (x y : ℝ) (T : Matrix n n ℂ) : ℂ :=
  (1 - (y : ℂ) • T).det / (1 + (x : ℂ) • T).det

/-- The real determinant ratio `F_{x,y}(T)` of the paper (the complex value is real on the band). -/
def ratioDet (x y : ℝ) (T : Matrix n n ℂ) : ℝ := (ratioDetC x y T).re

/-- The first variation `DF_{x,y}(T)[D] = F(T)·(Tr[(I-yT)⁻¹(-yD)] - Tr[(I+xT)⁻¹(xD)])`. -/
def ratioDetDeriv (x y : ℝ) (T D : Matrix n n ℂ) : ℂ :=
  ratioDetC x y T * (((1 - (y : ℂ) • T)⁻¹ * (-(y : ℂ) • D)).trace -
    ((1 + (x : ℂ) • T)⁻¹ * ((x : ℂ) • D)).trace)

/-- `c₁ = y/(1-y) + x`. -/
def ratioC1 (x y : ℝ) : ℝ := y / (1 - y) + x

/-- `c₂ = c₁² + (y/(1-y))² + x²`. -/
def ratioC2 (x y : ℝ) : ℝ := ratioC1 x y ^ 2 + (y / (1 - y)) ^ 2 + x ^ 2

theorem ratioC1_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1) : 0 ≤ ratioC1 x y :=
  add_nonneg (div_nonneg hy0 (by linarith)) hx

theorem ratioC2_nonneg (x y : ℝ) : 0 ≤ ratioC2 x y := by unfold ratioC2; positivity

theorem ratioDetDeriv_sub (x y : ℝ) (T D₁ D₂ : Matrix n n ℂ) :
    ratioDetDeriv x y T (D₁ - D₂) = ratioDetDeriv x y T D₁ - ratioDetDeriv x y T D₂ := by
  simp only [ratioDetDeriv, smul_sub, Matrix.mul_sub, trace_sub]
  ring

theorem ratioDetDeriv_smul (x y : ℝ) (T D : Matrix n n ℂ) (a : ℂ) :
    ratioDetDeriv x y T (a • D) = a * ratioDetDeriv x y T D := by
  simp only [ratioDetDeriv, smul_comm _ a D, Matrix.mul_smul, trace_smul, smul_eq_mul]
  ring

theorem ratioDetDeriv_add (x y : ℝ) (T D₁ D₂ : Matrix n n ℂ) :
    ratioDetDeriv x y T (D₁ + D₂) = ratioDetDeriv x y T D₁ + ratioDetDeriv x y T D₂ := by
  simp only [ratioDetDeriv, smul_add, Matrix.mul_add, trace_add]
  ring

/-!
### The band
-/

omit [DecidableEq n] in
theorem IsUnitBand.isHermitian {T : Matrix n n ℂ} (h : IsUnitBand T) : T.IsHermitian := h.1

omit [DecidableEq n] in
theorem quad_add_smul (T H : Matrix n n ℂ) (t : ℝ) (v : n → ℂ) :
    (star v ⬝ᵥ ((T + (t : ℂ) • H) *ᵥ v)).re =
      (star v ⬝ᵥ (T *ᵥ v)).re + t * (star v ⬝ᵥ (H *ᵥ v)).re := by
  rw [add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul, Complex.add_re,
    Complex.re_ofReal_mul]

omit [DecidableEq n] in
/-- The band is convex. -/
theorem IsUnitBand.segment {T₀ T₁ : Matrix n n ℂ} (h₀ : IsUnitBand T₀) (h₁ : IsUnitBand T₁)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : IsUnitBand (T₀ + (t : ℂ) • (T₁ - T₀)) := by
  refine ⟨?_, fun v => ?_⟩
  · have hH : (T₁ - T₀).IsHermitian := h₁.1.sub h₀.1
    unfold IsHermitian
    rw [conjTranspose_add, conjTranspose_smul, h₀.1.eq, hH.eq, Complex.star_def,
      Complex.conj_ofReal]
  · have e : (star v ⬝ᵥ ((T₀ + (t : ℂ) • (T₁ - T₀)) *ᵥ v)).re =
        (1 - t) * (star v ⬝ᵥ (T₀ *ᵥ v)).re + t * (star v ⬝ᵥ (T₁ *ᵥ v)).re := by
      rw [quad_add_smul, sub_mulVec, dotProduct_sub, Complex.sub_re]
      ring
    rw [e]
    obtain ⟨a0, a1⟩ := h₀.2 v
    obtain ⟨b0, b1⟩ := h₁.2 v
    constructor
    · have : 0 ≤ 1 - t := by linarith
      positivity
    · nlinarith

theorem band_accretive_sub {T : Matrix n n ℂ} (h : IsUnitBand T) {y : ℝ} (hy0 : 0 ≤ y)
    (v : n → ℂ) : (1 - y) * vecNormSq v ≤ (star v ⬝ᵥ ((1 - (y : ℂ) • T) *ᵥ v)).re := by
  rw [sub_mulVec, one_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, star_dotProduct_self,
    smul_eq_mul, Complex.sub_re, Complex.ofReal_re, Complex.re_ofReal_mul]
  have := (h.2 v).2
  nlinarith

theorem band_accretive_add {T : Matrix n n ℂ} (h : IsUnitBand T) {x : ℝ} (hx : 0 ≤ x)
    (v : n → ℂ) : 1 * vecNormSq v ≤ (star v ⬝ᵥ ((1 + (x : ℂ) • T) *ᵥ v)).re := by
  rw [add_mulVec, one_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, star_dotProduct_self,
    smul_eq_mul, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]
  have := (h.2 v).1
  nlinarith

theorem band_inv_sub {T : Matrix n n ℂ} (h : IsUnitBand T) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    IsUnit (1 - (y : ℂ) • T) ∧ ‖(1 - (y : ℂ) • T)⁻¹‖ ≤ (1 - y)⁻¹ :=
  accretive_isUnit_norm_inv_le (by linarith) (band_accretive_sub h hy0)

theorem band_inv_add {T : Matrix n n ℂ} (h : IsUnitBand T) {x : ℝ} (hx : 0 ≤ x) :
    IsUnit (1 + (x : ℂ) • T) ∧ ‖(1 + (x : ℂ) • T)⁻¹‖ ≤ 1 := by
  have := accretive_isUnit_norm_inv_le one_pos (band_accretive_add h hx)
  simpa using this

theorem vecNormSq_eigenvector {A : Matrix n n ℂ} (hA : A.IsHermitian) (i : n) :
    vecNormSq (hA.eigenvectorBasis i).ofLp = 1 := by
  rw [vecNormSq_eq_norm_sq]
  have : (EuclideanSpace.equiv n ℂ).symm (hA.eigenvectorBasis i).ofLp =
      hA.eigenvectorBasis i := rfl
  rw [this, (hA.eigenvectorBasis).norm_eq_one i, one_pow]

/-- Eigenvalues of a Hermitian matrix are `≥ c` when `c|v|² ≤ Re⟨v,Av⟩`. -/
theorem eigenvalues_ge_of_quad {A : Matrix n n ℂ} (hA : A.IsHermitian) {c : ℝ}
    (hc : ∀ v, c * vecNormSq v ≤ (star v ⬝ᵥ (A *ᵥ v)).re) (i : n) : c ≤ hA.eigenvalues i := by
  rw [hA.eigenvalues_eq i]
  have h1 := hc (hA.eigenvectorBasis i).ofLp
  rwa [vecNormSq_eigenvector, mul_one] at h1

/-- Eigenvalues of a Hermitian matrix are `≤ d` when `Re⟨v,Av⟩ ≤ d|v|²`. -/
theorem eigenvalues_le_of_quad {A : Matrix n n ℂ} (hA : A.IsHermitian) {d : ℝ}
    (hd : ∀ v, (star v ⬝ᵥ (A *ᵥ v)).re ≤ d * vecNormSq v) (i : n) : hA.eigenvalues i ≤ d := by
  rw [hA.eigenvalues_eq i]
  have h1 := hd (hA.eigenvectorBasis i).ofLp
  rwa [vecNormSq_eigenvector, mul_one] at h1

theorem norm_det_le_one_of_quad {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (hc : ∀ v, 0 * vecNormSq v ≤ (star v ⬝ᵥ (A *ᵥ v)).re)
    (hd : ∀ v, (star v ⬝ᵥ (A *ᵥ v)).re ≤ 1 * vecNormSq v) : ‖A.det‖ ≤ 1 := by
  rw [hA.det_eq_prod_eigenvalues, norm_prod]
  refine Finset.prod_le_one₀ (fun i _ => norm_nonneg _) fun i _ => ?_
  rw [RCLike.norm_ofReal, abs_of_nonneg (eigenvalues_ge_of_quad hA hc i)]
  exact eigenvalues_le_of_quad hA hd i

theorem one_le_norm_det_of_quad {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (hc : ∀ v, 1 * vecNormSq v ≤ (star v ⬝ᵥ (A *ᵥ v)).re) : 1 ≤ ‖A.det‖ := by
  rw [hA.det_eq_prod_eigenvalues, norm_prod]
  refine Finset.one_le_prod₀ fun i _ => ?_
  have := eigenvalues_ge_of_quad hA hc i
  rw [RCLike.norm_ofReal, abs_of_nonneg (by linarith)]
  exact this

/-- `0 ≤ F ≤ 1` (in norm) on the band. -/
theorem norm_ratioDetC_le_one {x y : ℝ} (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1)
    {T : Matrix n n ℂ} (h : IsUnitBand T) : ‖ratioDetC x y T‖ ≤ 1 := by
  have hHy : (1 - (y : ℂ) • T).IsHermitian := by
    refine (isHermitian_one).sub ?_
    unfold IsHermitian
    rw [conjTranspose_smul, h.1.eq, Complex.star_def, Complex.conj_ofReal]
  have hHx : (1 + (x : ℂ) • T).IsHermitian := by
    refine (isHermitian_one).add ?_
    unfold IsHermitian
    rw [conjTranspose_smul, h.1.eq, Complex.star_def, Complex.conj_ofReal]
  have hnum : ‖(1 - (y : ℂ) • T).det‖ ≤ 1 := by
    refine norm_det_le_one_of_quad hHy (fun v => ?_) (fun v => ?_)
    · have := band_accretive_sub h hy0 v
      have := vecNormSq_nonneg v
      nlinarith
    · rw [sub_mulVec, one_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul,
        star_dotProduct_self, smul_eq_mul, Complex.sub_re, Complex.ofReal_re,
        Complex.re_ofReal_mul]
      have := (h.2 v).1
      nlinarith
  have hden : 1 ≤ ‖(1 + (x : ℂ) • T).det‖ := one_le_norm_det_of_quad hHx (band_accretive_add h hx)
  unfold ratioDetC
  rw [norm_div]
  exact div_le_one_of_le₀ (hnum.trans hden) (by linarith)

/-- First variation bound: `‖DF(T)[D]‖ ≤ c₁ ‖D‖₁`. -/
theorem norm_ratioDetDeriv_le {x y : ℝ} (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1)
    {T D : Matrix n n ℂ} (h : IsUnitBand T) {r : ℝ} (hD : TraceBound D r) :
    ‖ratioDetDeriv x y T D‖ ≤ ratioC1 x y * r := by
  obtain ⟨-, hny⟩ := band_inv_sub h hy0 hy1
  obtain ⟨-, hnx⟩ := band_inv_add h hx
  have h1 : ‖((1 - (y : ℂ) • T)⁻¹ * (-(y : ℂ) • D)).trace‖ ≤ (1 - y)⁻¹ * (y * r) := by
    have := (hD.smul (-(y : ℂ))).trace_le (1 - (y : ℂ) • T)⁻¹
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy0] at this
    exact this.trans (mul_le_mul_of_nonneg_right hny (mul_nonneg hy0 hD.1))
  have h2 : ‖((1 + (x : ℂ) • T)⁻¹ * ((x : ℂ) • D)).trace‖ ≤ 1 * (x * r) := by
    have := (hD.smul (x : ℂ)).trace_le (1 + (x : ℂ) • T)⁻¹
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx] at this
    exact this.trans (mul_le_mul_of_nonneg_right hnx (mul_nonneg hx hD.1))
  unfold ratioDetDeriv
  rw [norm_mul]
  have hF := norm_ratioDetC_le_one hx hy0 hy1 h
  have hsum : ‖((1 - (y : ℂ) • T)⁻¹ * (-(y : ℂ) • D)).trace -
      ((1 + (x : ℂ) • T)⁻¹ * ((x : ℂ) • D)).trace‖ ≤ ratioC1 x y * r := by
    refine (norm_sub_le _ _).trans ?_
    have e : ratioC1 x y * r = (1 - y)⁻¹ * (y * r) + 1 * (x * r) := by
      unfold ratioC1; field_simp
    rw [e]
    exact add_le_add h1 h2
  calc ‖ratioDetC x y T‖ * _ ≤ 1 * (ratioC1 x y * r) :=
        mul_le_mul hF hsum (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

/-!
### Derivatives along a real matrix line
-/

/-- Jacobi's formula at any point `t₀` of the real line `A + tH` with invertible value. -/
theorem hasDerivAt_det_line (A H : Matrix n n ℂ) (t₀ : ℝ) (h : IsUnit (A + (t₀ : ℂ) • H).det) :
    HasDerivAt (fun t : ℝ => (A + (t : ℂ) • H).det)
      ((A + (t₀ : ℂ) • H).det * ((A + (t₀ : ℂ) • H)⁻¹ * H).trace) t₀ := by
  have h0 := BlockBand.DeterminantScore.hasDerivAt_det_realAffineLine (A + (t₀ : ℂ) • H) H h
  have h0' : HasDerivAt (fun t : ℝ => (A + (t₀ : ℂ) • H + (t : ℂ) • H).det)
      ((A + (t₀ : ℂ) • H).det * ((A + (t₀ : ℂ) • H)⁻¹ * H).trace) (t₀ - t₀) := by
    rw [sub_self]; exact h0
  have h1 := HasDerivAt.comp_sub_const t₀ t₀ h0'
  refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  show (A + (t : ℂ) • H).det = (A + (t₀ : ℂ) • H + ((t - t₀ : ℝ) : ℂ) • H).det
  rw [add_assoc, ← add_smul]
  congr 3
  push_cast
  ring

/-- Derivative of the inverse along the real line `A + tH`, at an invertible value. -/
theorem hasDerivAt_inv_line (A H : Matrix n n ℂ) (t₀ : ℝ) (h : IsUnit (A + (t₀ : ℂ) • H)) :
    HasDerivAt (fun t : ℝ => (A + (t : ℂ) • H)⁻¹)
      (-((A + (t₀ : ℂ) • H)⁻¹ * H * (A + (t₀ : ℂ) • H)⁻¹)) t₀ := by
  have hp : HasDerivAt (fun z : ℂ => A + z • H) H (t₀ : ℂ) := by
    simpa using ((hasDerivAt_id (t₀ : ℂ)).smul_const H).const_add A
  have hi := (hasFDerivAt_ringInverse (𝕜 := ℂ) h.unit).comp_hasDerivAt (t₀ : ℂ) hp
  have huinv : (↑(h.unit⁻¹) : Matrix n n ℂ) = (A + (t₀ : ℂ) • H)⁻¹ := by
    rw [← Ring.inverse_of_isUnit h, Matrix.nonsing_inv_eq_ringInverse]
  have hc : HasDerivAt (fun z : ℂ => (A + z • H)⁻¹)
      (-((A + (t₀ : ℂ) • H)⁻¹ * H * (A + (t₀ : ℂ) • H)⁻¹)) (t₀ : ℂ) := by
    simpa only [Function.comp_apply, huinv, _root_.neg_apply,
      ContinuousLinearMap.mulLeftRight_apply, Matrix.nonsing_inv_eq_ringInverse] using! hi
  have hr : HasDerivAt (fun t : ℝ => (t : ℂ)) ((1 : ℝ) : ℂ) t₀ := (hasDerivAt_id t₀).ofReal_comp
  exact (hc.scomp t₀ hr).congr_deriv (by simp)

/-- The trace commutes with real differentiation. -/
theorem hasDerivAt_trace {f : ℝ → Matrix n n ℂ} {f' : Matrix n n ℂ} {t : ℝ}
    (hf : HasDerivAt f f' t) : HasDerivAt (fun s => (f s).trace) f'.trace t := by
  let L : Matrix n n ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.traceLinearMap n ℝ ℂ)
  have h2 : (fun s => (f s).trace) = L ∘ f := by funext s; rfl
  rw [h2]
  exact L.hasFDerivAt.comp_hasDerivAt t hf

/-- **Second variation on the band**: for `x ≥ 0`, `0 ≤ y < 1`, band matrices `T₀, T₁` and
`‖T₁ - T₀‖₁ ≤ r`: `‖F(T₁) - F(T₀) - DF(T₀)[T₁ - T₀]‖ ≤ c₂ r²`. -/
theorem ratioDetC_second_order {x y : ℝ} (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1)
    {T₀ T₁ : Matrix n n ℂ} (h₀ : IsUnitBand T₀) (h₁ : IsUnitBand T₁) {r : ℝ}
    (hH : TraceBound (T₁ - T₀) r) :
    ‖ratioDetC x y T₁ - ratioDetC x y T₀ - ratioDetDeriv x y T₀ (T₁ - T₀)‖ ≤
      ratioC2 x y * r ^ 2 := by
  set H := T₁ - T₀ with hHdef
  set A₀ : Matrix n n ℂ := 1 - (y : ℂ) • T₀
  set A' : Matrix n n ℂ := -(y : ℂ) • H
  set B₀ : Matrix n n ℂ := 1 + (x : ℂ) • T₀
  set B' : Matrix n n ℂ := (x : ℂ) • H
  set At : ℝ → Matrix n n ℂ := fun t => A₀ + (t : ℂ) • A' with hAtdef
  set Bt : ℝ → Matrix n n ℂ := fun t => B₀ + (t : ℂ) • B' with hBtdef
  have hAt : ∀ t : ℝ, At t = 1 - (y : ℂ) • (T₀ + (t : ℂ) • H) := by
    intro t
    simp only [At, A₀, A', smul_add, smul_smul, neg_smul, smul_neg]
    rw [mul_comm]; abel
  have hBt : ∀ t : ℝ, Bt t = 1 + (x : ℂ) • (T₀ + (t : ℂ) • H) := by
    intro t
    simp only [Bt, B₀, B', smul_add, smul_smul]
    rw [mul_comm, add_assoc]
  have hband : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsUnitBand (T₀ + (t : ℂ) • H) :=
    fun t ht => h₀.segment h₁ ht.1 ht.2
  set φ : ℝ → ℂ := fun t => (At t).det / (Bt t).det with hφdef
  set ψ₁ : ℝ → ℂ := fun t => ((At t)⁻¹ * A').trace - ((Bt t)⁻¹ * B').trace with hψ₁def
  set ψ₂ : ℝ → ℂ := fun t => -((At t)⁻¹ * A' * (At t)⁻¹ * A').trace +
    ((Bt t)⁻¹ * B' * (Bt t)⁻¹ * B').trace with hψ₂def
  have hφ : ∀ t, φ t = ratioDetC x y (T₀ + (t : ℂ) • H) := by
    intro t; simp only [φ, ratioDetC, hAt, hBt]
  have hAu : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsUnit (At t) ∧ ‖(At t)⁻¹‖ ≤ (1 - y)⁻¹ := by
    intro t ht; rw [hAt]; exact band_inv_sub (hband t ht) hy0 hy1
  have hBu : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsUnit (Bt t) ∧ ‖(Bt t)⁻¹‖ ≤ 1 := by
    intro t ht; rw [hBt]; exact band_inv_add (hband t ht) hx
  -- first derivative
  have dφ : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt φ (φ t * ψ₁ t) t := by
    intro t ht
    have hA := (isUnit_iff_isUnit_det _).1 (hAu t ht).1
    have hB := (isUnit_iff_isUnit_det _).1 (hBu t ht).1
    have dA := hasDerivAt_det_line A₀ A' t hA
    have dB := hasDerivAt_det_line B₀ B' t hB
    have hB0 : (Bt t).det ≠ 0 := hB.ne_zero
    refine (dA.div dB hB0).congr_deriv ?_
    simp only [φ, ψ₁, At, Bt] at hB0 ⊢
    field_simp
  -- second derivative
  have dψ₁ : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt ψ₁ (ψ₂ t) t := by
    intro t ht
    have iA := ((hasDerivAt_inv_line A₀ A' t (hAu t ht).1).mul_const A')
    have iB := ((hasDerivAt_inv_line B₀ B' t (hBu t ht).1).mul_const B')
    refine ((hasDerivAt_trace iA).sub (hasDerivAt_trace iB)).congr_deriv ?_
    simp only [ψ₂, Matrix.neg_mul, trace_neg, sub_neg_eq_add]
    rfl
  have dφ' : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun s => φ s * ψ₁ s) (φ t * ψ₁ t * ψ₁ t + φ t * ψ₂ t) t := by
    intro t ht
    exact ((dφ t ht).mul (dψ₁ t ht)).congr_deriv (by ring)
  -- bounds
  have hA'tb : TraceBound A' (y * r) := by
    have := hH.smul (-(y : ℂ))
    rwa [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy0] at this
  have hB'tb : TraceBound B' (x * r) := by
    have := hH.smul (x : ℂ)
    rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx] at this
  have hr : 0 ≤ r := hH.1
  have hyy : 0 ≤ (1 - y)⁻¹ := inv_nonneg.2 (by linarith)
  have bφ : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖φ t‖ ≤ 1 := by
    intro t ht; rw [hφ]; exact norm_ratioDetC_le_one hx hy0 hy1 (hband t ht)
  have bψ₁ : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖ψ₁ t‖ ≤ ratioC1 x y * r := by
    intro t ht
    have h1 : ‖((At t)⁻¹ * A').trace‖ ≤ (1 - y)⁻¹ * (y * r) :=
      (hA'tb.trace_le _).trans (mul_le_mul_of_nonneg_right (hAu t ht).2 hA'tb.1)
    have h2 : ‖((Bt t)⁻¹ * B').trace‖ ≤ 1 * (x * r) :=
      (hB'tb.trace_le _).trans (mul_le_mul_of_nonneg_right (hBu t ht).2 hB'tb.1)
    have e : ratioC1 x y * r = (1 - y)⁻¹ * (y * r) + 1 * (x * r) := by
      unfold ratioC1; field_simp
    rw [e]
    exact (norm_sub_le _ _).trans (add_le_add h1 h2)
  have bψ₂ : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖ψ₂ t‖ ≤ ((y / (1 - y)) ^ 2 + x ^ 2) * r ^ 2 := by
    intro t ht
    have nA := hA'tb.norm_le
    have nB := hB'tb.norm_le
    have h1 : ‖((At t)⁻¹ * A' * (At t)⁻¹ * A').trace‖ ≤ (y / (1 - y)) ^ 2 * r ^ 2 := by
      refine (hA'tb.trace_le _).trans ?_
      have : ‖(At t)⁻¹ * A' * (At t)⁻¹‖ ≤ (1 - y)⁻¹ * (y * r) * (1 - y)⁻¹ := by
        refine (l2_opNorm_mul _ _).trans ?_
        refine mul_le_mul ((l2_opNorm_mul _ _).trans ?_) (hAu t ht).2 (norm_nonneg _)
          (by positivity)
        exact mul_le_mul (hAu t ht).2 nA (norm_nonneg _) hyy
      calc ‖(At t)⁻¹ * A' * (At t)⁻¹‖ * (y * r) ≤
            (1 - y)⁻¹ * (y * r) * (1 - y)⁻¹ * (y * r) :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = (y / (1 - y)) ^ 2 * r ^ 2 := by rw [div_eq_mul_inv]; ring
    have h2 : ‖((Bt t)⁻¹ * B' * (Bt t)⁻¹ * B').trace‖ ≤ x ^ 2 * r ^ 2 := by
      refine (hB'tb.trace_le _).trans ?_
      have : ‖(Bt t)⁻¹ * B' * (Bt t)⁻¹‖ ≤ 1 * (x * r) * 1 := by
        refine (l2_opNorm_mul _ _).trans ?_
        refine mul_le_mul ((l2_opNorm_mul _ _).trans ?_) (hBu t ht).2 (norm_nonneg _)
          (by positivity)
        exact mul_le_mul (hBu t ht).2 nB (norm_nonneg _) zero_le_one
      calc ‖(Bt t)⁻¹ * B' * (Bt t)⁻¹‖ * (x * r) ≤ 1 * (x * r) * 1 * (x * r) :=
            mul_le_mul_of_nonneg_right this (by positivity)
        _ = x ^ 2 * r ^ 2 := by ring
    calc ‖ψ₂ t‖ ≤ ‖((At t)⁻¹ * A' * (At t)⁻¹ * A').trace‖ +
          ‖((Bt t)⁻¹ * B' * (Bt t)⁻¹ * B').trace‖ := by
          simp only [ψ₂]
          exact (norm_add_le _ _).trans (by rw [norm_neg])
      _ ≤ _ := by rw [add_mul]; exact add_le_add h1 h2
  have b2 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖φ t * ψ₁ t * ψ₁ t + φ t * ψ₂ t‖ ≤ ratioC2 x y * r ^ 2 := by
    intro t ht
    have h1 := bφ t ht
    have h2 := bψ₁ t ht
    have h3 := bψ₂ t ht
    have hc1 := ratioC1_nonneg hx hy0 hy1
    calc ‖φ t * ψ₁ t * ψ₁ t + φ t * ψ₂ t‖ ≤ ‖φ t‖ * ‖ψ₁ t‖ * ‖ψ₁ t‖ + ‖φ t‖ * ‖ψ₂ t‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul, norm_mul]
      _ ≤ 1 * (ratioC1 x y * r) * (ratioC1 x y * r) +
          1 * (((y / (1 - y)) ^ 2 + x ^ 2) * r ^ 2) := by
          gcongr
      _ = ratioC2 x y * r ^ 2 := by unfold ratioC2; ring
  -- Taylor
  have step1 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖φ t * ψ₁ t - φ 0 * ψ₁ 0‖ ≤ ratioC2 x y * r ^ 2 * (t - 0) :=
    norm_image_sub_le_of_norm_deriv_le_segment' (f := fun s => φ s * ψ₁ s)
      (fun t ht => (dφ' t ht).hasDerivWithinAt)
      (fun t ht => b2 t (Set.Ico_subset_Icc_self ht))
  set g : ℝ → ℂ := fun t => φ t - (t : ℂ) * (φ 0 * ψ₁ 0) with hgdef
  have dg : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g (φ t * ψ₁ t - φ 0 * ψ₁ 0) t := by
    intro t ht
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * (φ 0 * ψ₁ 0)) (1 * (φ 0 * ψ₁ 0)) t :=
      (hasDerivAt_id t).ofReal_comp.mul_const _
    exact ((dφ t ht).sub h1).congr_deriv (by ring)
  have hC0 : 0 ≤ ratioC2 x y * r ^ 2 := mul_nonneg (ratioC2_nonneg x y) (sq_nonneg r)
  have step2 := norm_image_sub_le_of_norm_deriv_le_segment' (f := g)
    (C := ratioC2 x y * r ^ 2) (fun t ht => (dg t ht).hasDerivWithinAt)
    (fun t ht => by
      have := step1 t (Set.Ico_subset_Icc_self ht)
      have ht1 : t - 0 ≤ 1 := by linarith [ht.2]
      calc _ ≤ ratioC2 x y * r ^ 2 * (t - 0) := this
        _ ≤ ratioC2 x y * r ^ 2 * 1 := mul_le_mul_of_nonneg_left ht1 hC0
        _ = _ := mul_one _)
    1 (Set.right_mem_Icc.2 zero_le_one)
  have hg1 : g 1 - g 0 = ratioDetC x y T₁ - ratioDetC x y T₀ - ratioDetDeriv x y T₀ H := by
    have e1 : φ 1 = ratioDetC x y T₁ := by rw [hφ]; simp [H]
    have e0 : φ 0 = ratioDetC x y T₀ := by rw [hφ]; simp
    have eψ : φ 0 * ψ₁ 0 = ratioDetDeriv x y T₀ H := by
      rw [e0]; simp [ψ₁, At, Bt, A₀, A', B₀, B', ratioDetDeriv]
    simp only [g]
    rw [eψ, e1, e0]
    push_cast
    ring
  rw [← hg1]
  simpa using step2

end BlockBand.Endpoints
