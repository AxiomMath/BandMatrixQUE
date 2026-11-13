module

public import BlockBand.SourceProcess.Stochastic.Dyson.BrownianSemimartingale

/-!
# CEH flow: deterministic calculus of resolvent test functions

For a finite-dimensional real normed space `V`, an affine family `y ↦ A₀ + L y` of complex
matrices and a weight matrix `K`, the test function `invTest A₀ L K y = Re tr(K (A₀ + L y)⁻¹)`
(`reTr K`). Every real-linear functional of a matrix used later is of this form:
`Re⟨X B⟩ = reTr (N⁻¹ B) X`, `Im⟨X B⟩ = reTr (-i N⁻¹ B) X`, `Re x*Xy = reTr (y x*) X`,
`Im x*Xy = reTr (-i y x*) X`.

At every `y` where `A₀ + L y` is invertible (`R = (A₀ + L y)⁻¹`):
* `contDiffAt_invTest`: `invTest` is `C^n` for every `n`;
* `fderiv_invTest`: `D invTest(y)[u] = -Re tr(K R (L u) R)`;
* `fderiv_fderiv_invTest`: `D² invTest(y)[u, w] = Re tr(K (R Lu R Lw R + R Lw R Lu R))`.
The matrix norm (`Matrix.linftyOpNormedRing`) is used only inside proofs.

* `sum_hermBasis_mul_mul`: `∑_x E_x X E_x = tr(X) · 1` (every complex `X`);
* `sum_trace_mul_trace`: `∑_x tr(E_x A) tr(E_x C) = tr(A C)`;
* `sum_normSq_trace`: `∑_x |tr(E_x M)|² = Re tr(M Mᴴ)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.Flow
open Matrix Filter Topology BlockBand.SourceProcess.Stochastic.Dyson
open scoped ComplexConjugate

section Calc

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- `ℓ_K(X) = Re tr(K X)`. -/
def reTr (K X : Matrix ι ι ℂ) : ℝ := (trace (K * X)).re

/-- `reTr K` as an `ℝ`-linear map. -/
def reTrLin (K : Matrix ι ι ℂ) : Matrix ι ι ℂ →ₗ[ℝ] ℝ where
  toFun := reTr K
  map_add' X Y := by simp [reTr, Matrix.mul_add, trace_add]
  map_smul' r X := by
    simp only [reTr, RingHom.id_apply, smul_eq_mul]
    rw [Matrix.mul_smul, trace_smul, Complex.real_smul, Complex.re_ofReal_mul]

omit [DecidableEq ι] in
theorem reTr_add (K X Y : Matrix ι ι ℂ) : reTr K (X + Y) = reTr K X + reTr K Y :=
  (reTrLin K).map_add X Y

omit [DecidableEq ι] in
theorem reTr_neg (K X : Matrix ι ι ℂ) : reTr K (-X) = -reTr K X :=
  (reTrLin K).map_neg X

omit [DecidableEq ι] in
theorem reTr_ofReal_smul (K X : Matrix ι ι ℂ) (r : ℝ) : reTr K ((r : ℂ) • X) = r * reTr K X := by
  rw [Complex.coe_smul]; exact (reTrLin K).map_smul r X

omit [DecidableEq ι] in
theorem reTr_sum {κ : Type} (S : Finset κ) (K : Matrix ι ι ℂ) (X : κ → Matrix ι ι ℂ) :
    reTr K (∑ k ∈ S, X k) = ∑ k ∈ S, reTr K (X k) :=
  map_sum (reTrLin K) X S

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- Derivative of the inverse along an affine family. -/
theorem hasFDerivAt_inv_affine (A₀ : Matrix ι ι ℂ) (L : V →ₗ[ℝ] Matrix ι ι ℂ) {v : V}
    (hv : IsUnit (A₀ + L v).det) :
    ∃ D : V →L[ℝ] Matrix ι ι ℂ, HasFDerivAt (fun y => (A₀ + L y)⁻¹) D v ∧
      ∀ u, D u = -((A₀ + L v)⁻¹ * L u * (A₀ + L v)⁻¹) := by
  set L' := LinearMap.toContinuousLinearMap L
  have hA : HasFDerivAt (fun y => A₀ + L y) L' v :=
    (L'.hasFDerivAt (x := v)).const_add A₀
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).mpr hv
  have hinv := hasFDerivAt_ringInverse (𝕜 := ℝ) u
  rw [hu] at hinv
  have hc := hinv.comp v hA
  have hfun : (fun y => (A₀ + L y)⁻¹) = (Ring.inverse ∘ fun y => A₀ + L y) := by
    funext w
    simp [Matrix.nonsing_inv_eq_ringInverse]
  rw [hfun]
  refine ⟨_, hc, fun w => ?_⟩
  rw [← Ring.inverse_unit u, hu, ← Matrix.nonsing_inv_eq_ringInverse]
  rfl

theorem contDiffAt_inv_affine (A₀ : Matrix ι ι ℂ) (L : V →ₗ[ℝ] Matrix ι ι ℂ) {v : V}
    (hv : IsUnit (A₀ + L v).det) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (fun y => (A₀ + L y)⁻¹) v := by
  have hL : ContDiff ℝ n (fun y => A₀ + L y) :=
    contDiff_const.add ((LinearMap.toContinuousLinearMap L).contDiff (n := n))
  simp_rw [Matrix.nonsing_inv_eq_ringInverse]
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).mpr hv
  have h := contDiffAt_ringInverse ℝ (n := n) u
  rw [hu] at h
  exact h.comp v hL.contDiffAt

/-- `y ↦ Re tr(K (A₀ + L y)⁻¹)`. -/
def invTest (A₀ : Matrix ι ι ℂ) (L : V →ₗ[ℝ] Matrix ι ι ℂ) (K : Matrix ι ι ℂ) (y : V) : ℝ :=
  reTr K ((A₀ + L y)⁻¹)

theorem hasFDerivAt_invTest (A₀ : Matrix ι ι ℂ) (L : V →ₗ[ℝ] Matrix ι ι ℂ) (K : Matrix ι ι ℂ)
    {v : V} (hv : IsUnit (A₀ + L v).det) :
    ∃ D : V →L[ℝ] ℝ, HasFDerivAt (invTest A₀ L K) D v ∧
      ∀ u, D u = -reTr K ((A₀ + L v)⁻¹ * L u * (A₀ + L v)⁻¹) := by
  obtain ⟨D, hD, hDu⟩ := hasFDerivAt_inv_affine A₀ L hv
  set T := (reTrLin K).toContinuousLinearMap
  refine ⟨T.comp D, T.hasFDerivAt.comp v hD, fun u => ?_⟩
  change reTr K (D u) = _
  rw [hDu, reTr_neg]

theorem contDiffAt_invTest (A₀ : Matrix ι ι ℂ) (L : V →ₗ[ℝ] Matrix ι ι ℂ) (K : Matrix ι ι ℂ)
    {v : V} (hv : IsUnit (A₀ + L v).det) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (invTest A₀ L K) v :=
  ((reTrLin K).toContinuousLinearMap.contDiff.contDiffAt).comp v (contDiffAt_inv_affine A₀ L hv)

theorem fderiv_invTest (A₀ : Matrix ι ι ℂ) (L : V →ₗ[ℝ] Matrix ι ι ℂ) (K : Matrix ι ι ℂ)
    {v : V} (hv : IsUnit (A₀ + L v).det) (u : V) :
    fderiv ℝ (invTest A₀ L K) v u = -reTr K ((A₀ + L v)⁻¹ * L u * (A₀ + L v)⁻¹) := by
  obtain ⟨D, hD, hDu⟩ := hasFDerivAt_invTest A₀ L K hv
  rw [hD.fderiv, hDu]

theorem isOpen_isUnit_det (A₀ : Matrix ι ι ℂ) (L : V →ₗ[ℝ] Matrix ι ι ℂ) :
    IsOpen {v : V | IsUnit (A₀ + L v).det} := by
  have hc : Continuous fun v : V => (A₀ + L v).det :=
    (continuous_const.add (LinearMap.toContinuousLinearMap L).continuous).matrix_det
  simp_rw [isUnit_iff_ne_zero]
  exact isOpen_ne.preimage hc

/-- Derivative of the first partial `v ↦ -Re tr(K R L w R)`. -/
theorem hasFDerivAt_firstPartial (A₀ : Matrix ι ι ℂ) (L : V →ₗ[ℝ] Matrix ι ι ℂ)
    (K : Matrix ι ι ℂ) (w : V) {v : V} (hv : IsUnit (A₀ + L v).det) :
    ∃ D : V →L[ℝ] ℝ, HasFDerivAt (fun y => -reTr K ((A₀ + L y)⁻¹ * L w * (A₀ + L y)⁻¹)) D v ∧
      ∀ u, D u = reTr K ((A₀ + L v)⁻¹ * L u * (A₀ + L v)⁻¹ * L w * (A₀ + L v)⁻¹ +
        (A₀ + L v)⁻¹ * L w * (A₀ + L v)⁻¹ * L u * (A₀ + L v)⁻¹) := by
  obtain ⟨D, hD, hDu⟩ := hasFDerivAt_inv_affine A₀ L hv
  obtain ⟨P, hP, hPu⟩ : ∃ P : V →L[ℝ] Matrix ι ι ℂ,
      HasFDerivAt (fun y => (A₀ + L y)⁻¹ * L w * (A₀ + L y)⁻¹) P v ∧
      ∀ u, P u = (A₀ + L v)⁻¹ * L w * D u + D u * L w * (A₀ + L v)⁻¹ :=
    ⟨_, (hD.mul_const' (L w)).mul' hD, fun u => rfl⟩
  set T := (reTrLin K).toContinuousLinearMap
  refine ⟨-(T.comp P), (T.hasFDerivAt.comp v hP).neg, fun u => ?_⟩
  change -reTr K (P u) = _
  rw [hPu, hDu, ← reTr_neg]
  congr 1
  simp only [Matrix.mul_neg, Matrix.neg_mul, neg_add, neg_neg, Matrix.mul_assoc]
  abel

/-- **Second derivative** of `invTest`. -/
theorem fderiv_fderiv_invTest (A₀ : Matrix ι ι ℂ) (L : V →ₗ[ℝ] Matrix ι ι ℂ) (K : Matrix ι ι ℂ)
    {v : V} (hv : IsUnit (A₀ + L v).det) (u w : V) :
    fderiv ℝ (fderiv ℝ (invTest A₀ L K)) v u w =
      reTr K ((A₀ + L v)⁻¹ * L u * (A₀ + L v)⁻¹ * L w * (A₀ + L v)⁻¹ +
        (A₀ + L v)⁻¹ * L w * (A₀ + L v)⁻¹ * L u * (A₀ + L v)⁻¹) := by
  obtain ⟨D, hD, hDu⟩ := hasFDerivAt_firstPartial A₀ L K w hv
  have hev : (fun y => fderiv ℝ (invTest A₀ L K) y w) =ᶠ[𝓝 v]
      (fun y => -reTr K ((A₀ + L y)⁻¹ * L w * (A₀ + L y)⁻¹)) := by
    filter_upwards [(isOpen_isUnit_det A₀ L).mem_nhds hv] with y hy
    exact fderiv_invTest A₀ L K hy w
  have h2 := hD.congr_of_eventuallyEq hev
  have hdiff : DifferentiableAt ℝ (fderiv ℝ (invTest A₀ L K)) v :=
    ((contDiffAt_invTest A₀ L K hv (n := 2)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)
  have h1 := (ContinuousLinearMap.apply ℝ ℝ w).hasFDerivAt.comp v hdiff.hasFDerivAt
  rw [← hDu u, ← h1.unique h2]
  rfl

end Calc
section Basis

variable {N : ℕ}

/-- `∑_x E_x X E_x = tr(X) · 1`. -/
theorem sum_hermBasis_mul_mul (X : Matrix (Fin N) (Fin N) ℂ) :
    ∑ x, hermBasis x * X * hermBasis x = X.trace • (1 : Matrix (Fin N) (Fin N) ℂ) := by
  ext a d
  have h : ∀ x : Fin N × Fin N, (hermBasis x * X * hermBasis x) a d =
      ∑ b, ∑ c, X b c * (hermBasis x a b * hermBasis x c d) := by
    intro x
    simp only [mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by ring
  rw [Matrix.sum_apply, Finset.sum_congr rfl fun x _ => h x]
  have h2 : ∑ x : Fin N × Fin N, ∑ b, ∑ c, X b c * (hermBasis x a b * hermBasis x c d) =
      ∑ b, ∑ c, X b c * ∑ x, hermBasis x a b * hermBasis x c d := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  rw [h2]
  simp only [sum_hermBasis_mul_hermBasis, Matrix.smul_apply, one_apply, smul_eq_mul]
  by_cases had : a = d
  · subst had; simp [trace]
  · simp [had]

/-- `∑_x tr(E_x A) tr(E_x C) = tr(A C)`. -/
theorem sum_trace_mul_trace (A C : Matrix (Fin N) (Fin N) ℂ) :
    ∑ x, trace (hermBasis x * A) * trace (hermBasis x * C) = trace (A * C) := by
  conv_rhs => rw [← sum_trace_smul_hermBasis C]
  simp only [Matrix.mul_sum, Matrix.mul_smul, trace_sum, trace_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [trace_mul_comm A, mul_comm]

/-- `∑_x |tr(E_x M)|² = Re tr(M Mᴴ)`. -/
theorem sum_normSq_trace (M : Matrix (Fin N) (Fin N) ℂ) :
    ∑ x, Complex.normSq (trace (hermBasis x * M)) = (trace (M * Mᴴ)).re := by
  have hc : ∀ x, conj (trace (hermBasis x * M)) = trace (hermBasis x * Mᴴ) := by
    intro x
    change star (trace (hermBasis x * M)) = _
    rw [← trace_conjTranspose, conjTranspose_mul, (hermBasis_isHermitian x).eq, trace_mul_comm]
  rw [← sum_trace_mul_trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← hc, Complex.mul_conj, Complex.ofReal_re]

end Basis

end BlockBand.Native.CEH.Flow
