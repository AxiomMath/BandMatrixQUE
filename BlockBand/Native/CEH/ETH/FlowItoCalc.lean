module

public import BlockBand.Native.CEH.Flow.ResolventCalc
public import BlockBand.External.CEH.SourceObservables

/-!
# CEH ETH: deterministic calculus of two-resolvent test functions

For a finite-dimensional real normed space `V`, two affine families `y ↦ A₁ + L₁ y`,
`y ↦ A₂ + L₂ y` of complex matrices (in the application they share the matrix part and differ in
the spectral shift) and fixed matrices `K`, `A`, the test function is
`invTest2 A₁ L₁ A₂ L₂ K A y = Re tr(K R₁(y) A R₂(y))`, `R_i(y) = (A_i + L_i y)⁻¹`.

At every `y` where both `A_i + L_i y` are invertible:
* `contDiffAt_invTest2`: `invTest2` is `C^n` for every `n`;
* `fderiv_invTest2`: `D invTest2(y)[u] = -Re tr(K (R₁ L₁u R₁ A R₂ + R₁ A R₂ L₂u R₂))`;
* `fderiv_fderiv_invTest2`: `D² invTest2(y)[u, w] = Re tr(K S(u, w))` with the six-term sum
  `S(u, w) = R₁L₁uR₁L₁wR₁AR₂ + R₁L₁wR₁L₁uR₁AR₂ + R₁L₁wR₁AR₂L₂uR₂ + R₁L₁uR₁AR₂L₂wR₂
    + R₁AR₂L₂uR₂L₂wR₂ + R₁AR₂L₂wR₂L₂uR₂`
  (two second-order terms in each resolvent and the two mixed terms).

* `sum_mul_hermBasis_mul_mul`: `∑_x P (E_x X E_x) Q = tr(X) · P Q`;
* `sum_hermBasis_mul_mul_avg`: `(1/N) ∑_x E_x X E_x = ⟨X⟩ · 1`;
* `sum_trace_mul_hermBasis_mul_hermBasis`: `∑_x tr(P E_x Q E_x) = tr P · tr Q`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.ETH
open Matrix Filter Topology BlockBand.SourceProcess.Stochastic.Dyson
open BlockBand.Native.CEH.Flow

section Calc

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- `y ↦ Re tr(K (A₁ + L₁ y)⁻¹ A (A₂ + L₂ y)⁻¹)`. -/
def invTest2 (A₁ : Matrix ι ι ℂ) (L₁ : V →ₗ[ℝ] Matrix ι ι ℂ) (A₂ : Matrix ι ι ℂ)
    (L₂ : V →ₗ[ℝ] Matrix ι ι ℂ) (K A : Matrix ι ι ℂ) (y : V) : ℝ :=
  reTr K ((A₁ + L₁ y)⁻¹ * A * (A₂ + L₂ y)⁻¹)

variable (A₁ A₂ : Matrix ι ι ℂ) (L₁ L₂ : V →ₗ[ℝ] Matrix ι ι ℂ) (K A : Matrix ι ι ℂ)

theorem hasFDerivAt_invTest2 {v : V} (h₁ : IsUnit (A₁ + L₁ v).det)
    (h₂ : IsUnit (A₂ + L₂ v).det) :
    ∃ D : V →L[ℝ] ℝ, HasFDerivAt (invTest2 A₁ L₁ A₂ L₂ K A) D v ∧
      ∀ u, D u = -reTr K ((A₁ + L₁ v)⁻¹ * L₁ u * (A₁ + L₁ v)⁻¹ * A * (A₂ + L₂ v)⁻¹ +
        (A₁ + L₁ v)⁻¹ * A * (A₂ + L₂ v)⁻¹ * L₂ u * (A₂ + L₂ v)⁻¹) := by
  obtain ⟨D₁, hD₁, hD₁u⟩ := hasFDerivAt_inv_affine A₁ L₁ h₁
  obtain ⟨D₂, hD₂, hD₂u⟩ := hasFDerivAt_inv_affine A₂ L₂ h₂
  obtain ⟨P, hP, hPu⟩ : ∃ P : V →L[ℝ] Matrix ι ι ℂ,
      HasFDerivAt (fun y => (A₁ + L₁ y)⁻¹ * A * (A₂ + L₂ y)⁻¹) P v ∧
      ∀ u, P u = (A₁ + L₁ v)⁻¹ * A * D₂ u + D₁ u * A * (A₂ + L₂ v)⁻¹ :=
    ⟨_, (hD₁.mul_const' A).mul' hD₂, fun u => rfl⟩
  set T := (reTrLin K).toContinuousLinearMap
  refine ⟨T.comp P, T.hasFDerivAt.comp v hP, fun u => ?_⟩
  change reTr K (P u) = _
  rw [hPu, hD₁u, hD₂u, ← reTr_neg]
  congr 1
  simp only [Matrix.mul_neg, Matrix.neg_mul, neg_add, Matrix.mul_assoc]
  abel

theorem contDiffAt_invTest2 {v : V} (h₁ : IsUnit (A₁ + L₁ v).det)
    (h₂ : IsUnit (A₂ + L₂ v).det) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (invTest2 A₁ L₁ A₂ L₂ K A) v := by
  have h : ContDiffAt ℝ n (fun y => (A₁ + L₁ y)⁻¹ * A * (A₂ + L₂ y)⁻¹) v :=
    ((contDiffAt_inv_affine A₁ L₁ h₁).mul contDiffAt_const).mul (contDiffAt_inv_affine A₂ L₂ h₂)
  exact ((reTrLin K).toContinuousLinearMap.contDiff.contDiffAt).comp v h

theorem fderiv_invTest2 {v : V} (h₁ : IsUnit (A₁ + L₁ v).det)
    (h₂ : IsUnit (A₂ + L₂ v).det) (u : V) :
    fderiv ℝ (invTest2 A₁ L₁ A₂ L₂ K A) v u =
      -reTr K ((A₁ + L₁ v)⁻¹ * L₁ u * (A₁ + L₁ v)⁻¹ * A * (A₂ + L₂ v)⁻¹ +
        (A₁ + L₁ v)⁻¹ * A * (A₂ + L₂ v)⁻¹ * L₂ u * (A₂ + L₂ v)⁻¹) := by
  obtain ⟨D, hD, hDu⟩ := hasFDerivAt_invTest2 A₁ A₂ L₁ L₂ K A h₁ h₂
  rw [hD.fderiv, hDu]

/-- The six-term second-order matrix `S(u, w)` (`R_i = (A_i + L_i v)⁻¹`). -/
def secondTerm2 (R₁ R₂ A U₁ W₁ U₂ W₂ : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  R₁ * U₁ * R₁ * W₁ * R₁ * A * R₂ + R₁ * W₁ * R₁ * U₁ * R₁ * A * R₂ +
    R₁ * W₁ * R₁ * A * R₂ * U₂ * R₂ + R₁ * U₁ * R₁ * A * R₂ * W₂ * R₂ +
    R₁ * A * R₂ * U₂ * R₂ * W₂ * R₂ + R₁ * A * R₂ * W₂ * R₂ * U₂ * R₂

/-- Derivative of the first partial `v ↦ -Re tr(K (R₁ L₁w R₁ A R₂ + R₁ A R₂ L₂w R₂))`. -/
theorem hasFDerivAt_firstPartial2 (w : V) {v : V} (h₁ : IsUnit (A₁ + L₁ v).det)
    (h₂ : IsUnit (A₂ + L₂ v).det) :
    ∃ D : V →L[ℝ] ℝ, HasFDerivAt (fun y => -reTr K ((A₁ + L₁ y)⁻¹ * L₁ w * (A₁ + L₁ y)⁻¹ * A *
        (A₂ + L₂ y)⁻¹ + (A₁ + L₁ y)⁻¹ * A * (A₂ + L₂ y)⁻¹ * L₂ w * (A₂ + L₂ y)⁻¹)) D v ∧
      ∀ u, D u = reTr K (secondTerm2 (A₁ + L₁ v)⁻¹ (A₂ + L₂ v)⁻¹ A (L₁ u) (L₁ w) (L₂ u)
        (L₂ w)) := by
  obtain ⟨D₁, hD₁, hD₁u⟩ := hasFDerivAt_inv_affine A₁ L₁ h₁
  obtain ⟨D₂, hD₂, hD₂u⟩ := hasFDerivAt_inv_affine A₂ L₂ h₂
  set R₁ := (A₁ + L₁ v)⁻¹
  set R₂ := (A₂ + L₂ v)⁻¹
  obtain ⟨P, hP, hPu⟩ : ∃ P : V →L[ℝ] Matrix ι ι ℂ,
      HasFDerivAt (fun y => (A₁ + L₁ y)⁻¹ * L₁ w * (A₁ + L₁ y)⁻¹ * A * (A₂ + L₂ y)⁻¹ +
        (A₁ + L₁ y)⁻¹ * A * (A₂ + L₂ y)⁻¹ * L₂ w * (A₂ + L₂ y)⁻¹) P v ∧
      ∀ u, P u = (R₁ * L₁ w * R₁ * A * D₂ u +
          (R₁ * L₁ w * D₁ u + D₁ u * L₁ w * R₁) * A * R₂) +
        (R₁ * A * R₂ * L₂ w * D₂ u + (R₁ * A * D₂ u + D₁ u * A * R₂) * L₂ w * R₂) :=
    ⟨_, (((((hD₁.mul_const' (L₁ w)).mul' hD₁).mul_const' A).mul' hD₂).add
      ((((hD₁.mul_const' A).mul' hD₂).mul_const' (L₂ w)).mul' hD₂)), fun u => rfl⟩
  set T := (reTrLin K).toContinuousLinearMap
  refine ⟨-(T.comp P), (T.hasFDerivAt.comp v hP).neg, fun u => ?_⟩
  change -reTr K (P u) = _
  rw [hPu, hD₁u, hD₂u, ← reTr_neg]
  congr 1
  simp only [secondTerm2, Matrix.mul_neg, Matrix.neg_mul, Matrix.add_mul,
    neg_add, neg_neg, Matrix.mul_assoc]
  abel

/-- **Second derivative** of `invTest2`. -/
theorem fderiv_fderiv_invTest2 {v : V} (h₁ : IsUnit (A₁ + L₁ v).det)
    (h₂ : IsUnit (A₂ + L₂ v).det) (u w : V) :
    fderiv ℝ (fderiv ℝ (invTest2 A₁ L₁ A₂ L₂ K A)) v u w =
      reTr K (secondTerm2 (A₁ + L₁ v)⁻¹ (A₂ + L₂ v)⁻¹ A (L₁ u) (L₁ w) (L₂ u) (L₂ w)) := by
  obtain ⟨D, hD, hDu⟩ := hasFDerivAt_firstPartial2 A₁ A₂ L₁ L₂ K A w h₁ h₂
  have hev : (fun y => fderiv ℝ (invTest2 A₁ L₁ A₂ L₂ K A) y w) =ᶠ[𝓝 v]
      (fun y => -reTr K ((A₁ + L₁ y)⁻¹ * L₁ w * (A₁ + L₁ y)⁻¹ * A * (A₂ + L₂ y)⁻¹ +
        (A₁ + L₁ y)⁻¹ * A * (A₂ + L₂ y)⁻¹ * L₂ w * (A₂ + L₂ y)⁻¹)) := by
    filter_upwards [(isOpen_isUnit_det A₁ L₁).mem_nhds h₁,
      (isOpen_isUnit_det A₂ L₂).mem_nhds h₂] with y hy₁ hy₂
    exact fderiv_invTest2 A₁ A₂ L₁ L₂ K A hy₁ hy₂ w
  have h2 := hD.congr_of_eventuallyEq hev
  have hdiff : DifferentiableAt ℝ (fderiv ℝ (invTest2 A₁ L₁ A₂ L₂ K A)) v :=
    ((contDiffAt_invTest2 A₁ A₂ L₁ L₂ K A h₁ h₂ (n := 2)).fderiv_right (m := 1)
      (by norm_num)).differentiableAt (by norm_num)
  have h1 := (ContinuousLinearMap.apply ℝ ℝ w).hasFDerivAt.comp v hdiff.hasFDerivAt
  rw [← hDu u, ← h1.unique h2]
  rfl

end Calc

section Basis

variable {N : ℕ}

/-- `∑_x P (E_x X E_x) Q = tr(X) · P Q`. -/
theorem sum_mul_hermBasis_mul_mul (P X Q : Matrix (Fin N) (Fin N) ℂ) :
    ∑ x, P * (hermBasis x * X * hermBasis x) * Q = X.trace • (P * Q) := by
  rw [← Finset.sum_mul, ← Finset.mul_sum, sum_hermBasis_mul_mul, Matrix.mul_smul,
    Matrix.mul_one, Matrix.smul_mul]

/-- `(1/N) ∑_x E_x X E_x = ⟨X⟩ · 1`. -/
theorem sum_hermBasis_mul_mul_avg (X : Matrix (Fin N) (Fin N) ℂ) :
    ((N : ℂ)⁻¹) • ∑ x, hermBasis x * X * hermBasis x =
      BlockBand.External.CEH.normalizedTrace X • (1 : Matrix (Fin N) (Fin N) ℂ) := by
  rw [sum_hermBasis_mul_mul, smul_smul]
  rfl

/-- `∑_x tr(P E_x Q E_x) = tr P · tr Q`. -/
theorem sum_trace_mul_hermBasis_mul_hermBasis (P Q : Matrix (Fin N) (Fin N) ℂ) :
    ∑ x, trace (P * hermBasis x * Q * hermBasis x) = trace P * trace Q := by
  have e : ∀ x, P * hermBasis x * Q * hermBasis x = P * (hermBasis x * Q * hermBasis x) * 1 := by
    intro x; simp only [Matrix.mul_one, Matrix.mul_assoc]
  simp only [e]
  rw [← trace_sum, sum_mul_hermBasis_mul_mul, Matrix.mul_one, trace_smul, smul_eq_mul, mul_comm]

end Basis

end BlockBand.Native.CEH.ETH
