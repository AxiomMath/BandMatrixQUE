module
public import BlockBand.SourceProcess.Stochastic.SourceSDE.GenCalculus
public import BlockBand.SourceProcess.Stochastic.SourceAlgebra.TraceLyapunov
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Real-bilinear matrix forms and smoothness of the source coefficients

Support for the well-posedness of the finite source equation. Matrices carry the Frobenius
norm (local instance). The real-bilinear continuous maps

* `mulBil : (X, Y) ↦ X Y` (rectangular),
* `gramBil D : (X, Y) ↦ X 𝖣 Yᴴ`,
* `reInner : (X, Y) ↦ Re Tr(Xᴴ Y)` (so `reInner X X = ‖X‖²`, `reInner_self`),
* `reMul : (z, w) ↦ Re(z̄ w)` (so `reMul z z = ‖z‖²`),

and the real-linear `traceCLM`, feed the generator calculus (`vecGen`).
`contDiff_sourceDrift`, `contDiff_sourceDiffusion`: the coefficients of the finite source equation
are `C^∞`, hence locally Lipschitz (`locallyLipschitz_sourceDrift`,
`locallyLipschitz_sourceDiffusion`), the hypothesis of local well-posedness and nonexplosion.
-/

namespace BlockBand.SourceProcess.Stochastic.SourceSDE
open Matrix BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.SourceAlgebra

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

/-- A real-bilinear map on finite-dimensional spaces as a continuous bilinear map. -/
def toCLM₂ {F₁ F₂ F₃ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
    [FiniteDimensional ℝ F₁] [FiniteDimensional ℝ F₂] (f : F₁ →ₗ[ℝ] F₂ →ₗ[ℝ] F₃) :
    F₁ →L[ℝ] F₂ →L[ℝ] F₃ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (F₂ →ₗ[ℝ] F₃) ≃ₗ[ℝ] (F₂ →L[ℝ] F₃)).toLinearMap ∘ₗ f)

theorem toCLM₂_apply {F₁ F₂ F₃ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
    [FiniteDimensional ℝ F₁] [FiniteDimensional ℝ F₂] (f : F₁ →ₗ[ℝ] F₂ →ₗ[ℝ] F₃) (x : F₁)
    (y : F₂) : toCLM₂ f x y = f x y := rfl

/-- A real-linear map on a finite-dimensional space as a continuous linear map. -/
def toCLM {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₁] (f : F₁ →ₗ[ℝ] F₂) :
    F₁ →L[ℝ] F₂ :=
  LinearMap.toContinuousLinearMap f

variable {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]

/-- Matrix multiplication as a continuous real-bilinear map. -/
def mulBil :=
  toCLM₂ (F₁ := Matrix l m ℂ) (F₂ := Matrix m n ℂ) (F₃ := Matrix l n ℂ)
    (LinearMap.mk₂ ℝ (fun X Y => X * Y) (fun _ _ _ => Matrix.add_mul _ _ _)
    (fun _ _ _ => Matrix.smul_mul _ _ _) (fun _ _ _ => Matrix.mul_add _ _ _)
    (fun _ _ _ => Matrix.mul_smul _ _ _))

theorem mulBil_apply (X : Matrix l m ℂ) (Y : Matrix m n ℂ) : mulBil X Y = X * Y := rfl

/-- `(X, Y) ↦ X 𝖣 Yᴴ` as a continuous real-bilinear map. -/
def gramBil (D : Matrix n n ℂ) :=
  toCLM₂ (F₁ := Matrix m n ℂ) (F₂ := Matrix m n ℂ) (F₃ := Matrix m m ℂ)
    (LinearMap.mk₂ ℝ (fun X Y => X * D * Yᴴ)
    (fun _ _ _ => by simp only [Matrix.add_mul])
    (fun _ _ _ => by simp only [Matrix.smul_mul])
    (fun _ _ _ => by simp only [conjTranspose_add, Matrix.mul_add])
    (fun r _ _ => by simp only [conjTranspose_smul, star_trivial, Matrix.mul_smul]))

theorem gramBil_apply (D : Matrix n n ℂ) (X Y : Matrix m n ℂ) : gramBil D X Y = X * D * Yᴴ :=
  rfl

/-- `(X, Y) ↦ Re Tr(Xᴴ Y)` as a continuous real-bilinear form. -/
def reInner :=
  toCLM₂ (F₁ := Matrix m n ℂ) (F₂ := Matrix m n ℂ) (F₃ := ℝ)
    (LinearMap.mk₂ ℝ (fun X Y => (Xᴴ * Y).trace.re)
    (fun _ _ _ => by simp only [conjTranspose_add, Matrix.add_mul, trace_add, Complex.add_re])
    (fun _ _ _ => by
      simp only [conjTranspose_smul, star_trivial, Matrix.smul_mul, trace_smul, Complex.smul_re])
    (fun _ _ _ => by simp only [Matrix.mul_add, trace_add, Complex.add_re])
    (fun _ _ _ => by simp only [Matrix.mul_smul, trace_smul, Complex.smul_re]))

theorem reInner_apply (X Y : Matrix m n ℂ) : reInner X Y = (Xᴴ * Y).trace.re := rfl

theorem reInner_self (X : Matrix m n ℂ) : reInner X X = ‖X‖ ^ 2 := by
  rw [reInner_apply, ← frob_sq_eq_trace, Complex.ofReal_re]

theorem reInner_comm (X Y : Matrix m n ℂ) : reInner Y X = reInner X Y := by
  rw [reInner_apply, reInner_apply, ← conjTranspose_conjTranspose X, ← conjTranspose_mul,
    trace_conjTranspose, conjTranspose_conjTranspose, Complex.star_def, Complex.conj_re]

/-- `(z, w) ↦ Re(z̄ w)` as a continuous real-bilinear form. -/
def reMul : ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
  toCLM₂ (F₁ := ℂ) (F₂ := ℂ) (F₃ := ℝ) (LinearMap.mk₂ ℝ (fun z w => (star z * w).re)
    (fun _ _ _ => by simp only [star_add, add_mul, Complex.add_re])
    (fun _ _ _ => by simp only [star_smul, star_trivial, smul_mul_assoc, Complex.smul_re])
    (fun _ _ _ => by simp only [mul_add, Complex.add_re])
    (fun _ _ _ => by simp only [mul_smul_comm, Complex.smul_re]))

theorem reMul_apply (z w : ℂ) : reMul z w = (star z * w).re := rfl

theorem reMul_self (z : ℂ) : reMul z z = ‖z‖ ^ 2 := by
  rw [reMul_apply, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

theorem reMul_comm (z w : ℂ) : reMul w z = reMul z w := by
  rw [reMul_apply, reMul_apply, ← Complex.conj_re (star z * w)]
  simp [mul_comm]

/-- The trace as a continuous real-linear map. -/
def traceCLM :=
  toCLM (F₁ := Matrix m m ℂ) (F₂ := ℂ) ((Matrix.traceLinearMap m ℂ ℂ).restrictScalars ℝ)

theorem traceCLM_apply (X : Matrix m m ℂ) : traceCLM X = X.trace := rfl

/-!
### Measurable-space compatibility of the Frobenius structure

The Frobenius topology is definitionally the product topology (`frobTopology_eq`), but type-class
search does not see it; these two instances (used locally) bridge the two presentations.
-/

theorem frobTopology_eq :
    (Matrix.frobeniusNormedAddCommGroup (m := m) (n := n)
      (α := ℂ)).toSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      instTopologicalSpaceMatrix := rfl

/-- Borel structure of matrices for the Frobenius topology. -/
theorem frobBorelSpace : @BorelSpace (Matrix m n ℂ)
    (Matrix.frobeniusNormedAddCommGroup (m := m) (n := n)
      (α := ℂ)).toSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace _ :=
  inferInstanceAs (BorelSpace (Matrix m n ℂ))

/-- Pseudo-metrizability of the product topology of matrices. -/
theorem matrixPseudoMetrizable : TopologicalSpace.PseudoMetrizableSpace (Matrix m n ℂ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (m → n → ℂ))

/-!
### Smoothness of the source coefficients
-/

variable {ι c : Type*} [Fintype ι] [DecidableEq ι] [Fintype c]

omit [DecidableEq ι] in
theorem contDiff_gramProjection (P : Matrix ι ι ℂ) (D : Matrix c c ℂ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (fun V : Matrix ι c ℂ => gramProjection P V D) := by
  have h : ContDiff ℝ k (fun V : Matrix ι c ℂ => P + gramBil D V V) :=
    contDiff_const.add (contDiff_bilin _ contDiff_id contDiff_id)
  exact h

omit [DecidableEq ι] in
theorem contDiff_sourceDrift (D0 : ℝ) (Naux : ℕ) (P : Matrix ι ι ℂ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (fun V : Matrix ι c ℂ => sourceDrift D0 Naux P V) := by
  have h : ContDiff ℝ k (fun V : Matrix ι c ℂ =>
      (-(D0 * Naux / 4) : ℝ) • mulBil P V) :=
    (contDiff_bilin _ contDiff_const contDiff_id).const_smul _
  have e : (fun V : Matrix ι c ℂ => sourceDrift D0 Naux P V) =
      fun V => (-(D0 * Naux / 4) : ℝ) • mulBil P V := funext fun V => by
    rw [sourceDrift, mulBil_apply, ← Complex.coe_smul]
  rw [e]
  exact h

theorem contDiff_sourceDiffusion (D0 : ℝ) (P : Matrix ι ι ℂ) (D : Matrix c c ℂ)
    (a : SourceNoise ι) {k : WithTop ℕ∞} :
    ContDiff ℝ k (fun V : Matrix ι c ℂ => sourceDiffusion D0 P D a V) := by
  have h : ContDiff ℝ k (fun V : Matrix ι c ℂ => mulBil (mulBil (mulBil
      (gramProjection P V D) (Matrix.single a.1.2 a.1.1 (1 : ℂ))) P) V) :=
    contDiff_bilin _ (contDiff_bilin _ (contDiff_bilin _ (contDiff_gramProjection P D)
      contDiff_const) contDiff_const) contDiff_id
  exact h.const_smul _

omit [DecidableEq ι] in
theorem locallyLipschitz_sourceDrift (D0 : ℝ) (Naux : ℕ) (P : Matrix ι ι ℂ) :
    LocallyLipschitz (fun V : Matrix ι c ℂ => sourceDrift D0 Naux P V) :=
  (contDiff_sourceDrift D0 Naux P).locallyLipschitz

theorem locallyLipschitz_sourceDiffusion (D0 : ℝ) (P : Matrix ι ι ℂ) (D : Matrix c c ℂ)
    (a : SourceNoise ι) :
    LocallyLipschitz (fun V : Matrix ι c ℂ => sourceDiffusion D0 P D a V) :=
  (contDiff_sourceDiffusion D0 P D a).locallyLipschitz

end BlockBand.SourceProcess.Stochastic.SourceSDE
