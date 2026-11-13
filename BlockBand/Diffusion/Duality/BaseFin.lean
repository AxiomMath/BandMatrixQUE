module
public import BlockBand.Diffusion.Base.Defs
public import BlockBand.Diffusion.PathSpace.TestMP
public import Mathlib.LinearAlgebra.Matrix.Notation
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The base diffusion in `Fin 2` coordinates

The base generator in the coordinates `y = (y₀, y₁)` of `Fin 2 → ℝ` has
* drift `baseDrift D0 y = (D₀/2)(1 + 2y₀, 1 − 2y₁)`,
* covariance `baseCov D0 y = diag(D₀ y₀(1 + y₀), D₀ y₁(1 − y₁))`
(`mpGenerator_baseDrift_comp`: `mpGenerator (baseDrift D0) (baseCov D0) (f ∘ finProd) y =
exBaseGenerator D0 f (finProd y)` for `f ∈ C²(ℝ × ℝ)`). Hence the base diffusion, read in these
coordinates, solves the raw test-function martingale problem
(`IsExBaseDiffusion.isTestMPSolution`).
-/

namespace BlockBand.Diffusion
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic
open scoped NNReal

/-- `y ↦ (y 0, y 1)`. -/
def finProdLinear : (Fin 2 → ℝ) ≃ₗ[ℝ] ℝ × ℝ where
  toFun y := (y 0, y 1)
  invFun p := ![p.1, p.2]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv y := by ext i; fin_cases i <;> rfl
  right_inv p := rfl

/-- `ℝ² ≃L ℝ × ℝ`. -/
def finProd : (Fin 2 → ℝ) ≃L[ℝ] ℝ × ℝ := finProdLinear.toContinuousLinearEquiv

@[simp] theorem finProd_apply (y : Fin 2 → ℝ) : finProd y = (y 0, y 1) := rfl

@[simp] theorem finProd_symm_apply (p : ℝ × ℝ) : finProd.symm p = ![p.1, p.2] := rfl

/-- Drift of `𝒟₀` in `Fin 2` coordinates. -/
def baseDrift (D0 : ℝ) (y : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![D0 / 2 * (1 + 2 * y 0), D0 / 2 * (1 - 2 * y 1)]

/-- Covariance of `𝒟₀` in `Fin 2` coordinates. -/
def baseCov (D0 : ℝ) (y : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![D0 * (y 0 * (1 + y 0)), 0; 0, D0 * (y 1 * (1 - y 1))]

theorem continuous_baseDrift (D0 : ℝ) : Continuous (baseDrift D0) := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · simp only [baseDrift]; fun_prop
  · simp only [baseDrift]; fun_prop

theorem continuous_baseCov (D0 : ℝ) : Continuous (baseCov D0) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;> simp only [baseCov] <;> fun_prop

theorem baseCov_symm (D0 : ℝ) (y : Fin 2 → ℝ) (i j : Fin 2) :
    baseCov D0 y i j = baseCov D0 y j i := by
  fin_cases i <;> fin_cases j <;> rfl

theorem fderiv_comp_finProd (f : ℝ × ℝ → ℝ) (y v : Fin 2 → ℝ) :
    fderiv ℝ (f ∘ finProd) y v = fderiv ℝ f (finProd y) (finProd v) := by
  rw [finProd.comp_right_fderiv]; rfl

theorem fderiv_fderiv_comp_finProd (f : ℝ × ℝ → ℝ) (y v w : Fin 2 → ℝ) :
    fderiv ℝ (fderiv ℝ (f ∘ finProd)) y v w =
      fderiv ℝ (fderiv ℝ f) (finProd y) (finProd v) (finProd w) := by
  have h := finProd.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (mem_univ (finProd y)) 2
  simp only [preimage_univ, iteratedFDerivWithin_univ] at h
  have h2 := congrArg (fun L => L ![v, w]) h
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_two_apply] at h2
  simpa using h2

/-- `D²f(z)[h, k] = D(w ↦ Df(w)[k])(z)[h]` for `f` twice differentiable. -/
theorem fderiv_fderiv_apply' {f : ℝ × ℝ → ℝ} {z : ℝ × ℝ}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) z) (h k : ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ f) z h k = fderiv ℝ (fun w => fderiv ℝ f w k) z h := by
  rw [fderiv_clm_apply hf (differentiableAt_const k)]
  simp

/-- **Generator transport**: `mpGenerator (baseDrift D0) (baseCov D0) (f ∘ finProd) y =
exBaseGenerator D0 f (finProd y)`. -/
theorem mpGenerator_baseDrift_comp (D0 : ℝ) {f : ℝ × ℝ → ℝ} {y : Fin 2 → ℝ}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) (finProd y)) :
    mpGenerator (baseDrift D0) (baseCov D0) (f ∘ finProd) y =
      exBaseGenerator D0 f (finProd y) := by
  have e0 : finProd (Pi.single 0 1 : Fin 2 → ℝ) = (1, 0) := by simp
  have e1 : finProd (Pi.single 1 1 : Fin 2 → ℝ) = (0, 1) := by simp
  simp only [mpGenerator, fderiv_comp_finProd, fderiv_fderiv_comp_finProd, Fin.sum_univ_two, e0,
    e1]
  rw [exBaseGenerator, ← fderiv_fderiv_apply' hf, ← fderiv_fderiv_apply' hf]
  simp [baseDrift, baseCov]
  ring

/-- The base diffusion in `Fin 2` coordinates. -/
def baseFin {Ω : Type*} (Z : ℝ≥0 → Ω → ℝ × ℝ) (t : ℝ≥0) (ω : Ω) : Fin 2 → ℝ :=
  finProd.symm (Z t ω)

@[simp] theorem finProd_baseFin {Ω : Type*} (Z : ℝ≥0 → Ω → ℝ × ℝ) (t : ℝ≥0) (ω : Ω) :
    finProd (baseFin Z t ω) = Z t ω := by simp [baseFin]

@[simp] theorem baseFin_zero {Ω : Type*} (Z : ℝ≥0 → Ω → ℝ × ℝ) (t : ℝ≥0) (ω : Ω) :
    baseFin Z t ω 0 = (Z t ω).1 := rfl

@[simp] theorem baseFin_one {Ω : Type*} (Z : ℝ≥0 → Ω → ℝ × ℝ) (t : ℝ≥0) (ω : Ω) :
    baseFin Z t ω 1 = (Z t ω).2 := rfl

/-- **The base diffusion solves the raw test-function martingale problem in `Fin 2`
coordinates.** -/
theorem IsExBaseDiffusion.isTestMPSolution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {D0 : ℝ} {z : ℝ × ℝ}
    {Z : ℝ≥0 → Ω → ℝ × ℝ} (h : IsExBaseDiffusion P 𝓖 D0 z Z) :
    IsTestMPSolution P 𝓖 (baseDrift D0) (baseCov D0) univ (baseFin Z) where
  adapted t := finProd.symm.continuous.measurable.comp (h.adapted t)
  continuous := h.paths.mono fun ω hω => finProd.symm.continuous.comp hω.1
  martingale F hF := by
    set f : ℝ × ℝ → ℝ := F ∘ finProd.symm with hfdef
    have hfc : ContDiff ℝ (⊤ : ℕ∞) f := hF.1.comp finProd.symm.contDiff
    have hfs : HasCompactSupport f := hF.2.1.comp_homeomorph finProd.symm.toHomeomorph
    have hM := h.martingale f hfc hfs
    have hFe : f ∘ finProd = F := by
      funext y; simp only [hfdef, Function.comp, ContinuousLinearEquiv.symm_apply_apply]
    have hd : ∀ z, DifferentiableAt ℝ (fderiv ℝ f) z := fun z =>
      ((hfc.fderiv_right (m := 1) (by simp)).differentiable (by simp)) z
    have e : (fun t ω => F (baseFin Z t ω) - ∫ u in Ioc (0 : ℝ) t,
        mpGenerator (baseDrift D0) (baseCov D0) F (baseFin Z u.toNNReal ω)) =
        fun t ω => f (Z t ω) - ∫ u in Ioc (0 : ℝ) t, exBaseGenerator D0 f (Z u.toNNReal ω) := by
      funext t ω
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
      have := mpGenerator_baseDrift_comp D0 (hd _) (y := baseFin Z u.toNNReal ω)
      rw [hFe, finProd_baseFin] at this
      exact this
    rw [e]; exact hM

end BlockBand.Diffusion
