module
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Mul
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# A deterministic identity behind the bracket field

For continuous real functions `z_i, z_j, φ_i, φ_j, ψ` on `ℝ`, with primitives
`G_k(v) = ∫_0^v φ_k` and compensated paths `x_k = z_k - z_k(0) - G_k`:
`x_i x_j - ∫_0^σ ψ = (z_i z_j)|_0^σ - ∫_0^σ (φ_i z_j + φ_j z_i + ψ)
  - z_i(0) x_j - z_j(0) x_i - (x_i G_j - ∫_0^σ φ_j x_i) - (x_j G_i - ∫_0^σ φ_i x_j)` at `σ`
(`bracket_identity`). Applied pathwise to a martingale-problem solution, every bracketed term
on the right is a martingale (test function `y_i y_j`, drift, `𝓖_0`-multiples, and
`hasMartingaleModification_mul_integral`).
-/

namespace BlockBand.Diffusion
open MeasureTheory

/-- Primitive `G(v) = ∫_0^v φ`. -/
def prim (φ : ℝ → ℝ) (v : ℝ) : ℝ := ∫ u in (0 : ℝ)..v, φ u

theorem hasDerivAt_prim {φ : ℝ → ℝ} (hφ : Continuous φ) (v : ℝ) :
    HasDerivAt (prim φ) (φ v) v :=
  (hφ.integral_hasStrictDerivAt 0 v).hasDerivAt

theorem continuous_prim {φ : ℝ → ℝ} (hφ : Continuous φ) : Continuous (prim φ) :=
  continuous_iff_continuousAt.2 fun v => (hasDerivAt_prim hφ v).continuousAt

theorem prim_zero (φ : ℝ → ℝ) : prim φ 0 = 0 := intervalIntegral.integral_same

/-- Integration by parts for two primitives: `G_i G_j (σ) = ∫_0^σ (φ_i G_j + φ_j G_i)`. -/
theorem integral_prim_mul {φ ψ : ℝ → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ) (σ : ℝ) :
    ∫ u in (0 : ℝ)..σ, (φ u * prim ψ u + ψ u * prim φ u) = prim φ σ * prim ψ σ := by
  have hc : Continuous fun u => φ u * prim ψ u + prim φ u * ψ u :=
    (hφ.mul (continuous_prim hψ)).add ((continuous_prim hφ).mul hψ)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := σ)
    (f := fun v => prim φ v * prim ψ v)
    (f' := fun u => φ u * prim ψ u + prim φ u * ψ u)
    (fun x _ => (hasDerivAt_prim hφ x).mul (hasDerivAt_prim hψ x))
    (hc.intervalIntegrable 0 σ)
  simp only [prim_zero, mul_zero, sub_zero] at h
  rw [← h]
  congr 1; funext u; ring

/-- **The deterministic bracket identity.** -/
theorem bracket_identity {zi zj φi φj ψ : ℝ → ℝ} (hzi : Continuous zi) (hzj : Continuous zj)
    (hφi : Continuous φi) (hφj : Continuous φj) (hψ : Continuous ψ) (σ : ℝ) :
    let xi : ℝ → ℝ := fun u => zi u - zi 0 - prim φi u
    let xj : ℝ → ℝ := fun u => zj u - zj 0 - prim φj u
    xi σ * xj σ - ∫ u in (0 : ℝ)..σ, ψ u =
      (zi σ * zj σ - zi 0 * zj 0 - ∫ u in (0 : ℝ)..σ, (φi u * zj u + φj u * zi u + ψ u)) -
        zi 0 * xj σ - zj 0 * xi σ -
        (xi σ * prim φj σ - ∫ u in (0 : ℝ)..σ, φj u * xi u) -
        (xj σ * prim φi σ - ∫ u in (0 : ℝ)..σ, φi u * xj u) := by
  intro xi xj
  have cGi := continuous_prim hφi
  have cGj := continuous_prim hφj
  have cxi : Continuous xi := (hzi.sub continuous_const).sub cGi
  have cxj : Continuous xj := (hzj.sub continuous_const).sub cGj
  have ii : ∀ {f : ℝ → ℝ}, Continuous f → IntervalIntegrable f volume 0 σ :=
    fun hf => hf.intervalIntegrable _ _
  -- `φ_i z_j = z_j(0) φ_i + φ_i x_j + φ_i G_j`
  have c1 : ∫ u in (0 : ℝ)..σ, (φi u * zj u + φj u * zi u + ψ u) =
      zj 0 * prim φi σ + (∫ u in (0 : ℝ)..σ, φi u * xj u) +
      zi 0 * prim φj σ + (∫ u in (0 : ℝ)..σ, φj u * xi u) +
      (∫ u in (0 : ℝ)..σ, (φi u * prim φj u + φj u * prim φi u)) +
      ∫ u in (0 : ℝ)..σ, ψ u := by
    have e : (fun u => φi u * zj u + φj u * zi u + ψ u) = fun u =>
        zj 0 * φi u + φi u * xj u + (zi 0 * φj u + φj u * xi u) +
          (φi u * prim φj u + φj u * prim φi u) + ψ u := by
      funext u; simp only [xi, xj]; ring
    rw [e, intervalIntegral.integral_add, intervalIntegral.integral_add,
      intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    · simp only [prim]; ring
    all_goals exact ii (by fun_prop)
  have c2 := integral_prim_mul hφi hφj σ
  rw [c1, c2]
  simp only [xi, xj]
  ring

end BlockBand.Diffusion
