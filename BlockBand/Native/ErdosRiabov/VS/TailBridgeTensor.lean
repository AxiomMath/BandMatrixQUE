module

public import BlockBand.Native.ErdosRiabov.VS.TailBridgeTensorUniform
public import BlockBand.Native.ErdosRiabov.Prop.Glue

set_option autoImplicit false

/-!
# `combMg` with tensor-propagator coefficients

The martingale part of a chain combination with tensor-propagator coefficients, written through
the single-chain martingales.

* `contDiff_tensorCoef`: `s ↦ (U(s,t) V)(u, α)` is `C^n` on all of `ℝ` (a finite sum of finite
  products of affine functions).
* `deriv_tensorCoef`: for `s, t ∈ [0, 1]`, `∂_s (U(s,t) V)(u, α) = -(U(s,t) (⊕_j Â_j(s)) V)(u, α)`.
* **`combMg_tensorPropagator`** (uniform: `∀ᵐ x, ∀ t ≤ 1, ∀ u`): with coefficients
  `c_α(s) = (U(s,t) V)(u, α)`,
  `combMg … c t = ∑_α V(u, α) 𝓜^α_t + ∑_α ∫_0^t (U(s,t) (⊕_j Â_j(s)) V)(u, α) 𝓜^α_s ds`,
  and `combMg_tensorPropagator_one` (`V = I`):
  `= 𝓜^u_t + ∑_α ∫_0^t (U(s,t) ⊕_j Â_j(s))(u, α) 𝓜^α_s`.
-/

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.VS
open MeasureTheory Set Filter Topology Matrix Function
open BlockBand.SourceProcess
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.Native.ErdosRiabov.Stochastic
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Propagator
open scoped NNReal

variable {m N : ℕ} {S : Matrix (Fin N) (Fin N) ℝ}

/-!
### The tensor coefficients
-/

theorem contDiff_tensorCoef (μ μ' : Fin m → ℂ) (t : ℝ)
    (V : Matrix (Fin m → Fin N) (Fin m → Fin N) ℂ) (u α : Fin m → Fin N) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun s : ℝ => (vsTensorProp S μ μ' s t * V) u α) := by
  simp only [Matrix.mul_apply, vsTensorProp, tensorMat]
  exact ContDiff.sum fun β _ => (contDiff_prod fun j _ =>
    contDiff_vsPropagator_left (μ j) (μ' j) t (u j) (β j)).mul contDiff_const

theorem hasDerivAt_tensorCoef (hS : StochasticSymm S) {μ μ' : Fin m → ℂ}
    (hμ : ∀ j, ‖μ j‖ < 1) (hμ' : ∀ j, ‖μ' j‖ < 1) {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (V : Matrix (Fin m → Fin N) (Fin m → Fin N) ℂ)
    (u α : Fin m → Fin N) :
    HasDerivAt (fun r : ℝ => (vsTensorProp S μ μ' r t * V) u α)
      (-(vsTensorProp S μ μ' s t * vsTensorGen S μ μ' s * V) u α) s := by
  simp only [Matrix.mul_apply]
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun β _ =>
    (hasDerivAt_vsTensorProp_left hS hμ hμ' hs0 hs1 ht0 ht1 u β).mul_const (V β α)
  refine h.congr_deriv ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [Matrix.neg_apply, Matrix.mul_apply, neg_mul]

theorem deriv_tensorCoef (hS : StochasticSymm S) {μ μ' : Fin m → ℂ}
    (hμ : ∀ j, ‖μ j‖ < 1) (hμ' : ∀ j, ‖μ' j‖ < 1) {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (V : Matrix (Fin m → Fin N) (Fin m → Fin N) ℂ)
    (u α : Fin m → Fin N) :
    deriv (fun r : ℝ => (vsTensorProp S μ μ' r t * V) u α) s =
      -(vsTensorProp S μ μ' s t * vsTensorGen S μ μ' s * V) u α :=
  (hasDerivAt_tensorCoef hS hμ hμ' hs0 hs1 ht0 ht1 V u α).deriv

/-!
### The tensor Duhamel noise
-/

variable {p : BlockBand.Parameters} {k : ℕ}

/-- **The Duhamel noise of a tensor propagator** (composed with a fixed `V`).
For a stochastic symmetric `S` and `|μ j|, |μ' j| < 1`: a.s., for every `t ≤ 1` and every `u`,
with `c_α(s) = (U(s,t) V)(u, α)`,
`combMg A₀ zf B K c t = ∑_α V(u,α) 𝓜^α_t + ∑_α ∫_0^t (U(s,t) (⊕_j Â_j(s)) V)(u,α) 𝓜^α_s ds`. -/
theorem combMg_tensorPropagator (μ₀ : Measure p.SiteMatrix) [IsProbabilityMeasure μ₀]
    {A₀ : RingMat p} (hA₀ : A₀.IsHermitian) {zf : (Fin m → Fin N) → Fin k → ℝ → ℂ}
    (hzC : ∀ α j, ContDiff ℝ 2 (zf α j)) (hzim : ∀ α j t, (zf α j t).im ≠ 0)
    (B : (Fin m → Fin N) → Fin k → RingMat p) (K : (Fin m → Fin N) → RingMat p)
    (hS : StochasticSymm S) {μ μ' : Fin m → ℂ} (hμ : ∀ j, ‖μ j‖ < 1) (hμ' : ∀ j, ‖μ' j‖ < 1)
    (V : Matrix (Fin m → Fin N) (Fin m → Fin N) ℂ) :
    ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ₀, ∀ t : ℝ≥0, (t : ℝ) ≤ 1 → ∀ u,
      combMg A₀ zf B K (fun α s => (vsTensorProp S μ μ' s t * V) u α) t x =
        ∑ α, V u α * chainMg A₀ zf B K α t x + ∑ α, ∫ s in (0 : ℝ)..t,
          (vsTensorProp S μ μ' s t * vsTensorGen S μ μ' s * V) u α *
            chainMg A₀ zf B K α s.toNNReal x := by
  filter_upwards [combMg_eq_ibp_uniform hA₀ hzC hzim μ₀ B K] with x hx t ht u
  have ht0 : (0 : ℝ) ≤ t := t.2
  rw [hx _ (fun α => contDiff_tensorCoef μ μ' t V u α) t]
  have hself : vsTensorProp S μ μ' t t = 1 := vsTensorProp_self hS hμ hμ' ht0 ht
  simp only [hself, Matrix.one_mul, sub_eq_add_neg]
  rw [Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le ht0] at hs
  rw [deriv_tensorCoef hS hμ hμ' hs.1 (hs.2.trans ht) ht0 ht V u α]
  ring

/-- **Tensor Duhamel noise, `V = I`**: a.s., for every `t ≤ 1` and every `u`, with
`c_α(s) = U(s,t)(u, α)`: `combMg … c t = 𝓜^u_t + ∑_α ∫_0^t (U(s,t) ⊕_j Â_j(s))(u,α) 𝓜^α_s ds`. -/
theorem combMg_tensorPropagator_one (μ₀ : Measure p.SiteMatrix) [IsProbabilityMeasure μ₀]
    {A₀ : RingMat p} (hA₀ : A₀.IsHermitian) {zf : (Fin m → Fin N) → Fin k → ℝ → ℂ}
    (hzC : ∀ α j, ContDiff ℝ 2 (zf α j)) (hzim : ∀ α j t, (zf α j t).im ≠ 0)
    (B : (Fin m → Fin N) → Fin k → RingMat p) (K : (Fin m → Fin N) → RingMat p)
    (hS : StochasticSymm S) {μ μ' : Fin m → ℂ} (hμ : ∀ j, ‖μ j‖ < 1) (hμ' : ∀ j, ‖μ' j‖ < 1) :
    ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ₀, ∀ t : ℝ≥0, (t : ℝ) ≤ 1 → ∀ u,
      combMg A₀ zf B K (fun α s => vsTensorProp S μ μ' s t u α) t x =
        chainMg A₀ zf B K u t x + ∑ α, ∫ s in (0 : ℝ)..t,
          (vsTensorProp S μ μ' s t * vsTensorGen S μ μ' s) u α *
            chainMg A₀ zf B K α s.toNNReal x := by
  filter_upwards [combMg_tensorPropagator μ₀ hA₀ hzC hzim B K hS hμ hμ' 1] with x hx t ht u
  have h := hx t ht u
  simp only [Matrix.mul_one] at h
  rw [h]
  congr 1
  simp [Matrix.one_apply]

end BlockBand.Native.ErdosRiabov.VS
