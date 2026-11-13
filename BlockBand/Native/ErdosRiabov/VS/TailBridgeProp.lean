module

public import BlockBand.Native.ErdosRiabov.VS.TailBridgeChain
public import BlockBand.Native.ErdosRiabov.Kernel.VSKernelExtra

set_option autoImplicit false

/-!
# `combMg` with propagator coefficients is the propagated noise

The martingale part of the chain combination with the coefficients `P̂_{s,t}(u, α)` is the
propagated noise of the Duhamel formula.

* `deriv_vsPropagator_left`: for `s, t ∈ [0, 1]`, `∂_s P̂_{s,t}(u, α) = -(P̂_{s,t} Â_s)(u, α)`
  (`Kernel.hasDerivAt_vsPropagator_left`).
-/

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.VS
open MeasureTheory Set Filter Topology Matrix Function
open BlockBand.SourceProcess
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Stochastic
open scoped NNReal

variable {N : ℕ} {S : Matrix (Fin N) (Fin N) ℝ}

/-!
### The propagator coefficients
-/

theorem vsPropagator_apply_affine (μ μ' : ℂ) (s t : ℝ) (u α : Fin N) :
    vsPropagator S μ μ' s t u α = (1 - (t : ℂ) • vsY S μ μ')⁻¹ u α -
      (s : ℂ) * (vsY S μ μ' * (1 - (t : ℂ) • vsY S μ μ')⁻¹) u α := by
  rw [vsPropagator, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul]

theorem contDiff_vsPropagator_left (μ μ' : ℂ) (t : ℝ) (u α : Fin N) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun s : ℝ => vsPropagator S μ μ' s t u α) := by
  simp only [vsPropagator_apply_affine]
  exact contDiff_const.sub (Complex.ofRealCLM.contDiff.mul contDiff_const)

theorem deriv_vsPropagator_left (hS : StochasticSymm S) {μ μ' : ℂ} (hμ : ‖μ‖ < 1)
    (hμ' : ‖μ'‖ < 1) {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (u α : Fin N) :
    deriv (fun r : ℝ => vsPropagator S μ μ' r t u α) s =
      -(vsPropagator S μ μ' s t * vsKernel S μ μ' s) u α :=
  (hasDerivAt_vsPropagator_left hS hμ hμ' hs0 hs1 ht0 ht1 u α).deriv

/-!
### The propagated noise
-/

variable {p : BlockBand.Parameters} {k : ℕ}

/-- The `u`-th coordinate of the propagated noise `𝓜_t + ∫_0^t P̂_{s,t} Â_s 𝓜_s ds`. -/
def vsPropNoise (S : Matrix (Fin N) (Fin N) ℝ) (μ μ' : ℂ) (A₀ : RingMat p)
    (zf : Fin N → Fin k → ℝ → ℂ) (B : Fin N → Fin k → RingMat p) (K : Fin N → RingMat p)
    (t : ℝ≥0) (u : Fin N) (x : RingSample p) : ℂ :=
  chainMg A₀ zf B K u t x + ∑ α, ∫ s in (0 : ℝ)..t,
    (vsPropagator S μ μ' s t * vsKernel S μ μ' s) u α * chainMg A₀ zf B K α s.toNNReal x

/-- **The Duhamel noise is `combMg` with propagator coefficients.** For a stochastic
symmetric `S`, `|μ|, |μ'| < 1` and `t ∈ [0, 1]`: a.s., for every `u`,
`combMg A₀ zf B K (fun α s => P̂_{s,t}(u, α)) t = vsPropNoise … t u`. -/
theorem combMg_vsPropagator (μ : MeasureTheory.Measure p.SiteMatrix) [IsProbabilityMeasure μ]
    {A₀ : RingMat p} (hA₀ : A₀.IsHermitian) {zf : Fin N → Fin k → ℝ → ℂ}
    (hzC : ∀ α j, ContDiff ℝ 2 (zf α j)) (hzim : ∀ α j t, (zf α j t).im ≠ 0)
    (B : Fin N → Fin k → RingMat p) (K : Fin N → RingMat p) (hS : StochasticSymm S)
    {μ₁ μ₂ : ℂ} (h₁ : ‖μ₁‖ < 1) (h₂ : ‖μ₂‖ < 1) (t : ℝ≥0) (ht : (t : ℝ) ≤ 1) :
    ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ u : Fin N,
      combMg A₀ zf B K (fun α s => vsPropagator S μ₁ μ₂ s t u α) t x =
        vsPropNoise S μ₁ μ₂ A₀ zf B K t u x := by
  rw [ae_all_iff]
  intro u
  filter_upwards [combMg_eq_ibp hA₀ hzC hzim μ B K (fun α s => vsPropagator S μ₁ μ₂ s t u α)
    fun α => contDiff_vsPropagator_left μ₁ μ₂ t u α] with x hx
  have ht0 : (0 : ℝ) ≤ t := t.2
  rw [hx t, vsPropNoise]
  have hself : vsPropagator S μ₁ μ₂ t t = 1 :=
    vsPropagator_self hS (norm_smul_lt_one h₁ h₂ ht0 ht)
  simp only [hself, sub_eq_add_neg]
  rw [Finset.sum_add_distrib]
  have h1 : ∑ α, (1 : Matrix (Fin N) (Fin N) ℂ) u α * chainMg A₀ zf B K α t x =
      chainMg A₀ zf B K u t x := by
    simp [Matrix.one_apply]
  rw [h1]
  congr 1
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le ht0] at hs
  rw [deriv_vsPropagator_left hS h₁ h₂ hs.1 (hs.2.trans ht) ht0 ht u α]
  ring

end BlockBand.Native.ErdosRiabov.VS
