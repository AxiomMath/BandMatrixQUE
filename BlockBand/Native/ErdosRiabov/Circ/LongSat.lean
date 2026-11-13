module

public import BlockBand.Native.ErdosRiabov.Circ.CircEvol
public import BlockBand.Native.ErdosRiabov.Evol.RegSat

/-!
# The saturated averaged chains: `T̂^{⊕k}` forcing and the `combMg` noise

The Duhamel equation of saturated averaged chains with the generator `T̂^{⊕k}` written out, and
its martingale part in `combMg` form.

Setting: `Im P.z > 0`, `P.S = shortRingProfile p.b p.n p.W`, `1 ≤ k`, the
path `H_r = vsBandFin p r⁺ ω`, `𝒳_r(x) = P.avErr σ x r H_r`, `m = semicircleM P.z`.

* **`circ_chainMg_eq_combMg`**: a.s., for every `t` and every chain index `u`,
  `chainMg 0 … u t = combMg 0 … (fun α _ => if α = u then 1 else 0) t` (constant coefficients
  `δ_u`, via `VS.combMg_eq_ibp_uniform`).
* **`duhamel_av_sat_tensor`** (`¬ HasDesatFactor σ`, every sample, `t ∈ [0,1]`):
  `𝒳_t = 𝒳_0 + ∫_0^t (T̂_s^{⊕k}[𝒳_s] + 𝓕^av_s) ds + 𝓜_t`, with
  `T̂_s^{⊕k} = propOp (vsTensorGen S (fun _ => m) (fun _ => m̄) s)` (the identification
  `aTermAv = T̂^{⊕k}[𝒳]` stated for `Evol.duhamel_av_sat`).
* **`duhamel_av_sat_combMg`** (with `hZ`; a.s., every `t ≤ 1`, every `u`):
  `𝒳_t(u) = (∫_0^t (T̂_s^{⊕k}[𝒳_s] + 𝓕^av_s) ds)(u) + combMg 0 … δ_u t`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Circ

open MeasureTheory Set Matrix
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Stochastic
open BlockBand.Native.ErdosRiabov.VS
open BlockBand.Native.ErdosRiabov.Propagator
open BlockBand.Native.ErdosRiabov.Evol
open BlockBand.SourceProcess.FiniteDriverIntegration
open scoped NNReal ComplexConjugate

variable {p : BlockBand.Parameters} {k : ℕ} {P : PsiData (p.n * p.W)}

/-- **`chainMg = combMg(δ_u)`**: a.s., for every `t ≥ 0` and every chain index `u`, the chain
martingale part `𝓜^u_t` is `combMg` with the constant coefficients `c_α = 𝟙(α = u)`. -/
theorem circ_chainMg_eq_combMg (μ₀ : Measure p.SiteMatrix) [IsProbabilityMeasure μ₀]
    (hz : 0 < P.z.im) (σ : Fin k → Bool) (Bx : Sites p k → Fin k → RingMat p)
    (Kx : Sites p k → RingMat p) :
    ∀ᵐ ω ∂driverLaw (κ := Fin (ringDim p)) μ₀, ∀ t : ℝ≥0, ∀ u : Sites p k,
      chainMg 0 (zfam P.z σ) Bx Kx u t ω =
        combMg 0 (zfam P.z σ) Bx Kx (fun α _ => if α = u then (1 : ℂ) else 0) t ω := by
  filter_upwards [combMg_eq_ibp_uniform Matrix.isHermitian_zero (zfam_contDiff P.z σ)
    (zfam_im_ne_zero hz σ) μ₀ Bx Kx] with ω hω t u
  rw [hω _ (fun α => contDiff_const) t]
  simp only [deriv_const', zero_mul, intervalIntegral.integral_zero, sub_zero, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- **Saturated averaged Duhamel form with the `T̂^{⊕k}` forcing**, under the hypothesis
`Split.DerivStatement` (`hD`, proved as `MTerms.deriv_holds`). For a saturated pattern
(`¬ HasDesatFactor σ`),
every sample `ω` and every `t ∈ [0,1]`:
`𝒳_t = 𝒳_0 + ∫_0^t (T̂_s^{⊕k}[𝒳_s] + 𝓕^av_s) ds + 𝓜_t`.
-/
theorem duhamel_av_sat_tensor (hD : Split.DerivStatement) (hz : 0 < P.z.im)
    (hPS : P.S = Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W) (hk : 1 ≤ k)
    (σ : Fin k → Bool) (hσ : ¬ HasDesatFactor σ) (ω : RingSample p) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (fun x => P.avErr σ x t (pathH p ω t)) =
      (fun x => P.avErr σ x 0 (pathH p ω 0)) +
        (∫ s in (0 : ℝ)..t,
          propOp (vsTensorGen P.S (fun _ => semicircleM P.z) (fun _ => conj (semicircleM P.z)) s)
              (fun y => P.avErr σ y s (pathH p ω s)) +
            fun x => forcingAv P σ x s (pathH p ω s)) +
        (fun x => chainMg 0 (zfam P.z σ) (fun x => avSlots P.S x) (fun _ => 1) x t.toNNReal
          ω) := by
  rw [duhamel_av_sat hD hz hPS hk σ ω ht]
  congr 2
  refine intervalIntegral.integral_congr fun s _ => ?_
  funext x
  simp only [Pi.add_apply]
  rw [aTermAv_eq_propOp, circ_vsTensorGen_muAv σ hσ]

/-- **Saturated averaged chains in `combMg` form**, under the hypotheses
`Split.DerivStatement` and `Split.ZeroStatement` (proved as `MTerms.deriv_holds`,
`MTerms.zero_holds`). Almost surely, for every `t ∈ [0,1]` and
every site vector `u`:
`𝒳_t(u) = (∫_0^t (T̂_s^{⊕k}[𝒳_s] + 𝓕^av_s) ds)(u) + combMg 0 … δ_u t`.
-/
theorem duhamel_av_sat_combMg (μ₀ : Measure p.SiteMatrix) [IsProbabilityMeasure μ₀]
    (hD : Split.DerivStatement) (hZ : Split.ZeroStatement) (hz : 0 < P.z.im)
    (hPS : P.S = Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W) (hk : 1 ≤ k)
    (σ : Fin k → Bool) (hσ : ¬ HasDesatFactor σ) :
    ∀ᵐ ω ∂driverLaw (κ := Fin (ringDim p)) μ₀, ∀ t : ℝ≥0, (t : ℝ) ≤ 1 → ∀ u : Sites p k,
      P.avErr σ u t (pathH p ω t) =
        (∫ s in (0 : ℝ)..t,
          propOp (vsTensorGen P.S (fun _ => semicircleM P.z) (fun _ => conj (semicircleM P.z)) s)
              (fun y => P.avErr σ y s (pathH p ω s)) +
            fun x => forcingAv P σ x s (pathH p ω s)) u +
          combMg 0 (zfam P.z σ) (fun x => avSlots P.S x) (fun _ => 1)
            (fun α _ => if α = u then (1 : ℂ) else 0) t ω := by
  filter_upwards [circ_chainMg_eq_combMg μ₀ hz σ (fun x => avSlots P.S x) (fun _ => 1)]
    with ω hω t ht u
  have h := congrFun (duhamel_av_sat_tensor hD hz hPS hk σ hσ ω ⟨t.2, ht⟩) u
  rw [circ_avErr_pathH_zero hZ hk σ ω] at h
  simp only [Pi.add_apply, zero_add] at h
  refine h.trans ?_
  congr 1
  rw [← hω t u]
  simp

end BlockBand.Native.ErdosRiabov.Circ
