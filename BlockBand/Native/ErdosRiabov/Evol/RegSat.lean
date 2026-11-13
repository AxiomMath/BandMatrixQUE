module

public import BlockBand.Native.ErdosRiabov.Evol.Duhamel

/-!
# The saturated averaged Duhamel form

The averaged chain fluctuation `𝒳_t` equals `𝒳_0` plus the integral of the generator term and
the forcing plus the chain martingale part (`duhamel_av_sat`, the Duhamel form with zero weights).

* `vsTensorGen_zero_weights`, `vsTensorProp_zero_weights`: with all weights `0` the tensor
  generator is `0` and the tensor propagator is `I`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Evol

open MeasureTheory Set Matrix
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Stochastic
open BlockBand.Native.ErdosRiabov.VS
open BlockBand.Native.ErdosRiabov.Propagator
open ERNative.BlockBand.GaussianRing.ERZigStoppedDuhamel (propagatedNoise)
open scoped NNReal

section Zero

variable {N k : ℕ} (S : Matrix (Fin N) (Fin N) ℝ)

theorem vsTensorGen_zero_weights (s : ℝ) :
    vsTensorGen S (fun _ : Fin k => (0 : ℂ)) (fun _ => 0) s = 0 := by
  unfold vsTensorGen
  refine Finset.sum_eq_zero fun i _ => ?_
  ext x y
  simp only [tensorMat, Matrix.zero_apply]
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  rw [Function.update_self, vsKernel_zero_left, Matrix.zero_apply]

theorem vsTensorProp_zero_weights (s t : ℝ) :
    vsTensorProp S (fun _ : Fin k => (0 : ℂ)) (fun _ => 0) s t = 1 := by
  have h : vsPropagator S 0 0 s t = 1 := by
    simp [vsPropagator, vsY]
  unfold vsTensorProp
  simp only [h]
  exact tensorMat_one

end Zero

variable {p : BlockBand.Parameters} {k : ℕ} {P : PsiData (p.n * p.W)}

/-- **Saturated averaged Duhamel form** (`U = I`, generator term moved into the forcing), under
the hypothesis `Split.DerivStatement` (`hD`, proved as `MTerms.deriv_holds`). For `Im z > 0`,
`P.S = shortRingProfile p.b p.n p.W`, `1 ≤ k`, every pattern, every sample and every
`t ∈ [0,1]`: `𝒳_t = 𝒳_0 + ∫_0^t (aTermAv + 𝓕^av)_s ds + 𝓜_t`. -/
theorem duhamel_av_sat (hD : Split.DerivStatement) (hz : 0 < P.z.im)
    (hPS : P.S = Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W) (hk : 1 ≤ k)
    (σ : Fin k → Bool) (ω : RingSample p) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (fun x => P.avErr σ x t (pathH p ω t)) =
      (fun x => P.avErr σ x 0 (pathH p ω 0)) +
        (∫ s in (0 : ℝ)..t, fun x => aTermAv P σ x s (pathH p ω s) +
          forcingAv P σ x s (pathH p ω s)) +
        (fun x => chainMg 0 (zfam P.z σ) (fun x => avSlots P.S x) (fun _ => 1) x t.toNNReal
          ω) := by
  have hS : StochasticSymm P.S := hPS ▸ stochasticSymm_ring p
  have hz0 : propOp (0 : Matrix (Sites p k) (Sites p k) ℂ) = 0 := by
    ext f a
    simp [propOp_apply]
  have h := duhamel_generic hz hPS σ (fun x => avSlots P.S x) (fun _ => 1) (avM P σ) (dMav P σ)
    (fun x s hs => hasDerivAt_avM P hD hz.ne' hS hk σ x hs)
    (fun x => continuousOn_dMav P hz.ne' hS σ x) (μ := fun _ => 0) (μ' := fun _ => 0)
    (fun _ => by simp) (fun _ => by simp) ω
    (fun r x => aTermAv P σ x r (pathH p ω r) + forcingAv P σ x r (pathH p ω r)) ?_ ht
  · simp only [cVal_av, vsTensorProp_zero_weights, vsTensorGen_zero_weights, propOp_one,
      ContinuousLinearMap.id_apply] at h
    rw [h]
    congr 1
    unfold propagatedNoise
    simp [hz0, chainMg_zero]
    rfl
  · intro r _ x
    simp only [cVal_av, vsTensorGen_zero_weights, hz0]
    rw [_root_.zero_apply, Pi.zero_apply, zero_add, aTermAv_add_forcingAv, dGav, cDrift,
      Matrix.one_mul]

end BlockBand.Native.ErdosRiabov.Evol
