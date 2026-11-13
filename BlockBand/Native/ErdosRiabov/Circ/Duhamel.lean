module

public import BlockBand.Native.ErdosRiabov.Evol.Duhamel
public import BlockBand.Native.ErdosRiabov.Circ.Algebra

/-!
# Pathwise Duhamel form for a fixed linear image of the chains

For a fixed sample, a fixed linear map `V` applied to the chain fluctuations satisfies a Duhamel
equation with an extra forcing term.

Setting (as for `duhamel_generic`): `Im P.z > 0`,
`P.S = shortRingProfile p.b p.n p.W`, chains `(B_x, K_x)` along a pattern `σ`, deterministic
parts `m_x`, `X_r(x) = tr(K_x G_x(r)) - m_x(r)`, a **fixed sample** `ω`, `U(s,t) = ⊗_j P̂_j(s,t)`,
`A_s = ⊕_j Â_j(s)` and `𝓜_r(x) = VS.chainMg … x r⁺ ω`.

* **`duhamel_frozen`**: for any matrix `V` and any `F̃` with
  `V(A_r X_r) = A_r (V X_r) + V F̃_r` on `[0,1]`, for every `t ∈ [0,1]`:
  `V X_t = U(0,t) V X_0 + ∫_0^t U(s,t) V (F_s + F̃_s) ds + propagatedNoise U A (V 𝓜) 0 t`.
* **`frozenNoise_eq_combMg`** (`V` may depend on the final time): a.s., for every `t ≤ 1` and
  every `u`, the `u`-th coordinate of `propagatedNoise U A (V_t 𝓜) 0 t` is
  `VS.combMg 0 … (fun α s => (U(s,t) V_t)(u, α)) t` (coefficients of
  `∫_0^t P̂^{⊗k}_{s,t} 𝒰_t [d𝓜_s]`).
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
open ERNative.BlockBand.GaussianRing.ERZigStoppedDuhamel (propagatedNoise pathwise_duhamel)
open scoped NNReal

variable {p : BlockBand.Parameters} {k : ℕ} {P : PsiData (p.n * p.W)}

/-- **Duhamel form for a fixed linear image `V X`** (every sample `ω`, every `t ∈ [0,1]`):
if
`V(A_r X_r) = A_r (V X_r) + V F̃_r` on `[0,1]`, then
`V X_t = U(0,t) V X_0 + ∫_0^t U(s,t) V (F_s + F̃_s) ds + propagatedNoise U A (V 𝓜) 0 t`. -/
theorem duhamel_frozen (hz : 0 < P.z.im)
    (hPS : P.S = Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W) (σ : Fin k → Bool)
    (Bx : Sites p k → Fin k → RingMat p) (Kx : Sites p k → RingMat p)
    (mp dm : Sites p k → ℝ → ℂ) (hmp : ∀ x, ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt (mp x) (dm x s) s)
    (hdm : ∀ x, ContinuousOn (dm x) (Icc 0 1)) {μ μ' : Fin k → ℂ} (hμ : ∀ j, ‖μ j‖ < 1)
    (hμ' : ∀ j, ‖μ' j‖ < 1) (ω : RingSample p) (F Ft : ℝ → Sites p k → ℂ)
    (hF : ∀ r ∈ Icc (0 : ℝ) 1, ∀ x,
      propOp (vsTensorGen P.S μ μ' r) (fun y => cVal P σ (Bx y) (Kx y) ω r - mp y r) x + F r x =
        cDrift P σ (Bx x) (Kx x) ω r - dm x r)
    (V : Matrix (Sites p k) (Sites p k) ℂ)
    (hV : ∀ r ∈ Icc (0 : ℝ) 1, propOp V (propOp (vsTensorGen P.S μ μ' r)
        (fun y => cVal P σ (Bx y) (Kx y) ω r - mp y r)) =
      propOp (vsTensorGen P.S μ μ' r) (propOp V (fun y => cVal P σ (Bx y) (Kx y) ω r - mp y r)) +
        propOp V (Ft r))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    propOp V (fun x => cVal P σ (Bx x) (Kx x) ω t - mp x t) =
      propOp (vsTensorProp P.S μ μ' 0 t)
          (propOp V (fun x => cVal P σ (Bx x) (Kx x) ω 0 - mp x 0)) +
        (∫ s in (0 : ℝ)..t, propOp (vsTensorProp P.S μ μ' s t) (propOp V (F s + Ft s))) +
        propagatedNoise (fun s t => propOp (vsTensorProp P.S μ μ' s t))
          (fun s => propOp (vsTensorGen P.S μ μ' s))
          (fun r => propOp V (fun x => chainMg 0 (zfam P.z σ) Bx Kx x r.toNNReal ω)) 0 t := by
  have hS : StochasticSymm P.S := hPS ▸ stochasticSymm_ring p
  set X : ℝ → Sites p k → ℂ := fun r x => cVal P σ (Bx x) (Kx x) ω r - mp x r with hXdef
  set A : ℝ → (Sites p k → ℂ) →L[ℝ] (Sites p k → ℂ) := fun s => propOp (vsTensorGen P.S μ μ' s)
  set M : ℝ → Sites p k → ℂ := fun r x => chainMg 0 (zfam P.z σ) Bx Kx x r.toNNReal ω
  set L : (Sites p k → ℂ) →L[ℝ] (Sites p k → ℂ) := propOp V
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 1 := Icc_subset_Icc le_rfl ht.2
  have hA1 : ContinuousOn A (Icc 0 1) := continuousOn_propOp_vsTensorGen hS hμ hμ'
  have hX1 : ContinuousOn X (Icc 0 1) := continuousOn_pi.mpr fun x =>
    (continuousOn_cVal hz σ (Bx x) (Kx x) ω).sub
      (fun s hs => (hmp x s hs).continuousAt.continuousWithinAt)
  have hF1 : ContinuousOn F (Icc 0 1) := by
    have hc : ContinuousOn (fun r => fun x => cDrift P σ (Bx x) (Kx x) ω r - dm x r - A r (X r) x)
        (Icc 0 1) := continuousOn_pi.mpr fun x =>
      ((continuousOn_cDrift hz hPS σ (Bx x) (Kx x) ω).sub (hdm x)).sub
        ((continuous_apply x).comp_continuousOn (hA1.clm_apply hX1))
    refine hc.congr fun r hr => ?_
    funext x
    have := hF r hr x
    simp only [A, X] at this ⊢
    rw [← this]
    ring
  have hg1 : ContinuousOn (fun u => A u (X u) + F u) (Icc 0 1) := (hA1.clm_apply hX1).add hF1
  -- the integrated Itô form of `X` (as in `duhamel_generic`)
  have hIto : ∀ r ∈ Icc (0 : ℝ) 1,
      X r = X 0 + (∫ u in (0 : ℝ)..r, (A u (X u) + F u)) + (M r - M 0) := by
    intro r hr1
    have hsubr : uIcc (0 : ℝ) r ⊆ Icc 0 1 := by
      rw [uIcc_of_le hr1.1]
      exact Icc_subset_Icc le_rfl hr1.2
    have hgi : IntervalIntegrable (fun u => A u (X u) + F u) volume 0 r :=
      (hg1.mono hsubr).intervalIntegrable
    funext x
    have hproj : (∫ u in (0 : ℝ)..r, (A u (X u) + F u)) x =
        ∫ u in (0 : ℝ)..r, (cDrift P σ (Bx x) (Kx x) ω u - dm x u) := by
      have h := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Sites p k => ℂ) x
        ).intervalIntegral_comp_comm hgi
      simp only [ContinuousLinearMap.proj_apply] at h
      rw [← h]
      refine intervalIntegral.integral_congr fun u hu => ?_
      simp only [Pi.add_apply]
      exact hF u (hsubr hu) x
    have hci := (continuousOn_cDrift hz hPS σ (Bx x) (Kx x) ω).mono hsubr
    have hdi := (hdm x).mono hsubr
    have hftc : mp x r = mp x 0 + ∫ u in (0 : ℝ)..r, dm x u := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs => hmp x s (hsubr hs))
        hdi.intervalIntegrable]
      ring
    have hito := cVal_ito hz hPS σ Bx Kx x ω hr1
    have hM0 : M 0 x = 0 := by
      simp only [M, Real.toNNReal_zero]
      exact chainMg_zero _ _ _ _ _ _
    simp only [Pi.add_apply, Pi.sub_apply, hproj, hM0, sub_zero]
    rw [intervalIntegral.integral_sub hci.intervalIntegrable hdi.intervalIntegrable]
    simp only [X, M]
    rw [hito, hftc]
    ring
  
  have hG1 : ContinuousOn (fun u => L (F u + Ft u)) (Icc 0 1) := by
    have hc : ContinuousOn (fun u => L (A u (X u) + F u) - A u (L (X u))) (Icc 0 1) :=
      (L.continuous.comp_continuousOn hg1).sub (hA1.clm_apply (L.continuous.comp_continuousOn hX1))
    refine hc.congr fun u hu => ?_
    have h := hV u hu
    simp only [A, X, L] at h ⊢
    rw [map_add, map_add, h]
    abel
  have hMc : ContinuousOn M (Icc 0 t) := (continuous_pi fun x =>
    (continuous_chainMg_path hz σ Bx Kx x ω).comp continuous_real_toNNReal).continuousOn
  refine pathwise_duhamel (A := A) (P := fun s t => propOp (vsTensorProp P.S μ μ' s t))
    (X := fun r => L (X r)) (F := fun u => L (F u + Ft u)) (M := fun r => L (M r)) ht.1
    (hA1.mono hsub) ((L.continuous.comp_continuousOn hX1).mono hsub) (hG1.mono hsub)
    (L.continuous.comp_continuousOn hMc)
    ((continuousOn_propOp_vsTensorProp_left hS hμ hμ' ht.1 ht.2).mono hsub)
    (fun s hs => hasDerivAt_propOp_vsTensorProp_left hS hμ hμ' hs.1.le (hs.2.le.trans ht.2)
      ht.1 ht.2)
    (by rw [vsTensorProp_self hS hμ hμ' ht.1 ht.2, propOp_one]) ?_
  intro r hr
  have hr1 : r ∈ Icc (0 : ℝ) 1 := hsub hr
  have hsubr : uIcc (0 : ℝ) r ⊆ Icc 0 1 := by
    rw [uIcc_of_le hr.1]
    exact Icc_subset_Icc le_rfl hr1.2
  have hgi : IntervalIntegrable (fun u => A u (X u) + F u) volume 0 r :=
    (hg1.mono hsubr).intervalIntegrable
  have hcomm := L.intervalIntegral_comp_comm hgi
  have hint : (∫ u in (0 : ℝ)..r, L (A u (X u) + F u)) =
      ∫ u in (0 : ℝ)..r, (A u (L (X u)) + L (F u + Ft u)) := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    have h := hV u (hsubr hu)
    simp only [A, X, L] at h ⊢
    rw [map_add, map_add, h]
    abel
  rw [hIto r hr1, map_add, map_add, ← hcomm, hint, map_sub]

/-- **The Duhamel noise of `V X` is `combMg`**: a.s., for every `t ∈ [0,1]` and every
site vector `u`, with `c_α(s) = (U(s,t) V_t)(u, α)`,
`(propagatedNoise U A (V_t 𝓜) 0 t)(u) = combMg 0 … c t`.
The matrix `V_t` may depend on the final
time (`V_t = 𝒰_t` in `circEvol_short_combMg` and `circEvol_long_combMg`).
-/
theorem frozenNoise_eq_combMg (μ₀ : Measure p.SiteMatrix) [IsProbabilityMeasure μ₀]
    (hz : 0 < P.z.im) (hPS : P.S = Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W)
    (σ : Fin k → Bool) (Bx : Sites p k → Fin k → RingMat p) (Kx : Sites p k → RingMat p)
    {μ μ' : Fin k → ℂ} (hμ : ∀ j, ‖μ j‖ < 1) (hμ' : ∀ j, ‖μ' j‖ < 1)
    (V : ℝ → Matrix (Sites p k) (Sites p k) ℂ) :
    ∀ᵐ ω ∂driverLaw (κ := Fin (ringDim p)) μ₀, ∀ t : ℝ≥0, (t : ℝ) ≤ 1 → ∀ u : Sites p k,
      propagatedNoise (fun s t => propOp (vsTensorProp P.S μ μ' s t))
          (fun s => propOp (vsTensorGen P.S μ μ' s))
          (fun r => propOp (V t) (fun x => chainMg 0 (zfam P.z σ) Bx Kx x r.toNNReal ω)) 0 t u =
        combMg 0 (zfam P.z σ) Bx Kx (fun α s => (vsTensorProp P.S μ μ' s t * V t) u α) t ω := by
  have hS : StochasticSymm P.S := hPS ▸ stochasticSymm_ring p
  filter_upwards [combMg_eq_ibp_uniform Matrix.isHermitian_zero (zfam_contDiff P.z σ)
    (zfam_im_ne_zero hz σ) μ₀ Bx Kx] with ω hω t ht u
  have ht0 : (0 : ℝ) ≤ t := t.2
  rw [hω _ (fun α => contDiff_tensorCoef μ μ' t (V t) u α) t]
  have hsub : uIcc (0 : ℝ) t ⊆ Icc 0 1 := by
    rw [uIcc_of_le ht0]
    exact Icc_subset_Icc le_rfl ht
  have hentry : ∀ α, Continuous fun s : ℝ => chainMg 0 (zfam P.z σ) Bx Kx α s.toNNReal ω :=
    fun α => (continuous_chainMg_path hz σ Bx Kx α ω).comp continuous_real_toNNReal
  have hMc : Continuous fun s : ℝ => fun x => chainMg 0 (zfam P.z σ) Bx Kx x s.toNNReal ω :=
    continuous_pi hentry
  have h0 : (fun x : Sites p k => chainMg 0 (zfam P.z σ) Bx Kx x (Real.toNNReal 0) ω) = 0 := by
    funext x
    rw [Real.toNNReal_zero]
    exact chainMg_zero _ _ _ _ _ _
  unfold propagatedNoise
  beta_reduce
  rw [h0, map_zero]
  simp only [sub_zero, Pi.add_apply]
  have hint : IntervalIntegrable (fun s => propOp (vsTensorProp P.S μ μ' s t)
      (propOp (vsTensorGen P.S μ μ' s)
        (propOp (V t) (fun x => chainMg 0 (zfam P.z σ) Bx Kx x s.toNNReal ω)))) volume 0 t := by
    refine ContinuousOn.intervalIntegrable ?_
    exact (((continuousOn_propOp_vsTensorProp_left hS hμ hμ' ht0 ht).clm_apply
      ((continuousOn_propOp_vsTensorGen hS hμ hμ').clm_apply
        ((propOp (V t)).continuous.comp hMc).continuousOn))).mono hsub
  have hproj := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Sites p k => ℂ) u
    ).intervalIntegral_comp_comm hint
  simp only [ContinuousLinearMap.proj_apply] at hproj
  rw [← hproj]
  have hsum : (∫ s in (0 : ℝ)..t, propOp (vsTensorProp P.S μ μ' s t)
      (propOp (vsTensorGen P.S μ μ' s)
        (propOp (V t) (fun x => chainMg 0 (zfam P.z σ) Bx Kx x s.toNNReal ω))) u) =
      ∑ α, ∫ s in (0 : ℝ)..t,
        (vsTensorProp P.S μ μ' s t * vsTensorGen P.S μ μ' s * V t) u α *
          chainMg 0 (zfam P.z σ) Bx Kx α s.toNNReal ω := by
    simp_rw [← ContinuousLinearMap.comp_apply, ← propOp_mul, propOp_apply]
    rw [intervalIntegral.integral_finsetSum]
    · simp only [Matrix.mul_assoc]
    intro α _
    simp only [← Matrix.mul_assoc]
    refine ContinuousOn.intervalIntegrable ?_
    refine (ContinuousOn.mul ?_ (hentry α).continuousOn).mono hsub
    simp only [Matrix.mul_apply]
    exact continuousOn_finsetSum _ fun c _ =>
      (continuousOn_vsTensorProp_mul_gen_entry hS hμ hμ' ht0 ht u c).mul continuousOn_const
  have hcoef : ∀ α, (∫ s in (0 : ℝ)..t,
      deriv (fun r => (vsTensorProp P.S μ μ' r t * V t) u α) s *
        chainMg 0 (zfam P.z σ) Bx Kx α s.toNNReal ω) =
      -∫ s in (0 : ℝ)..t, (vsTensorProp P.S μ μ' s t * vsTensorGen P.S μ μ' s * V t) u α *
        chainMg 0 (zfam P.z σ) Bx Kx α s.toNNReal ω := by
    intro α
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht0] at hs
    rw [deriv_tensorCoef hS hμ hμ' hs.1 (hs.2.trans ht) ht0 ht (V t) u α]
    ring
  have hself : vsTensorProp P.S μ μ' t t = 1 := vsTensorProp_self hS hμ hμ' ht0 ht
  rw [hsum, Real.toNNReal_coe, propOp_apply, hself, Matrix.one_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [hcoef α]
  ring

end BlockBand.Native.ErdosRiabov.Circ
