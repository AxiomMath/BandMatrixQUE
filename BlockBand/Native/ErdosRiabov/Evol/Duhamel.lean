module

public import BlockBand.Native.ErdosRiabov.Evol.DuhamelIto
public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.ZigStoppedDuhamel

/-!
# The stochastic Duhamel form of the evolution equations

Setting as in `Evol.DuhamelIto`: `P.S = shortRingProfile p.b p.n p.W`, `Im P.z > 0`, pattern
`σ`, a **fixed sample** `ω`, the path `H_r = vsBandFin p r⁺ ω`, vectors indexed by the sites
`x : Fin k → Fin N` (`N = p.n * p.W`). With
`U(s,t) = propOp (vsTensorProp S μ μ' s t)` (`⊗_j P̂_j(s,t)`), `A_s = propOp (vsTensorGen S μ μ' s)`
(`⊕_j Â_j(s)`), the martingale vector `𝓜_r(x) = VS.chainMg … x r⁺ ω` and
`propagatedNoise U A 𝓜 0 t = 𝓜_t + ∫_0^t U(s,t) A_s 𝓜_s ds` (`ERZigStoppedDuhamel`):

* `duhamel_generic`: for chains `(B_x, K_x)` and deterministic parts `m_x` (differentiable on
  `[0,1]`, continuous derivative), if `A_r X_r + F_r = (G-drift) - m'_r` on `[0,1]` for
  `X_r(x) = tr(K_x G_x(r)) - m_x(r)`, then for every `t ∈ [0,1]`
  `X_t = U(0,t) X_0 + ∫_0^t U(s,t) F_s ds + propagatedNoise U A 𝓜 0 t`
  (`pathwise_duhamel`: interior derivatives and continuity; no endpoint derivative).
* **`duhamel_av`**: `𝒳^k`, `U = ⊗_{j=1}^k` (`μ_j = m_j`, `μ'_j = m_{j+1}`, cyclic), forcing
  `𝓕^av`. **`duhamel_iso`**: `𝒴^k`, the same with the last weight `μ_k := 0`, so the last factor
  is `I` (`k - 1` factors; for `k = 1`, `U = I`), forcing `𝓕^iso`. Both **conditional on
  `Split.DerivStatement`** (`hD`). Every sample, every `t ∈ [0,1]`.
* **`propagatedNoise_eq_combMg`** (the link to the martingale tail bound): a.s., for every `t ≤ 1`
  and every `u`, the `u`-th coordinate of the propagated noise is
  `VS.combMg 0 … (fun α s => U(s,t)(u, α)) t` (via `VS.combMg_tensorPropagator_one`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Evol

open MeasureTheory Set Matrix
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Chains
open BlockBand.Native.ErdosRiabov.Stochastic
open BlockBand.Native.ErdosRiabov.VS
open BlockBand.Native.ErdosRiabov.Propagator
open BlockBand.Native.CEH.Flow
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.FiniteDriverIntegration
open ERNative.BlockBand.GaussianRing.ERZigStoppedDuhamel (propagatedNoise pathwise_duhamel)
open scoped NNReal

/-!
### Continuity of the tensor generator and propagator
-/

section Tensor

variable {N k : ℕ} {S : Matrix (Fin N) (Fin N) ℝ}

theorem continuousOn_vsKernel_entry (hS : StochasticSymm S) {μ μ' : ℂ} (hμ : ‖μ‖ < 1)
    (hμ' : ‖μ'‖ < 1) (a b : Fin N) :
    ContinuousOn (fun s : ℝ => vsKernel S μ μ' s a b) (Icc 0 1) := fun _ hs =>
  (hasDerivAt_vsKernel hS (norm_smul_lt_one hμ hμ' hs.1 hs.2) a b).continuousAt.continuousWithinAt

theorem continuousOn_vsTensorGen_entry (hS : StochasticSymm S) {μ μ' : Fin k → ℂ}
    (hμ : ∀ j, ‖μ j‖ < 1) (hμ' : ∀ j, ‖μ' j‖ < 1) (a b : Fin k → Fin N) :
    ContinuousOn (fun s : ℝ => vsTensorGen S μ μ' s a b) (Icc 0 1) := by
  unfold vsTensorGen
  simp only [Matrix.sum_apply, tensorMat]
  refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetProd _ fun j _ => ?_
  by_cases hj : j = i
  · subst hj
    simp only [Function.update_self]
    exact continuousOn_vsKernel_entry hS (hμ j) (hμ' j) _ _
  · simp only [Function.update_of_ne hj]
    exact continuousOn_const

theorem continuousOn_propOp_vsTensorGen (hS : StochasticSymm S) {μ μ' : Fin k → ℂ}
    (hμ : ∀ j, ‖μ j‖ < 1) (hμ' : ∀ j, ‖μ' j‖ < 1) :
    ContinuousOn (fun s : ℝ => propOp (vsTensorGen S μ μ' s)) (Icc 0 1) := by
  have h : ContinuousOn (fun s : ℝ => fun a b => vsTensorGen S μ μ' s a b) (Icc 0 1) :=
    continuousOn_pi.mpr fun a => continuousOn_pi.mpr fun b =>
      continuousOn_vsTensorGen_entry hS hμ hμ' a b
  exact (propOpCLM _).continuous.comp_continuousOn h

theorem continuousOn_propOp_vsTensorProp_left (hS : StochasticSymm S) {μ μ' : Fin k → ℂ}
    (hμ : ∀ j, ‖μ j‖ < 1) (hμ' : ∀ j, ‖μ' j‖ < 1) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ContinuousOn (fun s : ℝ => propOp (vsTensorProp S μ μ' s t)) (Icc 0 1) := fun _ hs =>
  (hasDerivAt_propOp_vsTensorProp_left hS hμ hμ' hs.1 hs.2 ht0 ht1).continuousAt.continuousWithinAt

theorem continuousOn_vsTensorProp_mul_gen_entry (hS : StochasticSymm S) {μ μ' : Fin k → ℂ}
    (hμ : ∀ j, ‖μ j‖ < 1) (hμ' : ∀ j, ‖μ' j‖ < 1) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (a b : Fin k → Fin N) :
    ContinuousOn (fun s : ℝ => (vsTensorProp S μ μ' s t * vsTensorGen S μ μ' s) a b)
      (Icc 0 1) := by
  simp only [Matrix.mul_apply]
  refine continuousOn_finsetSum _ fun c _ => ContinuousOn.mul ?_
    (continuousOn_vsTensorGen_entry hS hμ hμ' c b)
  exact fun s hs =>
    (hasDerivAt_vsTensorProp_left hS hμ hμ' hs.1 hs.2 ht0 ht1 a c).continuousAt.continuousWithinAt

theorem vsKernel_zero_left (μ' : ℂ) (s : ℝ) : vsKernel S 0 μ' s = 0 := by
  simp [vsKernel, vsY]

end Tensor

/-!
### The generic pathwise Duhamel step
-/

variable {p : BlockBand.Parameters} {k : ℕ} {P : PsiData (p.n * p.W)}

/-- Sites of length `k` on `Fin (p.n * p.W)`. -/
abbrev Sites (p : BlockBand.Parameters) (k : ℕ) : Type := Fin k → Fin (p.n * p.W)

theorem continuousOn_cVal (hz : 0 < P.z.im) (σ : Fin k → Bool) (B : Fin k → RingMat p)
    (K : RingMat p) (ω : RingSample p) : ContinuousOn (cVal P σ B K ω) (Icc 0 1) := by
  have hφ := fun K' : RingMat p => (contDiff_chainTestT_ring Matrix.isHermitian_zero
    (zfam_contDiff (ι := Unit) P.z σ) (zfam_im_ne_zero (ι := Unit) hz σ) B K' ()).continuous
  have hq : Continuous fun r : ℝ => (r, vsNoise p r.toNNReal ω) :=
    continuous_id.prodMk (continuous_noisePath ω)
  have hc : Continuous fun r : ℝ =>
      ((chainTestT 0 (ringMatrixFin p) (vsPatternSpec P.z (semicircleM P.z) σ) B K
        (r, vsNoise p r.toNNReal ω) : ℝ) : ℂ) +
      ((chainTestT 0 (ringMatrixFin p) (vsPatternSpec P.z (semicircleM P.z) σ) B
        (-Complex.I • K) (r, vsNoise p r.toNNReal ω) : ℝ) : ℂ) * Complex.I :=
    (Complex.continuous_ofReal.comp ((hφ K).comp hq)).add
      ((Complex.continuous_ofReal.comp ((hφ (-Complex.I • K)).comp hq)).mul continuous_const)
  refine hc.continuousOn.congr fun r hr => ?_
  apply Complex.ext
  · simp [cVal_re hz σ B K ω hr]
  · simp [cVal_im hz σ B K ω hr]

/-- **Generic pathwise Duhamel form** (every sample `ω`, every `t ∈ [0,1]`). -/
theorem duhamel_generic (hz : 0 < P.z.im)
    (hPS : P.S = Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W) (σ : Fin k → Bool)
    (Bx : Sites p k → Fin k → RingMat p) (Kx : Sites p k → RingMat p)
    (mp dm : Sites p k → ℝ → ℂ) (hmp : ∀ x, ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt (mp x) (dm x s) s)
    (hdm : ∀ x, ContinuousOn (dm x) (Icc 0 1)) {μ μ' : Fin k → ℂ} (hμ : ∀ j, ‖μ j‖ < 1)
    (hμ' : ∀ j, ‖μ' j‖ < 1) (ω : RingSample p) (F : ℝ → Sites p k → ℂ)
    (hF : ∀ r ∈ Icc (0 : ℝ) 1, ∀ x,
      propOp (vsTensorGen P.S μ μ' r) (fun y => cVal P σ (Bx y) (Kx y) ω r - mp y r) x + F r x =
        cDrift P σ (Bx x) (Kx x) ω r - dm x r)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (fun x => cVal P σ (Bx x) (Kx x) ω t - mp x t) =
      propOp (vsTensorProp P.S μ μ' 0 t) (fun x => cVal P σ (Bx x) (Kx x) ω 0 - mp x 0) +
        (∫ s in (0 : ℝ)..t, propOp (vsTensorProp P.S μ μ' s t) (F s)) +
        propagatedNoise (fun s t => propOp (vsTensorProp P.S μ μ' s t))
          (fun s => propOp (vsTensorGen P.S μ μ' s))
          (fun r x => chainMg 0 (zfam P.z σ) Bx Kx x r.toNNReal ω) 0 t := by
  have hS : StochasticSymm P.S := hPS ▸ stochasticSymm_ring p
  set X : ℝ → Sites p k → ℂ := fun r x => cVal P σ (Bx x) (Kx x) ω r - mp x r with hXdef
  set A : ℝ → (Sites p k → ℂ) →L[ℝ] (Sites p k → ℂ) := fun s => propOp (vsTensorGen P.S μ μ' s)
  set M : ℝ → Sites p k → ℂ := fun r x => chainMg 0 (zfam P.z σ) Bx Kx x r.toNNReal ω
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
  have hM : ContinuousOn M (Icc 0 t) := (continuous_pi fun x =>
    (continuous_chainMg_path hz σ Bx Kx x ω).comp continuous_real_toNNReal).continuousOn
  have hg1 : ContinuousOn (fun u => A u (X u) + F u) (Icc 0 1) := (hA1.clm_apply hX1).add hF1
  refine pathwise_duhamel (A := A) (P := fun s t => propOp (vsTensorProp P.S μ μ' s t))
    (X := X) (F := F) (M := M) ht.1 (hA1.mono hsub) (hX1.mono hsub) (hF1.mono hsub) hM
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

/-!
### The averaged and isotropic chains
-/

/-- `μ_j = m_j` (1-based `m_{j+1}` for the 0-based slot `j`). -/
def muAv (P : PsiData (p.n * p.W)) (σ : Fin k → Bool) : Fin k → ℂ :=
  fun j => patM P.z σ (j.val + 1)

/-- `μ'_j = m_{j+1}` (cyclic). -/
def muNext (P : PsiData (p.n * p.W)) (σ : Fin k → Bool) : Fin k → ℂ :=
  fun j => patM P.z σ (nextIdx j)

/-- Isotropic weights: `μ_j = m_j` for `j < k - 1`, `μ_{k-1} = 0` (last factor `I`). -/
def muIso (P : PsiData (p.n * p.W)) (σ : Fin k → Bool) : Fin k → ℂ :=
  fun j => if j.val + 1 < k then patM P.z σ (j.val + 1) else 0

theorem norm_muAv (hz : P.z.im ≠ 0) (σ : Fin k → Bool) (j : Fin k) : ‖muAv P σ j‖ < 1 :=
  norm_patM_lt_one hz σ _

theorem norm_muNext (hz : P.z.im ≠ 0) (σ : Fin k → Bool) (j : Fin k) : ‖muNext P σ j‖ < 1 :=
  norm_patM_lt_one hz σ _

theorem norm_muIso (hz : P.z.im ≠ 0) (σ : Fin k → Bool) (j : Fin k) : ‖muIso P σ j‖ < 1 := by
  unfold muIso
  split_ifs
  · exact norm_patM_lt_one hz σ _
  · simp

/-- `(⊕_j Â_j)[𝒳] = propOp (vsTensorGen S μ μ')` applied to `𝒳`. -/
theorem aTermAv_eq_propOp (σ : Fin k → Bool) (x : Sites p k) (t : ℝ) (H : RingMat p) :
    aTermAv P σ x t H =
      propOp (vsTensorGen P.S (muAv P σ) (muNext P σ) t) (fun y => P.avErr σ y t H) x := by
  rw [propOp_vsTensorGen_apply]
  rfl

/-- `(⊕_{j<k-1} Â_j)[𝒴] = propOp (vsTensorGen S μ^iso μ')` applied to `𝒴` (the last weight `0`
gives the kernel `0`). -/
theorem aTermIso_eq_propOp (σ : Fin k → Bool) (a b : Fin (p.n * p.W)) (x : Sites p k) (t : ℝ)
    (H : RingMat p) :
    aTermIso P σ a b x t H =
      propOp (vsTensorGen P.S (muIso P σ) (muNext P σ) t) (fun y => P.isoErr σ a b y t H) x := by
  rw [propOp_vsTensorGen_apply, aTermIso, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : j.val + 1 < k
  · simp only [hj, ite_true, muIso, aKer, muNext]
  · simp only [hj, ite_false, muIso, vsKernel_zero_left, Matrix.zero_apply, zero_mul,
      Finset.sum_const_zero]

theorem cVal_av (σ : Fin k → Bool) (x : Sites p k) (ω : RingSample p) (r : ℝ) :
    cVal P σ (avSlots P.S x) 1 ω r - avM P σ x r = P.avErr σ x r (pathH p ω r) := by
  simp [cVal, PsiData.avErr, avM]

theorem cVal_iso (σ : Fin k → Bool) (a b : Fin (p.n * p.W)) (x : Sites p k) (ω : RingSample p)
    (r : ℝ) :
    cVal P σ (isoSlots P.S x) (Matrix.single b a 1) ω r - isoM P σ a b x r =
      P.isoErr σ a b x r (pathH p ω r) := by
  simp [cVal, PsiData.isoErr, isoM, trace_single_mul]

/-- **Stochastic Duhamel form, averaged chains.** **Conditional on `Split.DerivStatement`** (`hD`).
For `Im z > 0`, `P.S = shortRingProfile p.b p.n p.W`, `1 ≤ k`, a pattern `σ`, **every sample**
`ω` and every `t ∈ [0,1]`, with `𝒳_r = (x ↦ 𝒳^k_r(x)(H_r))`, `U = ⊗_{j=1}^k P̂_j`
(`μ_j = m_j`, `μ'_j = m_{j+1}`, cyclic), `A = ⊕_j Â_j`, `𝓕_r = (x ↦ 𝓕^av_r(x)(H_r))`:
`𝒳_t = U(0,t) 𝒳_0 + ∫_0^t U(s,t) 𝓕_s ds + propagatedNoise U A 𝓜 0 t`,
`𝓜_r(x) = chainMg` of the chain `x` (`K = 1`). -/
theorem duhamel_av (hD : Split.DerivStatement) (hz : 0 < P.z.im)
    (hPS : P.S = Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W) (hk : 1 ≤ k)
    (σ : Fin k → Bool) (ω : RingSample p) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (fun x => P.avErr σ x t (pathH p ω t)) =
      propOp (vsTensorProp P.S (muAv P σ) (muNext P σ) 0 t)
          (fun x => P.avErr σ x 0 (pathH p ω 0)) +
        (∫ s in (0 : ℝ)..t, propOp (vsTensorProp P.S (muAv P σ) (muNext P σ) s t)
          (fun x => forcingAv P σ x s (pathH p ω s))) +
        propagatedNoise (fun s t => propOp (vsTensorProp P.S (muAv P σ) (muNext P σ) s t))
          (fun s => propOp (vsTensorGen P.S (muAv P σ) (muNext P σ) s))
          (fun r x => chainMg 0 (zfam P.z σ) (fun x => avSlots P.S x) (fun _ => 1) x
            r.toNNReal ω) 0 t := by
  have hS : StochasticSymm P.S := hPS ▸ stochasticSymm_ring p
  have h := duhamel_generic hz hPS σ (fun x => avSlots P.S x) (fun _ => 1) (avM P σ) (dMav P σ)
    (fun x s hs => hasDerivAt_avM P hD hz.ne' hS hk σ x hs)
    (fun x => continuousOn_dMav P hz.ne' hS σ x) (norm_muAv hz.ne' σ) (norm_muNext hz.ne' σ) ω
    (fun r x => forcingAv P σ x r (pathH p ω r)) ?_ ht
  · simpa only [cVal_av] using h
  · intro r _ x
    simp only [cVal_av]
    rw [← aTermAv_eq_propOp, aTermAv_add_forcingAv, dGav, cDrift, Matrix.one_mul]

/-- **Stochastic Duhamel form, isotropic chains** (`k - 1` factors). **Conditional on
`Split.DerivStatement`** (`hD`). Hypotheses as in `duhamel_av`, plus sites `a, b`; `U = ⊗_j P̂_j`
with the isotropic weights (`μ_j = m_j` for `j < k-1`, `μ_{k-1} = 0`, so the last factor is `I`;
for `k = 1`, `U = I`), forcing `𝓕^iso`, `𝓜_r(x) = chainMg` of the chain `x` with `K = E_ba`;
every sample, every `t ∈ [0,1]`. -/
theorem duhamel_iso (hD : Split.DerivStatement) (hz : 0 < P.z.im)
    (hPS : P.S = Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W) (hk : 1 ≤ k)
    (σ : Fin k → Bool) (a b : Fin (p.n * p.W)) (ω : RingSample p) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (fun x => P.isoErr σ a b x t (pathH p ω t)) =
      propOp (vsTensorProp P.S (muIso P σ) (muNext P σ) 0 t)
          (fun x => P.isoErr σ a b x 0 (pathH p ω 0)) +
        (∫ s in (0 : ℝ)..t, propOp (vsTensorProp P.S (muIso P σ) (muNext P σ) s t)
          (fun x => forcingIso P σ a b x s (pathH p ω s))) +
        propagatedNoise (fun s t => propOp (vsTensorProp P.S (muIso P σ) (muNext P σ) s t))
          (fun s => propOp (vsTensorGen P.S (muIso P σ) (muNext P σ) s))
          (fun r x => chainMg 0 (zfam P.z σ) (fun x => isoSlots P.S x)
            (fun _ => Matrix.single b a 1) x r.toNNReal ω) 0 t := by
  have hS : StochasticSymm P.S := hPS ▸ stochasticSymm_ring p
  have h := duhamel_generic hz hPS σ (fun x => isoSlots P.S x) (fun _ => Matrix.single b a 1)
    (fun x => isoM P σ a b x) (fun x => dMiso P σ a b x)
    (fun x s hs => hasDerivAt_isoM P hD hz.ne' hS hk σ a b x hs)
    (fun x => continuousOn_dMiso P hz.ne' hS σ a b x) (norm_muIso hz.ne' σ)
    (norm_muNext hz.ne' σ) ω (fun r x => forcingIso P σ a b x r (pathH p ω r)) ?_ ht
  · simpa only [cVal_iso] using h
  · intro r _ x
    simp only [cVal_iso]
    rw [← aTermIso_eq_propOp, aTermIso_add_forcingIso, dGiso, cDrift, trace_single_mul,
      one_smul]

/-!
### The propagated noise as `combMg` (link to the martingale tail bound)
-/

/-- **The propagated noise is `combMg`**: a.s., for every `t ∈ [0,1]` and every site vector `u`,
the `u`-th coordinate of `propagatedNoise U A 𝓜 0 t` is `combMg 0 … (fun α s => U(s,t)(u,α)) t`,
for any chains `(B_x, K_x)` along the pattern `σ` and weights `|μ_j|, |μ'_j| < 1`. -/
theorem propagatedNoise_eq_combMg (μ₀ : Measure p.SiteMatrix) [IsProbabilityMeasure μ₀]
    (hz : 0 < P.z.im) (hPS : P.S = Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W)
    (σ : Fin k → Bool) (Bx : Sites p k → Fin k → RingMat p) (Kx : Sites p k → RingMat p)
    {μ μ' : Fin k → ℂ} (hμ : ∀ j, ‖μ j‖ < 1) (hμ' : ∀ j, ‖μ' j‖ < 1) :
    ∀ᵐ ω ∂driverLaw (κ := Fin (ringDim p)) μ₀, ∀ t : ℝ≥0, (t : ℝ) ≤ 1 → ∀ u : Sites p k,
      propagatedNoise (fun s t => propOp (vsTensorProp P.S μ μ' s t))
          (fun s => propOp (vsTensorGen P.S μ μ' s))
          (fun r x => chainMg 0 (zfam P.z σ) Bx Kx x r.toNNReal ω) 0 t u =
        combMg 0 (zfam P.z σ) Bx Kx (fun α s => vsTensorProp P.S μ μ' s t u α) t ω := by
  have hS : StochasticSymm P.S := hPS ▸ stochasticSymm_ring p
  filter_upwards [combMg_tensorPropagator_one μ₀ Matrix.isHermitian_zero
    (zfam_contDiff P.z σ) (zfam_im_ne_zero hz σ) Bx Kx hS hμ hμ'] with ω hω t ht u
  rw [hω t ht u]
  set M : ℝ → Sites p k → ℂ := fun r x => chainMg 0 (zfam P.z σ) Bx Kx x r.toNNReal ω
  have hM0 : M 0 = 0 := by
    funext x
    simp only [M, Real.toNNReal_zero, Pi.zero_apply]
    exact chainMg_zero _ _ _ _ _ _
  have ht0 : (0 : ℝ) ≤ t := t.2
  have hsub : uIcc (0 : ℝ) t ⊆ Icc 0 1 := by
    rw [uIcc_of_le ht0]
    exact Icc_subset_Icc le_rfl ht
  have hMc : Continuous M := continuous_pi fun x =>
    (continuous_chainMg_path hz σ Bx Kx x ω).comp continuous_real_toNNReal
  have hint : IntervalIntegrable (fun s => propOp (vsTensorProp P.S μ μ' s t)
      (propOp (vsTensorGen P.S μ μ' s) (M s - M 0))) volume 0 t := by
    refine ContinuousOn.intervalIntegrable ?_
    exact (((continuousOn_propOp_vsTensorProp_left hS hμ hμ' ht0 ht).clm_apply
      ((continuousOn_propOp_vsTensorGen hS hμ hμ').clm_apply
        (hMc.continuousOn.sub continuousOn_const)))).mono hsub
  unfold propagatedNoise
  rw [Pi.add_apply]
  have hproj := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Sites p k => ℂ) u
    ).intervalIntegral_comp_comm hint
  simp only [ContinuousLinearMap.proj_apply] at hproj
  rw [← hproj, hM0, sub_zero]
  simp only [sub_zero, M, Real.toNNReal_coe]
  congr 1
  simp_rw [← ContinuousLinearMap.comp_apply, ← propOp_mul, propOp_apply]
  refine intervalIntegral.integral_finsetSum fun α _ => ?_
  refine ContinuousOn.intervalIntegrable ?_
  exact ((continuousOn_vsTensorProp_mul_gen_entry hS hμ hμ' ht0 ht u α).mul
    ((continuous_chainMg_path hz σ Bx Kx α ω).comp
      continuous_real_toNNReal).continuousOn).mono hsub

end BlockBand.Native.ErdosRiabov.Evol
