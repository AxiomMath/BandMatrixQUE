module

public import BlockBand.Native.ErdosRiabov.Evol.Main
public import BlockBand.Native.ErdosRiabov.VS.TailBridgeTensor

/-!
# Integrated Itô form of the chains, pathwise

For every sample, traces of resolvent chains along the VS band process equal their initial value
plus the integrated drift plus the martingale part.

For a chain `(B, K)` along the pattern `σ` put (complex, `t ∈ [0,1]`)
`cVal r = tr(K G_{[1,k]}(r)(H_r))` and `cDrift r = tr(K · dGmat(r, H_r))`.
* `cVal_re`, `cVal_im`, `cDrift_re`, `cDrift_im`: real and imaginary parts are the chain test
  functions `chainTestT … K`, `chainTestT … (-iK)` and their drifts (`itoDrift`) along
  `Y_r - Y_0 = vsNoise p r⁺ ω`; `continuousOn_cDrift`: `cDrift` is continuous on `[0,1]`.
* **`cVal_ito`** (integrated Itô form, every sample, all `t ∈ [0,1]` at once):
  `cVal t = cVal 0 + ∫_0^t cDrift + 𝓜_t`, with `𝓜 = VS.chainMg` (the complex martingale part).
  This is the definition of `smCompensated` (no null set); the martingale property of `𝓜` is
  `VS.resolventChain_ito_vs`.
* `continuous_chainMg_path`: `t ↦ 𝓜_t` is continuous on `ℝ≥0` for **every** sample.
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
open BlockBand.Native.CEH.Flow
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess.Stochastic
open scoped NNReal

/-- The short-ring profile of the parameters is stochastic symmetric. -/
theorem stochasticSymm_ring (p : BlockBand.Parameters) :
    StochasticSymm (Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W) :=
  shortRingProfile_stochasticSymm p.b_pos p.b_lt_half (by have := p.n_ge_four; omega) p.W_pos

/-- Along a continuous path, the Itô drift of a `C²` test function is continuous. -/
theorem continuous_itoDrift_path {d : ℕ} {φ : ℝ × (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ 2 φ)
    {y : ℝ → Fin d → ℝ} (hy : Continuous y) (b : Fin d → ℝ) (A : Matrix (Fin d) (Fin d) ℝ) :
    Continuous fun s : ℝ => itoDrift φ (y s) s.toNNReal b A := by
  have hq : Continuous fun s : ℝ => (((s.toNNReal : ℝ≥0) : ℝ), y s) :=
    (NNReal.continuous_coe.comp continuous_real_toNNReal).prodMk hy
  have h1 : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by norm_num)
  have h2 : Continuous (fderiv ℝ (fderiv ℝ φ)) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  have c1 := h1.comp hq
  have c2 := h2.comp hq
  unfold itoDrift partialTime partialSpace partialSpace2
  refine ((c1.clm_apply continuous_const).add (continuous_finsetSum _ fun i _ =>
    continuous_const.mul (c1.clm_apply continuous_const))).add
    (continuous_const.mul (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      continuous_const.mul ((c2.clm_apply continuous_const).clm_apply continuous_const)))

variable {p : BlockBand.Parameters} {k : ℕ}

/-- The path `r ↦ H_r = vsBandFin p r⁺ ω` (real time). -/
def pathH (p : BlockBand.Parameters) (ω : RingSample p) (r : ℝ) : RingMat p :=
  vsBandFin p r.toNNReal ω

/-- `cVal r = tr(K G_{[1,k]}(r)(H_r))` for slots `B`. -/
def cVal (P : PsiData (p.n * p.W)) (σ : Fin k → Bool) (B : Fin k → RingMat p) (K : RingMat p)
    (ω : RingSample p) (r : ℝ) : ℂ :=
  trace (K * gChain (patZ P.z σ r) B (pathH p ω r))

/-- `cDrift r = tr(K · dGmat(r, H_r))`. -/
def cDrift (P : PsiData (p.n * p.W)) (σ : Fin k → Bool) (B : Fin k → RingMat p) (K : RingMat p)
    (ω : RingSample p) (r : ℝ) : ℂ :=
  trace (K * dGmat P.S P.z σ B r (pathH p ω r))

/-- The constant chain family of the pattern (all chains along `vsPatternSpec`). -/
abbrev zfam {ι : Type*} (z : ℂ) (σ : Fin k → Bool) : ι → Fin k → ℝ → ℂ :=
  fun _ => vsPatternSpec z (semicircleM z) σ

theorem zfam_contDiff {ι : Type*} (z : ℂ) (σ : Fin k → Bool) :
    ∀ (α : ι) j, ContDiff ℝ 2 (zfam (ι := ι) z σ α j) :=
  fun _ _ => contDiff_vsSpec _ _ (contDiff_vsSat _ (n := 2))

theorem zfam_im_ne_zero {ι : Type*} {z : ℂ} (hz : 0 < z.im) (σ : Fin k → Bool) :
    ∀ (α : ι) j t, (zfam (ι := ι) z σ α j t).im ≠ 0 :=
  fun _ j t => vsSpec_im_ne_zero hz (semicircleM_im_pos hz) (σ j) t

theorem coe_toNNReal_of_mem {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) : ((r.toNNReal : ℝ≥0) : ℝ) = r :=
  Real.coe_toNNReal r hr.1

theorem continuous_noisePath (ω : RingSample p) :
    Continuous fun r : ℝ => vsNoise p r.toNNReal ω :=
  (continuous_vsNoise p ω).comp continuous_real_toNNReal

variable {P : PsiData (p.n * p.W)}

theorem cVal_re (hz : 0 < P.z.im) (σ : Fin k → Bool) (B : Fin k → RingMat p) (K : RingMat p)
    (ω : RingSample p) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    (cVal P σ B K ω r).re = chainTestT 0 (ringMatrixFin p)
      (vsPatternSpec P.z (semicircleM P.z) σ) B K (r, vsNoise p r.toNNReal ω) := by
  rw [chainTestT_eq_reTr_gChain hz σ B K hr.2]
  rfl

theorem cVal_im (hz : 0 < P.z.im) (σ : Fin k → Bool) (B : Fin k → RingMat p) (K : RingMat p)
    (ω : RingSample p) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    (cVal P σ B K ω r).im = chainTestT 0 (ringMatrixFin p)
      (vsPatternSpec P.z (semicircleM P.z) σ) B (-Complex.I • K) (r, vsNoise p r.toNNReal ω) := by
  rw [chainTestT_eq_reTr_gChain hz σ B _ hr.2, reTr_neg_I_smul]
  rfl

theorem cDrift_re (hz : 0 < P.z.im)
    (hPS : P.S = Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W) (σ : Fin k → Bool)
    (B : Fin k → RingMat p) (K : RingMat p) (ω : RingSample p) {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) 1) :
    (cDrift P σ B K ω r).re = itoDrift (chainTestT 0 (ringMatrixFin p)
      (vsPatternSpec P.z (semicircleM P.z) σ) B K) (vsNoise p r.toNNReal ω) r.toNNReal 0
        (diagonal (ringVariance p)) := by
  rw [itoDrift_chainTestT_ring Matrix.isHermitian_zero _ (zfam_contDiff (ι := Unit) P.z σ ())
    (zfam_im_ne_zero (ι := Unit) hz σ ()), chainDrift_eq_reTr_dGmat hz σ B K
    (by rw [coe_toNNReal_of_mem hr]; exact hr.2), coe_toNNReal_of_mem hr, ← hPS]
  rfl

theorem cDrift_im (hz : 0 < P.z.im)
    (hPS : P.S = Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W) (σ : Fin k → Bool)
    (B : Fin k → RingMat p) (K : RingMat p) (ω : RingSample p) {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) 1) :
    (cDrift P σ B K ω r).im = itoDrift (chainTestT 0 (ringMatrixFin p)
      (vsPatternSpec P.z (semicircleM P.z) σ) B (-Complex.I • K)) (vsNoise p r.toNNReal ω)
        r.toNNReal 0 (diagonal (ringVariance p)) := by
  rw [itoDrift_chainTestT_ring Matrix.isHermitian_zero _ (zfam_contDiff (ι := Unit) P.z σ ())
    (zfam_im_ne_zero (ι := Unit) hz σ ()), chainDrift_eq_reTr_dGmat hz σ B _
    (by rw [coe_toNNReal_of_mem hr]; exact hr.2), coe_toNNReal_of_mem hr, ← hPS,
    reTr_neg_I_smul]
  rfl

theorem continuous_itoDrift_chain (hz : 0 < P.z.im) (σ : Fin k → Bool) (B : Fin k → RingMat p)
    (K : RingMat p) (ω : RingSample p) :
    Continuous fun r : ℝ => itoDrift (chainTestT 0 (ringMatrixFin p)
      (vsPatternSpec P.z (semicircleM P.z) σ) B K) (vsNoise p r.toNNReal ω) r.toNNReal 0
        (diagonal (ringVariance p)) :=
  continuous_itoDrift_path (contDiff_chainTestT_ring Matrix.isHermitian_zero
    (zfam_contDiff (ι := Unit) P.z σ) (zfam_im_ne_zero (ι := Unit) hz σ) B K ())
    (continuous_noisePath ω) 0 _

theorem continuousOn_cDrift (hz : 0 < P.z.im)
    (hPS : P.S = Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W) (σ : Fin k → Bool)
    (B : Fin k → RingMat p) (K : RingMat p) (ω : RingSample p) :
    ContinuousOn (cDrift P σ B K ω) (Icc 0 1) := by
  have h1 := continuous_itoDrift_chain hz σ B K ω
  have h2 := continuous_itoDrift_chain hz σ B (-Complex.I • K) ω
  have hc : Continuous fun r : ℝ =>
      ((itoDrift (chainTestT 0 (ringMatrixFin p) (vsPatternSpec P.z (semicircleM P.z) σ) B K)
        (vsNoise p r.toNNReal ω) r.toNNReal 0 (diagonal (ringVariance p)) : ℝ) : ℂ) +
      ((itoDrift (chainTestT 0 (ringMatrixFin p) (vsPatternSpec P.z (semicircleM P.z) σ) B
        (-Complex.I • K)) (vsNoise p r.toNNReal ω) r.toNNReal 0
          (diagonal (ringVariance p)) : ℝ) : ℂ) * Complex.I :=
    (Complex.continuous_ofReal.comp h1).add
      ((Complex.continuous_ofReal.comp h2).mul continuous_const)
  refine hc.continuousOn.congr fun r hr => ?_
  apply Complex.ext
  · simp [cDrift_re hz hPS σ B K ω hr]
  · simp [cDrift_im hz hPS σ B K ω hr]

/-- **Pathwise continuity of the chain martingale parts** (every sample). -/
theorem continuous_chainMg_path (hz : 0 < P.z.im) (σ : Fin k → Bool) {ι : Type*} [Fintype ι]
    (Bι : ι → Fin k → RingMat p) (Kι : ι → RingMat p) (α : ι) (ω : RingSample p) :
    Continuous fun t : ℝ≥0 => chainMg 0 (zfam P.z σ) Bι Kι α t ω := by
  have c1 := continuous_smCompensated_path (vsNoise p) (diagonal (ringVariance p))
    (continuous_vsNoise p ω) (contDiff_chainTestT_ring Matrix.isHermitian_zero
      (zfam_contDiff (ι := ι) P.z σ) (zfam_im_ne_zero hz σ) (Bι α) (Kι α) α).continuous
    fun T => (continuous_itoDrift_chain hz σ (Bι α) (Kι α) ω).integrableOn_Ioc
  have c2 := continuous_smCompensated_path (vsNoise p) (diagonal (ringVariance p))
    (continuous_vsNoise p ω) (contDiff_chainTestT_ring Matrix.isHermitian_zero
      (zfam_contDiff (ι := ι) P.z σ) (zfam_im_ne_zero hz σ) (Bι α) (-Complex.I • Kι α)
        α).continuous
    fun T => (continuous_itoDrift_chain hz σ (Bι α) (-Complex.I • Kι α) ω).integrableOn_Ioc
  exact (Complex.continuous_ofReal.comp c1).add
    ((Complex.continuous_ofReal.comp c2).mul continuous_const)

/-- The real martingale part, unfolded: `M_t = f(t, Y_t) - f(0, Y_0) - ∫_0^t (Itô drift)`. -/
theorem smCompensated_chain_eq (σ : Fin k → Bool) (B : Fin k → RingMat p) (K : RingMat p)
    (ω : RingSample p) {t : ℝ} (ht0 : 0 ≤ t) :
    smCompensated (testProc (chainTestT 0 (ringMatrixFin p)
        (vsPatternSpec P.z (semicircleM P.z) σ) B K) (vsNoise p))
      (testDrift (chainTestT 0 (ringMatrixFin p) (vsPatternSpec P.z (semicircleM P.z) σ) B K)
        (vsNoise p) (diagonal (ringVariance p))) 0 t.toNNReal ω =
      chainTestT 0 (ringMatrixFin p) (vsPatternSpec P.z (semicircleM P.z) σ) B K
          (t, vsNoise p t.toNNReal ω) -
        chainTestT 0 (ringMatrixFin p) (vsPatternSpec P.z (semicircleM P.z) σ) B K
          (0, vsNoise p (0 : ℝ).toNNReal ω) -
        ∫ s in (0 : ℝ)..t, itoDrift (chainTestT 0 (ringMatrixFin p)
          (vsPatternSpec P.z (semicircleM P.z) σ) B K) (vsNoise p s.toNNReal ω) s.toNNReal 0
            (diagonal (ringVariance p)) := by
  rw [intervalIntegral.integral_of_le ht0]
  simp only [smCompensated, testProc, testDrift, Real.coe_toNNReal t ht0, Real.toNNReal_zero,
    NNReal.coe_zero]

/-- **Integrated Itô form of a chain** (every sample, every `t ∈ [0,1]`):
`tr(K G(t)) = tr(K G(0)) + ∫_0^t tr(K dGmat(s, H_s)) ds + 𝓜_t`, `𝓜 = VS.chainMg`. -/
theorem cVal_ito (hz : 0 < P.z.im)
    (hPS : P.S = Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W) (σ : Fin k → Bool)
    {ι : Type*} (Bι : ι → Fin k → RingMat p) (Kι : ι → RingMat p) (α : ι) (ω : RingSample p)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    cVal P σ (Bι α) (Kι α) ω t = cVal P σ (Bι α) (Kι α) ω 0 +
      (∫ s in (0 : ℝ)..t, cDrift P σ (Bι α) (Kι α) ω s) +
        chainMg 0 (zfam P.z σ) Bι Kι α t.toNNReal ω := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hsub : uIcc (0 : ℝ) t ⊆ Icc 0 1 := by
    rw [uIcc_of_le ht.1]
    exact Icc_subset_Icc le_rfl ht.2
  have hint : IntervalIntegrable (cDrift P σ (Bι α) (Kι α) ω) volume 0 t :=
    ((continuousOn_cDrift hz hPS σ (Bι α) (Kι α) ω).mono hsub).intervalIntegrable
  have hre : (∫ s in (0 : ℝ)..t, cDrift P σ (Bι α) (Kι α) ω s).re =
      ∫ s in (0 : ℝ)..t, itoDrift (chainTestT 0 (ringMatrixFin p)
        (vsPatternSpec P.z (semicircleM P.z) σ) (Bι α) (Kι α)) (vsNoise p s.toNNReal ω)
          s.toNNReal 0 (diagonal (ringVariance p)) := by
    rw [← Complex.reCLM_apply, ← Complex.reCLM.intervalIntegral_comp_comm hint]
    refine intervalIntegral.integral_congr fun s hs => ?_
    simp only [Complex.reCLM_apply]
    exact cDrift_re hz hPS σ _ _ ω (hsub hs)
  have him : (∫ s in (0 : ℝ)..t, cDrift P σ (Bι α) (Kι α) ω s).im =
      ∫ s in (0 : ℝ)..t, itoDrift (chainTestT 0 (ringMatrixFin p)
        (vsPatternSpec P.z (semicircleM P.z) σ) (Bι α) (-Complex.I • Kι α))
          (vsNoise p s.toNNReal ω) s.toNNReal 0 (diagonal (ringVariance p)) := by
    rw [← Complex.imCLM_apply, ← Complex.imCLM.intervalIntegral_comp_comm hint]
    refine intervalIntegral.integral_congr fun s hs => ?_
    simp only [Complex.imCLM_apply]
    exact cDrift_im hz hPS σ _ _ ω (hsub hs)
  have hmre := smCompensated_chain_eq (P := P) σ (Bι α) (Kι α) ω ht.1
  have hmim := smCompensated_chain_eq (P := P) σ (Bι α) (-Complex.I • Kι α) ω ht.1
  apply Complex.ext
  · rw [Complex.add_re, Complex.add_re, hre, cVal_re hz σ _ _ ω ht, cVal_re hz σ _ _ ω h0]
    simp only [chainMg, chainMgRe, chainMgIm, zfam, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, add_zero]
    rw [hmre, Real.toNNReal_zero]
    ring
  · rw [Complex.add_im, Complex.add_im, him, cVal_im hz σ _ _ ω ht, cVal_im hz σ _ _ ω h0]
    simp only [chainMg, chainMgRe, chainMgIm, zfam, Complex.add_im, Complex.ofReal_re,
      Complex.mul_im, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      zero_add]
    rw [hmim, Real.toNNReal_zero]
    ring

end BlockBand.Native.ErdosRiabov.Evol
