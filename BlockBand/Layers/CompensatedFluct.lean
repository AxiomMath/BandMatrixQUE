module

public import BlockBand.Layers.CompensatedPhaseLogDet
public import BlockBand.Layers.CompensatedPhase
public import BlockBand.Layers.GaussianAbsorption

/-!
# The fluctuation of the compensated layer increment: `CphIncrementFluctuation`

The increment fluctuation step of the proof of the compensated phase lemma: the isolated input
`CphIncrementFluctuation` of `BlockBand.Layers.CompensatedPhase`.

Inputs (explicit hypotheses of `cphIncrementFluctuation_holds`, nothing else):
`Inputs.ConditionalBlockGUECount` (through `gaussianAbsorption_holds`: a.s. invertibility of
`𝒢⁻¹ = layerMatrix` and `‖‖𝒢‖‖_{L^q} ≤ C_A` for `1 ≤ q ≤ ε₁W`) and `Inputs.GaussianLpGradient`.

Law: `layerLaw W b σ` (`A_a ~ GUE_W(c/W)`, `c = 1-2b`, bonds `Gin(b/W)`), realized as the image of
`gaussianProduct (tflVar W b σ)` under `tflEmbed` (`tfl_layerLaw_eq_map`). Conditional on the old
Hermitian deformation `X` (deterministic here, as in every layer contract).

Proof.
1. **Regularized phase.** `f_κ(x) = π⁻¹ Im L(𝒢⁻¹ + iκ)` (`cplF`, `L = cplLogDet` of
   `BlockBand.Layers.CompensatedPhaseLogDet`); `𝒢⁻¹ + iκ ∈ cplDom` at every sample
   (`cpl_tflPsi_coercive`), so `f_κ` is `C¹` (`cplF_contDiff`) with
   `d f_κ(v) = π⁻¹ Im Tr((𝒢⁻¹ + iκ)⁻¹ Λv)` (`cplF_fderiv`) and `|f_κ| ≤ 4W` (`cplF_norm_le`, phase
   bound).
2. **Gradient.** `(Σᵢ vᵢ |∂ᵢ f_κ|²)^{1/2} ≤ 4 ‖(𝒢⁻¹ + iκ)⁻¹‖/π ≤ 8 ‖𝒢‖/π` (`cplF_gradient_le`,
   `tfl_weighted_trace_le`, `tflPsi_inv_le_two`): Hilbert–Schmidt norm `≤ √(4W) ‖·‖` against
   covariances `≤ 1/W`.
3. **`L^p` step.** `GaussianLpGradient`: `‖f_κ - Ef_κ‖_p ≤ C_g √p (8/π) C_A` for every `κ > 0`.
4. **`κ → 0`.** Where `A - E - X` is invertible (a.s., `srec_ae_isUnit_top`),
   `f_{κ_j} → N_-(A - E - X) + Θ_z(X₊)` (`cplF_tendsto`, the phase identity
   `cpl_tendsto_phase`); dominated convergence (`|f_κ| ≤ 4W`) for the means, Fatou for the norm
   (`cpl_fluct_core`).
5. **Small `W`** (`p > ε₁W`): the deterministic bound `|Δ - EΔ| ≤ 8W < 8p/ε₁`
   (`cpl_layer_bound`). The constant `Θ_{z_∂}(X)` cancels in the centering.

Constants: `K_p = max(C_g √p (8/π) C_A, 8p/ε₁)` with `C_g` from `GaussianLpGradient` and
`ε₁, C_A` from `GaussianAbsorptionContract` at `η₀ = (1-2b)√(4-(2-κ)²)/2`, `M = 3`; uniform in
`W ≥ 1`, Hermitian `X` and `E ∈ bulkInterval κ`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix WithLp Filter Topology
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs (gaussianProduct weightedGradientNorm GaussianLpGradient)
open BlockBand.Internal.Contracts.CoareaPalm (negativeCount)
open scoped ENNReal NNReal ComplexConjugate Matrix.Norms.L2Operator InnerProductSpace

/-!
## 1. The regularized phase in the Gaussian coordinates
-/

section Coordinates

/-- The physical block `D = A - E - X` of the layer matrix. -/
abbrev cplTop {W : ℕ} {σ : LayerShape} (E : ℝ) (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ)
    (ω : LayerSample W σ) : Matrix (PhysSite W σ) (PhysSite W σ) ℂ :=
  Internal.Contracts.Layers.blockDiag ω.1 - (E : ℂ) • (1 : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) -
    X

/-- `𝒢⁻¹ + iκ = [[D + iκ, B], [Bᴴ, z + iκ]]`. -/
theorem cpl_tflReg_layerMatrix {W : ℕ} (σ : LayerShape) (E : ℝ) (z : ℂ)
    (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) (ω : LayerSample W σ) (κ : ℝ) :
    tflReg κ (layerMatrix σ E z X ω) =
      fromBlocks (cplTop E X ω + ((κ : ℂ) * Complex.I) • 1) (bondMatrix σ ω.2) (bondMatrix σ ω.2)ᴴ
        ((z + (κ : ℂ) * Complex.I) • 1) := by
  rw [tflReg, layerMatrix, ← fromBlocks_one, fromBlocks_smul, fromBlocks_add]
  simp [add_smul]

variable (W : ℕ) (b : ℝ) (σ : LayerShape) (E : ℝ) (z : ℂ)
  (X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ)

variable {X} in
theorem cpl_tflPsi_coercive (hX : X.IsHermitian) (hz : 0 ≤ z.im) {κ : ℝ} (hκ : 0 < κ)
    (x : TflCoord W σ → ℝ) : cplCoercive κ (tflPsi W b σ E z X κ x) := by
  rw [tflPsi_eq, cpl_tflReg_layerMatrix]
  have hD : (cplTop E X (tflEmbed W b σ x)).IsHermitian :=
    layerDiag_isHermitian E X hX _ (tflEmbed_blockDiag_isHermitian W b σ x)
  have hA := cpl_coercive_herm_add hD (κ := κ)
  have hZ : cplCoercive κ ((z + (κ : ℂ) * Complex.I) • (1 : Matrix (PortSite W σ) _ ℂ)) := by
    refine cpl_coercive_mono ?_ cpl_coercive_scalar
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one]
    linarith
  have h := cpl_coercive_schurPath hκ hA hZ (bondMatrix σ (tflEmbed W b σ x).2) zero_le_one le_rfl
  simpa using h

variable {X} in
theorem cpl_tflPsi_mem (hX : X.IsHermitian) (hz : 0 ≤ z.im) {κ : ℝ} (hκ : 0 < κ)
    (x : TflCoord W σ → ℝ) : tflPsi W b σ E z X κ x ∈ cplDom (LayerSite W σ) :=
  ⟨κ, hκ, cpl_tflPsi_coercive W b σ E z hX hz hκ x⟩

/-- `w ↦ π⁻¹ Im w` as a real-linear map `ℂ → ℂ`. -/
def cplOut : ℂ →L[ℝ] ℂ := Real.pi⁻¹ • (Complex.ofRealCLM.comp Complex.imCLM)

theorem cplOut_apply (w : ℂ) : cplOut w = ((w.im / Real.pi : ℝ) : ℂ) := by
  simp [cplOut, div_eq_inv_mul, Complex.real_smul]

theorem cpl_norm_out_le (w : ℂ) : ‖cplOut w‖ ≤ ‖w‖ / Real.pi := by
  rw [cplOut_apply, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos Real.pi_pos]
  exact div_le_div_of_nonneg_right (Complex.abs_im_le_norm w) Real.pi_pos.le

/-- **The regularized phase** `f_κ(x) = π⁻¹ Im L(𝒢⁻¹ + iκ)` in real coordinates. -/
def cplF (κ : ℝ) (x : TflCoord W σ → ℝ) : ℂ :=
  cplOut (cplLogDet (tflPsi W b σ E z X κ x))

variable {X} in
theorem cplF_contDiff (hX : X.IsHermitian) (hz : 0 ≤ z.im) {κ : ℝ} (hκ : 0 < κ) :
    ContDiff ℝ 1 (cplF W b σ E z X κ) := by
  have hL : ContDiff ℝ 1 (tflPsi W b σ E z X κ) :=
    contDiff_const.add (ContinuousLinearMap.contDiff _)
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  have h := cpl_contDiffAt_logDet (cpl_tflPsi_mem W b σ E z hX hz hκ x)
  exact cplOut.contDiff.contDiffAt.comp x (h.comp x hL.contDiffAt)

variable {X} in
theorem cplF_fderiv (hX : X.IsHermitian) (hz : 0 ≤ z.im) {κ : ℝ} (hκ : 0 < κ)
    (x v : TflCoord W σ → ℝ) :
    fderiv ℝ (cplF W b σ E z X κ) x v =
      cplOut ((Ring.inverse (tflPsi W b σ E z X κ x) * tflLin W b σ v).trace) := by
  have hL : HasFDerivAt (tflPsi W b σ E z X κ)
      (LinearMap.toContinuousLinearMap (tflLinMap W b σ)) x :=
    (ContinuousLinearMap.hasFDerivAt _).const_add _
  have h1 := (cpl_hasFDerivAt_logDet (cpl_tflPsi_mem W b σ E z hX hz hκ x)).comp x hL
  have h2 := cplOut.hasFDerivAt.comp x h1
  rw [show cplF W b σ E z X κ = cplOut ∘ (cplLogDet ∘ tflPsi W b σ E z X κ) from rfl, h2.fderiv]
  simp only [ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap', cplTrMul_apply]
  rfl

variable {W} in
theorem cplF_norm_le {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ} (hX : X.IsHermitian)
    (hz : 0 ≤ z.im) {κ : ℝ} (hκ : 0 < κ) (x : TflCoord W σ → ℝ) :
    ‖cplF W b σ E z X κ x‖ ≤ 4 * W := by
  have hb := cpl_im_logDet_bounds (cpl_tflPsi_mem W b σ E z hX hz hκ x)
  have hc := tfl_card_layerSite_le W σ
  rw [cplF, cplOut_apply, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos Real.pi_pos,
    abs_of_nonneg hb.1, div_le_iff₀ Real.pi_pos]
  calc (cplLogDet (tflPsi W b σ E z X κ x)).im ≤ Fintype.card (LayerSite W σ) * Real.pi := hb.2
    _ ≤ 4 * W * Real.pi := mul_le_mul_of_nonneg_right hc Real.pi_pos.le

variable {X} in
/-- **Gradient bound**: `(Σᵢ vᵢ |∂ᵢ f_κ|²)^{1/2} ≤ 4 ‖(𝒢⁻¹ + iκ)⁻¹‖ / π`. -/
theorem cplF_gradient_le (hW : 0 < W) (hb0 : 0 < b) (hb1 : b < 1 / 2) (hX : X.IsHermitian)
    (hz : 0 ≤ z.im) {κ : ℝ} (hκ : 0 < κ) (x : TflCoord W σ → ℝ) :
    weightedGradientNorm (tflVar W b σ) (cplF W b σ E z X κ) x ≤
      4 * ‖Ring.inverse (tflPsi W b σ E z X κ x)‖ / Real.pi := by
  set R := Ring.inverse (tflPsi W b σ E z X κ x) with hR
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hder : ∀ i : TflCoord W σ, ‖fderiv ℝ (cplF W b σ E z X κ) x (Pi.single i 1)‖ ^ 2 ≤
      ‖(R * tflLin W b σ (Pi.single i 1)).trace‖ ^ 2 / Real.pi ^ 2 := by
    intro i
    rw [cplF_fderiv W b σ E z hX hz hκ, ← hR, ← div_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (cpl_norm_out_le _) 2
  obtain ⟨hA, hB⟩ := tfl_TA_TB_le hW hb0 hb1
  have hsum : ∑ i, (tflVar W b σ i : ℝ) *
      ‖fderiv ℝ (cplF W b σ E z X κ) x (Pi.single i 1)‖ ^ 2 ≤ (4 * ‖R‖ / Real.pi) ^ 2 := by
    calc ∑ i, (tflVar W b σ i : ℝ) * ‖fderiv ℝ (cplF W b σ E z X κ) x (Pi.single i 1)‖ ^ 2
        ≤ ∑ i, (tflVar W b σ i : ℝ) * (‖(R * tflLin W b σ (Pi.single i 1)).trace‖ ^ 2 /
            Real.pi ^ 2) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hder i) (NNReal.coe_nonneg _)
      _ = (∑ i, (tflVar W b σ i : ℝ) * ‖(R * tflLin W b σ (Pi.single i 1)).trace‖ ^ 2) /
            Real.pi ^ 2 := by
          rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ (16 * ‖R‖ ^ 2) / Real.pi ^ 2 := by
          gcongr
          have h1 := tfl_weighted_trace_le W b σ R
          have h2 := tfl_hs_le R
          have h3 := tfl_card_layerSite_le W σ
          have hHS0 : 0 ≤ ∑ x, ∑ y, ‖R x y‖ ^ 2 := by positivity
          have hc : 2 * (tflTA W b : ℝ) + 2 * (tflTB W b : ℝ) ≤ 4 / W := by
            have : (4 : ℝ) / W = 2 * (1 / W) + 2 * (1 / W) := by ring
            rw [this]; linarith
          calc ∑ i, (tflVar W b σ i : ℝ) * ‖(R * tflLin W b σ (Pi.single i 1)).trace‖ ^ 2
              ≤ (2 * (tflTA W b : ℝ) + 2 * (tflTB W b : ℝ)) * ∑ x, ∑ y, ‖R x y‖ ^ 2 := h1
            _ ≤ (4 / W) * (4 * W * ‖R‖ ^ 2) := by
                gcongr
                exact h2.trans (mul_le_mul_of_nonneg_right h3 (by positivity))
            _ = 16 * ‖R‖ ^ 2 := by field_simp; ring
      _ = (4 * ‖R‖ / Real.pi) ^ 2 := by ring
  unfold weightedGradientNorm
  calc Real.sqrt (∑ i, (tflVar W b σ i : ℝ) *
        ‖fderiv ℝ (cplF W b σ E z X κ) x (Pi.single i 1)‖ ^ 2)
      ≤ Real.sqrt ((4 * ‖R‖ / Real.pi) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = 4 * ‖R‖ / Real.pi := Real.sqrt_sq (by positivity)

variable {X} in
/-- **The `κ → 0` limit**: where `D = A - E - X` is invertible,
`f_{κ_j}(x) → N_-(D) + Θ_z(X₊)`. -/
theorem cplF_tendsto (hX : X.IsHermitian) (hz : 0 < z.im) (x : TflCoord W σ → ℝ)
    (hD : IsUnit (cplTop E X (tflEmbed W b σ x)).det) :
    Tendsto (fun j => cplF W b σ E z X (cplKappa j) x) atTop
      (𝓝 (((negativeCount (cplTop E X (tflEmbed W b σ x)) : ℝ) +
        phaseCount z (layerSchur σ E X (tflEmbed W b σ x)) : ℝ) : ℂ)) := by
  have hDh : (cplTop E X (tflEmbed W b σ x)).IsHermitian :=
    layerDiag_isHermitian E X hX _ (tflEmbed_blockDiag_isHermitian W b σ x)
  have h := cpl_tendsto_phase hDh hD (bondMatrix σ (tflEmbed W b σ x).2) hz
  have h2 := (Complex.continuous_ofReal.tendsto _).comp h
  refine h2.congr fun j => ?_
  simp only [Function.comp_apply, cplF, cplOut_apply, tflPsi_eq, cpl_tflReg_layerMatrix]

end Coordinates

/-!
## 2. The fluctuation bound for one fresh layer
-/

section Fluct

/-- **Core fluctuation bound.** From the gradient inequality (constant `Cg`), a.s. invertibility
of `𝒢⁻¹` and `‖‖𝒢‖‖_{L^p} ≤ CA`: for any Borel `G` equal, at samples with Hermitian blocks, to
`N_-(A - E - X) + Θ_z(X₊)`, `‖G - EG‖_p ≤ Cg √p (8/π) CA`. -/
theorem cpl_fluct_core {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hgr : ∀ (p : ℝ), 1 ≤ p → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (v : ι → ℝ≥0)
      (f : (ι → ℝ) → ℂ), ContDiff ℝ 1 f → MemLp f (ENNReal.ofReal p) (gaussianProduct v) →
        eLpNorm (fun x => f x - ∫ y, f y ∂gaussianProduct v) (ENNReal.ofReal p)
            (gaussianProduct v) ≤
          ENNReal.ofReal (Cg * Real.sqrt p) *
            eLpNorm (weightedGradientNorm v f) (ENNReal.ofReal p) (gaussianProduct v))
    {W : ℕ} (hW : 0 < W) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (σ : LayerShape)
    {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ} (hX : X.IsHermitian) (E : ℝ) {z : ℂ}
    (hz : 0 < z.im) {p : ℝ} (hp : 1 ≤ p) {CA : ℝ}
    (hinv : ∀ᵐ ω ∂layerLaw W b σ, IsUnit (layerMatrix σ E z X ω).det)
    (hmom : eLpNorm (fun ω => ‖layerResolvent σ E z X ω‖) (ENNReal.ofReal p)
      (layerLaw W b σ) ≤ ENNReal.ofReal CA)
    {G : LayerSample W σ → ℝ} (hG : Measurable G)
    (hGeq : ∀ ω : LayerSample W σ, (∀ j, (ω.1 j).IsHermitian) →
      G ω = (negativeCount (cplTop E X ω) : ℝ) + phaseCount z (layerSchur σ E X ω)) :
    eLpNorm (fun ω => G ω - ∫ ω', G ω' ∂layerLaw W b σ) (ENNReal.ofReal p) (layerLaw W b σ) ≤
      ENNReal.ofReal (Cg * Real.sqrt p * (8 / Real.pi) * CA) := by
  set μ := gaussianProduct (tflVar W b σ) with hμ
  set Φ := tflEmbed W b σ with hΦdef
  have hΦ : Measurable Φ := tfl_measurable_embed W b σ
  have hlaw : layerLaw W b σ = μ.map Φ := tfl_layerLaw_eq_map W b σ
  have hz0 : 0 ≤ z.im := hz.le
  set Gc : LayerSample W σ → ℂ := fun ω => (G ω : ℂ) with hGcdef
  have hGc : Measurable Gc := Complex.measurable_ofReal.comp hG
  -- pass to complex values
  have hreal : eLpNorm (fun ω => G ω - ∫ ω', G ω' ∂layerLaw W b σ) (ENNReal.ofReal p)
      (layerLaw W b σ) =
      eLpNorm (fun ω => Gc ω - ∫ ω', Gc ω' ∂layerLaw W b σ) (ENNReal.ofReal p) (layerLaw W b σ) := by
    have hint : ∫ ω', Gc ω' ∂layerLaw W b σ = ((∫ ω', G ω' ∂layerLaw W b σ : ℝ) : ℂ) :=
      integral_ofReal
    refine eLpNorm_congr_norm_ae (hG.sub_const _).aestronglyMeasurable
      (hGc.sub_const _).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [hint, hGcdef, ← Complex.ofReal_sub, Complex.norm_real]
  rw [hreal]
  set F : (TflCoord W σ → ℝ) → ℂ := fun x => Gc (Φ x) with hFdef
  have hF : Measurable F := hGc.comp hΦ
  have htransfer : eLpNorm (fun ω => Gc ω - ∫ ω', Gc ω' ∂layerLaw W b σ) (ENNReal.ofReal p)
      (layerLaw W b σ) = eLpNorm (fun x => F x - ∫ y, F y ∂μ) (ENNReal.ofReal p) μ := by
    rw [hlaw, integral_map hΦ.aemeasurable hGc.aestronglyMeasurable,
      eLpNorm_map_measure (hGc.sub_const _).aestronglyMeasurable hΦ.aemeasurable]
    rfl
  rw [htransfer]
  set Gr : (TflCoord W σ → ℝ) → Matrix (LayerSite W σ) (LayerSite W σ) ℂ :=
    fun x => layerResolvent σ E z X (Φ x) with hGrdef
  have hinvμ : ∀ᵐ x ∂μ, IsUnit (layerMatrix σ E z X (Φ x)).det := by
    rw [hlaw] at hinv
    exact ae_of_ae_map hΦ.aemeasurable hinv
  have hDμ : ∀ᵐ x ∂μ, IsUnit (cplTop E X (Φ x)).det := by
    have h := srec_ae_isUnit_top hb1 σ E X
    rw [hlaw] at h
    exact ae_of_ae_map hΦ.aemeasurable h
  have hmomμ : eLpNorm (fun x => ‖Gr x‖) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal CA := by
    rw [hlaw, eLpNorm_map_measure (measurable_norm_layerResolvent σ E z X).aestronglyMeasurable
      hΦ.aemeasurable] at hmom
    exact hmom
  set c : ℝ := 8 / Real.pi with hc
  have hc0 : 0 ≤ c := by positivity
  set Bd : ℝ≥0∞ := ENNReal.ofReal (Cg * Real.sqrt p * c * CA) with hBd
  have hp0 : 0 ≤ p := by linarith
  -- the bound for each regularization
  have hstep : ∀ κ : ℝ, 0 < κ →
      eLpNorm (fun x => cplF W b σ E z X κ x - ∫ y, cplF W b σ E z X κ y ∂μ)
        (ENNReal.ofReal p) μ ≤ Bd := by
    intro κ hκ
    have hC := cplF_contDiff W b σ E z hX hz0 hκ
    have hcont : Continuous (cplF W b σ E z X κ) := hC.continuous
    have hmem : MemLp (cplF W b σ E z X κ) (ENNReal.ofReal p) μ :=
      MemLp.of_bound hcont.aestronglyMeasurable (4 * W)
        (ae_of_all _ fun x => cplF_norm_le b σ E z hX hz0 hκ x)
    have h1 := hgr p hp (TflCoord W σ) (tflVar W b σ) (cplF W b σ E z X κ) hC hmem
    refine h1.trans ?_
    have hwc : Continuous (weightedGradientNorm (tflVar W b σ) (cplF W b σ E z X κ)) := by
      have hd := hC.continuous_fderiv one_ne_zero
      unfold weightedGradientNorm
      refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => ?_)
      exact continuous_const.mul ((hd.clm_apply continuous_const).norm.pow 2)
    have hwle : ∀ᵐ x ∂μ, ‖weightedGradientNorm (tflVar W b σ) (cplF W b σ E z X κ) x‖ ≤
        ‖c * ‖Gr x‖‖ := by
      filter_upwards [hinvμ] with x hx
      have hg := cplF_gradient_le W b σ E z hW hb0 hb1 hX hz0 hκ x
      have h2 := tflPsi_inv_le_two W b σ E z hX hz0 hκ x hx
      have hg0 : 0 ≤ weightedGradientNorm (tflVar W b σ) (cplF W b σ E z X κ) x :=
        Real.sqrt_nonneg _
      rw [Real.norm_of_nonneg hg0, Real.norm_of_nonneg (by positivity)]
      refine hg.trans ?_
      calc 4 * ‖Ring.inverse (tflPsi W b σ E z X κ x)‖ / Real.pi
          ≤ 4 * (2 * ‖Gr x‖) / Real.pi := by gcongr
        _ = c * ‖Gr x‖ := by rw [hc]; ring
    have h4 := eLpNorm_mono_ae (p := ENNReal.ofReal p) hwc.aestronglyMeasurable hwle
    have h5 : eLpNorm (fun x => c * ‖Gr x‖) (ENNReal.ofReal p) μ =
        ENNReal.ofReal c * eLpNorm (fun x => ‖Gr x‖) (ENNReal.ofReal p) μ := by
      rw [show (fun x => c * ‖Gr x‖) = c • (fun x => ‖Gr x‖) from rfl,
        eLpNorm_const_smul, Real.enorm_eq_ofReal hc0]
    calc ENNReal.ofReal (Cg * Real.sqrt p) *
          eLpNorm (weightedGradientNorm (tflVar W b σ) (cplF W b σ E z X κ)) (ENNReal.ofReal p) μ
        ≤ ENNReal.ofReal (Cg * Real.sqrt p) * (ENNReal.ofReal c * ENNReal.ofReal CA) := by
          gcongr
          exact h4.trans (h5.le.trans (by gcongr))
      _ = Bd := by
          rw [hBd, ← ENNReal.ofReal_mul hc0, ← ENNReal.ofReal_mul (by positivity)]
          ring_nf
  -- the limit `κ_j → 0`
  set Fm : ℕ → (TflCoord W σ → ℝ) → ℂ := fun j => cplF W b σ E z X (cplKappa j) with hFm
  have hFmc : ∀ j, Continuous (Fm j) := fun j =>
    (cplF_contDiff W b σ E z hX hz0 (cpl_kappa_pos j)).continuous
  have hconv : ∀ᵐ x ∂μ, Tendsto (fun j => Fm j x) atTop (𝓝 (F x)) := by
    filter_upwards [hDμ] with x hx
    have h := cplF_tendsto W b σ E z hX hz x hx
    have hFx : F x = (((negativeCount (cplTop E X (tflEmbed W b σ x)) : ℝ) +
        phaseCount z (layerSchur σ E X (tflEmbed W b σ x)) : ℝ) : ℂ) := by
      simp only [hFdef, hGcdef, hΦdef]
      rw [hGeq _ fun j => gueOfCoords_isHermitian _ _ _]
    rw [hFx]
    exact h
  have hbound : ∀ j, ∀ᵐ x ∂μ, ‖Fm j x‖ ≤ 4 * W := fun j =>
    ae_of_all _ fun x => cplF_norm_le b σ E z hX hz0 (cpl_kappa_pos j) x
  have hint : Tendsto (fun j => ∫ x, Fm j x ∂μ) atTop (𝓝 (∫ x, F x ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun _ => (4 * W : ℝ))
      (fun j => (hFmc j).aestronglyMeasurable) (integrable_const _) hbound hconv
  have hconv2 : ∀ᵐ x ∂μ, Tendsto (fun j => Fm j x - ∫ y, Fm j y ∂μ) atTop
      (𝓝 (F x - ∫ y, F y ∂μ)) := hconv.mono fun x hx => hx.sub hint
  have hfatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := ENNReal.ofReal p)
    (fun j => ((hFmc j).sub continuous_const).aestronglyMeasurable)
    (fun x => F x - ∫ y, F y ∂μ) (hF.sub_const _).aestronglyMeasurable hconv2
  refine hfatou.trans (Filter.liminf_le_of_frequently_le' (Frequently.of_forall fun j => ?_))
  exact hstep (cplKappa j) (cpl_kappa_pos j)

/-- **One layer, both regimes.** If `Δ = G - c` a.s. with Borel `G`, `|G| ≤ 4W`, `G` equal to
`N_-(A - E - X) + Θ_z(X₊)` at samples with Hermitian blocks, then
`‖Δ - EΔ‖_p ≤ max(Cg √p (8/π) CA, 8p/ε₁)`: the core bound when `p ≤ ε₁ W`, the deterministic
bound `8W < 8p/ε₁` otherwise. -/
theorem cpl_layer_bound {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hgr : ∀ (p : ℝ), 1 ≤ p → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (v : ι → ℝ≥0)
      (f : (ι → ℝ) → ℂ), ContDiff ℝ 1 f → MemLp f (ENNReal.ofReal p) (gaussianProduct v) →
        eLpNorm (fun x => f x - ∫ y, f y ∂gaussianProduct v) (ENNReal.ofReal p)
            (gaussianProduct v) ≤
          ENNReal.ofReal (Cg * Real.sqrt p) *
            eLpNorm (weightedGradientNorm v f) (ENNReal.ofReal p) (gaussianProduct v))
    {ε₁ CA : ℝ} (hε₁ : 0 < ε₁)
    {W : ℕ} (hW : 0 < W) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) (σ : LayerShape)
    {X : Matrix (PhysSite W σ) (PhysSite W σ) ℂ} (hX : X.IsHermitian) (E : ℝ) {z : ℂ}
    (hz : 0 < z.im) {p : ℝ} (hp : 1 ≤ p)
    (hinv : ∀ᵐ ω ∂layerLaw W b σ, IsUnit (layerMatrix σ E z X ω).det)
    (hmom : ∀ q : ℝ, 1 ≤ q → q ≤ ε₁ * W →
      eLpNorm (fun ω => ‖layerResolvent σ E z X ω‖) (ENNReal.ofReal q) (layerLaw W b σ) ≤
        ENNReal.ofReal CA)
    {G Δ : LayerSample W σ → ℝ} (hG : Measurable G) (hGb : ∀ ω, |G ω| ≤ 4 * W)
    (hGeq : ∀ ω : LayerSample W σ, (∀ j, (ω.1 j).IsHermitian) →
      G ω = (negativeCount (cplTop E X ω) : ℝ) + phaseCount z (layerSchur σ E X ω))
    {c : ℝ} (hΔ : Δ =ᵐ[layerLaw W b σ] fun ω => G ω - c) :
    eLpNorm (fun ω => Δ ω - ∫ ω', Δ ω' ∂layerLaw W b σ) (ENNReal.ofReal p) (layerLaw W b σ) ≤
      ENNReal.ofReal (max (Cg * Real.sqrt p * (8 / Real.pi) * CA) (8 * p / ε₁)) := by
  have hGi : Integrable G (layerLaw W b σ) :=
    cph_integrable_of_bound hG.aestronglyMeasurable hGb
  have hI : ∫ ω', Δ ω' ∂layerLaw W b σ = (∫ ω', G ω' ∂layerLaw W b σ) - c := by
    rw [integral_congr_ae hΔ, integral_sub hGi (integrable_const _), integral_const, probReal_univ,
      one_smul]
  have hae : (fun ω => Δ ω - ∫ ω', Δ ω' ∂layerLaw W b σ) =ᵐ[layerLaw W b σ]
      fun ω => G ω - ∫ ω', G ω' ∂layerLaw W b σ := by
    filter_upwards [hΔ] with ω hω
    rw [hω, hI]; ring
  rw [eLpNorm_congr_ae hae]
  by_cases hpW : p ≤ ε₁ * W
  · exact (cpl_fluct_core hCg hgr hW hb0 hb1 σ hX E hz hp hinv (hmom p hp hpW) hG hGeq).trans
      (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  · have hW' : (W : ℝ) < p / ε₁ := by
      rw [lt_div_iff₀ hε₁]; linarith [not_le.mp hpW]
    have hIb : |∫ ω', G ω' ∂layerLaw W b σ| ≤ 4 * W := cph_abs_integral_le hGb
    have hb : ∀ᵐ ω ∂layerLaw W b σ, ‖G ω - ∫ ω', G ω' ∂layerLaw W b σ‖ ≤ 8 * W :=
      ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]
        have := hGb ω
        rw [abs_le] at this hIb ⊢
        constructor <;> linarith
    refine (eLpNorm_le_of_ae_bound (hG.sub_const _).aestronglyMeasurable hb).trans ?_
    rw [measure_univ, ENNReal.one_rpow, one_mul]
    refine ENNReal.ofReal_le_ofReal ((le_max_right _ _).trans' ?_)
    rw [mul_div_assoc]
    linarith

end Fluct

/-!
## 3. The two port configurations and `CphIncrementFluctuation`
-/

section Shapes

/-- Borel `N_-(A - E - X) + Θ_{z_∂}(X₊)`, separate ports. -/
def cplSepG (b E : ℝ) {W : ℕ} (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ℓ : LayerSample W .separate) : ℝ :=
  cphRawSum cphNegInd (cplTop E X ℓ) + cphPhase (boundaryZ b E) (layerSchur .separate E X ℓ)

/-- Borel `N_-(A - E - X) + Θ_{z₀}(X₊)`, common port. -/
def cplComG (b E : ℝ) {W : ℕ} (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ℓ : LayerSample W .common) : ℝ :=
  cphRawSum cphNegInd (cplTop E X ℓ) + cphPhase (commonZ b E) (layerSchur .common E X ℓ)

theorem cpl_measurable_sepG (b E : ℝ) {W : ℕ} (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Measurable (cplSepG b E X) :=
  ((cph_measurable_rawSum cph_measurable_negInd).comp
    (cph_measurable_top E measurable_const measurable_fst)).add
    ((cph_measurable_phase _).comp (srec_measurable_layerSchur E measurable_const measurable_id))

theorem cpl_measurable_comG (b E : ℝ) {W : ℕ} (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Measurable (cplComG b E X) :=
  ((cph_measurable_rawSum cph_measurable_negInd).comp
    (cph_measurable_top E measurable_const measurable_fst)).add
    ((cph_measurable_phase _).comp (cph_measurable_layerSchur_common E measurable_const
      measurable_id))

theorem cpl_abs_G_le {W : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {z : ℂ} (hz : 0 ≤ z.im)
    (hι : (Fintype.card ι : ℝ) ≤ 2 * W) (D : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (Y : Matrix ι ι ℂ) : |cphRawSum cphNegInd D + cphPhase z Y| ≤ 4 * W := by
  have h0 := cph_rawNeg_nonneg D
  have h1 := cph_rawNeg_le D
  have h2 := cph_phase_nonneg hz Y
  have h3 := cph_phase_le z Y
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat] at h1
  rw [abs_of_nonneg (add_nonneg h0 h2)]
  linarith

/-- **`CphIncrementFluctuation`**: for each `p ≥ 1` the conditionally centered fresh-layer
increment `N_-(A - E - X) + Θ_z(X₊) - Θ_{z_∂}(X)` (separate ports `z = z_∂`, common port
`z = z₀`) has `L^p(layerLaw)` norm `≤ K_p`, uniformly in `W ≥ 1`, Hermitian `X` and
`E ∈ bulkInterval κ`. From `ConditionalBlockGUECount` (through `gaussianAbsorption_holds`) and
`GaussianLpGradient`; `K_p = max(C_g √p (8/π) C_A, 8p/ε₁)`. -/
theorem cphIncrementFluctuation_holds (hcount : Internal.Contracts.Inputs.ConditionalBlockGUECount)
    (hgrad : GaussianLpGradient) : CphIncrementFluctuation := by
  obtain ⟨Cg, hCg, hgr⟩ := hgrad
  have habs := gaussianAbsorption_holds hcount
  refine ⟨fun b hb0 hb1 κ hκ p hp => ?_, fun b hb0 hb1 κ hκ p hp => ?_⟩
  · rcases (bulkInterval κ).eq_empty_or_nonempty with he | ⟨E₀, hE₀⟩
    · exact ⟨0, fun W _ X _ E hE => by rw [he] at hE; exact absurd hE (Set.notMem_empty E)⟩
    set η₀ := (1 - 2 * b) * Real.sqrt (4 - (2 - κ) ^ 2) / 2 with hη₀
    have hη : 0 < η₀ := (commonZ_im_pos_of_mem_bulkInterval hb1 hκ hE₀).1
    obtain ⟨ε₁, CA, hε₁, -, habs'⟩ := habs b hb0 hb1 η₀ 3 hη
    refine ⟨max (Cg * Real.sqrt p * (8 / Real.pi) * CA) (8 * p / ε₁), fun W hW X hX E hE => ?_⟩
    have hzη : η₀ ≤ (boundaryZ b E).im := by
      refine le_trans ?_ (boundaryZ_im_ge_of_mem_bulkInterval (by linarith) hκ hE)
      have hs := Real.sqrt_nonneg (4 - (2 - κ) ^ 2)
      rw [hη₀]; nlinarith
    have hz3 : ‖boundaryZ b E‖ ≤ 3 :=
      norm_boundaryZ_le hb0.le (by linarith) (abs_lt_two_of_mem_bulkInterval hκ hE).le
    obtain ⟨hinv, hmom⟩ := habs' W hW .separate X hX E (boundaryZ b E) hzη hz3
    have hz : 0 < (boundaryZ b E).im := lt_of_lt_of_le hη hzη
    refine cpl_layer_bound hCg.le hgr hε₁ hW hb0 hb1 .separate hX E hz hp hinv hmom
      (cpl_measurable_sepG b E X) (fun ℓ => cpl_abs_G_le hz.le (by simp) _ _) (fun ℓ hA => ?_)
      (c := cphPhase (boundaryZ b E) X) ?_
    · unfold cplSepG
      rw [cph_negativeCount_eq_rawSum, cph_phaseCount_eq (srec_layerSchur_isHermitian E hX ℓ hA)]
    · filter_upwards [cph_sepIncrement_ae_eq b E hX (W := W)] with ℓ hℓ
      rw [hℓ]
      rfl
  · rcases (bulkInterval κ).eq_empty_or_nonempty with he | ⟨E₀, hE₀⟩
    · exact ⟨0, fun W _ X _ E hE => by rw [he] at hE; exact absurd hE (Set.notMem_empty E)⟩
    set η₀ := (1 - 2 * b) * Real.sqrt (4 - (2 - κ) ^ 2) / 2 with hη₀
    have hη : 0 < η₀ := (commonZ_im_pos_of_mem_bulkInterval hb1 hκ hE₀).1
    obtain ⟨ε₁, CA, hε₁, -, habs'⟩ := habs b hb0 hb1 η₀ 3 hη
    refine ⟨max (Cg * Real.sqrt p * (8 / Real.pi) * CA) (8 * p / ε₁), fun W hW X hX E hE => ?_⟩
    have hzη : η₀ ≤ (commonZ b E).im := (commonZ_im_pos_of_mem_bulkInterval hb1 hκ hE).2
    have hz3 : ‖commonZ b E‖ ≤ 3 :=
      norm_commonZ_le hb0.le (by linarith) (abs_lt_two_of_mem_bulkInterval hκ hE).le
    obtain ⟨hinv, hmom⟩ := habs' W hW .common X hX E (commonZ b E) hzη hz3
    have hz : 0 < (commonZ b E).im := lt_of_lt_of_le hη hzη
    have hW' : (0 : ℝ) ≤ W := Nat.cast_nonneg _
    refine cpl_layer_bound hCg.le hgr hε₁ hW hb0 hb1 .common hX E hz hp hinv hmom
      (cpl_measurable_comG b E X)
      (fun ℓ => cpl_abs_G_le hz.le (by simp; linarith) _ _) (fun ℓ hA => ?_)
      (c := cphPhase (boundaryZ b E) X) ?_
    · unfold cplComG
      rw [cph_negativeCount_eq_rawSum,
        cph_phaseCount_eq (rng_layerSchur_common_isHermitian E hX ℓ hA)]
    · filter_upwards [lct_ae_blocks_isHermitian W b .common] with ℓ hℓ
      rw [cph_comIncrement_eq b E hX hℓ]
      rfl

end Shapes

end BlockBand.Layers
