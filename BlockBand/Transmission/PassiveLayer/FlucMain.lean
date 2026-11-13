module

public import BlockBand.Transmission.PassiveLayer.FlucCoord
public import BlockBand.Transmission.PassiveLayer.Consistency
public import BlockBand.Transmission.PathScalar.OneStep

/-!
# `PathScalar.PassiveFluctuationStep`: the `C_p/W` fluctuation of the fresh port trace

`passiveFluctuationStep_holds (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)`
proves `‖W⁻¹Tr R₊ - E W⁻¹Tr R₊‖_p ≤ C_p/W` for every passive `X`, uniformly on
`bulkInterval κ`.

Route: `freshPortTrace = τ(𝒢) = W⁻¹tr(P₂𝒢)` a.s. (`freshPortTrace_ae_eq`, Woodbury). For the
regularized input, the gradient of `τ` is `-W⁻¹tr((𝒢P₂𝒢)∂_iM)`. Its weighted norm is
`≤ √8‖𝒢‖²/W` (`grad_tau_reg`, Hilbert–Schmidt contraction `layerDir_trace_sum_le` and
`‖A‖²_HS ≤ 2W‖A‖²`). The Gaussian `L^p` inequality, moments, and `ε ↓ 0` with Fatou
(as for `bilinear`) finish the proof.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveLayer

open Matrix MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.PassiveCovariance
open BlockBand.Internal.Contracts.Inputs
open scoped Matrix.Norms.L2Operator ComplexOrder NNReal ENNReal

open BlockBand.Transmission

variable {W : ℕ}

/-- `τ(G) = W⁻¹ tr(P₂G)`, the normalized port trace. -/
def tauMap (W : ℕ) (G : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) :
    ℂ := (W : ℂ)⁻¹ * (pTwo W * G).trace

/-- `τ` as a continuous ℂ-linear map. -/
def tauCLM (W : ℕ) :
    Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := tauMap W
      map_add' := fun G H => by simp [tauMap, Matrix.trace_add, mul_add]
      map_smul' := fun c G => by simp [tauMap, Matrix.trace_smul]; ring }

theorem tauCLM_apply (G : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) :
    tauCLM W G = tauMap W G := rfl

theorem hsSq_le_card {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℂ) : hsSq A ≤ Fintype.card n * ‖A‖ ^ 2 := by
  have hcol : ∀ y : n, ∑ x, ‖A x y‖ ^ 2 ≤ ‖A‖ ^ 2 := by
    intro y
    have h := vecNorm_mulVec_le' A (Pi.single y 1)
    have hv : vecNorm (Pi.single y (1 : ℂ)) = 1 := by
      simp only [vecNorm, Pi.single_apply]
      rw [Finset.sum_eq_single y (fun z _ hz => by simp [hz]) (by simp)]; simp
    have he : A *ᵥ Pi.single y 1 = fun x => A x y := by
      ext x; simp [mulVec, dotProduct, Pi.single_apply]
    rw [hv, mul_one, he] at h
    rw [← vecNorm_sq_eq]
    exact pow_le_pow_left₀ (vecNorm_nonneg _) h 2
  unfold hsSq
  rw [Finset.sum_comm]
  calc ∑ y, ∑ x, ‖A x y‖ ^ 2 ≤ ∑ _y : n, ‖A‖ ^ 2 := Finset.sum_le_sum fun y _ => hcol y
    _ = _ := by simp

theorem card_layerSite : Fintype.card (LayerSite W .oneBlockOnePort) = 2 * W := by
  simp [Fintype.card_sum]; ring

/-- Derivative of `τ` along an affine line of matrices. -/
theorem hasDerivAt_tau_line (M N : Matrix (LayerSite W .oneBlockOnePort)
    (LayerSite W .oneBlockOnePort) ℂ) (hM : IsUnit M) :
    HasDerivAt (fun t : ℝ => tauMap W ((M + (t : ℂ) • N)⁻¹))
      (-((W : ℂ)⁻¹ * ((M⁻¹ * pTwo W * M⁻¹) * N).trace)) 0 := by
  have h := ((tauCLM W).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hasDerivAt_inv_line M N hM)
  convert h using 1
  · funext t; rfl
  rw [ContinuousLinearMap.coe_restrictScalars', tauCLM_apply, tauMap, Matrix.mul_neg, trace_neg,
    mul_neg]
  congr 2
  rw [show pTwo W * (M⁻¹ * N * M⁻¹) = (pTwo W * M⁻¹ * N) * M⁻¹ by simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm (pTwo W * M⁻¹ * N) M⁻¹]
  simp only [Matrix.mul_assoc]

theorem fderiv_tau_gReg (E : ℝ) {w : ℂ} (hw : 0 < w.im) (b : ℝ) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) {ε : ℝ} (hε : 0 < ε) (ρ : CoordW W → ℝ) (i : CoordW W) :
    fderiv ℝ (fun ρ => tauMap W (gReg E w b X ε ρ)) ρ (Pi.single i 1) =
      -((W : ℂ)⁻¹ * ((gReg E w b X ε ρ * pTwo W * gReg E w b X ε ρ) *
        layerDir b (Pi.single i 1)).trace) := by
  have hMu := (layer_isUnit_reg E hw hY hε (coordMap_hermitian b ρ)).2.1
  have hG : ContDiff ℝ 1 fun ρ => gReg E w b X ε ρ :=
    (contDiff_layerResolvent_reg E hw b hY hε).of_le le_top
  have hc : ContDiff ℝ 1 fun ρ => tauMap W (gReg E w b X ε ρ) :=
    ((tauCLM W).restrictScalars ℝ).contDiff.comp hG
  refine fderiv_apply_eq_of_line ((hc.differentiable (by simp)) ρ) ?_
  have hline : (fun t : ℝ => tauMap W (gReg E w b X ε (ρ + t • Pi.single i 1))) =
      fun t : ℝ => tauMap W ((layerMatrix .oneBlockOnePort E w (liftX (regX X ε)) (coordMap W b ρ) +
          (t : ℂ) • layerDir b (Pi.single i 1))⁻¹) := by
    funext t
    simp only [gReg, layerResolvent, layerMatrix_line]
  rw [hline]
  exact hasDerivAt_tau_line _ _ hMu

theorem grad_tau_reg {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hW : 1 ≤ W) (E : ℝ) {w : ℂ}
    (hw : 0 < w.im) {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef) {ε : ℝ}
    (hε : 0 < ε) (ρ : CoordW W → ℝ) :
    weightedGradientNorm (coordVar W b) (fun ρ => tauMap W (gReg E w b X ε ρ)) ρ ≤
      Real.sqrt 8 * ‖gReg E w b X ε ρ‖ ^ 2 / W := by
  set G := gReg E w b X ε ρ
  set A := G * pTwo W * G
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  unfold weightedGradientNorm
  simp only [fderiv_tau_gReg E hw b hY hε ρ, norm_neg, norm_mul, norm_inv, Complex.norm_natCast,
    mul_pow]
  have hsum : ∑ i, (coordVar W b i : ℝ) * ((W : ℝ)⁻¹ ^ 2 * ‖(A * layerDir b (Pi.single i 1)).trace‖ ^ 2) ≤
      (W : ℝ)⁻¹ ^ 2 * (4 / W * hsSq A) := by
    have := layerDir_trace_sum_le hb0 hb hW A
    calc _ = (W : ℝ)⁻¹ ^ 2 * ∑ i, (coordVar W b i : ℝ) * ‖(A * layerDir b (Pi.single i 1)).trace‖ ^ 2 := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this (by positivity)
  have hA : ‖A‖ ≤ ‖G‖ ^ 2 := by
    have h1 : ‖G * pTwo W‖ ≤ ‖G‖ :=
      (norm_mul_le _ _).trans (by nlinarith [norm_pTwo_le (W := W), norm_nonneg G, norm_nonneg (pTwo W)])
    calc ‖A‖ ≤ ‖G * pTwo W‖ * ‖G‖ := norm_mul_le _ _
      _ ≤ ‖G‖ * ‖G‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = ‖G‖ ^ 2 := (sq _).symm
  have hhs : hsSq A ≤ 2 * W * ‖G‖ ^ 4 := by
    have h := hsSq_le_card A
    rw [card_layerSite] at h
    have : ‖A‖ ^ 2 ≤ (‖G‖ ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hA 2
    push_cast at h
    nlinarith [norm_nonneg A]
  have hfin : (W : ℝ)⁻¹ ^ 2 * (4 / W * hsSq A) ≤ (Real.sqrt 8 * ‖G‖ ^ 2 / W) ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num)]
    have h4 : 0 ≤ 4 / (W : ℝ) := by positivity
    calc (W : ℝ)⁻¹ ^ 2 * (4 / W * hsSq A) ≤ (W : ℝ)⁻¹ ^ 2 * (4 / W * (2 * W * ‖G‖ ^ 4)) := by
          gcongr
      _ = _ := by field_simp; ring
  refine (Real.sqrt_le_sqrt (hsum.trans hfin)).trans ?_
  rw [Real.sqrt_sq (by positivity)]

theorem norm_tauMap_le (G : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) :
    ‖tauMap W G‖ ≤ 2 * ‖G‖ := by
  rcases Nat.eq_zero_or_pos W with hW | hW
  · subst hW; simp [tauMap]
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hentry : ∀ z, ‖(pTwo W * G) z z‖ ≤ ‖G‖ := by
    intro z
    have h := norm_bilinear_le (Pi.single z 1) (pTwo W * G) (Pi.single z 1)
    have hv : vecNorm (Pi.single z (1 : ℂ)) = 1 := by
      simp only [vecNorm, Pi.single_apply]
      rw [Finset.sum_eq_single z (fun y _ hy => by simp [hy]) (by simp)]; simp
    have hb : bilinear (Pi.single z 1) (pTwo W * G) (Pi.single z 1) = (pTwo W * G) z z := by
      simp [bilinear, dotProduct, mulVec, Pi.single_apply]
    rw [hb, hv, one_mul, mul_one] at h
    have hP := norm_pTwo_le (W := W)
    have hP0 := norm_nonneg (pTwo W)
    have hG0 := norm_nonneg G
    have h2 : ‖pTwo W‖ * ‖G‖ ≤ ‖G‖ := by nlinarith
    exact h.trans ((norm_mul_le _ _).trans h2)
  have htr : ‖(pTwo W * G).trace‖ ≤ 2 * W * ‖G‖ := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ z, ‖(pTwo W * G) z z‖ ≤ ∑ _z : LayerSite W .oneBlockOnePort, ‖G‖ :=
          Finset.sum_le_sum fun z _ => hentry z
      _ = 2 * W * ‖G‖ := by simp; left; ring
  rw [tauMap, norm_mul, norm_inv, Complex.norm_natCast]
  calc (W : ℝ)⁻¹ * ‖(pTwo W * G).trace‖ ≤ (W : ℝ)⁻¹ * (2 * W * ‖G‖) :=
        mul_le_mul_of_nonneg_left htr (by positivity)
    _ = 2 * ‖G‖ := by field_simp

theorem continuous_tauMap : Continuous (tauMap W) := (tauCLM W).continuous

/-- The normalized port trace of the fresh layer. -/
def tauLayer (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) :
    ℂ := tauMap W (layerAt E w X ω)

theorem measurable_tauLayer (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) :
    Measurable (tauLayer (W := W) E w X) :=
  continuous_tauMap.measurable.comp (measurable_layerAt E w X)

theorem tau_centered_reg {C₀ : ℝ} (hLp : LpGradientBody C₀) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hW : 1 ≤ W) (E : ℝ) {w : ℂ} (hw : 0 < w.im) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) {ε : ℝ} (hε : 0 < ε) {p : ℝ} (hp : 1 ≤ p)
    (hMem : MemLp (tauLayer E w (regX X ε)) (ENNReal.ofReal p) (freshLaw W b)) :
    eLpNorm (fun ω => tauLayer E w (regX X ε) ω - ∫ ω', tauLayer E w (regX X ε) ω' ∂freshLaw W b)
        (ENNReal.ofReal p) (freshLaw W b) ≤
      ENNReal.ofReal (C₀ * Real.sqrt p) * (ENNReal.ofReal (Real.sqrt 8 / W) *
        eLpNorm (fun ω => ‖layerAt E w (regX X ε) ω‖ ^ 2) (ENNReal.ofReal p) (freshLaw W b)) := by
  set F := tauLayer E w (regX X ε)
  set f : (CoordW W → ℝ) → ℂ := fun ρ => tauMap W (gReg E w b X ε ρ)
  have hfF : f = F ∘ coordMap W b := rfl
  have hcm := measurable_coordMap W b
  have hG : ContDiff ℝ 1 fun ρ => gReg E w b X ε ρ :=
    (contDiff_layerResolvent_reg E hw b hY hε).of_le le_top
  have hfc : ContDiff ℝ 1 f := ((tauCLM W).restrictScalars ℝ).contDiff.comp hG
  have hFm : AEStronglyMeasurable F ((gaussianProduct (coordVar W b)).map (coordMap W b)) := by
    rw [← freshLaw_eq_map]; exact hMem.aestronglyMeasurable
  have hMf : MemLp f (ENNReal.ofReal p) (gaussianProduct (coordVar W b)) := by
    rw [hfF]
    exact (memLp_map_measure_iff hFm hcm.aemeasurable).mp (by rw [← freshLaw_eq_map]; exact hMem)
  have h := hLp p hp (CoordW W) (coordVar W b) f hfc hMf
  have hk0 : 0 ≤ Real.sqrt 8 / W := by positivity
  have hpw : Measurable fun ω => ‖layerAt E w (regX X ε) ω‖ ^ 2 :=
    (continuous_norm.measurable.comp (measurable_layerAt E w _)).pow_const 2
  have hLHS : eLpNorm (fun ω => F ω - ∫ ω', F ω' ∂freshLaw W b) (ENNReal.ofReal p) (freshLaw W b) =
      eLpNorm (fun x => f x - ∫ y, f y ∂gaussianProduct (coordVar W b)) (ENNReal.ofReal p)
        (gaussianProduct (coordVar W b)) := by
    rw [freshLaw_eq_map, integral_map hcm.aemeasurable hFm]
    have hg : AEStronglyMeasurable (fun ω => F ω - ∫ y, F (coordMap W b y)
        ∂gaussianProduct (coordVar W b)) ((gaussianProduct (coordVar W b)).map (coordMap W b)) :=
      hFm.sub aestronglyMeasurable_const
    rw [eLpNorm_map_measure hg hcm.aemeasurable]
    rfl
  have hgrad : eLpNorm (weightedGradientNorm (coordVar W b) f) (ENNReal.ofReal p)
      (gaussianProduct (coordVar W b)) ≤ ENNReal.ofReal (Real.sqrt 8 / W) *
        eLpNorm (fun ω => ‖layerAt E w (regX X ε) ω‖ ^ 2) (ENNReal.ofReal p) (freshLaw W b) := by
    have hpt : ∀ ρ, ‖weightedGradientNorm (coordVar W b) f ρ‖ ≤
        (Real.sqrt 8 / W) * ‖layerAt E w (regX X ε) (coordMap W b ρ)‖ ^ 2 := by
      intro ρ
      rw [Real.norm_of_nonneg (by unfold weightedGradientNorm; exact Real.sqrt_nonneg _)]
      refine (grad_tau_reg hb0 hb hW E hw hY hε ρ).trans (le_of_eq ?_)
      simp only [gReg, layerAt]; ring
    have hcont : Continuous (weightedGradientNorm (coordVar W b) f) := by
      unfold weightedGradientNorm
      have hd := hfc.continuous_fderiv one_ne_zero
      refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => ?_)
      exact continuous_const.mul ((hd.clm_apply continuous_const).norm.pow 2)
    refine (eLpNorm_mono_real hcont.aestronglyMeasurable hpt).trans (le_of_eq ?_)
    have hsm := eLpNorm_const_smul (Real.sqrt 8 / W)
      ((fun ω => ‖layerAt E w (regX X ε) ω‖ ^ 2) ∘ coordMap W b) (ENNReal.ofReal p)
      (gaussianProduct (coordVar W b))
    rw [show ((Real.sqrt 8 / W) • ((fun ω => ‖layerAt E w (regX X ε) ω‖ ^ 2) ∘ coordMap W b)) =
        fun ρ => Real.sqrt 8 / W * ‖layerAt E w (regX X ε) (coordMap W b ρ)‖ ^ 2 from rfl] at hsm
    rw [hsm, Real.enorm_eq_ofReal hk0, freshLaw_eq_map,
      eLpNorm_map_measure (by rw [← freshLaw_eq_map]; exact hpw.aestronglyMeasurable)
        hcm.aemeasurable]
  rw [hLHS]
  exact h.trans (by gcongr)

theorem tendsto_tauLayer_reg (E : ℝ) (w : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) (hu : IsUnit (layerMatrix .oneBlockOnePort E w (liftX X) ω)) :
    Tendsto (fun n : ℕ => tauLayer E w (regX X (epsN n)) ω) atTop (𝓝 (tauLayer E w X ω)) :=
  (continuous_tauMap.tendsto _).comp (tendsto_layerAt_reg E w X ω hu)

theorem freshPortTrace_ae_eq {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hW : 1 ≤ W) (E : ℝ)
    (hz : 0 < (boundaryZ b E).im) {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef) :
    ∀ᵐ ω ∂freshLaw W b, PathScalar.freshPortTrace b E X ω = tauLayer E (boundaryZ b E) X ω := by
  filter_upwards [ae_g22_eq_Rplus hb0 hb hW E hz hY] with ω hω
  rw [PathScalar.freshPortTrace, passiveResolvent, ← hω, g22_eq_iota, tauLayer, tauMap, pTwo,
    Matrix.trace_mul_comm (iota2 W * layerAt E (boundaryZ b E) X ω), ← Matrix.mul_assoc]

/-- **`PathScalar.PassiveFluctuationStep`**, from `GaussianAbsorptionContract` and
`GaussianLpGradient` (explicit hypotheses). -/
theorem passiveFluctuationStep_holds (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) : PathScalar.PassiveFluctuationStep := by
  intro b hb0 hb κ hκ p hp
  obtain ⟨C₀, hC₀, hLp'⟩ := hLp
  have hp0 : 0 < p := by linarith
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  obtain ⟨Cm', W₀m, hm⟩ := moments_holds hGA b hb0 hb κ hκ (2 * p) (by linarith)
  set Cm := max Cm' 0
  have hCm : 0 ≤ Cm := le_max_right _ _
  refine ⟨2 * (C₀ * Real.sqrt p) * Real.sqrt 8 * (Cm * Cm), max W₀m 1, by positivity, ?_⟩
  intro W hW E hE X hY
  have hWm : W₀m ≤ W := le_of_max_le_left hW
  have hW1 : 1 ≤ W := le_of_max_le_right hW
  have hE1 : -2 < E := by have := hE.1; linarith
  have hE2 : E < 2 := by have := hE.2; linarith
  have hz := boundaryZ_mem_paramDisk (b := b) (by linarith) hE1 hE2
  have hzim : 0 < (boundaryZ b E).im := Bridge.boundaryZ_im_pos (by linarith) hE1 hE2
  set z := boundaryZ b E
  have hpass : ∀ X' : Matrix (Fin W) (Fin W) ℂ, (passiveY X').PosSemidef →
      MemLp (tauLayer E z X') (ENNReal.ofReal p) (freshLaw W b) ∧
      eLpNorm (tauLayer E z X') (ENNReal.ofReal p) (freshLaw W b) ≤ ENNReal.ofReal (2 * Cm) ∧
      eLpNorm (fun ω => ‖layerAt E z X' ω‖ ^ 2) (ENNReal.ofReal p) (freshLaw W b) ≤
        ENNReal.ofReal (Cm * Cm) := by
    intro X' hY'
    have hg := (letter_momBd (hm W hWm E hE z hz X' hY').2).1
    have hgp := hg.exponent_mono (show p ≤ 2 * p by linarith)
    have hτm := (measurable_tauLayer (W := W) E z X').aestronglyMeasurable (μ := freshLaw W b)
    have hτ : eLpNorm (tauLayer E z X') (ENNReal.ofReal p) (freshLaw W b) ≤ ENNReal.ofReal (2 * Cm) :=
      (eLpNorm_mono_ae_real hτm (ae_of_all _ fun ω => norm_tauMap_le _)).trans
        (hgp.const_mul zero_le_two).2
    refine ⟨lt_of_le_of_lt hτ ENNReal.ofReal_lt_top, hτ, ?_⟩
    have := (MomBd.mul hp0 hg hg hCm).2
    simpa only [sq] using this
  obtain ⟨hMem, -, -⟩ := hpass X hY
  set B := ENNReal.ofReal (C₀ * Real.sqrt p) * (ENNReal.ofReal (Real.sqrt 8 / W) *
    ENNReal.ofReal (Cm * Cm))
  have hfix : ∀ n, eLpNorm (fun ω => tauLayer E z (regX X (epsN n)) ω -
      ∫ ω', tauLayer E z (regX X (epsN n)) ω' ∂freshLaw W b) (ENNReal.ofReal p)
        (freshLaw W b) ≤ B := by
    intro n
    obtain ⟨hMn, -, hwn⟩ := hpass _ (regX_posSemidef hY (epsN_pos n).le)
    exact (tau_centered_reg hLp' hb0 hb hW1 E hzim hY (epsN_pos n) hp hMn).trans
      (mul_le_mul' le_rfl (mul_le_mul' le_rfl hwn))
  have hmean : ∀ n, ‖∫ ω', tauLayer E z (regX X (epsN n)) ω' ∂freshLaw W b‖ ≤ 2 * Cm := by
    intro n
    obtain ⟨hMn, hn, -⟩ := hpass _ (regX_posSemidef hY (epsN_pos n).le)
    have h1 := (enorm_integral_le_eLpNorm hp1 hMn.aestronglyMeasurable).trans hn
    rw [← ofReal_norm] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
  have hlim : ∀ᵐ ω ∂freshLaw W b, Tendsto (fun n => tauLayer E z (regX X (epsN n)) ω)
      atTop (𝓝 (tauLayer E z X ω)) := by
    filter_upwards [ae_good W hb0 hW1] with ω hω
    exact tendsto_tauLayer_reg E z X ω ((isUnit_iff_isUnit_det _).mpr
      (layer_schur E hzim hY hω.1 hω.2).1)
  have hF := eLpNorm_centered_le_of_tendsto hp1
    (fun n => (measurable_tauLayer E z _).aestronglyMeasurable)
    (measurable_tauLayer E z X).aestronglyMeasurable
    (hMem.integrable hp1) hlim hmean hfix
  have hae := freshPortTrace_ae_eq hb0 hb hW1 E hzim hY
  have hcongr : (fun ω => PathScalar.freshPortTrace b E X ω -
      ∫ ω', PathScalar.freshPortTrace b E X ω' ∂freshLaw W b) =ᵐ[freshLaw W b]
      fun ω => tauLayer E z X ω - ∫ ω', tauLayer E z X ω' ∂freshLaw W b := by
    have hi := integral_congr_ae hae
    filter_upwards [hae] with ω hω
    rw [hi, hω]
  rw [eLpNorm_norm (f := fun ω => PathScalar.freshPortTrace b E X ω -
      ∫ ω', PathScalar.freshPortTrace b E X ω' ∂freshLaw W b), eLpNorm_congr_ae hcongr]
  refine hF.trans (le_of_eq ?_)
  simp only [B]
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
  · congr 1
    ring
  all_goals exact ((measurable_tauLayer E z X).aestronglyMeasurable.sub
    aestronglyMeasurable_const).congr hcongr.symm

end BlockBand.Transmission.PassiveLayer
