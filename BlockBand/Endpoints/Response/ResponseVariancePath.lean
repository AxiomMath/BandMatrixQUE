module

public import BlockBand.Endpoints.Response.ResponseVarianceSample

/-!
# Cauchy–Schwarz in the path measure

Cauchy–Schwarz in the path measure, the signed response trace bound and the Gaussian variance
lower bound give `|E ∂_{q_m}(F_L+F_R)(e)| ≤ C (E_{path,h}|h*B_qh/h*Ah|²)^{1/2}`; the multiplier
costs `E[(Tr A)²(1+g)]`.

* `rv_signedPassDerivative_sq_le`:
  `(E ∂_q(F_L+F_R))² ≤ C₁² · E[(1+√g)²(Tr A)²] · E_{path,h}|h*B_qh/h*Ah|²`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
  BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.ClocksCommonPort
  BlockBand.Internal.Contracts.Inputs
open scoped ENNReal NNReal ComplexOrder

variable {b e x y : ℝ} {W r : ℕ}

/-!
### Almost-sure invertibility at a fixed real energy
-/

/-- The full path matrix with its matched leads is a.s. invertible at every bulk real energy
(from `ConditionalBlockGUECount`, through `ae_isUnit_schur`).
-/
theorem rv_ae_isUnit_fullPathMatrix (hCount : ConditionalBlockGUECount) (hb1 : b < 1 / 2)
    (he1 : -2 < e) (he2 : e < 2) (hW : 0 < W) (r : ℕ) :
    ∀ᵐ ω ∂growthPathLaw W b, IsUnit (fullPathMatrix b e W r ω).det := by
  have hb : b < 1 := by linarith
  filter_upwards [ae_isUnit_schur hCount guelawBridge_holds hb1 he1 he2 hW r] with ω hω
  rw [fullPathMatrix_eq]
  exact isUnit_det_fromBlocks_of_schur (boundaryZ_ne_zero hb he1 he2) hω

/-!
### Integrability of the two expected derivatives
-/

theorem rv_pencilSourceGram_eq {q : ℝ → ℝ} (hq : ∀ t, 0 ≤ q t) (ω : GrowthPath W) :
    pencilSourceGram (fullPathMatrix b e W r ω) (sourceRoot W r q) (leadInclusion W r) =
      rvSourceGram b e W r q ω := by
  rw [pencilSourceGram_sourceRoot hq]; rfl

theorem rv_sourceGram_trace_le (hW : 0 < W) {q : ℝ → ℝ} (hq : ∀ t, |q t| ≤ 1)
    (ω : GrowthPath W) :
    (rvSourceGram b e W r q ω).trace.re ≤ (rvLeadClock b e W r ω).trace.re := by
  have h := (rv_sandwich (b := b) (e := e) (r := r) hW hq ω).2.1.trace_nonneg
  rw [trace_sub] at h
  have := (Complex.nonneg_iff.1 h).1
  rw [Complex.sub_re] at this
  linarith

theorem rv_abs_le_one_of_part {q : ℝ → ℝ} (hq : ∀ t, |q t| ≤ 1) :
    (∀ t, |posPart q t| ≤ 1) ∧ (∀ t, |negPart q t| ≤ 1) := by
  refine ⟨fun t => ?_, fun t => ?_⟩
  · have := abs_le.1 (hq t)
    rw [abs_le]; constructor <;> simp only [posPart] <;> [linarith [le_max_right (q t) 0];
      exact max_le this.2 zero_le_one]
  · have := abs_le.1 (hq t)
    rw [abs_le]; constructor <;> simp only [negPart] <;> [linarith [le_max_right (-q t) 0];
      exact max_le (by linarith) zero_le_one]

theorem rv_posPart_nonneg (q : ℝ → ℝ) (t : ℝ) : 0 ≤ posPart q t := le_max_right _ _

theorem rv_negPart_nonneg (q : ℝ → ℝ) (t : ℝ) : 0 ≤ negPart q t := le_max_right _ _

theorem rv_integrable_leadClock_trace {Cm : ℝ}
    (hCm : ∫⁻ ω, ENNReal.ofReal ((1 + Real.sqrt (rvConductance b e W r ω)) ^ 2 *
        (rvLeadClock b e W r ω).trace.re ^ 2) ∂growthPathLaw W b ≤ ENNReal.ofReal Cm) :
    Integrable (fun ω => (rvLeadClock b e W r ω).trace.re) (growthPathLaw W b) := by
  have := passDeriv_isProbabilityMeasure_growthPathLaw W b
  have hm : Measurable (fun ω => (rvLeadClock b e W r ω).trace.re) :=
    Complex.measurable_re.comp ((continuous_id.matrix_trace).measurable.comp
      (rv_measurable_leadClock_of b W r measurable_const measurable_id))
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω =>
    rv_leadClock_trace_nonneg b e W r ω)]
  refine lt_of_le_of_lt (lintegral_mono fun ω => ?_ : _ ≤ ∫⁻ ω, (1 + ENNReal.ofReal
    ((1 + Real.sqrt (rvConductance b e W r ω)) ^ 2 * (rvLeadClock b e W r ω).trace.re ^ 2))
      ∂growthPathLaw W b) ?_
  · rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hA := rv_leadClock_trace_nonneg b e W r ω
    have hg : 1 ≤ (1 + Real.sqrt (rvConductance b e W r ω)) ^ 2 := by
      nlinarith [Real.sqrt_nonneg (rvConductance b e W r ω)]
    nlinarith [sq_nonneg ((rvLeadClock b e W r ω).trace.re - 1),
      mul_le_mul_of_nonneg_right hg (sq_nonneg (rvLeadClock b e W r ω).trace.re)]
  · rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    exact ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, lt_of_le_of_lt hCm ENNReal.ofReal_lt_top⟩

theorem rv_integrable_portRatioDeriv (hb0 : 0 < b) (hb1 : b < 1 / 2) (he1 : -2 < e)
    (he2 : e < 2) (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1) (hW : 0 < W) {q : ℝ → ℝ}
    (hq0 : ∀ t, 0 ≤ q t) (hq1 : ∀ t, |q t| ≤ 1) {Cm : ℝ}
    (hinv : ∀ᵐ ω ∂growthPathLaw W b, IsUnit (fullPathMatrix b e W r ω).det)
    (hCm : ∫⁻ ω, ENNReal.ofReal ((1 + Real.sqrt (rvConductance b e W r ω)) ^ 2 *
        (rvLeadClock b e W r ω).trace.re ^ 2) ∂growthPathLaw W b ≤ ENNReal.ofReal Cm) :
    Integrable (fun ω => portRatioDeriv b e x y W r q ω) (growthPathLaw W b) := by
  have hb : b ≤ 1 := by linarith
  have hA := rv_integrable_leadClock_trace hCm
  refine Integrable.mono' (hA.const_mul (8 * ratioC1 x y)) ?_ ?_
  · have : (fun ω => portRatioDeriv b e x y W r q ω) =
        fun ω => portDeriv b e x y W r q 0 ω + portDeriv b e x y W r q 1 ω := by
      funext ω; exact portRatioDeriv_eq_add _ _ _ _ _ _ _ _
    rw [this]
    exact ((measurable_portDeriv 0).add (measurable_portDeriv 1)).aestronglyMeasurable
  · filter_upwards [ae_growthPath_isHermitian W b, hinv] with ω hH hM
    obtain ⟨-, h2⟩ := portRatio_pointwise hb he1 he2 hx hy0 hy1 hq0 hH
    have h4 := (h2 hM).2.2
    rw [Real.norm_eq_abs]
    have hη1 := etaZ_le_one hb0.le he1 he2
    have hη0 := etaZ_nonneg hb he1 he2
    have hc1 := ratioC1_nonneg hx hy0 hy1
    rw [rv_pencilSourceGram_eq hq0] at h4
    have hT := rv_sourceGram_trace_le (b := b) (e := e) (r := r) hW hq1 ω
    have hT0 : 0 ≤ (rvSourceGram b e W r q ω).trace.re := by
      have := (rv_posSemidef_conj_diagonal (rvLeadFrame b e W r ω)
        (d := rvSourceWeight W r q) (fun z => by
          rcases z with s | a
          · exact div_nonneg (hq0 _) (by positivity)
          · exact le_refl _)).trace_nonneg
      rw [← rv_sourceDiag_eq] at this
      exact (Complex.nonneg_iff.1 this).1
    calc |portRatioDeriv b e x y W r q ω|
        ≤ 2 * (ratioC1 x y * (4 * etaZ b e * (rvSourceGram b e W r q ω).trace.re)) := h4
      _ ≤ 2 * (ratioC1 x y * (4 * 1 * (rvLeadClock b e W r ω).trace.re)) := by
          gcongr
      _ = 8 * ratioC1 x y * (rvLeadClock b e W r ω).trace.re := by ring

/-- **The expected signed derivative is the expectation of the sample derivative.** -/
theorem rv_signedPassDerivative_eq_integral (hb0 : 0 < b) (hb1 : b < 1 / 2) (he1 : -2 < e)
    (he2 : e < 2) (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1) (hW : 0 < W) {q : ℝ → ℝ}
    (hq : ∀ t, |q t| ≤ 1) {Cm : ℝ}
    (hinv : ∀ᵐ ω ∂growthPathLaw W b, IsUnit (fullPathMatrix b e W r ω).det)
    (hCm : ∫⁻ ω, ENNReal.ofReal ((1 + Real.sqrt (rvConductance b e W r ω)) ^ 2 *
        (rvLeadClock b e W r ω).trace.re ^ 2) ∂growthPathLaw W b ≤ ENNReal.ofReal Cm) :
    signedPassDerivative b e x y W r q = ∫ ω, rvSignedDeriv b e x y W r q ω ∂growthPathLaw W b := by
  have hb : b ≤ 1 := by linarith
  obtain ⟨hp1, hn1⟩ := rv_abs_le_one_of_part hq
  have hderiv : ∀ q' : ℝ → ℝ, (∀ t, 0 ≤ q' t) →
      (fun ω => derivWithin (fun κ => portRatioSum b e x y W r q' κ ω) (Ici 0) 0) =ᵐ[growthPathLaw W b]
        fun ω => portRatioDeriv b e x y W r q' ω := by
    intro q' hq'
    filter_upwards [ae_growthPath_isHermitian W b, hinv] with ω hH hM
    obtain ⟨-, h2⟩ := portRatio_pointwise hb he1 he2 hx hy0 hy1 hq' hH
    exact (h2 hM).2.1.derivWithin (uniqueDiffWithinAt_Ici 0)
  rw [signedPassDerivative, integral_congr_ae (hderiv _ (rv_posPart_nonneg q)),
    integral_congr_ae (hderiv _ (rv_negPart_nonneg q)), ← integral_sub
      (rv_integrable_portRatioDeriv hb0 hb1 he1 he2 hx hy0 hy1 hW (rv_posPart_nonneg q) hp1 hinv hCm)
      (rv_integrable_portRatioDeriv hb0 hb1 he1 he2 hx hy0 hy1 hW (rv_negPart_nonneg q) hn1 hinv hCm)]
  rfl

/-!
### Cauchy–Schwarz
-/

theorem rv_ennreal_sqrt_mul_sq (X Y : ℝ≥0∞) :
    (X ^ (1 / 2 : ℝ) * Y ^ (1 / 2 : ℝ)) ^ 2 = X * Y := by
  rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul]
  norm_num

/-- Cauchy–Schwarz in the path measure:
`(E ∂_q(F_L+F_R))² ≤ C₁² · E[(1+√g)²(Tr A)²] · E_{path,h}|h*B_qh/h*Ah|²`,
`C₁ = 4 max(x+y, c) √(2c_G)`. -/
theorem rv_signedPassDerivative_sq_le {c cG Cm : ℝ} (hc : 0 ≤ c) (hcG : 0 < cG) (hCm0 : 0 ≤ Cm)
    (hb0 : 0 < b) (hb1 : b < 1 / 2) (he1 : -2 < e) (he2 : e < 2) (hx : 0 ≤ x) (hy0 : 0 ≤ y)
    (hy1 : y < 1) (hW : 0 < W) {q : ℝ → ℝ} (hq : ∀ t, |q t| ≤ 1)
    (hD : ∀ ω : GrowthPath W, (∀ k, (ω.1 k).IsHermitian) →
      IsUnit (fullPathMatrix b e W r ω).det →
      |rvSignedDeriv b e x y W r q ω| ≤ 4 * etaZ b e *
        ((x + y) * |(rvSourceGram b e W r q ω).trace.re| +
          c * Real.sqrt (rvConductance b e W r ω) * Real.sqrt (hsSq (rvSourceGram b e W r q ω))))
    (hG : ∀ A B : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, IsSandwichedOn B A →
      B.trace.re ^ 2 + hsSq B ≤
        cG * A.trace.re ^ 2 * ∫ h, (quadForm B h / quadForm A h) ^ 2
          ∂circularVectorLaw (Fin 2 × Fin W))
    (hinv : ∀ᵐ ω ∂growthPathLaw W b, IsUnit (fullPathMatrix b e W r ω).det)
    (hCm : ∫⁻ ω, ENNReal.ofReal ((1 + Real.sqrt (rvConductance b e W r ω)) ^ 2 *
        (rvLeadClock b e W r ω).trace.re ^ 2) ∂growthPathLaw W b ≤ ENNReal.ofReal Cm) :
    signedPassDerivative b e x y W r q ^ 2 ≤
      (4 * max (x + y) c * Real.sqrt (2 * cG)) ^ 2 * Cm *
        ∫ z, rvRatio q b e W r z ^ 2 ∂probedClockLaw W b := by
  have hP := passDeriv_isProbabilityMeasure_growthPathLaw W b
  have hPr := isProbabilityMeasure_probedClockLaw W b
  have hb : b ≤ 1 := by linarith
  rw [rv_signedPassDerivative_eq_integral hb0 hb1 he1 he2 hx hy0 hy1 hW hq hinv hCm]
  set C₁ := 4 * max (x + y) c * Real.sqrt (2 * cG) with hC₁
  have hC₁0 : 0 ≤ C₁ := by
    have : 0 ≤ max (x + y) c := hc.trans (le_max_right _ _)
    positivity
  set K₀ : GrowthPath W → ℝ := fun ω =>
    (1 + Real.sqrt (rvConductance b e W r ω)) * (rvLeadClock b e W r ω).trace.re
  set S : GrowthPath W → ℝ := fun ω =>
    Real.sqrt (∫ h, rvRatio q b e W r (ω, h) ^ 2 ∂circularVectorLaw (Fin 2 × Fin W))
  have hK₀ : ∀ ω, 0 ≤ K₀ ω := fun ω =>
    mul_nonneg (by positivity) (rv_leadClock_trace_nonneg b e W r ω)
  have hS : ∀ ω, 0 ≤ S ω := fun ω => Real.sqrt_nonneg _
  -- measurability
  have hZm : Measurable (fun z : GrowthPath W × (Fin 2 × Fin W → ℂ) => rvRatio q b e W r z ^ 2) :=
    (rv_measurable_ratio_of q b W r measurable_const measurable_id).pow_const 2
  have hK₀m : Measurable K₀ :=
    ((measurable_const.add (rv_measurable_conductance_of b W r measurable_const
      measurable_id).sqrt)).mul (Complex.measurable_re.comp ((continuous_id.matrix_trace).measurable.comp
        (rv_measurable_leadClock_of b W r measurable_const measurable_id)))
  have hIm : Measurable (fun ω : GrowthPath W =>
      ∫ h, rvRatio q b e W r (ω, h) ^ 2 ∂circularVectorLaw (Fin 2 × Fin W)) :=
    (hZm.stronglyMeasurable.integral_prod_right' (ν := circularVectorLaw (Fin 2 × Fin W))).measurable
  have hSm : Measurable S := hIm.sqrt
  have hZb : ∀ z, |rvRatio q b e W r z ^ 2| ≤ 1 := fun z => by
    rw [abs_of_nonneg (sq_nonneg _)]
    have := rv_abs_ratio_le hq b e W r z
    nlinarith [abs_nonneg (rvRatio q b e W r z), sq_abs (rvRatio q b e W r z)]
  have hZint : Integrable (fun z => rvRatio q b e W r z ^ 2) (probedClockLaw W b) :=
    Integrable.of_bound hZm.aestronglyMeasurable 1 (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact hZb z)
  -- pointwise bound
  have hpt : ∀ᵐ ω ∂growthPathLaw W b, ‖rvSignedDeriv b e x y W r q ω‖ₑ ≤
      ENNReal.ofReal C₁ * (ENNReal.ofReal (K₀ ω) * ENNReal.ofReal (S ω)) := by
    filter_upwards [ae_growthPath_isHermitian W b, hinv] with ω hH hM
    have h := rv_signedDeriv_le_ratio (b := b) (e := e) (r := r) hc hcG
      (add_nonneg hx hy0) hW (etaZ_le_one hb0.le he1 he2) (hD ω hH hM)
      (hG _ _ (rv_sandwich hW hq ω))
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (hK₀ ω), ← ENNReal.ofReal_mul hC₁0]
    refine ENNReal.ofReal_le_ofReal (h.trans (le_of_eq ?_))
    simp only [K₀, S]; ring
  -- Hölder
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (growthPathLaw W b) Real.HolderConjugate.two_two
    (f := fun ω => ENNReal.ofReal (K₀ ω)) (g := fun ω => ENNReal.ofReal (S ω))
    hK₀m.ennreal_ofReal.aemeasurable hSm.ennreal_ofReal.aemeasurable
  have hK2 : ∫⁻ ω, ENNReal.ofReal (K₀ ω) ^ (2 : ℝ) ∂growthPathLaw W b ≤ ENNReal.ofReal Cm := by
    refine le_trans (le_of_eq (lintegral_congr fun ω => ?_)) hCm
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (hK₀ ω)]
    congr 1; simp only [K₀]; ring
  have hS2 : ∫⁻ ω, ENNReal.ofReal (S ω) ^ (2 : ℝ) ∂growthPathLaw W b =
      ENNReal.ofReal (∫ z, rvRatio q b e W r z ^ 2 ∂probedClockLaw W b) := by
    have e1 : ∀ ω, ENNReal.ofReal (S ω) ^ (2 : ℝ) =
        ENNReal.ofReal (∫ h, rvRatio q b e W r (ω, h) ^ 2 ∂circularVectorLaw (Fin 2 × Fin W)) := by
      intro ω
      rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (hS ω), Real.sq_sqrt
        (integral_nonneg fun h => sq_nonneg _)]
    simp_rw [e1]
    have hint : Integrable (fun ω : GrowthPath W =>
        ∫ h, rvRatio q b e W r (ω, h) ^ 2 ∂circularVectorLaw (Fin 2 × Fin W)) (growthPathLaw W b) :=
      hZint.integral_prod_left
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun ω =>
      integral_nonneg fun h => sq_nonneg _)]
    congr 1
    exact (integral_prod _ hZint).symm
  set I := ∫ z, rvRatio q b e W r z ^ 2 ∂probedClockLaw W b
  have hI0 : 0 ≤ I := integral_nonneg fun z => sq_nonneg _
  have hmain : ‖∫ ω, rvSignedDeriv b e x y W r q ω ∂growthPathLaw W b‖ₑ ^ 2 ≤
      ENNReal.ofReal (C₁ ^ 2 * Cm * I) := by
    have h1 : ‖∫ ω, rvSignedDeriv b e x y W r q ω ∂growthPathLaw W b‖ₑ ≤
        ENNReal.ofReal C₁ * ((∫⁻ ω, ENNReal.ofReal (K₀ ω) ^ (2 : ℝ) ∂growthPathLaw W b) ^
          (1 / 2 : ℝ) * (∫⁻ ω, ENNReal.ofReal (S ω) ^ (2 : ℝ) ∂growthPathLaw W b) ^
            (1 / 2 : ℝ)) := by
      calc ‖∫ ω, rvSignedDeriv b e x y W r q ω ∂growthPathLaw W b‖ₑ
          ≤ ∫⁻ ω, ‖rvSignedDeriv b e x y W r q ω‖ₑ ∂growthPathLaw W b :=
            enorm_integral_le_lintegral_enorm _
        _ ≤ ∫⁻ ω, ENNReal.ofReal C₁ * (ENNReal.ofReal (K₀ ω) * ENNReal.ofReal (S ω))
            ∂growthPathLaw W b := lintegral_mono_ae hpt
        _ = ENNReal.ofReal C₁ * ∫⁻ ω, ENNReal.ofReal (K₀ ω) * ENNReal.ofReal (S ω)
            ∂growthPathLaw W b := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ _ := by gcongr; exact hH
    have h2 := pow_le_pow_left₀ zero_le h1 2
    rw [mul_pow, rv_ennreal_sqrt_mul_sq, hS2] at h2
    refine h2.trans ?_
    calc ENNReal.ofReal C₁ ^ 2 * ((∫⁻ ω, ENNReal.ofReal (K₀ ω) ^ (2 : ℝ) ∂growthPathLaw W b) *
          ENNReal.ofReal I)
        ≤ ENNReal.ofReal C₁ ^ 2 * (ENNReal.ofReal Cm * ENNReal.ofReal I) := by gcongr
      _ = ENNReal.ofReal (C₁ ^ 2 * Cm * I) := by
          rw [← ENNReal.ofReal_pow hC₁0, ← ENNReal.ofReal_mul hCm0, ← ENNReal.ofReal_mul
            (by positivity), mul_assoc]
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs] at hmain
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hmain

end BlockBand.Endpoints
