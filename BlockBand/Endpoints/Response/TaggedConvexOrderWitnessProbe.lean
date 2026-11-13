module

public import BlockBand.Endpoints.Response.TaggedConvexOrderWitnessStop

/-!
# Probe averages of the explicit witness at a fixed path

**Results.**
* `tcw_F_bound`: dimension-free `0 ≤ E_h Z_{l;k}^m ≤ c_m (Tr Q_{l;k})^m` at every path
  (`tco_lintegral_quadForm_pow_le`), with `h`-integrability.
* `tcw_ae_drift_path`: a.s. in the path, `0 ≤ G ≤ X²` for every probe `h`.
* `tcw_abs_H_le`: a.s. `|H_l| ≤ (D₀/2)|m(m-1)| F_l`.
* `tcw_integrable_F`, `tcw_integrable_H`: path integrability from the moments.
* `tcw_remainder_eq`: `ε_l(m) - d_l(m) = E tcw_rem`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Polynomial Finset Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Inputs
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder ENNReal NNReal

theorem tcw_probedClockLaw_eq (W : ℕ) (b : ℝ) :
    probedClockLaw W b = (growthPathLaw W b).prod (circularVectorLaw (Fin 2 × Fin W)) := rfl

/-- **Dimension-free probe moment** at every path: `0 ≤ E_h Z_{l;k}^m ≤ c_m (Tr Q_{l;k})^m`. -/
theorem tcw_F_bound (m : ℕ) : ∃ c : ℝ, 0 ≤ c ∧ ∀ (b e : ℝ) (W l k : ℕ) (ω : GrowthPath W),
    Integrable (fun h => lmf_tagResponseClock b e W l k (ω, h) ^ m)
      (circularVectorLaw (Fin 2 × Fin W)) ∧
    0 ≤ tcw_F b e W l k m ω ∧ tcw_F b e W l k m ω ≤ c * (tco_tagQ b e W l k ω).trace.re ^ m := by
  obtain ⟨c, hc0, hc⟩ := tco_lintegral_quadForm_pow_le m
  refine ⟨c, hc0, fun b e W l k ω => ?_⟩
  have hQ := tco_posSemidef_tagQ b e W l k ω
  have hmeas : Measurable (fun h : Fin 2 × Fin W → ℂ => quadForm (tco_tagQ b e W l k ω) h ^ m) :=
    ((tco_continuous_quadForm.comp (continuous_const.prodMk continuous_id)).pow m).measurable
  have h0 : ∀ h, 0 ≤ quadForm (tco_tagQ b e W l k ω) h ^ m :=
    fun h => pow_nonneg (tco_quadForm_nonneg_of_posSemidef hQ h) m
  have hK : 0 ≤ c * (tco_tagQ b e W l k ω).trace.re ^ m :=
    mul_nonneg hc0 (pow_nonneg (tco_trace_tagQ_nonneg b e W l k ω) m)
  obtain ⟨hI, hle⟩ := integrable_and_integral_le_of_lintegral hmeas h0 hK
    (hc (Fin 2 × Fin W) _ hQ)
  have e : (fun h => lmf_tagResponseClock b e W l k (ω, h) ^ m) =
      fun h => quadForm (tco_tagQ b e W l k ω) h ^ m := by
    funext h; rw [tco_tagClock_eq_quadForm]
  unfold tcw_F
  rw [e]
  exact ⟨hI, integral_nonneg h0, hle⟩

/-- A.s. in the path, `0 ≤ G ≤ X²` for every probe. -/
theorem tcw_ae_drift_path (hCount : ConditionalBlockGUECount) {b e : ℝ} (hb1 : b < 1 / 2)
    (he1 : -2 < e) (he2 : e < 2) {W : ℕ} (hW : 0 < W) (l k : ℕ) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ h, 0 ≤ tcw_G b e W l k (ω, h) ∧
      tcw_G b e W l k (ω, h) ≤ tcw_X b e W l k (ω, h) ^ 2 := by
  filter_upwards [ae_growthPath_isHermitian W b,
    rv_ae_isUnit_fullPathMatrix hCount hb1 he1 he2 hW l] with ω h1 h2 h
  obtain ⟨hP'h, hP'P'⟩ := tcs_pathProjection (n := l) h1 h2
  exact tcs_drift_sign (tcs_nearProjection_hermitian W) (tcs_nearProjection_idem W)
    hP'h hP'P' (tcw_v b e W l k (ω, h))

theorem tcw_coef_eq_zero {m : ℕ} (hm : m < 2) : (m : ℝ) * ((m : ℝ) - 1) = 0 := by
  interval_cases m <;> norm_num

/-- `|X^{m-2}G| ≤ X^m` where `0 ≤ G ≤ X²`, for `m ≥ 2`. -/
theorem tcw_abs_XG_le {X G : ℝ} (hX : 0 ≤ X) (hG0 : 0 ≤ G) (hG1 : G ≤ X ^ 2) {m : ℕ}
    (hm : 2 ≤ m) : |X ^ (m - 2) * G| ≤ X ^ m := by
  rw [abs_of_nonneg (mul_nonneg (pow_nonneg hX _) hG0)]
  calc X ^ (m - 2) * G ≤ X ^ (m - 2) * X ^ 2 := mul_le_mul_of_nonneg_left hG1 (pow_nonneg hX _)
    _ = X ^ m := by rw [← pow_add]; congr 1; omega

/-- A.s. `|H_l| ≤ (D₀/2)|m(m-1)| F_l`. -/
theorem tcw_abs_H_le (hCount : ConditionalBlockGUECount) {b e : ℝ} (hb : 0 < b)
    (hb1 : b < 1 / 2) (he1 : -2 < e) (he2 : e < 2) {W : ℕ} (hW : 0 < W) (l k m : ℕ)
    {c : ℝ} (hc : ∀ ω, Integrable (fun h => lmf_tagResponseClock b e W l k (ω, h) ^ m)
      (circularVectorLaw (Fin 2 × Fin W)) ∧ 0 ≤ tcw_F b e W l k m ω ∧
      tcw_F b e W l k m ω ≤ c * (tco_tagQ b e W l k ω).trace.re ^ m) :
    ∀ᵐ ω ∂growthPathLaw W b, |tcw_H b e W l k m ω| ≤
      transportD0 b e / 2 * |(m : ℝ) * ((m : ℝ) - 1)| * tcw_F b e W l k m ω := by
  have hD : 0 ≤ transportD0 b e / 2 := by have := transportD0_pos hb he1 he2; positivity
  filter_upwards [tcw_ae_drift_path hCount hb1 he1 he2 hW l k] with ω hω
  rcases lt_or_ge m 2 with hm | hm
  · have : tcw_H b e W l k m ω = 0 := by
      unfold tcw_H; simp [tcw_coef_eq_zero hm]
    rw [this, abs_zero]
    exact mul_nonneg (mul_nonneg hD (abs_nonneg _)) (hc ω).2.1
  · unfold tcw_H tcw_F
    rw [← integral_const_mul, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le ((hc ω).1.const_mul _) (Eventually.of_forall fun h => ?_)
    obtain ⟨hG0, hG1⟩ := hω h
    have hX := tcw_X_nonneg b e W l k (ω, h)
    have := tcw_abs_XG_le hX hG0 hG1 hm
    rw [tcw_X_eq] at this
    rw [Real.norm_eq_abs, mul_assoc, abs_mul, abs_mul, abs_of_nonneg hD, tcw_X_eq]
    exact mul_le_mul_of_nonneg_left this (mul_nonneg hD (abs_nonneg _))

theorem tcw_integrable_F {b e : ℝ} {W l k m : ℕ}
    (h : Integrable (fun x => lmf_tagResponseClock b e W l k x ^ m) (probedClockLaw W b)) :
    Integrable (tcw_F b e W l k m) (growthPathLaw W b) := by
  have := tco_isProbabilityMeasure_growthPathLaw W b
  have := tco_isProbabilityMeasure_circularVectorLaw (ι := Fin 2 × Fin W)
  rw [tcw_probedClockLaw_eq] at h
  exact h.integral_prod_left

/-- Integrability of the integrand of `H_l` on the probed path space. -/
theorem tcw_integrable_XG (hCount : ConditionalBlockGUECount) {b e : ℝ} (hb1 : b < 1 / 2)
    (he1 : -2 < e) (he2 : e < 2) {W : ℕ} (hW : 0 < W) (l k m : ℕ)
    (hmom : Integrable (fun x => lmf_tagResponseClock b e W l k x ^ (m - 2 + 2))
      (probedClockLaw W b)) :
    Integrable (fun x => transportD0 b e / 2 * ((m : ℝ) * ((m : ℝ) - 1)) *
      tcw_X b e W l k x ^ (m - 2) * tcw_G b e W l k x) (probedClockLaw W b) := by
  refine ((tcw_integrable_X_pow hmom).const_mul (|transportD0 b e / 2 *
    ((m : ℝ) * ((m : ℝ) - 1))|)).mono' ?_ ?_
  · exact ((measurable_const.mul ((tcw_measurable_X b e W l k).pow_const _)).mul
      (tcw_measurable_G b e W l k)).aestronglyMeasurable
  · filter_upwards [tcw_ae_drift hCount hb1 he1 he2 hW l k] with x hx
    obtain ⟨hX, hG0, hG1⟩ := hx
    have hX2 : 0 ≤ tcw_X b e W l k x ^ (m - 2) := pow_nonneg hX _
    rw [Real.norm_eq_abs, abs_mul _ (tcw_G b e W l k x), abs_mul _ (tcw_X b e W l k x ^ (m - 2)),
      abs_of_nonneg hX2, abs_of_nonneg hG0, pow_add, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hG1 hX2) (abs_nonneg _)

theorem tcw_integrable_H (hCount : ConditionalBlockGUECount) {b e : ℝ} (hb1 : b < 1 / 2)
    (he1 : -2 < e) (he2 : e < 2) {W : ℕ} (hW : 0 < W) (l k m : ℕ)
    (hmom : Integrable (fun x => lmf_tagResponseClock b e W l k x ^ (m - 2 + 2))
      (probedClockLaw W b)) :
    Integrable (tcw_H b e W l k m) (growthPathLaw W b) := by
  have := tco_isProbabilityMeasure_growthPathLaw W b
  have := tco_isProbabilityMeasure_circularVectorLaw (ι := Fin 2 × Fin W)
  have h := tcw_integrable_XG hCount hb1 he1 he2 hW l k m hmom
  rw [tcw_probedClockLaw_eq] at h
  exact h.integral_prod_left

theorem tcw_integral_law_pow {b e : ℝ} {W l k m : ℕ}
    (h : Integrable (fun x => lmf_tagResponseClock b e W l k x ^ m) (probedClockLaw W b)) :
    ∫ x, x ^ m ∂tcc_law b e W l k = ∫ ω, tcw_F b e W l k m ω ∂growthPathLaw W b := by
  have := tco_isProbabilityMeasure_growthPathLaw W b
  have := tco_isProbabilityMeasure_circularVectorLaw (ι := Fin 2 × Fin W)
  unfold tcc_law
  rw [integral_map (tco_measurable_tagClock b e W l k).aemeasurable
    (continuous_pow m).aestronglyMeasurable]
  rw [tcw_probedClockLaw_eq] at h ⊢
  exact integral_prod _ h

/-- **The remainder as a path expectation**: `ε_l(m) - d_l(m) = E[F_{l+1} - F_l - W⁻¹H_l]`
(`tcs_monoErr - tcw_deficit = E tcw_rem`), given the moments of `Z_{l;k}`, `Z_{l+1;k}`. -/
theorem tcw_remainder_eq (hCount : ConditionalBlockGUECount) {b e : ℝ} (hb1 : b < 1 / 2)
    (he1 : -2 < e) (he2 : e < 2) {W : ℕ} (hW : 0 < W) (l k m : ℕ)
    (h1 : Integrable (fun x => lmf_tagResponseClock b e W (l + 1) k x ^ m) (probedClockLaw W b))
    (h0 : Integrable (fun x => lmf_tagResponseClock b e W l k x ^ m) (probedClockLaw W b))
    (h2 : Integrable (fun x => lmf_tagResponseClock b e W l k x ^ (m - 2 + 2))
      (probedClockLaw W b)) :
    tcs_monoErr b e (transportD0 b e) W l k m - tcw_deficit b e W l k m =
      ∫ ω, tcw_rem b e W l k m ω ∂growthPathLaw W b := by
  set D0 := transportD0 b e
  set cm : ℝ := (m : ℝ) * ((m : ℝ) - 1)
  have := tco_isProbabilityMeasure_growthPathLaw W b
  have := tco_isProbabilityMeasure_circularVectorLaw (ι := Fin 2 × Fin W)
  have hXG : Integrable (fun x => D0 / 2 * cm * tcw_X b e W l k x ^ (m - 2) * tcw_G b e W l k x)
      (probedClockLaw W b) := tcw_integrable_XG hCount hb1 he1 he2 hW l k m h2
  have hdef : Integrable (fun x => cm * tcw_X b e W l k x ^ (m - 2) *
      (tcw_G b e W l k x - tcw_X b e W l k x ^ 2)) (probedClockLaw W b) :=
    tcw_integrable_deficit hCount hb1 he1 he2 hW l k m h2
  have hB : Integrable (fun x => cm * lmf_tagResponseClock b e W l k x ^ m)
      (probedClockLaw W b) := h0.const_mul _
  -- the deficit integrand splits as `m(m-1)X^{m-2}G - m(m-1)Z^m`
  have hpt : ∀ x, cm * tcw_X b e W l k x ^ (m - 2) *
      (tcw_G b e W l k x - tcw_X b e W l k x ^ 2) =
      cm * tcw_X b e W l k x ^ (m - 2) * tcw_G b e W l k x -
        cm * lmf_tagResponseClock b e W l k x ^ m := by
    intro x
    rcases lt_or_ge m 2 with hm | hm
    · simp [cm, tcw_coef_eq_zero hm]
    · rw [← tcw_X_eq, mul_sub, mul_assoc cm _ (tcw_X b e W l k x ^ 2), ← pow_add,
        show m - 2 + 2 = m by omega]
  have hA : Integrable (fun x => cm * tcw_X b e W l k x ^ (m - 2) * tcw_G b e W l k x)
      (probedClockLaw W b) := by
    refine (hdef.add hB).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    rw [hpt x]; ring
  have hdef_eq : tcw_deficit b e W l k m = D0 / (2 * W) *
      ((∫ x, cm * tcw_X b e W l k x ^ (m - 2) * tcw_G b e W l k x ∂probedClockLaw W b) -
        cm * ∫ ω, tcw_F b e W l k m ω ∂growthPathLaw W b) := by
    have hsplit : ∫ x, (m : ℝ) * ((m : ℝ) - 1) * tcw_X b e W l k x ^ (m - 2) *
        (tcw_G b e W l k x - tcw_X b e W l k x ^ 2) ∂probedClockLaw W b =
        ∫ x, (cm * tcw_X b e W l k x ^ (m - 2) * tcw_G b e W l k x -
          cm * lmf_tagResponseClock b e W l k x ^ m) ∂probedClockLaw W b :=
      integral_congr_ae (Eventually.of_forall hpt)
    unfold tcw_deficit
    rw [hsplit, integral_sub hA hB, integral_const_mul, ← tcw_integral_law_pow h0]
    unfold tcc_law
    rw [integral_map (tco_measurable_tagClock b e W l k).aemeasurable
      (continuous_pow m).aestronglyMeasurable]
  have hH : ∫ ω, tcw_H b e W l k m ω ∂growthPathLaw W b =
      D0 / 2 * ∫ x, cm * tcw_X b e W l k x ^ (m - 2) * tcw_G b e W l k x ∂probedClockLaw W b := by
    rw [← integral_const_mul]
    have e1 : ∫ x, D0 / 2 * (cm * tcw_X b e W l k x ^ (m - 2) * tcw_G b e W l k x)
        ∂probedClockLaw W b = ∫ x, D0 / 2 * cm * tcw_X b e W l k x ^ (m - 2) *
          tcw_G b e W l k x ∂probedClockLaw W b :=
      integral_congr_ae (Eventually.of_forall fun x => by ring)
    rw [e1]
    rw [tcw_probedClockLaw_eq] at hXG ⊢
    exact (integral_prod _ hXG).symm
  have hrem : ∫ ω, tcw_rem b e W l k m ω ∂growthPathLaw W b =
      ∫ ω, tcw_F b e W (l + 1) k m ω ∂growthPathLaw W b -
        ∫ ω, tcw_F b e W l k m ω ∂growthPathLaw W b -
        (W : ℝ)⁻¹ * ∫ ω, tcw_H b e W l k m ω ∂growthPathLaw W b := by
    unfold tcw_rem
    have i1 := tcw_integrable_F h1
    have i0 := tcw_integrable_F h0
    rw [integral_sub (f := fun ω => tcw_F b e W (l + 1) k m ω - tcw_F b e W l k m ω) (i1.sub i0)
      ((tcw_integrable_H hCount hb1 he1 he2 hW l k m h2).const_mul _),
      integral_sub i1 i0, integral_const_mul]
  rw [hrem, hH, hdef_eq]
  unfold tcs_monoErr
  rw [tcw_integral_law_pow h1, tcw_integral_law_pow h0]
  simp only [tcc_lam, cm]
  ring

end BlockBand.Endpoints
