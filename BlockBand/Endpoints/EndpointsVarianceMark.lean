module

public import BlockBand.Endpoints.EndpointsVarianceBasic
public import BlockBand.Endpoints.Response.EdgeClockMoments

/-!
# `EpMarkStatisticLimit` from `PhysicalLeadProfileContract`

We prove `epMarkStatisticLimit_of_lead`: `PhysicalLeadProfileContract` implies
`EpMarkStatisticLimit`. The proof is a Fatou sandwich, with no count moments and no uniform
integrability. Fix a critical family,
`τ`, a spectral weight `w`, a bounded continuous `Φ ≥ 0`, a critical sequence and realizations
`R j`. Write `G_Ψ(ξ) = ∫ w(u)Ψ(ν) dξ` (continuous in the vague topology), `P_j` the
`markedLaw` of `R j` and `P = family τ`. Then `physicalOneMark (R j) E w Ψ = E_{P_j} G_Ψ`.
1. *Fatou under weak convergence* (`epv_eventually_lt_lintegral`): truncate `G` at `n`;
   `min(G, n)` is bounded continuous, so the convergence in law (clause 3 of
   `IsCriticalFamily`) and monotone convergence give: every `y < E_P G` is eventually
   `< E_{P_j} G`.
2. *Physical intensity*: `PhysicalLeadProfileContract` at `Φ ≡ 1`; the lead side is exactly
   `∫ w = 1` (probability path/port priors, `n⁻¹ Σ_{J<n} 1 = 1`), so `E_{P_j} G_1 → 1`.
3. *Limit intensity*: `HasUnitSpectralIntensity` gives `E_P G_1 = 1`.
4. *Sandwich*: `G_Φ + G_{‖Φ‖-Φ} = ‖Φ‖ G_1`; Fatou for both terms and convergence of the sum force
   `E_{P_j} G_Φ → E_P G_Φ ≤ ‖Φ‖ < ∞`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.Clocks (physicalOneMark leadOneMark PhysicalLeadProfileContract)
open scoped ENNReal BoundedContinuousFunction

attribute [local instance] BlockBand.Model.Construction.massProfile_borelSpace

/-!
## 1. The weighted mark statistic `G_Ψ`
-/

/-- `G_Ψ(ξ) = ∫ w(u)Ψ(ν) dξ`. -/
def epv_G (w : SpectralWeight) (Ψ : MassProfile →ᵇ ℝ) (ξ : MarkedPointMeasure) : ℝ :=
  epv_markedIntegral (fun x => w x.1 * Ψ x.2) ξ

theorem epv_continuous_G (w : SpectralWeight) (Ψ : MassProfile →ᵇ ℝ) : Continuous (epv_G w Ψ) :=
  epv_continuous_markedIntegral (epv_weight_product_props w Ψ).1 (epv_weight_product_props w Ψ).2

theorem epv_G_nonneg (w : SpectralWeight) {Ψ : MassProfile →ᵇ ℝ} (hΨ : ∀ ν, 0 ≤ Ψ ν)
    (ξ : MarkedPointMeasure) : 0 ≤ epv_G w Ψ ξ :=
  epv_markedIntegral_nonneg (fun x => mul_nonneg (w.nonnegative x.1) (hΨ x.2)) ξ

theorem epv_limitOneMark_eq (P : ProbabilityMeasure MarkedPointMeasure) (w : SpectralWeight)
    {Ψ : MassProfile →ᵇ ℝ} (hΨ : ∀ ν, 0 ≤ Ψ ν) :
    ep_limitOneMark P w Ψ = ∫⁻ ξ, ENNReal.ofReal (epv_G w Ψ ξ) ∂(P : Measure MarkedPointMeasure) :=
  lintegral_congr fun ξ => epv_lintegral_marked_eq (epv_weight_product_props w Ψ).1 (epv_weight_product_props w Ψ).2
    (fun x => mul_nonneg (w.nonnegative x.1) (hΨ x.2)) ξ

/-- The physical one-mark statistic is the expectation of `G_Ψ` under `markedLaw`. -/
theorem epv_physicalOneMark_eq {p : Parameters} (R : FiniteRealization p) (E : ℝ)
    (w : SpectralWeight) {Ψ : MassProfile →ᵇ ℝ} (hΨ : ∀ ν, 0 ≤ Ψ ν) :
    physicalOneMark R E w Ψ =
      (∫⁻ ξ, ENNReal.ofReal (epv_G w Ψ ξ) ∂(R.markedLaw E : Measure MarkedPointMeasure)).toReal := by
  have hG := epv_continuous_G w Ψ
  rw [← integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (epv_G_nonneg w hΨ))
    hG.aestronglyMeasurable]
  unfold physicalOneMark FiniteRealization.markedLaw
  rw [ProbabilityMeasure.toMeasure_map, integral_map
    (R.spectral.measurable_markedConfig E).aemeasurable hG.aestronglyMeasurable]
  rfl

/-- `G_Φ + G_{c-Φ} = c G_1`. -/
theorem epv_G_add (w : SpectralWeight) (Ψ : MassProfile →ᵇ ℝ) (c : ℝ) (ξ : MarkedPointMeasure) :
    epv_G w Ψ ξ + epv_G w (BoundedContinuousFunction.const _ c - Ψ) ξ = c * epv_G w 1 ξ := by
  unfold epv_G epv_markedIntegral
  rw [← integral_add (epv_integrable_marked (epv_weight_product_props w Ψ).1 (epv_weight_product_props w Ψ).2 ξ)
    (epv_integrable_marked (epv_weight_product_props w _).1 (epv_weight_product_props w _).2 ξ), ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [BoundedContinuousFunction.coe_sub, BoundedContinuousFunction.const_apply,
    Pi.sub_apply, BoundedContinuousFunction.coe_one, Pi.one_apply]
  ring

/-!
## 2. Fatou under weak convergence
-/

/-- **Fatou under convergence in law** for a continuous nonnegative (possibly unbounded) `F`: every
`y < E_P F` is eventually `< E_{P_j} F`. -/
theorem epv_eventually_lt_lintegral {Ps : ℕ → ProbabilityMeasure MarkedPointMeasure}
    {P : ProbabilityMeasure MarkedPointMeasure} (hconv : Tendsto Ps atTop (𝓝 P))
    {F : MarkedPointMeasure → ℝ} (hF : Continuous F) (hF0 : ∀ ξ, 0 ≤ F ξ) {y : ℝ≥0∞}
    (hy : y < ∫⁻ ξ, ENNReal.ofReal (F ξ) ∂(P : Measure MarkedPointMeasure)) :
    ∀ᶠ j in atTop, y < ∫⁻ ξ, ENNReal.ofReal (F ξ) ∂(Ps j : Measure MarkedPointMeasure) := by
  set T : ℕ → MarkedPointMeasure → ℝ := fun n ξ => min (F ξ) n with hT
  have hTc : ∀ n, Continuous (T n) := fun n => hF.min continuous_const
  have hT0 : ∀ n ξ, 0 ≤ T n ξ := fun n ξ => le_min (hF0 ξ) (Nat.cast_nonneg n)
  have hsup : ∀ ξ, ⨆ n : ℕ, ENNReal.ofReal (T n ξ) = ENNReal.ofReal (F ξ) := by
    intro ξ
    refine le_antisymm (iSup_le fun n => ENNReal.ofReal_le_ofReal (min_le_left _ _)) ?_
    obtain ⟨n, hn⟩ := exists_nat_ge (F ξ)
    exact le_iSup_of_le n (le_of_eq (by simp [hT, min_eq_left hn]))
  have hmono : Monotone fun n ξ => ENNReal.ofReal (T n ξ) := by
    intro n m hnm ξ
    exact ENNReal.ofReal_le_ofReal (min_le_min le_rfl (Nat.cast_le.2 hnm))
  have hlim : ∫⁻ ξ, ENNReal.ofReal (F ξ) ∂(P : Measure MarkedPointMeasure) =
      ⨆ n : ℕ, ∫⁻ ξ, ENNReal.ofReal (T n ξ) ∂(P : Measure MarkedPointMeasure) := by
    rw [← lintegral_iSup (f := fun n ξ => ENNReal.ofReal (T n ξ))
      (fun n => ENNReal.measurable_ofReal.comp (hTc n).measurable) hmono]
    exact lintegral_congr fun ξ => (hsup ξ).symm
  rw [hlim] at hy
  obtain ⟨n, hn⟩ := lt_iSup_iff.1 hy
  let B : MarkedPointMeasure →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨T n, hTc n⟩ n
    fun ξ ζ => by
      have h1 := hT0 n ξ; have h2 := hT0 n ζ
      have h3 : T n ξ ≤ n := min_le_right _ _
      have h4 : T n ζ ≤ n := min_le_right _ _
      simp only [ContinuousMap.coe_mk, Real.dist_eq, abs_le]
      constructor <;> linarith
  have hB : ∀ Q : ProbabilityMeasure MarkedPointMeasure,
      ∫⁻ ξ, ENNReal.ofReal (T n ξ) ∂(Q : Measure MarkedPointMeasure) =
        ENNReal.ofReal (∫ ξ, B ξ ∂(Q : Measure MarkedPointMeasure)) := fun Q =>
    (ofReal_integral_eq_lintegral_ofReal (B.integrable _)
      (Eventually.of_forall (hT0 n))).symm
  have hw := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hconv) B
  have hw' := (ENNReal.continuous_ofReal.tendsto _).comp hw
  rw [hB P] at hn
  filter_upwards [hw'.eventually_const_lt hn] with j hj
  refine lt_of_lt_of_le hj ?_
  rw [Function.comp_apply, ← hB (Ps j)]
  exact lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal (min_le_left _ _)

/-!
## 3. The real sandwich
-/

theorem epv_real_sandwich {a b : ℕ → ℝ} {A B c : ℝ}
    (hA : ∀ y < A, ∀ᶠ j in atTop, y < a j) (hB : ∀ y < B, ∀ᶠ j in atTop, y < b j)
    (hsum : Tendsto (fun j => a j + b j) atTop (𝓝 c)) (hc : A + B = c) :
    Tendsto a atTop (𝓝 A) := by
  refine tendsto_order.2 ⟨hA, fun y hy => ?_⟩
  have hδ : 0 < y - A := by linarith
  filter_upwards [hB (B - (y - A) / 2) (by linarith),
    hsum.eventually_lt_const (show c < c + (y - A) / 2 by linarith)] with j h1 h2
  linarith

/-!
## 4. The intensities
-/

/-- `leadOneMark` at `Φ ≡ 1` is `∫ w = 1`. -/
theorem epv_leadOneMark_one (p : Parameters) (E : ℝ) (w : SpectralWeight) :
    leadOneMark p E w 1 = 1 := by
  have := BlockBand.Endpoints.isProbabilityMeasure_growthPathLaw p.W p.b
  have : IsProbabilityMeasure
      (BlockBand.Internal.Contracts.CoareaPalm.circularVectorLaw (Fin 2 × Fin p.W)) := by
    unfold BlockBand.Internal.Contracts.CoareaPalm.circularVectorLaw
    exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).2 inferInstance
  have hn : (p.n : ℝ) ≠ 0 := by have := p.n_ge_four; positivity
  unfold leadOneMark
  simp only [BoundedContinuousFunction.coe_one, Pi.one_apply, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one, inv_mul_cancel₀ hn, integral_const, probReal_univ,
    one_smul]
  exact w.integral_eq_one

theorem epv_tendsto_physical_one (hLead : PhysicalLeadProfileContract) {b : ℝ} (hb : 0 < b)
    (hb' : b < 1 / 2) {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) (w : SpectralWeight) {τ : ℝ}
    (hτ : 0 < τ) (s : CriticalSequence τ) (R : ∀ j, FiniteRealization (s.parameters b hb hb' j)) :
    Tendsto (fun j => physicalOneMark (R j) E w 1) atTop (𝓝 1) := by
  have h := hLead b hb hb' E hE1 hE2 w w.smooth w.compactSupport 1 τ hτ s R
  simp_rw [epv_leadOneMark_one] at h
  simpa using h.add_const 1

theorem epv_unit_intensity {P : ProbabilityMeasure MarkedPointMeasure}
    (hP : HasUnitSpectralIntensity P) (w : SpectralWeight) :
    ∫⁻ ξ, ENNReal.ofReal (epv_G w 1 ξ) ∂(P : Measure MarkedPointMeasure) = 1 := by
  let f : CompactlySupportedContinuousMap ℝ ℝ := ⟨w.toContinuousMap, w.compactSupport⟩
  have h := hP f
  have hint : ∀ ξ : MarkedPointMeasure, ∫ x, f x ∂ξ.spectral.measure = epv_G w 1 ξ := by
    intro ξ
    rw [ξ.spectral_eq, integral_map measurable_fst.aemeasurable (f := fun x : ℝ => f x)
      f.continuous.aestronglyMeasurable]
    unfold epv_G epv_markedIntegral
    simp only [BoundedContinuousFunction.coe_one, Pi.one_apply, mul_one]
    rfl
  simp_rw [hint] at h
  have h1 : ∫ x, f x = 1 := w.integral_eq_one
  rw [h1] at h
  rw [← ofReal_integral_eq_lintegral_ofReal (Integrable.of_integral_ne_zero (by rw [h]; norm_num))
    (Eventually.of_forall (epv_G_nonneg w fun _ => zero_le_one)), h, ENNReal.ofReal_one]

/-!
## 5. The mark-statistic limit
-/

/-- **`EpMarkStatisticLimit`**, from `PhysicalLeadProfileContract` alone.
-/
theorem epMarkStatisticLimit_of_lead (hLead : PhysicalLeadProfileContract) :
    EpMarkStatisticLimit := by
  intro b hb hb' E hE1 hE2 family hfam τ w Φ hΦ
  set c : ℝ := ‖Φ‖ with hc
  have hc0 : 0 ≤ c := norm_nonneg _
  set Φ' : MassProfile →ᵇ ℝ := BoundedContinuousFunction.const _ c - Φ with hΦ'
  have hΦ'0 : ∀ ν, 0 ≤ Φ' ν := fun ν => by
    have : Φ ν ≤ c := (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using Φ.norm_coe_le_norm ν)
    simp only [hΦ', BoundedContinuousFunction.coe_sub, BoundedContinuousFunction.const_apply,
      Pi.sub_apply]
    linarith
  have h10 : ∀ ν, 0 ≤ (1 : MassProfile →ᵇ ℝ) ν := fun _ => zero_le_one
  -- expectations under a law
  let L : (MassProfile →ᵇ ℝ) → ProbabilityMeasure MarkedPointMeasure → ℝ≥0∞ := fun Ψ Q =>
    ∫⁻ ξ, ENNReal.ofReal (epv_G w Ψ ξ) ∂(Q : Measure MarkedPointMeasure)
  have hsplit : ∀ Q : ProbabilityMeasure MarkedPointMeasure,
      L Φ Q + L Φ' Q = ENNReal.ofReal c * L 1 Q := by
    intro Q
    simp only [L]
    rw [← lintegral_add_left (f := fun ξ => ENNReal.ofReal (epv_G w Φ ξ))
        (ENNReal.measurable_ofReal.comp (epv_continuous_G w Φ).measurable),
      ← lintegral_const_mul (f := fun ξ => ENNReal.ofReal (epv_G w 1 ξ)) _
        (ENNReal.measurable_ofReal.comp (epv_continuous_G w 1).measurable)]
    refine lintegral_congr fun ξ => ?_
    rw [← ENNReal.ofReal_add (epv_G_nonneg w hΦ ξ) (epv_G_nonneg w hΦ'0 ξ),
      ← ENNReal.ofReal_mul hc0, epv_G_add]
  have hunit : L 1 (family τ) = 1 := epv_unit_intensity (hfam.2.2.2.2.1 τ) w
  have hlimsum : L Φ (family τ) + L Φ' (family τ) = ENNReal.ofReal c := by
    rw [hsplit, hunit, mul_one]
  have hAfin : L Φ (family τ) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hlimsum ▸ le_self_add)
  have hBfin : L Φ' (family τ) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hlimsum ▸ le_add_self)
  refine ⟨by rw [epv_limitOneMark_eq _ w hΦ]; exact hAfin, fun s R => ?_⟩
  rw [epv_limitOneMark_eq _ w hΦ]
  have hconv := hfam.2.2.1 τ s R
  set Ps : ℕ → ProbabilityMeasure MarkedPointMeasure := fun j => (R j).markedLaw E
  -- physical intensity
  have hone : Tendsto (fun j => (L 1 (Ps j)).toReal) atTop (𝓝 1) := by
    refine (epv_tendsto_physical_one hLead hb hb' hE1 hE2 w τ.2 s R).congr fun j => ?_
    exact epv_physicalOneMark_eq (R j) E w h10
  have hCfin : ∀ᶠ j in atTop, L 1 (Ps j) ≠ ∞ := by
    filter_upwards [hone.eventually_const_lt (show (0 : ℝ) < 1 by norm_num)] with j hj h
    rw [h, ENNReal.toReal_top] at hj
    exact lt_irrefl _ hj
  have hfinA : ∀ᶠ j in atTop, L Φ (Ps j) ≠ ∞ := by
    filter_upwards [hCfin] with j hj
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hj)
      ((hsplit (Ps j)) ▸ le_self_add)
  have hfinB : ∀ᶠ j in atTop, L Φ' (Ps j) ≠ ∞ := by
    filter_upwards [hCfin] with j hj
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hj)
      ((hsplit (Ps j)) ▸ le_add_self)
  -- lower bounds from Fatou
  have hlow : ∀ Ψ : MassProfile →ᵇ ℝ, (∀ ν, 0 ≤ Ψ ν) → L Ψ (family τ) ≠ ∞ →
      (∀ᶠ j in atTop, L Ψ (Ps j) ≠ ∞) →
      ∀ y < (L Ψ (family τ)).toReal, ∀ᶠ j in atTop, y < (L Ψ (Ps j)).toReal := by
    intro Ψ hΨ hfin hfinj y hy
    rcases lt_or_ge y 0 with hy0 | hy0
    · exact Eventually.of_forall fun j => hy0.trans_le ENNReal.toReal_nonneg
    · have hy' : ENNReal.ofReal y < L Ψ (family τ) :=
        (ENNReal.ofReal_lt_iff_lt_toReal hy0 hfin).2 hy
      filter_upwards [epv_eventually_lt_lintegral hconv (epv_continuous_G w Ψ)
        (epv_G_nonneg w hΨ) hy', hfinj] with j hj hjf
      exact (ENNReal.ofReal_lt_iff_lt_toReal hy0 hjf).1 hj
  -- the sum converges to `c`
  have hsum : Tendsto (fun j => (L Φ (Ps j)).toReal + (L Φ' (Ps j)).toReal) atTop (𝓝 c) := by
    have h := hone.const_mul c
    rw [mul_one] at h
    refine h.congr' ?_
    filter_upwards [hfinA, hfinB] with j hA hB
    rw [← ENNReal.toReal_add hA hB, hsplit, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0]
  have hcsum : (L Φ (family τ)).toReal + (L Φ' (family τ)).toReal = c := by
    rw [← ENNReal.toReal_add hAfin hBfin, hlimsum, ENNReal.toReal_ofReal hc0]
  refine (epv_real_sandwich (hlow Φ hΦ hAfin hfinA) (hlow Φ' hΦ'0 hBfin hfinB) hsum
    hcsum).congr fun j => ?_
  exact (epv_physicalOneMark_eq (R j) E w hΦ).symm

end BlockBand.Endpoints
