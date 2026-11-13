module

public import BlockBand.Endpoints.Response.PassDerivativeLimitResponse
public import BlockBand.Endpoints.Response.PassDerivativeLimitSpectral
public import BlockBand.Endpoints.Response.PassDerivativeLimitBridge
public import BlockBand.Endpoints.Response.PassDerivativeLimitPass

/-!
# The near-port critical derivative along moving energies

The near-port ratio is a transform of the transmission matrix (`portRatio_eq_transmissionRatio`);
at fixed `κ > 0` it converges along a moving energy (`tendsto_portRatio`); the port-wise
difference quotients pass uniformly in `W` (`portPass_uniform`); and for one realization of the
boundary dual with positive profile the near-port critical derivative converges
(`nearPort_tendsto_pos`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
  BlockBand.Internal.Contracts.TransmissionUniform BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal Matrix.Norms.L2Operator

/-!
### The near-port ratio is the transmission transform
-/

theorem portRatio_eq_transmissionRatio {b E x y κ : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2)
    (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1) {W n : ℕ} {p : ℝ → ℝ} (hp0 : ∀ t, 0 ≤ p t)
    (hpos : ∀ i : Fin n, 0 < layerAbsorption W (fun t => κ * p t) n i) (hκ : 0 ≤ κ)
    {ω : GrowthPath W} (hH : ∀ k, (ω.1 k).IsHermitian) :
    portRatio b E x y W n p κ 0 ω =
      transmissionRatio ![x] ![y] (traceMeasure (pathTransmission b E (fun t => κ * p t) W n ω)) := by
  have hband : IsUnitBand (portDefect (absorbedScattering b E W n κ p ω) 0) := by
    rw [absorbedScattering_eq hp0, portDefect_eq]
    exact pencilPortDefect_band (R := sourceRoot W n p) (etaZ_nonneg hb.le hE1 hE2) hκ
      (fullPathMatrix_ward hH) (portInclusion_norm_le 0)
  rw [portRatio, ratioDet_eq_transmissionRatio hx hy0 hy1 hband,
    portDefect_absorbedScattering_zero hb hE1 hE2 hpos hH]

theorem transmissionProcess_natCast_div {b E : ℝ} {κ : ℝ → ℝ} {W : ℕ} (hW : 0 < W) (n : ℕ)
    (ω : GrowthPath W) :
    transmissionProcess b E κ W ((n : ℝ) / W) ω = traceMeasure (pathTransmission b E κ W n ω) := by
  have : (W : ℝ) * ((n : ℝ) / W) = n := by field_simp
  simp only [transmissionProcess, this, Nat.floor_natCast]

theorem isTransmissionLimit_of_along {b E : ℝ} {κ : ℝ → ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {μ : ℝ → Ω → FiniteMeasure unitInterval}
    (h : IsTransmissionLimitAlong b (fun _ => E) κ P μ) : IsTransmissionLimit b E κ P μ :=
  ⟨h.prob, h.measurable, h.continuous, h.fdd, h.modulus⟩

theorem isMovingEnergy_const (E : ℝ) : IsMovingEnergy E 0 (fun _ => E) :=
  fun W _ => by simp [IsNearEnergy]

/-!
### Convergence of the near-port ratio at fixed `κ > 0`
-/

theorem tendsto_portRatio {b E x y κ τ Ce : ℝ} (hb : b < 1) (hE1 : -2 < E)
    (hE2 : E < 2) (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1) (hτ : 0 < τ) {j : ℕ → ℕ}
    (hj : Tendsto (fun W : ℕ => (j W : ℝ) / W) atTop (𝓝 τ)) {p : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hpc : ∀ t, c ≤ p t) (hκ : 0 < κ) {e : ℕ → ℝ} (he : IsMovingEnergy E Ce e)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {μ : ℝ → Ω → FiniteMeasure unitInterval}
    (hA : IsTransmissionLimitAlong b e (fun t => κ * p t) P μ) :
    Tendsto (fun W : ℕ => ∫ ω, portRatio b (e W) x y W (j W) p κ 0 ω ∂growthPathLaw W b) atTop
      (𝓝 (∫ ω, transmissionRatio ![x] ![y] (μ τ ω) ∂P)) := by
  have hp0 : ∀ t, 0 ≤ p t := fun t => hc.le.trans (hpc t)
  set Φ := ratioPhi hx hy0 hy1
  set L := ∫ ω, transmissionRatio ![x] ![y] (μ τ ω) ∂P
  have hfdd := hA.fdd 1 (fun _ => τ) (fun _ => hτ) Φ
  simp only [Φ, ratioPhi_apply] at hfdd
  set f : C(unitInterval, ℝ) := (ratioBCF hx hy0 hy1).toContinuousMap
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, W₀, hW₀⟩ := hA.modulus (τ / 2) (2 * τ) (by linarith) f (ε / 4) (ε / 4)
    (by linarith) (by linarith)
  obtain ⟨W₁, hW₁⟩ := Metric.tendsto_atTop.1 hfdd (ε / 4) (by linarith)
  have hev1 : ∀ᶠ W : ℕ in atTop, |(j W : ℝ) / W - τ| ≤ min δ (τ / 2) := by
    have := Metric.tendsto_nhds.1 hj (min δ (τ / 2)) (lt_min hδ (by linarith))
    filter_upwards [this] with W hW
    exact (le_of_lt hW)
  obtain ⟨W₂, hW₂⟩ := eventually_atTop.1 ((hev1.and (IsMovingEnergy.eventually_bulk he hE1 hE2)).and
    (eventually_gt_atTop 0))
  refine ⟨max W₀ (max W₁ W₂), fun W hW => ?_⟩
  have hW0' : W₀ ≤ W := le_trans (le_max_left _ _) hW
  have hW1' : W₁ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hW
  have hW2' : W₂ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hW
  obtain ⟨⟨htW, hbulk⟩, hWpos⟩ := hW₂ W hW2'
  have : IsProbabilityMeasure (growthPathLaw W b) :=
    passDeriv_isProbabilityMeasure_growthPathLaw W b
  set μW := growthPathLaw W b
  set tW := (j W : ℝ) / W
  have hWr : (0 : ℝ) < W := by exact_mod_cast hWpos
  have htW1 : |tW - τ| ≤ δ := htW.trans (min_le_left _ _)
  have htW2 : |tW - τ| ≤ τ / 2 := htW.trans (min_le_right _ _)
  rw [abs_le] at htW2
  have hpos : ∀ (m : ℕ) (i : Fin m), 0 < layerAbsorption W (fun t => κ * p t) m i := by
    intro m i
    simp only [layerAbsorption]
    exact div_pos (mul_pos hκ (hc.trans_le (hpc _))) (by positivity)
  set G₁ : GrowthPath W → ℝ := fun ω =>
    transmissionRatio ![x] ![y] (transmissionProcess b (e W) (fun t => κ * p t) W tW ω)
  set G₂ : GrowthPath W → ℝ := fun ω =>
    transmissionRatio ![x] ![y] (transmissionProcess b (e W) (fun t => κ * p t) W τ ω)
  have hHae := ae_growthPath_isHermitian W b
  have h1 : ∀ᵐ ω ∂μW, portRatio b (e W) x y W (j W) p κ 0 ω = G₁ ω := by
    filter_upwards [hHae] with ω hω
    simp only [G₁, tW]
    rw [transmissionProcess_natCast_div hWpos]
    exact portRatio_eq_transmissionRatio hb hbulk.1 hbulk.2 hx hy0 hy1 hp0 (hpos _) hκ.le hω
  have h2 : ∀ᵐ ω ∂μW, portRatio b (e W) x y W ⌊(W : ℝ) * τ⌋₊ p κ 0 ω = G₂ ω := by
    filter_upwards [hHae] with ω hω
    exact portRatio_eq_transmissionRatio hb hbulk.1 hbulk.2 hx hy0 hy1 hp0 (hpos _) hκ.le hω
  have hm1 : AEStronglyMeasurable G₁ μW :=
    ((measurable_portRatio hp0 κ 0).aestronglyMeasurable).congr h1
  have hm2 : AEStronglyMeasurable G₂ μW :=
    ((measurable_portRatio hp0 κ 0).aestronglyMeasurable).congr h2
  have hb1 : ∀ ω, |G₁ ω| ≤ 1 := fun ω => by
    rw [abs_le]; constructor <;>
      linarith [transmissionRatio_pos x y (transmissionProcess b (e W) (fun t => κ * p t) W tW ω),
        transmissionRatio_le_one hx hy0 hy1
          (transmissionProcess b (e W) (fun t => κ * p t) W tW ω)]
  have hb2 : ∀ ω, |G₂ ω| ≤ 1 := fun ω => by
    rw [abs_le]; constructor <;>
      linarith [transmissionRatio_pos x y (transmissionProcess b (e W) (fun t => κ * p t) W τ ω),
        transmissionRatio_le_one hx hy0 hy1
          (transmissionProcess b (e W) (fun t => κ * p t) W τ ω)]
  have hi1 : Integrable G₁ μW := Integrable.mono' (integrable_const 1) hm1
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hb1 ω)
  have hi2 : Integrable G₂ μW := Integrable.mono' (integrable_const 1) hm2
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hb2 ω)
  -- the bad set of the modulus
  set S := {ω : GrowthPath W | ∃ t ∈ Icc (τ / 2) (2 * τ), ∃ t' ∈ Icc (τ / 2) (2 * τ),
    |t - t'| ≤ δ ∧ ε / 4 < |∫ x, f x ∂(transmissionProcess b (e W) (fun t => κ * p t) W t ω :
      Measure unitInterval) - ∫ x, f x ∂(transmissionProcess b (e W) (fun t => κ * p t) W t' ω :
      Measure unitInterval)|}
  have hS : μW S ≤ ENNReal.ofReal (ε / 4) := hW₀ W hW0'
  set T := toMeasurable μW S
  have hT : μW T ≤ ENNReal.ofReal (ε / 4) := by rw [measure_toMeasurable]; exact hS
  have hTm : MeasurableSet T := measurableSet_toMeasurable _ _
  have hpt : ∀ ω, |G₁ ω - G₂ ω| ≤ ε / 4 + T.indicator 1 ω := by
    intro ω
    by_cases hω : ω ∈ T
    · rw [Set.indicator_of_mem hω, Pi.one_apply]
      have := hb1 ω; have := hb2 ω
      have : |G₁ ω - G₂ ω| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [abs_le.1 (hb1 ω), abs_le.1 (hb2 ω),
          transmissionRatio_pos x y (transmissionProcess b (e W) (fun t => κ * p t) W tW ω),
          transmissionRatio_pos x y (transmissionProcess b (e W) (fun t => κ * p t) W τ ω)]
      linarith
    · rw [Set.indicator_of_notMem hω, add_zero]
      have hnS : ω ∉ S := fun h => hω (subset_toMeasurable _ _ h)
      have hle : |∫ x, f x ∂(transmissionProcess b (e W) (fun t => κ * p t) W tW ω :
          Measure unitInterval) - ∫ x, f x ∂(transmissionProcess b (e W) (fun t => κ * p t) W τ ω :
          Measure unitInterval)| ≤ ε / 4 := by
        by_contra hc'
        exact hnS ⟨tW, ⟨by linarith, by linarith⟩, τ, ⟨by linarith, by linarith⟩, htW1,
          lt_of_not_ge hc'⟩
      exact (abs_transmissionRatio_sub_le hx hy0 hy1 _ _).trans hle
  have hind : Integrable (T.indicator (1 : GrowthPath W → ℝ)) μW :=
    (integrable_const (1 : ℝ)).indicator hTm
  have hdiff : |∫ ω, G₁ ω ∂μW - ∫ ω, G₂ ω ∂μW| ≤ ε / 4 + ε / 4 := by
    rw [← integral_sub hi1 hi2]
    calc |∫ ω, (G₁ ω - G₂ ω) ∂μW| ≤ ∫ ω, |G₁ ω - G₂ ω| ∂μW := abs_integral_le_integral_abs
      _ ≤ ∫ ω, (ε / 4 + T.indicator 1 ω) ∂μW :=
          integral_mono (hi1.sub hi2).abs ((integrable_const _).add hind) hpt
      _ = ε / 4 + μW.real T := by
          rw [integral_add (integrable_const _) hind, integral_const, probReal_univ, smul_eq_mul,
            one_mul, integral_indicator_one hTm]
      _ ≤ ε / 4 + ε / 4 := by
          have : μW.real T ≤ ε / 4 := by
            rw [Measure.real]
            exact ENNReal.toReal_le_of_le_ofReal (by linarith) hT
          linarith
  have hfd := hW₁ W hW1'
  rw [Real.dist_eq] at hfd ⊢
  rw [integral_congr_ae h1]
  have : |∫ ω, G₂ ω ∂μW - L| < ε / 4 := hfd
  calc |∫ ω, G₁ ω ∂μW - L| ≤ |∫ ω, G₁ ω ∂μW - ∫ ω, G₂ ω ∂μW| + |∫ ω, G₂ ω ∂μW - L| :=
        abs_sub_le _ _ _
    _ < ε := by linarith

/-!
### Uniform passage constants along a moving energy
-/

/-- `ν ↦ ∫ f dν` is measurable for the Giry structure, for bounded continuous `f`. -/
theorem measurable_integral_bcf (f : BoundedContinuousFunction unitInterval ℝ) :
    Measurable (fun ν : FiniteMeasure unitInterval => ∫ t, f t ∂(ν : Measure unitInterval)) := by
  set K := ‖f‖
  have hg0 : ∀ t, 0 ≤ f t + K := fun t => by
    have := f.norm_coe_le_norm t
    rw [Real.norm_eq_abs] at this
    linarith [neg_abs_le (f t)]
  have e : ∀ ν : FiniteMeasure unitInterval, ∫ t, f t ∂(ν : Measure unitInterval) =
      (∫⁻ t, ENNReal.ofReal (f t + K) ∂(ν : Measure unitInterval)).toReal -
        K * ((ν : Measure unitInterval) Set.univ).toReal := by
    intro ν
    have hi : Integrable (fun t => f t) (ν : Measure unitInterval) := f.integrable _
    rw [← integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hg0)
      (hi.add (integrable_const K)).aestronglyMeasurable, integral_add hi (integrable_const K),
      integral_const, smul_eq_mul, Measure.real]
    ring
  simp_rw [e]
  have hm : Measurable (fun ν : FiniteMeasure unitInterval => (ν : Measure unitInterval)) :=
    measurable_subtype_coe
  refine ((Measure.measurable_lintegral ?_).comp hm).ennreal_toReal.sub
    (measurable_const.mul ((Measure.measurable_coe MeasurableSet.univ).comp hm).ennreal_toReal)
  exact ENNReal.measurable_ofReal.comp (f.continuous.measurable.add_const K)

theorem bulk_margin {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) :
    0 < min (E + 2) (2 - E) ∧ E ∈ bulkInterval (min (E + 2) (2 - E)) := by
  refine ⟨lt_min (by linarith) (by linarith), ?_, ?_⟩
  · have := min_le_left (E + 2) (2 - E); linarith
  · have := min_le_right (E + 2) (2 - E); linarith

/-- Uniform port-wise passage along a moving energy. There are `C, W₀` with, for `W ≥ W₀`:
`|E D_i(p)| ≤ C`, the a.s. invertibility at `E_W`, integrability of `D_i`, and
`|E[(F_i(κ) - F_i(0))/κ] - E D_i| ≤ C(κ^{1/4} + κ)` for every `κ > 0`. -/
theorem portPass_uniform (hUnifMom : FullSourceMomentsEnergyUniformContract)
    (hInvU : PathFractionalInverseEnergyUniform) {b E x y τ Ce : ℝ} (hb0 : 0 < b)
    (hb1 : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1)
    (hτ : 0 < τ) {j : ℕ → ℕ} (hj : Tendsto (fun W : ℕ => (j W : ℝ) / W) atTop (𝓝 τ))
    {p : ℝ → ℝ} (hp0 : ∀ t, 0 ≤ p t) {Q : ℝ} (hpQ : ∀ t, p t ≤ Q) {e : ℕ → ℝ}
    (he : IsMovingEnergy E Ce e) (i : Fin 2) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W →
      (-2 < e W ∧ e W < 2) ∧
      (∀ᵐ ω ∂growthPathLaw W b, IsUnit (fullPathMatrix b (e W) W (j W) ω).det) ∧
      Integrable (fun ω => portDeriv b (e W) x y W (j W) p i ω) (growthPathLaw W b) ∧
      |∫ ω, portDeriv b (e W) x y W (j W) p i ω ∂growthPathLaw W b| ≤ C ∧
      ∀ κ : ℝ, 0 < κ →
        |(∫ ω, (portRatio b (e W) x y W (j W) p κ i ω - portRatio b (e W) x y W (j W) p 0 i ω) /
            κ ∂growthPathLaw W b) -
          ∫ ω, portDeriv b (e W) x y W (j W) p i ω ∂growthPathLaw W b| ≤
          C * (κ ^ ((1 / 2 : ℝ) / 2) + κ) := by
  have hQ0 : 0 ≤ Q := (hp0 0).trans (hpQ 0)
  have hb1' : b ≤ 1 := by linarith
  obtain ⟨hκI, hEI⟩ := bulk_margin hE1 hE2
  obtain ⟨C₁, W₁, hC₁⟩ := hUnifMom.clock b hb0 hb1 _ Ce (τ + 1) 2 hκI one_le_two
  obtain ⟨C₂, W₂, hC₂⟩ := hInvU b hb0 hb1 E hE1 hE2 τ hτ j hj (1 / 2) (by norm_num) (by norm_num) Ce
  have hev : ∀ᶠ W : ℕ in atTop, (j W : ℝ) / W < τ + 1 :=
    hj.eventually (gt_mem_nhds (by linarith))
  obtain ⟨W₃, hW₃⟩ := eventually_atTop.1 ((hev.and (IsMovingEnergy.eventually_bulk he hE1 hE2)).and
    (eventually_ge_atTop 1))
  set C₁' := max C₁ 0
  set C₂' := max C₂ 0
  set K₁ := Q ^ 2 * (C₁' * (τ + 2)) ^ 2
  set c₁ := ratioC1 x y
  set c₂ := ratioC2 x y
  have hc₁ : 0 ≤ c₁ := ratioC1_nonneg hx hy0 hy1
  have hc₂ : 0 ≤ c₂ := ratioC2_nonneg x y
  have hK₁ : 0 ≤ K₁ := by positivity
  have hC₂' : 0 ≤ C₂' := le_max_right _ _
  set s : ℝ := 1 / 2
  have hQs : 0 ≤ Q ^ s := Real.rpow_nonneg hQ0 s
  set C := 4 * c₁ * (1 + K₁) + (2 * c₁ * K₁ + 8 * c₁ * Q ^ s * C₂' + (36 * c₁ + 576 * c₂) * K₁)
  refine ⟨C, max (max W₁ W₂) W₃, by positivity, fun W hW => ?_⟩
  have hW1 : W₁ ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hW2 : W₂ ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hW3 : W₃ ≤ W := le_trans (le_max_right _ _) hW
  obtain ⟨⟨hjW, hbulk⟩, hWge⟩ := hW₃ W hW3
  have hWpos : 0 < W := by omega
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hWge
  have hW0 : (0 : ℝ) < W := by linarith
  have hnear : IsNearEnergy Ce W E (e W) := he W hWpos
  have hn : (j W : ℝ) ≤ (τ + 1) * W := by
    rw [div_lt_iff₀ hW0] at hjW; linarith
  have hclock := hC₁ W hW1 E hEI (e W) hnear (j W) hn
  have hclock' : eLpNorm (fun ω => (W : ℂ)⁻¹ *
      ((boundaryToInterior b (e W) W (j W) ω)ᴴ * boundaryToInterior b (e W) W (j W) ω).trace)
      (ENNReal.ofReal 2) (growthPathLaw W b) ≤ ENNReal.ofReal (C₁' * ((j W : ℝ) + 1)) :=
    hclock.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
  have hnW : ((j W : ℝ) + 1) / W ≤ τ + 2 := by
    rw [div_le_iff₀ hW0]; nlinarith
  have hF2 := trB_sq_moment hWr hp0 hpQ (le_max_right C₁ 0) hnW hclock'
  obtain ⟨hinv, hF3⟩ := hC₂ W hW2 (e W) hnear
  have hF3' : ∫⁻ ω, ENNReal.ofReal ((‖fullInverse b (e W) W (j W) ω‖ / (W : ℝ) ^ 2) ^ s)
      ∂growthPathLaw W b ≤ ENNReal.ofReal C₂' :=
    hF3.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  obtain ⟨hint, hD, hpass⟩ := portPass_bound hb1' hbulk.1 hbulk.2 hx hy0 hy1 hp0 hpQ
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) hK₁ hC₂' hF2 hF3' hinv i
  have hη0 : 0 ≤ etaZ b (e W) := etaZ_nonneg hb1' hbulk.1 hbulk.2
  have hη1 : etaZ b (e W) ≤ 1 := etaZ_le_one hb0.le hbulk.1 hbulk.2
  refine ⟨hbulk, hinv, hint, ?_, fun κ hκ => ?_⟩
  · refine hD.trans ?_
    have : 4 * c₁ * etaZ b (e W) * (1 + K₁) ≤ 4 * c₁ * (1 + K₁) := by
      have h0 : 0 ≤ 4 * c₁ * (1 + K₁) := by positivity
      calc 4 * c₁ * etaZ b (e W) * (1 + K₁) = (4 * c₁ * (1 + K₁)) * etaZ b (e W) := by ring
        _ ≤ (4 * c₁ * (1 + K₁)) * 1 := mul_le_mul_of_nonneg_left hη1 h0
        _ = _ := by ring
    have : 0 ≤ 2 * c₁ * K₁ + 8 * c₁ * Q ^ s * C₂' + (36 * c₁ + 576 * c₂) * K₁ := by positivity
    linarith
  · refine (hpass κ hκ).trans ?_
    have hl : 0 ≤ κ ^ (s / 2) + κ := by have := Real.rpow_nonneg hκ.le (s / 2); linarith
    refine mul_le_mul_of_nonneg_right ?_ hl
    have hη2 : etaZ b (e W) ^ 2 ≤ 1 := pow_le_one₀ hη0 hη1
    have a1 : 2 * c₁ * etaZ b (e W) * K₁ ≤ 2 * c₁ * K₁ := by
      have h0 : 0 ≤ 2 * c₁ * K₁ := by positivity
      calc 2 * c₁ * etaZ b (e W) * K₁ = (2 * c₁ * K₁) * etaZ b (e W) := by ring
        _ ≤ (2 * c₁ * K₁) * 1 := mul_le_mul_of_nonneg_left hη1 h0
        _ = _ := by ring
    have a2 : 8 * c₁ * etaZ b (e W) * Q ^ s * C₂' ≤ 8 * c₁ * Q ^ s * C₂' := by
      have h0 : 0 ≤ 8 * c₁ * Q ^ s * C₂' := by positivity
      calc 8 * c₁ * etaZ b (e W) * Q ^ s * C₂' = (8 * c₁ * Q ^ s * C₂') * etaZ b (e W) := by ring
        _ ≤ (8 * c₁ * Q ^ s * C₂') * 1 := mul_le_mul_of_nonneg_left hη1 h0
        _ = _ := by ring
    have a3 : (36 * c₁ + 576 * c₂) * etaZ b (e W) ^ 2 * K₁ ≤ (36 * c₁ + 576 * c₂) * K₁ := by
      have h0 : 0 ≤ (36 * c₁ + 576 * c₂) * K₁ := by positivity
      calc (36 * c₁ + 576 * c₂) * etaZ b (e W) ^ 2 * K₁ =
            ((36 * c₁ + 576 * c₂) * K₁) * etaZ b (e W) ^ 2 := by ring
        _ ≤ ((36 * c₁ + 576 * c₂) * K₁) * 1 := mul_le_mul_of_nonneg_left hη2 h0
        _ = _ := by ring
    have : 0 ≤ 4 * c₁ * (1 + K₁) := by positivity
    simp only [C]
    linarith

/-!
### The near-port limit for one realization of the boundary dual
-/

theorem integrable_portRatio {b E x y κ : ℝ} (hb : b ≤ 1) (hE1 : -2 < E) (hE2 : E < 2)
    (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1) {W n : ℕ} {p : ℝ → ℝ} (hp0 : ∀ t, 0 ≤ p t)
    (hκ : 0 ≤ κ) (i : Fin 2) :
    Integrable (fun ω => portRatio b E x y W n p κ i ω) (growthPathLaw W b) := by
  have : IsProbabilityMeasure (growthPathLaw W b) :=
    passDeriv_isProbabilityMeasure_growthPathLaw W b
  refine Integrable.mono' (integrable_const 1) (measurable_portRatio hp0 κ i).aestronglyMeasurable
    ((ae_growthPath_isHermitian W b).mono fun ω hω => ?_)
  rw [Real.norm_eq_abs]
  exact (portRatio_bounds hb hE1 hE2 hx hy0 hy1 hp0 i hω).1 κ hκ

theorem tendsto_rpow_quarter_add :
    Tendsto (fun κ : ℝ => κ ^ ((1 / 2 : ℝ) / 2) + κ) (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun κ : ℝ => κ ^ ((1 / 2 : ℝ) / 2)) (𝓝 0) (𝓝 ((0 : ℝ) ^ ((1 / 2 : ℝ) / 2))) :=
    (Real.continuous_rpow_const (by norm_num)).tendsto 0
  rw [Real.zero_rpow (by norm_num)] at h1
  have := (h1.add tendsto_id).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  simpa using this

/-- Near-port critical derivative, one realization, positive profile. -/
theorem nearPort_tendsto_pos (hUnifLaw : TransmissionLawEnergyUniformContract)
    (hUnifMom : FullSourceMomentsEnergyUniformContract) (hBdry : DualBoundaryStartContract)
    (hInvU : PathFractionalInverseEnergyUniform) {b E x y τ Ce : ℝ} (hb0 : 0 < b)
    (hb1 : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y < 1)
    (hxy : ¬(x = 0 ∧ y = 0)) (hτ : 0 < τ) {j : ℕ → ℕ}
    (hj : Tendsto (fun W : ℕ => (j W : ℝ) / W) atTop (𝓝 τ)) {p : ℝ → ℝ} (hpc : Continuous p)
    {c : ℝ} (hc : 0 < c) (hpc' : ∀ t, c ≤ p t) {Q : ℝ} (hpQ : ∀ t, p t ≤ Q) {e : ℕ → ℝ}
    (he : IsMovingEnergy E Ce e) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {N : ℝ≥0 → Ω → ℕ}
    {X Y : ℝ≥0 → Ω → ℕ → ℝ} (hR : IsBoundaryDualProcess P 𝓖 (transportD0 b E) ![x] ![y] N X Y) :
    Integrable (responseIntegrand τ (fun s => p (τ - s)) N X Y) P ∧
    Tendsto (fun W : ℕ => ∫ ω, portDeriv b (e W) x y W (j W) p 0 ω ∂growthPathLaw W b) atTop
      (𝓝 (-(4 * Real.pi * Parameters.semicircleDensity E) *
        ∫ ω, responseIntegrand τ (fun s => p (τ - s)) N X Y ω ∂P)) := by
  have hp0 : ∀ t, 0 ≤ p t := fun t => hc.le.trans (hpc' t)
  have hQ0 : 0 ≤ Q := (hp0 0).trans (hpQ 0)
  have hb' : b < 1 := by linarith
  have hD0 : 0 < transportD0 b E := by
    unfold transportD0
    have : 0 < 4 - E ^ 2 := by nlinarith
    positivity
  have hstart := isDualStart_one hx hy0 hy1.le hxy
  have hfirst := hBdry.firstMoment _ hD0 x y hstart Ω _ 𝓖 P N X Y hR
  have hprof : ∀ κ : ℝ, 0 < κ → IsAbsorptionProfile (fun t => κ * p t) := fun κ hκ =>
    ⟨continuous_const.mul hpc, fun t => mul_nonneg hκ.le (hp0 t),
      ⟨κ * Q, fun t => mul_le_mul_of_nonneg_left (hpQ t) hκ.le⟩⟩
  set DT : ℝ → ℝ := fun κ => dualTransform E (fun t => κ * p t) τ P N X Y
  -- convergence of the near-port ratio at each fixed `κ > 0`, and positivity at `κ = 1`
  have hconv : ∀ κ : ℝ, 0 < κ →
      Tendsto (fun W : ℕ => ∫ ω, portRatio b (e W) x y W (j W) p κ 0 ω ∂growthPathLaw W b) atTop
        (𝓝 (DT κ)) ∧ 0 < DT κ := by
    intro κ hκ
    obtain ⟨Ωκ, mκ, Pκ, μκ, hAlong, -⟩ := hUnifLaw.law b hb0 hb1 E hE1 hE2 _ (hprof κ hκ)
    have hLim := isTransmissionLimit_of_along (hAlong 0 _ (isMovingEnergy_const E))
    have hval := (hBdry.law b hb0 hb1 E hE1 hE2 _ (hprof κ hκ) Ωκ mκ Pκ μκ hLim τ hτ x y hstart
      hy1).2 Ω _ 𝓖 P N X Y hR
    refine ⟨?_, ?_⟩
    · rw [show DT κ = _ from hval]
      exact tendsto_portRatio hb' hE1 hE2 hx hy0 hy1 hτ hj hc hpc' hκ he (hAlong Ce e he)
    · rw [show DT κ = _ from hval]
      have : IsProbabilityMeasure Pκ := hLim.prob
      have hm : Measurable (fun ω => transmissionRatio ![x] ![y] (μκ τ ω)) :=
        Real.measurable_exp.comp ((measurable_integral_bcf (ratioBCF hx hy0 hy1)).comp
          (hLim.measurable τ hτ))
      have hi : Integrable (fun ω => transmissionRatio ![x] ![y] (μκ τ ω)) Pκ :=
        Integrable.mono' (integrable_const 1) hm.aestronglyMeasurable
          (Eventually.of_forall fun ω => by
            rw [Real.norm_eq_abs, abs_of_pos (transmissionRatio_pos _ _ _)]
            exact transmissionRatio_le_one hx hy0 hy1 _)
      rw [integral_pos_iff_support_of_nonneg (fun ω => (transmissionRatio_pos _ _ _).le) hi]
      have : Function.support (fun ω => transmissionRatio ![x] ![y] (μκ τ ω)) = Set.univ :=
        Set.eq_univ_of_forall fun ω => (transmissionRatio_pos _ _ _).ne'
      rw [this, measure_univ]
      exact one_pos
  have hne : dualTransform E p τ P N X Y ≠ 0 := by
    have := (hconv 1 one_pos).2
    simp only [DT, one_mul] at this
    exact this.ne'
  obtain ⟨hJint, hDT⟩ := dualTransform_rightDeriv hR hx hy0 hfirst hE1 hE2 hτ hp0 hpQ hne
  refine ⟨hJint, ?_⟩
  set lam := -(4 * Real.pi * Parameters.semicircleDensity E) *
    ∫ ω, responseIntegrand τ (fun s => p (τ - s)) N X Y ω ∂P
  obtain ⟨Cp, W₀, hCp0, hCp⟩ := portPass_uniform hUnifMom hInvU hb0 hb1 hE1 hE2 hx hy0 hy1 hτ hj
    hp0 hpQ he 0
  set a : ℕ → ℝ → ℝ := fun W κ => ∫ ω, portRatio b (e W) x y W (j W) p κ 0 ω ∂growthPathLaw W b
  set d : ℕ → ℝ := fun W => ∫ ω, portDeriv b (e W) x y W (j W) p 0 ω ∂growthPathLaw W b
  -- the difference quotient of the expectations
  have hquot : ∀ W, W₀ ≤ W → ∀ κ : ℝ, 0 < κ →
      |(a W κ - a W 0) / κ - d W| ≤ Cp * (κ ^ ((1 / 2 : ℝ) / 2) + κ) := by
    intro W hW κ hκ
    obtain ⟨hbulk, -, -, -, hpass⟩ := hCp W hW
    have h := hpass κ hκ
    have hi : ∀ κ' : ℝ, 0 ≤ κ' → Integrable (fun ω => portRatio b (e W) x y W (j W) p κ' 0 ω)
        (growthPathLaw W b) := fun κ' hκ' =>
      integrable_portRatio (by linarith) hbulk.1 hbulk.2 hx hy0 hy1 hp0 hκ' 0
    rwa [integral_div, integral_sub (hi κ hκ.le) (hi 0 le_rfl)] at h
  have hdb : ∀ W, W₀ ≤ W → |d W| ≤ Cp := fun W hW => (hCp W hW).2.2.2.1
  -- `DT κ - DT 0 → 0`
  have hDT0 : Tendsto (fun κ => DT κ - DT 0) (𝓝[>] 0) (𝓝 0) := by
    have h := (tendsto_nhdsWithin_of_tendsto_nhds (tendsto_id (x := 𝓝 (0 : ℝ)))).mul hDT
    rw [zero_mul] at h
    refine h.congr' (eventually_nhdsWithin_of_forall fun κ (hκ : 0 < κ) => ?_)
    simp only [id, DT]
    field_simp
  -- `a W 0 → DT 0`
  have ha0 : Tendsto (fun W => a W 0) atTop (𝓝 (DT 0)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hev : ∀ᶠ κ in 𝓝[>] (0 : ℝ), 0 < κ ∧ κ ≤ 1 ∧ 3 * Cp * κ < ε / 3 ∧
        |DT κ - DT 0| < ε / 3 := by
      refine eventually_mem_nhdsWithin.and ((Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (show ∀ᶠ κ in 𝓝 (0 : ℝ), κ ∈ Iic 1 from Iic_mem_nhds one_pos)).and
        (((tendsto_nhdsWithin_of_tendsto_nhds (tendsto_id (x := 𝓝 (0 : ℝ)))).const_mul
          (3 * Cp)).eventually (gt_mem_nhds (by rw [mul_zero]; linarith)) |>.and ?_))
      have := hDT0.eventually (Metric.ball_mem_nhds 0 (by linarith : 0 < ε / 3))
      filter_upwards [this] with κ hκ
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hκ
    obtain ⟨κ, hκ0, hκ1, hκ2, hκ3⟩ := hev.exists
    obtain ⟨W₁, hW₁⟩ := Metric.tendsto_atTop.1 (hconv κ hκ0).1 (ε / 3) (by linarith)
    refine ⟨max W₀ W₁, fun W hW => ?_⟩
    have hW0 : W₀ ≤ W := le_trans (le_max_left _ _) hW
    have hW1 : W₁ ≤ W := le_trans (le_max_right _ _) hW
    have h1 := hW₁ W hW1
    rw [Real.dist_eq] at h1 ⊢
    have hq := hquot W hW0 κ hκ0
    have hd := hdb W hW0
    have hr : κ ^ ((1 / 2 : ℝ) / 2) ≤ 1 := Real.rpow_le_one hκ0.le hκ1 (by norm_num)
    have hdiff : |a W κ - a W 0| ≤ 3 * Cp * κ := by
      have e1 : a W κ - a W 0 = κ * ((a W κ - a W 0) / κ) := by field_simp
      rw [e1, abs_mul, abs_of_pos hκ0]
      have : |(a W κ - a W 0) / κ| ≤ Cp + Cp * (κ ^ ((1 / 2 : ℝ) / 2) + κ) := by
        have := abs_sub_abs_le_abs_sub ((a W κ - a W 0) / κ) (d W)
        linarith
      have h2 : Cp + Cp * (κ ^ ((1 / 2 : ℝ) / 2) + κ) ≤ 3 * Cp := by nlinarith
      nlinarith
    calc |a W 0 - DT 0| ≤ |a W κ - a W 0| + |a W κ - DT κ| + |DT κ - DT 0| := by
          have := abs_sub_le (a W 0) (a W κ) (DT 0)
          have := abs_sub_le (a W κ) (DT κ) (DT 0)
          rw [abs_sub_comm (a W 0) (a W κ)] at *
          linarith
      _ < ε := by linarith
  -- `d W → λ`
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hev : ∀ᶠ κ in 𝓝[>] (0 : ℝ), 0 < κ ∧ Cp * (κ ^ ((1 / 2 : ℝ) / 2) + κ) < ε / 3 ∧
      |(DT κ - DT 0) / κ - lam| < ε / 3 := by
    refine eventually_mem_nhdsWithin.and ((tendsto_rpow_quarter_add.const_mul Cp).eventually
      (gt_mem_nhds (by rw [mul_zero]; linarith)) |>.and ?_)
    have := hDT.eventually (Metric.ball_mem_nhds lam (by linarith : 0 < ε / 3))
    filter_upwards [this] with κ hκ
    simpa only [Metric.mem_ball, Real.dist_eq] using hκ
  obtain ⟨κ, hκ0, hκ1, hκ2⟩ := hev.exists
  have hlimq : Tendsto (fun W => (a W κ - a W 0) / κ) atTop (𝓝 ((DT κ - DT 0) / κ)) :=
    ((hconv κ hκ0).1.sub ha0).div_const κ
  obtain ⟨W₁, hW₁⟩ := Metric.tendsto_atTop.1 hlimq (ε / 3) (by linarith)
  refine ⟨max W₀ W₁, fun W hW => ?_⟩
  have hW0 : W₀ ≤ W := le_trans (le_max_left _ _) hW
  have hW1 : W₁ ≤ W := le_trans (le_max_right _ _) hW
  have h1 := hW₁ W hW1
  rw [Real.dist_eq] at h1 ⊢
  have hq := hquot W hW0 κ hκ0
  calc |d W - lam| ≤ |(a W κ - a W 0) / κ - d W| + |(a W κ - a W 0) / κ - (DT κ - DT 0) / κ| +
        |(DT κ - DT 0) / κ - lam| := by
        have := abs_sub_le (d W) ((a W κ - a W 0) / κ) lam
        have := abs_sub_le ((a W κ - a W 0) / κ) ((DT κ - DT 0) / κ) lam
        rw [abs_sub_comm (d W) ((a W κ - a W 0) / κ)] at *
        linarith
    _ < ε := by linarith

end BlockBand.Endpoints
