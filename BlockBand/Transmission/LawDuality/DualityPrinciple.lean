module

public import BlockBand.Transmission.LawDuality.DualityEntrance

/-!
# The duality principle

Proof of `RatioDualityPrinciple`: replace the process by a version with every path continuous on
`(0, ∞)` (`exists_continuous_version`), check that the ratio martingale problem, the entrance, the
mass bound and the dual transform pass to the version, and apply the unstopped backward identity.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Dual
open scoped NNReal ENNReal

section Congr

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **A version of `μ` with every path continuous on `(0, ∞)`.** -/
theorem exists_continuous_version {μ : ℝ → Ω → FiniteMeasure unitInterval}
    (hmeas : ∀ t, 0 < t → Measurable (μ t))
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun t => μ t ω) (Ioi 0)) :
    ∃ μ' : ℝ → Ω → FiniteMeasure unitInterval, (∀ t, 0 < t → Measurable (μ' t)) ∧
      (∀ ω, ContinuousOn (fun t => μ' t ω) (Ioi 0)) ∧ ∀ᵐ ω ∂P, ∀ t, μ' t ω = μ t ω := by
  classical
  set B := toMeasurable P {ω | ¬ ContinuousOn (fun t => μ t ω) (Ioi 0)}
  have hB : MeasurableSet B := measurableSet_toMeasurable _ _
  have hB0 : P B = 0 := by rw [measure_toMeasurable]; exact ae_iff.1 hcont
  refine ⟨fun t => B.piecewise (fun _ => 0) (μ t), fun t ht =>
    Measurable.piecewise hB measurable_const (hmeas t ht), fun ω => ?_, ?_⟩
  · by_cases hω : ω ∈ B
    · simp only [piecewise_eq_of_mem _ _ _ hω]; exact continuousOn_const
    · simp only [piecewise_eq_of_notMem _ _ _ hω]
      by_contra hc; exact hω (subset_toMeasurable _ _ hc)
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hB0] with ω hω t
    exact piecewise_eq_of_notMem _ _ _ hω

variable {μ μ' : ℝ → Ω → FiniteMeasure unitInterval} (hae : ∀ᵐ ω ∂P, ∀ t, μ' t ω = μ t ω)
include hae

theorem isRatioMartingale_congr {D0 E : ℝ} {κ : ℝ → ℝ} (hM : IsRatioMartingale D0 E κ P μ) :
    IsRatioMartingale D0 E κ P μ' := by
  intro p z hz s t hs ht hst
  obtain ⟨hI, horth⟩ := hM p z hz s t hs ht hst
  have he : ∀ᵐ ω ∂P, (transmissionRatio z.1 z.2 (μ' t ω) - transmissionRatio z.1 z.2 (μ' s ω) -
      ∫ u in s..t, ratioDrift D0 E κ u z (μ' u ω)) = (transmissionRatio z.1 z.2 (μ t ω) -
        transmissionRatio z.1 z.2 (μ s ω) - ∫ u in s..t, ratioDrift D0 E κ u z (μ u ω)) := by
    filter_upwards [hae] with ω hω; simp only [hω]
  refine ⟨hI.congr (he.mono fun ω h => h.symm), fun m i u hu φ => ?_⟩
  rw [← horth m i u hu φ]
  refine integral_congr_ae ?_
  filter_upwards [hae, he] with ω hω h2
  simp only [hω] at h2 ⊢

theorem hasRatioEntrance_congr (h : HasRatioEntrance P μ) : HasRatioEntrance P μ' := by
  intro p hp z hz
  refine (h p hp z hz).congr fun s => integral_congr_ae ?_
  filter_upwards [hae] with ω hω; rw [hω]

theorem hasLocalMassBound_congr (h : HasLocalMassBound P μ) : HasLocalMassBound P μ' := by
  intro ε T hε
  obtain ⟨C, hC⟩ := h ε T hε
  refine ⟨C, fun t ht => le_of_eq_of_le (lintegral_congr_ae ?_) (hC t ht)⟩
  filter_upwards [hae] with ω hω; rw [hω]

omit hae in
theorem dualTransform_congr {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {N N' : ℝ≥0 → Ω' → ℕ} {X Y X' Y' : ℝ≥0 → Ω' → ℕ → ℝ}
    (h : ∀ᵐ ω ∂P', ∀ t, N' t ω = N t ω ∧ X' t ω = X t ω ∧ Y' t ω = Y t ω) (E : ℝ)
    (κ : ℝ → ℝ) (t : ℝ) : dualTransform E κ t P' N' X' Y' = dualTransform E κ t P' N X Y := by
  unfold dualTransform
  refine integral_congr_ae ?_
  filter_upwards [h] with ω hω
  have e1 : ∀ s, N' s ω = N s ω := fun s => (hω s).1
  have e2 : ∀ s, X' s ω = X s ω := fun s => (hω s).2.1
  have e3 : ∀ s, Y' s ω = Y s ω := fun s => (hω s).2.2
  simp only [dualExtinction, e1, e2, e3]
  rfl

omit hae in
theorem killFac_top_eq {Ω' : Type*} (k : ℝ → ℝ) (N : ℝ≥0 → Ω' → ℕ) (X Y : ℝ≥0 → Ω' → ℕ → ℝ)
    (ω : Ω') {t : ℝ} (ht : 0 ≤ t) : killFac k N X Y (fun _ => ⊤) t ω =
      Real.exp (-∫ s in (0 : ℝ)..t, k s * dualTotal (N s.toNNReal ω) (X s.toNNReal ω)
        (Y s.toNNReal ω)) := by
  simp only [killFac, killExp, max_eq_left ht]
  congr 2
  refine intervalIntegral.integral_congr fun v _ => ?_
  have : killInd (⊤ : WithTop ℝ≥0) v = 1 :=
    ite_eq_left_iff.2 fun h' => absurd (WithTop.coe_lt_top _) h'
  simp only [this, mul_one, killRate]

end Congr

/-- **`RatioDualityPrinciple` holds.** -/
theorem ratioDualityPrinciple_holds : RatioDualityPrinciple := by
  intro D0 hD0 E _ _ κ hκ Ω _ P μ hP hmeas hcont hM hent hmass t ht p x y hxy
  obtain ⟨μ', hmeas', hcont', hae⟩ := exists_continuous_version hmeas hcont
  have hM' := isRatioMartingale_congr hae hM
  have hent' := hasRatioEntrance_congr hae hent
  have hmass' := hasLocalMassBound_congr hae hmass
  have hU : ∫ ω, transmissionRatio x y (μ t ω) ∂P = ∫ ω, transmissionRatio x y (μ' t ω) ∂P :=
    integral_congr_ae (by filter_upwards [hae] with ω hω; rw [hω])
  rw [hU]
  intro Ω' m' 𝓖 P' N X Y hD
  obtain ⟨N', X', Y', hD', hpath', hst', hae'⟩ := exists_normalized hxy hD
  have := hD'.prob
  rw [← dualTransform_congr hae' E κ t, dualTransform_eq_lt hD0 hxy hD' E κ ht]
  set k : ℝ → ℝ := fun v => absorptionRate E κ (t - v) with hkdef
  obtain ⟨Kκ, hKκ⟩ := hκ.2.2
  have hκc : Continuous κ := hκ.1
  have hhc := DualBoundary.continuous_absorptionRate hκc E
  have hk : Continuous k := hhc.comp (continuous_const.sub continuous_id)
  have hh0 : ∀ u, 0 ≤ absorptionRate E κ u := fun u => DualBoundary.absorptionRate_nonneg hκ E u
  have hhC : ∀ u, |absorptionRate E κ u| ≤ DualBoundary.rateBound E Kκ := fun u => by
    rw [abs_of_nonneg (hh0 u)]; exact DualBoundary.absorptionRate_le hKκ E u
  have hk0 : ∀ v, 0 ≤ k v := fun v => hh0 _
  have hkC : ∀ v, k v ≤ DualBoundary.rateBound E Kκ := fun v => (le_abs_self _).trans (hhC _)
  have key : ∀ a0, 0 < a0 → a0 < t → ∫ ω, transmissionRatio x y (μ' t ω) ∂P =
      stripV P μ' a0 t P' k N' X' Y' (fun _ => ⊤) a0 (t - a0) := fun a0 ha0 hat =>
    ratio_eq_stripV_top hD' hpath' hk hk0 hmeas' hcont' ha0 hkC hκc hhC (fun v => rfl) hM'
      hmass' hxy hst' hat
  have hlim := tendsto_stripV_top (P := P) hD' hpath' hk hk0 hmeas' hent' ht
    (ae_dualExtinction_ne hD0 hxy hD' ht)
  have hconst : Tendsto (fun a0 => stripV P μ' a0 t P' k N' X' Y' (fun _ => ⊤) a0 (t - a0))
      (𝓝[>] 0) (𝓝 (∫ ω, transmissionRatio x y (μ' t ω) ∂P)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT ht] with a0 ha0 using key a0 ha0.1 ha0.2
  rw [tendsto_nhds_unique hconst hlim]
  refine integral_congr_ae (ae_of_all _ fun ω' => ?_)
  by_cases hζ : dualExtinction N' ω' < ENNReal.ofReal t
  · simp only [hζ, ↓reduceIte]
    rw [killFac_top_eq k N' X' Y' ω' ht.le]
  · simp only [hζ, ↓reduceIte]

end BlockBand.Transmission.LawDuality
