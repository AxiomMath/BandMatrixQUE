module

public import BlockBand.Transmission.LawDuality.Interface
public import BlockBand.Transmission.DualBoundary.LawConv
public import BlockBand.Transmission.Dual.GDelStep

/-!
# The transmission law: one-time uniqueness of subsequential limits

Assuming the limit ratio martingale problem (`SubLimitRatioMP`) and the duality principle
(`RatioDualityPrinciple`), every subsequential limit satisfies the dual identity, and any two
subsequential limits have the same one-time laws.

* `dualLawValue_unique`: two values of `DualLawValue` agree once a realization exists.
* `subLimit_dualLawValue`: the two hypotheses give the dual identity at every subsequential limit.
* **`subLimit_map_eq`**: under the two hypotheses, any two subsequential limits have the same
  one-time
  laws `P(μ_t ∈ ·)` (Giry σ-algebra): the dual values agree (`dualBoundaryLaw_holds.exists_`),
  so `map_eq_of_sameRatioTransforms` applies. This is the one-time ("`k = 1`") content of
  `SubLimitFddUnique`, up to measurability of weakly continuous tests for the Giry σ-algebra.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Transmission.DualBoundary
open scoped NNReal ENNReal BoundedContinuousFunction

theorem dualLawValue_unique {E : ℝ} {κ : ℝ → ℝ} {t D0 : ℝ} {p : ℕ} {x y : Fin p → ℝ}
    {v v' : ℝ} (hex : HasDualDeletionProcess D0 x y) (h : DualLawValue E κ t D0 x y v)
    (h' : DualLawValue E κ t D0 x y v') : v = v' := by
  obtain ⟨Ω, m, 𝓖, P, N, X, Y, hD⟩ := hex
  rw [← h Ω m 𝓖 P N X Y hD, h' Ω m 𝓖 P N X Y hD]

theorem hasDualDeletionProcess_transport {b E : ℝ} (hb : 0 < b) (hE1 : -2 < E) (hE2 : E < 2)
    {p : ℕ} {x y : Fin p → ℝ} (hxy : IsRatioParameter x y) :
    HasDualDeletionProcess (transportD0 b E) x y :=
  Dual.G.dualBoundaryLaw_holds.exists_ _ (transportD0_pos hb hE1 hE2) p x y hxy

section

variable {b E : ℝ} {κ : ℝ → ℝ} (hb : 0 < b) (hb2 : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
  (hκ : IsAbsorptionProfile κ)
include hb hb2 hE1 hE2 hκ

/-- **The dual identity at every subsequential limit**, from `SubLimitRatioMP` and
`RatioDualityPrinciple`. -/
theorem subLimit_dualLawValue (hMP : SubLimitRatioMP) (hPr : RatioDualityPrinciple)
    {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {μ : ℝ → Ω → FiniteMeasure unitInterval} (h : IsTransmissionSubLimit b E κ φ P μ) :
    ∀ t : ℝ, 0 < t → ∀ (p : ℕ) (x y : Fin p → ℝ), IsRatioParameter x y →
      DualLawValue E κ t (transportD0 b E) x y (∫ ω, transmissionRatio x y (μ t ω) ∂P) := by
  obtain ⟨h1, h2, h3⟩ := hMP b hb hb2 E hE1 hE2 κ hκ φ hφ Ω inferInstance P μ h
  exact hPr _ (transportD0_pos hb hE1 hE2) E hE1 hE2 κ hκ Ω inferInstance P μ h.prob
    h.measurable h.continuous h1 h2 h3

/-- **One-time uniqueness of subsequential limits**. -/
theorem subLimit_map_eq (hMP : SubLimitRatioMP) (hPr : RatioDualityPrinciple)
    {φ φ' : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) (hφ' : Tendsto φ' atTop atTop)
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
    {μ : ℝ → Ω → FiniteMeasure unitInterval} {μ' : ℝ → Ω' → FiniteMeasure unitInterval}
    (h : IsTransmissionSubLimit b E κ φ P μ) (h' : IsTransmissionSubLimit b E κ φ' P' μ')
    {t : ℝ} (ht : 0 < t) : P.map (μ t) = P'.map (μ' t) := by
  have := h.prob
  have := h'.prob
  refine map_eq_of_sameRatioTransforms (h.measurable t ht) (h'.measurable t ht) ?_
  intro p x y hxy
  exact dualLawValue_unique (hasDualDeletionProcess_transport hb hE1 hE2 hxy)
    (subLimit_dualLawValue hb hb2 hE1 hE2 hκ hMP hPr hφ h t ht p x y hxy)
    (subLimit_dualLawValue hb hb2 hE1 hE2 hκ hMP hPr hφ' h' t ht p x y hxy)

end

/-- **The `law` field of `TransmissionLawContract`**, from `TransmissionSubLimitExists`,
`TransmissionTraceModulus`, `SubLimitRatioMP`, `RatioDualityPrinciple` and `SubLimitFddUnique`. -/
theorem law_of (hEx : TransmissionSubLimitExists) (hMod : TransmissionTraceModulus)
    (hMP : SubLimitRatioMP) (hPr : RatioDualityPrinciple) (hUniq : SubLimitFddUnique) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ κ : ℝ → ℝ, IsAbsorptionProfile κ →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
        (μ : ℝ → Ω → FiniteMeasure unitInterval),
        IsTransmissionLimit b E κ P μ ∧
        ∀ t : ℝ, 0 < t → ∀ (p : ℕ) (x y : Fin p → ℝ), IsRatioParameter x y →
          HasDualDeletionProcess (transportD0 b E) x y ∧
          DualLawValue E κ t (transportD0 b E) x y (∫ ω, transmissionRatio x y (μ t ω) ∂P) := by
  intro b hb hb2 E hE1 hE2 κ hκ
  obtain ⟨ms, hms, Ω, mΩ, P, μ, hsub⟩ := hEx b hb hb2 E hE1 hE2 κ hκ id tendsto_id
  have hφ : Tendsto (id ∘ ms) atTop atTop := hms.tendsto_atTop
  refine ⟨Ω, mΩ, P, μ, ⟨hsub.prob, hsub.measurable, hsub.continuous, ?_,
    hMod b hb hb2 E hE1 hE2 κ hκ⟩, fun t ht p x y hxy =>
      ⟨hasDualDeletionProcess_transport hb hE1 hE2 hxy,
        subLimit_dualLawValue hb hb2 hE1 hE2 hκ hMP hPr hφ hsub t ht p x y hxy⟩⟩
  intro k τ hτ Φ
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨ms', hms', Ω', mΩ', P', μ', hsub'⟩ := hEx b hb hb2 E hE1 hE2 κ hκ ns hns
  refine ⟨ms', ?_⟩
  rw [hUniq b hb hb2 E hE1 hE2 κ hκ _ _ hφ (hns.comp hms'.tendsto_atTop) Ω mΩ P μ Ω' mΩ' P' μ'
    hsub hsub' k τ hτ Φ]
  exact hsub'.fdd k τ hτ Φ

end BlockBand.Transmission.LawDuality
