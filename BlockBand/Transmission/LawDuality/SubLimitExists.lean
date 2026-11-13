module

public import BlockBand.Transmission.LawDuality.SubLimitFdd
public import BlockBand.Transmission.LawDuality.TightAbsorbed
public import BlockBand.Transmission.LawDuality.Refined

/-!
# `TransmissionSubLimitExists` from power-sum tightness

Tightness comes from the polynomial tests and the conductance moments.

* **`SubLimit.exists_subLimit`** (abstract, `W`-free): a sequence of a.e.-measurable random
  finite-measure processes on `[0,1]` with one-time mass tightness (`OneTimeTight`) and the
  moment modulus (`MomentModulus`) has a subsequence with an fdd limit `(P, μ)` on
  `Ω = ℕ → FM[0,1]`: measurable marginals, a.s. continuous paths on `(0,∞)`, convergence of
  `E Φ(μ_n(τ))` for every bounded continuous `Φ` and every finite family of positive times.
  (Prokhorov on the dense times, `SubLimitTight`; continuous version, `SubLimitPath`;
  general times, `SubLimitFdd`. No Kolmogorov extension or Arzelà–Ascoli is used.)
* `oneTimeTight_of`, `momentModulus_of`: both hypotheses for `μ_W = transmissionProcess b E κ W`
  along `ns → ∞`, from `PowerTightAt b E κ` (`TightAbsorbed`).
* **`transmissionSubLimitExists_of_tight`**: `hTG ∧ AbsorbedPowerTight → TransmissionSubLimitExists`.
* **`transmissionSubLimitExists_zero`**: the `κ ≡ 0` instance from `hTG` alone.
* `law_of_tight`: the `law` clause from `hTG`, `AbsorbedPowerTight` and the last five
  hypotheses of `law_of_refined` (its first two hypotheses are discharged).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.LawFinite
open scoped NNReal ENNReal

namespace SubLimit

/-- **Subsequential fdd limits exist** (abstract form). -/
theorem exists_subLimit {Ωs : ℕ → Type} [∀ n, MeasurableSpace (Ωs n)] {Ps : ∀ n, Measure (Ωs n)}
    [∀ n, IsProbabilityMeasure (Ps n)] {X : ∀ n, ℝ → Ωs n → St} (hX : AEMeas Ps X)
    (hT : OneTimeTight Ps X) (hM : MomentModulus Ps X) :
    ∃ ms : ℕ → ℕ, StrictMono ms ∧ ∃ (P : Measure (ℕ → St)) (μ : ℝ → (ℕ → St) → St),
      IsProbabilityMeasure P ∧ (∀ t, 0 < t → Measurable (μ t)) ∧
      (∀ᵐ ω ∂P, ContinuousOn (fun t => μ t ω) (Ioi 0)) ∧
      ∀ (k : ℕ) (τ : Fin k → ℝ), (∀ i, 0 < τ i) →
        ∀ Φ : BoundedContinuousFunction (Fin k → St) ℝ,
          Tendsto (fun n => ∫ ω, Φ (fun i => X (ms n) (τ i) ω) ∂Ps (ms n)) atTop
            (𝓝 (∫ ω, Φ (fun i => μ (τ i) ω) ∂P)) := by
  obtain ⟨Q, ms, hms, hQ⟩ := exists_tendsto_lawY hX hT
  have hG := ae_goodSet hX hM hms hQ
  refine ⟨ms, hms, Q, fun t ω => extPath ω t, inferInstance, fun t ht => measurable_extPath ht,
    (ae_mem_goodSet hG).mono fun ω hω => continuousOn_extPath hω,
    fun k τ hτ Φ => tendsto_fdd hX hM hms hQ hG τ hτ Φ⟩

end SubLimit

open SubLimit

variable {b E : ℝ} {κ : ℝ → ℝ}

theorem eventually_le_of_tendsto {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop) (W₀ : ℕ) :
    ∃ N : ℕ, ∀ n, N ≤ n → W₀ ≤ ns n :=
  eventually_atTop.1 (tendsto_atTop.1 hns W₀)

/-- One-time mass tightness of `μ_W` along `ns`, from `PowerTightAt` (`k = 1`). -/
theorem oneTimeTight_of (hκ : ∀ s, 0 ≤ κ s) (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2)
    (hPT : PowerTightAt b E κ) {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop) :
    OneTimeTight (fun n => growthPathLaw (ns n) b) (fun n => transmissionProcess b E κ (ns n)) := by
  intro t ht θ hθ
  obtain ⟨M, W₀, hM⟩ := (hPT 1 le_rfl t (t + 1) ht (by linarith)).1 θ hθ
  obtain ⟨N, hN⟩ := eventually_le_of_tendsto hns W₀
  refine ⟨M, N, fun n hn => ?_⟩
  have hnull := ae_iff.1 (ae_moment_eq_absorbedPowerTrace (W := ns n) hκ hb hE1 hE2)
  refine (measure_mono (t := {ω | M < |absorbedPowerTrace b E κ (ns n) 1 t ω|} ∪
    {ω | ¬ ∀ (j : ℕ) (t : ℝ), moment j (transmissionProcess b E κ (ns n) t ω) =
      absorbedPowerTrace b E κ (ns n) (j + 1) t ω}) fun ω hω => ?_).trans
    ((measure_union_le _ _).trans (by rw [hnull, add_zero]; exact hM _ (hN n hn)))
  by_cases hg : ∀ (j : ℕ) (t : ℝ), moment j (transmissionProcess b E κ (ns n) t ω) =
      absorbedPowerTrace b E κ (ns n) (j + 1) t ω
  · left
    have h : M < moment 0 (transmissionProcess b E κ (ns n) t ω) := hω
    rw [hg 0 t] at h
    exact lt_of_lt_of_le h (le_abs_self _)
  · exact Or.inr hg

/-- The moment modulus of `μ_W` along `ns`, from `PowerTightAt` (`f = s^j`). -/
theorem momentModulus_of (hκ : ∀ s, 0 ≤ κ s) (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2)
    (hPT : PowerTightAt b E κ) {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop) :
    MomentModulus (fun n => growthPathLaw (ns n) b) (fun n => transmissionProcess b E κ (ns n)) := by
  intro ε T hε j η θ hη hθ
  obtain ⟨δ, hδ, W₀, hW⟩ := traceModulus_of_powerTightAt hκ hb hE1 hE2 hPT (T := T) hε
    ⟨fun s : unitInterval => (s : ℝ) ^ j, continuous_subtype_val.pow j⟩ hη hθ
  obtain ⟨N, hN⟩ := eventually_le_of_tendsto hns W₀
  exact ⟨δ, hδ, N, fun n hn => hW (ns n) (hN n hn)⟩

/-- `TransmissionSubLimitExists` at one `(b, E, κ)`, from `PowerTightAt b E κ`. -/
theorem subLimitExists_of_powerTightAt (hκ : ∀ s, 0 ≤ κ s) (hb : b < 1) (hE1 : -2 < E)
    (hE2 : E < 2) (hPT : PowerTightAt b E κ) {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop) :
    ∃ ms : ℕ → ℕ, StrictMono ms ∧
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
        (μ : ℝ → Ω → FiniteMeasure unitInterval), IsTransmissionSubLimit b E κ (ns ∘ ms) P μ := by
  obtain ⟨ms, hms, P, μ, hP, hmeas, hcont, hfdd⟩ := exists_subLimit
    (Ps := fun n => growthPathLaw (ns n) b) (X := fun n => transmissionProcess b E κ (ns n))
    (fun n t _ => aemeasurable_transmissionProcess hκ hb hE1 hE2 t)
    (oneTimeTight_of hκ hb hE1 hE2 hPT hns) (momentModulus_of hκ hb hE1 hE2 hPT hns)
  exact ⟨ms, hms, ℕ → St, inferInstance, P, μ, ⟨hP, hmeas, hcont, hfdd⟩⟩

/-- **`TransmissionSubLimitExists` from `hTG` and the absorbed tightness.** -/
theorem transmissionSubLimitExists_of_tight (hTG : TransmissionGeneratorContract)
    (hAbs : AbsorbedPowerTight) : TransmissionSubLimitExists :=
  fun _ hb hb2 _ hE1 hE2 _ hκ _ hns => subLimitExists_of_powerTightAt hκ.2.1 (by linarith) hE1 hE2
    (powerTightAt_of hTG hAbs hb hb2 hE1 hE2 hκ) hns

/-- **The `κ ≡ 0` instance of `TransmissionSubLimitExists`, from `hTG` alone.** -/
theorem transmissionSubLimitExists_zero (hTG : TransmissionGeneratorContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop → ∃ ms : ℕ → ℕ, StrictMono ms ∧
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
        (μ : ℝ → Ω → FiniteMeasure unitInterval),
        IsTransmissionSubLimit b E (fun _ => 0) (ns ∘ ms) P μ :=
  fun _ hb hb2 _ hE1 hE2 _ hns => subLimitExists_of_powerTightAt (fun _ => le_rfl) (by linarith)
    hE1 hE2 (powerTightAt_zero hTG hb hb2 hE1 hE2) hns

/-- **The `law` clause with the first two hypotheses of `law_of_refined` discharged** (from
`hTG` and `AbsorbedPowerTight`); the other inputs are `SubLimitRatioMartingale`,
`SubLimitMassBound`, `TransmissionEntranceBulk`, `RatioDualityPrinciple` and `SubLimitFddUnique`. -/
theorem law_of_tight (hTG : TransmissionGeneratorContract) (hAbs : AbsorbedPowerTight)
    (hMart : SubLimitRatioMartingale) (hMass : SubLimitMassBound)
    (hEnt : TransmissionEntranceBulk) (hPr : RatioDualityPrinciple)
    (hUniq : SubLimitFddUnique) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ κ : ℝ → ℝ, IsAbsorptionProfile κ →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
        (μ : ℝ → Ω → FiniteMeasure unitInterval),
        IsTransmissionLimit b E κ P μ ∧
        ∀ t : ℝ, 0 < t → ∀ (p : ℕ) (x y : Fin p → ℝ), IsRatioParameter x y →
          HasDualDeletionProcess (transportD0 b E) x y ∧
          DualLawValue E κ t (transportD0 b E) x y (∫ ω, transmissionRatio x y (μ t ω) ∂P) :=
  law_of_refined (transmissionSubLimitExists_of_tight hTG hAbs)
    (transmissionTraceModulus_of_tight hTG hAbs) hMart hMass hEnt hPr hUniq

end BlockBand.Transmission.LawDuality
