module

public import BlockBand.Transmission.Dual.GLemma1Test
public import BlockBand.SourceProcess.Stochastic.Uniqueness.Main

/-!
# The local Doob identity, abstract form

Setting: `Z` a base solution from `z` (`IsBaseSol`, any `(Ω : Type, 𝓖, P)`), `W` an interior
domain of the flat chamber with `z ∈ W`, `D₀ > 0`, and a **comparison solution** `Y₂` (any
filtered probability space) of the flat dual martingale problem in `W` with `Y₂(0) = z` in law
(for instance the dual up to exhaustion stopped at `ρ_m` with `closure W ⊂ int K_m`).
* `lemma1_law`: the law of `Y₂` stopped at its exit from `W` is `P̃ ∘ (Z^τ)⁻¹`, with `P̃ = g · P`
  the tilt of `lemma1_tilt` (`stoppedMartingaleProblemUniquenessPosDef_holds`).
* **`lemma1`**: for every `t₀` and every measurable set `B` of paths,
  `Q₂((Y₂^{τ₂})^{t₀} ∈ B) = E_P[H_q(Z_{t₀∧τ})/H_q(z); (Z^τ)^{t₀} ∈ B]`, where `w^{t₀}(t) = w(t ∧ t₀)`.
  This is the local Doob identity with `T = t₀ ∧ τ_K`, `K = closure W`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.Internal.Contracts.Transmission BlockBand.Transmission.Dual
open BlockBand.SourceProcess.Stochastic.Uniqueness
open BlockBand.SourceProcess.Stochastic.Semimartingale (stopTime stoppedProcess_eq_stopTime
  exitTimeFrom_attained mem_of_lt_exitTimeFrom)
open scoped NNReal ENNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {q : ℕ} {D0 : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {Z : ℝ≥0 → Ω → Fin (q + q) → ℝ}
  {z : Fin (q + q) → ℝ} {W : Set (Fin (q + q) → ℝ)}

/-- The stopped path leaves `W` exactly when the path does. -/
theorem exitTimeFrom_stopZ (hZ : IsBaseSol D0 q P 𝓖 Z z) (hW : IsOpen W) (ω : Ω) :
    exitTimeFrom W (stopZ W Z) ω = exitTimeFrom W Z ω := by
  rcases exitTimeFrom_attained hW (hZ.cont ω) with he | ⟨s₀, he, hs₀⟩
  · have : ∀ t, stopZ W Z t ω = Z t ω := fun t => by
      rw [stopZ, stoppedProcess_eq_stopTime, he, Semimartingale.stopTime_top]
    rw [exitTimeFrom_congr_path this]
  · rw [he]
    refine le_antisymm (iInf₂_le s₀ ?_) (le_iInf₂ fun t ht => ?_)
    · rw [stopZ, stoppedProcess_eq_stopTime, he, Semimartingale.stopTime_coe, min_self]
      exact hs₀
    · by_contra hlt
      push Not at hlt
      have hlt' : (t : WithTop ℝ≥0) < exitTimeFrom W Z ω := he ▸ hlt
      refine ht ?_
      rw [stopZ, stoppedProcess_eq_stopTime, Semimartingale.stopTime_of_lt hlt']
      exact mem_of_lt_exitTimeFrom hlt'

theorem stoppedProcess_stopZ (hZ : IsBaseSol D0 q P 𝓖 Z z) (hW : IsOpen W) :
    stoppedProcess (stopZ W Z) (exitTimeFrom W (stopZ W Z)) = stopZ W Z := by
  funext t ω
  rw [stoppedProcess_eq_stopTime, exitTimeFrom_stopZ hZ hW, stopZ, stoppedProcess_eq_stopTime,
    stoppedProcess_eq_stopTime, stopTime_stopTime_of_le le_rfl]

theorem measurable_stopZ_path (hZ : IsBaseSol D0 q P 𝓖 Z z) (hW : IsOpen W) (t₀ : ℝ≥0) :
    Measurable[𝓖 t₀] (fun ω t => stopZ W Z (min t t₀) ω) :=
  @Measurable.of_eval Ω ℝ≥0 (fun _ => Fin (q + q) → ℝ) (𝓖 t₀) _ _ fun t =>
    ((stronglyMeasurable_stopZ hZ hW (min t t₀)).measurable.mono (𝓖.mono (min_le_right _ _))
      le_rfl)

theorem measurable_truncate (t₀ : ℝ≥0) :
    Measurable (fun (w : ℝ≥0 → Fin (q + q) → ℝ) t => w (min t t₀)) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

variable [IsProbabilityMeasure P]

/-- **The local Doob identity, law form**: the stopped comparison law is the tilted law of
`Z^τ`. -/
theorem lemma1_law (hD0 : 0 < D0) (hZ : IsBaseSol D0 q P 𝓖 Z z)
    (hW : IsInteriorDomain W (flatChamber q)) (hzW : z ∈ W) {Ω₂ : Type} [MeasurableSpace Ω₂]
    {Q₂ : Measure Ω₂} [IsProbabilityMeasure Q₂]
    {𝓗 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₂)} {Y₂ : ℝ≥0 → Ω₂ → Fin (q + q) → ℝ}
    (h₂ : IsMPSolutionOn Q₂ 𝓗 (flatDrift D0 q) (flatDiff D0 q) W Y₂)
    (h₂0 : Q₂.map (Y₂ 0) = Measure.dirac z) :
    ∃ (M : ℝ≥0 → Ω → ℝ) (g : Ω → ℝ≥0), IsDensity P 𝓖 M g ∧
      (∀ t, M t =ᵐ[P] densM W Z z t) ∧ IsProbabilityMeasure (tilt P g) ∧
      Q₂.map (fun ω t => stoppedProcess Y₂ (exitTimeFrom W Y₂) t ω) =
        (tilt P g).map (fun ω t => stopZ W Z t ω) := by
  obtain ⟨M, g, hg, hMe, hprob, hsol⟩ := lemma1_tilt hZ hW hzW
  refine ⟨M, g, hg, hMe, hprob, ?_⟩
  have h0 : (tilt P g).map (stopZ W Z 0) = Q₂.map (Y₂ 0) := by
    have e : stopZ W Z 0 = fun _ => z := funext fun ω => by
      rw [stopZ, stoppedProcess_eq_stopTime, Semimartingale.stopTime_zero, hZ.start]
    rw [e, h₂0, Measure.map_const, measure_univ, one_smul]
  have hfull := stoppedMartingaleProblemUniquenessPosDef_holds (q + q) (flatDrift D0 q)
    (flatDiff D0 q) (flatChamber q) W (isOpen_flatChamber q) (locallyLipschitzOn_flatDrift D0)
    (contDiffOn_flatDiff D0) (fun w hw => flatDiff_posDef hD0 hw) hW Ω (tilt P g) 𝓖 (stopZ W Z)
    Ω₂ Q₂ 𝓗 Y₂ hsol h₂ h0
  rw [← hfull, stoppedProcess_stopZ hZ hW.1]

/-- **The local Doob identity.** For `t₀ ≥ 0` and a measurable set `B` of paths,
`Q₂((Y₂^{τ₂})^{t₀} ∈ B) = E_P[H_q(Z_{t₀∧τ})/H_q(z); (Z^τ)^{t₀} ∈ B]`. -/
theorem lemma1 (hD0 : 0 < D0) (hZ : IsBaseSol D0 q P 𝓖 Z z)
    (hW : IsInteriorDomain W (flatChamber q)) (hzW : z ∈ W) {Ω₂ : Type} [MeasurableSpace Ω₂]
    {Q₂ : Measure Ω₂} [IsProbabilityMeasure Q₂]
    {𝓗 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₂)} {Y₂ : ℝ≥0 → Ω₂ → Fin (q + q) → ℝ}
    (h₂ : IsMPSolutionOn Q₂ 𝓗 (flatDrift D0 q) (flatDiff D0 q) W Y₂)
    (h₂0 : Q₂.map (Y₂ 0) = Measure.dirac z) (t₀ : ℝ≥0)
    {B : Set (ℝ≥0 → Fin (q + q) → ℝ)} (hB : MeasurableSet B) :
    Q₂.real {ω | (fun t => stoppedProcess Y₂ (exitTimeFrom W Y₂) (min t t₀) ω) ∈ B} =
      ∫ ω in {ω | (fun t => stopZ W Z (min t t₀) ω) ∈ B}, densM W Z z t₀ ω ∂P := by
  obtain ⟨M, g, hg, hMe, hprob, hlaw⟩ := lemma1_law hD0 hZ hW hzW h₂ h₂0
  have hTB := measurable_truncate (q := q) t₀ hB
  have hY₂m : AEMeasurable (fun ω t => stoppedProcess Y₂ (exitTimeFrom W Y₂) t ω) Q₂ :=
    aemeasurable_stopped (fun t => (h₂.adapted t).measurable) h₂.continuous hW.1
  have hZm : Measurable fun ω t => stopZ W Z t ω :=
    Measurable.of_eval fun t => (stronglyMeasurable_stopZ hZ hW.1 t).measurable.mono
      (𝓖.le t) le_rfl
  have hS : MeasurableSet[𝓖 t₀] {ω | (fun t => stopZ W Z (min t t₀) ω) ∈ B} :=
    measurable_stopZ_path hZ hW.1 t₀ hB
  have e1 : Q₂ {ω | (fun t => stoppedProcess Y₂ (exitTimeFrom W Y₂) (min t t₀) ω) ∈ B} =
      tilt P g {ω | (fun t => stopZ W Z (min t t₀) ω) ∈ B} := by
    have := congrArg (fun μ : Measure (ℝ≥0 → Fin (q + q) → ℝ) =>
      μ ((fun (w : ℝ≥0 → Fin (q + q) → ℝ) t => w (min t t₀)) ⁻¹' B)) hlaw
    rwa [Measure.map_apply_of_aemeasurable hY₂m hTB, Measure.map_apply hZm hTB] at this
  have e2 := hg.setIntegral_tilt_eq (f := fun _ => (1 : ℝ)) stronglyMeasurable_const (C := 1)
    (Eventually.of_forall fun _ => by simp) hS
  rw [setIntegral_const, smul_eq_mul, mul_one] at e2
  rw [measureReal_def, e1, ← measureReal_def, e2]
  refine setIntegral_congr_ae (𝓖.le t₀ _ hS) ?_
  filter_upwards [hMe t₀] with ω hω _
  rw [mul_one, hω]

end BlockBand.Transmission.Dual.G
