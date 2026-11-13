module
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.AssemblyStrata
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.AssemblyLaw
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.RankCorOn
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.Patch
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Gram uniqueness: conditioning a Gram MP solution on an initial stratum

For a feasible Gram MP solution `G` on `(Ω, 𝓖, Q)` and a stratum index `s = (r, r')`, the event
`A_s = {stratumIdx (G_0) = s}` lies in `𝓖₀` (by `measurable_stratumIdx` and `measurable_G0`),
and under `Q[|A_s]` the process `G` is again a solution (`isGramMartingaleSolution_cond`) whose
initial state is a.s. on the fixed stratum required by `GramChart.gramLaw_eq_of_stratum`
(`stratum_ae_cond`). `cond_gramLaw_eq`: two solutions with equal initial laws have equal conditional
path laws on each stratum of positive mass.
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness
open Matrix MeasureTheory ProbabilityTheory Filter Set
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.SourceSDE
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  frobBorelSpace matrixPseudoMetrizable

variable {c : Type*} [Fintype c] [DecidableEq c]

universe u v

omit [DecidableEq c] in
theorem measurable_G0 {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {D0 : ℝ} {D : Matrix c c ℂ}
    {G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ} (hG : IsGramMartingaleSolution Q 𝓖 D0 D G)
    (t : ℝ≥0) : Measurable[𝓖 t] (G t) := by
  have : SecondCountableTopology (Matrix c c ℂ) :=
    inferInstanceAs (SecondCountableTopology (c → c → ℂ))
  have : BorelSpace (Matrix c c ℂ × Matrix c c ℂ) := Prod.borelSpace
  exact (hG.adapted t).measurable

omit [DecidableEq c] in
theorem measurable_path {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {D0 : ℝ} {D : Matrix c c ℂ}
    {G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ} (hG : IsGramMartingaleSolution Q 𝓖 D0 D G) :
    Measurable fun ω t => G t ω :=
  Measurable.of_eval fun t => (measurable_G0 hG t).mono (𝓖.le t) le_rfl

theorem stratum_ae_cond {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {D0 : ℝ} {D : Matrix c c ℂ}
    {G : ℝ≥0 → Ω → Matrix c c ℂ × Matrix c c ℂ} (hG : IsGramMartingaleSolution Q 𝓖 D0 D G)
    (s : Fin (Fintype.card c + 1) × Fin (Fintype.card c + 1)) :
    let A := (fun ω => stratumIdx (G 0 ω)) ⁻¹' {s}
    (∀ᵐ ω ∂Q[|A], principalMinorSum ((s.1 : ℕ) + 1) (G 0 ω).2 = 0) ∧
    (∀ᵐ ω ∂Q[|A], 0 < principalMinorSum (s.1 : ℕ) (G 0 ω).2) ∧
    (∀ᵐ ω ∂Q[|A], principalMinorSum ((s.2 : ℕ) + 1) ((G 0 ω).1 - (G 0 ω).2) = 0) ∧
    (∀ᵐ ω ∂Q[|A], 0 < principalMinorSum (s.2 : ℕ) ((G 0 ω).1 - (G 0 ω).2)) := by
  intro A
  have hA : MeasurableSet A :=
    ((measurable_stratumIdx.comp (measurable_G0 hG 0)).mono (𝓖.le 0) le_rfl)
      (measurableSet_singleton s)
  have key : ∀ᵐ ω ∂Q, ω ∈ A → (principalMinorSum ((s.1 : ℕ) + 1) (G 0 ω).2 = 0 ∧
      0 < principalMinorSum (s.1 : ℕ) (G 0 ω).2 ∧
      principalMinorSum ((s.2 : ℕ) + 1) ((G 0 ω).1 - (G 0 ω).2) = 0 ∧
      0 < principalMinorSum (s.2 : ℕ) ((G 0 ω).1 - (G 0 ω).2)) := by
    filter_upwards [hG.feasible] with ω hf hω
    have hs : stratumIdx (G 0 ω) = s := hω
    have h1 : rankB (G 0 ω) = s.1 := by rw [← hs]; rfl
    have h2 : rankC (G 0 ω) = s.2 := by rw [← hs]; rfl
    rw [← h1, ← h2]
    exact stratum_facts (hf 0)
  have hk := ae_cond_of_ae_on hA key
  exact ⟨hk.mono fun _ h => h.1, hk.mono fun _ h => h.2.1, hk.mono fun _ h => h.2.2.1,
    hk.mono fun _ h => h.2.2.2⟩

/-- Equal conditional path laws on each stratum of positive mass. -/
theorem cond_gramLaw_eq {D0 : ℝ} (hD0 : 0 < D0) {D : Matrix c c ℂ} (hD : IsSignature D)
    {Ω₁ : Type u} [MeasurableSpace Ω₁] {Q₁ : Measure Ω₁} [IsProbabilityMeasure Q₁]
    {𝓖₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₁)}
    {G₁ : ℝ≥0 → Ω₁ → Matrix c c ℂ × Matrix c c ℂ} (hG₁ : IsGramMartingaleSolution Q₁ 𝓖₁ D0 D G₁)
    {Ω₂ : Type v} [MeasurableSpace Ω₂] {Q₂ : Measure Ω₂} [IsProbabilityMeasure Q₂]
    {𝓖₂ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₂)}
    {G₂ : ℝ≥0 → Ω₂ → Matrix c c ℂ × Matrix c c ℂ} (hG₂ : IsGramMartingaleSolution Q₂ 𝓖₂ D0 D G₂)
    (h0 : Q₁.map (G₁ 0) = Q₂.map (G₂ 0))
    (s : Fin (Fintype.card c + 1) × Fin (Fintype.card c + 1))
    (hs : Q₁ ((fun ω => stratumIdx (G₁ 0 ω)) ⁻¹' {s}) ≠ 0) :
    (Q₁[|(fun ω => stratumIdx (G₁ 0 ω)) ⁻¹' {s}]).map (fun ω t => G₁ t ω) =
      (Q₂[|(fun ω => stratumIdx (G₂ 0 ω)) ⁻¹' {s}]).map (fun ω t => G₂ t ω) := by
  have hm₁ := (measurable_G0 hG₁ 0).mono (𝓖₁.le 0) le_rfl
  have hm₂ := (measurable_G0 hG₂ 0).mono (𝓖₂.le 0) le_rfl
  have hS : MeasurableSet (stratumIdx (c := c) ⁻¹' {s}) :=
    measurable_stratumIdx (measurableSet_singleton s)
  have hmass := mass_eq_of_map_eq hm₁ hm₂ h0 hS
  have hs₂ : Q₂ ((fun ω => stratumIdx (G₂ 0 ω)) ⁻¹' {s}) ≠ 0 := by
    change Q₂ (G₂ 0 ⁻¹' (stratumIdx ⁻¹' {s})) ≠ 0
    change Q₁ (G₁ 0 ⁻¹' (stratumIdx ⁻¹' {s})) ≠ 0 at hs
    rwa [← hmass]
  have hA₁ : MeasurableSet[𝓖₁ 0] ((fun ω => stratumIdx (G₁ 0 ω)) ⁻¹' {s}) :=
    (measurable_stratumIdx.comp (measurable_G0 hG₁ 0)) (measurableSet_singleton s)
  have hA₂ : MeasurableSet[𝓖₂ 0] ((fun ω => stratumIdx (G₂ 0 ω)) ⁻¹' {s}) :=
    (measurable_stratumIdx.comp (measurable_G0 hG₂ 0)) (measurableSet_singleton s)
  have := cond_isProbabilityMeasure (μ := Q₁) hs
  have := cond_isProbabilityMeasure (μ := Q₂) hs₂
  obtain ⟨a₁, b₁, c₁, d₁⟩ := stratum_ae_cond hG₁ s
  obtain ⟨a₂, b₂, c₂, d₂⟩ := stratum_ae_cond hG₂ s
  exact GramChart.gramLaw_eq_of_stratum hD0 hD (isGramMartingaleSolution_cond hG₁ hA₁ hs)
    a₁ b₁ c₁ d₁ (isGramMartingaleSolution_cond hG₂ hA₂ hs₂) a₂ b₂ c₂ d₂
    (cond_map_eq_of_map_eq hm₁ hm₂ h0 hS)

end BlockBand.SourceProcess.Stochastic.GramUniqueness
