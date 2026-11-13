module
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.AssemblyStratum
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.AmbientBridge
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Gram martingale-problem uniqueness, including initially singular strata

**`gramMartingaleProblemUniqueness_holds`** proves
`GramMartingaleProblemUniqueness μ Q 𝓖 D0 D Naux P` (the uniqueness part of the finite Gram law).

* `gramLaw_eq_of_initial`: two feasible Gram MP solutions (sample spaces in any universes) with
  equal initial laws have equal path laws. Partition both sample spaces into the finitely many
  `𝓖₀`-strata `{stratumIdx G₀ = (r, r')}` (`AssemblyStrata`). The strata have equal masses, and
  on each stratum of positive mass the conditional laws agree (`cond_gramLaw_eq`, from
  `GramChart.gramLaw_eq_of_stratum`). Then glue (`map_eq_of_cond_strata`).
* The main theorem applies this to `G` and to the ambient Gram process, which is a solution
  (`ambient_isGramMartingaleSolution`) and has initial law equal to that of `gramPair P ξ`
  (`X₀ = ξ` a.s.). Its path law is `gramPathLaw μ P X` by definition.
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness
open Matrix MeasureTheory ProbabilityTheory Filter Set
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.SourceSDE
open BlockBand.SourceProcess.FiniteDriverIntegration
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  frobBorelSpace matrixPseudoMetrizable

variable {c : Type*} [Fintype c] [DecidableEq c]

universe u v

/-- **Uniqueness of the Gram path law given the initial law.** -/
theorem gramLaw_eq_of_initial {D0 : ℝ} (hD0 : 0 < D0) {D : Matrix c c ℂ} (hD : IsSignature D)
    {Ω₁ : Type u} [MeasurableSpace Ω₁] {Q₁ : Measure Ω₁} [IsProbabilityMeasure Q₁]
    {𝓖₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₁)}
    {G₁ : ℝ≥0 → Ω₁ → Matrix c c ℂ × Matrix c c ℂ} (hG₁ : IsGramMartingaleSolution Q₁ 𝓖₁ D0 D G₁)
    {Ω₂ : Type v} [MeasurableSpace Ω₂] {Q₂ : Measure Ω₂} [IsProbabilityMeasure Q₂]
    {𝓖₂ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₂)}
    {G₂ : ℝ≥0 → Ω₂ → Matrix c c ℂ × Matrix c c ℂ} (hG₂ : IsGramMartingaleSolution Q₂ 𝓖₂ D0 D G₂)
    (h0 : Q₁.map (G₁ 0) = Q₂.map (G₂ 0)) :
    Q₁.map (fun ω t => G₁ t ω) = Q₂.map (fun ω t => G₂ t ω) := by
  have hm₁ := (measurable_G0 hG₁ 0).mono (𝓖₁.le 0) le_rfl
  have hm₂ := (measurable_G0 hG₂ 0).mono (𝓖₂.le 0) le_rfl
  exact map_eq_of_cond_strata (measurable_stratumIdx.comp hm₁) (measurable_stratumIdx.comp hm₂)
    (measurable_path hG₁) (measurable_path hG₂)
    (fun s => mass_eq_of_map_eq hm₁ hm₂ h0 (measurable_stratumIdx (measurableSet_singleton s)))
    (fun s hs => cond_gramLaw_eq hD0 hD hG₁ hG₂ h0 s hs)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]

/-- **`GramMartingaleProblemUniqueness` holds.** -/
theorem gramMartingaleProblemUniqueness_holds {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    [IsProbabilityMeasure Q] (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (D0 : ℝ) (D : Matrix c c ℂ) (Naux : ℕ) (P : Matrix ι ι ℂ) :
    GramMartingaleProblemUniqueness μ Q 𝓖 D0 D Naux P := by
  intro hD0 hP hD G hG ξ hξm hξc h0 X hX
  have hGa := ambient_isGramMartingaleSolution μ hD0 hP hD hξm hξc hX
  refine gramLaw_eq_of_initial hD0 hD hG hGa ?_
  rw [h0]
  refine Measure.map_congr ?_
  filter_upwards [hX.2] with x hx
  simp only [hx]

end BlockBand.SourceProcess.Stochastic.GramUniqueness
