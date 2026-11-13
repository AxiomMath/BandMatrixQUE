module
public import BlockBand.SourceProcess.Stochastic.SemimartingaleIto.Localizer
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Universe-polymorphic Itô formula

`SemimartingaleItoFormulaU` is `SemimartingaleItoFormula` with the probability space in an
arbitrary universe, and `semimartingaleItoFormulaU_holds` proves it by the same argument.
-/

namespace BlockBand.SourceProcess.Stochastic.SemimartingaleIto
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.Internal.Contracts.Transmission
open scoped NNReal

universe u

/-- The statement of `SemimartingaleItoFormula` with `Ω : Type u`. -/
def SemimartingaleItoFormulaU (d : ℕ) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) (Y : ℝ≥0 → Ω → Fin d → ℝ)
    (β : ℝ≥0 → Ω → Fin d → ℝ) (α : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ),
    IsContinuousSemimartingale Q 𝓖 Y β α →
  ∀ U : Set (Fin d → ℝ), IsOpen U → (∀ᵐ ω ∂Q, ∀ t, Y t ω ∈ U) →
  ∀ φ : ℝ × (Fin d → ℝ) → ℝ, Measurable φ → ContDiffOn ℝ 2 φ (Set.univ ×ˢ U) →
    IsContinuousSemimartingale (d := 1) Q 𝓖 (fun t ω (_ : Fin 1) => φ ((t : ℝ), Y t ω))
      (fun t ω (_ : Fin 1) => itoDrift φ (Y t ω) t (β t ω) (α t ω))
      (fun t ω => Matrix.of fun (_ _ : Fin 1) => itoBracket φ (Y t ω) t (α t ω))

/-- `SemimartingaleItoFormula` is the universe-0 instance. -/
theorem semimartingaleItoFormulaU_zero_iff (d : ℕ) :
    SemimartingaleItoFormulaU.{0} d ↔ SemimartingaleItoFormula d := Iff.rfl

/-- The Itô formula in every universe, by the proof of `SemimartingaleItoFormula`. -/
theorem semimartingaleItoFormulaU_holds (d : ℕ) : SemimartingaleItoFormulaU.{u} d := by
  intro Ω _ Q _ 𝓖 Y β α H U hU hYU φ hφm hφ
  obtain ⟨σ, hσ, hσlim, hloc⟩ := exists_localizer H hU hYU hφm hφ
  have hconst : Continuous fun x : ℝ => (fun _ : Fin 1 => x) :=
    continuous_pi fun _ => continuous_id
  refine ⟨fun t => ?_, fun i => ?_, ?_, fun i => ?_, fun i => ?_, ?_, ⟨σ, hσ, hσlim, fun m => ?_⟩⟩
  · exact hconst.comp_stronglyMeasurable
      ((isStronglyProgressive_phi hφm H.progressive).stronglyAdapted t)
  · exact hconst.comp_stronglyMeasurable (isStronglyProgressive_phi hφm H.progressive i)
  · filter_upwards [H.continuous, hYU] with ω hω hU'
    exact hconst.comp (hφ.continuousOn.comp_continuous (NNReal.continuous_coe.prodMk hω)
      fun t => ⟨mem_univ _, hU' t⟩)
  · exact hconst.comp_stronglyMeasurable (isStronglyProgressive_driftPath φ H.progressive
      H.drift_progressive H.cov_progressive i)
  · exact (continuous_matrix fun _ _ => continuous_id).comp_stronglyMeasurable
      (isStronglyProgressive_bracketPath φ H.progressive H.cov_progressive i)
  · filter_upwards [H.continuous, hYU, H.integrable] with ω hω hU' hi t
    exact ⟨fun _ => integrableOn_itoDrift_path hU hφ hω hU' t (hi t).1 (hi t).2,
      fun _ _ => integrableOn_itoBracket_path hU hφ hω hU' t (hi t).2⟩
  · obtain ⟨⟨W, T, c, ys, D⟩, hN, hB⟩ := hloc m
    obtain ⟨h1, h2⟩ := D.ito_local hN hB
    refine ⟨fun i => ?_, fun i j => ?_⟩
    · obtain rfl : i = 0 := Subsingleton.elim _ _
      exact h1
    · obtain rfl : i = 0 := Subsingleton.elim _ _
      obtain rfl : j = 0 := Subsingleton.elim _ _
      exact h2

end BlockBand.SourceProcess.Stochastic.SemimartingaleIto
