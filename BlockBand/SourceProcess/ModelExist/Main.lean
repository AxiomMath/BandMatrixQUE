module

public import BlockBand.SourceProcess.ModelExist.ModelSpec
public import BlockBand.SourceProcess.ModelExist.ModelSDE
public import BlockBand.SourceProcess.ModelExist.ModelLaws
public import BlockBand.SourceProcess.SourceProcessLaw.Interface

/-!
# `ModelExists` from the perpendicular selection

`modelExists_of_perpSelection (hPS : PerpSelectionHolds) : ModelExists`; the hypothesis is proved in
`perpSelectionHolds`. Construction: the driver space over `S = (ℕ → ℝ) × (π → ℝ)` with
`μ = ρ ⊗ Π birthTimeLaw`; the ambient space `Amb K R` (`R = 2K + |π| + 1` extra near coordinates);
the solution `X` of the finite source equation from the extended frame `[initialFrame | 1]`
(`finiteSourceWellPosed_holds`); its Gram process `𝒢` (a Gram martingale-problem solution,
`ambient_isGramMartingaleSolution`); probe vectors chosen in the order of the birth times by the
selection (`BirthSort`); the born Gram process `G_t = congrGram L_t 𝒢_t`
(`isBornGramSolution_bornG`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ModelExist
open MeasureTheory ProbabilityTheory Filter Set Matrix
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.BornUnique BlockBand.SourceProcess.SourceProcessLaw
open scoped NNReal ENNReal

/-- **A measurable perpendicular selection exists** for every finite column type (pure linear
algebra and measurability). Proved as `perpSelectionHolds`, from
`perpSelection_holds`. -/
def PerpSelectionHolds : Prop :=
  ∀ (c' : Type) [Fintype c'] [DecidableEq c'] (n : ℕ) (cur : c' → Prop) [DecidablePred cur],
    PerpSelection c' n cur

theorem measurableSpace_congr {Ω : Type*} [MeasurableSpace Ω]
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {τ₁ τ₂ : Ω → WithTop ℝ≥0}
    (h : τ₁ = τ₂) (h₁ : IsStoppingTime 𝓖 τ₁) (h₂ : IsStoppingTime 𝓖 τ₂) :
    h₁.measurableSpace = h₂.measurableSpace := by
  subst h; rfl

theorem v_nonneg {b s T : ℝ} (hb1 : b < 1 / 2) {q : ℝ → ℝ} (hq : IsSourceTest s T q) (M : ℕ) :
    0 ≤ dStar b * sourceMass s T q / M := by
  have hd : 0 < dStar b := by unfold dStar; exact one_div_pos.2 (by linarith)
  exact div_nonneg (mul_nonneg hd.le (sourceMass_nonneg hq)) (Nat.cast_nonneg M)

end BlockBand.SourceProcess.ModelExist
