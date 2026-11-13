module
public import BlockBand.SourceProcess.Stochastic.UniquenessDeg.DegSquare
public import BlockBand.SourceProcess.Stochastic.UniquenessDeg.PadMP
public import BlockBand.SourceProcess.Stochastic.Uniqueness.Sqrt
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Stopped-law uniqueness with a locally Lipschitz square root, in every universe

* `StoppedMartingaleProblemUniquenessU.{u,v} d m`: the body of
  `StoppedMartingaleProblemUniqueness d m` with
  `Ω₁ : Type u`, `Ω₂ : Type v`; `stoppedMartingaleProblemUniquenessU_zero_iff` (`Iff.rfl`).
* **`stoppedMartingaleProblemUniquenessU_holds`**, **`stoppedMartingaleProblemUniqueness_holds`**:
  state padding `y ↦ (y, 0) ∈ ℝ^{d+m}` (`Pad`, `PadMP`) reduces `σ : ℝ^d → ℝ^{d×m}`
  to the square case `stoppedMPUniqueness_square` (`DegSquare`), whose exit time from `padW W`
  is the exit time from `W`; the laws are transported back by the coordinatewise projection.
* `StoppedMartingaleProblemUniquenessPosDefU.{u,v} d`, `…PosDefU_zero_iff` (`Iff.rfl`),
  **`stoppedMartingaleProblemUniquenessPosDefU_holds`** (the positive definite case in every
  universe): the locally
  Lipschitz square root `σ = √a` (`exists_sqrt_of_posDef`) and the square case.

Proof of the square case (no pseudoinverse integrand, no Yamada–Watanabe): on the Wiener
extension with `2d` extra noises, the Tikhonov-regularized drivers
`Bd n = ∫ [P_ε | √(2ε) P_ε | ε G_ε⁻¹] dZ` (`P_ε = (sᵀs+ε)⁻¹sᵀ`, `G_ε = sᵀs+ε`, `s = σ(Y)`,
`ε = 1/(n+1)`) of the joint integrator `Z = (M, B')` are Brownian motions (`DegFromMP`); the
Euler schemes driven by `Bd n` approximate the stopped solution with an error controlled by
`frob(tikX ε - pinvX) → 0` (`DegCompY`, `DegCompX`, `DegLimit`, `DegChain`); the Euler schemes are
functionals of `(ξ, Bd n)` whose law depends only on `law(ξ)` (`DegLaw`).
-/

namespace BlockBand.SourceProcess.Stochastic.UniquenessDeg
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.Uniqueness
open scoped NNReal ENNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

universe u v

/-- The body of `StoppedMartingaleProblemUniqueness` with `Ω₁ : Type u`, `Ω₂ : Type v`. -/
def StoppedMartingaleProblemUniquenessU (d m : ℕ) : Prop :=
  ∀ (b : (Fin d → ℝ) → Fin d → ℝ) (σ : (Fin d → ℝ) → Matrix (Fin d) (Fin m) ℝ)
    (U W : Set (Fin d → ℝ)), IsOpen U → LocallyLipschitzOn U b → LocallyLipschitzOn U σ →
    IsInteriorDomain W U →
  ∀ (Ω₁ : Type u) [MeasurableSpace Ω₁] (Q₁ : Measure Ω₁) [IsProbabilityMeasure Q₁]
    (𝓖₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₁)) (Y₁ : ℝ≥0 → Ω₁ → Fin d → ℝ)
    (Ω₂ : Type v) [MeasurableSpace Ω₂] (Q₂ : Measure Ω₂) [IsProbabilityMeasure Q₂]
    (𝓖₂ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₂)) (Y₂ : ℝ≥0 → Ω₂ → Fin d → ℝ),
    IsMPSolutionOn Q₁ 𝓖₁ b (fun y => σ y * (σ y).transpose) W Y₁ →
    IsMPSolutionOn Q₂ 𝓖₂ b (fun y => σ y * (σ y).transpose) W Y₂ →
    Q₁.map (Y₁ 0) = Q₂.map (Y₂ 0) →
    Q₁.map (fun ω t => stoppedProcess Y₁ (exitTimeFrom W Y₁) t ω) =
      Q₂.map (fun ω t => stoppedProcess Y₂ (exitTimeFrom W Y₂) t ω)

/-- `StoppedMartingaleProblemUniqueness` is the universe-`0` instance. -/
theorem stoppedMartingaleProblemUniquenessU_zero_iff (d m : ℕ) :
    StoppedMartingaleProblemUniquenessU.{0, 0} d m ↔ StoppedMartingaleProblemUniqueness d m :=
  Iff.rfl

/-- The body of `StoppedMartingaleProblemUniquenessPosDef` with `Ω₁ : Type u`, `Ω₂ : Type v`. -/
def StoppedMartingaleProblemUniquenessPosDefU (d : ℕ) : Prop :=
  ∀ (b : (Fin d → ℝ) → Fin d → ℝ) (a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ)
    (U W : Set (Fin d → ℝ)), IsOpen U → LocallyLipschitzOn U b → ContDiffOn ℝ 2 a U →
    (∀ y ∈ U, (a y).PosDef) → IsInteriorDomain W U →
  ∀ (Ω₁ : Type u) [MeasurableSpace Ω₁] (Q₁ : Measure Ω₁) [IsProbabilityMeasure Q₁]
    (𝓖₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₁)) (Y₁ : ℝ≥0 → Ω₁ → Fin d → ℝ)
    (Ω₂ : Type v) [MeasurableSpace Ω₂] (Q₂ : Measure Ω₂) [IsProbabilityMeasure Q₂]
    (𝓖₂ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₂)) (Y₂ : ℝ≥0 → Ω₂ → Fin d → ℝ),
    IsMPSolutionOn Q₁ 𝓖₁ b a W Y₁ → IsMPSolutionOn Q₂ 𝓖₂ b a W Y₂ →
    Q₁.map (Y₁ 0) = Q₂.map (Y₂ 0) →
    Q₁.map (fun ω t => stoppedProcess Y₁ (exitTimeFrom W Y₁) t ω) =
      Q₂.map (fun ω t => stoppedProcess Y₂ (exitTimeFrom W Y₂) t ω)

/-- `StoppedMartingaleProblemUniquenessPosDef` is the universe-`0` instance. -/
theorem stoppedMartingaleProblemUniquenessPosDefU_zero_iff (d : ℕ) :
    StoppedMartingaleProblemUniquenessPosDefU.{0, 0} d ↔
      StoppedMartingaleProblemUniquenessPosDef d :=
  Iff.rfl

variable {d m : ℕ}

theorem exitTimeFrom_pad {Ω : Type*} (W : Set (Fin d → ℝ)) (Y : ℝ≥0 → Ω → Fin d → ℝ) :
    exitTimeFrom (padW (m := m) W) (fun t ω => padV (m := m) (Y t ω)) = exitTimeFrom W Y := by
  have h : ∀ y : Fin d → ℝ, padV (m := m) y ∈ padW (m := m) W ↔ y ∈ W := fun y =>
    Set.ext_iff.1 (preimage_padV_padW (m := m) W) y
  funext ω
  simp only [exitTimeFrom, h]

theorem measurable_padPath :
    Measurable fun (f : ℝ≥0 → Fin d → ℝ) (t : ℝ≥0) => padV (m := m) (f t) :=
  Measurable.of_eval fun t => continuous_padV.measurable.comp (measurable_pi_apply t)

theorem measurable_prjPath :
    Measurable fun (g : ℝ≥0 → Fin (d + m) → ℝ) (t : ℝ≥0) => prj (g t) :=
  Measurable.of_eval fun t => continuous_prj.measurable.comp (measurable_pi_apply t)

theorem map_eq_map_pad {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {F : Ω → ℝ≥0 → Fin d → ℝ} (hF : AEMeasurable F Q) :
    Q.map F = (Q.map fun ω t => padV (m := m) (F ω t)).map fun g t => prj (g t) := by
  have e : (fun ω t => padV (m := m) (F ω t)) = (fun f t => padV (m := m) (f t)) ∘ F := rfl
  rw [e, AEMeasurable.map_map_of_aemeasurable measurable_prjPath.aemeasurable
    ((measurable_padPath (m := m)).comp_aemeasurable hF)]
  congr 1
  funext ω t
  simp

/-- **Stopped-law uniqueness with a locally Lipschitz square root, in every universe.** -/
theorem stoppedMartingaleProblemUniquenessU_holds (d m : ℕ) :
    StoppedMartingaleProblemUniquenessU.{u, v} d m := by
  intro b σ U W hU hb hσ hWU Ω₁ _ Q₁ _ 𝓖₁ Y₁ Ω₂ _ Q₂ _ 𝓖₂ Y₂ hY₁ hY₂ h0
  have hYa₁ : ∀ t, Measurable[𝓖₁ t] (Y₁ t) := fun t => (hY₁.adapted t).measurable
  have hYa₂ : ∀ t, Measurable[𝓖₂ t] (Y₂ t) := fun t => (hY₂.adapted t).measurable
  have h0' : Q₁.map (fun ω => padV (m := m) (Y₁ 0 ω)) = Q₂.map (fun ω => padV (m := m) (Y₂ 0 ω)) := by
    rw [show (fun ω => padV (m := m) (Y₁ 0 ω)) = padV ∘ Y₁ 0 from rfl,
      show (fun ω => padV (m := m) (Y₂ 0 ω)) = padV ∘ Y₂ 0 from rfl,
      ← Measure.map_map continuous_padV.measurable ((hYa₁ 0).mono (𝓖₁.le 0) le_rfl),
      ← Measure.map_map continuous_padV.measurable ((hYa₂ 0).mono (𝓖₂.le 0) le_rfl), h0]
  have hp := stoppedMPUniqueness_square (padB b) (padS σ) (prj (m := m) ⁻¹' U) (padW W)
    (hU.preimage continuous_prj) (locallyLipschitzOn_padB hb) (locallyLipschitzOn_padS hσ)
    (isInteriorDomain_padW hWU) (isMPSolutionOn_pad hY₁) (isMPSolutionOn_pad hY₂) h0'
  rw [exitTimeFrom_pad, exitTimeFrom_pad] at hp
  rw [map_eq_map_pad (m := m) (aemeasurable_stopped hYa₁ hY₁.continuous hWU.1),
    map_eq_map_pad (m := m) (aemeasurable_stopped hYa₂ hY₂.continuous hWU.1)]
  exact congrArg (fun μ => μ.map fun g t => prj (g t)) hp

/-- **`StoppedMartingaleProblemUniqueness` holds.** -/
theorem stoppedMartingaleProblemUniqueness_holds (d m : ℕ) :
    StoppedMartingaleProblemUniqueness d m :=
  (stoppedMartingaleProblemUniquenessU_zero_iff d m).1
    (stoppedMartingaleProblemUniquenessU_holds d m)

/-- **Stopped-law uniqueness for a positive definite covariance, in every universe.** -/
theorem stoppedMartingaleProblemUniquenessPosDefU_holds (d : ℕ) :
    StoppedMartingaleProblemUniquenessPosDefU.{u, v} d := by
  intro b a U W hU hb ha hpos hWU Ω₁ _ Q₁ _ 𝓖₁ Y₁ Ω₂ _ Q₂ _ 𝓖₂ Y₂ hY₁ hY₂ h0
  obtain ⟨σ, hσL, hσa, -⟩ := exists_sqrt_of_posDef hU ha hpos
  have hWsubU : W ⊆ U := subset_closure.trans hWU.2.2
  exact stoppedMPUniqueness_square b σ U W hU hb hσL hWU
    (isMPSolutionOn_congr hY₁ fun y hy => (hσa y (hWsubU hy)).symm)
    (isMPSolutionOn_congr hY₂ fun y hy => (hσa y (hWsubU hy)).symm) h0

end BlockBand.SourceProcess.Stochastic.UniquenessDeg
