module

public import BlockBand.SourceProcess.PhysApprox.B3GramSum
public import BlockBand.SourceProcess.PhysApprox.B3GenMem

/-!
# The closed contracting coordinates and their decay

* `B3ClosedContrDecay` (the decay, stated as a hypothesis): after each restart `r` (the
  closing length `n_s`, or `⌊Wτ_i⌋ + 1`), `‖1_{A_j}Q^Σ_{kl}(j)‖_p ≤ C(ρ^{j-r} + W^{-1/2})`, in the
  `genStepRate` form.
* `B3ClosedContrCesaro` (weaker): the Cesàro form
  `W⁻¹ Σ_{n_s ≤ j < ⌊WT⌋} ‖1_{A_j}Q^Σ_{kl}(j)‖_p → 0`; it already suffices for the summed drifts.
* `measurable_b3ContrCoord`, `aestronglyMeasurable_contr`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory ProbabilityTheory Filter Topology Matrix Finset
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Layers
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open BlockBand.SourceProcess.ClosingAux BlockBand.SourceProcess.FullSourceStops
open BlockBand.Transmission.Bridge
open scoped NNReal ENNReal ComplexConjugate

/-!
## The closed contracting separators and coordinates
-/

/-- The closed near-port scattering `P𝕊_cl = P𝕊_jC_j(z)` at length `j` (on the closed frame). -/
def b3ClosedPS (b E s h : ℝ) (W j : ℕ) (ω : GrowthPath W) (z : ℂ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  nearPortProj W * scatteringMatrix b E W j ω * physClosingMapAt b E s h W j ω z

/-- The four closed contracting separators `P𝕊_cl, 𝕊_cl*P, P𝕊_clP, P𝕊_cl*P`. -/
def b3ContrSep (b E s h : ℝ) (W j : ℕ) (ω : GrowthPath W) (z : ℂ) :
    Fin 4 → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  ![b3ClosedPS b E s h W j ω z, (b3ClosedPS b E s h W j ω z)ᴴ,
    b3ClosedPS b E s h W j ω z * nearPortProj W, nearPortProj W * (b3ClosedPS b E s h W j ω z)ᴴ]

/-- **The closed contracting coordinates** `Q^σ_{kl}(j) = (V_jᴴ Σ_σ V_j)_{kl}`, `V_j` the closed
frame at length `j`. -/
def b3ContrCoord (b E s h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (σ : Fin 4)
    (k l : SrcCol K (Fin np)) (y : ProbedPath W np × ℝ) : ℂ :=
  ((b3ClosedFrameAt b E s h τ m W j Vs y)ᴴ * b3ContrSep b E s h W j y.1.1 (phase y.2) σ *
    b3ClosedFrameAt b E s h τ m W j Vs y) k l

/-!
## Measurability
-/

theorem measurable_b3ClosedPS_comp (b E s h : ℝ) {np : ℕ} (W j : ℕ) :
    Measurable fun y : ProbedPath W np × ℝ => b3ClosedPS b E s h W j y.1.1 (phase y.2) := by
  have hω : Measurable fun y : ProbedPath W np × ℝ => y.1.1 := measurable_fst.comp measurable_fst
  have hz : Measurable fun y : ProbedPath W np × ℝ => phase y.2 :=
    measurable_phase.comp measurable_snd
  exact measurable_matrix_mul' (measurable_matrix_mul' measurable_const
    ((measurable_scatteringMatrix b E j).comp hω))
    (measurable_physClosingMapAt_comp b E s h j hω hz)

theorem measurable_b3ContrSep_comp (b E s h : ℝ) {np : ℕ} (W j : ℕ) (σ : Fin 4) :
    Measurable fun y : ProbedPath W np × ℝ => b3ContrSep b E s h W j y.1.1 (phase y.2) σ := by
  have hP := measurable_b3ClosedPS_comp b E s h (np := np) W j
  fin_cases σ
  · exact hP
  · exact measurable_matrix_conjTranspose' hP
  · exact measurable_matrix_mul' hP measurable_const
  · exact measurable_matrix_mul' measurable_const (measurable_matrix_conjTranspose' hP)

theorem measurable_b3ContrCoord (b E s h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (W j : ℕ)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} (hV : Measurable Vs)
    (σ : Fin 4) (k l : SrcCol K (Fin np)) :
    Measurable (b3ContrCoord b E s h τ m W j Vs σ k l) := by
  have hF := measurable_b3ClosedFrameAt b E s h τ m W j hV
  exact (measurable_matrix_mul' (measurable_matrix_mul' (measurable_matrix_conjTranspose' hF)
    (measurable_b3ContrSep_comp b E s h W j σ)) hF).eval_matrix

/-- The alive closed contracting coordinates are a.e. strongly measurable. -/
theorem aestronglyMeasurable_contr {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2)
    (s h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (R : ℝ) (W j : ℕ)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} (hV : Measurable Vs)
    (i : ℕ) (σ : Fin 4) (k l : SrcCol K (Fin np)) :
    AEStronglyMeasurable ((b3Alive b E s h τ m R W j Vs).indicator
      (b3ContrCoord b E s h τ m W i Vs σ k l)) (closedLaw b W np) :=
  genMem_aesm_indicator hb hE1 hE2 s h τ m R W j hV
    (measurable_b3ContrCoord b E s h τ m W i hV σ k l)

/-!
## The decay
-/

/-- **The closed contracting-word decay after restarts** (the word mixing rate for the closed
system). For every admissible frame, trace level `R` and exponent `p ≥ 1` there are `C ≥ 0` and
`0 ≤ ρ < 1` such that, eventually in `W`, at every length `n_s ≤ j ≤ ⌊WT⌋`, for every closed
contracting separator `σ` and all frame columns `k, l`,
`‖1_{A_j} Q^σ_{kl}(j)‖_{L^p(closedLaw)} ≤ C(Σ_{restarts r ≤ j} ρ^{j-r} + W^{-1/2})`. -/
def B3ClosedContrDecay : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R p : ℝ, 1 ≤ p →
    ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧
    ∀ᶠ W in atTop, ∀ j, closeLen s W ≤ j → j ≤ ⌊(W : ℝ) * T⌋₊ →
    ∀ (σ : Fin 4) (k l : SrcCol K (Fin np)),
      eLpNorm ((b3Alive b E s h τ m R W j (Vs W)).indicator
          (b3ContrCoord b E s h τ m W j (Vs W) σ k l)) (ENNReal.ofReal p) (closedLaw b W np) ≤
        ENNReal.ofReal (C * (genStepRate ρ s τ W j + 1 / Real.sqrt W))

/-- **The Cesàro form of the decay** (weaker). For every admissible frame, `R`,
`p ≥ 1`, `σ, k, l`: `W⁻¹ Σ_{n_s ≤ j < ⌊WT⌋} ‖1_{A_j} Q^σ_{kl}(j)‖_p → 0`. Implied by
`B3ClosedContrDecay` (`b3ClosedContrCesaro_of_decay`); it is all the summed drifts need. -/
def B3ClosedContrCesaro : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R p : ℝ, 1 ≤ p →
    ∀ (σ : Fin 4) (k l : SrcCol K (Fin np)),
    Tendsto (fun W : ℕ => (W : ℝ≥0∞)⁻¹ * ∑ j ∈ Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊,
      eLpNorm ((b3Alive b E s h τ m R W j (Vs W)).indicator
          (b3ContrCoord b E s h τ m W j (Vs W) σ k l)) (ENNReal.ofReal p) (closedLaw b W np))
      atTop (𝓝 0)

end BlockBand.SourceProcess.PhysApprox.B3
