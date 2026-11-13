module

public import BlockBand.SourceProcess.PhysApprox.Defs
public import BlockBand.SourceProcess.ClosingAux.Meas
public import BlockBand.SourceProcess.ComplexSourceLaw.Measurability
public import BlockBand.SourceProcess.ComplexConstruct.Tight

/-!
# Measurability of the closed complex source data

* `closedK_zero`: `closedK … 0 = complexSourceK …` (the `f(0) = 0` of Kolmogorov; the Gram
  coordinates do not reduce at `z = 0`).
* `measurable_closedK_comp`, `measurable_closedFrame_comp`, `measurable_closedSourceData_comp`:
  along measurable maps to the probed path and to the phase `z ∈ ℂ`.
* `measurable_closedSourceData`: jointly measurable in the probed path and `θ`, `z = phase θ`
  (the integrand of `closedPhysExpectation`).
* `integrable_closedIntegrand`: `Φ ∘ closedSourceData` is integrable under
  `probedPathLaw ⊗ phaseLaw` for every bounded continuous `Φ`.
-/

set_option autoImplicit false

@[expose] public section

namespace BlockBand.SourceProcess.PhysApprox

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.Closing
open BlockBand.SourceProcess.ClosingAux
open BlockBand.Transmission.Bridge BlockBand.SourceProcess.FullSourceStops

variable {W np : ℕ}

/-- At `z = 0` the closed `𝒦` is the unclosed `𝒦 = complexSourceK`. -/
theorem closedK_zero (b E s T h : ℝ) (τ m : Fin np → ℝ) (x : ProbedPath W np) :
    closedK b E s T h τ m W 0 x = complexSourceK b E W ⌊(W : ℝ) * T⌋₊ τ m x := by
  simp [closedK]

/-- `N = Π𝕊A` along a measurable map to the path. -/
theorem measurable_physClosingN_comp {α : Type*} [MeasurableSpace α] (b E s T h : ℝ)
    {f : α → GrowthPath W} (hf : Measurable f) :
    Measurable fun a => physClosingN b E s T h W (f a) := by
  unfold physClosingN closingN
  exact measurable_matrix_mul' (measurable_matrix_mul'
    (measurable_farEmbed ((measurable_closingPairing b E h _).comp hf))
    ((measurable_scatteringMatrix b E _).comp hf))
    (measurable_farEmbed ((measurable_omittedProj b E h _).comp hf))

/-- The closed `𝒦` along measurable maps to the probed path and the phase. -/
theorem measurable_closedK_comp {α : Type*} [MeasurableSpace α] (b E s T h : ℝ)
    (τ m : Fin np → ℝ) {f : α → ProbedPath W np} {z : α → ℂ} (hf : Measurable f)
    (hz : Measurable z) :
    Measurable fun a => closedK b E s T h τ m W (z a) (f a) := by
  have hω : Measurable fun a => (f a).1 := measurable_fst.comp hf
  have hV : Measurable fun a => probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m (f a) :=
    (measurable_probeFrame b E W _ τ m).comp hf
  have hinv : Measurable fun a => (1 - z a • physClosingN b E s T h W (f a).1)⁻¹ :=
    measurable_matrix_inv.comp (measurable_matrix_sub measurable_const
      (measurable_matrix_cmul hz (measurable_physClosingN_comp b E s T h hω)))
  have hc : Measurable fun a => ((2 * etaZ b E : ℝ) : ℂ) * Complex.I * z a :=
    measurable_const.mul hz
  unfold closedK
  exact measurable_matrix_sub ((measurable_complexSourceK b E W _ τ m).comp hf)
    (measurable_matrix_cmul hc (measurable_matrix_mul' (measurable_matrix_mul'
      (measurable_matrix_mul' (measurable_matrix_mul' (measurable_matrix_conjTranspose' hV) hinv)
        (measurable_farEmbed ((measurable_closingPairing b E h _).comp hω)))
      ((measurable_scatteringMatrix b E _).comp hω)) hV))

/-- The physical closing map along measurable maps to the path and to `z ∈ ℂ`. -/
theorem measurable_physClosingMap_comp_complex {α : Type*} [MeasurableSpace α] (b E s T h : ℝ)
    {f : α → GrowthPath W} {z : α → ℂ} (hf : Measurable f) (hz : Measurable z) :
    Measurable fun a => physClosingMap b E s T h W (f a) (z a) :=
  measurable_closingMap ((measurable_scatteringMatrix b E _).comp hf)
    (measurable_farEmbed ((measurable_omittedProj b E h _).comp hf))
    (measurable_farEmbed ((measurable_closingPairing b E h _).comp hf)) hz

/-- The closed probe frame along measurable maps to the probed path and the phase. -/
theorem measurable_closedFrame_comp {α : Type*} [MeasurableSpace α] (b E s T h : ℝ)
    (τ m : Fin np → ℝ) {f : α → ProbedPath W np} {z : α → ℂ} (hf : Measurable f)
    (hz : Measurable z) :
    Measurable fun a => closedFrame b E s T h τ m W (z a) (f a) :=
  measurable_matrix_mul' (measurable_matrix_conjTranspose'
    (measurable_physClosingMap_comp_complex b E s T h (measurable_fst.comp hf) hz))
    ((measurable_probeFrame b E W _ τ m).comp hf)

/-- The closed source data along measurable maps to the probed path and the phase. -/
theorem measurable_closedSourceData_comp {α : Type*} [MeasurableSpace α] (b E s T h : ℝ)
    (τ m : Fin np → ℝ) {f : α → ProbedPath W np} {z : α → ℂ} (hf : Measurable f)
    (hz : Measurable z) :
    Measurable fun a => closedSourceData b E s T h τ m W (z a) (f a) := by
  have hω : Measurable fun a => (f a).1 := measurable_fst.comp hf
  have hV := measurable_closedFrame_comp b E s T h τ m hf hz
  have hVs := measurable_matrix_conjTranspose' hV
  have hC := measurable_physClosingMap_comp_complex b E s T h hω hz
  have hS : Measurable fun a => scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ (f a).1 :=
    (measurable_scatteringMatrix b E _).comp hω
  refine measurable_pi_iff.2 fun r => ?_
  fin_cases r
  · exact measurable_closedK_comp b E s T h τ m hf hz
  · exact measurable_matrix_mul' hVs hV
  · exact measurable_matrix_mul' (measurable_matrix_mul' hVs measurable_const) hV
  · exact measurable_matrix_mul' (measurable_matrix_mul' hVs (measurable_matrix_sub
      (measurable_matrix_mul' (measurable_matrix_mul' (measurable_matrix_mul'
        (measurable_matrix_mul' (measurable_matrix_conjTranspose' hC)
          (measurable_matrix_conjTranspose' hS)) measurable_const) hS) hC)
      measurable_const)) hV

/-- **The closed source data are jointly measurable** in the probed path and the phase angle. -/
theorem measurable_closedSourceData (b E s T h : ℝ) (τ m : Fin np → ℝ) (W : ℕ) :
    Measurable fun y : ProbedPath W np × ℝ =>
      closedSourceData b E s T h τ m W (phase y.2) y.1 :=
  measurable_closedSourceData_comp b E s T h τ m measurable_fst
    (measurable_phase.comp measurable_snd)

/-- **The closed integrand is integrable**: `Φ ∘ closedSourceData` under
`probedPathLaw ⊗ phaseLaw`, for every bounded continuous `Φ`. -/
theorem integrable_closedIntegrand (b E s T h : ℝ) (τ m : Fin np → ℝ) (W : ℕ)
    (Φ : BoundedContinuousFunction (SourceData np) ℝ) :
    Integrable (fun y : ProbedPath W np × ℝ =>
      Φ (closedSourceData b E s T h τ m W (phase y.2) y.1))
      ((probedPathLaw W np b).prod phaseLaw) := by
  have hF := measurable_closedSourceData b E s T h τ m W
  have hΦ : Integrable Φ (((probedPathLaw W np b).prod phaseLaw).map
      fun y : ProbedPath W np × ℝ => closedSourceData b E s T h τ m W (phase y.2) y.1) :=
    Φ.integrable _
  exact hΦ.comp_measurable hF

end BlockBand.SourceProcess.PhysApprox
