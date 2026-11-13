module

public import BlockBand.Window.Count.SharperFreshCount

/-!
# `GueSpectralLpGradient` from `GaussianLpGradient` and a deterministic trace gradient

* `gueMeasure_eq_map`: `gueMeasure (Fin W) t` is the image of the standard real Gaussian
  product `gaussianProduct 1` on `((Fin W × Fin W) × Fin 2) → ℝ` under the coordinate map
  `gueCoordMap W t x = gueSample t (circularBrownianCoordinates x)` (definitional, by
  `Measure.map_map`).
* `SpectralCoordinateGradient` — the remaining **deterministic** statement (matrix
  calculus, no probability): for every `C^1` `f` with bounded `f'`, the complex function
  `x ↦ Tr f(gueCoordMap W t x + F)` is `C^1` and its weighted gradient norm with unit
  covariances is `(t · Tr f'(·)^2)^{1/2}`. This is the trace-derivative identity
  `D Tr f(M)[K] = Re Tr(f'(M) K)` together with
  `Σ_{a,b,k} |Tr(G ∂_{abk} H)|^2 = t Tr G^2` for Hermitian `G`. Not an assumption of any
  finished result.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Window.Count

open MeasureTheory ProbabilityTheory
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess
open scoped ENNReal NNReal

/-- Real Gaussian coordinates of `GUE_W(t)`: `x ↦ √(t/2)(X + X*)`, `X = (x_{·,0} + i x_{·,1})/√2`. -/
def gueCoordMap (W : ℕ) (t : ℝ≥0) (x : ((Fin W × Fin W) × Fin 2) → ℝ) :
    Matrix (Fin W) (Fin W) ℂ :=
  gueSample t (circularBrownianCoordinates x)

theorem continuous_gueCoordMap (W : ℕ) (t : ℝ≥0) : Continuous (gueCoordMap W t) :=
  (continuous_gueSample' t).comp continuous_circularBrownianCoordinates'

theorem gueMeasure_eq_map (W : ℕ) (t : ℝ≥0) :
    gueMeasure (Fin W) t =
      (gaussianProduct (fun _ : ((Fin W × Fin W) × Fin 2) => (1 : ℝ≥0))).map (gueCoordMap W t) := by
  unfold gueMeasure commonCircularIncrementLaw gaussianProduct gueCoordMap
  rw [Measure.map_map (continuous_gueSample' t).measurable
    continuous_circularBrownianCoordinates'.measurable]
  rfl

/-- **Deterministic trace gradient in GUE coordinates (remaining obligation 2').** For every
`W ≥ 1`, `t ≥ 0`, Hermitian `F` and `C^1` `f` with bounded `f'`, the complex function
`φ(x) = Tr f(gueCoordMap W t x + F)` on `((Fin W × Fin W) × Fin 2) → ℝ` is `C^1`, and
`(Σ_i |∂_i φ(x)|^2)^{1/2} = (t · Tr f'(gueCoordMap W t x + F)^2)^{1/2}` at every `x`.
Pure matrix calculus. Not an assumption of any finished result. -/
def SpectralCoordinateGradient : Prop :=
  ∀ (W : ℕ), 0 < W → ∀ (t : ℝ≥0) (F : Matrix (Fin W) (Fin W) ℂ), F.IsHermitian →
    ∀ f : ℝ → ℝ, ContDiff ℝ 1 f → (∃ B : ℝ, ∀ x, |deriv f x| ≤ B) →
      ContDiff ℝ 1 (fun x => (spectralSum f (gueCoordMap W t x + F) : ℂ)) ∧
      ∀ x, weightedGradientNorm (fun _ => (1 : ℝ≥0))
          (fun x => (spectralSum f (gueCoordMap W t x + F) : ℂ)) x =
        Real.sqrt (t * spectralSum (fun y => deriv f y ^ 2) (gueCoordMap W t x + F))

/-- **Probabilistic transfer.** `Inputs.GaussianLpGradient` (one absolute `C`, factor `√p`)
and the deterministic `SpectralCoordinateGradient` give `GueSpectralLpGradient` with the
same `C`. Law: `gueMeasure (Fin W) (c/W)` as the image of the real Gaussian product. -/
theorem gueSpectralLpGradient_of (hLp : GaussianLpGradient)
    (hD : SpectralCoordinateGradient) : GueSpectralLpGradient := by
  obtain ⟨C, hC, hL⟩ := hLp
  refine ⟨C, hC.le, ?_⟩
  intro p hp c hc W hW F hF f hf hfB hdB
  obtain ⟨B, hB⟩ := hfB
  set t : ℝ≥0 := Real.toNNReal (c / W) with htdef
  have ht : (t : ℝ) = c / W := Real.coe_toNNReal _ (by positivity)
  set μ0 := gaussianProduct (fun _ : ((Fin W × Fin W) × Fin 2) => (1 : ℝ≥0)) with hμ0
  have hprob : IsProbabilityMeasure μ0 := by rw [hμ0]; unfold gaussianProduct; infer_instance
  obtain ⟨hC1, hgradEq⟩ := hD W hW t F hF f hf hdB
  have hadd : Measurable (fun A : Matrix (Fin W) (Fin W) ℂ => A + F) := measurable_id.add_const _
  have hgm : Measurable (fun A : Matrix (Fin W) (Fin W) ℂ => spectralSum f (A + F)) :=
    (measurable_spectralSum hf.continuous.measurable).comp hadd
  have hΦ : Measurable (gueCoordMap W t) := (continuous_gueCoordMap W t).measurable
  set fc : ((Fin W × Fin W) × Fin 2 → ℝ) → ℂ :=
    fun x => (spectralSum f (gueCoordMap W t x + F) : ℂ) with hfc
  have hfcm : Measurable fc := Complex.measurable_ofReal.comp (hgm.comp hΦ)
  have hmem : MemLp fc (ENNReal.ofReal p) μ0 := by
    refine MemLp.of_bound hfcm.aestronglyMeasurable ((W : ℝ) * |B|)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [hfc, Complex.norm_real, Real.norm_eq_abs]
    simpa using abs_spectralSum_le hB (gueCoordMap W t x + F)
  have key := hL p hp ((Fin W × Fin W) × Fin 2) (fun _ => (1 : ℝ≥0)) fc hC1 hmem
  -- rewrite the goal on the coordinate space
  rw [gueMeasure_eq_map W t]
  have hI : (∫ A', spectralSum f (A' + F) ∂(μ0.map (gueCoordMap W t))) =
      ∫ x, spectralSum f (gueCoordMap W t x + F) ∂μ0 :=
    integral_map hΦ.aemeasurable hgm.aestronglyMeasurable
  rw [hI]
  have hSm : Measurable (fun A : Matrix (Fin W) (Fin W) ℂ =>
      Real.sqrt (c / W * spectralSum (fun x => deriv f x ^ 2) (A + F))) :=
    (((measurable_spectralSum ((measurable_deriv _).pow_const 2)).comp hadd).const_mul _).sqrt
  rw [eLpNorm_map_measure (hgm.sub_const _).aestronglyMeasurable hΦ.aemeasurable,
    eLpNorm_map_measure hSm.aestronglyMeasurable hΦ.aemeasurable]
  have hlhs : eLpNorm ((fun A => spectralSum f (A + F) -
        ∫ x, spectralSum f (gueCoordMap W t x + F) ∂μ0) ∘ gueCoordMap W t) (ENNReal.ofReal p) μ0 =
      eLpNorm (fun x => fc x - ∫ y, fc y ∂μ0) (ENNReal.ofReal p) μ0 := by
    refine eLpNorm_congr_norm_ae ((hgm.comp hΦ).sub_const _).aestronglyMeasurable
      (hfcm.sub_const _).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [hfc, integral_complex_ofReal, ← Complex.ofReal_sub, Complex.norm_real]
    rfl
  have hrhs : weightedGradientNorm (fun _ => (1 : ℝ≥0)) fc =
      (fun A => Real.sqrt (c / W * spectralSum (fun x => deriv f x ^ 2) (A + F))) ∘
        gueCoordMap W t := by
    funext x
    rw [hfc, hgradEq x, ht]
    rfl
  rw [hlhs, ← hrhs]
  exact key

end BlockBand.Window.Count
