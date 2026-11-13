module

public import BlockBand.Critical.GlobalSource.Assembly

/-!
# Global Gaussian source: characteristic tests and Lévy continuity

* `cosTest`, `sinTest`, `charFun_eq_cos_sin`: real and imaginary parts of `exp(i⟪x,u⟫)`.
* `exists_tendsto_of_forall_integral_tendsto`: abstract Lévy continuity for a limit functional.
* `norm_charFun_map_sub_le`: coupling bound `|φ_X(u) - φ_Y(u)| ≤ E min(2, ‖u‖‖X - Y‖)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.GlobalSource

open MeasureTheory ProbabilityTheory Filter Topology Complex
open scoped InnerProductSpace RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- `|cos a - cos b| ≤ 2`. -/
theorem dist_cos_le_two (a b : ℝ) : dist (Real.cos a) (Real.cos b) ≤ 2 := by
  rw [Real.dist_eq]
  have h1 := Real.abs_cos_le_one a
  have h2 := Real.abs_cos_le_one b
  calc |Real.cos a - Real.cos b| ≤ |Real.cos a| + |Real.cos b| := abs_sub _ _
    _ ≤ 2 := by linarith

/-- `|sin a - sin b| ≤ 2`. -/
theorem dist_sin_le_two (a b : ℝ) : dist (Real.sin a) (Real.sin b) ≤ 2 := by
  rw [Real.dist_eq]
  have h1 := Real.abs_sin_le_one a
  have h2 := Real.abs_sin_le_one b
  calc |Real.sin a - Real.sin b| ≤ |Real.sin a| + |Real.sin b| := abs_sub _ _
    _ ≤ 2 := by linarith

/-- The real part `x ↦ cos⟪x, u⟫` of the characteristic test `exp(i⟪x, u⟫)`, as a bounded
continuous function. -/
def cosTest (u : E) : BoundedContinuousFunction E ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨fun x => Real.cos ⟪x, u⟫, by fun_prop⟩ 2
    fun x y => dist_cos_le_two _ _

/-- The imaginary part `x ↦ sin⟪x, u⟫` of the characteristic test `exp(i⟪x, u⟫)`. -/
def sinTest (u : E) : BoundedContinuousFunction E ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨fun x => Real.sin ⟪x, u⟫, by fun_prop⟩ 2
    fun x y => dist_sin_le_two _ _

omit [FiniteDimensional ℝ E] in
/-- `φ_μ(u) = ∫ cos⟪x,u⟫ dμ + i ∫ sin⟪x,u⟫ dμ` for finite `μ`. -/
theorem charFun_eq_cos_sin (μ : Measure E) [IsFiniteMeasure μ] (u : E) :
    charFun μ u = ((∫ x, cosTest u x ∂μ : ℝ) : ℂ) + ((∫ x, sinTest u x ∂μ : ℝ) : ℂ) * I := by
  rw [charFun_apply]
  have hpt : ∀ x : E, exp (⟪x, u⟫ * I) =
      ((cosTest u x : ℝ) : ℂ) + ((sinTest u x : ℝ) : ℂ) * I := by
    intro x
    rw [exp_mul_I]
    simp [cosTest, sinTest, Complex.ofReal_cos, Complex.ofReal_sin]
  simp_rw [hpt]
  rw [integral_add ((cosTest u).integrable μ).ofReal (((sinTest u).integrable μ).ofReal.mul_const _),
    integral_mul_const, integral_complex_ofReal, integral_complex_ofReal]

/-- **Abstract Lévy continuity** (Mathlib `isTightMeasureSet_of_tendsto_charFun` plus
`exists_tendsto_of_tight_of_tendsto_charFun`). Let `μ_j` be probability measures on a
finite-dimensional real inner product space and `L` a functional on bounded continuous real tests
with `∫ Φ dμ_j → L Φ` for every `Φ`. If `u ↦ L(cos⟪·,u⟫) + i L(sin⟪·,u⟫)` is continuous at `0`,
then `μ_j → ρ` weakly for a probability measure `ρ` with `∫ Φ dρ = L Φ` for every `Φ`. Used to
build the `M`-sampled limit law `ρ_M` of `IsGlobalProbeLaw` as a measure. -/
theorem exists_tendsto_of_forall_integral_tendsto {μ : ℕ → ProbabilityMeasure E}
    {L : BoundedContinuousFunction E ℝ → ℝ}
    (hL : ∀ Φ, Tendsto (fun j => ∫ x, Φ x ∂(μ j : Measure E)) atTop (𝓝 (L Φ)))
    (hcont : ContinuousAt (fun u : E => ((L (cosTest u) : ℝ) : ℂ) + ((L (sinTest u) : ℝ) : ℂ) * I) 0) :
    ∃ ρ : ProbabilityMeasure E, Tendsto μ atTop (𝓝 ρ) ∧ ∀ Φ, ∫ x, Φ x ∂(ρ : Measure E) = L Φ := by
  set f : E → ℂ := fun u => ((L (cosTest u) : ℝ) : ℂ) + ((L (sinTest u) : ℝ) : ℂ) * I
  have hf : ∀ u, Tendsto (fun j => charFun (μ j : Measure E) u) atTop (𝓝 (f u)) := by
    intro u
    simp_rw [charFun_eq_cos_sin]
    exact ((continuous_ofReal.tendsto _).comp (hL (cosTest u))).add
      (((continuous_ofReal.tendsto _).comp (hL (sinTest u))).mul_const I)
  have htight : IsTightMeasureSet {(μ n : Measure E) | n} := by
    have h := isTightMeasureSet_of_tendsto_charFun (μ := fun n => (μ n : Measure E)) hcont hf
    convert h using 1
    ext x; simp [Set.mem_range]
  obtain ⟨ρ, hρ, -⟩ := exists_tendsto_of_tight_of_tendsto_charFun htight hf
  refine ⟨ρ, hρ, fun Φ => ?_⟩
  exact tendsto_nhds_unique (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hρ Φ) (hL Φ)

/-- `|e^{ia} - e^{ib}| ≤ min(2, |a - b|)`. -/
theorem norm_exp_mul_I_sub_le (a b : ℝ) :
    ‖exp (a * I) - exp (b * I)‖ ≤ min 2 |a - b| := by
  refine le_min ?_ ?_
  · calc ‖exp (a * I) - exp (b * I)‖ ≤ ‖exp (a * I)‖ + ‖exp (b * I)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_exp_ofReal_mul_I, norm_exp_ofReal_mul_I]; norm_num
  · have h : exp (a * I) - exp (b * I) = exp (b * I) * (exp (I * ((a - b : ℝ) : ℂ)) - 1) := by
      rw [mul_sub, ← Complex.exp_add, mul_one]
      congr 2
      push_cast; ring
    rw [h, norm_mul, norm_exp_ofReal_mul_I, one_mul]
    exact Real.norm_exp_I_mul_ofReal_sub_one_le.trans (le_of_eq (Real.norm_eq_abs _))

/-- **Coupling bound for characteristic functions**: for two random vectors `X, Y` on one
probability space, `|φ_X(u) - φ_Y(u)| ≤ E min(2, ‖u‖ ‖X - Y‖)`. -/
theorem norm_charFun_map_sub_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {X Y : Ω → E} (hX : Measurable X) (hY : Measurable Y) (u : E) :
    ‖charFun (μ.map X) u - charFun (μ.map Y) u‖ ≤ ∫ ω, min 2 (‖u‖ * ‖X ω - Y ω‖) ∂μ := by
  have hc : Continuous fun x : E => exp (⟪x, u⟫ * I) := by fun_prop
  rw [charFun_apply, charFun_apply, integral_map hX.aemeasurable hc.aestronglyMeasurable,
    integral_map hY.aemeasurable hc.aestronglyMeasurable]
  have hiX : Integrable (fun ω => exp (⟪X ω, u⟫ * I)) μ :=
    (integrable_const (1 : ℝ)).mono' (hc.measurable.comp hX).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [norm_exp_ofReal_mul_I])
  have hiY : Integrable (fun ω => exp (⟪Y ω, u⟫ * I)) μ :=
    (integrable_const (1 : ℝ)).mono' (hc.measurable.comp hY).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [norm_exp_ofReal_mul_I])
  rw [← integral_sub hiX hiY]
  refine (norm_integral_le_integral_norm _).trans (integral_mono (hiX.sub hiY).norm ?_ fun ω => ?_)
  · have hm : Measurable fun ω => min 2 (‖u‖ * ‖X ω - Y ω‖) :=
      measurable_const.min (measurable_const.mul (hX.sub hY).norm)
    exact (integrable_const (2 : ℝ)).mono' hm.aestronglyMeasurable (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (by norm_num) (by positivity))]
      exact min_le_left _ _)
  · refine (norm_exp_mul_I_sub_le _ _).trans (min_le_min le_rfl ?_)
    rw [← inner_sub_left, mul_comm]
    exact abs_real_inner_le_norm _ _

end BlockBand.Critical.GlobalSource
