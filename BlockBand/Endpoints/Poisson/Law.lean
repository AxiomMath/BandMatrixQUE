module

public import BlockBand.Endpoints.Poisson.Binomial
public import BlockBand.Endpoints.LaplaceDetermination
public import BlockBand.Endpoints.LaplaceLimit

/-!
# Existence and uniqueness of the unit Poisson law

The unit-intensity Poisson law on the vague point-measure space exists, as a limit of the
binomial approximants, and is unique, since it is determined by its Laplace functional.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter
open scoped ENNReal Topology

/-- The binomial approximant as a law on the vague state space: the
pushforward of `2n+2` independent uniform points on `(-(n+1), n+1)` under
`x ↦ ∑ j, δ_{x j}`. -/
def binomialLaw (n : ℕ) : ProbabilityMeasure (VaguePointMeasure ℝ) :=
  ⟨(binomialPointLaw n).map finitePointMeasure,
    inferInstance⟩

theorem measurable_finitePointMeasure_binomial (n : ℕ) :
    Measurable (finitePointMeasure : (Fin (binomialCount n) → ℝ) → VaguePointMeasure ℝ) :=
  measurable_finitePointMeasure

theorem binomialLaw_toMeasure (n : ℕ) :
    (binomialLaw n : Measure (VaguePointMeasure ℝ)) =
      (binomialPointLaw n).map finitePointMeasure := rfl

theorem integral_exp_neg_binomialLaw (n : ℕ) (f : CompactlySupportedContinuousMap ℝ ℝ) :
    ∫ ξ, Real.exp (-∫ x, f x ∂ξ.measure) ∂(binomialLaw n : Measure (VaguePointMeasure ℝ)) =
      ∫ x, Real.exp (-∑ j, f (x j)) ∂binomialPointLaw n := by
  rw [binomialLaw_toMeasure, integral_map (measurable_finitePointMeasure_binomial n).aemeasurable]
  · congr 1
    ext x
    rw [integral_finitePointMeasure x f f.continuous]
  · exact (Real.continuous_exp.measurable.comp
      (measurable_coordinate f).neg).aestronglyMeasurable

theorem lintegral_coordinate_binomialLaw_le (n : ℕ) (g : CompactlySupportedContinuousMap ℝ ℝ)
    (hg : ∀ x, 0 ≤ g x) :
    ∫⁻ ξ, ENNReal.ofReal (∫ x, g x ∂ξ.measure)
        ∂(binomialLaw n : Measure (VaguePointMeasure ℝ)) ≤
      ∫⁻ y, ENNReal.ofReal (g y) := by
  rw [binomialLaw_toMeasure, lintegral_map
    (f := fun ξ : VaguePointMeasure ℝ => ENNReal.ofReal (∫ x, g x ∂ξ.measure))
    (ENNReal.measurable_ofReal.comp (measurable_coordinate g))
    (measurable_finitePointMeasure_binomial n)]
  simp_rw [integral_finitePointMeasure _ g g.continuous]
  exact lintegral_sum_binomialPointLaw_le n g g.continuous hg

/-- Existence of a law with the unit Poisson Laplace functional. -/
theorem exists_isUnitPoissonLaw :
    ∃ P : ProbabilityMeasure (VaguePointMeasure ℝ), IsUnitPoissonLaw P := by
  obtain ⟨Q, hQ⟩ := exists_law_of_tendsto_laplace binomialLaw
    (fun g hg => ⟨∫⁻ y, ENNReal.ofReal (g y),
      (g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport).lintegral_lt_top.ne,
      fun n => lintegral_coordinate_binomialLaw_le n g hg⟩)
    (fun f => Real.exp (-∫ y, (1 - Real.exp (-f y))))
    (fun f _ => by
      simp_rw [integral_exp_neg_binomialLaw]
      exact tendsto_integral_exp_neg_sum_binomialPointLaw f)
  exact ⟨Q, hQ⟩

/-- **Unit Poisson law: existence and uniqueness** on the
`VaguePointMeasure ℝ` with its vague Borel σ-algebra. This is the clause
`∃! poissonLaw, IsUnitPoissonLaw poissonLaw` of `HasCriticalEndpoints`
(the endpoints theorem); it uses no external input. -/
theorem existsUnique_isUnitPoissonLaw :
    ∃! P : ProbabilityMeasure (VaguePointMeasure ℝ), IsUnitPoissonLaw P := by
  obtain ⟨P, hP⟩ := exists_isUnitPoissonLaw
  exact ⟨P, hP, fun Q hQ => isUnitPoissonLaw_unique hQ hP⟩

end BlockBand.Endpoints
