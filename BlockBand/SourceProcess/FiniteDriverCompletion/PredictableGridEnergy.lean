module
public import BlockBand.SourceProcess.FiniteDriverCompletion.RefinedGridIntegral

/-!
# Predictable classes of grid presentations

The predictable class `predictableFamily` of a grid presentation, with one step function per noise
direction, has squared norm `Σ_a ∫ dt E H_a(t)²`, which equals the second moment of the finite
stochastic sum; it is unchanged under contiguous refinement.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.SourceProcess.FiniteDriverCompletion
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open FiniteIto ContinuousItoCommonRefinement PredictableRectangle

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {μ : Measure S} [IsProbabilityMeasure μ]

/-- The real finite noise-family norm is the Hilbert sum of predictable energies. -/
abbrev PredictableFamily (T : ℝ≥0) :=
  PiLp 2 (fun _ : κ => PredictableL2 (enlargedPredictableFiltration (S := S) (κ := κ))
    T (driverLaw (κ := κ) μ))

/-- The squared norm of an `L²` class is the integral of the square of its representative. -/
theorem norm_sq_toLp {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {f : Ω → ℝ} (hf : MemLp f 2 ν) : ‖hf.toLp f‖^2 = ∫ x, (f x)^2 ∂ν := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp only [hx, Real.inner_apply, pow_two]

namespace GridPresentation
variable {T : ℝ≥0}

def predictableFunction (d : GridPresentation (κ := κ) μ T) (a : κ) : ℝ × DriverSample S κ → ℝ :=
  fun x => ∑ k, coefficientRectangle (d.grid.time k.castSucc) (d.grid.time k.succ) (d.coeff k a) x

theorem predictableFunction_memLp (d : GridPresentation (κ := κ) μ T) (a : κ) :
    MemLp (d.predictableFunction a) 2 (timeProbMeasure T (driverLaw (κ := κ) μ)) :=
  memLp_finsetSum _ (fun k _ => memLp_coefficientRectangle T _ _ (d.coeffL2 k a))

/-- The predictable class of the step function of one noise direction. -/
def scalarPredictable (d : GridPresentation (κ := κ) μ T) (a : κ) :
    PredictableL2 (enlargedPredictableFiltration (S := S) (κ := κ)) T (driverLaw (κ := κ) μ) := by
  let f := d.predictableFunction a
  have hf := d.predictableFunction_memLp a
  refine ⟨hf.toLp f, ?_⟩
  have hp : StronglyMeasurable[predictableSpace enlargedPredictableFiltration] f := by
    have hsum := Finset.stronglyMeasurable_sum Finset.univ (fun k _ =>
      stronglyMeasurable_coefficientRectangle enlargedPredictableFiltration
        (s := d.grid.time k.castSucc) (t := d.grid.time k.succ) (d.adapted k a))
    have heq : (∑ k, coefficientRectangle (d.grid.time k.castSucc)
      (d.grid.time k.succ) (d.coeff k a)) = f := by
      funext x
      rw [Finset.sum_apply]
      rfl
    rw [← heq]
    exact hsum
  exact hp.aestronglyMeasurable.congr hf.coeFn_toLp.symm

theorem scalarPredictable_coeFn (d : GridPresentation (κ := κ) μ T) (a : κ) :
    (((d.scalarPredictable a : PredictableL2 enlargedPredictableFiltration T (driverLaw (κ := κ) μ)) :
      Lp ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ))) : ℝ × DriverSample S κ → ℝ)
      =ᵐ[timeProbMeasure T (driverLaw (κ := κ) μ)] d.predictableFunction a :=
  (d.predictableFunction_memLp a).coeFn_toLp

omit [IsProbabilityMeasure μ] in
/-- Grid rectangles are pointwise disjoint in time. -/
theorem rectangle_mul_eq_zero (d : GridPresentation (κ := κ) μ T) (a : κ)
    {i j : Fin d.steps} (hij : i ≠ j) (x : ℝ × DriverSample S κ) :
    coefficientRectangle (d.grid.time i.castSucc) (d.grid.time i.succ) (d.coeff i a) x *
      coefficientRectangle (d.grid.time j.castSucc) (d.grid.time j.succ) (d.coeff j a) x = 0 := by
  by_cases hi : x.1 ∈ Set.Ioc (d.grid.time i.castSucc : ℝ) (d.grid.time i.succ : ℝ)
  · by_cases hj : x.1 ∈ Set.Ioc (d.grid.time j.castSucc : ℝ) (d.grid.time j.succ : ℝ)
    · rcases lt_or_gt_of_ne hij with hlt | hgt
      · have ht : (d.grid.time i.succ : ℝ) ≤ (d.grid.time j.castSucc : ℝ) := by
          exact_mod_cast d.grid.strictMono_time.monotone (Fin.succ_le_castSucc_iff.mpr hlt)
        exact (not_lt_of_ge (hi.2.trans ht) hj.1).elim
      · have ht : (d.grid.time j.succ : ℝ) ≤ (d.grid.time i.castSucc : ℝ) := by
          exact_mod_cast d.grid.strictMono_time.monotone (Fin.succ_le_castSucc_iff.mpr hgt)
        exact (not_lt_of_ge (hj.2.trans ht) hi.1).elim
    · simp [coefficientRectangle, hi, hj]
  · simp [coefficientRectangle, hi]

/-- The squared norm of the predictable class is the `dt × P` energy of the step function. -/
theorem scalarPredictable_norm_sq (d : GridPresentation (κ := κ) μ T) (a : κ) :
    ‖d.scalarPredictable a‖^2 =
      ∑ k, (d.grid.step k : ℝ) * ∫ x, (d.coeff k a x)^2 ∂driverLaw (κ := κ) μ := by
  change ‖(d.predictableFunction_memLp a).toLp (d.predictableFunction a)‖^2 = _
  rw [norm_sq_toLp]
  let R : Fin d.steps → ℝ × DriverSample S κ → ℝ := fun k =>
    coefficientRectangle (d.grid.time k.castSucc) (d.grid.time k.succ) (d.coeff k a)
  have hr (k : Fin d.steps) : MemLp (R k) 2 (timeProbMeasure T (driverLaw (κ := κ) μ)) :=
    memLp_coefficientRectangle T _ _ (d.coeffL2 k a)
  have hprod (i j : Fin d.steps) : Integrable (fun x => R i x * R j x)
      (timeProbMeasure T (driverLaw (κ := κ) μ)) := (hr i).integrable_mul (hr j)
  calc
    _ = ∫ x, ∑ i, ∑ j, R i x * R j x ∂timeProbMeasure T (driverLaw (κ := κ) μ) := by
      apply integral_congr_ae
      filter_upwards with x
      change (∑ k, R k x)^2 = _
      rw [sq, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
    _ = ∑ i, ∑ j, ∫ x, R i x * R j x ∂timeProbMeasure T (driverLaw (κ := κ) μ) := by
      rw [integral_finsetSum Finset.univ]
      · apply Finset.sum_congr rfl
        intro i _
        rw [integral_finsetSum Finset.univ]
        exact fun j _ => hprod i j
      · exact fun i _ => integrable_finsetSum _ (fun j _ => hprod i j)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single i]
      · simp only [← pow_two]
        change (∫ x, (coefficientRectangle (d.grid.time i.castSucc)
          (d.grid.time i.succ) (d.coeff i a) x)^2
            ∂timeProbMeasure T (driverLaw (κ := κ) μ)) = _
        rw [integral_sq_coefficientRectangle T _ _
          (d.grid.strictMono_time i.castSucc_lt_succ).le
          (by
            calc d.grid.time i.succ ≤ d.grid.time (Fin.last d.steps) :=
                   d.grid.strictMono_time.monotone (Fin.le_last _)
                 _ = T := d.terminal_time)]
        rw [TimeGrid.step, NNReal.coe_sub (d.grid.strictMono_time i.castSucc_lt_succ).le]
      · intro j _ hji
        have hz : (fun x => R i x * R j x) = fun _ => (0 : ℝ) :=
          funext (fun x => d.rectangle_mul_eq_zero a hji.symm x)
        rw [hz, integral_zero]
      · simp

theorem integralLp_norm_sq (d : GridPresentation (κ := κ) μ T) :
    ‖d.integralLp‖^2 = ∑ ka : Fin d.steps × κ, (d.grid.step ka.1 : ℝ) *
      ∫ x, (d.coeff ka.1 ka.2 x)^2 ∂driverLaw (κ := κ) μ :=
  (norm_sq_toLp d.integral_memLp).trans d.integral_secondMoment

/-- The predictable family of a grid presentation. -/
def predictableFamily (d : GridPresentation (κ := κ) μ T) : PredictableFamily (S := S) (κ := κ) (μ := μ) T :=
  WithLp.toLp 2 (fun a => d.scalarPredictable a)

/-- The norm of the predictable family equals the `L²` norm of the stochastic sum. -/
theorem predictableFamily_norm_eq_integralLp (d : GridPresentation (κ := κ) μ T) :
    ‖d.predictableFamily‖ = ‖d.integralLp‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [predictableFamily, PiLp.toLp_apply, scalarPredictable_norm_sq]
  rw [d.integralLp_norm_sq, Fintype.sum_prod_type,
    Finset.sum_comm]

/-- Predictable classes are unchanged by a contiguous refinement. -/
theorem scalarPredictable_pullback (d : GridPresentation (κ := κ) μ T) {n : ℕ}
    {fine : TimeGrid n} (r : ContiguousGridRefinement d.grid fine) (a : κ) :
    (d.pullback r).scalarPredictable a = d.scalarPredictable a := by
  apply (predictableL2_eq_iff_ae_eq _ _).2
  filter_upwards [(d.pullback r).scalarPredictable_coeFn a,
    d.scalarPredictable_coeFn a] with x hx hy
  rw [hx, hy]
  exact PredictableRectangle.ContiguousGridRefinement.sum_coefficientRectangle_pullback
    r (fun k => d.coeff k a) x

theorem predictableFamily_pullback (d : GridPresentation (κ := κ) μ T) {n : ℕ}
    {fine : TimeGrid n} (r : ContiguousGridRefinement d.grid fine) :
    (d.pullback r).predictableFamily = d.predictableFamily := by
  apply PiLp.ext
  intro a
  change (d.pullback r).scalarPredictable a = d.scalarPredictable a
  exact d.scalarPredictable_pullback r a

end GridPresentation
end BlockBand.SourceProcess.FiniteDriverCompletion
