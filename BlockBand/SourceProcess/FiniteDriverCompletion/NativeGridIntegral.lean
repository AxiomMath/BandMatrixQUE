module
public import BlockBand.SourceProcess.FiniteDriverIntegration.FiniteDriverSteps
public import BlockBand.SourceProcess.FiniteDriverCompletion.PredictableRectangle
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The Itô isometry for finite-grid stochastic sums

A `GridPresentation` is a finite time grid on `[0, T]` with coefficients `H_{k,a}` measurable at
the left endpoint `t_k` and square integrable. Its stochastic sum
`Σ_{k,a} H_{k,a}(W_a(t_{k+1}) - W_a(t_k))` satisfies the Itô isometry
`E|Σ|² = Σ_{k,a} (t_{k+1} - t_k) E H_{k,a}²`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.SourceProcess.FiniteDriverCompletion
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators
open BlockBand.SourceProcess.FiniteDriverIntegration
open FiniteIto ContinuousItoCommonRefinement
open PredictableRectangle

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable (μ : Measure S) [IsProbabilityMeasure μ]

/-- A driver step with a past-measurable coefficient has conditional mean zero. -/
theorem driverStep_condExp (s u : ℝ≥0) (a : κ) {H : DriverSample S κ → ℝ}
    (hH : Measurable[commonWienerFiltration S κ s] H)
    (hHL2 : MemLp H 2 (driverLaw (κ := κ) μ)) :
    (driverLaw (κ := κ) μ)[driverStep s u a H | commonWienerFiltration S κ s]
      =ᵐ[driverLaw (κ := κ) μ] 0 := by
  have hi := (hasLaw_driverIncrement μ s u a).memLp (memLp_id_gaussianReal (2 : ℝ≥0))
  have hp := condExp_mul_of_stronglyMeasurable_left hH.stronglyMeasurable
    ((driverStep_memLp μ s u a hH hHL2).integrable (by norm_num)) (hi.integrable (by norm_num))
  filter_upwards [hp, driverIncrement_condExp μ s u a] with x hx hz
  change (driverLaw (κ := κ) μ)[H * driverIncrement s u a |
    commonWienerFiltration S κ s] x = 0
  rw [hx]
  simp only [Pi.mul_apply, hz, Pi.zero_apply, mul_zero]

/-- Every square-integrable past-measurable multiplier is orthogonal to a future driver step. -/
theorem driverStep_temporal_orthogonality (s u : ℝ≥0) (a : κ)
    {A H : DriverSample S κ → ℝ}
    (hA : Measurable[commonWienerFiltration S κ s] A)
    (hAL2 : MemLp A 2 (driverLaw (κ := κ) μ))
    (hH : Measurable[commonWienerFiltration S κ s] H)
    (hHL2 : MemLp H 2 (driverLaw (κ := κ) μ)) :
    ∫ x, A x * driverStep s u a H x ∂driverLaw (κ := κ) μ = 0 := by
  let Y := driverStep s u a H
  have hYL2 := driverStep_memLp μ s u a hH hHL2
  have hprod : Integrable (A * Y) (driverLaw (κ := κ) μ) := hAL2.integrable_mul hYL2
  have hp := condExp_mul_of_stronglyMeasurable_left hA.stronglyMeasurable hprod (hYL2.integrable (by norm_num))
  have hzero : (driverLaw (κ := κ) μ)[A * Y | commonWienerFiltration S κ s]
      =ᵐ[driverLaw (κ := κ) μ] 0 := by
    filter_upwards [hp, driverStep_condExp μ s u a hH hHL2] with x hx hz
    change (driverLaw (κ := κ) μ)[A * Y | commonWienerFiltration S κ s] x =
      A x * (driverLaw (κ := κ) μ)[Y | commonWienerFiltration S κ s] x at hx
    change (driverLaw (κ := κ) μ)[Y | commonWienerFiltration S κ s] x = 0 at hz
    change (driverLaw (κ := κ) μ)[A * Y | commonWienerFiltration S κ s] x = 0
    rw [hx, hz, mul_zero]
  change ∫ x, (A * Y) x ∂driverLaw (κ := κ) μ = 0
  rw [← integral_condExp ((commonWienerFiltration S κ).le s),
    integral_congr_ae hzero]
  simp only [Pi.zero_apply, integral_zero]

/-- A finite-grid presentation with past-measurable coefficients on the horizon `[0, T]`. -/
structure GridPresentation (T : ℝ≥0) where
  steps : ℕ
  grid : TimeGrid steps
  initial_time : grid.time 0 = 0
  terminal_time : grid.time (Fin.last steps) = T
  coeff : Fin steps → κ → DriverSample S κ → ℝ
  adapted : ∀ k a, Measurable[commonWienerFiltration S κ (grid.time k.castSucc)] (coeff k a)
  coeffL2 : ∀ k a, MemLp (coeff k a) 2 (driverLaw (κ := κ) μ)

namespace GridPresentation
variable {μ} {T : ℝ≥0}

/-- The term of one noise direction on one grid interval. -/
def term (d : GridPresentation (κ := κ) μ T) (k : Fin d.steps) (a : κ) : DriverSample S κ → ℝ :=
  driverStep (d.grid.time k.castSucc) (d.grid.step k) a (d.coeff k a)

omit [IsProbabilityMeasure μ] in
theorem term_apply (d : GridPresentation (κ := κ) μ T) (k : Fin d.steps) (a : κ)
    (x : DriverSample S κ) :
    d.term k a x = d.coeff k a x *
      (commonRealBrownian (d.grid.time k.succ) x a - commonRealBrownian (d.grid.time k.castSucc) x a) := by
  unfold term driverStep driverIncrement TimeGrid.step
  rw [add_tsub_cancel_of_le (d.grid.strictMono_time k.castSucc_lt_succ).le]

theorem term_memLp (d : GridPresentation (κ := κ) μ T) (k : Fin d.steps) (a : κ) :
    MemLp (d.term k a) 2 (driverLaw (κ := κ) μ) :=
  driverStep_memLp μ _ _ a (d.adapted k a) (d.coeffL2 k a)

omit [IsProbabilityMeasure μ] in
/-- Earlier stochastic terms are measurable at every later left endpoint. -/
theorem term_measurable_later (d : GridPresentation (κ := κ) μ T)
    {i j : Fin d.steps} (hij : i < j) (a : κ) :
    Measurable[commonWienerFiltration S κ (d.grid.time j.castSucc)] (d.term i a) := by
  have hcoef := (d.adapted i a).mono
    ((commonWienerFiltration S κ).mono
      (d.grid.strictMono_time.monotone (Fin.castSucc_le_castSucc_iff.mpr hij.le))) le_rfl
  have hev (k : Fin (d.steps + 1)) (hkj : k ≤ j.castSucc) :
      Measurable[commonWienerFiltration S κ (d.grid.time j.castSucc)]
        (fun x : DriverSample S κ => commonRealBrownian (d.grid.time k) x a) :=
    ((measurable_pi_apply a).comp (commonRealBrownian_adapted (d.grid.time k))).mono
      ((commonWienerFiltration S κ).mono (d.grid.strictMono_time.monotone hkj)) le_rfl
  have hmeas := hcoef.mul
    ((hev i.succ (Fin.succ_le_castSucc_iff.mpr hij)).sub
      (hev i.castSucc (Fin.castSucc_le_castSucc_iff.mpr hij.le)))
  convert hmeas using 1
  funext x
  exact d.term_apply i a x

/-- Terms on distinct grid intervals are orthogonal. -/
theorem term_cross_time (d : GridPresentation (κ := κ) μ T)
    {i j : Fin d.steps} (hij : i < j) (a b : κ) :
    ∫ x, d.term i a x * d.term j b x ∂driverLaw (κ := κ) μ = 0 :=
  driverStep_temporal_orthogonality μ _ _ b (d.term_measurable_later hij a)
    (d.term_memLp i a) (d.adapted j b) (d.coeffL2 j b)

/-- Terms with distinct time or direction indices have zero cross moment. -/
theorem term_cross (d : GridPresentation (κ := κ) μ T)
    (i j : Fin d.steps × κ) (hij : i ≠ j) :
    ∫ x, d.term i.1 i.2 x * d.term j.1 j.2 x ∂driverLaw (κ := κ) μ = 0 := by
  by_cases ht : i.1 = j.1
  · have ha : i.2 ≠ j.2 := by
      intro h
      exact hij (Prod.ext ht h)
    simpa only [term, ht] using
      driverStep_crossMoment μ (d.grid.time j.1.castSucc) (d.grid.step j.1) ha
        (d.adapted j.1 i.2) (d.adapted j.1 j.2)
  · rcases lt_or_gt_of_ne ht with hlt | hgt
    · exact d.term_cross_time hlt i.2 j.2
    · have he := d.term_cross_time hgt j.2 i.2
      simpa only [mul_comm] using he

/-- The second moment of one term. -/
theorem term_secondMoment (d : GridPresentation (κ := κ) μ T) (k : Fin d.steps) (a : κ) :
    ∫ x, (d.term k a x)^2 ∂driverLaw (κ := κ) μ =
      (d.grid.step k : ℝ) * ∫ x, (d.coeff k a x)^2 ∂driverLaw (κ := κ) μ := by
  have hn : nndist (d.grid.time k.castSucc + d.grid.step k) (d.grid.time k.castSucc) = d.grid.step k := by
    apply NNReal.eq
    rw [coe_nndist, NNReal.dist_eq, NNReal.coe_add, add_sub_cancel_left,
      abs_of_nonneg (NNReal.coe_nonneg _)]
  simpa only [term, hn] using driverStep_secondMoment μ (d.grid.time k.castSucc) (d.grid.step k) a (d.adapted k a) (d.coeffL2 k a)

/-- The finite stochastic sum. -/
def integral (d : GridPresentation (κ := κ) μ T) : DriverSample S κ → ℝ :=
  fun x => ∑ ka : Fin d.steps × κ, d.term ka.1 ka.2 x

theorem integral_memLp (d : GridPresentation (κ := κ) μ T) :
    MemLp d.integral 2 (driverLaw (κ := κ) μ) :=
  memLp_finsetSum _ (fun ka _ => d.term_memLp ka.1 ka.2)

/-- The Itô isometry for the finite stochastic sum. -/
theorem integral_secondMoment (d : GridPresentation (κ := κ) μ T) :
    ∫ x, (d.integral x)^2 ∂driverLaw (κ := κ) μ =
      ∑ ka : Fin d.steps × κ, (d.grid.step ka.1 : ℝ) *
        ∫ x, (d.coeff ka.1 ka.2 x)^2 ∂driverLaw (κ := κ) μ := by
  let Z : Fin d.steps × κ → DriverSample S κ → ℝ := fun ka => d.term ka.1 ka.2
  have hprod (i j : Fin d.steps × κ) : Integrable (fun x => Z i x * Z j x)
      (driverLaw (κ := κ) μ) := (d.term_memLp i.1 i.2).integrable_mul (d.term_memLp j.1 j.2)
  calc
    _ = ∫ x, ∑ i, ∑ j, Z i x * Z j x ∂driverLaw (κ := κ) μ := by
      apply integral_congr_ae
      filter_upwards with x
      change (∑ i, Z i x)^2 = _
      rw [sq, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
    _ = ∑ i, ∑ j, ∫ x, Z i x * Z j x ∂driverLaw (κ := κ) μ := by
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
      · simpa only [Z, pow_two] using d.term_secondMoment i.1 i.2
      · intro j _ hji
        exact d.term_cross i j hji.symm
      · simp

/-- The `L²` class of the finite stochastic sum. -/
def integralLp (d : GridPresentation (κ := κ) μ T) : Lp ℝ 2 (driverLaw (κ := κ) μ) :=
  d.integral_memLp.toLp d.integral

end GridPresentation
end BlockBand.SourceProcess.FiniteDriverCompletion
