module

public import BlockBand.SourceProcess.CommonMatrixBrownian
public import BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousItoPredictableLambdaSystemClosure
public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Enlarged-past finite-driver stochastic steps

The driver space is an old state `S` with law `μ` together with a finite family of independent
Wiener paths indexed by `κ`. A future increment of any coordinate is independent of the enlarged
past, so a step `H(W_a(u) - W_a(s))` with an `F_s`-measurable square-integrable coefficient has
conditional mean zero, second moment `(u - s) E H²`, and steps in distinct directions are
orthogonal; this gives the Itô isometry for one finite-driver step.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.SourceProcess.FiniteDriverIntegration
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

abbrev DriverSample (S κ : Type*) := S × (κ → CanonicalWienerPath)

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable (μ : Measure S) [IsProbabilityMeasure μ]

def driverLaw : Measure (DriverSample S κ) := μ.prod (commonWienerLaw κ)
instance driverLaw_probability : IsProbabilityMeasure (driverLaw (κ := κ) μ) := by
  unfold driverLaw
  infer_instance

/-- The enlarged driver filtration as a continuous-time filtration. -/
def enlargedPredictableFiltration : ContinuousIto.ContinuousFiltration (DriverSample S κ) where
  space := commonWienerFiltration S κ
  mono_space := (commonWienerFiltration S κ).mono'
  le_ambient := (commonWienerFiltration S κ).le

/-- Predictable rectangles are dense for the enlarged filtration. -/
theorem enlargedPredictable_dense (T : ℝ≥0) :
    Dense (ContinuousIto.elementaryPredictableSubmodule
      (enlargedPredictableFiltration (S := S) (κ := κ)) T (driverLaw (κ := κ) μ) :
      Set (ContinuousIto.PredictableL2 (enlargedPredictableFiltration (S := S) (κ := κ))
        T (driverLaw (κ := κ) μ))) :=
  ContinuousItoPredictableLambdaSystemClosure.elementaryPredictableSubmodule_dense
    enlargedPredictableFiltration T (driverLaw (κ := κ) μ)

def driverIncrement (s u : ℝ≥0) (a : κ) (x : DriverSample S κ) : ℝ :=
  commonRealBrownian (s + u) x a - commonRealBrownian s x a

omit [Fintype κ] in
theorem measurable_driverIncrement (s u : ℝ≥0) (a : κ) :
    Measurable (driverIncrement (S := S) s u a) := by
  unfold driverIncrement commonRealBrownian
  exact ((ContinuousMap.measurable_eval (s + u)).comp
    ((measurable_pi_apply a).comp measurable_snd)).sub
    ((ContinuousMap.measurable_eval s).comp ((measurable_pi_apply a).comp measurable_snd))

theorem hasLaw_driverIncrement (s u : ℝ≥0) (a : κ) :
    HasLaw (driverIncrement (S := S) s u a)
      (gaussianReal 0 (nndist (s + u) s)) (driverLaw (κ := κ) μ) :=
  (commonRealBrownian_isBrownian μ a).toIsPreBrownianReal.hasLaw_sub (s + u) s

/-- The increments of the coordinates over one interval are jointly independent. -/
theorem driverIncrement_iIndepFun (s u : ℝ≥0) :
    iIndepFun (driverIncrement (S := S) s u) (driverLaw (κ := κ) μ) := by
  apply (iIndepFun_iff_hasLaw_pi_pi (hasLaw_driverIncrement μ s u)).2
  exact hasLaw_commonRealBrownian_increment μ s (s + u)

/-- Every future coordinate increment is independent of the enlarged past. -/
theorem driverIncrement_independent_past (s u : ℝ≥0) (a : κ) :
    IndepFun (driverIncrement (S := S) s u a)
      (fun x : DriverSample S κ => (x.1, commonWienerPast s x.2))
      (driverLaw (κ := κ) μ) := by
  have h := (commonWienerFuture_independent_old_past μ s).comp
    ((measurable_pi_apply u).comp (measurable_pi_apply a)) measurable_id
  exact h

/-- Every enlarged-past measurable coefficient is independent of a future increment. -/
theorem pastCoefficient_independent_increment (s u : ℝ≥0) (a : κ)
    {H : DriverSample S κ → ℝ} (hH : Measurable[commonWienerFiltration S κ s] H) :
    IndepFun H (driverIncrement (S := S) s u a) (driverLaw (κ := κ) μ) := by
  exact indep_of_indep_of_le (driverIncrement_independent_past μ s u a).symm
    (measurable_iff_comap_le.1 hH)
    (measurable_iff_comap_le.1 (comap_measurable (driverIncrement (S := S) s u a)))

theorem driverIncrement_mean (s u : ℝ≥0) (a : κ) :
    ∫ x, driverIncrement (S := S) s u a x ∂driverLaw (κ := κ) μ = 0 := by
  rw [(hasLaw_driverIncrement μ s u a).integral_eq, integral_id_gaussianReal]

theorem driverIncrement_secondMoment (s u : ℝ≥0) (a : κ) :
    ∫ x, (driverIncrement (S := S) s u a x)^2 ∂driverLaw (κ := κ) μ =
      (nndist (s + u) s : ℝ) := by
  have hv := (hasLaw_driverIncrement μ s u a).variance_eq
  rw [variance_eq_integral (measurable_driverIncrement s u a).aemeasurable,
    driverIncrement_mean μ s u a, variance_id_gaussianReal] at hv
  simpa using hv

/-- A future increment has conditional mean zero given the enlarged past. -/
theorem driverIncrement_condExp (s u : ℝ≥0) (a : κ) :
    (driverLaw (κ := κ) μ)[driverIncrement (S := S) s u a |
      commonWienerFiltration S κ s] =ᵐ[driverLaw (κ := κ) μ] 0 := by
  have hc := condExp_indep_eq
    (measurable_driverIncrement (S := S) s u a).comap_le
    ((commonWienerFiltration S κ).le s)
    (comap_measurable (driverIncrement (S := S) s u a)).stronglyMeasurable
    (driverIncrement_independent_past μ s u a)
  rw [driverIncrement_mean μ s u a] at hc
  exact hc

/-- The scalar stochastic step `H(W_a(u) - W_a(s))`. -/
def driverStep (s u : ℝ≥0) (a : κ) (H : DriverSample S κ → ℝ) : DriverSample S κ → ℝ :=
  fun x => H x * driverIncrement s u a x

/-- A step with a square-integrable past coefficient is square integrable. -/
theorem driverStep_memLp (s u : ℝ≥0) (a : κ) {H : DriverSample S κ → ℝ}
    (hH : Measurable[commonWienerFiltration S κ s] H)
    (hHL2 : MemLp H 2 (driverLaw (κ := κ) μ)) :
    MemLp (driverStep s u a H) 2 (driverLaw (κ := κ) μ) := by
  have hInd := (pastCoefficient_independent_increment μ s u a hH).comp
    (by fun_prop : Measurable fun z : ℝ => z^2)
    (by fun_prop : Measurable fun z : ℝ => z^2)
  have hIL2 := (hasLaw_driverIncrement μ s u a).memLp (memLp_id_gaussianReal (2 : ℝ≥0))
  have hInt := hInd.integrable_mul hHL2.integrable_sq hIL2.integrable_sq
  apply (memLp_two_iff_integrable_sq
    (((hH.mono ((commonWienerFiltration S κ).le s) le_rfl).mul
      (measurable_driverIncrement s u a)).aestronglyMeasurable)).2
  apply hInt.congr
  filter_upwards with x
  simp only [Function.comp_def, Pi.mul_apply]
  ring

/-- The second moment of a step is `(u - s) E H²`. -/
theorem driverStep_secondMoment (s u : ℝ≥0) (a : κ) {H : DriverSample S κ → ℝ}
    (hH : Measurable[commonWienerFiltration S κ s] H)
    (hHL2 : MemLp H 2 (driverLaw (κ := κ) μ)) :
    ∫ x, (driverStep s u a H x)^2 ∂driverLaw (κ := κ) μ =
      (nndist (s + u) s : ℝ) * ∫ x, (H x)^2 ∂driverLaw (κ := κ) μ := by
  have hi := (pastCoefficient_independent_increment μ s u a hH).comp
    (by fun_prop : Measurable fun z : ℝ => z^2)
    (by fun_prop : Measurable fun z : ℝ => z^2)
  have hHm : AEStronglyMeasurable (fun x => (H x)^2) (driverLaw (κ := κ) μ) := hHL2.integrable_sq.aestronglyMeasurable
  have hIm : AEStronglyMeasurable (fun x => (driverIncrement (S := S) s u a x)^2) (driverLaw (κ := κ) μ) :=
    ((measurable_driverIncrement (S := S) s u a).pow_const 2).aestronglyMeasurable
  have he := hi.integral_fun_mul_eq_mul_integral hHm hIm
  simp only [Function.comp_def] at he
  calc
    _ = ∫ x, (H x)^2 * (driverIncrement (S := S) s u a x)^2 ∂driverLaw (κ := κ) μ := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [driverStep]
      ring
    _ = _ := by rw [he, driverIncrement_secondMoment μ s u a, mul_comm]

/-- Simultaneous distinct real noise directions have zero joint increment moment. -/
theorem driverIncrement_crossMoment (s u : ℝ≥0) {a b : κ} (hab : a ≠ b) :
    ∫ x, driverIncrement (S := S) s u a x * driverIncrement s u b x
      ∂driverLaw (κ := κ) μ = 0 := by
  rw [((driverIncrement_iIndepFun μ s u).indepFun hab).integral_fun_mul_eq_mul_integral
    (measurable_driverIncrement s u a).aestronglyMeasurable
    (measurable_driverIncrement s u b).aestronglyMeasurable,
    driverIncrement_mean μ s u a, zero_mul]

/-- Steps over the same interval in distinct directions are orthogonal, for any
past-measurable coefficients. -/
theorem driverStep_crossMoment (s u : ℝ≥0) {a b : κ} (hab : a ≠ b)
    {H K : DriverSample S κ → ℝ}
    (hH : Measurable[commonWienerFiltration S κ s] H)
    (hK : Measurable[commonWienerFiltration S κ s] K) :
    ∫ x, driverStep s u a H x * driverStep s u b K x
      ∂driverLaw (κ := κ) μ = 0 := by
  let F : (κ → ℝ≥0 → ℝ) → ℝ := fun f => f a u * f b u
  have hF : Measurable F := by
    unfold F
    fun_prop
  have hp : IndepFun (fun x : DriverSample S κ => H x * K x)
      (fun x => commonWienerFuture s x.2) (driverLaw (κ := κ) μ) :=
    indep_of_indep_of_le (commonWienerFuture_independent_old_past μ s).symm
      (measurable_iff_comap_le.1 (hH.mul hK))
      (measurable_iff_comap_le.1 (comap_measurable (fun x : DriverSample S κ => commonWienerFuture s x.2)))
  have hi := hp.comp measurable_id hF
  have hHm : AEStronglyMeasurable (fun x => H x * K x) (driverLaw (κ := κ) μ) := ((hH.mul hK).mono ((commonWienerFiltration S κ).le s) le_rfl).aestronglyMeasurable
  have hIm : AEStronglyMeasurable (fun x => driverIncrement (S := S) s u a x * driverIncrement s u b x) (driverLaw (κ := κ) μ) := ((measurable_driverIncrement (S := S) s u a).mul
    (measurable_driverIncrement s u b)).aestronglyMeasurable
  have he := hi.integral_fun_mul_eq_mul_integral hHm hIm
  change (∫ x, (H x * K x) *
    (driverIncrement (S := S) s u a x * driverIncrement s u b x) ∂driverLaw (κ := κ) μ) =
    (∫ x, H x * K x ∂driverLaw (κ := κ) μ) *
      (∫ x, driverIncrement (S := S) s u a x * driverIncrement s u b x
        ∂driverLaw (κ := κ) μ) at he
  calc
    _ = ∫ x, (H x * K x) *
      (driverIncrement (S := S) s u a x * driverIncrement s u b x)
        ∂driverLaw (κ := κ) μ := by
      apply integral_congr_ae
      filter_upwards with x
      unfold driverStep
      ring
    _ = _ := by rw [he, driverIncrement_crossMoment μ s u hab, mul_zero]

/-- The finite-driver step: the sum of the steps over all noise directions. -/
def finiteDriverStep (s u : ℝ≥0) (H : κ → DriverSample S κ → ℝ) : DriverSample S κ → ℝ :=
  fun x => ∑ a, driverStep s u a (H a) x

theorem finiteDriverStep_memLp (s u : ℝ≥0) (H : κ → DriverSample S κ → ℝ)
    (hH : ∀ a, Measurable[commonWienerFiltration S κ s] (H a))
    (hHL2 : ∀ a, MemLp (H a) 2 (driverLaw (κ := κ) μ)) :
    MemLp (finiteDriverStep s u H) 2 (driverLaw (κ := κ) μ) := by
  exact memLp_finsetSum _ (fun a _ => driverStep_memLp μ s u a (hH a) (hHL2 a))

/-- The Itô isometry for one finite-driver step with a past-measurable coefficient vector. -/
theorem finiteDriverStep_secondMoment (s u : ℝ≥0) (H : κ → DriverSample S κ → ℝ)
    (hH : ∀ a, Measurable[commonWienerFiltration S κ s] (H a))
    (hHL2 : ∀ a, MemLp (H a) 2 (driverLaw (κ := κ) μ)) :
    ∫ x, (finiteDriverStep s u H x)^2 ∂driverLaw (κ := κ) μ =
      ∑ a, (nndist (s + u) s : ℝ) * ∫ x, (H a x)^2 ∂driverLaw (κ := κ) μ := by
  let Z : κ → DriverSample S κ → ℝ := fun a => driverStep s u a (H a)
  have hz (a : κ) : MemLp (Z a) 2 (driverLaw (κ := κ) μ) :=
    driverStep_memLp μ s u a (hH a) (hHL2 a)
  have hprod (a b : κ) : Integrable (fun x => Z a x * Z b x) (driverLaw (κ := κ) μ) :=
    (hz a).integrable_mul (hz b)
  calc
    _ = ∫ x, ∑ a, ∑ b, Z a x * Z b x ∂driverLaw (κ := κ) μ := by
      apply integral_congr_ae
      filter_upwards with x
      change (∑ a, Z a x)^2 = _
      rw [sq, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
    _ = ∑ a, ∑ b, ∫ x, Z a x * Z b x ∂driverLaw (κ := κ) μ := by
      rw [integral_finsetSum Finset.univ]
      · apply Finset.sum_congr rfl
        intro a _
        rw [integral_finsetSum Finset.univ]
        exact fun b _ => hprod a b
      · exact fun a _ => integrable_finsetSum _ (fun b _ => hprod a b)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_eq_single a]
      · simpa only [Z, pow_two] using driverStep_secondMoment μ s u a (hH a) (hHL2 a)
      · intro b _ hba
        exact driverStep_crossMoment μ s u hba.symm (hH a) (hH b)
      · simp

end BlockBand.SourceProcess.FiniteDriverIntegration
