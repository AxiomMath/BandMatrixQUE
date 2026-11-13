module
public import BlockBand.SourceProcess.Stochastic.Integral.PredictableRaw
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Bounded multiplication operators

Multiplication by a bounded a.e. strongly measurable real function `φ` (`|φ| ≤ C`) as a
continuous linear operator on `L²(ν)` (any measure `ν`); on the scalar predictable space
`PredictableL2 = lpMeas (raw predictable σ-algebra) 2 (dt ⊗ driverLaw μ)` when `φ` is a.e. raw
predictable; and coordinatewise on the predictable family `PredictableFamily T`. This is the
sup-norm multiplier needed for `I_T(H 1_{(a,b]} g) = H (X_b − X_a)`.
-/

namespace BlockBand.SourceProcess.Stochastic.Integral
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.FiniteDriverCompletion

section Generic
variable {α : Type*} [mα : MeasurableSpace α] {ν : Measure α}

theorem memLp_mul_of_bound {φ : α → ℝ} (hφ : AEStronglyMeasurable φ ν) {C : ℝ}
    (hC : ∀ x, |φ x| ≤ C) {f : α → ℝ} (hf : MemLp f 2 ν) :
    MemLp (fun x => φ x * f x) 2 ν :=
  hf.of_le_mul (hφ.mul hf.aestronglyMeasurable) (Eventually.of_forall fun x => by
    rw [norm_mul, Real.norm_eq_abs (φ x)]
    exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _))

/-- The linear map `f ↦ φ f` on `L²(ν)` for a bounded `φ`. -/
def mulL2Linear (φ : α → ℝ) (hφ : AEStronglyMeasurable φ ν) (C : ℝ) (hC : ∀ x, |φ x| ≤ C) :
    Lp ℝ 2 ν →ₗ[ℝ] Lp ℝ 2 ν where
  toFun f := (memLp_mul_of_bound hφ hC (Lp.memLp f)).toLp (fun x => φ x * (f : α → ℝ) x)
  map_add' f g := by
    have hae : (fun x => φ x * ((f + g : Lp ℝ 2 ν) : α → ℝ) x) =ᵐ[ν]
        (fun x => φ x * (f : α → ℝ) x) + (fun x => φ x * (g : α → ℝ) x) := by
      filter_upwards [Lp.coeFn_add f g] with x hx
      simp only [Pi.add_apply, hx, mul_add]
    exact (MemLp.toLp_congr _ ((memLp_mul_of_bound hφ hC (Lp.memLp f)).add
      (memLp_mul_of_bound hφ hC (Lp.memLp g))) hae).trans (MemLp.toLp_add _ _)
  map_smul' c f := by
    have hae : (fun x => φ x * ((c • f : Lp ℝ 2 ν) : α → ℝ) x) =ᵐ[ν]
        c • (fun x => φ x * (f : α → ℝ) x) := by
      filter_upwards [Lp.coeFn_smul c f] with x hx
      simp only [Pi.smul_apply, hx, smul_eq_mul]
      ring
    exact (MemLp.toLp_congr _ ((memLp_mul_of_bound hφ hC (Lp.memLp f)).const_smul c)
      hae).trans (MemLp.toLp_const_smul _ _)

/-- Multiplication by a bounded `φ` on `L²(ν)`, a continuous linear operator. -/
def mulL2 (φ : α → ℝ) (hφ : AEStronglyMeasurable φ ν) (C : ℝ) (hC : ∀ x, |φ x| ≤ C) :
    Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  (mulL2Linear φ hφ C hC).mkContinuous C fun f => by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [MemLp.coeFn_toLp (memLp_mul_of_bound hφ hC (Lp.memLp f))] with x hx
    change ‖((memLp_mul_of_bound hφ hC (Lp.memLp f)).toLp
      (fun x => φ x * (f : α → ℝ) x) : α → ℝ) x‖ ≤ C * ‖(f : α → ℝ) x‖
    rw [hx, norm_mul, Real.norm_eq_abs (φ x)]
    exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)

theorem mulL2_coeFn (φ : α → ℝ) (hφ : AEStronglyMeasurable φ ν) (C : ℝ) (hC : ∀ x, |φ x| ≤ C)
    (f : Lp ℝ 2 ν) :
    (mulL2 φ hφ C hC f : α → ℝ) =ᵐ[ν] fun x => φ x * (f : α → ℝ) x :=
  MemLp.coeFn_toLp (memLp_mul_of_bound hφ hC (Lp.memLp f))

end Generic

section Family
variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {μ : Measure S} {T : ℝ≥0}

theorem mul_mem_lpMeas {φ : ℝ × DriverSample S κ → ℝ}
    (hφ : AEStronglyMeasurable[rawPredictable S κ] φ (timeProbMeasure T (driverLaw (κ := κ) μ)))
    {C : ℝ} (hC : ∀ x, |φ x| ≤ C) (f : ScalarPredictable (κ := κ) μ T) :
    mulL2 φ (MeasureTheory.AEStronglyMeasurable.mono (predictableSpace_le _) hφ) C hC
      (f : Lp ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ)))
      ∈ lpMeas ℝ ℝ (rawPredictable S κ) 2 (timeProbMeasure T (driverLaw (κ := κ) μ)) := by
  rw [mem_lpMeas_iff_aestronglyMeasurable]
  obtain ⟨g, hg, hfg⟩ := lpMeas.aestronglyMeasurable f
  obtain ⟨ψ, hψ, hφψ⟩ := id hφ
  refine ⟨fun x => ψ x * g x, hψ.mul hg, ?_⟩
  filter_upwards [mulL2_coeFn φ
    (MeasureTheory.AEStronglyMeasurable.mono (predictableSpace_le _) hφ) C hC (f : Lp ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ))), hfg, hφψ] with x hx hx' hx''
  rw [hx, hx', hx'']

/-- Multiplication by a bounded a.e. raw predictable `φ` on scalar predictable `L²`. -/
def mulScalar (φ : ℝ × DriverSample S κ → ℝ)
    (hφ : AEStronglyMeasurable[rawPredictable S κ] φ (timeProbMeasure T (driverLaw (κ := κ) μ)))
    (C : ℝ) (hC : ∀ x, |φ x| ≤ C) :
    ScalarPredictable (κ := κ) μ T →L[ℝ] ScalarPredictable (κ := κ) μ T :=
  ((mulL2 φ (MeasureTheory.AEStronglyMeasurable.mono (predictableSpace_le _) hφ) C hC).comp
    (lpMeas ℝ ℝ (rawPredictable S κ) 2 (timeProbMeasure T (driverLaw (κ := κ) μ))).subtypeL).codRestrict
    _ (mul_mem_lpMeas hφ hC)

theorem mulScalar_coeFn (φ : ℝ × DriverSample S κ → ℝ)
    (hφ : AEStronglyMeasurable[rawPredictable S κ] φ (timeProbMeasure T (driverLaw (κ := κ) μ)))
    (C : ℝ) (hC : ∀ x, |φ x| ≤ C) (f : ScalarPredictable (κ := κ) μ T) :
    (((mulScalar φ hφ C hC f : ScalarPredictable (κ := κ) μ T) :
      Lp ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ))) : ℝ × DriverSample S κ → ℝ)
      =ᵐ[timeProbMeasure T (driverLaw (κ := κ) μ)]
      fun x => φ x * ((f : Lp ℝ 2 (timeProbMeasure T (driverLaw (κ := κ) μ))) :
        ℝ × DriverSample S κ → ℝ) x :=
  mulL2_coeFn φ (MeasureTheory.AEStronglyMeasurable.mono (predictableSpace_le _) hφ) C hC _

/-- Coordinatewise multiplication by a bounded a.e. raw predictable `φ` on the predictable
`L²(dt ⊗ driverLaw μ)` family on `(0,T]`. -/
def mulFamily (φ : ℝ × DriverSample S κ → ℝ)
    (hφ : AEStronglyMeasurable[rawPredictable S κ] φ (timeProbMeasure T (driverLaw (κ := κ) μ)))
    (C : ℝ) (hC : ∀ x, |φ x| ≤ C) :
    PredictableFamily (S := S) (κ := κ) (μ := μ) T →L[ℝ]
      PredictableFamily (S := S) (κ := κ) (μ := μ) T :=
  (PiLp.continuousLinearEquiv 2 ℝ _).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun a =>
      (mulScalar φ hφ C hC).comp
        (PiLp.proj 2 (fun _ : κ => ScalarPredictable (κ := κ) μ T) a))

theorem mulFamily_apply (φ : ℝ × DriverSample S κ → ℝ)
    (hφ : AEStronglyMeasurable[rawPredictable S κ] φ (timeProbMeasure T (driverLaw (κ := κ) μ)))
    (C : ℝ) (hC : ∀ x, |φ x| ≤ C) (f : PredictableFamily (S := S) (κ := κ) (μ := μ) T) (a : κ) :
    mulFamily φ hφ C hC f a = mulScalar φ hφ C hC (f a) := rfl

theorem mulFamily_single [DecidableEq κ] (φ : ℝ × DriverSample S κ → ℝ)
    (hφ : AEStronglyMeasurable[rawPredictable S κ] φ (timeProbMeasure T (driverLaw (κ := κ) μ)))
    (C : ℝ) (hC : ∀ x, |φ x| ≤ C) (c : κ) (g : ScalarPredictable (κ := κ) μ T) :
    mulFamily φ hφ C hC (PiLp.single 2 c g) = PiLp.single 2 c (mulScalar φ hφ C hC g) := by
  apply PiLp.ext
  intro b
  rw [mulFamily_apply]
  by_cases hb : b = c
  · subst hb
    simp only [PiLp.single_eq_same]
  · rw [PiLp.single_eq_of_ne 2 hb, PiLp.single_eq_of_ne 2 hb, map_zero]

end Family
end BlockBand.SourceProcess.Stochastic.Integral
