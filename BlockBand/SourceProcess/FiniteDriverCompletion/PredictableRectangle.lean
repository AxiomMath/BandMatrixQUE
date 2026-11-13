module
public import BlockBand.SourceProcess.FiniteDriverCompletion.NativeGridRecovery
public import BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousItoPredictableLambdaSystemClosure
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Predictable coefficient rectangles

A coefficient rectangle `1_{(s,t]}(r) H(ω)` with `H` measurable at time `s` is predictable; if `H`
is square integrable it defines a predictable `L²` class with squared norm `(t - s) E H²`.
Coefficient rectangles telescope over the fine intervals of a contiguous refinement.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.SourceProcess.FiniteDriverCompletion.PredictableRectangle
open scoped NNReal ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.FiniteDriverCompletion.FiniteIto
open BlockBand.SourceProcess.FiniteDriverCompletion.ContinuousItoCommonRefinement
/-- A coefficient supported on the predictable rectangle `(s,t] × Ω`. -/
def coefficientRectangle {Ω : Type*} (s t : ℝ≥0) (H : Ω → ℝ) :
    ℝ × Ω → ℝ :=
  (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ (Set.univ : Set Ω)).indicator
    (fun x => H x.2)

/-- An endpoint-measurable coefficient rectangle is measurable for the predictable
sigma algebra. -/
theorem stronglyMeasurable_coefficientRectangle {Ω : Type*}
    [MeasurableSpace Ω] (ℱ : ContinuousFiltration Ω) {s t : ℝ≥0}
    {H : Ω → ℝ} (hH : @Measurable Ω ℝ (ℱ.space s) (borel ℝ) H) :
    StronglyMeasurable[predictableSpace ℱ] (coefficientRectangle s t H) := by
  apply Measurable.stronglyMeasurable
  intro C hC
  by_cases h0 : (0 : ℝ) ∈ C
  · have hHC : MeasurableSet[ℱ.space s] (H ⁻¹' Cᶜ) := hH hC.compl
    have heq : coefficientRectangle s t H ⁻¹' C =
        (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ (H ⁻¹' Cᶜ))ᶜ := by
      ext x
      by_cases hu : x.1 ∈ Set.Ioc (s : ℝ) (t : ℝ)
      · simp [coefficientRectangle, hu]
      · simp [coefficientRectangle, hu, h0]
    rw [heq]
    exact (measurableSet_predictableRectangle ℱ hHC).compl
  · have hHC : MeasurableSet[ℱ.space s] (H ⁻¹' C) := hH hC
    have heq : coefficientRectangle s t H ⁻¹' C =
        Set.Ioc (s : ℝ) (t : ℝ) ×ˢ (H ⁻¹' C) := by
      ext x
      by_cases hu : x.1 ∈ Set.Ioc (s : ℝ) (t : ℝ)
      · simp [coefficientRectangle, hu]
      · simp [coefficientRectangle, hu, h0]
    rw [heq]
    exact measurableSet_predictableRectangle ℱ hHC

/-- An ambient `L²(P)` coefficient gives an `L²(dt × P)` rectangle. -/
theorem memLp_coefficientRectangle {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [SFinite P] (T s t : ℝ≥0) {H : Ω → ℝ}
    (hH : MemLp H 2 P) :
    MemLp (coefficientRectangle s t H) 2 (timeProbMeasure T P) := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc 0 (T : ℝ))
  have hlift : MemLp (fun x : ℝ × Ω => H x.2) 2 (μ.prod P) :=
    hH.comp_snd μ
  have hset : NullMeasurableSet
      (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ (Set.univ : Set Ω)) (μ.prod P) :=
    (measurableSet_Ioc.prod MeasurableSet.univ).nullMeasurableSet
  exact MemLp.indicator hset hlift

/-- The predictable `L²` class of an arbitrary endpoint-measurable square-integrable
coefficient rectangle. -/
def coefficientRectanglePredictableL2 {Ω : Type*} [MeasurableSpace Ω]
    (ℱ : ContinuousFiltration Ω) (T : ℝ≥0) (P : Measure Ω) [SFinite P]
    {s t : ℝ≥0} (H : Ω → ℝ)
    (hHmeas : @Measurable Ω ℝ (ℱ.space s) (borel ℝ) H)
    (hHLp : MemLp H 2 P) : PredictableL2 ℱ T P := by
  have hmem := memLp_coefficientRectangle T s t hHLp
  refine ⟨hmem.toLp (coefficientRectangle s t H), ?_⟩
  exact (stronglyMeasurable_coefficientRectangle ℱ hHmeas).aestronglyMeasurable.congr
    hmem.coeFn_toLp.symm

/-- The square integral of one coefficient rectangle. -/
theorem integral_sq_coefficientRectangle {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [SFinite P] (T s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (H : Ω → ℝ) :
    ∫ x, (coefficientRectangle s t H x) ^ 2 ∂(timeProbMeasure T P) =
      ((t : ℝ) - (s : ℝ)) * ∫ ω, (H ω) ^ 2 ∂P := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc 0 (T : ℝ))
  have hpoint : (fun x : ℝ × Ω => (coefficientRectangle s t H x) ^ 2) =
      (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ (Set.univ : Set Ω)).indicator
        (fun x => (1 : ℝ) * (H x.2) ^ 2) := by
    funext x
    by_cases hx : x ∈ Set.Ioc (s : ℝ) (t : ℝ) ×ˢ (Set.univ : Set Ω) <;>
      simp [coefficientRectangle, hx]
  rw [hpoint, integral_indicator (measurableSet_Ioc.prod MeasurableSet.univ)]
  change (∫ x in Set.Ioc (s : ℝ) (t : ℝ) ×ˢ (Set.univ : Set Ω),
      (1 : ℝ) * (H x.2) ^ 2 ∂μ.prod P) = _
  rw [show (∫ x in Set.Ioc (s : ℝ) (t : ℝ) ×ˢ (Set.univ : Set Ω),
      (1 : ℝ) * (H x.2) ^ 2 ∂μ.prod P) =
      (∫ _ in Set.Ioc (s : ℝ) (t : ℝ), (1 : ℝ) ∂μ) *
        ∫ ω in (Set.univ : Set Ω), (H ω) ^ 2 ∂P by
    simpa using setIntegral_prod_mul (μ := μ) (ν := P)
      (fun _ : ℝ => (1 : ℝ)) (fun ω : Ω => (H ω) ^ 2)
      (Set.Ioc (s : ℝ) (t : ℝ)) (Set.univ : Set Ω)]
  simp only [integral_const, Measure.real, smul_eq_mul, mul_one, setIntegral_univ]
  have hsub : Set.Ioc (s : ℝ) (t : ℝ) ⊆ Set.Ioc 0 (T : ℝ) := by
    intro x hx
    have htT' : (t : ℝ) ≤ (T : ℝ) := by exact_mod_cast htT
    exact ⟨lt_of_le_of_lt (show (0 : ℝ) ≤ (s : ℝ) from s.2) hx.1,
      hx.2.trans htT'⟩
  rw [Measure.restrict_apply_univ]
  rw [Measure.restrict_apply (measurableSet_Ioc)]
  rw [Set.inter_eq_left.2 hsub]
  simp [hst]

/-- A half-open coefficient rectangle is a coefficient times the difference of two
endpoint Heaviside functions. -/
theorem coefficientRectangle_eq_mul_endpointDifference {Ω : Type*}
    (s t : ℝ≥0) (hst : s ≤ t) (H : Ω → ℝ) (x : ℝ × Ω) :
    coefficientRectangle s t H x = H x.2 *
      ((if x.1 ≤ (t : ℝ) then (1 : ℝ) else 0) -
        if x.1 ≤ (s : ℝ) then (1 : ℝ) else 0) := by
  have hst' : (s : ℝ) ≤ (t : ℝ) := by exact_mod_cast hst
  by_cases hxs : x.1 ≤ (s : ℝ)
  · have hxt : x.1 ≤ (t : ℝ) := hxs.trans hst'
    simp [coefficientRectangle, hxs, hxt, not_lt_of_ge hxs]
  · have hsx : (s : ℝ) < x.1 := lt_of_not_ge hxs
    by_cases hxt : x.1 ≤ (t : ℝ)
    · simp [coefficientRectangle, hsx, hxs, hxt]
    · have htx : (t : ℝ) < x.1 := lt_of_not_ge hxt
      simp [coefficientRectangle, hsx, hxs, hxt]

/-- Over one coarse parent fiber, the pulled-back fine rectangles sum to the coarse rectangle. -/
theorem ContiguousGridRefinement.sum_coefficientRectangle_parentFiber
    {m n : ℕ} {coarse : TimeGrid m} {fine : TimeGrid n}
    (r : ContiguousGridRefinement coarse fine)
    {Ω : Type*} (H : Fin m → Ω → ℝ) (i : Fin m) (x : ℝ × Ω) :
    (∑ k : {k : Fin n // r.toGridRefinement.parent k = i},
      coefficientRectangle (fine.time k.val.castSucc) (fine.time k.val.succ)
        (H i) x) =
      coefficientRectangle (coarse.time i.castSucc) (coarse.time i.succ)
        (H i) x := by
  let F : Fin (n + 1) → ℝ := fun j =>
    if x.1 ≤ (fine.time j : ℝ) then 1 else 0
  calc
    (∑ k : {k : Fin n // r.toGridRefinement.parent k = i},
      coefficientRectangle (fine.time k.val.castSucc) (fine.time k.val.succ)
        (H i) x) =
        ∑ k : {k : Fin n // r.toGridRefinement.parent k = i},
          H i x.2 * (F k.val.succ - F k.val.castSucc) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [coefficientRectangle_eq_mul_endpointDifference]
      exact (fine.strictMono_time k.val.castSucc_lt_succ).le
    _ = H i x.2 * ∑ k : {k : Fin n // r.toGridRefinement.parent k = i},
          (F k.val.succ - F k.val.castSucc) := by
      rw [Finset.mul_sum]
    _ = H i x.2 *
        (F (r.endpointIndex i.succ) - F (r.endpointIndex i.castSucc)) := by
      rw [r.sum_path_increments F i]
    _ = coefficientRectangle (coarse.time i.castSucc) (coarse.time i.succ)
        (H i) x := by
      rw [coefficientRectangle_eq_mul_endpointDifference]
      · simp only [F, r.endpoint_time]
      · exact (coarse.strictMono_time i.castSucc_lt_succ).le

/-- Pointwise invariance of the whole predictable step process under contiguous
pullback. -/
theorem ContiguousGridRefinement.sum_coefficientRectangle_pullback
    {m n : ℕ} {coarse : TimeGrid m} {fine : TimeGrid n}
    (r : ContiguousGridRefinement coarse fine)
    {Ω : Type*} (H : Fin m → Ω → ℝ) (x : ℝ × Ω) :
    (∑ k : Fin n,
      coefficientRectangle (fine.time k.castSucc) (fine.time k.succ)
        (H (r.toGridRefinement.parent k)) x) =
      ∑ i : Fin m,
        coefficientRectangle (coarse.time i.castSucc) (coarse.time i.succ)
          (H i) x := by
  rw [← Fintype.sum_fiberwise r.toGridRefinement.parent
    (fun k => coefficientRectangle (fine.time k.castSucc) (fine.time k.succ)
      (H (r.toGridRefinement.parent k)) x)]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    (∑ k : {k : Fin n // r.toGridRefinement.parent k = i},
      coefficientRectangle (fine.time k.val.castSucc) (fine.time k.val.succ)
        (H (r.toGridRefinement.parent k.val)) x) =
      ∑ k : {k : Fin n // r.toGridRefinement.parent k = i},
        coefficientRectangle (fine.time k.val.castSucc) (fine.time k.val.succ)
          (H i) x := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [k.property]
    _ = coefficientRectangle (coarse.time i.castSucc) (coarse.time i.succ)
        (H i) x :=
      ContiguousGridRefinement.sum_coefficientRectangle_parentFiber r H i x

end BlockBand.SourceProcess.FiniteDriverCompletion.PredictableRectangle
