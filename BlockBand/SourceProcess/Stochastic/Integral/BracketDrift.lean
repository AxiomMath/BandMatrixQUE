module
public import BlockBand.SourceProcess.Stochastic.Integral.MultiplierStopped
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The pathwise bracket drift `∫_0^t ∑_a g_a h_a ds`

Measures: `P = driverLaw μ` on `Ω = DriverSample S κ`, `ν = timeProbMeasure T P =
(dt|_{(0,T]}) ⊗ P`. For native integrands `g, h` (`L²(ν)`, a.e. raw predictable) the bracket
density `∑_a g_a h_a` is in `L¹(ν)`. We use the given representatives `g, h` themselves:

* `bracketDrift T g h t x = ∫_{(0, t ∧ T]} ∑_a g_a(s,x) h_a(s,x) ds` (Bochner, `volume`);
  `bracketDrift_of_le` rewrites it as `∫_{(0,t]}` for `t ≤ T`;
* `ae_integrableOn_bracketDensity`: for `P`-a.e. `x` the time integrand is integrable on `(0,T]`
  (the pathwise integral is a.e. a Lebesgue integral);
* `integrable_bracketDrift`: `bracketDrift T g h t ∈ L¹(P)`;
* `setIntegral_bracketDrift_sub`: Fubini on `B × (r ∧ T, t ∧ T]`.

The sibling module proves
* `exists_adapted_bracketDrift`: `bracketDrift T g h t` is a.e. equal to a raw
  `F_{t ∧ T}`-measurable function (raw predictable sets restricted to `(0,u] × Ω` are
  `Borel ⊗ F_u`-measurable, then Fubini measurability).
-/

namespace BlockBand.SourceProcess.Stochastic.Integral
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open BlockBand.SourceProcess.FiniteDriverCompletion

variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]

/-- The bracket density `∑_a g_a h_a`. -/
def bracketDensity (g h : κ → ℝ × DriverSample S κ → ℝ) (p : ℝ × DriverSample S κ) : ℝ :=
  ∑ c, g c p * h c p

/-- The pathwise bracket drift `∫_{(0, t ∧ T]} ∑_a g_a(s,x) h_a(s,x) ds`. -/
def bracketDrift (T : ℝ≥0) (g h : κ → ℝ × DriverSample S κ → ℝ) (t : ℝ≥0)
    (x : DriverSample S κ) : ℝ :=
  ∫ s in Set.Ioc (0 : ℝ) ((min t T : ℝ≥0) : ℝ), bracketDensity g h (s, x)

omit [MeasurableSpace S] in
theorem bracketDrift_of_le {T t : ℝ≥0} (htT : t ≤ T) (g h : κ → ℝ × DriverSample S κ → ℝ)
    (x : DriverSample S κ) :
    bracketDrift T g h t x = ∫ s in Set.Ioc (0 : ℝ) (t : ℝ), ∑ c, g c (s, x) * h c (s, x) := by
  simp only [bracketDrift, bracketDensity, min_eq_left htT]

/-- The restricted time law `dt|_{(0,T]}`. -/
abbrev timeLaw (T : ℝ≥0) : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))

variable {μ : Measure S} [IsProbabilityMeasure μ] {T : ℝ≥0}

/-- A `dt ⊗ P`-a.e. property holds for `P`-a.e. sample and then `dt`-a.e. time in `(0,T]`. -/
theorem ae_ae_of_ae_timeProb {q : ℝ × DriverSample S κ → Prop}
    (h : ∀ᵐ p ∂timeProbMeasure T (driverLaw (κ := κ) μ), q p) :
    ∀ᵐ x ∂driverLaw (κ := κ) μ, ∀ᵐ s ∂timeLaw T, q (s, x) := by
  have h' : ∀ᵐ z ∂(driverLaw (κ := κ) μ).prod (timeLaw T), q z.swap :=
    (Measure.measurePreserving_swap (μ := driverLaw (κ := κ) μ)
      (ν := timeLaw T)).quasiMeasurePreserving.ae h
  exact Measure.ae_ae_of_ae_prod h'

omit [IsProbabilityMeasure μ] in
theorem integrable_bracketDensity {g h : κ → ℝ × DriverSample S κ → ℝ}
    (hg : NativeIntegrand μ T g) (hh : NativeIntegrand μ T h) :
    Integrable (bracketDensity g h) (timeProbMeasure T (driverLaw (κ := κ) μ)) :=
  integrable_finsetSum _ fun c _ => (hg c).2.integrable_mul (hh c).2

omit [IsProbabilityMeasure μ] in
theorem aestronglyMeasurable_bracketDensity {g h : κ → ℝ × DriverSample S κ → ℝ}
    (hg : NativeIntegrand μ T g) (hh : NativeIntegrand μ T h) :
    AEStronglyMeasurable[rawPredictable S κ] (bracketDensity g h)
      (timeProbMeasure T (driverLaw (κ := κ) μ)) := by
  have he : bracketDensity g h = ∑ c, (g c * h c) := by
    funext p
    simp only [bracketDensity, Finset.sum_apply, Pi.mul_apply]
  rw [he]
  refine Finset.sum_induction _ (fun f => AEStronglyMeasurable[rawPredictable S κ] f
      (timeProbMeasure T (driverLaw (κ := κ) μ))) (fun a b ha hb => ha.add hb) ?_
    (fun c _ => (hg c).1.mul (hh c).1)
  exact ⟨fun _ => 0, stronglyMeasurable_const, Eventually.of_forall fun _ => rfl⟩

/-- **Pathwise finiteness.** For `P`-a.e. `x`, `s ↦ ∑_a g_a(s,x) h_a(s,x)` is integrable on
`(0,T]`. -/
theorem ae_integrableOn_bracketDensity {g h : κ → ℝ × DriverSample S κ → ℝ}
    (hg : NativeIntegrand μ T g) (hh : NativeIntegrand μ T h) :
    ∀ᵐ x ∂driverLaw (κ := κ) μ,
      IntegrableOn (fun s => bracketDensity g h (s, x)) (Set.Ioc 0 (T : ℝ)) :=
  (integrable_bracketDensity hg hh).prod_left_ae

omit [MeasurableSpace S] [Fintype κ] [IsProbabilityMeasure μ] in
theorem indicator_prod_univ_apply (u : ℝ) (G : ℝ × DriverSample S κ → ℝ) (s : ℝ)
    (x : DriverSample S κ) :
    (Set.Ioc 0 u ×ˢ (Set.univ : Set (DriverSample S κ))).indicator G (s, x) =
      (Set.Ioc 0 u).indicator (fun s => G (s, x)) s := by
  by_cases hs : s ∈ Set.Ioc 0 u
  · rw [Set.indicator_of_mem (Set.mk_mem_prod hs (Set.mem_univ x)), Set.indicator_of_mem hs]
  · rw [Set.indicator_of_notMem (fun h => hs (Set.mem_prod.1 h).1), Set.indicator_of_notMem hs]

omit [MeasurableSpace S] [Fintype κ] [IsProbabilityMeasure μ] in
theorem setIntegral_eq_timeLaw {u : ℝ} (huT : u ≤ T) (G : ℝ × DriverSample S κ → ℝ)
    (x : DriverSample S κ) :
    ∫ s in Set.Ioc (0 : ℝ) u, G (s, x) =
      ∫ s, (Set.Ioc 0 u).indicator (fun s => G (s, x)) s ∂timeLaw T := by
  rw [setIntegral_indicator measurableSet_Ioc,
    Set.inter_eq_right.2 (Set.Ioc_subset_Ioc_right huT)]

theorem integrable_bracketDrift {g h : κ → ℝ × DriverSample S κ → ℝ}
    (hg : NativeIntegrand μ T g) (hh : NativeIntegrand μ T h) (t : ℝ≥0) :
    Integrable (bracketDrift T g h t) (driverLaw (κ := κ) μ) := by
  have hK := ((integrable_bracketDensity hg hh).indicator
    ((measurableSet_Ioc (a := (0 : ℝ)) (b := ((min t T : ℝ≥0) : ℝ))).prod
      (MeasurableSet.univ (α := DriverSample S κ)))).integral_prod_right
  refine hK.congr (Eventually.of_forall fun x => ?_)
  simp only [indicator_prod_univ_apply]
  exact (setIntegral_eq_timeLaw (NNReal.coe_le_coe.2 (min_le_right t T)) _ x).symm

omit [MeasurableSpace S] [Fintype κ] [IsProbabilityMeasure μ] in
theorem indicator_Ioc_sub {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) (f : ℝ → ℝ) (s : ℝ) :
    (Set.Ioc 0 t).indicator f s - (Set.Ioc 0 r).indicator f s = (Set.Ioc r t).indicator f s := by
  rw [← Set.Ioc_union_Ioc_eq_Ioc hr hrt,
    Set.indicator_union_of_disjoint (Set.Ioc_disjoint_Ioc_of_le le_rfl)]
  ring

/-- **Fubini for drift increments.** For `r ≤ t` and measurable `B`,
`∫_B (A_t − A_r) dP = ∫ 1_{(r∧T, t∧T] × B} ∑_a g_a h_a d(dt ⊗ P)`. -/
theorem setIntegral_bracketDrift_sub {g h : κ → ℝ × DriverSample S κ → ℝ}
    (hg : NativeIntegrand μ T g) (hh : NativeIntegrand μ T h) {r t : ℝ≥0} (hrt : r ≤ t)
    {B : Set (DriverSample S κ)} (hB : MeasurableSet B) :
    ∫ x in B, (bracketDrift T g h t x - bracketDrift T g h r x) ∂driverLaw (κ := κ) μ =
      ∫ p, (Set.Ioc ((min r T : ℝ≥0) : ℝ) ((min t T : ℝ≥0) : ℝ) ×ˢ B).indicator
        (bracketDensity g h) p ∂timeProbMeasure T (driverLaw (κ := κ) μ) := by
  have hint := (integrable_bracketDensity hg hh).indicator
    ((measurableSet_Ioc (a := ((min r T : ℝ≥0) : ℝ)) (b := ((min t T : ℝ≥0) : ℝ))).prod hB)
  rw [timeProbMeasure, integral_prod_symm _ hint, ← integral_indicator hB]
  apply integral_congr_ae
  filter_upwards [ae_integrableOn_bracketDensity hg hh] with x hx
  have hinner : ∫ s, (Set.Ioc ((min r T : ℝ≥0) : ℝ) ((min t T : ℝ≥0) : ℝ) ×ˢ B).indicator
      (bracketDensity g h) (s, x) ∂timeLaw T = B.indicator (fun x =>
        ∫ s, (Set.Ioc ((min r T : ℝ≥0) : ℝ) ((min t T : ℝ≥0) : ℝ)).indicator
          (fun s => bracketDensity g h (s, x)) s ∂timeLaw T) x := by
    by_cases hxB : x ∈ B
    · rw [Set.indicator_of_mem hxB]
      congr 1
      funext s
      by_cases hs : s ∈ Set.Ioc ((min r T : ℝ≥0) : ℝ) ((min t T : ℝ≥0) : ℝ)
      · rw [Set.indicator_of_mem (Set.mk_mem_prod hs hxB), Set.indicator_of_mem hs]
      · rw [Set.indicator_of_notMem (fun h => hs (Set.mem_prod.1 h).1),
          Set.indicator_of_notMem hs]
    · rw [Set.indicator_of_notMem hxB]
      have h0 : (fun s => (Set.Ioc ((min r T : ℝ≥0) : ℝ) ((min t T : ℝ≥0) : ℝ) ×ˢ B).indicator
          (bracketDensity g h) (s, x)) = fun _ => 0 := by
        funext s
        exact Set.indicator_of_notMem (fun h => hxB (Set.mem_prod.1 h).2) _
      rw [h0, integral_zero]
  change _ = ∫ s, (Set.Ioc ((min r T : ℝ≥0) : ℝ) ((min t T : ℝ≥0) : ℝ) ×ˢ B).indicator
      (bracketDensity g h) (s, x) ∂timeLaw T
  rw [hinner]
  by_cases hxB : x ∈ B
  · rw [Set.indicator_of_mem hxB, Set.indicator_of_mem hxB]
    simp only [bracketDrift]
    rw [setIntegral_eq_timeLaw (NNReal.coe_le_coe.2 (min_le_right t T)),
      setIntegral_eq_timeLaw (NNReal.coe_le_coe.2 (min_le_right r T)),
      ← integral_sub (hx.indicator measurableSet_Ioc) (hx.indicator measurableSet_Ioc)]
    congr 1
    funext s
    exact indicator_Ioc_sub (NNReal.coe_nonneg _)
      (NNReal.coe_le_coe.2 (min_le_min_right T hrt)) _ s
  · rw [Set.indicator_of_notMem hxB, Set.indicator_of_notMem hxB]

end BlockBand.SourceProcess.Stochastic.Integral
