module
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.Density
public import BlockBand.SourceProcess.Stochastic.Integral.Indicator
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Indicator multipliers on predictable `L²` and stochastic intervals

Setting: an arbitrary measurable space `(Ω, m₀)`, a raw filtration `𝓖 : Filtration ℝ≥0 m₀`,
an arbitrary measure `μ` on `ℝ × Ω` (in applications the bracket measure `ν_T` of
`Setting`), and the integrand space `PredL2 𝓖 μ` (predictable classes in `L²(μ)`).

* `predInd 𝓖 R hR`: multiplication by `1_R` for a predictable set `R`, a continuous linear
  operator on `PredL2 𝓖 μ` of norm `≤ 1` (built from the generic `Integral.indicatorL2`).
  Algebra: disjoint unions add (`predInd_union`), composition is intersection
  (`predInd_predInd`), a.e.-equal sets give equal operators (`predInd_congr`), null sets give
  `0` (`predInd_null`).
* `stopSet τ = {(s,ω) | s⁺ ≤ τ ω}`, the stochastic interval `[[0, τ]]` (time read as
  `s.toNNReal`). `measurableSet_stopSet`: for a raw `𝓖`-stopping time `τ`
  (`{τ ≤ t} ∈ 𝓖_t`, values in `WithTop ℝ≥0`), `stopSet τ` is predictable. Proof: its
  complement is the countable union of the predictable rectangles
  `(q, q + n] × {τ ≤ q}`, `q ∈ ℚ`, `n ∈ ℕ`.
-/

namespace BlockBand.SourceProcess.Stochastic.GeneralIntegral
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] (𝓖 : Filtration ℝ≥0 mΩ) {μ : Measure (ℝ × Ω)}

/-- Two predictable classes are equal iff their representatives agree `μ`-a.e. -/
theorem predL2_ext {f g : PredL2 𝓖 μ}
    (h : ((f : Lp ℝ 2 μ) : ℝ × Ω → ℝ) =ᵐ[μ] ((g : Lp ℝ 2 μ) : ℝ × Ω → ℝ)) : f = g :=
  Subtype.ext (Lp.ext h)

theorem indicator_mem_predL2 (R : Set (ℝ × Ω)) (hR : MeasurableSet[predictableSpace (toCF 𝓖)] R)
    (f : PredL2 𝓖 μ) :
    Integral.indicatorL2 R (predictableSpace_le _ R hR) (f : Lp ℝ 2 μ) ∈
      lpMeas ℝ ℝ (predictableSpace (toCF 𝓖)) 2 μ := by
  rw [mem_lpMeas_iff_aestronglyMeasurable]
  obtain ⟨g, hg, hfg⟩ := lpMeas.aestronglyMeasurable f
  refine ⟨R.indicator g, hg.indicator hR, ?_⟩
  filter_upwards [Integral.indicatorL2_coeFn R (predictableSpace_le _ R hR) (f : Lp ℝ 2 μ), hfg]
    with x hx hx'
  rw [hx]
  by_cases hxR : x ∈ R
  · simp only [indicator_of_mem hxR, hx']
  · simp only [indicator_of_notMem hxR]

/-- Multiplication by `1_R` (`R` predictable) on `PredL2 𝓖 μ`. -/
def predInd (R : Set (ℝ × Ω)) (hR : MeasurableSet[predictableSpace (toCF 𝓖)] R) :
    PredL2 𝓖 μ →L[ℝ] PredL2 𝓖 μ :=
  ((Integral.indicatorL2 R (predictableSpace_le _ R hR)).comp
    (lpMeas ℝ ℝ (predictableSpace (toCF 𝓖)) 2 μ).subtypeL).codRestrict _
    (indicator_mem_predL2 𝓖 R hR)

theorem predInd_coeFn (R : Set (ℝ × Ω)) (hR : MeasurableSet[predictableSpace (toCF 𝓖)] R)
    (f : PredL2 𝓖 μ) :
    (((predInd 𝓖 R hR f : PredL2 𝓖 μ) : Lp ℝ 2 μ) : ℝ × Ω → ℝ) =ᵐ[μ]
      R.indicator ((f : Lp ℝ 2 μ) : ℝ × Ω → ℝ) :=
  Integral.indicatorL2_coeFn R (predictableSpace_le _ R hR) _

theorem norm_predInd_le (R : Set (ℝ × Ω)) (hR : MeasurableSet[predictableSpace (toCF 𝓖)] R)
    (f : PredL2 𝓖 μ) : ‖predInd 𝓖 R hR f‖ ≤ ‖f‖ :=
  Integral.norm_indicator_toLp_le R (predictableSpace_le _ R hR) (f : Lp ℝ 2 μ)

theorem predInd_union {A B : Set (ℝ × Ω)} (hA : MeasurableSet[predictableSpace (toCF 𝓖)] A)
    (hB : MeasurableSet[predictableSpace (toCF 𝓖)] B) (hAB : Disjoint A B) (f : PredL2 𝓖 μ) :
    predInd 𝓖 (A ∪ B) (hA.union hB) f = predInd 𝓖 A hA f + predInd 𝓖 B hB f := by
  refine predL2_ext 𝓖 ?_
  filter_upwards [predInd_coeFn 𝓖 _ (hA.union hB) f, predInd_coeFn 𝓖 _ hA f,
    predInd_coeFn 𝓖 _ hB f, Lp.coeFn_add ((predInd 𝓖 A hA f : PredL2 𝓖 μ) : Lp ℝ 2 μ)
      ((predInd 𝓖 B hB f : PredL2 𝓖 μ) : Lp ℝ 2 μ)] with x h1 h2 h3 h4
  change _ = (((predInd 𝓖 A hA f : PredL2 𝓖 μ) : Lp ℝ 2 μ) +
    ((predInd 𝓖 B hB f : PredL2 𝓖 μ) : Lp ℝ 2 μ)) x
  rw [h1, h4, Pi.add_apply, h2, h3, indicator_union_of_disjoint hAB]

theorem predInd_predInd {A B : Set (ℝ × Ω)} (hA : MeasurableSet[predictableSpace (toCF 𝓖)] A)
    (hB : MeasurableSet[predictableSpace (toCF 𝓖)] B) (f : PredL2 𝓖 μ) :
    predInd 𝓖 A hA (predInd 𝓖 B hB f) = predInd 𝓖 (A ∩ B) (hA.inter hB) f := by
  refine predL2_ext 𝓖 ?_
  filter_upwards [predInd_coeFn 𝓖 _ hA (predInd 𝓖 B hB f), predInd_coeFn 𝓖 _ hB f,
    predInd_coeFn 𝓖 _ (hA.inter hB) f] with x h1 h2 h3
  rw [h1, h3]
  by_cases hxA : x ∈ A
  · rw [indicator_of_mem hxA, h2]
    by_cases hxB : x ∈ B
    · rw [indicator_of_mem hxB, indicator_of_mem (show x ∈ A ∩ B from ⟨hxA, hxB⟩)]
    · rw [indicator_of_notMem hxB, indicator_of_notMem (fun h => hxB h.2)]
  · rw [indicator_of_notMem hxA, indicator_of_notMem (fun h => hxA h.1)]

theorem predInd_congr {A B : Set (ℝ × Ω)} (hA : MeasurableSet[predictableSpace (toCF 𝓖)] A)
    (hB : MeasurableSet[predictableSpace (toCF 𝓖)] B) (hAB : A =ᵐ[μ] B) (f : PredL2 𝓖 μ) :
    predInd 𝓖 A hA f = predInd 𝓖 B hB f := by
  refine predL2_ext 𝓖 ?_
  filter_upwards [predInd_coeFn 𝓖 _ hA f, predInd_coeFn 𝓖 _ hB f,
    indicator_ae_eq_of_ae_eq_set (f := ((f : Lp ℝ 2 μ) : ℝ × Ω → ℝ)) hAB] with x h1 h2 h3
  rw [h1, h2, h3]

theorem predInd_univ (f : PredL2 𝓖 μ) : predInd 𝓖 univ MeasurableSet.univ f = f := by
  refine predL2_ext 𝓖 ?_
  filter_upwards [predInd_coeFn 𝓖 _ MeasurableSet.univ f] with x h1
  rw [h1, indicator_univ]

theorem predInd_null {A : Set (ℝ × Ω)} (hA : MeasurableSet[predictableSpace (toCF 𝓖)] A)
    (h0 : μ A = 0) (f : PredL2 𝓖 μ) : predInd 𝓖 A hA f = 0 := by
  refine predL2_ext 𝓖 ?_
  have hz : ((((0 : PredL2 𝓖 μ) : Lp ℝ 2 μ)) : ℝ × Ω → ℝ) =ᵐ[μ] 0 := Lp.coeFn_zero _ _ _
  filter_upwards [predInd_coeFn 𝓖 _ hA f, hz, measure_eq_zero_iff_ae_notMem.1 h0]
    with x h1 h2 h3
  rw [h1, h2, indicator_of_notMem h3, Pi.zero_apply]

/-- Predictable rectangles `(q₁, q₂] × C`, `C ∈ 𝓖_{q₁}` (no order or horizon condition). -/
theorem measurableSet_rect_pred {q₁ q₂ : ℝ≥0} {C : Set Ω} (hC : MeasurableSet[𝓖 q₁] C) :
    MeasurableSet[predictableSpace (toCF 𝓖)] (Ioc (q₁ : ℝ) q₂ ×ˢ C) :=
  measurableSet_predictableRectangle (toCF 𝓖) hC

/-!
### The stochastic interval `[[0, τ]]`
-/

/-- The stochastic interval `[[0, τ]] = {(s, ω) | s⁺ ≤ τ ω}`. -/
def stopSet (τ : Ω → WithTop ℝ≥0) : Set (ℝ × Ω) :=
  {p | ((p.1.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ p.2}

omit mΩ in
theorem compl_stopSet (τ : Ω → WithTop ℝ≥0) :
    (stopSet τ)ᶜ = ⋃ (q : ℚ) (n : ℕ),
      Ioc (((q : ℝ).toNNReal : ℝ≥0) : ℝ) ((((q : ℝ).toNNReal + n : ℝ≥0)) : ℝ) ×ˢ
        {ω | τ ω ≤ ((q : ℝ).toNNReal : WithTop ℝ≥0)} := by
  ext p
  simp only [stopSet, mem_compl_iff, mem_ofPred_eq, not_le, mem_iUnion, mem_prod, mem_Ioc]
  constructor
  · intro hlt
    obtain ⟨σ, hσ⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hlt)
    rw [← hσ, WithTop.coe_lt_coe] at hlt
    have hpos : (σ : ℝ) < p.1 := by
      have h := NNReal.coe_lt_coe.2 hlt
      rw [Real.coe_toNNReal'] at h
      rcases lt_max_iff.1 h with h | h
      · exact h
      · exact absurd h (not_lt.2 σ.coe_nonneg)
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hpos
    have hq0 : (0 : ℝ) ≤ q := σ.coe_nonneg.trans hq1.le
    obtain ⟨n, hn⟩ := exists_nat_ge (p.1 - q)
    refine ⟨q, n, ⟨⟨?_, ?_⟩, ?_⟩⟩
    · rw [Real.coe_toNNReal _ hq0]; exact hq2
    · rw [NNReal.coe_add, Real.coe_toNNReal _ hq0, NNReal.coe_natCast]; linarith
    · rw [← hσ, WithTop.coe_le_coe, ← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0]
      exact hq1.le
  · rintro ⟨q, n, ⟨h1, -⟩, h3⟩
    refine lt_of_le_of_lt h3 (WithTop.coe_lt_coe.2 ?_)
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ ((NNReal.coe_nonneg _).trans h1.le)]
    exact h1

/-- **The stochastic interval `[[0, τ]]` of a raw stopping time is predictable.** -/
theorem measurableSet_stopSet {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ) :
    MeasurableSet[predictableSpace (toCF 𝓖)] (stopSet τ) := by
  rw [← compl_compl (stopSet τ), compl_stopSet]
  refine MeasurableSet.compl (MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun n => ?_)
  exact measurableSet_predictableRectangle (toCF 𝓖) (t := (q : ℝ).toNNReal + n) (hτ _)

omit mΩ in
theorem mem_stopSet {τ : Ω → WithTop ℝ≥0} {p : ℝ × Ω} :
    p ∈ stopSet τ ↔ ((p.1.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ τ p.2 := Iff.rfl

omit mΩ in
/-- Deterministic stopping: `[[0, t]] = (-∞, t] × Ω`. -/
theorem stopSet_const (t : ℝ≥0) :
    stopSet (fun _ : Ω => (t : WithTop ℝ≥0)) = Iic (t : ℝ) ×ˢ univ := by
  ext p
  simp only [stopSet, mem_ofPred_eq, WithTop.coe_le_coe, mem_prod, mem_Iic, mem_univ, and_true,
    Real.toNNReal_le_iff_le_coe]

omit mΩ in
theorem stopSet_min (τ σ : Ω → WithTop ℝ≥0) :
    stopSet (fun ω => min (τ ω) (σ ω)) = stopSet τ ∩ stopSet σ := by
  ext p
  simp only [stopSet, mem_ofPred_eq, mem_inter_iff, le_min_iff]

/-- The deterministic interval `(-∞, t] × Ω` is predictable. -/
theorem measurableSet_Iic_prod_univ (t : ℝ≥0) :
    MeasurableSet[predictableSpace (toCF 𝓖)] (Iic (t : ℝ) ×ˢ (univ : Set Ω)) := by
  rw [← stopSet_const (Ω := Ω) t]
  exact measurableSet_stopSet 𝓖 (isStoppingTime_const 𝓖 t)

end BlockBand.SourceProcess.Stochastic.GeneralIntegral
