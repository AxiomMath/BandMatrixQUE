module
public import BlockBand.Counting.PhysicalMarkedTightness
public import BlockBand.Counting.PhysicalFactorialConsequences
public import BlockBand.Counting.SimpleSpectralLimitsTopology
public import BlockBand.Native.PSSS.SourceContract

/-!
# Second moments of the marked window count

The number of marked atoms with spectral coordinate in `[-L, L]` is a measurable function of the
marked configuration, and its second moment is bounded uniformly over the exact physical models
with a fixed parameter `p.b = b`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.PointProcess.BlockAtom
open MeasureTheory Set Filter
open BlockBand.Model.Construction BlockBand.Counting BlockBand.External.PSSS
open scoped Topology ENNReal NNReal

/-- Number of marked atoms with spectral coordinate in `[-L, L]`, in `ℝ≥0∞`; marks are
unrestricted. -/
def markedWindowCount (L : ℝ) (ξ : MarkedPointMeasure) : ℝ≥0∞ :=
  ξ.marked.measure (Set.Icc (-L) L ×ˢ Set.univ)

/-- The window count is the spectral-projection mass of `[-L, L]`, for every marked
point measure (uses only the constrained field `spectral_eq`). -/
theorem markedWindowCount_eq_spectral (L : ℝ) (ξ : MarkedPointMeasure) :
    markedWindowCount L ξ = ξ.spectral.measure (Set.Icc (-L) L) := by
  rw [ξ.spectral_eq, Measure.map_apply measurable_fst measurableSet_Icc, markedWindowCount,
    Set.prod_univ]

/-- The closed interval `[a, b]` is the decreasing intersection of the open intervals
`(a - 1/(n+1), b + 1/(n+1))`. -/
theorem iInter_Ioo_one_div_eq_Icc (a b : ℝ) :
    (⋂ n : ℕ, Ioo (a - 1 / ((n : ℝ) + 1)) (b + 1 / ((n : ℝ) + 1))) = Icc a b := by
  ext x
  simp only [mem_iInter, mem_Ioo, mem_Icc]
  constructor
  · intro h
    constructor
    · by_contra hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr (lt_of_not_ge hx))
      linarith [(h n).1]
    · by_contra hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr (lt_of_not_ge hx))
      linarith [(h n).2]
  · rintro ⟨h1, h2⟩ n
    have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := Nat.one_div_pos_of_nat
    constructor <;> linarith

/-- On every locally finite point measure on `ℝ`, the closed-interval mass is the
countable infimum of open-interval masses. -/
theorem vague_Icc_mass_eq_iInf (ξ : VaguePointMeasure ℝ) (a b : ℝ) :
    ξ.measure (Icc a b) =
      ⨅ n : ℕ, ξ.measure (Ioo (a - 1 / ((n : ℝ) + 1)) (b + 1 / ((n : ℝ) + 1))) := by
  rw [← iInter_Ioo_one_div_eq_Icc a b]
  apply Antitone.measure_iInter
  · intro n m hnm
    have h : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := Nat.one_div_le_one_div hnm
    exact Ioo_subset_Ioo (by linarith) (by linarith)
  · exact fun n => measurableSet_Ioo.nullMeasurableSet
  · refine ⟨0, (lt_of_le_of_lt (measure_mono Ioo_subset_Icc_self)
      (ξ.finite_on_compact _ isCompact_Icc)).ne⟩

/-- Closed-interval mass is Borel measurable for the ordinary vague topology. -/
theorem measurable_vague_Icc_mass (a b : ℝ) :
    Measurable (fun ξ : VaguePointMeasure ℝ => ξ.measure (Icc a b)) := by
  simp_rw [vague_Icc_mass_eq_iInf]
  exact Measurable.iInf fun n => measurable_vague_Ioo_mass _ _

/-- The window count is Borel measurable on marked point measures with the ordinary vague topology
(via the continuous spectral projection). -/
theorem measurable_markedWindowCount (L : ℝ) : Measurable (markedWindowCount L) := by
  have h : markedWindowCount L =
      (fun ξ : VaguePointMeasure ℝ => ξ.measure (Icc (-L) L)) ∘
        MarkedPointMeasure.spectralProjection := by
    funext ξ
    exact markedWindowCount_eq_spectral L ξ
  rw [h]
  exact (measurable_vague_Icc_mass _ _).comp continuous_markedSpectralProjection.measurable

/-- On every matrix `H` (no good-locus restriction), the window count of the physical marked
configuration equals the canonical local count of `PhysicalMarkedTightness`, whose window is also
`Icc (-L) L`. -/
theorem markedWindowCount_physical (p : Parameters) (E L : ℝ) (H : p.SiteMatrix) :
    markedWindowCount L (physicalOrderedMarkedConfig p E H) =
      (physicalCanonicalLocalCount p E L H : ℝ≥0∞) := by
  classical
  unfold markedWindowCount physicalOrderedMarkedConfig physicalSpectralDataMarkedConfig
  rw [finiteAtomicMarkedPointMeasure_marked,
    finiteAtomicMeasure_apply _ _ (measurableSet_Icc.prod MeasurableSet.univ)]
  unfold finiteAtomicCount physicalCanonicalLocalCount finiteSpectralCount
    physicalCanonicalMarkedLocations
  congr 2
  ext α
  simp

/-- Elementary inequality `x² ≤ 2 eˣ` for `x ≥ 0`. -/
theorem sq_le_two_mul_exp {x : ℝ} (hx : 0 ≤ x) : x ^ 2 ≤ 2 * Real.exp x := by
  have h := Real.quadratic_le_exp_of_nonneg hx
  nlinarith

/-- Explicit second-moment constant; it depends only on `b`, `E`, `L` (and the fixed
PSSS source constant). -/
def markedWindowSecondMomentConstant (b E L : ℝ) : ℝ :=
  2 * Real.exp (2 * L * (Native.PSSS.sourceContract_holds_zero.C /
    (Real.sqrt (1 - 2 * b) * Parameters.semicircleDensity E)) * (Real.exp 1 - 1))

/-- Second-moment bound for one exact physical model, on the raw Gaussian law, with
the explicit constant of `markedWindowSecondMomentConstant p.b E L`. -/
theorem lintegral_markedWindowCount_sq_le_model (p : Parameters) (model : p.GaussianRingModel)
    (E : ℝ) (hE : -2 < E) (hE' : E < 2) (L : ℝ) (hL : 0 ≤ L) :
    ∫⁻ ξ, markedWindowCount L ξ ^ 2
        ∂(model.canonicalPhysicalMarkedLaw E : Measure MarkedPointMeasure) ≤
      ENNReal.ofReal (markedWindowSecondMomentConstant p.b E L) := by
  let source := Native.PSSS.sourceContract_holds_zero
  let μ : Measure p.SiteMatrix := model.law
  let cnt := p.physicalUnfoldedIntervalCount ⟨0, Matrix.isHermitian_zero⟩ E
    (Parameters.semicircleDensity E) (-L) L
  have hmap : (model.canonicalPhysicalMarkedLaw E : Measure MarkedPointMeasure) =
      μ.map (physicalOrderedMarkedConfig p E) := by
    simp [Parameters.GaussianRingModel.canonicalPhysicalMarkedLaw, μ]
  rw [hmap, lintegral_map ((measurable_markedWindowCount L).pow_const 2)
    (measurable_physicalOrderedMarkedConfig p E)]
  simp_rw [markedWindowCount_physical]
  have hae := physicalCanonicalLocalCount_eq_physical_ae p model E L
  rw [lintegral_congr_ae (hae.mono fun H h => congrArg (fun n : ℕ => (n : ℝ≥0∞) ^ 2) h)]
  have hpt : ∀ H, ((cnt H : ℕ) : ℝ≥0∞) ^ 2 ≤
      ENNReal.ofReal (2 * Real.exp (1 * (cnt H : ℝ))) := by
    intro H
    rw [one_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (Nat.cast_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (sq_le_two_mul_exp (Nat.cast_nonneg _))
  refine (lintegral_mono hpt).trans ?_
  have hint := (model.physicalUnfoldedIntervalCount_exponentialIntegrable
    ⟨0, Matrix.isHermitian_zero⟩ E (Parameters.semicircleDensity E) (-L) L 1).const_mul 2
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun H => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [integral_const_mul]
  have hb := model.physicalUnfoldedIntervalCount_exponentialBound_semicircle source
    ⟨0, Matrix.isHermitian_zero⟩ E ⟨hE, hE'⟩ L 1 hL zero_le_one
  unfold markedWindowSecondMomentConstant
  simp only [Parameters.physicalUnfoldedConstant, Parameters.c] at hb
  exact mul_le_mul_of_nonneg_left hb (by norm_num)

/-- Uniform second moment of the window count under `model.canonicalPhysicalMarkedLaw E`: for fixed
`b ∈ (0, 1/2)`, bulk `E ∈ (-2, 2)` and `L ≥ 0`, one finite constant `C` (depending only on `b`,
`E`, `L`) bounds the moment for every admissible `p` with `p.b = b` (all `n ≥ 4`, `W ≥ 1`) and
every Gaussian ring model of `p`. -/
theorem lintegral_markedWindowCount_sq_le (b : ℝ) (_hb : 0 < b) (_hb' : b < 1 / 2) (E : ℝ)
    (hE : -2 < E) (hE' : E < 2) (L : ℝ) (hL : 0 ≤ L) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (p : Parameters), p.b = b → ∀ model : p.GaussianRingModel,
      ∫⁻ ξ, markedWindowCount L ξ ^ 2
        ∂(model.canonicalPhysicalMarkedLaw E : Measure MarkedPointMeasure) ≤ C := by
  refine ⟨ENNReal.ofReal (markedWindowSecondMomentConstant b E L), ENNReal.ofReal_ne_top, ?_⟩
  intro p hp model
  have h := lintegral_markedWindowCount_sq_le_model p model E hE hE' L hL
  rwa [hp] at h

end BlockBand.PointProcess.BlockAtom
