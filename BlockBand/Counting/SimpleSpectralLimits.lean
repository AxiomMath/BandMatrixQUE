module
public import BlockBand.Counting.SimpleSpectralLimitsPhysical

/-!
# Simple spectral locations of subsequential limits

If a law on marked configurations gives probability at most `(K (y - x))²` to the event that
an open interval `(x,y)` contains two spectral points, then almost surely no spectral point
has multiplicity larger than one.  Applied to the physical estimate and passed to weak
limits, every subsequential weak limit of the marked laws along a critical sequence has
simple spectral locations.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Counting
open MeasureTheory Set Filter
open BlockBand.External.PSSS BlockBand.Parameters
open scoped Topology ENNReal NNReal

def spectralCollisionInWindow (R : ℝ) : Set MarkedPointMeasure :=
  {ξ | ∃ x : ℝ, |x| ≤ R ∧ (1 : ℝ≥0∞) < ξ.spectral.measure {x}}

/-- A slightly enlarged closed grid covers every repeated singleton. -/
theorem spectralCollisionInWindow_subset_grid {R a : ℝ} (hR : 0 ≤ R) (ha : 0 < a) :
    spectralCollisionInWindow R ⊆
      ⋃ j : Fin (closePairGridSize R a),
        {ξ : MarkedPointMeasure | (1 : ℝ≥0∞) < ξ.spectral.measure
          (Ioo (closePairGridLo R a j - a / 2) (closePairGridHi R a j + a / 2))} := by
  rintro ξ ⟨x, hxR, hmass⟩
  obtain ⟨j, hjlo, hjhi⟩ := exists_closePairGridWindow (x := x) (y := x) hR ha hxR (by simpa using ha)
  apply mem_iUnion.mpr
  refine ⟨j, hmass.trans_le (measure_mono ?_)⟩
  intro y hy
  have hyx : y = x := mem_singleton_iff.mp hy
  subst y
  constructor <;> linarith

/-- Quadratic interval collision control yields a vanishing localized collision bound. -/
theorem measure_spectralCollisionInWindow_le
    (μ : ProbabilityMeasure MarkedPointMeasure) (K R a : ℝ) (hR : 0 ≤ R) (ha : 0 < a)
    (hinterval : ∀ x y : ℝ, x ≤ y →
      (μ : Measure MarkedPointMeasure) {ξ | (1 : ℝ≥0∞) < ξ.spectral.measure (Ioo x y)} ≤
        ENNReal.ofReal ((K * (y-x)) ^ 2)) :
    (μ : Measure MarkedPointMeasure) (spectralCollisionInWindow R) ≤
      ENNReal.ofReal (18 * K ^ 2 * R * a + 36 * K ^ 2 * a ^ 2) := by
  classical
  have hcover := measure_mono (μ := (μ : Measure MarkedPointMeasure))
    (spectralCollisionInWindow_subset_grid hR ha)
  apply hcover.trans
  have hu : (μ : Measure MarkedPointMeasure)
      (⋃ j : Fin (closePairGridSize R a),
        {ξ : MarkedPointMeasure | (1 : ℝ≥0∞) < ξ.spectral.measure
          (Ioo (closePairGridLo R a j - a / 2) (closePairGridHi R a j + a / 2))}) ≤
      ∑ j : Fin (closePairGridSize R a),
        (μ : Measure MarkedPointMeasure) {ξ | (1 : ℝ≥0∞) < ξ.spectral.measure
          (Ioo (closePairGridLo R a j - a / 2) (closePairGridHi R a j + a / 2))} := by
    simpa using measure_biUnion_finset_le (μ := (μ : Measure MarkedPointMeasure)) Finset.univ
      (fun j : Fin (closePairGridSize R a) => {ξ : MarkedPointMeasure |
        (1 : ℝ≥0∞) < ξ.spectral.measure
          (Ioo (closePairGridLo R a j - a / 2) (closePairGridHi R a j + a / 2))})
  apply hu.trans
  have hs : (∑ j : Fin (closePairGridSize R a),
        (μ : Measure MarkedPointMeasure) {ξ | (1 : ℝ≥0∞) < ξ.spectral.measure
          (Ioo (closePairGridLo R a j - a / 2) (closePairGridHi R a j + a / 2))}) ≤
      ∑ _j : Fin (closePairGridSize R a), ENNReal.ofReal ((K * (3*a)) ^ 2) := by
    apply Finset.sum_le_sum
    intro j _
    have h := hinterval (closePairGridLo R a j - a / 2) (closePairGridHi R a j + a / 2)
      (by unfold closePairGridHi; linarith)
    have hlen : (closePairGridHi R a j + a / 2) - (closePairGridLo R a j - a / 2) = 3*a := by
      unfold closePairGridHi
      ring
    rw [hlen] at h
    exact h
  apply hs.trans
  have he : (∑ _j : Fin (closePairGridSize R a), ENNReal.ofReal ((K * (3*a)) ^ 2)) =
      ENNReal.ofReal ((closePairGridSize R a : ℝ) * (K * (3*a)) ^ 2) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
    simp
  rw [he]
  apply ENNReal.ofReal_le_ofReal
  convert closePairGrid_card_mul_square_le (K := (3/2)*K) hR ha using 1 <;> ring

/-- Simplicity follows from quadratic short-interval two-point bounds. -/
theorem hasSimpleSpectralLocations_of_Ioo_twoPoint_bounds
    (μ : ProbabilityMeasure MarkedPointMeasure) (K : ℝ)
    (hinterval : ∀ x y : ℝ, x ≤ y →
      (μ : Measure MarkedPointMeasure) {ξ | (1 : ℝ≥0∞) < ξ.spectral.measure (Ioo x y)} ≤
        ENNReal.ofReal ((K * (y-x)) ^ 2)) : HasSimpleSpectralLocations μ := by
  have hzero (m : ℕ) : (μ : Measure MarkedPointMeasure) (spectralCollisionInWindow m) = 0 := by
    have hscale : Tendsto (fun n : ℕ => (1 : ℝ) / (n+1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal
        (18 * K ^ 2 * m * ((1 : ℝ)/(n+1)) + 36 * K ^ 2 * ((1 : ℝ)/(n+1)) ^ 2))
        atTop (𝓝 0) := by
      have hr : Tendsto (fun n : ℕ =>
          18 * K ^ 2 * m * ((1 : ℝ)/(n+1)) + 36 * K ^ 2 * ((1 : ℝ)/(n+1)) ^ 2)
          atTop (𝓝 0) := by
        convert (hscale.const_mul (18 * K ^ 2 * m)).add
          ((hscale.pow 2).const_mul (36 * K ^ 2)) using 1
        simp
      simpa only [Function.comp_def, ENNReal.ofReal_zero] using
        (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hr
    apply le_antisymm _ bot_le
    exact ge_of_tendsto hlim (Eventually.of_forall fun n =>
      measure_spectralCollisionInWindow_le μ K m ((1 : ℝ)/(n+1)) (Nat.cast_nonneg _)
        Nat.one_div_pos_of_nat hinterval)
  have hae : ∀ᵐ ξ ∂(μ : Measure MarkedPointMeasure),
      ∀ m : ℕ, ξ ∉ spectralCollisionInWindow m := by
    apply ae_all_iff.mpr
    intro m
    apply (mem_ae_iff).mpr
    have he : {ξ : MarkedPointMeasure | ξ ∉ spectralCollisionInWindow m}ᶜ =
        spectralCollisionInWindow m := by ext ξ; simp
    rw [he]
    exact hzero m
  filter_upwards [hae] with ξ hξ
  intro x
  by_contra hn
  obtain ⟨m, hm⟩ := exists_nat_ge |x|
  exact hξ m ⟨x, hm, lt_of_not_ge hn⟩

/-- Every subsequential weak limit of the physical marked laws along a critical sequence
has simple spectral locations.  No rate or `n → ∞` hypothesis is used; existence of a
weak limit is not asserted. -/
theorem criticalSequence_marked_weakLimit_hasSimple
    (source : SourceContract.{0}) {τ : ℝ} (s : CriticalSequence τ)
    (b E : ℝ) (hb : 0 < b) (hb' : b < 1/2) (hrho : 0 < semicircleDensity E)
    (R : ∀ j, FiniteRealization (s.parameters b hb hb' j)) (φ : ℕ → ℕ)
    (μ : ProbabilityMeasure MarkedPointMeasure)
    (hlim : Tendsto (fun j => (R (φ j)).markedLaw E) atTop (𝓝 μ)) :
    HasSimpleSpectralLocations μ := by
  apply hasSimpleSpectralLocations_of_Ioo_twoPoint_bounds μ
    (source.C / (Real.sqrt (1-2*b) * semicircleDensity E))
  intro x y hxy
  apply marked_Ioo_twoPoint_le_of_weakLimit (fun j => (R (φ j)).markedLaw E) μ hlim
  intro j
  simpa only [physicalUnfoldedConstant, Parameters.c, CriticalSequence.parameters] using
    finiteRealization_markedLaw_Ioo_twoPoint_bound (R (φ j)) source E hrho x y hxy

end BlockBand.Counting
