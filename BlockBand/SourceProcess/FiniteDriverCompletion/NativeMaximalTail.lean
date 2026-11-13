module
public import BlockBand.SourceProcess.FiniteDriverCompletion.NativeGridMartingale
public import BlockBand.SourceProcess.FiniteDriverCompletion.PredictableGridEnergy
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Probability.Martingale.OptionalStopping

/-!
# Discrete maximal inequality for continuous grid sums

The square of a continuous grid sum is a submartingale (conditional Jensen), so its energy at
earlier times is bounded by its terminal energy, and along any monotone sequence of sampling times
in `[0, T]` the maximal tail is bounded by the terminal energy, uniformly in the sampling.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.SourceProcess.FiniteDriverCompletion
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators
open BlockBand.SourceProcess.FiniteDriverIntegration
variable {S κ : Type*} [MeasurableSpace S] [Fintype κ]
variable {μ : Measure S} [IsProbabilityMeasure μ] {T : ℝ≥0}
namespace GridPresentation

/-- The square of a continuous grid sum is a submartingale (conditional Jensen). -/
theorem continuousIntegral_sq_submartingale (d : GridPresentation (κ := κ) μ T) :
    Submartingale (fun u x => (d.continuousIntegral u x)^2)
      (commonWienerFiltration S κ) (driverLaw (κ := κ) μ) := by
  refine ⟨fun u => ((d.continuousIntegral_adapted u).pow_const 2).stronglyMeasurable, ?_,
    fun u => (d.continuousIntegral_memLp u).integrable_sq⟩
  intro r v hrv
  have hcv : ConvexOn ℝ Set.univ (fun z : ℝ => z^2) :=
    (by norm_num : Even 2).convexOn_pow
  have hj := ConvexOn.map_condExp_le_univ ((commonWienerFiltration S κ).le r)
    hcv (continuous_id.pow 2).lowerSemicontinuous
    ((d.continuousIntegral_memLp v).integrable (by norm_num))
    (d.continuousIntegral_memLp v).integrable_sq
  filter_upwards [hj, d.continuousIntegral_martingale.condExp_ae_eq hrv] with x hx hy
  change ((driverLaw (κ := κ) μ)[d.continuousIntegral v |
    commonWienerFiltration S κ r] x)^2 ≤ _ at hx
  rw [hy] at hx
  exact hx

/-- The energy of a continuous grid sum at earlier times is bounded by its terminal energy. -/
theorem continuousIntegral_sq_le_terminal (d : GridPresentation (κ := κ) μ T)
    (u : ℝ≥0) (hu : u ≤ T) :
    ∫ x, (d.continuousIntegral u x)^2 ∂driverLaw (κ := κ) μ ≤ ‖d.predictableFamily‖^2 := by
  have hj := d.continuousIntegral_sq_submartingale.2.1 u T hu
  have hm := integral_mono_ae (d.continuousIntegral_memLp u).integrable_sq
    integrable_condExp hj
  rw [integral_condExp ((commonWienerFiltration S κ).le u)] at hm
  change (∫ x, (d.continuousIntegral u x)^2 ∂driverLaw (κ := κ) μ) ≤
    ∫ x, (d.continuousIntegral T x)^2 ∂driverLaw (κ := κ) μ at hm
  rw [d.continuousIntegral_terminal] at hm
  rw [d.predictableFamily_norm_eq_integralLp]
  change _ ≤ ‖d.integral_memLp.toLp d.integral‖^2
  rw [norm_sq_toLp d.integral_memLp]
  exact hm

/-- The discrete filtration along a monotone sequence of sampling times. -/
def samplingFiltration (q : ℕ → ℝ≥0) (hq : Monotone q) :
    Filtration ℕ (inferInstance : MeasurableSpace (DriverSample S κ)) where
  seq n := commonWienerFiltration S κ (q n)
  mono' := fun _i _j hij => (commonWienerFiltration S κ).mono (hq hij)
  le' n := (commonWienerFiltration S κ).le (q n)

/-- The maximal tail along finitely many sampling times is bounded by the terminal energy,
uniformly in the sampling and in the grid presentation. -/
theorem continuousIntegral_finite_maximal_tail (d : GridPresentation (κ := κ) μ T)
    (q : ℕ → ℝ≥0) (hq : Monotone q) (n : ℕ) (hnT : q n ≤ T) (ε : ℝ≥0) :
    (ε^2 : ℝ≥0) * (driverLaw (κ := κ) μ)
      {x | ((ε^2 : ℝ≥0) : ℝ) ≤ (Finset.range (n + 1)).sup'
        Finset.nonempty_range_add_one (fun k => (d.continuousIntegral (q k) x)^2)} ≤
      ENNReal.ofReal (‖d.predictableFamily‖^2) := by
  let f : ℕ → DriverSample S κ → ℝ := fun k x => (d.continuousIntegral (q k) x)^2
  have hs : Submartingale f (samplingFiltration (S := S) (κ := κ) q hq)
      (driverLaw (κ := κ) μ) :=
    ⟨fun k => d.continuousIntegral_sq_submartingale.1 (q k),
      fun i j hij => d.continuousIntegral_sq_submartingale.2.1 (q i) (q j) (hq hij),
      fun k => d.continuousIntegral_sq_submartingale.2.2 (q k)⟩
  have hm := maximal_ineq hs (fun k x => sq_nonneg (d.continuousIntegral (q k) x))
    (ε := ε^2) n
  refine hm.trans (ENNReal.ofReal_le_ofReal ?_)
  exact (setIntegral_le_integral (d.continuousIntegral_memLp (q n)).integrable_sq
    (Eventually.of_forall (fun x => sq_nonneg (d.continuousIntegral (q n) x)))).trans
      (d.continuousIntegral_sq_le_terminal (q n) hnT)

end GridPresentation
end BlockBand.SourceProcess.FiniteDriverCompletion
