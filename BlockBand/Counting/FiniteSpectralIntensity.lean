module

public import BlockBand.Counting.IntervalIntensityDomination
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Expected intensity of a finite measurable spectrum

For a random finite family of real locations, the expected intensity measure assigns to a
Borel set the expected multiplicity count of the locations in it.  It has total mass `d`,
integrates functions to the expected sum over the locations, and is at most `K` times
Lebesgue measure whenever every expected interval count is at most `K` times the length.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.Counting
open MeasureTheory Set
open scoped ENNReal NNReal
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- Expected unnormalized finite eigenvalue intensity, retaining every multiplicity. -/
def finiteSpectralIntensity (P : Measure Ω) (locations : Ω → Fin d → ℝ) : Measure ℝ :=
  ∑ i : Fin d, Measure.map (fun ω => locations ω i) P

/-- Finite multiplicity count in an arbitrary spectral set. -/
def finiteSpectralCount (locations : Ω → Fin d → ℝ) (A : Set ℝ) (ω : Ω) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => locations ω i ∈ A)).card

theorem finiteSpectralIntensity_isFiniteMeasure (P : Measure Ω) [IsFiniteMeasure P]
    (locations : Ω → Fin d → ℝ) : IsFiniteMeasure (finiteSpectralIntensity P locations) := by
  unfold finiteSpectralIntensity
  infer_instance

attribute [instance] finiteSpectralIntensity_isFiniteMeasure

/-- Measurable spectral sets give measurable finite multiplicity counts. -/
theorem measurable_finiteSpectralCount (locations : Ω → Fin d → ℝ)
    (hlocations : ∀ i, Measurable (fun ω => locations ω i)) (A : Set ℝ) (hA : MeasurableSet A) :
    Measurable (finiteSpectralCount locations A) := by
  classical
  have heq : finiteSpectralCount locations A =
      fun ω => ∑ i : Fin d, if locations ω i ∈ A then 1 else 0 := by
    funext ω
    simp [finiteSpectralCount, Finset.sum_boole]
  rw [heq]
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite (hA.preimage (hlocations i)) measurable_const measurable_const

omit [MeasurableSpace Ω] in
/-- A `d`-point spectrum has at most `d` points in any set, including collisions. -/
theorem finiteSpectralCount_le (locations : Ω → Fin d → ℝ) (A : Set ℝ) (ω : Ω) :
    finiteSpectralCount locations A ω ≤ d := by
  classical
  unfold finiteSpectralCount
  exact (Finset.card_filter_le _ _).trans_eq (by simp)

/-- Finite expected intensity has exactly mass `d` for a probability sample law. -/
theorem finiteSpectralIntensity_univ (P : Measure Ω) [IsProbabilityMeasure P]
    (locations : Ω → Fin d → ℝ) (hlocations : ∀ i, Measurable (fun ω => locations ω i)) :
    finiteSpectralIntensity P locations univ = (d : ℝ≥0∞) := by
  simp [finiteSpectralIntensity, Measure.map_apply (hlocations _) MeasurableSet.univ]

/-- Exact nonnegative intensity integral equals expectation of the eigenvalue sum. -/
theorem lintegral_finiteSpectralIntensity (P : Measure Ω) (locations : Ω → Fin d → ℝ)
    (hlocations : ∀ i, Measurable (fun ω => locations ω i))
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x ∂finiteSpectralIntensity P locations = ∫⁻ ω, ∑ i : Fin d, f (locations ω i) ∂P := by
  rw [finiteSpectralIntensity, lintegral_finsetSum_measure]
  simp_rw [lintegral_map hf (hlocations _)]
  rw [lintegral_finsetSum]
  intro i _
  exact hf.comp (hlocations i)

/-- Every Borel intensity mass is exactly the expected multiplicity count. -/
theorem finiteSpectralIntensity_apply (P : Measure Ω) (locations : Ω → Fin d → ℝ)
    (hlocations : ∀ i, Measurable (fun ω => locations ω i)) (A : Set ℝ) (hA : MeasurableSet A) :
    finiteSpectralIntensity P locations A = ∫⁻ ω, (finiteSpectralCount locations A ω : ℝ≥0∞) ∂P := by
  rw [← lintegral_indicator_one hA]
  change (∫⁻ x, A.indicator (fun _ : ℝ => (1 : ℝ≥0∞)) x ∂finiteSpectralIntensity P locations) = _
  rw [lintegral_finiteSpectralIntensity P locations hlocations _ (measurable_const.indicator hA)]
  apply lintegral_congr
  intro ω
  simp [finiteSpectralCount, Set.indicator, Finset.sum_boole]

/-- The real-valued finite count is integrable, by the bound `d`. -/
theorem integrable_finiteSpectralCount (P : Measure Ω) [IsFiniteMeasure P]
    (locations : Ω → Fin d → ℝ) (hlocations : ∀ i, Measurable (fun ω => locations ω i))
    (A : Set ℝ) (hA : MeasurableSet A) :
    Integrable (fun ω => (finiteSpectralCount locations A ω : ℝ)) P := by
  have hm : Measurable (fun ω => (finiteSpectralCount locations A ω : ℝ)) :=
    (measurable_from_nat : Measurable (fun n : ℕ => (n : ℝ))).comp
      (measurable_finiteSpectralCount locations hlocations A hA)
  apply (integrable_const (d : ℝ)).mono hm.aestronglyMeasurable
  filter_upwards with ω
  have hc : (0 : ℝ) ≤ (finiteSpectralCount locations A ω : ℝ) := Nat.cast_nonneg _
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
  simp only [Real.norm_eq_abs, abs_of_nonneg hc, abs_of_nonneg hd]
  exact_mod_cast finiteSpectralCount_le locations A ω

/-- Intensity mass equals `ENNReal.ofReal` of the real expected count. -/
theorem finiteSpectralIntensity_apply_eq_ofReal_integral (P : Measure Ω) [IsFiniteMeasure P]
    (locations : Ω → Fin d → ℝ) (hlocations : ∀ i, Measurable (fun ω => locations ω i))
    (A : Set ℝ) (hA : MeasurableSet A) :
    finiteSpectralIntensity P locations A = ENNReal.ofReal (∫ ω, (finiteSpectralCount locations A ω : ℝ) ∂P) := by
  rw [finiteSpectralIntensity_apply P locations hlocations A hA]
  symm
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_finiteSpectralCount P locations hlocations A hA)
    (Filter.Eventually.of_forall fun _ => Nat.cast_nonneg _)]
  apply lintegral_congr
  intro ω
  simp

/-- Expected-count interval estimates imply full Borel intensity domination. -/
theorem finiteSpectralIntensity_le_volume_of_expectedCount_le
    (P : Measure Ω) [IsFiniteMeasure P] (locations : Ω → Fin d → ℝ)
    (hlocations : ∀ i, Measurable (fun ω => locations ω i)) (K : ℝ) (hK : 0 ≤ K)
    (hcount : ∀ a b : ℝ, a ≤ b →
      (∫ ω, (finiteSpectralCount locations (Icc a b) ω : ℝ) ∂P) ≤ K * (b - a)) :
    finiteSpectralIntensity P locations ≤ ENNReal.ofReal K • (volume : Measure ℝ) := by
  apply intensity_le_volume_of_Icc_le _ K hK
  intro a b hab
  rw [finiteSpectralIntensity_apply_eq_ofReal_integral P locations hlocations _ measurableSet_Icc]
  exact ENNReal.ofReal_le_ofReal (hcount a b hab)

/-- Bochner integration against the intensity equals the expected finite sum.
Only intensity-integrability is required; every sample-side summand is derived integrable. -/
theorem integral_finiteSpectralIntensity {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [CompleteSpace V]
    (P : Measure Ω) (locations : Ω → Fin d → ℝ) (hlocations : ∀ i, Measurable (fun ω => locations ω i))
    (f : ℝ → V) (hf : Integrable f (finiteSpectralIntensity P locations)) :
    ∫ x, f x ∂finiteSpectralIntensity P locations = ∫ ω, ∑ i : Fin d, f (locations ω i) ∂P := by
  have hi (i : Fin d) : Integrable f (Measure.map (fun ω => locations ω i) P) :=
    (integrable_finsetSum_measure.mp hf) i (Finset.mem_univ i)
  have hsample (i : Fin d) : Integrable (fun ω => f (locations ω i)) P :=
    (hi i).comp_measurable (hlocations i)
  rw [finiteSpectralIntensity, integral_finsetSum_measure (fun i _ => hi i)]
  simp_rw [integral_map (hlocations _).aemeasurable (hi _).aestronglyMeasurable]
  rw [integral_finsetSum Finset.univ (fun i _ => hsample i)]

end BlockBand.Counting
