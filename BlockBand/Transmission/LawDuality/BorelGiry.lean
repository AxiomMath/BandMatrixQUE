module

public import BlockBand.Transmission.LawDuality.ModulusZero

/-!
# The weak topology on `FiniteMeasure [0,1]`: moments, second countability, Borel = Giry

* `momentVec ν = (∫ t^j dν)_j : ℕ → ℝ`; `continuous_momentVec`, `measurable_momentVec`.
* `tendsto_of_tendsto_moments`: convergence of all moments (including the mass `j = 0`)
  implies weak convergence (Weierstrass with the mass bound; any filter).
* **`isInducing_momentVec`**: the weak topology is induced by the moment vector.
* `instSecondCountableFiniteMeasureUnit`, `instPseudoMetrizableFiniteMeasureUnit` (instances):
  the weak topology is second countable and pseudo-metrizable.
* **`borel_eq_giry`**: `borel (FiniteMeasure [0,1]) = ` the Giry σ-algebra; `≤` from the
  inducing map into `ℝ^ℕ`, `≥` from `measurable_of_logTransform` and the weak continuity of
  the log-transforms. Hence the instance `instBorelSpaceFiniteMeasureUnit`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Transmission.DualBoundary
open scoped NNReal ENNReal BoundedContinuousFunction

/-- The moment vector `(m_j(ν))_{j ∈ ℕ}`. -/
def momentVec (ν : FiniteMeasure unitInterval) : ℕ → ℝ := fun j => moment j ν

/-- `s ↦ s^j` as a bounded continuous function on `[0,1]`. -/
def powBCF' (j : ℕ) : unitInterval →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨fun s => (s : ℝ) ^ j, continuous_subtype_val.pow j⟩

theorem continuous_moment (j : ℕ) : Continuous (moment j) :=
  FiniteMeasure.continuous_integral_boundedContinuousFunction (powBCF' j)

theorem continuous_momentVec : Continuous momentVec := continuous_pi continuous_moment

theorem measurable_moment (j : ℕ) : Measurable (moment j) :=
  measurable_moment_of (ν := id) (fun k => measurable_logTransform (evalPoint_pos k).le) j

theorem measurable_momentVec : Measurable momentVec :=
  measurable_pi_iff.2 measurable_moment

theorem moment_zero_nonneg (ν : FiniteMeasure unitInterval) : 0 ≤ moment 0 ν := by
  rw [← real_univ_eq_moment_zero]; exact measureReal_nonneg

/-- **Moments determine weak convergence** (for any filter). -/
theorem tendsto_of_tendsto_moments {γ : Type*} {F : Filter γ} {νs : γ → FiniteMeasure unitInterval}
    {ν : FiniteMeasure unitInterval}
    (h : ∀ j, Tendsto (fun i => moment j (νs i)) F (𝓝 (moment j ν))) : Tendsto νs F (𝓝 ν) := by
  rw [FiniteMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  rw [Metric.tendsto_nhds]
  intro e he
  have hm0 := moment_zero_nonneg ν
  set e' : ℝ := e / (3 * (moment 0 ν + 2)) with he'_def
  have he' : 0 < e' := by positivity
  obtain ⟨p, hp⟩ := exists_polynomial_near_continuousMap 0 1 f.toContinuousMap e' he'
  let Q : FiniteMeasure unitInterval → ℝ := fun μ =>
    ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * moment i μ
  have hQ : Tendsto (fun i => Q (νs i)) F (𝓝 (Q ν)) :=
    tendsto_finsetSum _ fun i _ => (h i).const_mul _
  have h1 : ∀ᶠ i in F, |Q (νs i) - Q ν| < e / 3 := by
    have := (Metric.tendsto_nhds.1 hQ) (e / 3) (by positivity)
    simpa [Real.dist_eq] using this
  have h2 : ∀ᶠ i in F, moment 0 (νs i) < moment 0 ν + 1 :=
    (h 0).eventually (gt_mem_nhds (by linarith))
  filter_upwards [h1, h2] with i hi1 hi2
  rw [Real.dist_eq]
  have ha : |∫ x, f x ∂(νs i : Measure unitInterval) - Q (νs i)| ≤ e' * moment 0 (νs i) := by
    rw [← real_univ_eq_moment_zero]; exact abs_integral_sub_poly_le (νs i) hp
  have hb : |∫ x, f x ∂(ν : Measure unitInterval) - Q ν| ≤ e' * moment 0 ν := by
    rw [← real_univ_eq_moment_zero]; exact abs_integral_sub_poly_le ν hp
  have hc : e' * moment 0 (νs i) ≤ e' * (moment 0 ν + 1) :=
    mul_le_mul_of_nonneg_left hi2.le he'.le
  have hd : e' * (moment 0 ν + 1) + e' * moment 0 ν < 2 * e / 3 := by
    rw [he'_def, ← mul_add, div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have := abs_sub_le (∫ x, f x ∂(νs i : Measure unitInterval)) (Q (νs i))
    (∫ x, f x ∂(ν : Measure unitInterval))
  have := abs_sub_le (Q (νs i)) (Q ν) (∫ x, f x ∂(ν : Measure unitInterval))
  rw [abs_sub_comm] at hb
  linarith

/-- **The weak topology on `FiniteMeasure [0,1]` is induced by the moment vector.** -/
theorem isInducing_momentVec : Topology.IsInducing momentVec := by
  rw [Topology.isInducing_iff_nhds]
  intro ν
  refine le_antisymm (continuous_momentVec.tendsto ν).le_comap ?_
  have hc : Tendsto momentVec (comap momentVec (𝓝 (momentVec ν))) (𝓝 (momentVec ν)) :=
    tendsto_comap
  exact tendsto_id'.1 (tendsto_of_tendsto_moments fun j =>
    ((continuous_apply j).tendsto (momentVec ν)).comp hc)

instance instSecondCountableFiniteMeasureUnit :
    SecondCountableTopology (FiniteMeasure unitInterval) :=
  isInducing_momentVec.secondCountableTopology

instance instPseudoMetrizableFiniteMeasureUnit :
    TopologicalSpace.PseudoMetrizableSpace (FiniteMeasure unitInterval) :=
  isInducing_momentVec.pseudoMetrizableSpace

theorem continuous_logTransform_of {x : ℝ} (hx : 0 ≤ x) :
    Continuous fun ν : FiniteMeasure unitInterval => logTransform x ν := by
  have e : (fun ν : FiniteMeasure unitInterval => logTransform x ν) =
      fun ν : FiniteMeasure unitInterval => -∫ t, ratioBCF hx le_rfl zero_lt_one t ∂(ν : Measure unitInterval) := by
    funext ν
    unfold logTransform logKernel
    rw [integral_neg]
    rfl
  rw [e]
  exact (FiniteMeasure.continuous_integral_boundedContinuousFunction _).neg

/-- **Borel = Giry on `FiniteMeasure [0,1]`.** -/
theorem borel_eq_giry :
    borel (FiniteMeasure unitInterval) = (inferInstance : MeasurableSpace (FiniteMeasure unitInterval)) := by
  refine le_antisymm ?_ ?_
  · refine MeasurableSpace.generateFrom_le fun U hU => ?_
    obtain ⟨V, hV, rfl⟩ := isInducing_momentVec.isOpen_iff.1 hU
    exact measurable_momentVec hV.measurableSet
  · have hid : @Measurable _ _ (borel (FiniteMeasure unitInterval)) _
        (id : FiniteMeasure unitInterval → FiniteMeasure unitInterval) :=
      @measurable_of_logTransform _ (borel _) id fun k =>
        (continuous_logTransform_of (evalPoint_pos k).le).borel_measurable
    simpa [MeasurableSpace.comap_id] using hid.comap_le

instance instBorelSpaceFiniteMeasureUnit : BorelSpace (FiniteMeasure unitInterval) :=
  ⟨borel_eq_giry.symm⟩

/-- Bounded continuous tests of finitely many random finite measures integrate through the
joint (Giry) law. -/
theorem integral_bcf_eq_of_map_eq {k : ℕ} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {Y : Ω → Fin k → FiniteMeasure unitInterval}
    {Y' : Ω' → Fin k → FiniteMeasure unitInterval} (hY : Measurable Y) (hY' : Measurable Y')
    (h : P.map Y = P'.map Y') (Φ : BoundedContinuousFunction (Fin k → FiniteMeasure unitInterval) ℝ) :
    ∫ ω, Φ (Y ω) ∂P = ∫ ω, Φ (Y' ω) ∂P' := by
  rw [← integral_map hY.aemeasurable Φ.continuous.aestronglyMeasurable,
    ← integral_map hY'.aemeasurable Φ.continuous.aestronglyMeasurable, h]

end BlockBand.Transmission.LawDuality
