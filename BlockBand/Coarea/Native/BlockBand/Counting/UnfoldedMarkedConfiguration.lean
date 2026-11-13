module

public import BlockBand.Coarea.Native.BlockBand.Counting.MarkedConfigurationSpace

/-!
# The finite unfolded BlockGUE configuration

This module connects the ordered spectrum of a deformed finite BlockGUE
matrix to `FiniteMarkedConfiguration`.  The eigenvector-profile
mark is not constructed as a measurable random variable here, so the mark is
`Unit`: this is the unmarked unfolded eigenvalue configuration, represented as a
trivially marked one.

The spectral coordinate is the normalization
`L * ρ * (λᵢ - e)`.  We prove measurability of the full finite configuration,
construct its pushforward probability law, identify its local counts with the
existing `eigenCount`, and, for positive `L` and `ρ`, identify the symmetric
unfolded window `[-R,R]` with `BlockGUE.unfoldedIntervalCount`.  Consequently
the open local-count events in the finite configuration space are
measurable events of the BlockGUE sample.

This fixed-dimensional labeled law is not a locally finite point measure and
does not put different matrix dimensions in a common state space.  Thus it
does not supply the varying-size vague topology or the compact-containment
hypothesis of the counting theorem.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CoareaNative.BlockBand

open MeasureTheory

universe u

/-- The sample probability measure packaged from the probability-measure field
of a BlockGUE law. -/
def BlockGUE.sampleProbability
    {k : ℕ} {d : Fin k → ℕ} {hd : ∀ j, 0 < d j}
    (M : BlockGUE.Law.{u} d hd) : ProbabilityMeasure M.Ω :=
  ⟨M.P, inferInstance⟩

/-- The deformed BlockGUE matrix is a measurable Hermitian-matrix-valued
random variable. -/
theorem BlockGUE.measurable_deformed
    {k : ℕ} {d : Fin k → ℕ} {hd : ∀ j, 0 < d j}
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d)) :
    Measurable (fun ω => BlockGUE.deformed M A₀ ω) := by
  apply Measurable.subtype_mk
  rw [Matrix.measurable_iff]
  intro x y
  exact measurable_const.add (M.measurable_entry x y)

/-- The finite unfolded ordered spectrum, with the trivial mark
`Unit`.  No eigenvector or eigenvector-profile selection is hidden here. -/
def BlockGUE.unfoldedMarkedConfiguration
    {k : ℕ} {d : Fin k → ℕ} {hd : ∀ j, 0 < d j}
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (e L ρ : ℝ) (ω : M.Ω) :
    FiniteMarkedConfiguration (Fintype.card (BlockGUE.Index d)) Unit :=
  fun i => (BlockGUE.unfoldedLocation M A₀ e L ρ ω i, ())

/-- The finite unfolded trivially marked configuration is measurable. -/
theorem BlockGUE.measurable_unfoldedMarkedConfiguration
    {k : ℕ} {d : Fin k → ℕ} {hd : ∀ j, 0 < d j}
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (e L ρ : ℝ) :
    Measurable (BlockGUE.unfoldedMarkedConfiguration M A₀ e L ρ) := by
  rw [measurable_pi_iff]
  intro i
  change Measurable fun ω =>
    (BlockGUE.unfoldedLocation M A₀ e L ρ ω i, ())
  apply Measurable.prodMk
  · unfold BlockGUE.unfoldedLocation
    have heig : Measurable (fun ω =>
        orderedEigenvalue (BlockGUE.deformed M A₀ ω) i) :=
      (measurable_orderedEigenvalue i).comp
        (BlockGUE.measurable_deformed M A₀)
    exact (measurable_const.mul measurable_const).mul
      (heig.sub measurable_const)
  · exact measurable_const

/-- For any Borel spectral window, the finite local count is a measurable
natural-valued function on a finite marked configuration space. -/
theorem measurable_finiteMarkedLocalCount
    {N : ℕ} {Mark : Type u} [MeasurableSpace Mark]
    (U : Set ℝ) (hU : MeasurableSet U) :
    Measurable (finiteMarkedLocalCount (N := N) (Mark := Mark) U) := by
  classical
  change Measurable fun x : FiniteMarkedConfiguration N Mark =>
    (Finset.univ.filter fun i => (x i).1 ∈ U).card
  simp_rw [Finset.card_filter]
  apply Finset.measurable_sum
  intro i _hi
  apply Measurable.ite
  · exact hU.preimage (measurable_fst.comp (measurable_pi_apply i))
  · exact measurable_const
  · exact measurable_const

/-- For a Borel window, every finite local-count superlevel event is
measurable.  Openness requires the stronger open-window hypothesis. -/
theorem measurableSet_finiteMarkedCountGE_of_measurableSet
    {N : ℕ} {Mark : Type u} [MeasurableSpace Mark]
    (U : Set ℝ) (hU : MeasurableSet U) (m : ℕ) :
    MeasurableSet (finiteMarkedCountGE (N := N) (Mark := Mark) U m) := by
  exact measurableSet_Ici.preimage
    (measurable_finiteMarkedLocalCount (N := N) (Mark := Mark) U hU)

/-- The probability law of the finite unfolded trivially marked ordered
spectrum. -/
def BlockGUE.unfoldedMarkedConfigurationLaw
    {k : ℕ} {d : Fin k → ℕ} {hd : ∀ j, 0 < d j}
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (e L ρ : ℝ) :
    ProbabilityMeasure
      (FiniteMarkedConfiguration (Fintype.card (BlockGUE.Index d)) Unit) :=
  (BlockGUE.sampleProbability M).map
    (BlockGUE.unfoldedMarkedConfiguration M A₀ e L ρ)

/-- Local counts of the finite configuration are exactly ordered-eigenvalue
counts in the inverse image of the unfolded window. -/
theorem BlockGUE.finiteMarkedLocalCount_unfoldedMarkedConfiguration
    {k : ℕ} {d : Fin k → ℕ} {hd : ∀ j, 0 < d j}
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (e L ρ : ℝ) (U : Set ℝ) (ω : M.Ω) :
    finiteMarkedLocalCount U
        (BlockGUE.unfoldedMarkedConfiguration M A₀ e L ρ ω) =
      BlockGUE.intervalCount M A₀
        {x | L * ρ * (x - e) ∈ U} ω := by
  rfl

/-- Under positive unfolding slope, the finite-configuration count in
`[-R,R]` is exactly the already formalized unfolded interval count. -/
theorem BlockGUE.finiteMarkedLocalCount_Icc_eq_unfoldedIntervalCount
    {k : ℕ} {d : Fin k → ℕ} {hd : ∀ j, 0 < d j}
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (e L ρ R : ℝ) (hL : 0 < L) (hρ : 0 < ρ) (ω : M.Ω) :
    finiteMarkedLocalCount (Set.Icc (-R) R)
        (BlockGUE.unfoldedMarkedConfiguration M A₀ e L ρ ω) =
      BlockGUE.unfoldedIntervalCount M A₀ e L ρ R ω := by
  classical
  unfold finiteMarkedLocalCount BlockGUE.unfoldedMarkedConfiguration
    BlockGUE.unfoldedLocation BlockGUE.unfoldedIntervalCount
    BlockGUE.intervalCount eigenCount
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Icc]
  have hq : 0 < L * ρ := mul_pos hL hρ
  constructor
  · rintro ⟨hlo, hhi⟩
    constructor
    · have hlo' : -R / (L * ρ) ≤
          orderedEigenvalue (BlockGUE.deformed M A₀ ω) i - e :=
        (div_le_iff₀ hq).2 (by nlinarith)
      calc
        e - R / (L * ρ) = -R / (L * ρ) + e := by ring
        _ ≤ (orderedEigenvalue (BlockGUE.deformed M A₀ ω) i - e) + e :=
          by
            convert add_le_add_right hlo' e using 1 <;> ring
        _ = orderedEigenvalue (BlockGUE.deformed M A₀ ω) i := by ring
    · have hhi' : orderedEigenvalue (BlockGUE.deformed M A₀ ω) i - e ≤
          R / (L * ρ) :=
        (le_div_iff₀ hq).2 (by nlinarith)
      calc
        orderedEigenvalue (BlockGUE.deformed M A₀ ω) i =
            (orderedEigenvalue (BlockGUE.deformed M A₀ ω) i - e) + e := by ring
        _ ≤ R / (L * ρ) + e := by
          convert add_le_add_right hhi' e using 1 <;> ring
        _ = e + R / (L * ρ) := by ring
  · rintro ⟨hlo, hhi⟩
    constructor
    · have hlo0 : -R / (L * ρ) ≤
          orderedEigenvalue (BlockGUE.deformed M A₀ ω) i - e := by
        calc
          -R / (L * ρ) = (e - R / (L * ρ)) - e := by ring
          _ ≤ orderedEigenvalue (BlockGUE.deformed M A₀ ω) i - e :=
            sub_le_sub_right hlo e
      have hlo' := (div_le_iff₀ hq).1 hlo0
      nlinarith
    · have hhi0 : orderedEigenvalue (BlockGUE.deformed M A₀ ω) i - e ≤
          R / (L * ρ) := by
        calc
          orderedEigenvalue (BlockGUE.deformed M A₀ ω) i - e ≤
              (e + R / (L * ρ)) - e := sub_le_sub_right hhi e
          _ = R / (L * ρ) := by ring
      have hhi' := (le_div_iff₀ hq).1 hhi0
      nlinarith

/-- The pushforward law assigns every Borel event its BlockGUE preimage
probability. -/
theorem BlockGUE.unfoldedMarkedConfigurationLaw_apply
    {k : ℕ} {d : Fin k → ℕ} {hd : ∀ j, 0 < d j}
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (e L ρ : ℝ)
    {S : Set (FiniteMarkedConfiguration
      (Fintype.card (BlockGUE.Index d)) Unit)} (hS : MeasurableSet S) :
    (BlockGUE.unfoldedMarkedConfigurationLaw M A₀ e L ρ).toMeasure S =
      M.P ((BlockGUE.unfoldedMarkedConfiguration M A₀ e L ρ) ⁻¹' S) := by
  change Measure.map
    (BlockGUE.unfoldedMarkedConfiguration M A₀ e L ρ) M.P S = _
  exact Measure.map_apply
    (BlockGUE.measurable_unfoldedMarkedConfiguration M A₀ e L ρ) hS

/-- Open finite-configuration local-count events pull back to measurable
BlockGUE sample events, with their probability computed by the concrete
pushforward law. -/
theorem BlockGUE.unfoldedMarkedConfigurationLaw_countGE
    {k : ℕ} {d : Fin k → ℕ} {hd : ∀ j, 0 < d j}
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (e L ρ : ℝ) {U : Set ℝ} (hU : MeasurableSet U) (m : ℕ) :
    (BlockGUE.unfoldedMarkedConfigurationLaw M A₀ e L ρ).toMeasure
        (finiteMarkedCountGE U m) =
      M.P {ω | m ≤ BlockGUE.intervalCount M A₀
        {x | L * ρ * (x - e) ∈ U} ω} := by
  rw [BlockGUE.unfoldedMarkedConfigurationLaw_apply M A₀ e L ρ
    (measurableSet_finiteMarkedCountGE_of_measurableSet
      (Mark := Unit) U hU m)]
  congr 1

/-- The probability of a symmetric closed-window count event under the
concrete finite configuration law is exactly the corresponding BlockGUE
unfolded-count probability. -/
theorem BlockGUE.unfoldedMarkedConfigurationLaw_countGE_Icc
    {k : ℕ} {d : Fin k → ℕ} {hd : ∀ j, 0 < d j}
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (e L ρ R : ℝ) (hL : 0 < L) (hρ : 0 < ρ) (m : ℕ) :
    (BlockGUE.unfoldedMarkedConfigurationLaw M A₀ e L ρ).toMeasure
        (finiteMarkedCountGE (Set.Icc (-R) R) m) =
      M.P {ω | m ≤ BlockGUE.unfoldedIntervalCount M A₀ e L ρ R ω} := by
  rw [BlockGUE.unfoldedMarkedConfigurationLaw_apply M A₀ e L ρ
    (measurableSet_finiteMarkedCountGE_of_measurableSet
      (Mark := Unit) (Set.Icc (-R) R) measurableSet_Icc m)]
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq]
  change (m ≤ finiteMarkedLocalCount (Set.Icc (-R) R)
    (BlockGUE.unfoldedMarkedConfiguration M A₀ e L ρ ω)) ↔ _
  rw [BlockGUE.finiteMarkedLocalCount_Icc_eq_unfoldedIntervalCount
    M A₀ e L ρ R hL hρ ω]

/-- The PSSS first-moment Markov bound transported to the finite
configuration law.  This is a local-count tail, but it is not an
escape-tail bound for the labeled compact-containment sets. -/
theorem psss_unfoldedMarkedConfiguration_count_tail
    (input : PSSSInput.{u})
    {k : ℕ} {d : Fin k → ℕ} (hd : ∀ j, 0 < d j)
    (M : BlockGUE.Law.{u} d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (e L ρ R : ℝ) (hL : 0 < L) (hρ : 0 < ρ) (hR : 0 ≤ R)
    (m : ℕ) :
    (m : ℝ) *
        (BlockGUE.unfoldedMarkedConfigurationLaw M A₀ e L ρ).toMeasure.real
          (finiteMarkedCountGE (Set.Icc (-R) R) m) ≤
      input.C * (Fintype.card (BlockGUE.Index d) : ℝ) *
        ((e + R / (L * ρ)) - (e - R / (L * ρ))) := by
  rw [Measure.real, BlockGUE.unfoldedMarkedConfigurationLaw_countGE_Icc
    M A₀ e L ρ R hL hρ m]
  have hevent :
      {ω | (m : ℝ) ≤
        (BlockGUE.unfoldedIntervalCount M A₀ e L ρ R ω : ℝ)} =
      {ω | m ≤ BlockGUE.unfoldedIntervalCount M A₀ e L ρ R ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro h <;> exact_mod_cast h
  rw [← hevent]
  unfold BlockGUE.unfoldedIntervalCount
  simpa only [Measure.real] using
    (psss_count_tail input hd M A₀
      (e - R / (L * ρ)) (e + R / (L * ρ)) (m : ℝ) (by
        have hq : 0 < L * ρ := mul_pos hL hρ
        have : 0 ≤ R / (L * ρ) := div_nonneg hR hq.le
        linarith))

end CoareaNative.BlockBand
