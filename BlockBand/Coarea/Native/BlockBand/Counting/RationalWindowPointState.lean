module

public import BlockBand.Coarea.Native.BlockBand.Counting.CountingTheoremInstantiation

/-!
# Rational-window local point states

This module replaces the empty determining family used by the first common-state
precursor with the countable family of rational closed intervals, cut down to
each exhaustion window.  Every finite unfolded configuration embeds in the
resulting state space, and the restriction mass is exactly the number of labels
in the corresponding rational window.

The final results isolate a diagonal tightness argument.  Coordinatewise
compact support and summable uniform coordinate-mass tails produce compact
sets in the product state space and hence a weakly convergent subsequence.  As
in the underlying bundled state-space construction, compactness is conditional
on continuity of sharp restrictions and of the chosen restriction-mass maps;
these interfaces exclude boundary-charging pathologies and are not silently
postulated.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace CoareaNative.BlockBand

open MeasureTheory Filter
open scoped Topology NNReal ENNReal

attribute [local instance] Classical.propDecidable

/-- The rational interval indexed by `q`, intersected with the `n`th closed
spectral exhaustion window.  The `Unit` factor is the paper's currently
formalized trivial mark. -/
def rationalWindowDeterminingFamily (n : ℕ) (q : ℚ × ℚ) :
    Set (MarkedSpectralSpace Unit) :=
  (Set.Icc (max (-(n : ℝ)) (q.1 : ℝ))
    (min (n : ℝ) (q.2 : ℝ))) ×ˢ Set.univ

/-- Common bundled state carrying all rational-window restriction counts. -/
abbrev RationalWindowPointState :=
  LocalPointMeasureStateSpace Unit (ℚ × ℚ)
    rationalWindowDeterminingFamily

/-- Every rational determining window is Borel. -/
theorem measurableSet_rationalWindowDeterminingFamily (n : ℕ) (q : ℚ × ℚ) :
    MeasurableSet (rationalWindowDeterminingFamily n q) :=
  measurableSet_Icc.prod MeasurableSet.univ

/-- The `n`th rational determining sets are local: they lie in the
`n`th exhaustion window. -/
theorem rationalWindowDeterminingFamily_subset_markedSpectralWindow
    (n : ℕ) (q : ℚ × ℚ) :
    rationalWindowDeterminingFamily n q ⊆ markedSpectralWindow Unit n := by
  rintro ⟨x, u⟩ ⟨hx, -⟩
  exact ⟨⟨le_trans (le_max_left _ _) hx.1,
    le_trans hx.2 (min_le_left _ _)⟩, Set.mem_univ u⟩

/-- A restriction of a finite counting measure to a measurable set has the
natural mass given by the number of labels which lie in that set. -/
theorem finiteMarkedCountingMeasure_restrict_mass_eq_card
    {N : ℕ} (x : FiniteMarkedConfiguration N Unit)
    {S : Set (MarkedSpectralSpace Unit)} (hS : MeasurableSet S) :
    ((finiteMarkedCountingMeasure x).restrict S).mass =
      (Finset.univ.filter fun i => x i ∈ S).card := by
  classical
  apply ENNReal.coe_injective
  rw [FiniteMeasure.ennreal_mass]
  change ((∑ i : Fin N, Measure.dirac (x i)).restrict S) Set.univ =
    ((↑(Finset.univ.filter fun i => x i ∈ S).card : NNReal) : ENNReal)
  rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  simp only [Measure.dirac_apply' _ hS, Set.indicator, Pi.one_apply]
  simp only [Finset.sum_boole]
  norm_cast

/-- In particular, all measurable restrictions of a finite counting measure
have natural-number mass. -/
theorem finiteMarkedCountingMeasure_restrict_mass_mem_range
    {N : ℕ} (x : FiniteMarkedConfiguration N Unit)
    {S : Set (MarkedSpectralSpace Unit)} (hS : MeasurableSet S) :
    ((finiteMarkedCountingMeasure x).restrict S).mass ∈
      Set.range ((↑) : ℕ → NNReal) := by
  refine ⟨(Finset.univ.filter fun i => x i ∈ S).card, ?_⟩
  exact (finiteMarkedCountingMeasure_restrict_mass_eq_card x hS).symm

/-- Restricting the `n`th local encoding once more to a rational local window
is the same as restricting the original counting measure directly. -/
theorem finiteMarkedLocalWindowEncoding_restrict_rationalWindow
    {N : ℕ} (x : FiniteMarkedConfiguration N Unit)
    (n : ℕ) (q : ℚ × ℚ) :
    (finiteMarkedLocalWindowEncoding x n).restrict
        (rationalWindowDeterminingFamily n q) =
      (finiteMarkedCountingMeasure x).restrict
        (rationalWindowDeterminingFamily n q) := by
  ext S hS
  change ((finiteMarkedCountingMeasure x : Measure _).restrict
      (markedSpectralWindow Unit n)).restrict
        (rationalWindowDeterminingFamily n q) S =
    (finiteMarkedCountingMeasure x : Measure _).restrict
      (rationalWindowDeterminingFamily n q) S
  rw [Measure.restrict_restrict_of_subset
    (rationalWindowDeterminingFamily_subset_markedSpectralWindow n q)]

/-- Exact rational-window count in a finite local encoding. -/
theorem finiteMarkedLocalWindowEncoding_rationalWindow_mass_eq_card
    {N : ℕ} (x : FiniteMarkedConfiguration N Unit)
    (n : ℕ) (q : ℚ × ℚ) :
    ((finiteMarkedLocalWindowEncoding x n).restrict
      (rationalWindowDeterminingFamily n q)).mass =
      (Finset.univ.filter fun i =>
        x i ∈ rationalWindowDeterminingFamily n q).card := by
  rw [finiteMarkedLocalWindowEncoding_restrict_rationalWindow]
  exact finiteMarkedCountingMeasure_restrict_mass_eq_card x
    (measurableSet_rationalWindowDeterminingFamily n q)

/-- A finite configuration of arbitrary cardinality embeds into one common
state space carrying all rational-window counts. -/
def finiteMarkedRationalWindowPointState
    {N : ℕ} (x : FiniteMarkedConfiguration N Unit) :
    LocalPointMeasureStateSpace Unit (ℚ × ℚ)
      rationalWindowDeterminingFamily :=
  ⟨finiteMarkedLocalWindowEncoding x,
    finiteMarkedLocalWindowEncoding_consistent x,
    by
      intro n q
      rw [finiteMarkedLocalWindowEncoding_restrict_rationalWindow]
      exact finiteMarkedCountingMeasure_restrict_mass_mem_range x
        (measurableSet_rationalWindowDeterminingFamily n q)⟩

/-- The underlying local-window encoding of the rational-window state is the
original finite counting encoding. -/
theorem finiteMarkedRationalWindowPointState_encoding
    {N : ℕ} (x : FiniteMarkedConfiguration N Unit) :
    (finiteMarkedRationalWindowPointState x).encoding =
      finiteMarkedLocalWindowEncoding x := rfl

/-- The rational restriction mass stored by the common point state is exactly
the corresponding finite label count. -/
theorem finiteMarkedRationalWindowPointState_window_mass_eq_card
    {N : ℕ} (x : FiniteMarkedConfiguration N Unit)
    (n : ℕ) (q : ℚ × ℚ) :
    (((finiteMarkedRationalWindowPointState x).window n).restrict
      (rationalWindowDeterminingFamily n q)).mass =
      (Finset.univ.filter fun i =>
        x i ∈ rationalWindowDeterminingFamily n q).card :=
  finiteMarkedLocalWindowEncoding_rationalWindow_mass_eq_card x n q

/-- The finite unfolded BlockGUE spectrum, at any matrix dimension, as
a rational-window point state in the common target type. -/
def BlockGUE.unfoldedRationalWindowPointState
    {k : ℕ} {d : Fin k → ℕ} {hd : ∀ j, 0 < d j}
    (M : BlockGUE.Law d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (e L ρ : ℝ) (ω : M.Ω) : RationalWindowPointState :=
  finiteMarkedRationalWindowPointState
    (BlockGUE.unfoldedMarkedConfiguration M A₀ e L ρ ω)

/-- Every rational restriction of the unfolded BlockGUE state has exactly the
number of ordered unfolded eigenvalues lying in that rational local window. -/
theorem BlockGUE.unfoldedRationalWindowPointState_window_mass_eq_card
    {k : ℕ} {d : Fin k → ℕ} {hd : ∀ j, 0 < d j}
    (M : BlockGUE.Law d hd)
    (A₀ : HermitianMatrix (BlockGUE.Index d))
    (e L ρ : ℝ) (ω : M.Ω) (n : ℕ) (q : ℚ × ℚ) :
    (((BlockGUE.unfoldedRationalWindowPointState M A₀ e L ρ ω).window n).restrict
      (rationalWindowDeterminingFamily n q)).mass =
      (Finset.univ.filter fun i =>
        BlockGUE.unfoldedMarkedConfiguration M A₀ e L ρ ω i ∈
          rationalWindowDeterminingFamily n q).card :=
  finiteMarkedRationalWindowPointState_window_mass_eq_card
    (BlockGUE.unfoldedMarkedConfiguration M A₀ e L ρ ω) n q

/-- Coordinatewise mass caps, with the canonical compact support supplied by
the closed exhaustion windows. -/
def rationalWindowPointCompactSet (C : ℕ → NNReal) :
    Set (LocalPointMeasureStateSpace Unit (ℚ × ℚ)
      rationalWindowDeterminingFamily) :=
  localPointMeasureCompactContainment (sets := rationalWindowDeterminingFamily)
    C (markedSpectralWindow Unit)

/-- Every consistent local state is supported on its own exhaustion window.
This follows from consistency at `n ≤ n`; it is not an additional compact
containment assumption. -/
theorem localPointMeasureStateSpace_window_compl_eq_zero
    (ν : LocalPointMeasureStateSpace Unit (ℚ × ℚ)
      rationalWindowDeterminingFamily) (n : ℕ) :
    (ν.window n : Measure (MarkedSpectralSpace Unit))
      (markedSpectralWindow Unit n)ᶜ = 0 := by
  have hrestrict := ν.2.1 n n le_rfl
  have hmeasure :
      (ν.window n : Measure (MarkedSpectralSpace Unit)).restrict
          (markedSpectralWindow Unit n) =
        (ν.window n : Measure (MarkedSpectralSpace Unit)) :=
    congrArg (fun μ : FiniteMeasure (MarkedSpectralSpace Unit) =>
      (μ : Measure (MarkedSpectralSpace Unit))) hrestrict
  calc
    (ν.window n : Measure _) (markedSpectralWindow Unit n)ᶜ =
        ((ν.window n : Measure _).restrict
          (markedSpectralWindow Unit n)) (markedSpectralWindow Unit n)ᶜ := by
      rw [hmeasure]
    _ = 0 := by
      rw [Measure.restrict_apply
        (measurableSet_markedSpectralWindow Unit n).compl]
      simp

/-- Membership in the diagonal compact set is exactly the family of coordinate
mass bounds; compact support is automatic from consistency. -/
theorem mem_rationalWindowPointCompactSet_iff
    (C : ℕ → NNReal)
    (ν : LocalPointMeasureStateSpace Unit (ℚ × ℚ)
      rationalWindowDeterminingFamily) :
    ν ∈ rationalWindowPointCompactSet C ↔
      ∀ n, (ν.window n).mass ≤ C n := by
  change ν.1 ∈ localWindowCompactContainment C
      (markedSpectralWindow Unit) ↔ _
  rw [mem_localWindowCompactContainment_iff]
  constructor
  · intro h n
    exact (h n).1
  · intro h n
    refine ⟨h n, ?_⟩
    apply ENNReal.coe_injective
    rw [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    exact localPointMeasureStateSpace_window_compl_eq_zero ν n

/-- The complement of a diagonal mass-cap set is covered by the union of its
coordinate mass-tail events. -/
theorem compl_rationalWindowPointCompactSet_subset_iUnion_massTail
    (C : ℕ → NNReal) :
    (rationalWindowPointCompactSet C)ᶜ ⊆
      ⋃ n, {ν | (C n : ENNReal) < ((ν.window n).mass : ENNReal)} := by
  intro ν hν
  by_contra h
  apply hν
  rw [mem_rationalWindowPointCompactSet_iff]
  intro n
  have hn : ¬ (C n : ENNReal) < ((ν.window n).mass : ENNReal) := by
    intro hlt
    apply h
    exact Set.mem_iUnion.2 ⟨n, hlt⟩
  exact_mod_cast le_of_not_gt hn

/-- Diagonal compact sets are compact under the exact
boundary-regularity interfaces of the bundled state-space construction. -/
theorem isCompact_rationalWindowPointCompactSet
    (hsharp : SharpWindowRestrictionMapsContinuous (Mark := Unit))
    (hmass : LocalRestrictionMassMapsContinuous
      rationalWindowDeterminingFamily)
    (C : ℕ → NNReal) :
    IsCompact (rationalWindowPointCompactSet C) := by
  apply isCompact_localPointMeasureCompactContainment
    rationalWindowDeterminingFamily hsharp hmass C
    (markedSpectralWindow Unit)
  intro n
  exact isCompact_markedSpectralWindow_inter_marks n isCompact_univ

/-- Summable coordinate mass tails give the required uniform complement bound
for the diagonal compact set. -/
theorem measure_compl_rationalWindowPointCompactSet_le_tsum
    (μs : ℕ → ProbabilityMeasure
      (LocalPointMeasureStateSpace Unit (ℚ × ℚ)
        rationalWindowDeterminingFamily))
    (C : ℕ → ℕ → NNReal) (u : ℕ → ℕ → ENNReal)
    (htail : ∀ i m n, (μs i : Measure _)
      {ν : RationalWindowPointState |
        (C m n : ENNReal) < ((ν.window n).mass : ENNReal)} ≤ u m n)
    (i m : ℕ) :
    (μs i : Measure _) ((rationalWindowPointCompactSet (C m))ᶜ) ≤
      ∑' n, u m n := by
  calc
    (μs i : Measure _) ((rationalWindowPointCompactSet (C m))ᶜ) ≤
        (μs i : Measure _) (⋃ n,
          {ν : RationalWindowPointState |
            (C m n : ENNReal) < ((ν.window n).mass : ENNReal)}) :=
      measure_mono (compl_rationalWindowPointCompactSet_subset_iUnion_massTail (C m))
    _ ≤ ∑' n, (μs i : Measure _)
          {ν : RationalWindowPointState |
            (C m n : ENNReal) < ((ν.window n).mass : ENNReal)} :=
      measure_iUnion_le _
    _ ≤ ∑' n, u m n := ENNReal.tsum_le_tsum fun n => htail i m n

/-- A summable diagonal schedule of uniform local-count tails makes the whole
family of rational-window point-state laws tight.  Thus no pre-supplied compact
containment sets are required. -/
theorem isTightMeasureSet_range_rationalWindowPointState_of_diagonalTails
    [T2Space (LocalPointMeasureStateSpace Unit (ℚ × ℚ)
      rationalWindowDeterminingFamily)]
    [BorelSpace (LocalPointMeasureStateSpace Unit (ℚ × ℚ)
      rationalWindowDeterminingFamily)]
    (μs : ℕ → ProbabilityMeasure
      (LocalPointMeasureStateSpace Unit (ℚ × ℚ)
        rationalWindowDeterminingFamily))
    (hsharp : SharpWindowRestrictionMapsContinuous (Mark := Unit))
    (hmass : LocalRestrictionMassMapsContinuous
      rationalWindowDeterminingFamily)
    (C : ℕ → ℕ → NNReal) (u : ℕ → ℕ → ENNReal)
    (hu : Tendsto (fun m => ∑' n, u m n) atTop (𝓝 0))
    (htail : ∀ i m n, (μs i : Measure _)
      {ν : RationalWindowPointState |
        (C m n : ENNReal) < ((ν.window n).mass : ENNReal)} ≤ u m n) :
    IsTightMeasureSet
      (Set.range (ProbabilityMeasure.toMeasure ∘ μs)) := by
  apply isTightMeasureSet_range_of_compact_exhaustion μs
    (fun m => rationalWindowPointCompactSet (C m))
    (fun m => isCompact_rationalWindowPointCompactSet hsharp hmass (C m))
    (fun m => ∑' n, u m n) hu
  intro i m
  exact measure_compl_rationalWindowPointCompactSet_le_tsum μs C u htail i m

/-- Prokhorov plus the diagonal rational-window tail argument produces a
weakly convergent subsequence in the common state space. -/
theorem exists_weaklyConvergent_subsequence_rationalWindowPointState
    [T2Space (LocalPointMeasureStateSpace Unit (ℚ × ℚ)
      rationalWindowDeterminingFamily)]
    [BorelSpace (LocalPointMeasureStateSpace Unit (ℚ × ℚ)
      rationalWindowDeterminingFamily)]
    [FirstCountableTopology (ProbabilityMeasure
      (LocalPointMeasureStateSpace Unit (ℚ × ℚ)
        rationalWindowDeterminingFamily))]
    (μs : ℕ → ProbabilityMeasure
      (LocalPointMeasureStateSpace Unit (ℚ × ℚ)
        rationalWindowDeterminingFamily))
    (hsharp : SharpWindowRestrictionMapsContinuous (Mark := Unit))
    (hmass : LocalRestrictionMassMapsContinuous
      rationalWindowDeterminingFamily)
    (C : ℕ → ℕ → NNReal) (u : ℕ → ℕ → ENNReal)
    (hu : Tendsto (fun m => ∑' n, u m n) atTop (𝓝 0))
    (htail : ∀ i m n, (μs i : Measure _)
      {ν : RationalWindowPointState |
        (C m n : ENNReal) < ((ν.window n).mass : ENNReal)} ≤ u m n) :
    ∃ μ : ProbabilityMeasure
        (LocalPointMeasureStateSpace Unit (ℚ × ℚ)
          rationalWindowDeterminingFamily),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (μs ∘ φ) atTop (𝓝 μ) := by
  apply exists_weaklyConvergent_subsequence_of_isTight μs
  exact isTightMeasureSet_range_rationalWindowPointState_of_diagonalTails
    μs hsharp hmass C u hu htail

end CoareaNative.BlockBand
