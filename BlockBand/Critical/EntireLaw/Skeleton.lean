module

public import BlockBand.Critical.EntireLaw.PhasePassage
public import BlockBand.Critical.EntireLaw.ConeBound
public import BlockBand.Critical.EntireLaw.Moments
public import BlockBand.Critical.GlobalSource.Uniqueness
public import BlockBand.Critical.DecoratedSine.AtZero
public import BlockBand.Critical.JointRecovery.Assembly
public import BlockBand.Critical.GlobalSource.ReplacementProof

/-!
# The entire law: the reduction skeleton `entireLaw_of`

`entireLaw_of` derives `EntireLawContract` from `GlobalGaussianSourceStatement`,
`MatrixClosingStatement` and the five steps `FiniteGaussianMomentIdentity`, `CollarSourceRemoval`,
`ClosedSourceLimitStep`, `EntireTightness` and `InverseMomentDetermination`: along a critical
sequence the finite mixed inverse moments converge to the closed-source values, the finite laws
are tight, every cluster point is cone-bounded and carries the hierarchy values, and these values
determine the law.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.EntireLaw

open MeasureTheory Filter Topology Set
open BlockBand.Critical.Entire
open BlockBand.Internal.Contracts.CriticalEntire
open BlockBand.Critical.GlobalSource

/-- **Moment chain along one critical sequence**: the finite
mixed inverse moments converge to the value `E exp{-i Σ σ_j 𝒯_jj}` of every realization `C` of
`𝖢_J(0)`, for the global probe law `κ` of the global Gaussian source statement. Uses
`FiniteGaussianMomentIdentity`, `CollarSourceRemoval`, `ClosedSourceLimitStep` and
`MatrixClosingStatement`. -/
theorem tendsto_finiteMoment_value (hMC : BlockBand.Critical.MatrixClosing.MatrixClosingStatement)
    (hO1 : FiniteGaussianMomentIdentity) (hO2 : CollarSourceRemoval) (hO4 : ClosedSourceLimitStep)
    {b E : ℝ} (hb : 0 < b) (hb' : b < 1 / 2) (hE : -2 < E ∧ E < 2) (τ : PositiveRatio) {k : ℕ}
    {q : Fin k → C(Torus, ℝ)} (hq : IsProfileFamily q) {J : ℕ} (y : Fin J → Fin (k + 1) → ℝ)
    (σ : Fin J → ℤˣ) (hy : ∀ j a, 0 ≤ y j a) (s : CriticalSequence τ.1)
    (R : ∀ j, FiniteRealization (s.parameters b hb hb' j))
    {κ : Measure (Matrix (Fin J) (Fin J) ℂ)}
    (hκ : IsGlobalProbeLaw b E τ.1 (probeProfile q y) κ ∧
      IsGlobalProbeCriticalLimit b E τ.1 (probeProfile q y) κ)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (Ξ : Ω → VaguePointMeasure (ℝ × (Fin J → ℂ)))
    (C : Ω → Matrix (Fin J) (Fin J) ℂ) (hC : IsCanonicalCauchyAtZero J P Ξ C) :
    Tendsto (fun j => mixedInverseMoment (finiteEntireLaw (R j) E (fullProfile q)) y σ) atTop
      (𝓝 (∫ K, ∫ ω, closedSourcePhase σ (closedSourceMatrix b E K (C ω)) ∂P ∂κ)) := by
  have hQ := probeProfile_nonneg hq hy
  have hκP : IsProbabilityMeasure κ := hκ.1.1
  have hring := isRingProbeCriticalLimit_of_global hb hb' hκ.2
  have h4 := hO4 hMC b E hb hb' hE τ J (probeProfile q y) hQ κ hκP hring σ Ω inferInstance P Ξ C
    hC s R
  have h2 := tendsto_phase_sub_of_collarSourceRemoval hO2 hb hb' hE τ hQ σ s R
  have h := h2.add h4
  rw [zero_add] at h
  refine h.congr fun j => ?_
  rw [hO1 _ (R j) E k q hq J y σ hy]
  ring

/-- **Every cluster value of the finite laws satisfies the determining hierarchy value**: if
along a non-trivial filter `L ≤ atTop` the laws of `D_W` (any critical sequence, any realizations)
converge to `ν`, then `ClosedSourceMomentValue b E τ (probeProfile q y) σ (mixedInverseMoment ν y σ)`.
Uses `GlobalGaussianSourceStatement`, `MatrixClosingStatement`, `FiniteGaussianMomentIdentity`,
`CollarSourceRemoval` and `ClosedSourceLimitStep`. -/
theorem closedSourceMomentValue_of_tendsto (hGS : GlobalGaussianSourceStatement)
    (hMC : BlockBand.Critical.MatrixClosing.MatrixClosingStatement)
    (hO1 : FiniteGaussianMomentIdentity) (hO2 : CollarSourceRemoval) (hO4 : ClosedSourceLimitStep)
    {b E : ℝ} (hb : 0 < b) (hb' : b < 1 / 2) (hE : -2 < E ∧ E < 2) (τ : PositiveRatio) {k : ℕ}
    {q : Fin k → C(Torus, ℝ)} (hq : IsProfileFamily q) (s : CriticalSequence τ.1)
    (R : ∀ j, FiniteRealization (s.parameters b hb hb' j)) {L : Filter ℕ} [L.NeBot]
    (hL : L ≤ atTop) {ν : RandomEntire (k + 1)}
    (hν : Tendsto (fun j => finiteEntireLaw (R j) E (fullProfile q)) L (𝓝 ν))
    {J : ℕ} (y : Fin J → Fin (k + 1) → ℝ) (σ : Fin J → ℤˣ) (hy : ∀ j a, 0 ≤ y j a) :
    ClosedSourceMomentValue b E τ.1 (probeProfile q y) σ (mixedInverseMoment ν y σ) := by
  have hQ := probeProfile_nonneg hq hy
  obtain ⟨κ₀, hκ₀, -⟩ := hGS b E hb hb' hE τ J (probeProfile q y) hQ
  have hfin : ∀ j, HasInverseConeBound (finiteEntireLaw (R j) E (fullProfile q)) := fun j =>
    hasInverseConeBound_finiteEntireLaw (R j) E (fullProfile_nonneg hq)
  have hνc : HasInverseConeBound ν := hasInverseConeBound_of_tendsto hν hfin
  refine ⟨⟨κ₀, hκ₀.1⟩, BlockBand.Critical.DecoratedSine.exists_isCanonicalCauchyAtZero J, ?_⟩
  intro κ hκ Ω mΩ P Ξ C hC
  obtain rfl : κ₀ = κ := isGlobalProbeLaw_unique hκ₀.1 hκ
  have h1 := tendsto_finiteMoment_value hMC hO1 hO2 hO4 hb hb' hE τ hq y σ hy s R hκ₀ Ω P Ξ C hC
  have h2 := tendsto_mixedInverseMoment hν hfin hνc y σ hy
  exact tendsto_nhds_unique (h1.mono_left hL) h2

/-- Compact closure of the finite laws along a critical sequence (`EntireTightness` and Prokhorov). -/
theorem isCompact_closure_range_finiteEntireLaw (hO5 : EntireTightness) {b E : ℝ} (hb : 0 < b)
    (hb' : b < 1 / 2) (hE : -2 < E ∧ E < 2) (τ : PositiveRatio) {k : ℕ}
    {q : Fin k → C(Torus, ℝ)} (hq : IsProfileFamily q) (s : CriticalSequence τ.1)
    (R : ∀ j, FiniteRealization (s.parameters b hb hb' j)) :
    IsCompact (closure (range fun j => finiteEntireLaw (R j) E (fullProfile q))) := by
  apply isCompact_closure_of_isTightMeasureSet
  have ht := hO5 b E hb hb' hE τ k q hq s R
  convert ht using 1
  ext μ
  constructor
  · rintro ⟨ν, ⟨j, rfl⟩, rfl⟩; exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩; exact ⟨_, ⟨j, rfl⟩, rfl⟩

/-- A cluster point of the finite laws is cone-bounded and carries the hierarchy values. -/
theorem isDeterminingHierarchyLaw_of_mapClusterPt (hGS : GlobalGaussianSourceStatement)
    (hMC : BlockBand.Critical.MatrixClosing.MatrixClosingStatement)
    (hO1 : FiniteGaussianMomentIdentity) (hO2 : CollarSourceRemoval) (hO4 : ClosedSourceLimitStep)
    {b E : ℝ} (hb : 0 < b) (hb' : b < 1 / 2) (hE : -2 < E ∧ E < 2) (τ : PositiveRatio) {k : ℕ}
    {q : Fin k → C(Torus, ℝ)} (hq : IsProfileFamily q) (s : CriticalSequence τ.1)
    (R : ∀ j, FiniteRealization (s.parameters b hb hb' j)) {ν : RandomEntire (k + 1)}
    (hν : MapClusterPt ν atTop fun j => finiteEntireLaw (R j) E (fullProfile q)) :
    IsDeterminingHierarchyLaw b E τ q ν := by
  obtain ⟨U, hU, hUt⟩ := mapClusterPt_iff_ultrafilter.mp hν
  refine ⟨hasInverseConeBound_of_tendsto hUt fun j =>
    hasInverseConeBound_finiteEntireLaw (R j) E (fullProfile_nonneg hq), fun J y σ hy => ?_⟩
  exact closedSourceMomentValue_of_tendsto hGS hMC hO1 hO2 hO4 hb hb' hE τ hq s R hU hUt y σ hy

/-- **The entire law from `GlobalGaussianSourceStatement`, `MatrixClosingStatement` and the
steps `FiniteGaussianMomentIdentity`, `CollarSourceRemoval`, `ClosedSourceLimitStep`,
`EntireTightness`, `InverseMomentDetermination`.** -/
theorem entireLaw_of (hGS : GlobalGaussianSourceStatement)
    (hMC : BlockBand.Critical.MatrixClosing.MatrixClosingStatement)
    (hO1 : FiniteGaussianMomentIdentity) (hO2 : CollarSourceRemoval)
    (hO4 : ClosedSourceLimitStep) (hO5 : EntireTightness) (hO6 : InverseMomentDetermination) :
    EntireLawContract := by
  refine ⟨?_, ?_, entireLaw_coneBound, hO6⟩
  · intro b E hb hb' hE τ k q hq
    obtain ⟨s₀⟩ := BlockBand.Critical.Assembly.exists_criticalSequence τ.1 τ.2
    let R₀ : ∀ j, FiniteRealization (s₀.parameters b hb hb' j) := fun j =>
      (BlockBand.Model.Construction.nonempty_finiteRealization _).some
    obtain ⟨μ₀, -, hμ₀⟩ := (isCompact_closure_range_finiteEntireLaw hO5 hb hb' hE τ hq s₀ R₀).exists_mapClusterPt
      (f := atTop) (u := fun j => finiteEntireLaw (R₀ j) E (fullProfile q))
      (le_principal_iff.mpr (mem_map.mpr (Eventually.of_forall fun j =>
        subset_closure (mem_range_self j))))
    have hH₀ := isDeterminingHierarchyLaw_of_mapClusterPt hGS hMC hO1 hO2 hO4 hb hb' hE τ hq s₀ R₀
      hμ₀
    refine ⟨μ₀, fun s R => ?_⟩
    refine (isCompact_closure_range_finiteEntireLaw hO5 hb hb' hE τ hq s R).tendsto_nhds_of_unique_mapClusterPt
      (Eventually.of_forall fun j => subset_closure (mem_range_self j)) fun ν _ hν => ?_
    have hH := isDeterminingHierarchyLaw_of_mapClusterPt hGS hMC hO1 hO2 hO4 hb hb' hE τ hq s R hν
    exact hO6 (k + 1) ν μ₀ hH.1 hH₀.1 fun J y σ hy =>
      BlockBand.Critical.JointRecovery.closedSourceMomentValue_unique (hH.2 J y σ hy) (hH₀.2 J y σ hy)
  · intro b E hb hb' hE τ k q hq μ hμ J y σ hy
    obtain ⟨s₀⟩ := BlockBand.Critical.Assembly.exists_criticalSequence τ.1 τ.2
    let R₀ : ∀ j, FiniteRealization (s₀.parameters b hb hb' j) := fun j =>
      (BlockBand.Model.Construction.nonempty_finiteRealization _).some
    exact closedSourceMomentValue_of_tendsto hGS hMC hO1 hO2 hO4 hb hb' hE τ hq s₀ R₀ le_rfl
      (hμ s₀ R₀) y σ hy

/-- **The entire law theorem** (`EntireLawContract`) from `ComplexSourceLawContract`,
`ComplexSourceLimitAlongSequences`, `MatrixClosingStatement` and the steps
`FiniteGaussianMomentIdentity`, `CollarSourceRemoval`, `ClosedSourceLimitStep`, `EntireTightness`,
`InverseMomentDetermination` (composition of `entireLaw_of` with
`GlobalSource.globalGaussianSource_holds_of_sourceLimit`). -/
theorem entireLaw_of_sourceLimit
    (hCS : BlockBand.Internal.Contracts.TransmissionLaws.ComplexSourceLawContract)
    (hA : ComplexSourceLimitAlongSequences)
    (hMC : BlockBand.Critical.MatrixClosing.MatrixClosingStatement)
    (hO1 : FiniteGaussianMomentIdentity) (hO2 : CollarSourceRemoval)
    (hO4 : ClosedSourceLimitStep) (hO5 : EntireTightness) (hO6 : InverseMomentDetermination) :
    EntireLawContract :=
  entireLaw_of (globalGaussianSource_holds_of_sourceLimit hCS hA) hMC hO1 hO2 hO4 hO5 hO6

end BlockBand.Critical.EntireLaw
