module

public import BlockBand.Critical.JointRecovery.Identification
public import BlockBand.Critical.JointRecovery.ReadoutDetermination
public import BlockBand.Counting.PhysicalMarkedTightness
public import BlockBand.Counting.SimpleSpectralLimits
public import BlockBand.Critical.Assembly.CriticalOfContracts
public import BlockBand.Internal.Contracts.Inputs

/-!
# Joint recovery from the entire law

`jointRecovery_of_entireLaw` derives `CriticalEntire.JointRecoveryContract` from
* `CriticalEntire.EntireLawContract` (all four clauses),
* the PSSS input `BlockBand.External.PSSS.SourceContract` (the premise of the counting
  results `Counting.criticalSequence_markedLaws_isTight`,
  `Counting.finiteRealization_markedLaw_Ioo_twoPoint_bound`,
  `Counting.criticalSequence_marked_weakLimit_hasSimple`), and
* `Inputs.CriticalUnitIntensity` (the critical density).

Domain: every `0 < b < 1/2`, `-2 < E < 2`; for each `τ > 0` one law on `MarkedPointMeasure`
(marked vague topology, weak marks on `P(𝕋)`), the physical unfolding `u = Nρ(E)(λ - E)`; every
critical sequence (`W → ∞`, `n/W → τ`, both parities, no rate) and every finite realization.
Order of limits: `W → ∞` only. Proof: tightness and Prokhorov give cluster points; each cluster
point is identified, for every finite nonnegative family, through the root/derivative extraction
from the unique entire law; the readout tests determine the marked law, so all cluster points
along all sequences coincide.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Critical.JointRecovery

open Filter Topology Set MeasureTheory
open BlockBand.Critical.Entire
open BlockBand.Internal.Contracts.CriticalEntire

/-- `ClosedSourceMomentValue` determines its value. -/
theorem closedSourceMomentValue_unique {b E τ : ℝ} {J : ℕ} {Q : Fin J → C(Torus, ℝ)}
    {σ : Fin J → ℤˣ} {v v' : ℂ} (hv : ClosedSourceMomentValue b E τ Q σ v)
    (hv' : ClosedSourceMomentValue b E τ Q σ v') : v = v' := by
  obtain ⟨⟨κ, hκ⟩, ⟨Ω, mΩ, P, Ξ, C, hC⟩, h⟩ := hv
  obtain ⟨-, -, h'⟩ := hv'
  exact (h κ hκ Ω mΩ P Ξ C hC).symm.trans (h' κ hκ Ω mΩ P Ξ C hC)

/-- Every determining-hierarchy law is the entire limit (the determination clause of the entire law). -/
theorem eq_of_isDeterminingHierarchyLaw (hEL : EntireLawContract) {b E : ℝ} {τ : PositiveRatio}
    {k : ℕ} {q : Fin k → C(Torus, ℝ)} {μ μ' : RandomEntire (k + 1)}
    (hμ : IsDeterminingHierarchyLaw b E τ q μ) (hμ' : IsDeterminingHierarchyLaw b E τ q μ') :
    μ = μ' :=
  hEL.determination (k + 1) μ μ' hμ.1 hμ'.1 fun J y σ hy =>
    closedSourceMomentValue_unique (hμ.2 J y σ hy) (hμ'.2 J y σ hy)

/-- Tightness of the physical marked laws gives compact closure (Prokhorov). -/
theorem isCompact_closure_range_markedLaw (source : BlockBand.External.PSSS.SourceContract.{0})
    {τ : ℝ} (s : CriticalSequence τ) (b E : ℝ) (hb : 0 < b) (hb' : b < 1 / 2)
    (hρ : 0 < Parameters.semicircleDensity E)
    (R : ∀ j, FiniteRealization (s.parameters b hb hb' j)) :
    IsCompact (closure (range fun j => (R j).markedLaw E)) := by
  have := BlockBand.Model.Construction.markedPointMeasure_t2Space
  apply isCompact_closure_of_isTightMeasureSet
  have ht := BlockBand.Counting.criticalSequence_markedLaws_isTight source s b E hb hb' hρ R
  convert ht using 1
  ext μ
  constructor
  · rintro ⟨ν, ⟨j, rfl⟩, rfl⟩; exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩; exact ⟨_, ⟨j, rfl⟩, rfl⟩

/-- **Cluster points exist** along every critical sequence (existence only; identification
is `isReadoutLimit_of_mapClusterPt`): tightness (the counting theorem, from the PSSS input) and Prokhorov. -/
theorem exists_mapClusterPt_markedLaw (source : BlockBand.External.PSSS.SourceContract.{0})
    {τ : ℝ} (s : CriticalSequence τ) (b E : ℝ) (hb : 0 < b) (hb' : b < 1 / 2)
    (hρ : 0 < Parameters.semicircleDensity E)
    (R : ∀ j, FiniteRealization (s.parameters b hb hb' j)) :
    ∃ ν, MapClusterPt ν atTop (fun j => (R j).markedLaw E) := by
  obtain ⟨ν, -, hν⟩ := (isCompact_closure_range_markedLaw source s b E hb hb' hρ R).exists_mapClusterPt
    (f := atTop) (u := fun j => (R j).markedLaw E)
    (le_principal_iff.mpr (mem_map.mpr (Eventually.of_forall fun j =>
      subset_closure (mem_range_self j))))
  exact ⟨ν, hν⟩

/-- The common readout identity of all critical cluster points at ratio `τ`. -/
def IsReadoutLimit (hEL : EntireLawContract) (b E : ℝ) (hb : 0 < b) (hb' : b < 1 / 2)
    (hE : -2 < E ∧ E < 2) (τ : PositiveRatio) (ν : ProbabilityMeasure MarkedPointMeasure) :
    Prop :=
  ∀ (k : ℕ) (q : Fin k → C(Torus, ℝ)) (hq : IsProfileFamily q),
    ∀ f : CompactlySupportedContinuousMap (ℝ × (Fin (k + 1) → ℂ)) ℝ, (∀ z, 0 ≤ f z) →
      readoutLaplace q ν f =
        extractorLaplace E τ.1 (hEL.convergence b E hb hb' hE τ k q hq).choose f

/-- Every cluster point of the physical marked laws along a critical sequence at ratio `τ`
(fixed `0 < b < 1/2`, `|E| < 2`, any realizations) satisfies `IsReadoutLimit`, with the entire
limit chosen from `EntireLawContract.convergence` (which holds along every critical sequence).
Inputs: `EntireLawContract`, PSSS. -/
theorem isReadoutLimit_of_mapClusterPt (hEL : EntireLawContract)
    (source : BlockBand.External.PSSS.SourceContract.{0}) {b E : ℝ} (hb : 0 < b)
    (hb' : b < 1 / 2) (hE : -2 < E ∧ E < 2) (τ : PositiveRatio) (s : CriticalSequence τ.1)
    (R : ∀ j, FiniteRealization (s.parameters b hb hb' j))
    {ν : ProbabilityMeasure MarkedPointMeasure}
    (hν : MapClusterPt ν atTop (fun j => (R j).markedLaw E)) :
    IsReadoutLimit hEL b E hb hb' hE τ ν := by
  intro k q hq f hf
  have hρ := BlockBand.Parameters.semicircleDensity_pos hE
  exact readoutLaplace_eq_of_mapClusterPt source τ.2 s b E hb hb' hρ R q
    ((hEL.convergence b E hb hb' hE τ k q hq).choose_spec s R) f hf hν

/-- Two laws on `MarkedPointMeasure` with the readout identity of `IsReadoutLimit` (same
`b, E, τ`) are equal (`markedLaw_eq_of_readoutLaplace`). Deterministic in the laws. -/
theorem eq_of_isReadoutLimit {hEL : EntireLawContract} {b E : ℝ} {hb : 0 < b}
    {hb' : b < 1 / 2} {hE : -2 < E ∧ E < 2} {τ : PositiveRatio}
    {ν ν' : ProbabilityMeasure MarkedPointMeasure} (h : IsReadoutLimit hEL b E hb hb' hE τ ν)
    (h' : IsReadoutLimit hEL b E hb hb' hE τ ν') : ν = ν' :=
  markedLaw_eq_of_readoutLaplace ν ν' fun k q hq f hf => (h k q hq f hf).trans (h' k q hq f hf).symm

/-- **Convergence along every critical sequence** to any readout limit. -/
theorem tendsto_markedLaw_of_isReadoutLimit (hEL : EntireLawContract)
    (source : BlockBand.External.PSSS.SourceContract.{0}) {b E : ℝ} (hb : 0 < b)
    (hb' : b < 1 / 2) (hE : -2 < E ∧ E < 2) (τ : PositiveRatio)
    {ν : ProbabilityMeasure MarkedPointMeasure} (hν : IsReadoutLimit hEL b E hb hb' hE τ ν)
    (s : CriticalSequence τ.1) (R : ∀ j, FiniteRealization (s.parameters b hb hb' j)) :
    Tendsto (fun j => (R j).markedLaw E) atTop (𝓝 ν) := by
  have hρ := BlockBand.Parameters.semicircleDensity_pos hE
  refine (isCompact_closure_range_markedLaw source s b E hb hb' hρ R).tendsto_nhds_of_unique_mapClusterPt
    (Eventually.of_forall fun j => subset_closure (mem_range_self j)) fun x _ hx => ?_
  exact eq_of_isReadoutLimit (isReadoutLimit_of_mapClusterPt hEL source hb hb' hE τ s R hx) hν

/-- ** from **.
Law: for each `τ > 0` a probability law on the `MarkedPointMeasure` (marked vague
topology: compact spectral tests, weak topology on the marks `P(𝕋)`;
Borel σ-algebra); the
physical laws are those of `Ξ_W` under the exact Gaussian ring law with unfolding
`u = Nρ(E)(λ - E)`.
Domain:
`0 < b < 1/2`, `-2 < E < 2`, `τ > 0`; both parities, every
admissible finite realization.
Quantifier order:
`b, E` first, then one family for all `τ`,
then every critical sequence and realization (`∃!` family).
Order of limits:
`W → ∞` along
every critical sequence at fixed `τ` (`n/W → τ`, no rate).
Uniformity: none in `(b, E, τ)`.
Inputs:
Conclusion:
`JointRecoveryContract` (convergence,
simple spectral locations, unit spectral intensity, root/derivative rule for every finite
nonnegative profile family, uniqueness).
-/
theorem jointRecovery_of_entireLaw (hEL : EntireLawContract)
    (source : BlockBand.External.PSSS.SourceContract.{0})
    (hUI : BlockBand.Internal.Contracts.Inputs.CriticalUnitIntensity) :
    JointRecoveryContract := by
  intro b E hb hb' hE
  have := BlockBand.Model.Construction.markedPointMeasureLaw_t2Space
  have hρ := BlockBand.Parameters.semicircleDensity_pos hE
  have hE2 : E ^ 2 < 4 := by nlinarith [hE.1, hE.2]
  -- canonical sequence and realizations
  have hcan : ∀ τ : PositiveRatio, ∃ ν, IsReadoutLimit hEL b E hb hb' hE τ ν := by
    intro τ
    obtain ⟨s⟩ := BlockBand.Critical.Assembly.exists_criticalSequence τ.1 τ.2
    let R : ∀ j, FiniteRealization (s.parameters b hb hb' j) := fun j =>
      (BlockBand.Model.Construction.nonempty_finiteRealization _).some
    obtain ⟨ν, hν⟩ := exists_mapClusterPt_markedLaw source s b E hb hb' hρ R
    exact ⟨ν, isReadoutLimit_of_mapClusterPt hEL source hb hb' hE τ s R hν⟩
  choose family hfamily using hcan
  have hconv : ∀ (τ : PositiveRatio) (s : CriticalSequence τ.1)
      (R : ∀ j, FiniteRealization (s.parameters b hb hb' j)),
      Tendsto (fun j => (R j).markedLaw E) atTop (𝓝 (family τ)) := fun τ s R =>
    tendsto_markedLaw_of_isReadoutLimit hEL source hb hb' hE τ (hfamily τ) s R
  refine ⟨family, ⟨hconv, ?_, ?_, ?_⟩, ?_⟩
  · intro τ
    obtain ⟨s⟩ := BlockBand.Critical.Assembly.exists_criticalSequence τ.1 τ.2
    let R : ∀ j, FiniteRealization (s.parameters b hb hb' j) := fun j =>
      (BlockBand.Model.Construction.nonempty_finiteRealization _).some
    exact BlockBand.Counting.criticalSequence_marked_weakLimit_hasSimple source s b E hb hb' hρ R
      id (family τ) (hconv τ s R)
  · intro τ
    obtain ⟨s⟩ := BlockBand.Critical.Assembly.exists_criticalSequence τ.1 τ.2
    let R : ∀ j, FiniteRealization (s.parameters b hb hb' j) := fun j =>
      (BlockBand.Model.Construction.nonempty_finiteRealization _).some
    exact hUI τ.1 s τ.2 b E hb hb' hE2 R id strictMono_id (family τ) (hconv τ s R)
  · intro τ k q hq
    have hlim := (hEL.convergence b E hb hb' hE τ k q hq).choose_spec
    have hhier : IsDeterminingHierarchyLaw b E τ q
        (hEL.convergence b E hb hb' hE τ k q hq).choose :=
      ⟨hEL.coneBound b E hb hb' hE τ k q hq _ hlim,
        hEL.characterization b E hb hb' hE τ k q hq _ hlim⟩
    refine ⟨⟨_, hhier⟩, fun μ hμ f hf => ?_⟩
    rw [eq_of_isDeterminingHierarchyLaw hEL hμ hhier]
    exact hfamily τ k q hq f hf
  · intro family' hfam'
    funext τ
    obtain ⟨s⟩ := BlockBand.Critical.Assembly.exists_criticalSequence τ.1 τ.2
    let R : ∀ j, FiniteRealization (s.parameters b hb hb' j) := fun j =>
      (BlockBand.Model.Construction.nonempty_finiteRealization _).some
    exact tendsto_nhds_unique (hfam'.convergence τ s R) (hconv τ s R)

end BlockBand.Critical.JointRecovery
