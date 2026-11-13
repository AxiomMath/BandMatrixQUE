module

public import BlockBand.Critical.RelativeVectors.Angular.GapStop
public import BlockBand.Palm.MomentFlow.BridgeBrownian
public import BlockBand.Palm.RelativeLocalizationLabels

/-!
# The measurable simple-spectrum set

* `simpleRatSet F a c`: the paths `ω` with a uniform positive lower bound `1/(m+1)` on all gaps
  of `λ = flowEigenvalue F a ω` at the times `{a, c} ∪ (ℚ ∩ [a, c])`.
* `measurableSet_simpleRatSet`: for `a ≤ c` it is `pathSigma F a a c`-measurable (countable
  operations on the path eigenvalues).
* `mem_simpleRatSet_iff`: for Hermitian `F`, `a ≤ c` and a sample with Hermitian `ω.1` (so that
  `σ ↦ λ(σ)` is continuous and sorted), `ω ∈ simpleRatSet F a c` iff the spectrum is simple on all
  of `[a, c]` (`∀ σ ∈ [a, c], StrictMono (λ(σ))`); compactness gives a uniform gap and density of
  the rationals transports it back.
* `hermProj_mem_simpleRatSet_iff`, `ae_mem_simpleRatSet_iff`: the same for `hermProj ω` (every
  sample) and for `ω` itself (`flowLaw`-a.s., `hermProj_ae_eq`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors.RelativeDuhamel

open MeasureTheory Set Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Palm.MomentFlow

variable {N : ℕ}

/-- **The switch set** `S₀`: some `m` bounds every gap of `λ = flowEigenvalue F a ω` below by
`1/(m+1)` at the times `{a, c} ∪ (ℚ ∩ [a, c])`. -/
def simpleRatSet (F : Matrix (Fin N) (Fin N) ℂ) (a c : ℝ) : Set (FlowSample N) :=
  {ω | ∃ m : ℕ, ∀ σ ∈ ({a, c} ∪ {σ | σ ∈ Icc a c ∧ ∃ q : ℚ, (q : ℝ) = σ} : Set ℝ),
    ∀ i j : Fin N, i ≠ j →
      1 / ((m : ℝ) + 1) ≤ |flowEigenvalue F a ω σ i - flowEigenvalue F a ω σ j|}

/-- The test times are countable. -/
theorem countable_ratTimes (a c : ℝ) :
    ({a, c} ∪ {σ | σ ∈ Icc a c ∧ ∃ q : ℚ, (q : ℝ) = σ} : Set ℝ).Countable :=
  ((Set.countable_singleton c).insert a).union
    ((Set.countable_range ((↑) : ℚ → ℝ)).mono fun _ hx => by
      obtain ⟨-, q, hq⟩ := hx
      exact ⟨q, hq⟩)

/-- For `a ≤ c` the test times lie in `[a, c]`. -/
theorem ratTimes_subset_Icc {a c : ℝ} (hac : a ≤ c) :
    ({a, c} ∪ {σ | σ ∈ Icc a c ∧ ∃ q : ℚ, (q : ℝ) = σ} : Set ℝ) ⊆ Icc a c := by
  rintro σ (hσ | ⟨hσ, -⟩)
  · rcases hσ with rfl | hσ
    · exact ⟨le_rfl, hac⟩
    · rw [mem_singleton_iff] at hσ; subst hσ; exact ⟨hac, le_rfl⟩
  · exact hσ

/-- **Measurability of the switch set.** For `a ≤ c`, `simpleRatSet F a c` is
`pathSigma F a a c`-measurable. -/
theorem measurableSet_simpleRatSet (F : Matrix (Fin N) (Fin N) ℂ) {a c : ℝ} (hac : a ≤ c) :
    MeasurableSet[pathSigma F a a c] (simpleRatSet F a c) := by
  have e : simpleRatSet F a c = ⋃ m : ℕ,
      ⋂ σ ∈ ({a, c} ∪ {σ | σ ∈ Icc a c ∧ ∃ q : ℚ, (q : ℝ) = σ} : Set ℝ),
        ⋂ i : Fin N, ⋂ j : Fin N, ⋂ (_ : i ≠ j),
          {ω : FlowSample N | 1 / ((m : ℝ) + 1) ≤
            |flowEigenvalue F a ω σ i - flowEigenvalue F a ω σ j|} := by
    ext ω
    simp only [simpleRatSet, mem_ofPred_eq, mem_iUnion, mem_iInter]
  rw [e]
  refine MeasurableSet.iUnion fun m => MeasurableSet.biInter (countable_ratTimes a c)
    fun σ hσ => MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ => ?_
  have hσ' := ratTimes_subset_Icc hac hσ
  let _ : MeasurableSpace (FlowSample N) := pathSigma F a a c
  have hi : Measurable fun ω : FlowSample N => flowEigenvalue F a ω σ i :=
    measurable_flowEigenvalue_pathSigma F a a c hσ' i
  have hj : Measurable fun ω : FlowSample N => flowEigenvalue F a ω σ j :=
    measurable_flowEigenvalue_pathSigma F a a c hσ' j
  exact (hi.sub hj).abs measurableSet_Ici

/-- The flow matrix of a sample with Hermitian `ω.1` is Hermitian. -/
theorem flowMatrix_isHermitian_of {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (a : ℝ)
    {ω : FlowSample N} (hω : ω.1.IsHermitian) (σ : ℝ) : (flowMatrix F a ω σ).IsHermitian :=
  (hF.add hω).add (hermitianBrownian_isHermitian _ _)

/-- For Hermitian `F` and `ω.1`, every ordered flow eigenvalue is continuous in time. -/
theorem continuous_flowEigenvalue {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (a : ℝ)
    {ω : FlowSample N} (hω : ω.1.IsHermitian) (k : Fin N) :
    Continuous fun σ => flowEigenvalue F a ω σ k := by
  have e : (fun σ => flowEigenvalue F a ω σ k) =
      fun σ => dysonEigenvalue N (flowMatrix F a ω σ) k.rev := by
    funext σ
    exact freshEigenvalue_eq_dyson (flowMatrix_isHermitian_of hF a hω σ) k
  rw [e]
  exact (Angular.continuous_dysonEigenvalue k.rev).comp (continuous_flowMatrix F a ω)

/-- A continuous function `≥ δ` at `a` and at the rationals of `[a, c]` is `≥ δ` on `[a, c]`. -/
theorem ge_on_Icc_of_rat_Icc {φ : ℝ → ℝ} (hφ : Continuous φ) {a c δ : ℝ} (hac : a ≤ c)
    (ha : δ ≤ φ a) (h : ∀ q : ℚ, (q : ℝ) ∈ Icc a c → δ ≤ φ q) : ∀ x ∈ Icc a c, δ ≤ φ x := by
  have hS : IsClosed {x : ℝ | δ ≤ φ x} := isClosed_le continuous_const hφ
  rcases hac.eq_or_lt with hac' | hlt
  · intro x hx
    rw [show x = a from le_antisymm (hac' ▸ hx.2) hx.1]
    exact ha
  · have hsub : Ioo a c ∩ range ((↑) : ℚ → ℝ) ⊆ {x : ℝ | δ ≤ φ x} := by
      rintro x ⟨hx, q, rfl⟩
      exact h q (Ioo_subset_Icc_self hx)
    have h1 : Ioo a c ⊆ closure (Ioo a c ∩ range ((↑) : ℚ → ℝ)) :=
      Rat.denseRange_cast.open_subset_closure_inter isOpen_Ioo
    have h2 : Icc a c ⊆ {x : ℝ | δ ≤ φ x} := by
      rw [← closure_Ioo hlt.ne]
      exact closure_minimal (h1.trans (closure_minimal hsub hS)) hS
    exact fun x hx => h2 hx

/-- **The switch set is the simple-spectrum set on Hermitian samples.** For Hermitian `F`,
`a ≤ c` and `ω` with Hermitian `ω.1`: `ω ∈ simpleRatSet F a c` iff the spectrum of the flow is
simple at every time of `[a, c]`. -/
theorem mem_simpleRatSet_iff {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a c : ℝ}
    (hac : a ≤ c) {ω : FlowSample N} (hω : ω.1.IsHermitian) :
    ω ∈ simpleRatSet F a c ↔ ∀ σ ∈ Icc a c, StrictMono (flowEigenvalue F a ω σ) := by
  have hcont := fun k => continuous_flowEigenvalue hF a hω k
  have hgapc : ∀ i j : Fin N,
      Continuous fun σ => |flowEigenvalue F a ω σ i - flowEigenvalue F a ω σ j| :=
    fun i j => ((hcont i).sub (hcont j)).abs
  have hmono : ∀ σ, Monotone (flowEigenvalue F a ω σ) := fun σ =>
    BlockBand.Palm.RelativeLocalization.freshEigenvalue_monotone
      (flowMatrix_isHermitian_of hF a hω σ)
  constructor
  · rintro ⟨m, hm⟩ σ hσ
    refine (hmono σ).strictMono_of_injective fun i j hij => ?_
    by_contra hne
    have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    have := ge_on_Icc_of_rat_Icc (hgapc i j) hac (hm a (by simp) i j hne)
      (fun q hq => hm q (Or.inr ⟨hq, q, rfl⟩) i j hne) σ hσ
    rw [hij, sub_self, abs_zero] at this
    linarith
  · intro h
    have hpair : ∀ p : Fin N × Fin N, ∃ m : ℕ, p.1 ≠ p.2 → ∀ σ ∈ Icc a c,
        1 / ((m : ℝ) + 1) ≤ |flowEigenvalue F a ω σ p.1 - flowEigenvalue F a ω σ p.2| := by
      rintro ⟨i, j⟩
      by_cases hij : i = j
      · exact ⟨0, fun h' => absurd hij h'⟩
      · obtain ⟨x0, hx0, hmin⟩ := (isCompact_Icc (a := a) (b := c)).exists_isMinOn
          ⟨a, le_rfl, hac⟩ (hgapc i j).continuousOn
        have hpos : 0 < |flowEigenvalue F a ω x0 i - flowEigenvalue F a ω x0 j| :=
          abs_pos.2 (sub_ne_zero.2 fun e => hij ((h x0 hx0).injective e))
        obtain ⟨m, hm⟩ := exists_nat_one_div_lt hpos
        exact ⟨m, fun _ σ hσ => hm.le.trans (isMinOn_iff.1 hmin σ hσ)⟩
    choose m hm using hpair
    refine ⟨Finset.univ.sup m, fun σ hσ i j hij => ?_⟩
    have hσ' := ratTimes_subset_Icc hac hσ
    have hle : (m (i, j) : ℝ) ≤ (Finset.univ.sup m : ℕ) := by
      exact_mod_cast Finset.le_sup (f := m) (Finset.mem_univ (i, j))
    calc 1 / ((Finset.univ.sup m : ℕ) + 1 : ℝ) ≤ 1 / ((m (i, j) : ℝ) + 1) :=
          one_div_le_one_div_of_le (by positivity) (by linarith)
      _ ≤ _ := hm (i, j) hij σ hσ'

/-- **Corollary for `hermProj`.** For every sample, `hermProj ω ∈ simpleRatSet F a c` iff the
flow of `hermProj ω` has simple spectrum on `[a, c]`. -/
theorem hermProj_mem_simpleRatSet_iff {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    {a c : ℝ} (hac : a ≤ c) (ω : FlowSample N) :
    hermProj ω ∈ simpleRatSet F a c ↔
      ∀ σ ∈ Icc a c, StrictMono (flowEigenvalue F a (hermProj ω) σ) :=
  mem_simpleRatSet_iff hF hac (hermPart_isHermitian ω.1)

/-- **Almost-sure form.** `flowLaw`-a.s., `ω ∈ simpleRatSet F a c` iff the spectrum is simple on
`[a, c]`. -/
theorem ae_mem_simpleRatSet_iff {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a c : ℝ}
    (hac : a ≤ c) :
    ∀ᵐ ω ∂flowLaw N a,
      (ω ∈ simpleRatSet F a c ↔ ∀ σ ∈ Icc a c, StrictMono (flowEigenvalue F a ω σ)) := by
  filter_upwards [hermProj_ae_eq (N := N) a] with ω hω
  have := hermProj_mem_simpleRatSet_iff hF hac ω
  rwa [hω] at this

end BlockBand.Critical.RelativeVectors.RelativeDuhamel
