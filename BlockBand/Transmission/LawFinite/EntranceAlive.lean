module

public import BlockBand.Transmission.LawFinite.EntranceStep
public import BlockBand.Transmission.Generator.Discrete

/-!
# Alive events and the first-exit decomposition of the entrance event

* `aliveSet b E κ W K d r = {K ≤ q_i, δ₀,i ≤ d for 1 ≤ i ≤ r}`; it is a past event at length
  `r` (`measurableSet_aliveSet_sigma`, `exists_past_aliveSet`), via `Bridge.pathNearSchur_adapted`;
* **`crossing_subset`**: `{∃ r ≤ N, q_r < K} ⊆ {q₁ < K} ∪ ⋃_{1≤j<N} (A_j ∩ {q_{j+1} < K}) ∪
  ⋃_{r≤N} {δ₀,r > d}` (first index of `{q < K} ∪ {δ₀ > d}`, by `Nat.find`). This replaces the
  paper's stopping time.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawFinite

open Matrix MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open scoped ENNReal

variable {W : ℕ}

/-- The alive event `A_r = {K ≤ q_i, δ₀,i ≤ d for 1 ≤ i ≤ r}` (`A_0` is everything). -/
def aliveSet (b E : ℝ) (κ : ℝ → ℝ) (W : ℕ) (K d : ℝ) (r : ℕ) : Set (GrowthPath W) :=
  {ω | ∀ i, 1 ≤ i → i ≤ r → K ≤ passiveMass b E (pathNearSchur b E κ W i ω) ∧
    jetDistance0 b E (pathNearSchur b E κ W i ω) ≤ d}

theorem measurableSet_aliveSet_sigma (b E : ℝ) (κ : ℝ → ℝ) (K d : ℝ) (r : ℕ) :
    MeasurableSet[growthSigma W r] (aliveSet b E κ W K d r) := by
  have : aliveSet b E κ W K d r = ⋂ i ∈ Finset.Icc 1 r,
      ({ω | K ≤ passiveMass b E (pathNearSchur b E κ W i ω)} ∩
        {ω | jetDistance0 b E (pathNearSchur b E κ W i ω) ≤ d}) := by
    ext ω; simp only [aliveSet, Set.mem_iInter, Finset.mem_Icc, Set.mem_inter_iff,
      Set.mem_ofPred_eq]
    exact ⟨fun h i hi => h i hi.1 hi.2, fun h i h1 h2 => h i ⟨h1, h2⟩⟩
  rw [this]
  refine Finset.measurableSet_biInter _ fun i hi => ?_
  have hX := (pathNearSchur_adapted b E κ W i).mono
    (Generator.growthSigma_mono (Finset.mem_Icc.mp hi).2) le_rfl
  exact (measurableSet_le measurable_const ((SourceMixing.measurable_passiveMass b E).comp hX)).inter
    (measurableSet_le ((measurable_jetDistance0 b E).comp hX) measurable_const)

theorem measurableSet_aliveSet (b E : ℝ) (κ : ℝ → ℝ) (K d : ℝ) (r : ℕ) :
    MeasurableSet (aliveSet b E κ W K d r) :=
  Generator.growthSigma_le W r _ (measurableSet_aliveSet_sigma b E κ K d r)

/-- `A_r` is a past event. -/
theorem exists_past_aliveSet (b E : ℝ) (κ : ℝ → ℝ) (K d : ℝ) (r : ℕ) :
    ∃ S : Set (PastSample W r), MeasurableSet S ∧ pastCoords W r ⁻¹' S = aliveSet b E κ W K d r :=
  (measurableSet_aliveSet_sigma b E κ K d r)

theorem aliveSet_succ_subset (b E : ℝ) (κ : ℝ → ℝ) (K d : ℝ) (r : ℕ) :
    aliveSet b E κ W K d (r + 1) ⊆ aliveSet b E κ W K d r :=
  fun _ h i h1 h2 => h i h1 (by omega)

theorem aliveSet_succ_disj (b E : ℝ) (κ : ℝ → ℝ) (K d : ℝ) (r : ℕ) {ω : GrowthPath W}
    (h : ω ∈ aliveSet b E κ W K d (r + 1)) : K ≤ passiveMass b E (pathNearSchur b E κ W (r + 1) ω) :=
  (h (r + 1) (by omega) le_rfl).1

/-- **Decomposition at the first exit** (the stopping time of, without stopping
times): a crossing below `K` by length `N` happens at length `1`, or at a length `j+1` from the
alive event `A_j`, or after an exit of the scalar domain `δ₀ ≤ d`. -/
theorem crossing_subset (b E : ℝ) (κ : ℝ → ℝ) (K d : ℝ) (N : ℕ) :
    {ω : GrowthPath W | ∃ r, 1 ≤ r ∧ r ≤ N ∧ passiveMass b E (pathNearSchur b E κ W r ω) < K} ⊆
      ({ω | passiveMass b E (pathNearSchur b E κ W 1 ω) < K} ∪
        ⋃ j ∈ Finset.Ico 1 N, (aliveSet b E κ W K d j ∩
          {ω | passiveMass b E (pathNearSchur b E κ W (j + 1) ω) < K})) ∪
        ⋃ r ∈ Finset.Icc 1 N, {ω | d < jetDistance0 b E (pathNearSchur b E κ W r ω)} := by
  classical
  intro ω ⟨r, hr1, hrN, hr⟩
  set P : ℕ → Prop := fun m => 1 ≤ m ∧ (passiveMass b E (pathNearSchur b E κ W m ω) < K ∨
    d < jetDistance0 b E (pathNearSchur b E κ W m ω))
  have hex : ∃ m, P m := ⟨r, hr1, Or.inl hr⟩
  set m := Nat.find hex
  have hm : P m := Nat.find_spec hex
  have hmr : m ≤ r := Nat.find_min' hex ⟨hr1, Or.inl hr⟩
  have hmin : ∀ i, 1 ≤ i → i < m → K ≤ passiveMass b E (pathNearSchur b E κ W i ω) ∧
      jetDistance0 b E (pathNearSchur b E κ W i ω) ≤ d := fun i h1 h2 => by
    have := Nat.find_min hex h2
    simp only [P, not_and, not_or, not_lt] at this
    exact this h1
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq, Finset.mem_Ico,
    Finset.mem_Icc, exists_prop]
  rcases hm.2 with hq | hd
  · by_cases h1 : m = 1
    · left; left; rw [← h1]; exact hq
    · left; right
      refine ⟨m - 1, ⟨by omega, by omega⟩, fun i hi1 hi2 => hmin i hi1 (by omega), ?_⟩
      rwa [show m - 1 + 1 = m by omega]
  · right; exact ⟨m, ⟨hm.1, by omega⟩, hd⟩

end BlockBand.Transmission.LawFinite
