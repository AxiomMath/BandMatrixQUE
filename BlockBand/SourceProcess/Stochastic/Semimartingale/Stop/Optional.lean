module
public import BlockBand.SourceProcess.Stochastic.Semimartingale.Stop.Grid
public import BlockBand.SourceProcess.Stochastic.Semimartingale.Tools
public import Mathlib.Probability.Martingale.OptionalSampling
public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Optional stopping for a.s. continuous processes with a martingale modification

Setting: probability space `(Ω, m₀, Q)`, raw filtration `𝓖 : Filtration ℝ≥0 m₀`.
`exists_martingale_stoppedProcess`: if `X` has a.s. continuous paths and a `𝓖`-martingale
modification `M`, and `ρ` is a `𝓖`-stopping time, then `X^ρ` has a `𝓖`-martingale
modification.

Proof: on the grids `t_k` of `[s, t]`, the discrete transforms
`Σ_k 1{t_k < ρ}(M_{t_{k+1}} - M_{t_k}) = M_{σ_n} - M_s` (with the countable-range stopping
times `σ_n` = first grid point at or after `ρ`) have zero mean on `𝓖_s`-sets, converge a.s. to
`X_{t∧ρ} - X_{s∧ρ}` (path continuity), and are uniformly integrable
(`M_{σ_n} = E[M_t | 𝓖_{σ_n}]`, optional sampling for countable range).
-/

namespace BlockBand.SourceProcess.Stochastic.Semimartingale
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {Q : Measure Ω} {𝓖 : Filtration ℝ≥0 m₀}
  {ρ : Ω → WithTop ℝ≥0}

/-- The discretized stopping time: first grid point of `[s, t]` at or after `ρ`. -/
def gridStop (ρ : Ω → WithTop ℝ≥0) (s t : ℝ≥0) (n : ℕ) (ω : Ω) : WithTop ℝ≥0 :=
  (grid s t n (firstIdx (ρ ω) s t n) : WithTop ℝ≥0)

theorem measurableSet_firstIdx_eq (hρ : IsStoppingTime 𝓖 ρ) {s t : ℝ≥0} (hst : s ≤ t) (n : ℕ)
    {k : ℕ} (hk : k ≤ n + 1) :
    MeasurableSet[𝓖 (grid s t n k)] {ω | firstIdx (ρ ω) s t n = k} := by
  classical
  have e : {ω | firstIdx (ρ ω) s t n = k} =
      ({ω | ¬ ((grid s t n k : WithTop ℝ≥0) < ρ ω)} ∪ {_ω | k = n + 1}) ∩
        ⋂ j ∈ Finset.range k, {ω | (grid s t n j : WithTop ℝ≥0) < ρ ω} := by
    ext ω
    simp only [firstIdx, Set.mem_ofPred_eq, mem_inter_iff, mem_union, mem_iInter, Finset.mem_range]
    rw [Nat.find_eq_iff]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun j hj => ?_⟩
      have := h2 j hj
      push Not at this
      exact this.1
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun j hj => ?_⟩
      push Not
      exact ⟨h2 j hj, by omega⟩
  rw [e]
  refine MeasurableSet.inter (MeasurableSet.union ?_ ?_) ?_
  · have := hρ (grid s t n k)
    convert this using 1
    ext ω; simp only [mem_ofPred]; exact not_lt
  · by_cases h : k = n + 1 <;> simp [h]
  · refine Finset.measurableSet_biInter _ fun j hj => ?_
    have hjk : grid s t n j ≤ grid s t n k :=
      grid_mono hst n (Finset.mem_range.1 hj).le
    have := (hρ (grid s t n j)).compl
    have h2 := 𝓖.mono hjk _ this
    convert h2 using 1
    ext ω; simp only [mem_ofPred, mem_compl_iff]; exact not_le.symm

theorem isStoppingTime_gridStop (hρ : IsStoppingTime 𝓖 ρ) {s t : ℝ≥0} (hst : s ≤ t) (n : ℕ) :
    IsStoppingTime 𝓖 (gridStop ρ s t n) := by
  classical
  intro r
  have e : {ω | gridStop ρ s t n ω ≤ r} = ⋃ k ∈ (Finset.range (n + 2)).filter
      (fun k => grid s t n k ≤ r), {ω | firstIdx (ρ ω) s t n = k} := by
    ext ω
    simp only [gridStop, Set.mem_ofPred_eq, WithTop.coe_le_coe, mem_iUnion, Finset.mem_filter,
      Finset.mem_range, exists_prop]
    constructor
    · intro h; exact ⟨_, ⟨Nat.lt_succ_of_le firstIdx_le, h⟩, rfl⟩
    · rintro ⟨k, ⟨_, hk⟩, rfl⟩; exact hk
  rw [e]
  refine Finset.measurableSet_biUnion _ fun k hk => ?_
  obtain ⟨hk1, hk2⟩ := Finset.mem_filter.1 hk
  exact 𝓖.mono hk2 _ (measurableSet_firstIdx_eq hρ hst n (Nat.lt_succ_iff.1
    (Finset.mem_range.1 hk1)))

theorem gridStop_le {s t : ℝ≥0} (hst : s ≤ t) (n : ℕ) (ω : Ω) :
    gridStop ρ s t n ω ≤ t := by
  have := grid_mono hst n (firstIdx_le (τ := ρ ω) (s := s) (t := t) (n := n))
  rw [grid_last hst] at this
  exact WithTop.coe_le_coe.2 this

theorem countable_range_gridStop (s t : ℝ≥0) (n : ℕ) :
    (Set.range (gridStop ρ s t n)).Countable := by
  refine ((Finset.range (n + 2)).finite_toSet.image
    (fun k => (grid s t n k : WithTop ℝ≥0))).countable.mono ?_
  rintro _ ⟨ω, rfl⟩
  exact ⟨firstIdx (ρ ω) s t n, Finset.mem_range.2 (Nat.lt_succ_of_le firstIdx_le), rfl⟩

/-- The discrete martingale transform along the grid of `[s, t]`. -/
def gridTransform (M : ℝ≥0 → Ω → ℝ) (ρ : Ω → WithTop ℝ≥0) (s t : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    (if (grid s t n k : WithTop ℝ≥0) < ρ ω then M (grid s t n (k + 1)) ω - M (grid s t n k) ω
      else 0)

theorem gridTransform_eq (M : ℝ≥0 → Ω → ℝ) {s t : ℝ≥0} (hst : s ≤ t) (n : ℕ) (ω : Ω) :
    gridTransform M ρ s t n ω = stoppedValue M (gridStop ρ s t n) ω - M s ω := by
  rw [gridTransform, sum_ite_lt_eq (fun u => M u ω) hst]
  simp only [stoppedValue, gridStop, WithTop.untopA, WithTop.untopD_coe]

variable [IsProbabilityMeasure Q]

theorem integral_indicator_gridTransform {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M 𝓖 Q)
    (hρ : IsStoppingTime 𝓖 ρ) {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω} (hA : MeasurableSet[𝓖 s] A)
    (n : ℕ) :
    Integrable (fun ω => A.indicator (fun _ => (1 : ℝ)) ω * gridTransform M ρ s t n ω) Q ∧
    ∫ ω, A.indicator (fun _ => (1 : ℝ)) ω * gridTransform M ρ s t n ω ∂Q = 0 := by
  classical
  set g : ℕ → Ω → ℝ := fun k ω => A.indicator (fun _ => (1 : ℝ)) ω *
    (if (grid s t n k : WithTop ℝ≥0) < ρ ω then 1 else 0)
  have hgm : ∀ k, StronglyMeasurable[𝓖 (grid s t n k)] (g k) := by
    intro k
    have hA' : MeasurableSet[𝓖 (grid s t n k)] A := by
      have := grid_mono hst n (Nat.zero_le k); rw [grid_zero] at this; exact 𝓖.mono this A hA
    have hB : MeasurableSet[𝓖 (grid s t n k)] {ω | (grid s t n k : WithTop ℝ≥0) < ρ ω} := by
      have := (hρ (grid s t n k)).compl
      convert this using 1; ext ω; simp only [mem_ofPred, mem_compl_iff]; exact not_le.symm
    refine (stronglyMeasurable_const.indicator hA').mul ?_
    have : (fun ω => if (grid s t n k : WithTop ℝ≥0) < ρ ω then (1 : ℝ) else 0) =
        {ω | (grid s t n k : WithTop ℝ≥0) < ρ ω}.indicator (fun _ => 1) := by
      funext ω
      by_cases h : (grid s t n k : WithTop ℝ≥0) < ρ ω
      · rw [Set.indicator_of_mem (show ω ∈ {ω | (grid s t n k : WithTop ℝ≥0) < ρ ω} from h)]
        split_ifs; rfl
      · rw [Set.indicator_of_notMem (show ω ∉ {ω | (grid s t n k : WithTop ℝ≥0) < ρ ω} from h)]
        split_ifs; rfl
    rw [this]; exact stronglyMeasurable_const.indicator hB
  have hgb : ∀ k, ∀ᵐ ω ∂Q, ‖g k ω‖ ≤ 1 := fun k => ae_of_all _ fun ω => by
    simp only [g]
    by_cases h1 : ω ∈ A
    · rw [Set.indicator_of_mem h1]; split_ifs <;> simp
    · rw [Set.indicator_of_notMem h1]; simp
  have hi : ∀ k, Integrable (fun ω => g k ω *
      (M (grid s t n (k + 1)) ω - M (grid s t n k) ω)) Q := fun k =>
    ((hM.integrable _).sub (hM.integrable _)).bdd_mul
      ((hgm k).mono (𝓖.le _)).aestronglyMeasurable (hgb k)
  have e : (fun ω => A.indicator (fun _ => (1 : ℝ)) ω * gridTransform M ρ s t n ω) =
      fun ω => ∑ k ∈ Finset.range (n + 1), g k ω *
        (M (grid s t n (k + 1)) ω - M (grid s t n k) ω) := by
    funext ω
    simp only [gridTransform, Finset.mul_sum, g]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> ring
  rw [e]
  refine ⟨integrable_finsetSum _ fun k _ => hi k, ?_⟩
  rw [integral_finsetSum _ fun k _ => hi k]
  exact Finset.sum_eq_zero fun k _ => martingale_integral_mul_sub_eq_zero hM
    (grid_mono hst n (Nat.le_succ k)) (hgm k).aestronglyMeasurable (hgb k)

end BlockBand.SourceProcess.Stochastic.Semimartingale
