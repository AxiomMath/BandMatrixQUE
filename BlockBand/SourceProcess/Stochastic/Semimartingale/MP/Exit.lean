module
public import BlockBand.SourceProcess.Stochastic.MartingaleProblem
public import BlockBand.SourceProcess.Stochastic.Semimartingale.Riemann
public import Mathlib.Topology.Order.Monotone
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Exit times of continuous paths

Deterministic facts on `exitTimeFrom W Y ω` for an open `W` and a path `t ↦ Y t ω`, and on
the stopped time `stopTime τ t = min t τ` (so `stoppedProcess Y τ t ω = Y (stopTime (τ ω) t) ω`).
For a continuous path: the infimum is attained (`Y_τ ∉ W` when `τ < ⊤`), `Y_{t∧τ} ∈ W ↔ t < τ`,
and `Y_{t∧τ} ∈ closure W` when `Y_0 ∈ W`. Also: `Y_{t∧τ} - Y_0` is the limit of the telescoping
sums `Σ_k 1{t_k < τ}(Y_{t_{k+1}} - Y_{t_k})` over the grids of `[0, t]`.
-/

namespace BlockBand.SourceProcess.Stochastic.Semimartingale
open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

/-- `min t τ` as an element of `ℝ≥0`. -/
def stopTime (τ : WithTop ℝ≥0) (t : ℝ≥0) : ℝ≥0 := (min (t : WithTop ℝ≥0) τ).untopA

theorem stopTime_top (t : ℝ≥0) : stopTime ⊤ t = t := by
  show WithTop.untopD _ (min (t : WithTop ℝ≥0) ⊤) = t
  rw [min_top_right, WithTop.untopD_coe]

theorem stopTime_coe (s₀ t : ℝ≥0) : stopTime (s₀ : WithTop ℝ≥0) t = min t s₀ := by
  show WithTop.untopD _ (min (t : WithTop ℝ≥0) s₀) = min t s₀
  rw [← WithTop.coe_min, WithTop.untopD_coe]

theorem stopTime_le (τ : WithTop ℝ≥0) (t : ℝ≥0) : stopTime τ t ≤ t := by
  induction τ with
  | top => simp [stopTime_top]
  | coe s₀ => rw [stopTime_coe]; exact min_le_left _ _

theorem stopTime_of_lt {τ : WithTop ℝ≥0} {t : ℝ≥0} (h : (t : WithTop ℝ≥0) < τ) :
    stopTime τ t = t := by
  induction τ with
  | top => simp [stopTime_top]
  | coe s₀ => rw [stopTime_coe]; exact min_eq_left (WithTop.coe_lt_coe.1 h).le

theorem continuous_stopTime (τ : WithTop ℝ≥0) : Continuous (stopTime τ) := by
  induction τ with
  | top => rw [show stopTime ⊤ = id from funext stopTime_top]; exact continuous_id
  | coe s₀ =>
    rw [show stopTime (s₀ : WithTop ℝ≥0) = fun t => min t s₀ from funext (stopTime_coe s₀)]
    exact continuous_id.min continuous_const

theorem stoppedProcess_eq_stopTime {Ω E : Type*} (Y : ℝ≥0 → Ω → E) (τ : Ω → WithTop ℝ≥0)
    (t : ℝ≥0) (ω : Ω) : stoppedProcess Y τ t ω = Y (stopTime (τ ω) t) ω := rfl

variable {Ω E : Type*} [TopologicalSpace E] {W : Set E} {Y : ℝ≥0 → Ω → E} {ω : Ω}

/-- Before the exit time the path is in `W` (no continuity needed). -/
theorem mem_of_lt_exitTimeFrom {d : ℕ} {W : Set (Fin d → ℝ)} {Y : ℝ≥0 → Ω → Fin d → ℝ}
    {u : ℝ≥0} (h : (u : WithTop ℝ≥0) < exitTimeFrom W Y ω) : Y u ω ∈ W := by
  by_contra hu
  exact absurd (iInf₂_le u hu : exitTimeFrom W Y ω ≤ u) (not_le.2 h)

/-- For a continuous path and open `W`, the exit time is `⊤` or attained. -/
theorem exitTimeFrom_attained {d : ℕ} {W : Set (Fin d → ℝ)} {Y : ℝ≥0 → Ω → Fin d → ℝ}
    (hW : IsOpen W) (hY : Continuous fun t => Y t ω) :
    exitTimeFrom W Y ω = ⊤ ∨ ∃ s₀ : ℝ≥0, exitTimeFrom W Y ω = s₀ ∧ Y s₀ ω ∉ W := by
  set S := {t : ℝ≥0 | Y t ω ∉ W}
  rcases S.eq_empty_or_nonempty with hS | hS
  · left
    refine iInf₂_eq_top.2 fun t ht => absurd ht ?_
    have : t ∉ S := by rw [hS]; exact id
    simpa [S] using this
  · right
    have hc : IsClosed S := hW.isClosed_compl.preimage hY
    have hmem := hc.csInf_mem hS ⟨0, fun _ _ => zero_le⟩
    refine ⟨sInf S, le_antisymm (iInf₂_le _ hmem) (le_iInf₂ fun t ht =>
      WithTop.coe_le_coe.2 (csInf_le ⟨0, fun _ _ => zero_le⟩ ht)), hmem⟩

/-- For a continuous path, `Y_{t∧τ} ∈ W ↔ t < τ`. -/
theorem stop_mem_iff {d : ℕ} {W : Set (Fin d → ℝ)} {Y : ℝ≥0 → Ω → Fin d → ℝ}
    (hW : IsOpen W) (hY : Continuous fun t => Y t ω) (t : ℝ≥0) :
    Y (stopTime (exitTimeFrom W Y ω) t) ω ∈ W ↔ (t : WithTop ℝ≥0) < exitTimeFrom W Y ω := by
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    rcases exitTimeFrom_attained hW hY with h1 | ⟨s₀, h1, h2⟩
    · rw [h1] at hlt; exact absurd hlt (not_le.2 (WithTop.coe_lt_top t))
    · rw [h1] at hlt h
      rw [stopTime_coe, min_eq_right (WithTop.coe_le_coe.1 hlt)] at h
      exact h2 h
  · intro h
    rw [stopTime_of_lt h]
    exact mem_of_lt_exitTimeFrom h

/-- For a continuous path starting in `W`, the stopped path stays in `closure W`. -/
theorem stop_mem_closure {d : ℕ} {W : Set (Fin d → ℝ)} {Y : ℝ≥0 → Ω → Fin d → ℝ}
    (hW : IsOpen W) (hY : Continuous fun t => Y t ω) (h0 : Y 0 ω ∈ W) (t : ℝ≥0) :
    Y (stopTime (exitTimeFrom W Y ω) t) ω ∈ closure W := by
  by_cases h : (t : WithTop ℝ≥0) < exitTimeFrom W Y ω
  · exact subset_closure ((stop_mem_iff hW hY t).2 h)
  · push Not at h
    rcases exitTimeFrom_attained hW hY with h1 | ⟨s₀, h1, h2⟩
    · rw [h1] at h; exact absurd h (not_le.2 (WithTop.coe_lt_top t))
    · rw [h1] at h ⊢
      rw [stopTime_coe, min_eq_right (WithTop.coe_le_coe.1 h)]
      have hs0 : 0 < s₀ := by
        rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s₀) with h3 | h3
        · rw [← h3] at h2; exact absurd h0 h2
        · exact h3
      have hne : (𝓝[<] s₀).NeBot := by
        rw [← mem_closure_iff_nhdsWithin_neBot, closure_Iio' (a := s₀) ⟨0, hs0⟩]; exact mem_Iic.2 le_rfl
      refine mem_closure_of_tendsto (f := fun v => Y v ω) (b := 𝓝[<] s₀)
        ((hY.tendsto s₀).mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [self_mem_nhdsWithin] with v hv
      refine mem_of_lt_exitTimeFrom ?_
      rw [h1]; exact WithTop.coe_lt_coe.2 hv

end BlockBand.SourceProcess.Stochastic.Semimartingale
