module
public import BlockBand.SourceProcess.Stochastic.MartingaleProblem
public import BlockBand.SourceProcess.Stochastic.Semimartingale.MP.Exit
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.NNRat.Encodable
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Reconstructing an exit time from rational samples

For a closed `F` and a sample `v : ℚ≥0 → ℝ^d`:
* `hitQ F k v = inf {q : infEDist(v_q, F) < (k+1)⁻¹}`, `exitQ F v = sup_k hitQ F k v`;
  **`measurable_exitQ`** (product σ-algebra on the countable product).
* **`exitQ_eq`**: for an open `W`, a path `t ↦ Y_t ω` continuous, and a sample `v` agreeing
  with the path at every rational `q ≤ τ = exitTimeFrom W Y ω`, `exitQ Wᶜ v = τ`
  (both the values after `τ` and the event `τ = ⊤` are handled; `infEDist` to `∅` is `⊤`).
-/

namespace BlockBand.SourceProcess.Stochastic.Uniqueness
open MeasureTheory Filter Topology Set Metric
open BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal ENNReal

variable {d : ℕ}

/-- `ε_k = (k + 1)⁻¹`. -/
def epsK (k : ℕ) : ℝ≥0∞ := ((k : ℝ≥0∞) + 1)⁻¹

/-- First rational time at which the sample is `ε_k`-close to `F`. -/
def hitQ (F : Set (Fin d → ℝ)) (k : ℕ) (v : ℚ≥0 → Fin d → ℝ) : WithTop ℝ≥0 :=
  ⨅ (q : ℚ≥0) (_ : infEDist (v q) F < epsK k), (((q : ℝ≥0) : ℝ≥0) : WithTop ℝ≥0)

/-- The reconstructed exit time. -/
def exitQ (F : Set (Fin d → ℝ)) (v : ℚ≥0 → Fin d → ℝ) : WithTop ℝ≥0 := ⨆ k, hitQ F k v

theorem measurable_hitQ (F : Set (Fin d → ℝ)) (k : ℕ) : Measurable (hitQ F k) := by
  classical
  have e : hitQ F k = fun v => ⨅ q : ℚ≥0,
      if infEDist (v q) F < epsK k then (((q : ℝ≥0) : ℝ≥0) : WithTop ℝ≥0) else ⊤ := by
    funext v; simp only [hitQ, iInf_eq_if]
  rw [e]
  refine Measurable.iInf fun q => Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_lt (continuous_infEDist.measurable.comp (measurable_pi_apply q))
    measurable_const

theorem measurable_exitQ (F : Set (Fin d → ℝ)) : Measurable (exitQ (d := d) F) :=
  Measurable.iSup fun k => measurable_hitQ F k

theorem coe_toNNRat_real (r : ℚ) (hr : 0 ≤ r) : (((r.toNNRat : ℚ≥0) : ℝ≥0) : ℝ) = (r : ℝ) := by
  have h1 : (((r.toNNRat : ℚ≥0) : ℝ≥0) : ℝ) = (((r.toNNRat : ℚ≥0) : ℚ) : ℝ) := Real.ext_cauchy rfl
  rw [h1, Rat.coe_toNNRat r hr]

variable {Ω : Type*} {W : Set (Fin d → ℝ)} {Y : ℝ≥0 → Ω → Fin d → ℝ} {ω : Ω}

theorem hitQ_le_exit (hW : IsOpen W) (hY : Continuous fun t => Y t ω) {v : ℚ≥0 → Fin d → ℝ}
    (hv : ∀ q : ℚ≥0, (((q : ℝ≥0) : ℝ≥0) : WithTop ℝ≥0) ≤ exitTimeFrom W Y ω → v q = Y q ω)
    (k : ℕ) : hitQ Wᶜ k v ≤ exitTimeFrom W Y ω := by
  rcases exitTimeFrom_attained hW hY with h | ⟨s₀, hs, hns⟩
  · rw [h]; exact le_top
  have hg : Continuous fun r : ℝ≥0 => infEDist (Y r ω) Wᶜ := continuous_infEDist.comp hY
  have hk : (0 : ℝ≥0∞) < epsK k := ENNReal.inv_pos.2 (by simp)
  have h0 : infEDist (Y s₀ ω) Wᶜ = 0 := infEDist_zero_of_mem hns
  have hev : ∀ᶠ r in 𝓝 s₀, infEDist (Y r ω) Wᶜ < epsK k :=
    hg.continuousAt.eventually (gt_mem_nhds (by
      show infEDist (Y s₀ ω) Wᶜ < epsK k; rw [h0]; exact hk))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have key : ∃ q : ℚ≥0, (q : ℝ≥0) ≤ s₀ ∧ infEDist (Y q ω) Wᶜ < epsK k := by
    rcases eq_or_ne s₀ 0 with h0' | h0'
    · refine ⟨0, by simp, ?_⟩
      have := hball (y := s₀) (by simpa using hδ)
      simpa [h0'] using this
    · have hpos : (0 : ℝ) < s₀ := lt_of_le_of_ne s₀.2 (fun h => h0' (NNReal.coe_eq_zero.1 h.symm))
      obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show max 0 ((s₀ : ℝ) - δ) < s₀ from
        max_lt hpos (by linarith))
      have hr0 : (0 : ℝ) < r := lt_of_le_of_lt (le_max_left _ _) hr1
      have hr0' : (0 : ℚ) ≤ r := by exact_mod_cast hr0.le
      refine ⟨r.toNNRat, ?_, hball ?_⟩
      · rw [← NNReal.coe_le_coe, coe_toNNRat_real r hr0']; exact hr2.le
      · rw [NNReal.dist_eq, coe_toNNRat_real r hr0', abs_sub_lt_iff]
        constructor <;> linarith [le_max_right 0 ((s₀ : ℝ) - δ)]
  obtain ⟨q, hq1, hq2⟩ := key
  rw [hs]
  have hvq : v q = Y q ω := hv q (by rw [hs]; exact_mod_cast hq1)
  exact (iInf₂_le q (by rw [hvq]; exact hq2)).trans (by exact_mod_cast hq1)

theorem hitQ_eq_path (hW : IsOpen W) (hY : Continuous fun t => Y t ω) {v : ℚ≥0 → Fin d → ℝ}
    (hv : ∀ q : ℚ≥0, (((q : ℝ≥0) : ℝ≥0) : WithTop ℝ≥0) ≤ exitTimeFrom W Y ω → v q = Y q ω)
    (k : ℕ) : hitQ Wᶜ k v = hitQ Wᶜ k (fun q => Y q ω) := by
  have h1 := hitQ_le_exit hW hY hv k
  have h2 := hitQ_le_exit (v := fun q => Y q ω) hW hY (fun _ _ => rfl) k
  refine le_antisymm (le_iInf₂ fun q hq => ?_) (le_iInf₂ fun q hq => ?_)
  · by_cases hqτ : (((q : ℝ≥0) : ℝ≥0) : WithTop ℝ≥0) ≤ exitTimeFrom W Y ω
    · exact iInf₂_le q (by show infEDist (v q) Wᶜ < _; rw [hv q hqτ]; exact hq)
    · exact h1.trans (not_le.1 hqτ).le
  · by_cases hqτ : (((q : ℝ≥0) : ℝ≥0) : WithTop ℝ≥0) ≤ exitTimeFrom W Y ω
    · exact iInf₂_le q (by show infEDist (Y q ω) Wᶜ < _; rw [← hv q hqτ]; exact hq)
    · exact h2.trans (not_le.1 hqτ).le

theorem exit_le_iSup_hitQ (hW : IsOpen W) (hY : Continuous fun t => Y t ω) :
    exitTimeFrom W Y ω ≤ ⨆ k, hitQ Wᶜ k (fun q => Y q ω) := by
  by_contra hlt
  push Not at hlt
  set σ := ⨆ k, hitQ Wᶜ k (fun q => Y q ω)
  obtain ⟨s₀, hs₀⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hlt)
  obtain ⟨s₁, hs01, hs1⟩ : ∃ s₁ : ℝ≥0, s₀ < s₁ ∧ (s₁ : WithTop ℝ≥0) < exitTimeFrom W Y ω := by
    rcases eq_or_ne (exitTimeFrom W Y ω) ⊤ with h | h
    · exact ⟨s₀ + 1, lt_add_one _, by rw [h]; exact WithTop.coe_lt_top _⟩
    · obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 h
      rw [← hs, ← hs₀] at hlt
      have hlt' : (s₀ : ℝ) < s := by exact_mod_cast WithTop.coe_lt_coe.1 hlt
      refine ⟨(s₀ + s) / 2, ?_, ?_⟩
      · rw [← NNReal.coe_lt_coe]; push_cast; linarith
      · rw [← hs, WithTop.coe_lt_coe, ← NNReal.coe_lt_coe]; push_cast; linarith
  have hg : Continuous fun r : ℝ≥0 => infEDist (Y r ω) Wᶜ := continuous_infEDist.comp hY
  obtain ⟨r₀, hr₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 (zero_le : 0 ≤ s₁))
    hg.continuousOn
  have hmem : ∀ r ∈ Icc (0 : ℝ≥0) s₁, Y r ω ∈ W := fun r hr =>
    mem_of_lt_exitTimeFrom (lt_of_le_of_lt (WithTop.coe_le_coe.2 hr.2) hs1)
  have hpos : 0 < infEDist (Y r₀ ω) Wᶜ := by
    rw [infEDist_pos_iff_notMem_closure, hW.isClosed_compl.closure_eq]
    exact fun h => h (hmem r₀ hr₀)
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hpos.ne'
  have hk : epsK n ≤ (n : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 le_self_add
  have hs1n : (s₁ : WithTop ℝ≥0) ≤ hitQ Wᶜ n (fun q => Y q ω) := le_iInf₂ fun q hq => by
    by_contra h
    push Not at h
    have hq1 : ((q : ℝ≥0) : ℝ≥0) ∈ Icc (0 : ℝ≥0) s₁ := ⟨zero_le, (WithTop.coe_lt_coe.1 h).le⟩
    have := hmin hq1
    exact absurd hq (not_lt.2 ((hk.trans hn.le).trans this))
  have hle : hitQ Wᶜ n (fun q => Y q ω) ≤ σ :=
    le_iSup (fun k => hitQ Wᶜ k (fun q => Y q ω)) n
  have : (s₁ : WithTop ℝ≥0) ≤ s₀ := by rw [hs₀]; exact hs1n.trans hle
  exact absurd (WithTop.coe_le_coe.1 this) (not_le.2 hs01)

/-- **The exit time is reconstructed from rational samples.** -/
theorem exitQ_eq (hW : IsOpen W) (hY : Continuous fun t => Y t ω) {v : ℚ≥0 → Fin d → ℝ}
    (hv : ∀ q : ℚ≥0, (((q : ℝ≥0) : ℝ≥0) : WithTop ℝ≥0) ≤ exitTimeFrom W Y ω → v q = Y q ω) :
    exitQ Wᶜ v = exitTimeFrom W Y ω := by
  unfold exitQ
  simp_rw [hitQ_eq_path hW hY hv]
  exact le_antisymm (iSup_le fun k => hitQ_le_exit hW hY (fun _ _ => rfl) k)
    (exit_le_iSup_hitQ hW hY)

end BlockBand.SourceProcess.Stochastic.Uniqueness
