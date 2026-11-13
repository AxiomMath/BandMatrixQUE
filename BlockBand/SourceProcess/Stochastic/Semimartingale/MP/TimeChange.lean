module
public import BlockBand.SourceProcess.Stochastic.Semimartingale.MP.Telescope
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Integrals along a path stopped at its exit time

Deterministic. For a continuous path `Y · ω` in `ℝ^d`, open `W`, `τ = exitTimeFrom W Y ω`,
and any `g`:
`∫_{(0, t∧τ]} g(Y_v) dv = ∫_{(0, t]} 1_W(Y_{v∧τ}) g(Y_{v∧τ}) dv` (Lebesgue measure).
This identifies the stopped compensators with the pathwise integrals of the
characteristics `1_W(Z) b(Z)`, `1_W(Z) a(Z)`, `1_W(Z) 𝓛φ(Z)` of `Z = Y_{·∧τ}`.
-/

namespace BlockBand.SourceProcess.Stochastic.Semimartingale
open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

variable {Ω : Type*} {d : ℕ} {W : Set (Fin d → ℝ)} {Y : ℝ≥0 → Ω → Fin d → ℝ} {ω : Ω}

theorem stopTime_le_self (τ : WithTop ℝ≥0) (t : ℝ≥0) : (stopTime τ t : WithTop ℝ≥0) ≤ τ := by
  induction τ with
  | top => exact le_top
  | coe s₀ => rw [stopTime_coe]; exact WithTop.coe_le_coe.2 (min_le_right _ _)

theorem setIntegral_stop_eq (hW : IsOpen W) (hY : Continuous fun t => Y t ω)
    (g : (Fin d → ℝ) → ℝ) (t : ℝ≥0) :
    ∫ v in Ioc (0 : ℝ) (stopTime (exitTimeFrom W Y ω) t), g (Y v.toNNReal ω) =
      ∫ v in Ioc (0 : ℝ) t,
        W.indicator g (Y (stopTime (exitTimeFrom W Y ω) v.toNNReal) ω) := by
  set τ := exitTimeFrom W Y ω
  set σ := stopTime τ t
  have hσt : (σ : ℝ) ≤ t := by exact_mod_cast stopTime_le τ t
  have hστ : (σ : WithTop ℝ≥0) ≤ τ := stopTime_le_self τ t
  have hae : ∀ᵐ v ∂volume, v ∈ Ioc (0 : ℝ) t →
      W.indicator g (Y (stopTime τ v.toNNReal) ω) =
        (Ioc (0 : ℝ) σ).indicator (fun v => g (Y v.toNNReal ω)) v := by
    filter_upwards [(countable_singleton (σ : ℝ)).ae_notMem volume] with v hv hvI
    have hvσ : v ≠ σ := fun h => hv (by simp [h])
    have hv0 : 0 ≤ v := hvI.1.le
    have hcoe : ((v.toNNReal : ℝ≥0) : ℝ) = v := Real.coe_toNNReal v hv0
    rcases lt_or_gt_of_ne hvσ with hlt | hgt
    · have hu : (v.toNNReal : WithTop ℝ≥0) < τ := by
        refine lt_of_lt_of_le (WithTop.coe_lt_coe.2 ?_) hστ
        rw [← NNReal.coe_lt_coe, hcoe]; exact hlt
      rw [Set.indicator_of_mem (show v ∈ Ioc (0 : ℝ) σ from ⟨hvI.1, hlt.le⟩), stopTime_of_lt hu,
        Set.indicator_of_mem (mem_of_lt_exitTimeFrom hu)]
    · have hnot : ¬ ((v.toNNReal : WithTop ℝ≥0) < τ) := by
        intro hu
        have h1 : v.toNNReal ≤ t := by
          rw [← NNReal.coe_le_coe, hcoe]; exact hvI.2
        have : v.toNNReal ≤ σ := le_stopTime hu.le h1
        have : v ≤ σ := by rw [← hcoe]; exact_mod_cast this
        linarith
      rw [Set.indicator_of_notMem (fun h => hnot ((stop_mem_iff hW hY _).1 h)),
        Set.indicator_of_notMem (fun h => not_le.2 hgt h.2)]
  rw [setIntegral_congr_ae measurableSet_Ioc hae, setIntegral_indicator measurableSet_Ioc,
    Set.inter_eq_right.2 (Ioc_subset_Ioc_right hσt)]

end BlockBand.SourceProcess.Stochastic.Semimartingale
