module
public import BlockBand.SourceProcess.Stochastic.Uniqueness.LocalLaw
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Equality of stopped laws for two Euler setups

The local form of uniqueness in law; see `LocalLaw` for the setting and the chain of arguments.

**`map_stopped_eq`**: two `EulerSetup`s with the same coefficients, the same open domain and
equal initial laws have equal finite-dimensional laws of the stopped paths `t ↦ Y_{t∧τ}`.
-/

namespace BlockBand.SourceProcess.Stochastic.Uniqueness
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.Levy
open BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal ENNReal

variable {d : ℕ} {c : LipCoef d} {W : Set (Fin d → ℝ)}

namespace EulerSetup

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (S : EulerSetup c W P)

/-- The rational samples of the Euler limit. -/
def V (ω : Ω) : ℚ≥0 → Fin d → ℝ := fun q => eulLim c S.ξ S.B q ω

/-- The rational samples of the `m`-th Euler scheme. -/
def Vm (m : ℕ) (ω : Ω) : ℚ≥0 → Fin d → ℝ := fun q => eulX c m S.ξ S.B q ω

theorem Vm_eq (m : ℕ) : S.Vm m = eulF c m ∘ initBrownian S.ξ S.B :=
  funext fun ω => funext fun q => eulX_eq_eulF c m S.ξ S.B q ω

theorem measurable_initB : Measurable (initBrownian S.ξ S.B) :=
  measurable_initBrownian (S.hξ.mono (S.𝓕.le 0) le_rfl) (brownian_measurable S.hB)

theorem measurable_Vm (m : ℕ) : Measurable (S.Vm m) := by
  rw [S.Vm_eq]; exact (measurable_eulF c m).comp S.measurable_initB

theorem tendsto_V : ∀ᵐ ω ∂P, Tendsto (fun m => S.Vm m ω) atTop (𝓝 (S.V ω)) := by
  filter_upwards [ae_all_iff.2 fun q : ℚ≥0 => tendsto_eulLim S.hB c S.hξ q] with ω hω
  exact tendsto_pi_nhds.2 hω

theorem aemeasurable_V : AEMeasurable S.V P :=
  aemeasurable_of_tendsto_metrizable_ae' (fun m => (S.measurable_Vm m).aemeasurable) S.tendsto_V

theorem tendsto_recon (hW : IsOpen W) (I : Finset ℝ≥0) : ∀ᵐ ω ∂P,
    Tendsto (fun j => reconQ W I j (S.V ω)) atTop
      (𝓝 (I.restrict fun t => S.Y (stopTime (S.τ ω) t) ω)) := by
  filter_upwards [S.hYc, S.hτe, ae_all_iff.2 fun q : ℚ≥0 => eulLim_eq_of_le S.hB c S.hξ S.hτ
    S.hYm S.hYc S.hγY S.hγYe S.hrep q] with ω hc hτ hq
  have hv : ∀ q : ℚ≥0, (((q : ℝ≥0) : ℝ≥0) : WithTop ℝ≥0) ≤ exitTimeFrom W S.Y ω →
      S.V ω q = S.Y q ω := fun q h => hq q (by rw [hτ]; exact h)
  have hex : exitQ Wᶜ (S.V ω) = S.τ ω := by rw [exitQ_eq hW hc hv, hτ]
  refine tendsto_pi_nhds.2 fun t => ?_
  simp only [reconQ, hex, Finset.restrict]
  set s := stopTime (S.τ ω) t
  have hsτ : (s : WithTop ℝ≥0) ≤ exitTimeFrom W S.Y ω := by
    rw [← hτ]
    exact (GeneralIntegral.coe_untopA_min t (S.τ ω)).le.trans (min_le_right _ _)
  have e : ∀ j, S.V ω (rhoQ j s) = S.Y (rhoQ j s) ω := fun j =>
    hv _ ((WithTop.coe_le_coe.2 (rhoQ_le j s)).trans hsτ)
  simp_rw [e]
  exact (hc.tendsto s).comp (tendsto_rhoQ s)

end EulerSetup

/-- **Equality of the stopped finite-dimensional laws.** -/
theorem map_stopped_eq (hW : IsOpen W)
    {Ω₁ : Type*} [MeasurableSpace Ω₁] {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁]
    (S₁ : EulerSetup c W P₁)
    {Ω₂ : Type*} [MeasurableSpace Ω₂] {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    (S₂ : EulerSetup c W P₂) (hξ : P₁.map S₁.ξ = P₂.map S₂.ξ) (I : Finset ℝ≥0) :
    P₁.map (fun ω => I.restrict fun t => S₁.Y (stopTime (S₁.τ ω) t) ω) =
      P₂.map (fun ω => I.restrict fun t => S₂.Y (stopTime (S₂.τ ω) t) ω) := by
  have hB := map_initBrownian_eq S₁.hB S₁.hξ S₂.hB S₂.hξ hξ
  have hVm : ∀ m, P₁.map (S₁.Vm m) = P₂.map (S₂.Vm m) := fun m => by
    rw [S₁.Vm_eq, S₂.Vm_eq, ← Measure.map_map (measurable_eulF c m) S₁.measurable_initB,
      ← Measure.map_map (measurable_eulF c m) S₂.measurable_initB, hB]
  have hV : P₁.map S₁.V = P₂.map S₂.V :=
    map_eq_of_tendsto_ae (fun m => (S₁.measurable_Vm m).aemeasurable)
      (fun m => (S₂.measurable_Vm m).aemeasurable) S₁.tendsto_V S₂.tendsto_V hVm
  refine map_eq_of_tendsto_ae (f₁ := fun j ω => reconQ W I j (S₁.V ω))
    (f₂ := fun j ω => reconQ W I j (S₂.V ω))
    (fun j => (measurable_reconQ W I j).comp_aemeasurable S₁.aemeasurable_V)
    (fun j => (measurable_reconQ W I j).comp_aemeasurable S₂.aemeasurable_V)
    (S₁.tendsto_recon hW I) (S₂.tendsto_recon hW I) fun j => ?_
  show P₁.map (reconQ W I j ∘ S₁.V) = P₂.map (reconQ W I j ∘ S₂.V)
  rw [← AEMeasurable.map_map_of_aemeasurable (measurable_reconQ W I j).aemeasurable
      S₁.aemeasurable_V,
    ← AEMeasurable.map_map_of_aemeasurable (measurable_reconQ W I j).aemeasurable
      S₂.aemeasurable_V, hV]

end BlockBand.SourceProcess.Stochastic.Uniqueness
