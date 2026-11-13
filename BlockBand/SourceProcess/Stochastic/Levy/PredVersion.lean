module
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.VersionAlpha
public import BlockBand.SourceProcess.Stochastic.GeneralIntegral.PredInd
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# A predictable version of an adapted continuous process

Setting: arbitrary `(Ω, m₀)`, raw filtration `𝓖`, raw predictable σ-algebra
`predictableSpace (toCF 𝓖)` on `ℝ × Ω`, time read through `s ↦ s.toNNReal`.

For a `𝓖`-adapted `Y : ℝ≥0 → Ω → ℝ^d`, `predVersion Y (s, ω)` is the coordinatewise limit of
the dyadic left samples of `Y` (`compositeVersion` with `τ = ⊤` and the coordinate maps).

* `stronglyMeasurable_predVersion`: `predVersion Y` is raw predictable (everywhere, no null set);
* `stronglyMeasurable_comp_predVersion`: so is `g ∘ predVersion Y` for every **Borel**
  `g : ℝ^d → ℝ` (e.g. entries of the Moore–Penrose pseudoinverse `σ⁺`, which is Borel but not
  continuous), and `stronglyMeasurable_stopped_comp_predVersion` for `1{s ≤ τ} g(predVersion)`
  with a raw stopping time `τ`;
* `predVersion_eq`: on every continuous path and every `s > 0`, `predVersion Y (s, ω) = Y_s(ω)`;
  `ae_comp_predVersion_eq`: hence `g ∘ predVersion Y = g(Y_s)` `μ`-a.e. for every `μ ≪ dt ⊗ Q`
  on `(0,T] × Ω` (e.g. the bracket measures `ν_T`).
-/

namespace BlockBand.SourceProcess.Stochastic.Levy
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic.GeneralIntegral
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}

/-- The predictable version: coordinatewise limits of left samples (`τ = ⊤`). -/
def predVersion (Y : ℝ≥0 → Ω → Fin d → ℝ) (p : ℝ × Ω) : Fin d → ℝ :=
  fun i => compositeVersion (fun _ => ⊤) (fun y : Fin d → ℝ => y i) Y p

omit mΩ in
/-- **Pathwise identification** on continuous paths for `s > 0`. -/
theorem predVersion_eq {Y : ℝ≥0 → Ω → Fin d → ℝ} {p : ℝ × Ω}
    (hp : Continuous fun t => Y t p.2) (hs : 0 < p.1) :
    predVersion Y p = Y p.1.toNNReal p.2 := by
  funext i
  rw [predVersion, compositeVersion_eq _ (continuous_apply i) hp hs, stoppedComposite,
    ite_eq_left le_top]

variable (𝓖 : Filtration ℝ≥0 mΩ)

theorem isStoppingTime_top' : IsStoppingTime 𝓖 (fun _ : Ω => (⊤ : WithTop ℝ≥0)) :=
  fun t => by simp

/-- **The version is raw predictable.** -/
theorem stronglyMeasurable_predVersion {Y : ℝ≥0 → Ω → Fin d → ℝ}
    (hY : ∀ t, StronglyMeasurable[𝓖 t] (Y t)) :
    StronglyMeasurable[predictableSpace (toCF 𝓖)] (predVersion Y) := by
  have h : Measurable[predictableSpace (toCF 𝓖)] (predVersion Y) :=
    @measurable_pi_iff (ℝ × Ω) (Fin d) (fun _ => ℝ) (predictableSpace (toCF 𝓖)) _ _ |>.2
      fun i => (stronglyMeasurable_compositeVersion 𝓖 (isStoppingTime_top' 𝓖)
        (continuous_apply i) hY).measurable
  exact h.stronglyMeasurable

/-- **Borel functions of the version are raw predictable.** -/
theorem stronglyMeasurable_comp_predVersion {Y : ℝ≥0 → Ω → Fin d → ℝ}
    (hY : ∀ t, StronglyMeasurable[𝓖 t] (Y t)) {g : (Fin d → ℝ) → ℝ} (hg : Measurable g) :
    StronglyMeasurable[predictableSpace (toCF 𝓖)] fun p => g (predVersion Y p) := by
  have h : Measurable[predictableSpace (toCF 𝓖)] fun p => g (predVersion Y p) :=
    hg.comp (stronglyMeasurable_predVersion 𝓖 hY).measurable
  exact h.stronglyMeasurable

/-- **Stopped Borel functions of the version are raw predictable.** -/
theorem stronglyMeasurable_stopped_comp_predVersion {Y : ℝ≥0 → Ω → Fin d → ℝ}
    (hY : ∀ t, StronglyMeasurable[𝓖 t] (Y t)) {g : (Fin d → ℝ) → ℝ} (hg : Measurable g)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ) :
    StronglyMeasurable[predictableSpace (toCF 𝓖)]
      ((stopSet τ).indicator fun p => g (predVersion Y p)) :=
  (stronglyMeasurable_comp_predVersion 𝓖 hY hg).indicator (measurableSet_stopSet 𝓖 hτ)

omit mΩ in
/-- On a.e. path, `g ∘ predVersion Y` agrees with `g(Y_s)` for all `s > 0`. -/
theorem ae_comp_predVersion_eq [MeasurableSpace Ω] {Q : Measure Ω} [SFinite Q] {T : ℝ≥0}
    {μ : Measure (ℝ × Ω)} (hμ : μ ≪ timeProbMeasure T Q) {Y : ℝ≥0 → Ω → Fin d → ℝ}
    (hYc : ∀ᵐ ω ∂Q, Continuous fun t => Y t ω) (g : (Fin d → ℝ) → ℝ) :
    (fun p => g (predVersion Y p)) =ᵐ[μ] fun p => g (Y p.1.toNNReal p.2) := by
  filter_upwards [hμ.ae_le (ae_timeProb_snd (T := T) hYc), hμ.ae_le (ae_timeProb_mem Q T)]
    with p hp hpos
  rw [predVersion_eq hp hpos.1]

end BlockBand.SourceProcess.Stochastic.Levy
