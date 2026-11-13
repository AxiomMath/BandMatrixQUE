module
public import BlockBand.SourceProcess.Stochastic.Uniqueness.EulerIdent
public import BlockBand.SourceProcess.Stochastic.Uniqueness.EulerSample
public import BlockBand.SourceProcess.Stochastic.Uniqueness.ExitRecon
public import BlockBand.SourceProcess.Stochastic.Uniqueness.LawLimit
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The stopped law is determined by the initial law (local form)

`EulerSetup c W P`: on `(Ω, P)`, a raw filtration `𝓕`, an `𝓕`-Brownian motion `B`, a
`𝓕_0`-measurable `ξ`, a raw stopping time `τ` equal a.s. to `exitTimeFrom W Y`, and a process
`Y` (measurable marginals, a.s. continuous) solving the stopped SDE with coefficients `c`
driven by `B` (general integral, hypotheses of `eulLim_eq_of_le`).

This module provides the dyadic rational grid `rhoQ` and the reconstruction `reconQ` used in the
proof of **`map_stopped_eq`** (sibling module): for two Euler setups with the same `c`, open `W`,
and equal laws of `ξ`, the finite-dimensional laws of `t ↦ Y_{t∧τ}` agree. Chain: the Euler schemes
are measurable functionals of `(ξ, B_ℚ)` whose law is determined by `law(ξ)`
(`map_initBrownian_eq`); their a.s. limits `V = (eulLim q)_q` have equal laws
(`map_eq_of_tendsto_ae`); `V_q = Y_q` for rational `q ≤ τ` (`eulLim_eq_of_le`), so `τ = exitQ(V)`
(`exitQ_eq`) and `Y_{t∧τ}` is the a.s. limit of the measurable functionals `V_{ρ_j(t ∧ exitQ V)}`
(dyadic `ρ_j(s) ↑ s`).
-/

namespace BlockBand.SourceProcess.Stochastic.Uniqueness
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.GeneralIntegral
open BlockBand.SourceProcess.Stochastic.Levy
open BlockBand.SourceProcess.Stochastic.Representation
open BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal ENNReal

variable {d : ℕ}

/-- A stopped solution driven by a filtration Brownian motion (see the module docstring). -/
structure EulerSetup (c : LipCoef d) (W : Set (Fin d → ℝ)) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] where
  𝓕 : Filtration ℝ≥0 mΩ
  B : ℝ≥0 → Ω → Fin d → ℝ
  ξ : Ω → Fin d → ℝ
  τ : Ω → WithTop ℝ≥0
  Y : ℝ≥0 → Ω → Fin d → ℝ
  γY : Fin d → Fin d → ℝ × Ω → ℝ
  hB : IsFiltrationBrownian P 𝓕 B
  hξ : Measurable[𝓕 0] ξ
  hτ : IsStoppingTime 𝓕 τ
  hτe : ∀ᵐ ω ∂P, τ ω = exitTimeFrom W Y ω
  hYm : ∀ t, Measurable (Y t)
  hYc : ∀ᵐ ω ∂P, Continuous fun t => Y t ω
  hγY : ∀ i l, IsBddPred 𝓕 (γY i l)
  hγYe : ∀ᵐ ω ∂P, ∀ r : ℝ, 0 < r → ∀ i l, γY i l (r, ω) =
    (stopSet τ).indicator (fun p => c.σ (Y p.1.toNNReal p.2) i l) (r, ω)
  hrep : ∀ n : ℕ, haveI := hB.isL2IntegratorVec.isFiniteMeasure_bar (n : ℝ≥0)
    ∀ᵐ ω ∂P, ∀ t ≤ (n : ℝ≥0), ∀ i, Y (stopTime (τ ω) t) ω i = ξ ω i +
      ((∫ r in Ioc (0 : ℝ) t, (stopSet τ).indicator
          (fun p => c.b (Y p.1.toNNReal p.2) i) (r, ω)) +
        hB.isL2IntegratorVec.vecCont (n : ℝ≥0) (fun l => bpL2 _ (hγY i l)) t ω)

/-- The dyadic rational below `s`: `ρ_j(s) = 2^{-j} (⌈s 2^j⌉ - 1)`. -/
def rhoQ (j : ℕ) (s : ℝ≥0) : ℚ≥0 := gridQ j (gridIdx j s)

theorem rhoQ_le (j : ℕ) (s : ℝ≥0) : ((rhoQ j s : ℚ≥0) : ℝ≥0) ≤ s := by
  rw [rhoQ, coe_gridQ]
  rcases eq_or_ne s 0 with h | h
  · subst h; simp [gridIdx_zero, gridT_zero]
  · exact (gridT_idx_lt (pos_iff_ne_zero.2 h)).le

theorem tendsto_rhoQ (s : ℝ≥0) :
    Tendsto (fun j => ((rhoQ j s : ℚ≥0) : ℝ≥0)) atTop (𝓝 s) := by
  rw [← NNReal.tendsto_coe]
  have hup : ∀ j, (s : ℝ) - 1 / 2 ^ j ≤ ((rhoQ j s : ℚ≥0) : ℝ≥0) := fun j => by
    have h1 := le_gridT_idx_succ j s
    have h2 := gridT_succ_sub j (gridIdx j s)
    rw [rhoQ, coe_gridQ]
    have : (s : ℝ) ≤ gridT j (gridIdx j s + 1) := h1
    linarith
  have hlow : ∀ j, (((rhoQ j s : ℚ≥0) : ℝ≥0) : ℝ) ≤ s := fun j => rhoQ_le j s
  have h0 : Tendsto (fun j : ℕ => (s : ℝ) - 1 / 2 ^ j) atTop (𝓝 s) := by
    have : Tendsto (fun j : ℕ => (1 : ℝ) / 2 ^ j) atTop (𝓝 0) := by
      simpa [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
    simpa using this.const_sub (s : ℝ)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h0 tendsto_const_nhds hup hlow

/-- The reconstruction functional `v ↦ (v_{ρ_j(t ∧ exitQ v)})_{t ∈ I}`. -/
def reconQ (W : Set (Fin d → ℝ)) (I : Finset ℝ≥0) (j : ℕ) (v : ℚ≥0 → Fin d → ℝ) :
    I → Fin d → ℝ :=
  fun t => v (rhoQ j (stopTime (exitQ Wᶜ v) t))

theorem measurable_reconQ (W : Set (Fin d → ℝ)) (I : Finset ℝ≥0) (j : ℕ) :
    Measurable (reconQ W I j) := by
  refine Measurable.of_eval fun t => ?_
  have hs : Measurable fun v : ℚ≥0 → Fin d → ℝ => stopTime (exitQ Wᶜ v) t :=
    Measurable.untopA (measurable_const.min (measurable_exitQ Wᶜ))
  have hn : Measurable fun v : ℚ≥0 → Fin d → ℝ => gridIdx j (stopTime (exitQ Wᶜ v) t) :=
    (measurable_of_countable fun n : ℕ => n - 1).comp (Nat.measurable_ceil.comp
      (hs.mul_const _))
  have h1 : Measurable fun p : (ℚ≥0 → Fin d → ℝ) × ℕ => p.1 (gridQ j p.2) :=
    measurable_from_prod_countable_left fun n => measurable_pi_apply (gridQ j n)
  exact h1.comp (measurable_id.prodMk hn)

end BlockBand.SourceProcess.Stochastic.Uniqueness
