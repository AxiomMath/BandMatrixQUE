module

public import BlockBand.SourceProcess.PhysApprox.B3Bridges
public import BlockBand.SourceProcess.PhysApprox.B3BridgesJet

/-!
# One closed `δ₀`-jet family for both closed-jet hypotheses

The final assembly uses two closed `δ₀`-jet hypotheses at the closed input `b3ClosedX`, both
stated in other modules:

* `ClosedJetL4Fam b3ClosedX`: whole space, `L⁴`, `E δ₀⁴ ≤ C/W⁴`, at every step
  `n_s ≤ j < ⌊WT⌋` after the first birth;
* `ClosedJet0Lp`: on the alive set `A_j`, every `p ≥ 1`, `C_p/W`, at every no-birth step
  `n_s ≤ j < ⌊WT⌋`.

Both integrands are `jetDistance0 b E (b3ClosedX b E s h τ m W j y)` under
`closedLaw b W np`; no identification through `b3Jet` is needed (`b3Jet` enters only `δ₁`).

* **`ClosedJet0Fam`**, stated as a hypothesis: whole space, every `p ≥ 1`,
  `‖δ₀(X_cl,j)‖_p ≤ C_p/W`, at every step `n_s ≤ j < ⌊WT⌋`. It is the conclusion shape of
  `closedJetLp_of` at `Xcl = b3ClosedX`;
* **`closedJetL4Fam_of_fam`**: `ClosedJet0Fam ⇒ ClosedJetL4Fam b3ClosedX` (`p = 4`, raised to
  the fourth power; the birth restriction is dropped);
* **`closedJet0Lp_of_fam`**: `ClosedJet0Fam ⇒ ClosedJet0Lp` (`‖1_A f‖_p ≤ ‖f‖_p`; the no-birth
  steps lie in `[n_s, ⌊WT⌋)`);
* `closedJetHalf_of_fam`, `covErrMoments_b3CovErr_of_fam`, `b3ClosedJetLp_of_fam`: the
  downstream consumers with `ClosedJet0Fam` in place of the two hypotheses.

`b3ClosedX` reads only the path and the phase (`τ, m` are unused), so births do not act on
`δ₀(X_cl,j)`: the step set `[n_s, ⌊WT⌋)` costs nothing over the two step sets except the start
`j = n_s`, which `ClosedJet0Lp` already needs on `A_{n_s}`. The whole-space bound off the alive
set is the deterministic port bound `δ₀ ≤ η⁻¹ + |a|` for passive `X_cl`, paid by the probability
of an exit.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.Bridge
open BlockBand.SourceProcess.ClosedPath
open scoped NNReal ENNReal

/-- **`ClosedJet0Fam`: the closed `δ₀` jet in every `L^p`, whole space, at the `W⁻¹` scale**
(the passive jet moments at the closed input): on the domain, for every `p ≥ 1`, eventually, at
every step `n_s ≤ j < ⌊WT⌋`, `‖δ₀(X_cl,j)‖_p ≤ C_p/W`. -/
def ClosedJet0Fam : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ p : ℝ, 1 ≤ p → ∃ C : ℝ, ∀ᶠ W in atTop,
      ∀ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊,
        eLpNorm (fun y => jetDistance0 b E (b3ClosedX b E s h τ m W j y)) (ENNReal.ofReal p)
          (closedLaw b W np) ≤ ENNReal.ofReal (C / W)

/-- `∫ f⁴ ≤ a⁴` from `‖f‖₄ ≤ a < ∞`, for `f ≥ 0` (measurability from the finite norm). -/
theorem jetFam_lintegral_four_le {α : Type*} [MeasurableSpace α] (μ : Measure α) {f : α → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) {a : ℝ} (ha : 0 ≤ a)
    (h : eLpNorm f (ENNReal.ofReal 4) μ ≤ ENNReal.ofReal a) :
    ∫⁻ x, ENNReal.ofReal (f x ^ 4) ∂μ ≤ ENNReal.ofReal (a ^ 4) := by
  have hfm : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_eLpNorm_ne_top (h.trans_lt ENNReal.ofReal_lt_top).ne
  have h4 : ENNReal.ofReal 4 ≠ 0 := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h4 ENNReal.ofReal_ne_top hfm,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 4)] at h
  have e : ∀ x, ‖f x‖ₑ ^ (4 : ℝ) = ENNReal.ofReal (f x ^ 4) := fun x => by
    rw [Real.enorm_eq_ofReal (hf0 x), ENNReal.rpow_ofNat, ENNReal.ofReal_pow (hf0 x)]
  simp_rw [e] at h
  have h' := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 4)
  rwa [← ENNReal.rpow_mul, one_div_mul_cancel (by norm_num), ENNReal.rpow_one,
    ENNReal.rpow_ofNat, ← ENNReal.ofReal_pow ha] at h'

/-- **`ClosedJetL4Fam b3ClosedX` from the family** (`p = 4`; `(C/W)⁴ = C⁴/W⁴`). -/
theorem closedJetL4Fam_of_fam (hJ : ClosedJet0Fam) : ClosedJetL4Fam b3ClosedX := by
  intro b E np τ m T s h K Vs hD
  obtain ⟨C, hev⟩ := hJ b E np τ m T s h K Vs hD 4 (by norm_num)
  refine ⟨max C 0 ^ 4, ?_⟩
  filter_upwards [hev] with W hW j hj _
  have hb : eLpNorm (fun y => jetDistance0 b E (b3ClosedX b E s h τ m W j y))
      (ENNReal.ofReal 4) (closedLaw b W np) ≤ ENNReal.ofReal (max C 0 / W) :=
    (hW j hj).trans (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg W)))
  refine (jetFam_lintegral_four_le _ (fun y => norm_nonneg _)
    (div_nonneg (le_max_right _ _) (Nat.cast_nonneg W)) hb).trans (le_of_eq ?_)
  rw [div_pow]

/-- **`ClosedJet0Lp` from the family** (`‖1_{A_j} f‖_p ≤ ‖f‖_p`). -/
theorem closedJet0Lp_of_fam (hJ : ClosedJet0Fam) : ClosedJet0Lp := by
  intro b E np τ m T s h K Vs hF R p hp
  obtain ⟨C, hev⟩ := hJ b E np τ m T s h K Vs hF p hp
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  filter_upwards [hev, hF.2.2.2.2.2] with W hW hVW j hj
  have hjI : j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊ := (Finset.mem_filter.1 hj).1
  have hV : Measurable (Vs W) :=
    hVW.1.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  obtain ⟨⟨-, hb1, hE1, hE2, -⟩, -⟩ := id hF
  refine (eLpNorm_indicator_le _ (nullMeasurableSet_b3Alive (by linarith) hE1 hE2 s h τ m R W j
    hV)).trans ((hW j hjI).trans (ENNReal.ofReal_le_ofReal ?_))
  exact div_le_div_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg W)

/-- `ClosedJetHalf b3ClosedX` from the family. -/
theorem closedJetHalf_of_fam (hJ : ClosedJet0Fam) : ClosedJetHalf b3ClosedX :=
  closedJetHalf_of_L4Fam (closedJetL4Fam_of_fam hJ)

/-- `CovErrMoments b3CovErr` from the family and the two other closed estimates. -/
theorem covErrMoments_b3CovErr_of_fam (hJ : ClosedJet0Fam) (h1 : ClosedJet1Lp)
    (hg : ClosedCondLp) : CovErrMoments b3CovErr :=
  covErrMoments_b3CovErr (closedJet0Lp_of_fam hJ) h1 hg

/-- `B3ClosedJetLp` from the family, the two other closed estimates and the step-form hypothesis
(passivity of `b3ClosedX`, through `b3ClosedJetLp_of_jets`). -/
theorem b3ClosedJetLp_of_fam (hJ : ClosedJet0Fam) (h1 : ClosedJet1Lp) (hg : ClosedCondLp)
    (hF : ClosedKStepForm b3ClosedX) : B3DecayIn.B3ClosedJetLp :=
  b3ClosedJetLp_of_jets (closedJet0Lp_of_fam hJ) h1 hg hF

end BlockBand.SourceProcess.PhysApprox.B3
