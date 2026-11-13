module

public import BlockBand.SourceProcess.PhysApprox.B3DecayInStep
public import BlockBand.SourceProcess.PhysApprox.B3CovRepErr
public import BlockBand.SourceProcess.PhysApprox.B3StepK

/-!
# The jet bridge `ClosedErrLp b3CovErr ⇒ B3ClosedJetLp`

The input `B3ClosedJetLp` of the contracting decay bounds `‖1_A b3LayerErr(sj, X_cl)‖_p` for
every stationary jet `sj`, with `|g|/W`. The hypothesis `ClosedErrLp b3CovErr` bounds
`‖1_A b3LayerErrX(X_cl)‖_p`, at `b3Jet` and with `g/W`. The two integrands agree where `X_cl` is
passive: `sj = b3Jet` (`b3Jet_eq`, uniqueness of the stationary jet) and `g ≥ 0`
(`FullSourceCovariance.conductance_nonneg`). Passivity of `b3ClosedX` a.e. is a clause of the
step form `ClosedKStepForm b3ClosedX`, so no new hypothesis arises.

* `B3ClosedXPassive`, `b3ClosedXPassive_of_stepForm`;
* **`b3ClosedJetLp_of_closedErrLp`**: `ClosedErrLp b3CovErr + B3ClosedXPassive ⇒ B3ClosedJetLp`;
* **`b3ClosedJetLp_of_jets`**: `ClosedJet0Lp + ClosedJet1Lp + ClosedCondLp + ClosedKStepForm
  b3ClosedX ⇒ B3ClosedJetLp` (through `closedErrLp_of_jets`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory ProbabilityTheory Filter Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.Transmission.Bridge
open scoped NNReal ENNReal ComplexOrder

/-- The closed input `b3ClosedX` is a.e. passive at every step `n_s ≤ j < ⌊WT⌋`, eventually. -/
def B3ClosedXPassive : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ᶠ W in atTop,
      ∀ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊,
        ∀ᵐ y ∂closedLaw b W np, (passiveY (b3ClosedX b E s h τ m W j y)).PosSemidef

/-- **Passivity of `b3ClosedX`** is a clause of the step form. -/
theorem b3ClosedXPassive_of_stepForm (hF : ClosedKStepForm b3ClosedX) : B3ClosedXPassive := by
  intro b E np τ m T s h K Vs hD
  obtain ⟨_, hev⟩ := hF b E np τ m T s h K Vs hD 0
  filter_upwards [hev] with W hW j hj
  exact (hW j hj).2.2.1

/-- **The jet bridge**: `ClosedErrLp b3CovErr` and passivity give `B3ClosedJetLp`. -/
theorem b3ClosedJetLp_of_closedErrLp (hE : ClosedErrLp b3CovErr) (hP : B3ClosedXPassive) :
    B3DecayIn.B3ClosedJetLp := by
  intro b E np τ m T s h K Vs hD R p hp
  obtain ⟨hb0, hb, hE1, hE2, -⟩ := hD.1
  have hη : 0 ≤ etaZ b E :=
    (Transmission.PassiveCovariance.etaZ_pos b E (by linarith) hE1 hE2).le
  obtain ⟨C, -, hev⟩ := hE b E np τ m T s h K Vs hD R p hp
  refine ⟨C, ?_⟩
  filter_upwards [hev, hP b E np τ m T s h K Vs hD] with W hW hPW j hj sj hsj
  refine le_of_eq_of_le (eLpNorm_congr_ae ?_) (hW j hj)
  filter_upwards [hPW j (Finset.mem_filter.1 hj).1] with y hy
  by_cases hA : y ∈ b3Alive b E s h τ m R W j (Vs W)
  · rw [Set.indicator_of_mem hA, Set.indicator_of_mem hA]
    simp only [b3CovErr, B3DecayIn.b3LayerErr, b3LayerErrX, b3Jet_eq hb0 hb hE1 hE2 hsj,
      abs_of_nonneg (FullSourceCovariance.conductance_nonneg b E hη hy)]
  · rw [Set.indicator_of_notMem hA, Set.indicator_of_notMem hA]

/-- **`B3ClosedJetLp` from the three closed jets** and the step form. -/
theorem b3ClosedJetLp_of_jets (h0 : ClosedJet0Lp) (h1 : ClosedJet1Lp) (hg : ClosedCondLp)
    (hF : ClosedKStepForm b3ClosedX) : B3DecayIn.B3ClosedJetLp :=
  b3ClosedJetLp_of_closedErrLp (closedErrLp_of_jets h0 h1 hg) (b3ClosedXPassive_of_stepForm hF)

end BlockBand.SourceProcess.PhysApprox.B3
