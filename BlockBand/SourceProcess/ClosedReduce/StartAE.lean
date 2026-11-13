module

public import BlockBand.SourceProcess.ClosedReduce.Start

/-!
# `G₀ = initialGram` and the closed-transport iterate for admissible frames, a.s.

For every admissible time-`s` frame `Vs` (`IsTimeSFrame`), almost surely: the closed Gram process
starts at `initialGram` for every sample with no tag of positive grid mass born before `n_s` and
every phase (`ae_closedGramAt_start_adm`), and the closed current columns are the closed transports
of `Vs` for every phase in the closed unit disc (`ae_closedCurrent_iterate_adm`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedReduce

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedSum
open BlockBand.Transmission.Bridge

variable {W p K M : ℕ} {b E s T h : ℝ}

/-- Closing fixes every frame killed by `A_-`. -/
theorem closedFix {κ : Type*} {n : ℕ} {ω : GrowthPath W} (z : ℂ) {V : Matrix (Fin 2 × Fin W) κ ℂ}
    (hV : farEmbed (omittedProj b E h W (closeLen s W) ω) * V = 0) :
    (physClosingMapAt b E s h W n ω z)ᴴ * V = V := by
  refine closingMap_conj_fix ?_ ?_ hV
  · rw [farEmbed_conjTranspose, omittedProj_conjTranspose]
  · rw [farEmbed_mul, omittedProj_mul_closingPairing]

/-- No tag of positive grid mass is born before `n_s`. A zero-mass test has weight `0`; asking
`n_s ≤ k` for every tag would fail surely for a zero-mass test, whose sampled index is `0`. -/
def StartOK (s T : ℝ) (q : Fin p → ℝ → ℝ) (W : ℕ) (k : Fin p × Fin M → ℕ) : Prop :=
  ∀ il, closeLen s W ≤ k il ∨ gridMass W ⌊(W : ℝ) * T⌋₊ (q il.1) = 0

/-- The open frame at `n_s` (no tag of positive mass born before `n_s`): `[Vs | 0]`. -/
theorem openFrameAt_start_adm (q : Fin p → ℝ → ℝ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (x : SampledPath W p M)
    (hk : StartOK s T q W x.2.1) :
    openFrameAt b E s T q W (closeLen s W) Vs x =
      Matrix.of fun z col => Sum.elim (fun k => Vs x.1 z k) (fun _ => 0) col := by
  ext z (k | il)
  · simp [openFrameAt, stepProd]
  · rcases hk il with hk | hk
    · have h0 : SourceProcessLaw.tagVector W (closeLen s W) (x.2.1 il) (x.2.2 il) = 0 := by
        funext y; simp [SourceProcessLaw.tagVector, not_lt.2 hk]
      simp only [openFrameAt, of_apply, Sum.elim_inr, h0, mulVec_zero, Pi.zero_apply, mul_zero]
    · simp [openFrameAt, probeWeight, hk]

/-- **The closed Gram process of an admissible frame starts at `initialGram`**, almost surely,
for every sample with no tag of positive mass born before `n_s` and every phase. -/
theorem ae_closedGramAt_start_adm (q : Fin p → ℝ → ℝ) (hb : b < 1 / 2) (hE1 : -2 < E)
    (hE2 : E < 2) (hW : 1 ≤ W) {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hVs : IsTimeSFrame b E s h K W Vs) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ (km : (Fin p × Fin M → ℕ) × (Fin p × Fin M → Fin W → ℂ))
      (θ : ℝ), StartOK s T q W km.1 →
      closedGramAt b E s T h q W (closeLen s W) Vs ((ω, km), θ) =
        initialGram K (Fin p × Fin M) (physTseq b E s W ω) h := by
  filter_upwards [hVs.2, FullSourceStops.ae_scattering_unitary hb hE1 hE2 hW]
    with ω ⟨hG, hE⟩ hU km θ hk
  have hA := omitted_mul_timeSFrame (Vs ω) (hU _).1 hG hE
  have hX := openFrameAt_start_adm (b := b) (E := E) (T := T) q Vs (ω, km) hk
  have hAX : farEmbed (omittedProj b E h W (closeLen s W) ω) *
      openFrameAt b E s T q W (closeLen s W) Vs (ω, km) = 0 := by
    rw [hX]
    ext z (k | il)
    · have := congrFun (congrFun hA z) k
      simpa [mul_apply] using this
    · simp [mul_apply]
  rw [closedGramAt, closedFrameAt, closedFix _ hAX, hX]
  have hG1 := congrArg Prod.fst hG
  have hG2 := congrArg Prod.snd hG
  rw [← curGramOf_initialGram (Fin p × Fin M)] at hG1 hG2
  refine Prod.ext ?_ ?_
  · ext (k | il) (k' | il')
    · have := congrFun (congrFun hG1 k) k'
      simpa [gramPair, sourceGram, curGramOf, mul_apply] using this
    all_goals simp [gramPair, sourceGram, initialGram, initialFrame, mul_apply]
  · ext (k | il) (k' | il')
    · have := congrFun (congrFun hG2 k) k'
      simpa [gramPair, nearGram, curGramOf, mul_apply] using this
    all_goals simp [gramPair, nearGram, initialGram, initialFrame, mul_apply]

/-- **The closed current columns of an admissible frame are its closed transports**, for every
`m` and every phase in the closed unit disc, almost surely. -/
theorem ae_closedCurrent_iterate_adm (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E)
    (hE2 : E < 2) (hW : 1 ≤ W) (hh : h ^ 2 < 1) (hs : 1 ≤ closeLen s W)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hVs : IsTimeSFrame b E s h K W Vs) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ (m : ℕ) (z : ℂ), ‖z‖ ≤ 1 →
      (physClosingMapAt b E s h W (closeLen s W + m) ω z)ᴴ *
          (stepProd (fun j => transportN b E W j ω) (closeLen s W) m)ᴴ * Vs ω =
        (stepProd (closedTransport b E s h W ω z) (closeLen s W) m)ᴴ * Vs ω := by
  filter_upwards [hVs.2, FullSourceStops.ae_scattering_unitary hb hE1 hE2 hW,
    ae_closedCol_transport_disc (s := s) (h := h) hb0 hb hE1 hE2 hW hh]
    with ω ⟨hG, hE⟩ hU hT m z hz
  have it := conj_stepProd_iterate (fun j => physClosingMapAt b E s h W j ω z)
    (fun j => transportN b E W j ω) (closedTransport b E s h W ω z) (closeLen s W) m
    (fun i _ => hT _ (by omega) z hz)
  rw [it, Matrix.mul_assoc, closedFix z (omitted_mul_timeSFrame (Vs ω) (hU _).1 hG hE)]

end BlockBand.SourceProcess.ClosedReduce
