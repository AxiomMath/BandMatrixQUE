module

public import BlockBand.SourceProcess.ClosedSum.Resolvent
public import BlockBand.SourceProcess.ClosedSum.Retained
public import BlockBand.SourceProcess.ClosedSum.ModeEigen

/-!
# The closed time-`s` frame theorems without their extra hypotheses

All statements are almost sure under `growthPathLaw W b`, uniform in the remaining parameters:

* **`ae_gramPair_closedCurFrame_timeS`** (`b < 1/2`, `-2 < E < 2`, `W ≥ 1`): for every `K`, `h`
  and phase `z`, the frame closed at time `s` has Gram state exactly `initialGram K π t h`
  (the hypothesis `hS` from `ae_scattering_unitary`, `hlt` from `ae_hlt`).
* **`ae_physCurFrame_eigen`**: every current column at time `s` is an eigenvector of
  `P' - P` with eigenvalue `±√t_k`.
* **`ae_closedCol_transport_disc`** (`0 < b < 1/2`, `h² < 1`): the one-step closed transport
  identity for every `j ≥ 1` and every `‖z‖ ≤ 1`, with no invertibility hypothesis.
* **`ae_closedCurrent_iterate_disc`** (also `1 ≤ n_s`): the iterated identity
  `C_{n_s+m}(z)ᴴ (N_{n_s}⋯N_{n_s+m-1})ᴴ V_s = (N^cl_{n_s}⋯N^cl_{n_s+m-1})ᴴ V_s`
  for every `m` and every `‖z‖ ≤ 1`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedSum

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.SourceProcess.Stochastic
open BlockBand.Transmission.Bridge BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedLimit

variable {W : ℕ} {b E s : ℝ}

/-- **The frame closed at time `s` has Gram state `initialGram`, almost surely.** -/
theorem ae_gramPair_closedCurFrame_timeS (π : Type*) (hb : b < 1 / 2) (hE1 : -2 < E)
    (hE2 : E < 2) (hW : 1 ≤ W) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ (K : ℕ) (h : ℝ) (z : ℂ),
      gramPair (nearPortProj W) ((physClosingMapAt b E s h W (closeLen s W) ω z)ᴴ *
        physCurFrame b E s h K π W ω) = initialGram K π (physTseq b E s W ω) h := by
  filter_upwards [FullSourceStops.ae_scattering_unitary hb hE1 hE2 hW,
    ae_hlt (s := s) hb hE1 hE2 hW] with ω hU hlt K h z
  exact gramPair_closedCurFrame_timeS π z (hU _).1 (hlt K h)

/-- **The current columns at time `s` are `±√t_k` eigenvectors of `P' - P`, almost surely.** -/
theorem ae_physCurFrame_eigen (π : Type*) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hW : 1 ≤ W) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ (K : ℕ) (h : ℝ) (x : Fin 2 × Fin W) (k : Fin K) (σ : Fin 2),
      ((physOutProj b E s W ω - nearPortProj W) * physCurFrame b E s h K π W ω) x
          (Sum.inl (k, σ)) =
        modeEig (physTseq b E s W ω k.val) σ * physCurFrame b E s h K π W ω x (Sum.inl (k, σ)) := by
  filter_upwards [FullSourceStops.ae_scattering_unitary hb hE1 hE2 hW,
    ae_hlt (s := s) hb hE1 hE2 hW] with ω hU hlt K h x k σ
  exact sub_mul_curFrame π nearPortProj_mul_self (physOutProj_mul_self (hU _).1)
    nearPortProj_mul_physF physF_conj_mul_self (one_sub_mul_physOutProj_mul_physF (hU _).1)
    (fun k hk => ⟨lt_of_le_of_lt (sq_nonneg h) hk, hlt K h k hk⟩) x k σ

/-- **One-step closed transport, for every phase in the closed unit disc**, almost surely. -/
theorem ae_closedCol_transport_disc {h : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E)
    (hE2 : E < 2) (hW : 1 ≤ W) (hh : h ^ 2 < 1) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ j, 1 ≤ j → ∀ z : ℂ, ‖z‖ ≤ 1 →
      (physClosingMapAt b E s h W (j + 1) ω z)ᴴ * (transportN b E W j ω)ᴴ =
        ((1 - farEmbed (omittedProj b E h W (closeLen s W) ω)) *
          (transportN b E W j ω * physClosingMapAt b E s h W (j + 1) ω z))ᴴ *
          (physClosingMapAt b E s h W j ω z)ᴴ := by
  filter_upwards [ae_closedCol_transport (s := s) (h := h) hb0 hb hE1 hE2 hW,
    ae_isUnit_closingResolvent hb0 hb hE1 hE2 hW hh (closeLen s W)] with ω hT hR j hj z hz
  exact hT j hj z (hR j hj z hz) (hR (j + 1) (by omega) z hz)

/-- **The closed current columns are the closed transports of the time-`s` frame**, for every
`m` and every phase in the closed unit disc, almost surely. -/
theorem ae_closedCurrent_iterate_disc (π : Type*) {h : ℝ} {K : ℕ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hE1 : -2 < E) (hE2 : E < 2) (hW : 1 ≤ W) (hh : h ^ 2 < 1) (hs : 1 ≤ closeLen s W) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ (m : ℕ) (z : ℂ), ‖z‖ ≤ 1 →
      (physClosingMapAt b E s h W (closeLen s W + m) ω z)ᴴ *
          (stepProd (fun j => transportN b E W j ω) (closeLen s W) m)ᴴ *
          physCurFrame b E s h K π W ω =
        (stepProd (closedTransport b E s h W ω z) (closeLen s W) m)ᴴ *
          physCurFrame b E s h K π W ω := by
  filter_upwards [ae_closedCurrent_iterate (K := K) π hb0 hb hE1 hE2 hW hs,
    ae_isUnit_closingResolvent (h := h) hb0 hb hE1 hE2 hW hh (closeLen s W)] with ω hI hR m z hz
  exact hI m z fun i _ => hR _ (by omega) z hz

end BlockBand.SourceProcess.ClosedSum
