module

public import BlockBand.SourceProcess.ClosedSum.Derived
public import BlockBand.SourceProcess.ClosedLimit.Frame

/-!
# The finite-`W` closed Gram process at every length

On `SampledPath W p M × ℝ` (path, sampled tags `k_{a,l}`, Gaussians `g_{a,l}`, phase `θ`,
`z = e^{iθ}`), at every length `j`, the closed frame is `C_j(z)ᴴ X_j`, where `C_j(z)` is the
closing map with the time-`s` data (`physClosingMapAt`) and `X_j` has
* probe columns `√(m_a/(MW)) 𝒰_jᴴ ι_{k_{a,l}} g_{a,l}`, which vanish before the birth
  (`k_{a,l} ≥ j`).

`closedGramAt = gramPair P (C_j(z)ᴴ X_j)`. By `ae_closedCurrent_iterate_disc` the current columns
are a.s. the closed transports `(N^cl_{n_s}⋯N^cl_{j-1})ᴴ V_s`. Proved:
* **`closedFrameAt_final`**, **`cappedClosedTransform_eq_closedGramAt`**: at the final length
  `⌊WT⌋` the frame is `closedFrame`, so the capped closed transform is
  `E[1_cap · sampledTransformValue a (closedGramAt ⌊WT⌋)]`;
* **`ae_closedGramAt_start`**: with `V_s` = the current block of `physCurFrame`, almost surely,
  for every sample with no tag born before `n_s` and every phase, `closedGramAt n_s =
  initialGram K π t h` (the initial condition at finite `W`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedSum

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedIdent
open BlockBand.Transmission.Bridge

variable {W p K M : ℕ}

/-- The unclosed frame `X_j`: transported current columns and the sampled probe columns. -/
def openFrameAt (b E s T : ℝ) (q : Fin p → ℝ → ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (x : SampledPath W p M) :
    Matrix (Fin 2 × Fin W) (SrcCol K (Fin p × Fin M)) ℂ :=
  Matrix.of fun z col => Sum.elim
    (fun k => ((stepProd (fun i => transportN b E W i x.1) (closeLen s W) (j - closeLen s W))ᴴ *
      Vs x.1) z k)
    (fun il => ((Real.sqrt (probeWeight T q M W il.1) : ℝ) : ℂ) *
      ((boundaryToInterior b E W j x.1)ᴴ *ᵥ SourceProcessLaw.tagVector W j (x.2.1 il) (x.2.2 il)) z) col

/-- **The closed frame at length `j`**: `C_j(z)ᴴ X_j`. -/
def closedFrameAt (b E s T h : ℝ) (q : Fin p → ℝ → ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (y : SampledPath W p M × ℝ) : Matrix (Fin 2 × Fin W) (SrcCol K (Fin p × Fin M)) ℂ :=
  (physClosingMapAt b E s h W j y.1.1 (phase y.2))ᴴ * openFrameAt b E s T q W j Vs y.1

/-- **The closed Gram coordinates at length `j`.** -/
def closedGramAt (b E s T h : ℝ) (q : Fin p → ℝ → ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (y : SampledPath W p M × ℝ) : GramState (SrcCol K (Fin p × Fin M)) :=
  gramPair (nearPortProj W) (closedFrameAt b E s T h q W j Vs y)

/-- The current block of a frame. -/
def curBlock {ι π : Type*} (V : Matrix ι (SrcCol K π) ℂ) : Matrix ι (Fin K × Fin 2) ℂ :=
  Matrix.of fun z k => V z (Sum.inl k)

/-- **At the final length the closed frame is `closedFrame`.** -/
theorem closedFrameAt_final (b E s T h : ℝ) (q : Fin p → ℝ → ℝ) (W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (y : SampledPath W p M × ℝ) :
    closedFrameAt b E s T h q W ⌊(W : ℝ) * T⌋₊ Vs y =
      closedFrame b E s T h q W (curBlock (closedFrameAt b E s T h q W ⌊(W : ℝ) * T⌋₊ Vs y)) y := by
  ext z (k | il)
  · rfl
  · simp only [closedFrame, closedProbeFrame, closedProbeCol, of_apply, Sum.elim_inr,
      closedFrameAt, openFrameAt, physClosingMapAt_final, mul_apply, mulVec, dotProduct,
      probeVec, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring_nf

/-- **The capped closed transform from the closed Gram process at the final length.** -/
theorem cappedClosedTransform_eq_closedGramAt (b E s T h : ℝ) {J : ℕ} {q : Fin p → ℝ → ℝ}
    (hq : ∀ i x, 0 ≤ q i x) (a : Fin J → Fin p → ℝ) (W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) :
    cappedClosedTransform b E s T h q a K M W =
      ∫ y, (physCapEvent b E s h K W).indicator (fun _ => (1 : ℝ)) y.1.1 *
          sampledTransformValue a (closedGramAt b E s T h q W ⌊(W : ℝ) * T⌋₊ Vs y)
        ∂((sampledPathLaw b W ⌊(W : ℝ) * T⌋₊ q M).prod phaseLaw) := by
  rw [cappedClosedTransform_eq_gram b E s T h hq a W
    (fun y => curBlock (closedFrameAt b E s T h q W ⌊(W : ℝ) * T⌋₊ Vs y))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [closedGramAt, closedGram, ← closedFrameAt_final]

/-- With `V_s` the current block of `physCurFrame` and no tag born before `n_s`, the open frame
at `n_s` is `physCurFrame`. -/
theorem openFrameAt_start (b E s T h : ℝ) (q : Fin p → ℝ → ℝ) (W : ℕ) (x : SampledPath W p M)
    (hk : ∀ il, closeLen s W ≤ x.2.1 il) :
    openFrameAt b E s T q W (closeLen s W)
        (fun ω => curBlock (physCurFrame b E s h K (Fin p × Fin M) W ω)) x =
      physCurFrame b E s h K (Fin p × Fin M) W x.1 := by
  ext z (k | il)
  · simp [openFrameAt, curBlock, stepProd]
  · have h0 : SourceProcessLaw.tagVector W (closeLen s W) (x.2.1 il) (x.2.2 il) = 0 := by
      funext y; simp [SourceProcessLaw.tagVector, not_lt.2 (hk il)]
    simp only [openFrameAt, of_apply, Sum.elim_inr, h0, mulVec_zero, Pi.zero_apply, mul_zero]
    simp [physCurFrame, curFrame, mul_apply, initialFrame]

/-- **The closed Gram process starts at `initialGram`**, almost surely, for every sample with no
tag born before `n_s` and every phase (the initial condition at finite `W`). -/
theorem ae_closedGramAt_start (b E s T h : ℝ) (q : Fin p → ℝ → ℝ) (hb : b < 1 / 2)
    (hE1 : -2 < E) (hE2 : E < 2) (hW : 1 ≤ W) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ (km : (Fin p × Fin M → ℕ) × (Fin p × Fin M → Fin W → ℂ))
      (θ : ℝ), (∀ il, closeLen s W ≤ km.1 il) →
      closedGramAt b E s T h q W (closeLen s W)
          (fun ω => curBlock (physCurFrame b E s h K (Fin p × Fin M) W ω)) ((ω, km), θ) =
        initialGram K (Fin p × Fin M) (physTseq b E s W ω) h := by
  filter_upwards [ae_gramPair_closedCurFrame_timeS (s := s) (Fin p × Fin M) hb hE1 hE2 hW]
    with ω hG km θ hk
  rw [closedGramAt, closedFrameAt, openFrameAt_start b E s T h q W (ω, km) hk]
  exact hG K h (phase θ)

end BlockBand.SourceProcess.ClosedSum
