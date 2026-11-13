module

public import BlockBand.SourceProcess.ClosedSum.ClosedGram

/-!
# `ClosedSummed`: the closed-path analogue of `EarlySummed`

**`ClosedSummed`** expresses that the full-source calculation applies with finitely many far open
channels, with errors uniform at this fixed rank and probe number. On
`sampledPathLaw ⊗ phaseLaw` with filtration `closedSigma j = σ(A_{<j}, B_{≤j}) ⊗ σ(samples, θ)`,
for the closed Gram process `closedGramAt`, restricted to `physCapEvent`
and before the trace stop `Re Tr M < R`, the summed `L¹` errors over `n_s ≤ j < ⌊WT⌋`
* of the conditional drift `E_j ΔG_e - W⁻¹ b_e(G_j)` at steps without a birth,
* of the conditional bracket `E_j ΔG_e ΔG_e' - W⁻¹ c_{ee'}(G_j)` at steps without a birth,
* of the birth jump `ΔG_e - (birth of the probes with k_{a,l} = j)` at birth steps
  (squared norm `d_* m_a/M`, near, zero overlaps)
tend to `0` as `W → ∞`. `b_e, c_{ee'}` are the finite Gram law coefficients `gramDriftEntry` and
`gramCovEntry` with `D₀ = transportD0 b E`, `𝖣 = srcSignature`.

*Caveat.* As in `EarlySummed`, Mathlib's conditional expectation of a non-integrable function is
`0`; the statement then asks the corresponding `W⁻¹`-terms to be summably small. The needed
moments come from closing at time `s` (bounded near-reflector corrections).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedSum

open MeasureTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedIdent
open BlockBand.Transmission.Bridge
open scoped ENNReal

variable {W p K M : ℕ}

/-- The current block of a Gram state. -/
def curGramOf {π : Type*} (G : GramState (SrcCol K π)) : GramState (Fin K × Fin 2) :=
  (G.1.submatrix Sum.inl Sum.inl, G.2.submatrix Sum.inl Sum.inl)

/-- **Admissible time-`s` frames**: `growthSigma W n_s`-measurable, and almost surely with the
Gram state of `initialGram` and `±√t_k` eigencolumns of `P' - P`. -/
def IsTimeSFrame (b E s h : ℝ) (K W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) : Prop :=
  Measurable[growthSigma W (closeLen s W)] Vs ∧ ∀ᵐ ω ∂growthPathLaw W b,
    gramPair (nearPortProj W) (Vs ω) = curGramOf (initialGram K (Fin 0) (physTseq b E s W ω) h) ∧
    ∀ x k, ((physOutProj b E s W ω - nearPortProj W) * Vs ω) x k =
      modeEig (physTseq b E s W ω k.1.val) k.2 * Vs ω x k

theorem gramPair_curBlock {ι π : Type*} [Fintype ι] (P : Matrix ι ι ℂ)
    (V : Matrix ι (SrcCol K π) ℂ) : gramPair P (curBlock V) = curGramOf (gramPair P V) := by
  ext <;> simp [gramPair, sourceGram, nearGram, curGramOf, curBlock, mul_apply]

theorem curGramOf_initialGram (π : Type*) (t : ℕ → ℝ) (h : ℝ) :
    curGramOf (initialGram K π t h) = curGramOf (initialGram K (Fin 0) t h) := by
  ext <;> simp [curGramOf, initialGram, gramPair, sourceGram, nearGram, initialFrame, mul_apply]

/-- **The current block of `physCurFrame` satisfies the almost-sure clauses of `IsTimeSFrame`**
(its measurability in `ω` is not part of this statement). -/
theorem ae_timeSFrame_phys {b E s : ℝ} (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hW : 1 ≤ W) (h : ℝ) :
    ∀ᵐ ω ∂growthPathLaw W b,
      gramPair (nearPortProj W) (curBlock (physCurFrame b E s h K (Fin 0) W ω)) =
        curGramOf (initialGram K (Fin 0) (physTseq b E s W ω) h) ∧
      ∀ x k, ((physOutProj b E s W ω - nearPortProj W) *
          curBlock (physCurFrame b E s h K (Fin 0) W ω)) x k =
        modeEig (physTseq b E s W ω k.1.val) k.2 * curBlock (physCurFrame b E s h K (Fin 0) W ω) x k := by
  filter_upwards [FullSourceStops.ae_scattering_unitary hb hE1 hE2 hW,
    ae_hlt (s := s) hb hE1 hE2 hW, ae_physCurFrame_eigen (s := s) (Fin 0) hb hE1 hE2 hW]
    with ω hU hlt hEig
  refine ⟨?_, fun x k => ?_⟩
  · rw [gramPair_curBlock, gramPair_physCurFrame _ (hU _).1 (hlt K h)]
  · have := hEig K h x k.1 k.2
    simpa [curBlock, mul_apply] using this

/-- **A measurable time-`s` frame exists**: a measurable selection of the retained far
eigenvectors (sorted eigenvalues `t_k > h²`, phases fixed through the far vector). Proved as
`ClosedReduce.existsTimeSFrame_holds`.
-/
def ExistsTimeSFrame : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ s : ℝ, 0 < s → ∀ h : ℝ, 0 < h →
    h < 1 → ∀ K : ℕ, ∀ᶠ W in atTop, ∃ Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ,
      IsTimeSFrame b E s h K W Vs

/-- The closed filtration at length `j`: the path up to `j` (`growthSigma W j`), the samples and
the phase. -/
abbrev closedSigma (W j p M : ℕ) : MeasurableSpace (SampledPath W p M × ℝ) :=
  MeasurableSpace.comap (fun y : SampledPath W p M × ℝ => (pastCoords W j y.1.1, y.1.2, y.2))
    inferInstance

/-- Alive at `j`: on the physical cap event and `Re Tr M_i < R` for `n_s ≤ i ≤ j`. -/
def closedAlive (b E s T h : ℝ) (q : Fin p → ℝ → ℝ) (R : ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) :
    Set (SampledPath W p M × ℝ) :=
  {y | y.1.1 ∈ physCapEvent b E s h K W ∧ ∀ i, closeLen s W ≤ i → i ≤ j →
    ((closedGramAt b E s T h q W i Vs y).1.trace).re < R}

/-- No probe is born at step `j → j+1` (`k_{a,l} ≠ j`). -/
def noBirth (j : ℕ) : Set (SampledPath W p M × ℝ) := {y | ∀ il, y.1.2.1 il ≠ j}

/-- The model birth jump of the probes born at step `j` (squared norm `d_* m_a/M`). -/
def birthAt (b s T : ℝ) (q : Fin p → ℝ → ℝ) (j : ℕ) (y : SampledPath W p M × ℝ) :
    GramState (SrcCol K (Fin p × Fin M)) :=
  ∑ il, if y.1.2.1 il = j then
    ((((dStar b * sourceMass s T (q il.1) / M : ℝ)) : ℂ) • Matrix.single (Sum.inr il) (Sum.inr il) 1,
      (((dStar b * sourceMass s T (q il.1) / M : ℝ)) : ℂ) • Matrix.single (Sum.inr il) (Sum.inr il) 1)
  else 0

/-- **The three summed errors** of `ClosedSummed` at width `W`. -/
def closedSummedErr (b E s T h : ℝ) (q : Fin p → ℝ → ℝ) (R : ℝ) (W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (e e' : Fin 2 × SrcCol K (Fin p × Fin M) × SrcCol K (Fin p × Fin M)) : ℝ≥0∞ :=
  let μ := (sampledPathLaw b W ⌊(W : ℝ) * T⌋₊ q M).prod phaseLaw
  let G : ℕ → SampledPath W p M × ℝ → GramState (SrcCol K (Fin p × Fin M)) :=
    fun j => closedGramAt b E s T h q W j Vs
  let A : ℕ → Set (SampledPath W p M × ℝ) := fun j => closedAlive b E s T h q R W j Vs ∩ noBirth j
  let B : ℕ → Set (SampledPath W p M × ℝ) := fun j => closedAlive b E s T h q R W j Vs \ noBirth j
  let D0 := transportD0 b E
  let D := srcSignature K (Fin p × Fin M)
  let steps := Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊
  (∑ j ∈ steps, ∫⁻ y, ‖(A j).indicator (fun y =>
      μ[(A j).indicator (fun y => gramEntry e (G (j + 1) y) - gramEntry e (G j y)) |
        closedSigma W j p M] y - (W : ℂ)⁻¹ * gramDriftEntry D0 D e (G j y)) y‖ₑ ∂μ) +
  (∑ j ∈ steps, ∫⁻ y, ‖(A j).indicator (fun y =>
      μ[(A j).indicator (fun y => (gramEntry e (G (j + 1) y) - gramEntry e (G j y)) *
          (gramEntry e' (G (j + 1) y) - gramEntry e' (G j y))) | closedSigma W j p M] y -
        (W : ℂ)⁻¹ * gramCovEntry D0 D e e' (G j y)) y‖ₑ ∂μ) +
  (∑ j ∈ steps, ∫⁻ y, ‖(B j).indicator (fun y =>
      gramEntry e (G (j + 1) y - G j y - birthAt b s T q j y)) y‖ₑ ∂μ)

/-- **`ClosedSummed`**, with the births: for every
admissible time-`s` frame, the summed drift, bracket and birth errors of the closed Gram
coordinates on the cap event and before the trace stop tend to `0`. This is stated as a
hypothesis. -/
def ClosedSummed : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ s T : ℝ, 0 < s → s < T →
    ∀ (p : ℕ) (q : Fin p → ℝ → ℝ), (∀ i, IsSourceTest s T (q i)) → ∀ h : ℝ, 0 < h → h < 1 →
    ∀ K M : ℕ, 0 < M → ∀ R : ℝ,
    ∀ Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ,
      (∀ᶠ W in atTop, IsTimeSFrame b E s h K W (Vs W)) →
    ∀ e e' : Fin 2 × SrcCol K (Fin p × Fin M) × SrcCol K (Fin p × Fin M),
      Tendsto (fun W => closedSummedErr b E s T h q R W (Vs W) e e') atTop (𝓝 0)

end BlockBand.SourceProcess.ClosedSum
