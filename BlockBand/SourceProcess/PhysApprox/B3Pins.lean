module

public import BlockBand.SourceProcess.PhysApprox.PinsIdent
public import BlockBand.SourceProcess.ClosedSum.Pins

/-!
# The estimates behind `ComplexClosedLimitLaw`

* **model content** `ComplexTestedOfFinite` (all fixed source moments are bounded): every
  filtered complex model has a modification that is a tested (unstopped) model. Needed only for
  the unstopped form `ComplexClosedLimitLaw`; the stopped form `ComplexClosedLimitLawStopped` needs
  nothing.
* **physical content** `ComplexCapCondLimit` (on the cap event): limit points of the capped
  closed expectation are `μ(s)(capSet) ·` the value of a filtered complex model with the
  conditioned entrance. `ComplexCapCondLimit` implies `ComplexClosedLimitIdentification` and
  `ComplexClosedLimitLawStopped`, and with `ComplexTestedOfFinite` it implies
  `ComplexClosedLimitLaw`.
* the **finite-`W` closed complex process at every length** (`b3ClosedFrameAt`,
  `b3ClosedGramAt`, `b3ClosedKAt`; the analogue of `closedGramAt`, with the deterministic tags of
  `probeFrame` and the closed `𝒦`), and the estimates behind `ComplexCapCondLimit`:
  * `ComplexClosedSummed`: summed drift, bilinear-bracket, conjugate-bracket and birth errors of
    the Gram **and `𝒦`** coordinates, on the cap event, before the Gram trace stop;
  * `ComplexClosedTight`: tightness and modulus of all coordinates;
  * `ComplexKStoppedMoment` (the stop for `𝒦`): uniform fourth moments of the closed `𝒦` before
    the Gram trace stop;
  * `ComplexClosedCurrent`: the closed current coordinate `J_pr` agrees in probability with
    `(M𝖣M)_pr` of the closed Gram process on the cap event;
  * `TargetCapCond`: the limit passage, these estimates ⇒ `ComplexCapCondLimit`. It is the
    complex copy of `ClosedSummed + ClosedTight + EigenSel ⇒ CapCondLimit`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Layers
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open BlockBand.Transmission.Bridge
open scoped NNReal ENNReal ComplexConjugate

/-!
## Model content and physical content
-/

/-- **Model content: filtered complex models have tested modifications** (the complex source
SDE is linear in the noise with Gram-bounded coefficients, and all fixed source moments are
bounded on bounded time intervals, which removes the stops). Every filtered complex model is,
after a modification of `(G, 𝒦)` on null sets, a tested model (unstopped tested identities,
`G − J` and `𝒦 − J_𝒦` continuous for every `ω`). Only the unstopped form
`ComplexClosedLimitLaw` needs it. -/
def ComplexTestedOfFinite : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T : ℝ), ComplexSourceLawDomain b E τ m T →
  ∀ s : ℝ, 0 < s → (∀ j, s < τ j) → ∀ h : ℝ, 0 < h → ∀ (K : ℕ)
    (entrance : Measure (Measure unitInterval))
    (Ω : Type) (mΩ : MeasurableSpace Ω) (𝓖 : Filtration ℝ≥0 mΩ) (Q : Measure Ω)
    (tseq : Ω → ℕ → ℝ) (G : ℝ≥0 → Ω → GramState (SrcCol K (Fin np)))
    (Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ),
    IsFiniteComplexSourceModel b E s τ m h K entrance 𝓖 Q tseq G Kc →
    ∃ (G' : ℝ≥0 → Ω → GramState (SrcCol K (Fin np)))
      (Kc' : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ),
      IsTestedComplexModel b E s τ m h K entrance Q tseq G' Kc' ∧
      ∀ t, G' t =ᵐ[Q] G t ∧ Kc' t =ᵐ[Q] Kc t

/-- Frequently as
`h ↓ 0` and as `K → ∞`, along every `W_n → ∞` on which the capped closed expectation converges
to `L`: if `μ(s)(capSet K h) = 0` then `L = 0`; otherwise some filtered complex model with
entrance `μ(s)` conditioned on `capSet K h` has value `L / μ(s)(capSet K h)` at `T − s`.
Only
the stopped martingale problem of the `IsFiniteComplexSourceModel` is asked, and nothing
off the cap event.
-/
def ComplexCapCondLimit : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T : ℝ), ComplexSourceLawDomain b E τ m T →
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
    (μ : ℝ → Ω → FiniteMeasure unitInterval), IsTransmissionLimit b E (fun _ => 0) P μ →
  ∀ s : ℝ, 0 < s → (∀ j, s < τ j) → ∀ Φ : BoundedContinuousFunction (SourceData np) ℝ,
  ∃ᶠ h in 𝓝[>] (0 : ℝ), ∃ᶠ K in atTop,
    ∀ φ : ℕ → ℕ, Tendsto φ atTop atTop → ∀ L : ℝ,
      Tendsto (fun n => cappedClosedPhysExpectation b E s T h τ m Φ K (φ n)) atTop (𝓝 L) →
      (entranceLaw P μ s (capSet K h) = 0 → L = 0) ∧
      (entranceLaw P μ s (capSet K h) ≠ 0 →
        ∃ (Ω' : Type) (mΩ : MeasurableSpace Ω') (𝓖 : Filtration ℝ≥0 mΩ) (Q : Measure Ω')
          (tseq : Ω' → ℕ → ℝ) (G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin np)))
          (Kc : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ),
          IsFiniteComplexSourceModel b E s τ m h K ((entranceLaw P μ s)[|capSet K h]) 𝓖 Q
            tseq G Kc ∧
          (entranceLaw P μ s (capSet K h)).toReal * modelExpectation K s T Q G Kc Φ = L)

/-!
## The closed complex process at every length
-/

/-- The unclosed frame `X_j` at length `j`: the time-`s` frame `V_s` transported by the physical
path (current columns) and the probe frame `V_pr = 𝒰_jᴴ𝒥` at length `j` (probe columns; a tag
column is present iff `⌊Wτ_i⌋ < j`). -/
def b3OpenFrameAt (b E s : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (x : ProbedPath W np) :
    Matrix (Fin 2 × Fin W) (SrcCol K (Fin np)) ℂ :=
  Matrix.of fun z col => Sum.elim
    (fun k => ((stepProd (fun i => transportN b E W i x.1) (closeLen s W) (j - closeLen s W))ᴴ *
      Vs x.1) z k)
    (fun i => probeFrame b E W j τ m x z i) col

/-- **The closed frame at length `j`**: `C_j(z)ᴴ X_j`, `C_j` the closing map with the time-`s`
omitted channels (`physClosingMapAt`), `z = e^{iθ}`. -/
def b3ClosedFrameAt (b E s h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (y : ProbedPath W np × ℝ) : Matrix (Fin 2 × Fin W) (SrcCol K (Fin np)) ℂ :=
  (physClosingMapAt b E s h W j y.1.1 (phase y.2))ᴴ * b3OpenFrameAt b E s τ m W j Vs y.1

/-- **The closed Gram coordinates at length `j`.** -/
def b3ClosedGramAt (b E s h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)
    (y : ProbedPath W np × ℝ) : GramState (SrcCol K (Fin np)) :=
  gramPair (nearPortProj W) (b3ClosedFrameAt b E s h τ m W j Vs y)

/-- **The closed `𝒦` at length `j`**:
`𝒦_j − 2iηz V_jᴴ(1 − zN_j)⁻¹Π𝕊_jV_j`, `N_j = Π𝕊_jA`, omitted channels chosen at `⌊Ws⌋`. -/
def b3ClosedKAt (b E s h : ℝ) {np : ℕ} (τ m : Fin np → ℝ) (W j : ℕ) (y : ProbedPath W np × ℝ) :
    Matrix (Fin np) (Fin np) ℂ :=
  complexSourceK b E W j τ m y.1 -
    ((2 * etaZ b E : ℝ) * Complex.I * phase y.2) •
      ((probeFrame b E W j τ m y.1)ᴴ *
        (1 - phase y.2 • closingN (scatteringMatrix b E W j y.1.1)
          (farEmbed (omittedProj b E h W (closeLen s W) y.1.1))
          (farEmbed (closingPairing b E h W (closeLen s W) y.1.1)))⁻¹ *
        farEmbed (closingPairing b E h W (closeLen s W) y.1.1) *
        scatteringMatrix b E W j y.1.1 * probeFrame b E W j τ m y.1)

/-!
## Coordinates, coefficients and births
-/

/-- Coordinates of the complex closed process: Gram entries `(σ, k, l)` and `𝒦` entries. -/
abbrev CIdx (K np : ℕ) := (Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np)) ⊕ (Fin np × Fin np)

/-- The value of a coordinate. -/
def cEntry {K np : ℕ} (c : CIdx K np) (G : GramState (SrcCol K (Fin np)))
    (Kc : Matrix (Fin np) (Fin np) ℂ) : ℂ :=
  match c with
  | Sum.inl e => gramEntry e G
  | Sum.inr ij => Kc ij.1 ij.2

/-- Drift coefficients: the Gram drift for Gram entries, `0` for `𝒦`. -/
def cDrift (b E : ℝ) {K np : ℕ} (c : CIdx K np) (G : GramState (SrcCol K (Fin np))) : ℂ :=
  match c with
  | Sum.inl e => gramDriftEntry (transportD0 b E) (srcSignature K (Fin np)) e G
  | Sum.inr _ => 0

/-- The `𝒦`–Gram bracket `d𝒦_ij dG_(σ,k,l)` of `IsComplexSourceExtension.crossM` (`σ = 0`) and
`crossB` (`σ = 1`). -/
def kGramCov (b E : ℝ) {K np : ℕ} (ij : Fin np × Fin np)
    (e : Fin 2 × SrcCol K (Fin np) × SrcCol K (Fin np)) (G : GramState (SrcCol K (Fin np))) : ℂ :=
  if e.1 = 0 then
    -(Complex.I * ((etaZ b E * transportD0 b E : ℝ) : ℂ)) * G.2 (Sum.inr ij.1) e.2.2 *
      gramC0 G.1 G.2 (srcSignature K (Fin np)) e.2.1 (Sum.inr ij.2)
  else
    -(Complex.I * ((etaZ b E * transportD0 b E : ℝ) : ℂ)) * G.2 (Sum.inr ij.1) e.2.2 *
      (gramC1 G.1 G.2 (srcSignature K (Fin np)))ᴴ e.2.1 (Sum.inr ij.2)

/-- Bilinear bracket coefficients `dX_c dX_c'`: the Gram covariance for Gram pairs,
`d𝒦 d𝒦 = 0` (`holomorphic`), and `kGramCov` for mixed pairs. -/
def cCov (b E : ℝ) {K np : ℕ} (c c' : CIdx K np) (G : GramState (SrcCol K (Fin np))) : ℂ :=
  match c, c' with
  | Sum.inl e, Sum.inl e' => gramCovEntry (transportD0 b E) (srcSignature K (Fin np)) e e' G
  | Sum.inr _, Sum.inr _ => 0
  | Sum.inr ij, Sum.inl e => kGramCov b E ij e G
  | Sum.inl e, Sum.inr ij => kGramCov b E ij e G

/-- The conjugate bracket `d𝒦_ij d\bar𝒦_kl = 2η²D₀ B_ik (C₀)_lj` (`antiholomorphic`). -/
def kConjCov (b E : ℝ) {K np : ℕ} (ij kl : Fin np × Fin np)
    (G : GramState (SrcCol K (Fin np))) : ℂ :=
  ((2 * etaZ b E ^ 2 * transportD0 b E : ℝ) : ℂ) * G.2 (Sum.inr ij.1) (Sum.inr kl.1) *
    gramC0 G.1 G.2 (srcSignature K (Fin np)) (Sum.inr kl.2) (Sum.inr ij.2)

/-- A tag is born at step `j → j + 1` (`⌊Wτ_i⌋ = j`). -/
def IsBirthStep {np : ℕ} (τ : Fin np → ℝ) (W j : ℕ) : Prop := ∃ i, ⌊(W : ℝ) * τ i⌋₊ = j

instance {np : ℕ} (τ : Fin np → ℝ) (W j : ℕ) : Decidable (IsBirthStep τ W j) := by
  unfold IsBirthStep; infer_instance

/-- The Gram birth jump at step `j` (squared norm `d_* m_i`, near, zero overlaps). -/
def b3BirthAt (b : ℝ) {K np : ℕ} (τ m : Fin np → ℝ) (W j : ℕ) : GramState (SrcCol K (Fin np)) :=
  ∑ i, if ⌊(W : ℝ) * τ i⌋₊ = j then
    (((dStar b * m i : ℝ) : ℂ) • Matrix.single (Sum.inr i) (Sum.inr i) 1,
      ((dStar b * m i : ℝ) : ℂ) • Matrix.single (Sum.inr i) (Sum.inr i) 1) else 0

/-- The `𝒦` birth jump at step `j` (diagonal `a m_i`, zero cross entries). -/
def b3KBirthAt (E : ℝ) {np : ℕ} (τ m : Fin np → ℝ) (W j : ℕ) : Matrix (Fin np) (Fin np) ℂ :=
  ∑ i, if ⌊(W : ℝ) * τ i⌋₊ = j then (matchedA E * (m i : ℂ)) • Matrix.single i i 1 else 0

/-- The births of steps `n_s ≤ l < j` (Gram). -/
def b3JumpAt (b s : ℝ) {K np : ℕ} (τ m : Fin np → ℝ) (W j : ℕ) : GramState (SrcCol K (Fin np)) :=
  ∑ l ∈ Finset.Ico (closeLen s W) j, b3BirthAt b τ m W l

/-- The births of steps `n_s ≤ l < j` (`𝒦`). -/
def b3KJumpAt (E s : ℝ) {np : ℕ} (τ m : Fin np → ℝ) (W j : ℕ) : Matrix (Fin np) (Fin np) ℂ :=
  ∑ l ∈ Finset.Ico (closeLen s W) j, b3KBirthAt E τ m W l

/-!
## The finite-`W` estimates behind `ComplexCapCondLimit`
-/

/-- The closed law: path, probes and one phase. -/
abbrev closedLaw (b : ℝ) (W np : ℕ) : Measure (ProbedPath W np × ℝ) :=
  (probedPathLaw W np b).prod phaseLaw

/-- The closed filtration at length `j`: the path up to `j`, the probe Gaussians and the phase. -/
abbrev b3Sigma (W j np : ℕ) : MeasurableSpace (ProbedPath W np × ℝ) :=
  MeasurableSpace.comap (fun y : ProbedPath W np × ℝ => (pastCoords W j y.1.1, y.1.2, y.2))
    inferInstance

/-- Alive at `j`: on the physical cap event and `Re Tr M_i < R` for `n_s ≤ i ≤ j`. -/
def b3Alive (b E s h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (R : ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) :
    Set (ProbedPath W np × ℝ) :=
  {y | y.1.1 ∈ physCapEventC b E s h K W ∧ ∀ i, closeLen s W ≤ i → i ≤ j →
    ((b3ClosedGramAt b E s h τ m W i Vs y).1.trace).re < R}

/-- The coordinate `c` of the closed process at length `j`. -/
def b3X (b E s h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (c : CIdx K np)
    (y : ProbedPath W np × ℝ) : ℂ :=
  cEntry c (b3ClosedGramAt b E s h τ m W j Vs y) (b3ClosedKAt b E s h τ m W j y)

/-- The increment of coordinate `c` at step `j → j + 1`. -/
def b3dX (b E s h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (c : CIdx K np)
    (y : ProbedPath W np × ℝ) : ℂ :=
  b3X b E s h τ m W (j + 1) Vs c y - b3X b E s h τ m W j Vs c y

/-- **The summed errors** at width `W`: over the steps `n_s ≤ j < ⌊WT⌋`, on
the alive set, the conditional drift error and the conditional bilinear-bracket error of the
coordinates `c, c'` at steps without a birth, and the birth error at birth steps. -/
def b3SummedErr (b E s T h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (R : ℝ) (W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (c c' : CIdx K np) : ℝ≥0∞ :=
  let μ := closedLaw b W np
  let A : ℕ → Set (ProbedPath W np × ℝ) := fun j => b3Alive b E s h τ m R W j Vs
  let dX : ℕ → CIdx K np → ProbedPath W np × ℝ → ℂ := fun j => b3dX b E s h τ m W j Vs
  let G : ℕ → ProbedPath W np × ℝ → GramState (SrcCol K (Fin np)) :=
    fun j => b3ClosedGramAt b E s h τ m W j Vs
  let steps := Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊
  (∑ j ∈ steps.filter (fun j => ¬ IsBirthStep τ W j), ∫⁻ y, ‖(A j).indicator (fun y =>
      μ[(A j).indicator (dX j c) | b3Sigma W j np] y - (W : ℂ)⁻¹ * cDrift b E c (G j y)) y‖ₑ
    ∂μ) +
  (∑ j ∈ steps.filter (fun j => ¬ IsBirthStep τ W j), ∫⁻ y, ‖(A j).indicator (fun y =>
      μ[(A j).indicator (fun y => dX j c y * dX j c' y) | b3Sigma W j np] y -
        (W : ℂ)⁻¹ * cCov b E c c' (G j y)) y‖ₑ ∂μ) +
  (∑ j ∈ steps.filter (fun j => IsBirthStep τ W j), ∫⁻ y, ‖(A j).indicator (fun y =>
      dX j c y - cEntry c (b3BirthAt b τ m W j) (b3KBirthAt E τ m W j)) y‖ₑ ∂μ)

/-- **The summed conjugate-bracket error** of two `𝒦` entries (`antiholomorphic`) at width `W`. -/
def b3ConjErr (b E s T h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (R : ℝ) (W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (ij kl : Fin np × Fin np) :
    ℝ≥0∞ :=
  let μ := closedLaw b W np
  let A : ℕ → Set (ProbedPath W np × ℝ) := fun j => b3Alive b E s h τ m R W j Vs
  let dX : ℕ → CIdx K np → ProbedPath W np × ℝ → ℂ := fun j => b3dX b E s h τ m W j Vs
  ∑ j ∈ (Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊).filter (fun j => ¬ IsBirthStep τ W j),
    ∫⁻ y, ‖(A j).indicator (fun y =>
      μ[(A j).indicator (fun y => dX j (Sum.inr ij) y * conj (dX j (Sum.inr kl) y)) |
          b3Sigma W j np] y -
        (W : ℂ)⁻¹ * kConjCov b E ij kl (b3ClosedGramAt b E s h τ m W j Vs y)) y‖ₑ ∂μ

/-- The parameter domain of the finite-`W` estimates: `ComplexSourceLawDomain`, a source-free start `s`, a
cutoff `0 < h < 1`, a cap `K`, and an eventually admissible time-`s` frame `V_s`
(`IsTimeSFrame`). -/
def FrameDomain (b E : ℝ) {np : ℕ} (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) : Prop :=
  ComplexSourceLawDomain b E τ m T ∧ 0 < s ∧ (∀ j, s < τ j) ∧ 0 < h ∧ h < 1 ∧
    ∀ᶠ W in atTop, IsTimeSFrame b E s h K W (Vs W)

/-- **`ComplexClosedSummed`** (complex copy of `ClosedSummed`, with the `𝒦` multiplier and the
deterministic tag births): for every admissible time-`s` frame and trace level `R`, the summed
errors of all coordinate pairs tend to `0`. -/
def ComplexClosedSummed : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ,
    (∀ c c' : CIdx K np, Tendsto (fun W => b3SummedErr b E s T h τ m R W (Vs W) c c') atTop
      (𝓝 0)) ∧
    ∀ ij kl : Fin np × Fin np, Tendsto (fun W => b3ConjErr b E s T h τ m R W (Vs W) ij kl) atTop
      (𝓝 0)

/-- **`ComplexClosedTight`** (complex copy of `ClosedTight`): on the cap event, every coordinate
of the closed process at `⌊Wt₁⌋` is tight, and its continuous part (births removed) has a
vanishing modulus on `[t₁, T]`, for `s < t₁ < T`. -/
def ComplexClosedTight : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ (c : CIdx K np) (t₁ : ℝ), s < t₁ → t₁ < T →
      (∀ θ : ℝ, 0 < θ → ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W →
        closedLaw b W np {y | y.1.1 ∈ physCapEventC b E s h K W ∧
          C < ‖b3X b E s h τ m W ⌊(W : ℝ) * t₁⌋₊ (Vs W) c y‖} ≤ ENNReal.ofReal θ) ∧
      (∀ η θ : ℝ, 0 < η → 0 < θ → ∃ δ : ℝ, 0 < δ ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
        closedLaw b W np {y | y.1.1 ∈ physCapEventC b E s h K W ∧
          ∃ t ∈ Set.Icc t₁ T, ∃ t' ∈ Set.Icc t₁ T, |t - t'| ≤ δ ∧ η <
            ‖b3X b E s h τ m W ⌊(W : ℝ) * t⌋₊ (Vs W) c y -
              cEntry c (b3JumpAt b s τ m W ⌊(W : ℝ) * t⌋₊) (b3KJumpAt E s τ m W ⌊(W : ℝ) * t⌋₊) -
              (b3X b E s h τ m W ⌊(W : ℝ) * t'⌋₊ (Vs W) c y -
                cEntry c (b3JumpAt b s τ m W ⌊(W : ℝ) * t'⌋₊)
                  (b3KJumpAt E s τ m W ⌊(W : ℝ) * t'⌋₊))‖} ≤ ENNReal.ofReal θ)

/-- **`ComplexKStoppedMoment`: the stop for `𝒦`** (the centred increment has `L^p` size
`C_p Tr M_pr/√W`; Minkowski and Burkholder give all fixed `𝒦` moments). `𝒦` is not bounded by
the Gram trace, so the trace stop alone does not bound it; this estimate gives uniform fourth
moments of the closed `𝒦` one step past every alive length, which is what uniform integrability
of the `𝒦` brackets needs in the limit passage. -/
def ComplexKStoppedMoment : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ C : ℝ, ∀ᶠ W in atTop,
      ∀ j, closeLen s W ≤ j → j < ⌊(W : ℝ) * T⌋₊ → ∀ ij : Fin np × Fin np,
        ∫⁻ y, (b3Alive b E s h τ m R W j (Vs W)).indicator
          (fun y => ‖b3ClosedKAt b E s h τ m W (j + 1) y ij.1 ij.2‖ₑ ^ 4) y
            ∂closedLaw b W np ≤ ENNReal.ofReal C

/-- **`ComplexClosedCurrent`** (`V𝖣V* = ⊕(P'_i − P_i)` on the cap): on the cap event, the closed
current coordinate `J_pr` of `closedSourceData` agrees in probability with `(M𝖣M)_pr` of the
closed Gram process at the final length. -/
def ComplexClosedCurrent : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ θ : ℝ, 0 < θ → ∀ᶠ W in atTop,
      closedLaw b W np {y | y.1.1 ∈ physCapEventC b E s h K W ∧ ∃ i k : Fin np,
        θ < ‖(closedSourceData b E s T h τ m W (phase y.2) y.1 3 -
          probeBlock ((b3ClosedGramAt b E s h τ m W ⌊(W : ℝ) * T⌋₊ (Vs W) y).1 *
            srcSignature K (Fin np) *
              (b3ClosedGramAt b E s h τ m W ⌊(W : ℝ) * T⌋₊ (Vs W) y).1)) i k‖}
        ≤ ENNReal.ofReal θ

/-- **The limit passage**: `TransmissionLawContract`, a measurable time-`s` frame and the
finite-`W` estimates `ComplexClosedSummed`, `ComplexClosedTight`, `ComplexKStoppedMoment`,
`ComplexClosedCurrent` give `ComplexCapCondLimit` (Prokhorov on the cap event, a continuous
version, tested stopped identities passing to the limit, the entrance at non-atom `h`).
-/
def TargetCapCond : Prop :=
  TransmissionLawContract → ExistsTimeSFrame → ComplexClosedSummed → ComplexClosedTight →
    ComplexKStoppedMoment → ComplexClosedCurrent → ComplexCapCondLimit

end BlockBand.SourceProcess.PhysApprox.B3
