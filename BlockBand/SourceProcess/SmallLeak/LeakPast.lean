module

public import BlockBand.SourceProcess.SmallLeak.LeakLayer
public import BlockBand.SourceProcess.SmallLeak.GrowthStep
public import BlockBand.SourceProcess.ContractingWords.PathStep

/-!
# The leakage as a function of the past; its one-step identity; the trace stop

* `srcPast j p`: `Q_j(q)` from the past (`intervalSource_extPast`);
* `ae_omittedLeak_succ`: a.s. `ℓ_{j+1} = Re Tr F(N*Q_jN + c_j D₊*D₊)` (`intervalSource_succ`);
* `traceStop K j = {Tr Q_i ≤ K, n_s ≤ i ≤ j}` and its past form.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SmallLeak

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.FullSourceStops
open BlockBand.SourceProcess.FullSource BlockBand.Transmission.PathScalar
open BlockBand.SourceProcess.ClosingLeak
open scoped Matrix ComplexOrder ENNReal

variable {W : ℕ}

/-- `Q_j(q)` read from the past at length `j`. -/
def srcPast (b E : ℝ) (q : ℝ → ℝ) (W j : ℕ) (p : PastSample W j) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  intervalSource b E W j q (extPast W j p)

theorem intervalSource_extPast (b E : ℝ) (q : ℝ → ℝ) (j : ℕ) (ω : GrowthPath W) :
    srcPast b E q W j (pastCoords W j ω) = intervalSource b E W j q ω := by
  simp only [srcPast, intervalSource, tagResponse_eq_factor, pastCoords_extPast]

theorem measurable_srcPast (b E : ℝ) (q : ℝ → ℝ) (j : ℕ) : Measurable (srcPast b E q W j) :=
  (measurable_intervalSource b E j q).comp (measurable_extPast _)

/-- `ℓ_j` read from the past. -/
def leakPast (b E h s : ℝ) (q : ℝ → ℝ) (W j : ℕ) (p : PastSample W j) : ℝ :=
  (farEmbed (omittedPast b E h s W j p) * srcPast b E q W j p).trace.re

theorem omittedLeak_eq_past {b E h s : ℝ} (q : ℝ → ℝ) {j : ℕ} (hj : ⌊(W : ℝ) * s⌋₊ ≤ j)
    (ω : GrowthPath W) :
    omittedLeak b E h s q W j ω = leakPast b E h s q W j (pastCoords W j ω) := by
  rw [leakPast, intervalSource_extPast, omittedProj_extPast hj]; rfl

theorem measurable_leakPast (b E h s : ℝ) (q : ℝ → ℝ) (j : ℕ) :
    Measurable (leakPast b E h s q W j) :=
  measurable_trace_re (measurable_matrix_mul' (ClosingAux.measurable_farEmbed
    (measurable_omittedPast b E h s j)) (measurable_srcPast b E q j))

/-- The birth weight `c_j = q((j+1)/W)/W²`. -/
def birthWeight (q : ℝ → ℝ) (W j : ℕ) : ℝ := q (((j + 1 : ℕ) : ℝ) / W) / (W : ℝ) ^ 2

/-- The fresh integrand `Re Tr F(N*QN + c D₊*D₊)` of the step. -/
def leakNext (b E h s : ℝ) (q : ℝ → ℝ) (W j : ℕ)
    (x : PastSample W j × LayerSample W .oneBlockOnePort) : ℝ :=
  (farEmbed (omittedPast b E h s W j x.1) * ((freshTransport b E (pastXX E W j x.1) x.2)ᴴ *
    srcPast b E q W j x.1 * freshTransport b E (pastXX E W j x.1) x.2 +
    ((birthWeight q W j : ℝ) : ℂ) • ((freshD b E (pastXX E W j x.1) x.2)ᴴ *
      freshD b E (pastXX E W j x.1) x.2))).trace.re

/-- **The one-step identity of the leakage**, almost surely. -/
theorem ae_omittedLeak_succ {b E h s : ℝ} (q : ℝ → ℝ) (hb0 : 0 < b) (hb : b < 1 / 2)
    (hE1 : -2 < E) (hE2 : E < 2) (hW : 1 ≤ W) {j : ℕ} (hj1 : 1 ≤ j)
    (hj : ⌊(W : ℝ) * s⌋₊ ≤ j) :
    ∀ᵐ ω ∂growthPathLaw W b, omittedLeak b E h s q W (j + 1) ω =
      leakNext b E h s q W j (pastCoords W j ω, freshSample W j ω) := by
  filter_upwards [ae_tagResponse_succ_full hb0 hb hE1 hE2 hW,
    ae_tagResponse_succ_new_full hb0 hb hE1 hE2 hW] with ω hold hnew
  have hQ := ContractingWords.intervalSource_succ b E j q ω _ _ (hold j hj1) (hnew j hj1)
  rw [omittedLeak, hQ, farOmitted, leakNext, intervalSource_extPast, omittedProj_extPast hj,
    ← pastXX_eq]
  rfl

/-- The trace stop `{Tr Q_i ≤ K for n_s ≤ i ≤ j}`. -/
def traceStopEv (b E s : ℝ) (q : ℝ → ℝ) (K : ℝ) (W j : ℕ) : Set (GrowthPath W) :=
  {ω | ∀ i, ⌊(W : ℝ) * s⌋₊ ≤ i → i ≤ j → (intervalSource b E W i q ω).trace.re ≤ K}

/-- The trace stop as a set of past coordinates. -/
def traceStopPast (b E s : ℝ) (q : ℝ → ℝ) (K : ℝ) (W j : ℕ) : Set (PastSample W j) :=
  {p | ∀ i (h : i ≤ j), ⌊(W : ℝ) * s⌋₊ ≤ i →
    (srcPast b E q W i (restrictPast h p)).trace.re ≤ K}

theorem traceStopEv_eq (b E s : ℝ) (q : ℝ → ℝ) (K : ℝ) (j : ℕ) :
    traceStopEv b E s q K W j = pastCoords W j ⁻¹' traceStopPast b E s q K W j := by
  ext ω
  simp only [traceStopEv, traceStopPast, Set.mem_ofPred_eq, Set.mem_preimage]
  constructor
  · intro h i hij hi
    rw [← pastCoords_restrict hij, intervalSource_extPast]; exact h i hi hij
  · intro h i hi hij
    have := h i hij hi
    rwa [← pastCoords_restrict hij, intervalSource_extPast] at this

theorem measurableSet_traceStopPast (b E s : ℝ) (q : ℝ → ℝ) (K : ℝ) (j : ℕ) :
    MeasurableSet (traceStopPast b E s q K W j) := by
  have : traceStopPast b E s q K W j = ⋂ i, ⋂ (h : i ≤ j), ⋂ (_ : ⌊(W : ℝ) * s⌋₊ ≤ i),
      {p | (srcPast b E q W i (restrictPast h p)).trace.re ≤ K} := by
    ext p; simp [traceStopPast]
  rw [this]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun h => MeasurableSet.iInter fun _ =>
    measurableSet_le (measurable_trace_re ((measurable_srcPast b E q i).comp
      (measurable_restrictPast h))) measurable_const

theorem measurableSet_traceStopEv (b E s : ℝ) (q : ℝ → ℝ) (K : ℝ) (j : ℕ) :
    MeasurableSet (traceStopEv b E s q K W j) := by
  rw [traceStopEv_eq]
  exact (measurableSet_traceStopPast b E s q K j).preimage (measurable_pastCoords W j)

theorem traceStopEv_succ_subset (b E s : ℝ) (q : ℝ → ℝ) (K : ℝ) (j : ℕ) :
    traceStopEv b E s q K W (j + 1) ⊆ traceStopEv b E s q K W j :=
  fun _ h i hi hij => h i hi (by omega)

end BlockBand.SourceProcess.SmallLeak
