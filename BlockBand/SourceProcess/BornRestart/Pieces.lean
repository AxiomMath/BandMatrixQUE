module

public import BlockBand.SourceProcess.BornRestart.Bounds
public import BlockBand.SourceProcess.Stochastic.Semimartingale.HittingTime

/-!
# The trace stop of a born path is a stopping time of a right-continuous filtration

The trace stop `σ_K = inf {u : K ≤ Re Tr M_u}` of a path with jumps is a hitting time of a
closed set by a càdlàg path. It is split along the inter-birth pieces: piece `f₀ : Option F`
starts at `s = 0` (`none`) or `s = max (b f) 0` (`some f`); on `[s, b_g - 1/(m+1)]` for every
later birth `g` the jump part is the constant `J(s)`, so the piece hit is the `rawHit` of the
continuous process `(Re Tr (Y - J + J(s)), u - s, (b_g - u - 1/(m+1))_g)` in a closed set.
`pieceStop` is the infimum over pieces and `m`. Its strict sublevel sets are countable unions,
so it is a stopping time by right-continuity (`isStoppingTime_pieceStop`). On every path with
continuous `Y - J`, `pieceStop = gramTraceStop Y K` (`pieceStop_eq`), because the trace is
right-continuous, so the infimum is attained.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.BornRestart

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.SourceProcess.BornUnique
open BlockBand.SourceProcess.SourceProcessLaw
open scoped NNReal

variable {c F : Type} [Fintype c] [Fintype F] {Ω : Type*}

/-- Start of a piece. -/
def pieceStart (b : F → ℝ) : Option F → ℝ
  | none => 0
  | some f => max (b f) 0

/-- The continuous process whose hit of `pieceSet K` is the trace hit on piece `(f₀, m)`. -/
def pieceProc (j : F → GramState c) (Y : ℝ≥0 → Ω → GramState c) (b : Ω → F → ℝ)
    (f₀ : Option F) (m : ℕ) (u : ℝ≥0) (ω : Ω) : ℝ × ℝ × (F → ℝ) :=
  (((Y u ω - birthSum j (b ω) (u : ℝ) + birthSum j (b ω) (pieceStart (b ω) f₀)).1.trace).re,
    (u : ℝ) - pieceStart (b ω) f₀,
    fun g => if pieceStart (b ω) f₀ < b ω g then b ω g - u - 1 / ((m : ℝ) + 1) else 1)

/-- The closed target set. -/
def pieceSet (K : ℝ) : Set (ℝ × ℝ × (F → ℝ)) :=
  {z | K ≤ z.1} ∩ ({z | 0 ≤ z.2.1} ∩ ⋂ g, {z | 0 ≤ z.2.2 g})

omit [Fintype F] in
theorem mem_pieceSet {K : ℝ} {z : ℝ × ℝ × (F → ℝ)} :
    z ∈ pieceSet K ↔ K ≤ z.1 ∧ 0 ≤ z.2.1 ∧ ∀ g, 0 ≤ z.2.2 g := by
  simp [pieceSet]

/-- The trace stop built from pieces. -/
def pieceStop (j : F → GramState c) (Y : ℝ≥0 → Ω → GramState c) (b : Ω → F → ℝ) (K : ℝ)
    (ω : Ω) : WithTop ℝ≥0 :=
  ⨅ (f₀ : Option F) (m : ℕ), rawHit (pieceSet K) (pieceProc j Y b f₀ m) ω

omit [Fintype F] in
theorem isClosed_pieceSet (K : ℝ) : IsClosed (pieceSet (F := F) K) := by
  refine (isClosed_le continuous_const continuous_fst).inter
    ((isClosed_le continuous_const (continuous_fst.comp continuous_snd)).inter ?_)
  exact isClosed_iInter fun g =>
    isClosed_le continuous_const ((continuous_apply g).comp (continuous_snd.comp continuous_snd))

theorem measurable_birthSum₂ (j : F → GramState c) :
    Measurable fun p : (F → ℝ) × ℝ => birthSum j p.1 p.2 := by
  have : BorelSpace (GramState c) := gramState_borel
  have : SecondCountableTopology (GramState c) := gramState_secondCountable
  unfold birthSum
  refine Finset.measurable_sum _ fun f _ => ?_
  exact Measurable.ite (measurableSet_le ((measurable_pi_apply f).comp measurable_fst)
    measurable_snd) measurable_const measurable_const

omit [Fintype F] in
theorem measurable_pieceStart (f₀ : Option F) : Measurable fun x : F → ℝ => pieceStart x f₀ := by
  cases f₀ with
  | none => exact measurable_const
  | some f => exact (measurable_pi_apply f).max measurable_const

variable {m : MeasurableSpace Ω}

theorem measurable_pieceProc {m' : MeasurableSpace Ω} {j : F → GramState c}
    {Y : ℝ≥0 → Ω → GramState c} {b : Ω → F → ℝ} {u : ℝ≥0}
    (hY : StronglyMeasurable[m'] (Y u)) (hb : Measurable[m'] b) (f₀ : Option F) (k : ℕ) :
    Measurable[m'] (pieceProc j Y b f₀ k u) := by
  have : BorelSpace (GramState c) := gramState_borel
  have : SecondCountableTopology (GramState c) := gramState_secondCountable
  have : MeasurableAdd₂ (GramState c) := ContinuousAdd.measurableMul₂
  have : MeasurableSub₂ (GramState c) := ContinuousSub.measurableSub₂
  have hs : Measurable[m'] fun ω => pieceStart (b ω) f₀ := (measurable_pieceStart f₀).comp hb
  have h1 : Measurable[m'] fun ω => Y u ω - birthSum j (b ω) (u : ℝ) +
      birthSum j (b ω) (pieceStart (b ω) f₀) :=
    (hY.measurable.sub ((measurable_birthSum j _).comp hb)).add
      ((measurable_birthSum₂ j).comp (hb.prodMk hs))
  have hc : Continuous fun x : GramState c => (x.1.trace).re :=
    Complex.continuous_re.comp (continuous_fst.matrix_trace)
  refine (hc.measurable.comp h1).prodMk ((measurable_const.sub hs).prodMk
    (measurable_pi_iff.2 fun g => ?_))
  exact Measurable.ite (measurableSet_lt hs ((measurable_pi_apply g).comp hb))
    (((measurable_pi_apply g).comp hb).sub_const _ |>.sub_const _) measurable_const

/-- **The piece stop is a stopping time** of every right-continuous filtration to which `Y` is
adapted. -/
theorem isStoppingTime_pieceStop {𝓗 : Filtration ℝ≥0 m} [𝓗.IsRightContinuous]
    {j : F → GramState c} {Y : ℝ≥0 → Ω → GramState c} {b : Ω → F → ℝ}
    (hY : ∀ u, StronglyMeasurable[𝓗 u] (Y u)) (hb : Measurable[𝓗 0] b) (K : ℝ) :
    IsStoppingTime 𝓗 (pieceStop j Y b K) := by
  refine isStoppingTime_of_measurableSet_lt_of_isRightContinuous fun t => ?_
  have e : {ω | pieceStop j Y b K ω < t} =
      ⋃ (f₀ : Option F) (k : ℕ), {ω | rawHit (pieceSet K) (pieceProc j Y b f₀ k) ω < t} := by
    ext ω
    simp only [pieceStop, mem_ofPred_eq, mem_iUnion, iInf_lt_iff]
  rw [e]
  refine MeasurableSet.iUnion fun f₀ => MeasurableSet.iUnion fun k => ?_
  exact (isStoppingTime_rawHit (𝓖 := 𝓗) fun u =>
    measurable_pieceProc (hY u) (hb.mono (𝓗.mono zero_le) le_rfl) f₀ k).measurableSet_lt t

end BlockBand.SourceProcess.BornRestart
