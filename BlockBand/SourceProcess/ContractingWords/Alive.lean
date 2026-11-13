module

public import BlockBand.SourceProcess.FullSourceStops.CurrentStep

/-!
# The survival events `{j < σ_K}` are past events and decrease

The survival events `A_j = {j < σ_K}` of the trace stop decrease in `j`, and `A_j` is measurable
with respect to the past at length `j`.

* `alive_succ_subset`: `A_{j+1} ⊆ A_j`.
* `alive_eq`: `A_j = {∀ i ≤ j, ¬(εW ≤ i ∧ K < L_i)}`, `L_i = traceLoad` (the first hitting time
  in `ℕ∞` is attained).
* `measurableSet_alive`: `A_j ∈ growthSigma W j`. Every load `L_i`, `i ≤ j`, is a function of the
  past at length `j`: it depends on `ω` only through `pathAt W i ω`, which the zero extension
  `extPast` of the past coordinates preserves; and `Tr|J| = Re Tr cfc(|·|)(J)` is measurable
  (`J = 𝕊ᴴP𝕊 - P` is Hermitian for every `𝕊`; `measurable_cfc_abs`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.FullSource
open BlockBand.SourceProcess.FullSourceStops BlockBand.Transmission.Bridge

variable {W : ℕ}

theorem alive_succ_subset (b E : ℝ) {nT nI : ℕ} (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ)
    (K ε : ℝ) (j : ℕ) : alive b E k q K ε W (j + 1) ⊆ alive b E k q K ε W j := fun ω hω => by
  have h : ((j : ℕ) : ℕ∞) < ((j + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.lt_succ_self j
  exact lt_trans h hω

theorem alive_eq (b E : ℝ) {nT nI : ℕ} (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (K ε : ℝ)
    (j : ℕ) : alive b E k q K ε W j =
      ⋂ i ∈ Finset.range (j + 1), {ω | ¬(ε * W ≤ i ∧ K < traceLoad b E k q W i ω)} := by
  ext ω
  simp only [alive, traceStop, Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_range]
  constructor
  · intro h i hi hP
    have := lt_of_lt_of_le h (iInf₂_le i hP)
    exact absurd (by exact_mod_cast this : j < i) (by omega)
  · intro h
    have hle : ((j + 1 : ℕ) : ℕ∞) ≤ ⨅ (i : ℕ) (_ : ε * W ≤ i ∧ K < traceLoad b E k q W i ω),
        (i : ℕ∞) := by
      refine le_iInf₂ fun i hP => ?_
      have : j + 1 ≤ i := by
        by_contra hc; exact h i (by omega) hP
      exact_mod_cast this
    exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self j) hle

theorem pathAt_extPast_le {i j : ℕ} (h : i ≤ j) (ω : GrowthPath W) :
    pathAt W i (extPast W j (pastCoords W j ω)) = pathAt W i ω := by
  rw [pathAt_eq_pathOfPast, Function.comp_apply, Function.comp_apply, pastCoords_restrict h,
    pastCoords_extPast, ← pastCoords_restrict h]

theorem traceLoad_congr (b E : ℝ) {nT nI : ℕ} (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (i : ℕ)
    {ω ω' : GrowthPath W} (h : pathAt W i ω = pathAt W i ω') :
    traceLoad b E k q W i ω = traceLoad b E k q W i ω' := by
  have hL : ∀ ℓ : TraceLetter nT nI, letterMatrix b E k q W i ω ℓ =
      letterMatrix b E k q W i ω' ℓ := by
    intro ℓ
    cases ℓ <;> simp only [letterMatrix, pathCurrent, scatteringMatrix, boundaryResolvent,
      fullInverse, fullPathMatrix, tagResponse, boundaryToInterior, intervalSource, h]
  have hJ : pathCurrent b E W i ω = pathCurrent b E W i ω' := hL .current
  simp only [traceLoad, sourceTrace, hL, hJ]

theorem pathCurrent_isHermitian (b E : ℝ) (i : ℕ) (ω : GrowthPath W) :
    (pathCurrent b E W i ω).IsHermitian :=
  current_isHermitian _ _ nearProjection_conjTranspose

theorem measurable_nuclearNorm_pathCurrent (b E : ℝ) (i : ℕ) :
    Measurable fun ω : GrowthPath W => nuclearNorm (pathCurrent b E W i ω) := by
  have e : (fun ω : GrowthPath W => nuclearNorm (pathCurrent b E W i ω)) =
      fun ω => (cfc (fun x : ℝ => |x|) (pathCurrent b E W i ω)).trace.re := by
    funext ω
    rw [cfc_abs_eq_absMat (pathCurrent_isHermitian b E i ω), trace_absMat]
  rw [e]
  exact measurable_trace_re (measurable_cfc_abs.comp (measurable_pathCurrent b E i))

theorem measurable_traceLoad (b E : ℝ) {nT nI : ℕ} (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ)
    (i : ℕ) : Measurable fun ω : GrowthPath W => traceLoad b E k q W i ω :=
  (Finset.measurable_sum _ fun a _ => measurable_sourceTrace b E k q i a).add
    (measurable_nuclearNorm_pathCurrent b E i)

/-- A load at length `i ≤ j` is `growthSigma W j`-measurable. -/
theorem measurable_traceLoad_past (b E : ℝ) {nT nI : ℕ} (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ)
    {i j : ℕ} (h : i ≤ j) :
    Measurable[growthSigma W j] fun ω : GrowthPath W => traceLoad b E k q W i ω := by
  have e : (fun ω : GrowthPath W => traceLoad b E k q W i ω) =
      (fun ω => traceLoad b E k q W i ω) ∘ extPast W j ∘ pastCoords W j := by
    funext ω
    exact (traceLoad_congr b E k q i (pathAt_extPast_le h ω)).symm
  rw [e]
  exact ((measurable_traceLoad b E k q i).comp (measurable_extPast j)).comp
    (comap_measurable (pastCoords W j))

/-- **The survival event is a past event**: `A_j ∈ growthSigma W j`. -/
theorem measurableSet_alive (b E : ℝ) {nT nI : ℕ} (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ)
    (K ε : ℝ) (j : ℕ) : MeasurableSet[growthSigma W j] (alive b E k q K ε W j) := by
  rw [alive_eq]
  refine Finset.measurableSet_biInter _ fun i hi => ?_
  have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  by_cases hε : ε * W ≤ i
  · have : {ω : GrowthPath W | ¬(ε * W ≤ i ∧ K < traceLoad b E k q W i ω)} =
        {ω | traceLoad b E k q W i ω ≤ K} := by
      ext ω; simp [hε]
    rw [this]
    exact measurableSet_le (measurable_traceLoad_past b E k q hij) measurable_const
  · have : {ω : GrowthPath W | ¬(ε * W ≤ i ∧ K < traceLoad b E k q W i ω)} = Set.univ := by
      ext ω; simp [hε]
    rw [this]; exact MeasurableSet.univ

end BlockBand.SourceProcess.ContractingWords
