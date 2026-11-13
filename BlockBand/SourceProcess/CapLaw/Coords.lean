module

public import BlockBand.SourceProcess.CapLaw.Cond
public import BlockBand.SourceProcess.CapCond.Main
public import BlockBand.SourceProcess.EigenSelConstruct.Main

/-!
# The coordinates of the conditioned closed process

Labels `Lab K p M`:
* `inl e`: the Gram entry `e` of the continuous part `G − J` (`closedGramAt − closedJump`) at the
  length `⌊W·min(t, T)⌋` (physical time `t ≥ s`, stopped at `T`);
* `inr (inl k)`: the clamped entrance eigenvalue `clamp01 t_k` (`= t_k` a.s.);
* `inr (inr (inl (r, k)))`: the truncated smoothed count `min (smCount r (μ_W(s))) (k+1)`
  (Borel version of `μ_W(s)`; `k < min C (k+1) ↔ k < C`, so `countExt` is unchanged);
* `inr (inr (inr (inl il)))`: the birth time `min((k_il+1)/W, T)` (`s` for a zero-mass test);
* `inr (inr (inr (inr il)))`: the indicator `1{n_s ≤ k_il < ⌊WT⌋}`.
`capProc` enumerates them by `Encodable` (the format of `WordLim`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CapLaw

open MeasureTheory ProbabilityTheory Filter Topology
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.SourceProcess.ClosedPath BlockBand.SourceProcess.ClosedIdent
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.ClosedSumProof
open BlockBand.Transmission.LawDuality

variable {W p K M : ℕ}

/-- Gram entry labels. -/
abbrev GIdx (K p M : ℕ) := Fin 2 × SrcCol K (Fin p × Fin M) × SrcCol K (Fin p × Fin M)

/-- Coordinate labels. -/
abbrev Lab (K p M : ℕ) :=
  GIdx K p M ⊕ ℕ ⊕ (CapCond.RatPair × ℕ) ⊕ (Fin p × Fin M) ⊕ (Fin p × Fin M)

/-- Clamp to `[0, 1]`. -/
def clamp01 (x : ℝ) : ℝ := max 0 (min 1 x)

/-- The length at physical time `t`, stopped at `T`. -/
def idx (T : ℝ) (W : ℕ) (t : ℝ) : ℕ := ⌊(W : ℝ) * min t T⌋₊

/-- The birth-time coordinate of a tag index (`s` for a zero-mass test). -/
def birthCoord (s T : ℝ) (q : ℝ → ℝ) (W k : ℕ) : ℝ :=
  if 0 < sourceMass s T q then min (((k + 1 : ℕ) : ℝ) / W) T else s

/-- The indicator that a tag is born in the closed window `[n_s, ⌊WT⌋)`. -/
def bornInd (s T : ℝ) (W k : ℕ) : ℝ :=
  if closeLen s W ≤ k ∧ k < ⌊(W : ℝ) * T⌋₊ then 1 else 0

/-- The Borel version of the entrance measure `μ_W(s)`. -/
def entMeas (b E s : ℝ) (W : ℕ) (ω : GrowthPath W) : FiniteMeasure unitInterval :=
  clampedTraceMeasure (pathTransmission b E (fun _ => 0) W ⌊(W : ℝ) * s⌋₊ ω)

/-- **The coordinates.** -/
def capCoord (b E s T h : ℝ) (q : Fin p → ℝ → ℝ) (W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) :
    Lab K p M → ℝ → SampledPath W p M × ℝ → ℂ
  | Sum.inl e => fun t y => gramEntry e (closedGramAt b E s T h q W (idx T W t) Vs y -
      closedJump b s T q W (idx T W t) y)
  | Sum.inr (Sum.inl k) => fun _ y => (clamp01 (physTseq b E s W y.1.1 k) : ℂ)
  | Sum.inr (Sum.inr (Sum.inl rk)) => fun _ y =>
      ((min (CapCond.smCount rk.1.1.1 rk.1.1.2 (entMeas b E s W y.1.1)) ((rk.2 : ℝ) + 1) : ℝ) : ℂ)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl il))) => fun _ y =>
      (birthCoord s T (q il.1) W (y.1.2.1 il) : ℂ)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr il))) => fun _ y => (bornInd s T W (y.1.2.1 il) : ℂ)

/-- The coordinates enumerated by `ℕ` (`0` for codes of no label). -/
def capProc (b E s T h : ℝ) (q : Fin p → ℝ → ℝ) (Wn : ℕ → ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (n a : ℕ) (t : ℝ)
    (y : SampledPath (Wn n) p M × ℝ) : ℂ :=
  match Encodable.decode (α := Lab K p M) a with
  | some l => capCoord b E s T h q (Wn n) (Vs (Wn n)) l t y
  | none => 0

theorem capProc_encode (b E s T h : ℝ) (q : Fin p → ℝ → ℝ) (Wn : ℕ → ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (n : ℕ)
    (l : Lab K p M) :
    capProc (M := M) b E s T h q Wn Vs n (Encodable.encode l) =
      capCoord b E s T h q (Wn n) (Vs (Wn n)) l := by
  funext t y; simp [capProc, Encodable.encodek]

theorem idx_ge {s T t : ℝ} (hsT : s < T) (ht : s ≤ t) : closeLen s W ≤ idx T W t :=
  Nat.floor_mono (mul_le_mul_of_nonneg_left (le_min ht hsT.le) (Nat.cast_nonneg _))

theorem idx_le {T t : ℝ} : idx T W t ≤ ⌊(W : ℝ) * T⌋₊ :=
  Nat.floor_mono (mul_le_mul_of_nonneg_left (min_le_right _ _) (Nat.cast_nonneg _))

theorem measurable_physTseq (b E s : ℝ) (W k : ℕ) :
    Measurable fun ω : GrowthPath W => physTseq b E s W ω k := by
  obtain ⟨V, hVm, hV⟩ := EigenSelConstruct.measurableEigenSelection_holds (Fin W)
  have e : (fun ω : GrowthPath W => physTseq b E s W ω k) =
      (fun S => selT V S k) ∘ scatteringMatrix b E W (closeLen s W) := by
    funext ω; simp only [Function.comp_apply, selT_phys hV]
  rw [e]
  exact (measurable_selT hVm k).comp (FullSourceStops.measurable_scatteringMatrix b E _)

theorem measurable_entMeas (b E s : ℝ) (W : ℕ) : Measurable (entMeas b E s W) :=
  measurable_clampedTraceMeasure.comp (measurable_pathTransmission b E _ _)

theorem measurable_tag (il : Fin p × Fin M) :
    Measurable fun y : SampledPath W p M × ℝ => y.1.2.1 il :=
  (measurable_pi_apply il).comp (measurable_fst.comp (measurable_snd.comp measurable_fst))

theorem measurable_gramEntry_closedJump (b s T : ℝ) (q : Fin p → ℝ → ℝ) (j : ℕ)
    (e : GIdx K p M) :
    Measurable fun y : SampledPath W p M × ℝ => gramEntry e (closedJump b s T q W j y) := by
  simp only [closedJump, gramEntry_sum]
  exact Finset.measurable_sum _ fun i _ => measurable_gramEntry_birthAt e b s T q i

/-- **Every coordinate is measurable** at times `t ≥ s`, for a `growthSigma`-measurable frame. -/
theorem measurable_capCoord {b E s T h : ℝ} (hsT : s < T) {q : Fin p → ℝ → ℝ}
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hVs : Measurable[growthSigma W (closeLen s W)] Vs) (l : Lab K p M) {t : ℝ} (ht : s ≤ t) :
    Measurable (capCoord b E s T h q W Vs l t) := by
  rcases l with e | k | r | il | il
  · simp only [capCoord, gramEntry_sub]
    exact ((measurable_gramEntry e).comp ((measurable_closedGramAt_past b E s T h q
      (idx_ge hsT ht) hVs).mono (closedSigma_le _) le_rfl)).sub
      (measurable_gramEntry_closedJump b s T q _ e)
  · exact Complex.measurable_ofReal.comp ((measurable_const.max (measurable_const.min
      (measurable_physTseq b E s W k))).comp (measurable_fst.comp measurable_fst))
  · exact Complex.measurable_ofReal.comp ((((CapCond.continuous_smCount
      (Rat.cast_pos.mpr r.1.2.1) _).measurable.comp (measurable_entMeas b E s W)).min
      measurable_const).comp (measurable_fst.comp measurable_fst))
  · exact Complex.measurable_ofReal.comp ((measurable_from_nat (f := fun k =>
      birthCoord s T (q il.1) W k)).comp (measurable_tag il))
  · exact Complex.measurable_ofReal.comp ((measurable_from_nat (f := fun k =>
      bornInd s T W k)).comp (measurable_tag il))

end BlockBand.SourceProcess.CapLaw
