module

public import BlockBand.SourceProcess.Stochastic.FiniteSource
public import BlockBand.SourceProcess.Stochastic.Semimartingale.MP.TimeChange

/-!
# Trace stops of a path glued at a deterministic time

Pathwise part of `GramHorizonExtension`.

`pStop p K` is the trace stop `σ_K` of one path (`gramTraceStop G K ω = pStop (G · ω) K` by
`rfl`). `glue r g y` follows `g` on `[0, r]` and `y(· - r)` after `r`.
* `stopTime_eq_of_char`: `m = σ ∧ t` as soon as `m ≤ t`, no hit before `m`, and `m = t` or a hit
  at `m` (no continuity needed).
* `stopTime_char`: for a continuous path, `σ ∧ t` has these properties (the infimum of the closed
  hit set is attained).
* For a continuous glued path with `y 0 = g r`: before `r` its stop is that of `g`
  (`stopTime_glue_of_le`); after `r`, if `g` hits on `[0, r]` then `σ ∧ t = σ ∧ r`
  (`stopTime_glue_hit`), and otherwise `σ ∧ t = r + σ^y ∧ (t - r)` (`stopTime_glue_noHit`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.HorizonExt

open Set BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal

variable {c : Type} [Fintype c]

/-- The trace stop of one path. -/
def pStop (p : ℝ≥0 → Matrix c c ℂ × Matrix c c ℂ) (K : ℝ) : WithTop ℝ≥0 :=
  ⨅ (t : ℝ≥0) (_ : K ≤ ((p t).1.trace).re), (t : WithTop ℝ≥0)

/-- The path glued at `r`. -/
def glue (r : ℝ≥0) (g y : ℝ≥0 → Matrix c c ℂ × Matrix c c ℂ) (t : ℝ≥0) :
    Matrix c c ℂ × Matrix c c ℂ :=
  if t ≤ r then g t else y (t - r)

variable {p g y : ℝ≥0 → Matrix c c ℂ × Matrix c c ℂ} {K : ℝ}

theorem pStop_le {v : ℝ≥0} (hv : K ≤ ((p v).1.trace).re) : pStop p K ≤ v := iInf₂_le v hv

theorem le_pStop {m : ℝ≥0} (h : ∀ v < m, ¬ K ≤ ((p v).1.trace).re) : (m : WithTop ℝ≥0) ≤ pStop p K :=
  le_iInf₂ fun v hv => WithTop.coe_le_coe.2 (not_lt.1 fun hlt => h v hlt hv)

/-- **Characterization of `σ ∧ t`.** -/
theorem stopTime_eq_of_char {t m : ℝ≥0} (hmt : m ≤ t) (h1 : ∀ v < m, ¬ K ≤ ((p v).1.trace).re)
    (h2 : m = t ∨ K ≤ ((p m).1.trace).re) : stopTime (pStop p K) t = m := by
  have hle := le_pStop h1
  have e : min (t : WithTop ℝ≥0) (pStop p K) = m := by
    refine le_antisymm ?_ (le_min (WithTop.coe_le_coe.2 hmt) hle)
    rcases h2 with h2 | h2
    · rw [h2]; exact min_le_left _ _
    · exact (min_le_right _ _).trans (pStop_le h2)
  show WithTop.untopD _ (min (t : WithTop ℝ≥0) (pStop p K)) = m
  rw [e, WithTop.untopD_coe]

theorem continuous_reTrace (hp : Continuous p) : Continuous fun v => ((p v).1.trace).re :=
  Complex.continuous_re.comp ((continuous_fst.comp hp).matrix_trace)

/-- At a finite stop of a continuous path the trace level is reached. -/
theorem hit_of_pStop_eq (hp : Continuous p) {s : ℝ≥0} (hs : pStop p K = s) :
    K ≤ ((p s).1.trace).re := by
  set S : Set ℝ≥0 := {v | K ≤ ((p v).1.trace).re}
  have hS : IsClosed S := isClosed_le continuous_const (continuous_reTrace hp)
  have hne : S.Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    have : pStop p K = ⊤ := by
      refine iInf₂_eq_top.2 fun v hv => ?_
      have : v ∈ S := hv
      rw [hne] at this
      exact this.elim
    rw [this] at hs
    exact WithTop.top_ne_coe hs
  have hmem := hS.csInf_mem hne (OrderBot.bddBelow S)
  have e : pStop p K = (sInf S : ℝ≥0) :=
    le_antisymm (pStop_le hmem) (le_iInf₂ fun v hv => WithTop.coe_le_coe.2
      (csInf_le (OrderBot.bddBelow S) hv))
  rw [hs, WithTop.coe_inj] at e
  rw [e]
  exact hmem

theorem not_hit_of_lt_stopTime {t v : ℝ≥0} (hv : v < stopTime (pStop p K) t) :
    ¬ K ≤ ((p v).1.trace).re := fun h =>
  absurd (WithTop.coe_le_coe.1 ((stopTime_le_self _ t).trans (pStop_le h))) (not_le.2 hv)

/-- **`σ ∧ t` of a continuous path.** -/
theorem stopTime_char (hp : Continuous p) (t : ℝ≥0) :
    stopTime (pStop p K) t = t ∨ K ≤ ((p (stopTime (pStop p K) t)).1.trace).re := by
  induction h : pStop p K with
  | top => exact Or.inl (stopTime_top t)
  | coe s =>
    rw [stopTime_coe]
    rcases le_total t s with hts | hst
    · exact Or.inl (min_eq_left hts)
    · rw [min_eq_right hst]
      exact Or.inr (hit_of_pStop_eq hp h)

theorem stopTime_min_of_le (σ : WithTop ℝ≥0) {r t : ℝ≥0} (ht : t ≤ r) :
    stopTime (min σ (r : WithTop ℝ≥0)) t = stopTime σ t := by
  have e : min (t : WithTop ℝ≥0) (min σ r) = min (t : WithTop ℝ≥0) σ := by
    rw [min_comm σ, ← min_assoc, min_eq_left (WithTop.coe_le_coe.2 ht)]
  simp only [stopTime, e]

omit [Fintype c] in
theorem glue_of_le {r t : ℝ≥0} (ht : t ≤ r) : glue r g y t = g t := by
  simp only [glue, ht, ↓reduceIte]

omit [Fintype c] in
theorem glue_of_lt {r t : ℝ≥0} (ht : r < t) : glue r g y t = y (t - r) := by
  simp only [glue, not_le.2 ht, ↓reduceIte]

omit [Fintype c] in
theorem glue_add {r u : ℝ≥0} (hy : y 0 = g r) : glue r g y (r + u) = y u := by
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ u) with h | h
  · rw [← h, add_zero, glue_of_le le_rfl, hy]
  · rw [glue_of_lt (lt_add_of_pos_right r h), add_tsub_cancel_left]

omit [Fintype c] in
theorem continuous_glue {r : ℝ≥0} (hg : Continuous g) (hy : Continuous y) (h0 : y 0 = g r) :
    Continuous (glue r g y) :=
  Continuous.if_le hg (hy.comp (continuous_id.sub continuous_const)) continuous_id
    continuous_const fun t ht => by rw [ht, tsub_self, h0]

/-- Before `r` the glued path stops like `g`. -/
theorem stopTime_glue_of_le {r t : ℝ≥0} (hh : Continuous (glue r g y)) (ht : t ≤ r) :
    stopTime (pStop (glue r g y) K) t = stopTime (min (pStop g K) (r : WithTop ℝ≥0)) t := by
  rw [stopTime_min_of_le _ ht]
  have hm := stopTime_le (pStop (glue r g y) K) t
  have hmr := hm.trans ht
  refine (stopTime_eq_of_char hm (fun v hv => ?_) ?_).symm
  · have h := not_hit_of_lt_stopTime hv
    rwa [glue_of_le (hv.le.trans hmr)] at h
  · rcases stopTime_char hh (K := K) t with h | h
    · exact Or.inl h
    · rw [glue_of_le hmr] at h
      exact Or.inr h

/-- After `r`, if `g` hits on `[0, r]`, the stopped glued path is constant after `r`: `σ ∧ t = σ ∧ r`. -/
theorem stopTime_glue_hit {r t s : ℝ≥0} (hrt : r ≤ t) (hs : s ≤ r)
    (hK : K ≤ ((g s).1.trace).re) :
    stopTime (pStop (glue r g y) K) t = stopTime (pStop (glue r g y) K) r := by
  have hle : pStop (glue r g y) K ≤ r :=
    (pStop_le (v := s) (by rwa [glue_of_le hs])).trans (WithTop.coe_le_coe.2 hs)
  simp only [stopTime, min_eq_right (hle.trans (WithTop.coe_le_coe.2 hrt)), min_eq_right hle]

/-- Without a hit on `[0, r]`, `g` has `σ ≥ r`. -/
theorem le_pStop_of_noHit {r : ℝ≥0} (hno : ∀ s ≤ r, ¬ K ≤ ((g s).1.trace).re) :
    stopTime (min (pStop g K) (r : WithTop ℝ≥0)) r = r := by
  have h : (r : WithTop ℝ≥0) ≤ pStop g K := le_iInf₂ fun v hv =>
    WithTop.coe_le_coe.2 (not_lt.1 fun hlt => hno v hlt.le hv)
  show WithTop.untopD _ (min (r : WithTop ℝ≥0) (min (pStop g K) r)) = r
  rw [min_eq_right h, min_self, WithTop.untopD_coe]

/-- After `r`, without a hit on `[0, r]`: `σ ∧ t = r + σ^y ∧ (t - r)`. -/
theorem stopTime_glue_noHit {r t : ℝ≥0} (hy : Continuous y) (h0 : y 0 = g r) (hrt : r ≤ t)
    (hno : ∀ s ≤ r, ¬ K ≤ ((g s).1.trace).re) :
    stopTime (pStop (glue r g y) K) t = r + stopTime (pStop y K) (t - r) := by
  set m' := stopTime (pStop y K) (t - r)
  have hm' : m' ≤ t - r := stopTime_le _ _
  refine stopTime_eq_of_char ((add_le_add_right hm' r).trans (add_tsub_cancel_of_le hrt).le)
    (fun v hv => ?_) ?_
  · rcases le_or_gt v r with hvr | hvr
    · rw [glue_of_le hvr]; exact hno v hvr
    · rw [glue_of_lt hvr]
      exact not_hit_of_lt_stopTime ((tsub_lt_iff_left hvr.le).2 hv)
  · rcases stopTime_char hy (K := K) (t - r) with h | h
    · left
      have h' : m' = t - r := h
      rw [h', add_tsub_cancel_of_le hrt]
    · right
      rw [glue_add h0]
      exact h

end BlockBand.SourceProcess.HorizonExt
