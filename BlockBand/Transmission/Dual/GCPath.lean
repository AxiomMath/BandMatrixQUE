module

public import BlockBand.SourceProcess.Stochastic.SemimartingaleIto.Localize
public import BlockBand.SourceProcess.Stochastic.Semimartingale.HittingTime
public import BlockBand.SourceProcess.Stochastic.Semimartingale.MP.Exit
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop

/-!
# The space of continuous paths and the stopping functionals

* `pexit W w`, the exit time of `w` from an open `W`, is measurable (`measurable_pexit`: it equals
  the raw hitting time `rawHit Wᶜ` of the coordinate process, a stopping time for the constant
  filtration);
* `pstop W t₀ w = (w^{τ_W})^{t₀}` (`t ↦ w(t ∧ τ_W(w) ∧ t₀)`) is a measurable map
  `CPath d → CPath d` (`measurable_pstop`, via joint measurability of the evaluation);
* `pstop_congr`: `pstop W t₀ w` depends only on `w` on `[0, τ_W(w) ∧ t₀]`; hence
  `pstop_pstop`: `pstop W t₀ ∘ pstop W' t₀ = pstop W t₀` for open `W ⊆ W'`.
This replaces the killed path space of §6.3: the level-`p` law is carried by the sequence of
stopped paths `(pstop W_n t₀ Z)_n` (file `GDomSeq`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.SemimartingaleIto
open scoped NNReal ENNReal

variable {d : ℕ}

/-- Continuous paths in `ℝ^d`. -/
abbrev CPath (d : ℕ) : Type := {w : ℝ≥0 → Fin d → ℝ // Continuous w}

/-- The coordinate process of `CPath d`. -/
def cev (d : ℕ) (t : ℝ≥0) (w : CPath d) : Fin d → ℝ := w.1 t

theorem measurable_cev (t : ℝ≥0) : Measurable (cev d t) :=
  (measurable_pi_apply t).comp measurable_subtype_coe

/-- The exit time of a continuous path from `W`. -/
def pexit (W : Set (Fin d → ℝ)) (w : CPath d) : WithTop ℝ≥0 := exitTimeFrom W (cev d) w

/-- The filtration constantly equal to the ambient σ-algebra. -/
def topFiltration (α : Type*) [MeasurableSpace α] :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace α) :=
  ⟨fun _ => inferInstance, fun _ _ _ => le_rfl, fun _ => le_rfl⟩

theorem measurable_pexit {W : Set (Fin d → ℝ)} (hW : IsOpen W) : Measurable (pexit W) := by
  have hτ : IsStoppingTime (topFiltration (CPath d)) (rawHit Wᶜ (cev d)) :=
    isStoppingTime_rawHit (𝓖 := topFiltration (CPath d)) fun t => measurable_cev t
  have e : rawHit Wᶜ (cev d) = pexit W := funext fun w =>
    rawHit_compl_eq_exitTimeFrom hW (Y := cev d) w.2
  rw [← e]
  exact hτ.measurable'

/-- The stopped, truncated path `t ↦ w(t ∧ τ_W(w) ∧ t₀)`. -/
def pstopFun (W : Set (Fin d → ℝ)) (t₀ : ℝ≥0) (w : CPath d) : ℝ≥0 → Fin d → ℝ :=
  fun t => w.1 (stopTime (pexit W w) (min t t₀))

theorem continuous_pstopFun (W : Set (Fin d → ℝ)) (t₀ : ℝ≥0) (w : CPath d) :
    Continuous (pstopFun W t₀ w) :=
  w.2.comp ((continuous_stopTime _).comp (continuous_id.min continuous_const))

/-- The stopped, truncated path as a continuous path. -/
def pstop (W : Set (Fin d → ℝ)) (t₀ : ℝ≥0) (w : CPath d) : CPath d :=
  ⟨pstopFun W t₀ w, continuous_pstopFun W t₀ w⟩

/-- Evaluation `(s, w) ↦ w(s)` is jointly measurable. -/
theorem measurable_eval_cpath :
    Measurable fun p : ℝ≥0 × CPath d => p.2.1 p.1 :=
  measurable_uncurry_of_continuous_of_measurable (u := fun s (w : CPath d) => w.1 s)
    (fun w => w.2) fun s => measurable_cev s

theorem measurable_pstop {W : Set (Fin d → ℝ)} (hW : IsOpen W) (t₀ : ℝ≥0) :
    Measurable (pstop W t₀) := by
  refine Measurable.subtype_mk (measurable_pi_iff.2 fun t => ?_)
  have hs : Measurable fun w : CPath d => stopTime (pexit W w) (min t t₀) :=
    Measurable.untopA (measurable_const.min (measurable_pexit hW))
  exact measurable_eval_cpath.comp (hs.prodMk measurable_id)

theorem stopTime_of_le {τ : WithTop ℝ≥0} {t : ℝ≥0} (h : (t : WithTop ℝ≥0) ≤ τ) :
    stopTime τ t = t := by
  induction τ with
  | top => simp [stopTime_top]
  | coe s₀ => rw [stopTime_coe]; exact min_eq_left (WithTop.coe_le_coe.1 h)

theorem coe_stopTime_min (τ : WithTop ℝ≥0) (t t₀ : ℝ≥0) :
    ((stopTime τ (min t t₀) : ℝ≥0) : WithTop ℝ≥0) = min (t : WithTop ℝ≥0) (min τ t₀) := by
  induction τ with
  | top => rw [stopTime_top, WithTop.coe_min, min_top_left]
  | coe s₀ =>
    rw [stopTime_coe, WithTop.coe_min, WithTop.coe_min, min_assoc,
      min_comm (t₀ : WithTop ℝ≥0)]

/-- The truncated exit time is determined by the path up to itself. -/
theorem min_pexit_congr {W : Set (Fin d → ℝ)} (hW : IsOpen W) {w w' : CPath d} (t₀ : ℝ≥0)
    (h : ∀ u : ℝ≥0, (u : WithTop ℝ≥0) ≤ min (pexit W w) t₀ → w'.1 u = w.1 u) :
    min (pexit W w') t₀ = min (pexit W w) t₀ := by
  refine le_antisymm ?_ ?_
  · rcases le_total (pexit W w) (t₀ : WithTop ℝ≥0) with hle | hle
    · rcases exitTimeFrom_attained hW (Y := cev d) (ω := w) w.2 with h1 | ⟨s₀, h1, h2⟩
      · exact absurd hle (by rw [pexit, h1]; exact not_le.2 (WithTop.coe_lt_top t₀))
      · have hs : (s₀ : WithTop ℝ≥0) ≤ min (pexit W w) t₀ := by
          rw [min_eq_left hle, pexit, h1]
        have hw' : cev d s₀ w' ∉ W := by
          simp only [cev] at h2 ⊢; rw [h s₀ hs]; exact h2
        have he' : pexit W w' ≤ s₀ := iInf₂_le s₀ hw'
        rw [min_eq_left hle, show pexit W w = s₀ from h1]
        exact (min_le_left _ _).trans he'
    · rw [min_eq_right hle]; exact min_le_right _ _
  · refine le_min ?_ (min_le_right _ _)
    refine le_iInf₂ fun u hu => ?_
    by_contra hlt
    push Not at hlt
    have hmem : cev d u w ∈ W := mem_of_lt_exitTimeFrom (lt_of_lt_of_le hlt (min_le_left _ _))
    simp only [cev] at hu hmem
    rw [h u hlt.le] at hu
    exact hu hmem

/-- **`pstop W t₀ w` depends only on `w` on `[0, τ_W(w) ∧ t₀]`.** -/
theorem pstop_congr {W : Set (Fin d → ℝ)} (hW : IsOpen W) {w w' : CPath d} (t₀ : ℝ≥0)
    (h : ∀ u : ℝ≥0, (u : WithTop ℝ≥0) ≤ min (pexit W w) t₀ → w'.1 u = w.1 u) :
    pstop W t₀ w' = pstop W t₀ w := by
  have hm := min_pexit_congr hW t₀ h
  have ht : ∀ t, stopTime (pexit W w') (min t t₀) = stopTime (pexit W w) (min t t₀) := fun t => by
    rw [← WithTop.coe_inj, coe_stopTime_min, coe_stopTime_min, hm]
  refine Subtype.ext (funext fun t => ?_)
  show w'.1 (stopTime (pexit W w') (min t t₀)) = w.1 (stopTime (pexit W w) (min t t₀))
  rw [ht t]
  refine h _ ?_
  rw [coe_stopTime_min]; exact min_le_right _ _

/-- **Nested stopping**: for open `W ⊆ W'`, stopping at `W'` first changes nothing. -/
theorem pstop_pstop {W W' : Set (Fin d → ℝ)} (hW : IsOpen W) (hWW : W ⊆ W') (t₀ : ℝ≥0)
    (w : CPath d) : pstop W t₀ (pstop W' t₀ w) = pstop W t₀ w := by
  refine pstop_congr hW t₀ fun u hu => ?_
  have hut : u ≤ t₀ := WithTop.coe_le_coe.1 (hu.trans (min_le_right _ _))
  have hue : (u : WithTop ℝ≥0) ≤ pexit W' w :=
    (hu.trans (min_le_left _ _)).trans
      (le_iInf₂ fun t ht => iInf₂_le t fun h' => ht (hWW h'))
  show w.1 (stopTime (pexit W' w) (min u t₀)) = w.1 u
  rw [min_eq_left hut, stopTime_of_le hue]

end BlockBand.Transmission.Dual.G
