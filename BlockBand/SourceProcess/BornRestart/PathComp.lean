module

public import BlockBand.SourceProcess.BornRestart.Path
public import BlockBand.SourceProcess.Stochastic.Semimartingale.MP.TimeChange

/-!
# Compensated coordinates along born paths: restart identities and bounds

* `pComp_shift`, `pBr_shift`: restarting the path at `a` (`g' v = g (a + v)`, births `b - a`)
  gives the increments after `a`; `pBr` picks up the cross terms `C_e(a) C'_{e'}`.
* `pComp_stop_shift`, `pBr_stop_shift`: the same after stopping at `θ` (resp. `θ - a`).
* `exists_pComp_bound`, `exists_pBr_bound` (proved in the sibling module `Bounds` from these
  identities): if the continuous part stays in a ball before `θ`,
  the stopped processes are bounded by `C (1 + r)` and `C (1 + r)²`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.BornRestart

open MeasureTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.GramUniqueness
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.SourceProcess.BornUnique
open scoped NNReal

variable {c F : Type} [Fintype c] [DecidableEq c] [Fintype F] (D0 : ℝ) (D : Matrix c c ℂ)
  (j : F → GramState c)

/-- The compensated coordinate along a path (`bornCompensated` at one `ω`). -/
def pComp (g : ℝ≥0 → GramState c) (b : F → ℝ) (e : Fin 2 × c × c) (t : ℝ≥0) : ℂ :=
  gramEntry e (g t - birthSum j b (t : ℝ)) - gramEntry e (g 0 - birthSum j b ((0 : ℝ≥0) : ℝ)) -
    ∫ s in Ioc (0 : ℝ) t, gramDriftEntry D0 D e (g s.toNNReal)

/-- The compensated product along a path. -/
def pBr (g : ℝ≥0 → GramState c) (b : F → ℝ) (e e' : Fin 2 × c × c) (t : ℝ≥0) : ℂ :=
  pComp D0 D j g b e t * pComp D0 D j g b e' t -
    ∫ s in Ioc (0 : ℝ) t, gramCovEntry D0 D e e' (g s.toNNReal)

theorem bornCompensated_eq {Ω : Type*} (G : ℝ≥0 → Ω → GramState c) (β : Ω → F → ℝ)
    (e : Fin 2 × c × c) (t : ℝ≥0) (ω : Ω) :
    bornCompensated D0 D G (fun t ω => birthSum j (β ω) (t : ℝ)) e t ω =
      pComp D0 D j (fun t => G t ω) (β ω) e t := rfl

variable {D0 D j}

omit [DecidableEq c] in
@[simp] theorem pComp_zero (g : ℝ≥0 → GramState c) (b : F → ℝ) (e : Fin 2 × c × c) :
    pComp D0 D j g b e 0 = 0 := by
  simp [pComp]

omit [DecidableEq c] in
@[simp] theorem pBr_zero (g : ℝ≥0 → GramState c) (b : F → ℝ) (e e' : Fin 2 × c × c) :
    pBr D0 D j g b e e' 0 = 0 := by
  simp [pBr]

variable {g : ℝ≥0 → GramState c} {b : F → ℝ}

theorem continuous_pComp (hc : Continuous fun t => g t - birthSum j b (t : ℝ))
    (e : Fin 2 × c × c) : Continuous (pComp D0 D j g b e) :=
  (((continuous_gramEntry e).comp hc).sub continuous_const).sub
    (continuous_pathIntegral hc (continuous_gramDriftEntry D0 D e))

theorem continuous_pBr (hc : Continuous fun t => g t - birthSum j b (t : ℝ))
    (e e' : Fin 2 × c × c) : Continuous (pBr D0 D j g b e e') :=
  ((continuous_pComp hc e).mul (continuous_pComp hc e')).sub
    (continuous_pathIntegral hc (continuous_gramCovEntry D0 D e e'))

omit [Fintype c] [DecidableEq c] in
theorem continuous_shift (hc : Continuous fun t => g t - birthSum j b (t : ℝ)) (a : ℝ≥0) :
    Continuous fun v : ℝ≥0 => g (a + v) - birthSum j (fun f => b f - a) (v : ℝ) := by
  have e : (fun v : ℝ≥0 => g (a + v) - birthSum j (fun f => b f - a) (v : ℝ)) =
      (fun t => g t - birthSum j b (t : ℝ)) ∘ fun v => a + v := by
    funext v; simp only [Function.comp, birthSum_shift]
  rw [e]
  exact hc.comp (continuous_const.add continuous_id)

/-- **Restart identity** for the compensated coordinates. -/
theorem pComp_shift (hc : Continuous fun t => g t - birthSum j b (t : ℝ)) (a u : ℝ≥0)
    (e : Fin 2 × c × c) :
    pComp D0 D j (fun v => g (a + v)) (fun f => b f - a) e u =
      pComp D0 D j g b e (a + u) - pComp D0 D j g b e a := by
  simp only [pComp, birthSum_shift, add_zero]
  rw [pathIntegral_shift hc (continuous_gramDriftEntry D0 D e) a u]
  ring

/-- **Restart identity** for the compensated products (with the cross terms). -/
theorem pBr_shift (hc : Continuous fun t => g t - birthSum j b (t : ℝ)) (a u : ℝ≥0)
    (e e' : Fin 2 × c × c) :
    pBr D0 D j (fun v => g (a + v)) (fun f => b f - a) e e' u =
      (pBr D0 D j g b e e' (a + u) - pBr D0 D j g b e e' a) -
        pComp D0 D j g b e a * pComp D0 D j (fun v => g (a + v)) (fun f => b f - a) e' u -
        pComp D0 D j g b e' a * pComp D0 D j (fun v => g (a + v)) (fun f => b f - a) e u := by
  unfold pBr
  rw [pComp_shift hc, pComp_shift hc, pathIntegral_shift hc (continuous_gramCovEntry D0 D e e') a u]
  ring

/-!
### Stopping times and restarts
-/

theorem stopTime_zero' (t : ℝ≥0) : stopTime 0 t = 0 := by
  rw [show (0 : WithTop ℝ≥0) = ((0 : ℝ≥0) : WithTop ℝ≥0) from rfl, stopTime_coe, min_eq_right zero_le]

theorem stopTime_of_le {θ : WithTop ℝ≥0} {a : ℝ≥0} (h : θ ≤ a) (v : ℝ≥0) :
    stopTime θ (a + v) = stopTime θ a := by
  induction θ with
  | top => exact absurd h (not_le.2 (WithTop.coe_lt_top a))
  | coe x =>
    have hx : x ≤ a := WithTop.coe_le_coe.1 h
    rw [stopTime_coe, stopTime_coe, min_eq_right (hx.trans le_self_add), min_eq_right hx]

theorem stopTime_add {θ : WithTop ℝ≥0} {a : ℝ≥0} (h : (a : WithTop ℝ≥0) < θ) (u : ℝ≥0) :
    stopTime θ (a + u) = a + stopTime (θ - a) u ∧ stopTime θ a = a := by
  induction θ with
  | top => rw [WithTop.top_sub_coe, stopTime_top, stopTime_top, stopTime_top]; exact ⟨rfl, rfl⟩
  | coe x =>
    have hx : a < x := WithTop.coe_lt_coe.1 h
    rw [← WithTop.coe_sub, stopTime_coe, stopTime_coe, stopTime_coe, min_eq_left hx.le]
    refine ⟨?_, rfl⟩
    rw [← min_add_add_left, add_tsub_cancel_of_le hx.le]

theorem sub_eq_zero_of_le' {θ : WithTop ℝ≥0} {a : ℝ≥0} (h : θ ≤ a) : θ - a = 0 :=
  tsub_eq_zero_of_le h

/-- **Restart identity after stopping** (compensated coordinates). -/
theorem pComp_stop_shift (hc : Continuous fun t => g t - birthSum j b (t : ℝ)) (θ : WithTop ℝ≥0)
    (a u : ℝ≥0) (e : Fin 2 × c × c) :
    pComp D0 D j (fun v => g (a + v)) (fun f => b f - a) e (stopTime (θ - a) u) =
      pComp D0 D j g b e (stopTime θ (a + u)) - pComp D0 D j g b e (stopTime θ a) := by
  rcases le_or_gt θ a with h | h
  · rw [sub_eq_zero_of_le' h, stopTime_zero', pComp_zero, stopTime_of_le h, sub_self]
  · obtain ⟨h1, h2⟩ := stopTime_add h u
    rw [h1, h2, pComp_shift hc]

/-- **Restart identity after stopping** (compensated products). -/
theorem pBr_stop_shift (hc : Continuous fun t => g t - birthSum j b (t : ℝ)) (θ : WithTop ℝ≥0)
    (a u : ℝ≥0) (e e' : Fin 2 × c × c) :
    pBr D0 D j (fun v => g (a + v)) (fun f => b f - a) e e' (stopTime (θ - a) u) =
      (pBr D0 D j g b e e' (stopTime θ (a + u)) - pBr D0 D j g b e e' (stopTime θ a)) -
        pComp D0 D j g b e (stopTime θ a) *
          pComp D0 D j (fun v => g (a + v)) (fun f => b f - a) e' (stopTime (θ - a) u) -
        pComp D0 D j g b e' (stopTime θ a) *
          pComp D0 D j (fun v => g (a + v)) (fun f => b f - a) e (stopTime (θ - a) u) := by
  rcases le_or_gt θ a with h | h
  · rw [sub_eq_zero_of_le' h, stopTime_zero', pBr_zero, pComp_zero, pComp_zero, stopTime_of_le h]
    ring
  · obtain ⟨h1, h2⟩ := stopTime_add h u
    rw [h1, h2, pBr_shift hc]

end BlockBand.SourceProcess.BornRestart
