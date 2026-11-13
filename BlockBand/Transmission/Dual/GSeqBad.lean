module

public import BlockBand.Transmission.Dual.GSeqPath
public import BlockBand.Transmission.Dual.GCollNull

/-!
# The good and bad events of the boundary classification on the sequence space

Level `q + 1`, flat coordinates `w : Fin ((q+1)+(q+1)) → ℝ` with `(x, y) = ofFlat (q+1) w`. On
`ℕ → CPath`, for an exhaustion `W` and a horizon `t₀`:
* `IsCorner q c`: `c` is a paired corner `(0, x̃; 0, ỹ)` with survivors in `𝒞_q`
  (`restOf 0` form: `isCorner_iff`);
* `PosColl q c`: `x₀ + y₀ > 0` and two `x`'s or two `y`'s coincide (a collision at positive
  height, the event of the collision bound);
* `goodSeq q W t₀`: `ρ_∞ < t₀ →` the left limit exists and is a corner (the conclusion of the
  boundary classification at level `q+1` before `t₀`);
* `badLim`: `ρ_∞ < t₀` and no left limit; `badCorner`: `ρ_∞ < t₀`, a left limit that is neither
  a corner nor a positive-height collision (only `badCorner` needs the atomlessness of the
  lifetime); `collLim`: `ρ_∞ < t₀`, a left limit that is a positive-height collision.
* All are measurable, and `goodSeqᶜ ⊆ badLim ∪ badCorner ∪ collLim` (`compl_goodSeq_subset`).
* `slotJoin j p r = Fin.append p r ∘ slotEquiv j` (the inverse of the pair/rest projections) and
  its coordinates; `mono_of_mem_closure`: closure points of the chamber are weakly ordered.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.Transmission.Dual
open scoped NNReal ENNReal

variable {q : ℕ}

/-!
## The slot join
-/

/-- The level-`(q+1)` point with pair `p` in the slots `(x₀, y_j)` and rest `r`. -/
def slotJoin (j : Fin (q + 1)) (p : Fin (1 + 1) → ℝ) (r : Fin (q + q) → ℝ) :
    Fin ((q + 1) + (q + 1)) → ℝ := Fin.append p r ∘ slotEquiv j

theorem slotJoin_comp_symm (j : Fin (q + 1)) (p : Fin (1 + 1) → ℝ) (r : Fin (q + q) → ℝ) :
    slotJoin j p r ∘ (slotEquiv j).symm = Fin.append p r := by
  funext s; simp [slotJoin]

theorem pairOf_slotJoin (j : Fin (q + 1)) (p : Fin (1 + 1) → ℝ) (r : Fin (q + q) → ℝ) :
    pairOf j (ofFlat (q + 1) (slotJoin j p r)) = ofFlat 1 p := by
  rw [← ofFlat_left_slot, slotJoin_comp_symm]
  congr 1; funext i; exact Fin.append_left p r i

theorem restOf_slotJoin (j : Fin (q + 1)) (p : Fin (1 + 1) → ℝ) (r : Fin (q + q) → ℝ) :
    restOf j (ofFlat (q + 1) (slotJoin j p r)) = ofFlat q r := by
  rw [← ofFlat_right_slot, slotJoin_comp_symm]
  congr 1; funext i; exact Fin.append_right p r i

theorem slotPath_eq_slotJoin {Ω₁ Ω₂ : Type*} (j : Fin (q + 1)) (Y₁ : ℝ≥0 → Ω₁ → Fin (1 + 1) → ℝ)
    (Y₂ : ℝ≥0 → Ω₂ → Fin (q + q) → ℝ) (t : ℝ≥0) (x : Ω₁ × Ω₂) :
    slotPath j Y₁ Y₂ t x = slotJoin j (Y₁ t x.1) (Y₂ t x.2) := rfl

theorem continuous_append {a b : ℕ} :
    Continuous fun pr : (Fin a → ℝ) × (Fin b → ℝ) => Fin.append pr.1 pr.2 := by
  refine continuous_pi fun k => ?_
  induction k using Fin.addCases with
  | left i => simp only [Fin.append_left]; exact (continuous_apply i).comp continuous_fst
  | right i => simp only [Fin.append_right]; exact (continuous_apply i).comp continuous_snd

theorem continuous_slotJoin (j : Fin (q + 1)) :
    Continuous fun pr : (Fin (1 + 1) → ℝ) × (Fin (q + q) → ℝ) => slotJoin j pr.1 pr.2 :=
  continuous_pi fun k => (continuous_apply (slotEquiv j k)).comp continuous_append

/-!
## Closure points of the chamber are weakly ordered
-/

theorem mono_of_mem_closure {c : Fin (q + q) → ℝ} (hc : c ∈ closure (flatChamber q)) :
    (∀ i k : Fin q, i ≤ k → (ofFlat q c).1 i ≤ (ofFlat q c).1 k) ∧
      ∀ i k : Fin q, i ≤ k → (ofFlat q c).2 i ≤ (ofFlat q c).2 k := by
  have c1 : ∀ i, Continuous fun w : Fin (q + q) → ℝ => (ofFlat q w).1 i := fun i =>
    (continuous_apply i).comp (continuous_fst.comp (ofFlat q).continuous)
  have c2 : ∀ i, Continuous fun w : Fin (q + q) → ℝ => (ofFlat q w).2 i := fun i =>
    (continuous_apply i).comp (continuous_snd.comp (ofFlat q).continuous)
  set S : Set (Fin (q + q) → ℝ) := {w | (∀ i k : Fin q, i ≤ k → (ofFlat q w).1 i ≤ (ofFlat q w).1 k) ∧
      ∀ i k : Fin q, i ≤ k → (ofFlat q w).2 i ≤ (ofFlat q w).2 k}
  have hS : IsClosed S := by
    simp only [S, ofPred_and, ofPred_forall]
    exact (isClosed_iInter fun i => isClosed_iInter fun k => isClosed_iInter fun _ =>
      isClosed_le (c1 i) (c1 k)).inter (isClosed_iInter fun i => isClosed_iInter fun k =>
        isClosed_iInter fun _ => isClosed_le (c2 i) (c2 k))
  have hsub : flatChamber q ⊆ S := fun w hw =>
    ⟨fun _ _ h => hw.1.monotone h, fun _ _ h => hw.2.1.monotone h⟩
  exact closure_minimal hsub hS hc

/-!
## Corners and positive-height collisions
-/

/-- A paired corner `(0, x̃; 0, ỹ)` with survivors in `𝒞_q`. -/
def IsCorner (q : ℕ) (c : Fin ((q + 1) + (q + 1)) → ℝ) : Prop :=
  (ofFlat (q + 1) c).1 0 = 0 ∧ (ofFlat (q + 1) c).2 0 = 0 ∧
    rightPart (c ∘ (slotEquiv (0 : Fin (q + 1))).symm) ∈ flatChamber q

theorem isCorner_iff (c : Fin ((q + 1) + (q + 1)) → ℝ) :
    IsCorner q c ↔ (ofFlat (q + 1) c).1 0 = 0 ∧ (ofFlat (q + 1) c).2 0 = 0 ∧
      restOf 0 (ofFlat (q + 1) c) ∈ dualChamber q := by
  unfold IsCorner flatChamber
  rw [mem_preimage, ofFlat_right_slot]

/-- A collision at positive height: `x₀ + y₀ > 0` and two `x`'s or two `y`'s coincide. -/
def PosColl (q : ℕ) (c : Fin ((q + 1) + (q + 1)) → ℝ) : Prop :=
  0 < (ofFlat (q + 1) c).1 0 + (ofFlat (q + 1) c).2 0 ∧
    ((∃ i k : Fin (q + 1), i < k ∧ (ofFlat (q + 1) c).1 i = (ofFlat (q + 1) c).1 k) ∨
      ∃ i k : Fin (q + 1), i < k ∧ (ofFlat (q + 1) c).2 i = (ofFlat (q + 1) c).2 k)

theorem measurable_ofFlat_fst (i : Fin (q + 1)) :
    Measurable fun c : Fin ((q + 1) + (q + 1)) → ℝ => (ofFlat (q + 1) c).1 i :=
  ((continuous_apply i).comp (continuous_fst.comp (ofFlat (q + 1)).continuous)).measurable

theorem measurable_ofFlat_snd (i : Fin (q + 1)) :
    Measurable fun c : Fin ((q + 1) + (q + 1)) → ℝ => (ofFlat (q + 1) c).2 i :=
  ((continuous_apply i).comp (continuous_snd.comp (ofFlat (q + 1)).continuous)).measurable

theorem measurable_isCorner : Measurable (IsCorner q) := by
  have hr : Continuous fun c : Fin ((q + 1) + (q + 1)) → ℝ =>
      rightPart (c ∘ (slotEquiv (0 : Fin (q + 1))).symm) :=
    (rightL.comp (compL (slotEquiv (0 : Fin (q + 1))).symm)).continuous
  refine Measurable.and ?_ (Measurable.and ?_ ?_)
  · exact measurableSet_setOfPred.1 (measurableSet_eq_fun (measurable_ofFlat_fst 0) measurable_const)
  · exact measurableSet_setOfPred.1 (measurableSet_eq_fun (measurable_ofFlat_snd 0) measurable_const)
  · exact measurableSet_setOfPred.1 ((isOpen_flatChamber q).preimage hr).measurableSet

theorem measurable_posColl : Measurable (PosColl q) := by
  refine Measurable.and (measurableSet_setOfPred.1 (measurableSet_lt measurable_const
    ((measurable_ofFlat_fst 0).add (measurable_ofFlat_snd 0)))) (Measurable.or ?_ ?_)
  · exact Measurable.exists fun i => Measurable.exists fun k => Measurable.and measurable_const
      (measurableSet_setOfPred.1 (measurableSet_eq_fun (measurable_ofFlat_fst i)
        (measurable_ofFlat_fst k)))
  · exact Measurable.exists fun i => Measurable.exists fun k => Measurable.and measurable_const
      (measurableSet_setOfPred.1 (measurableSet_eq_fun (measurable_ofFlat_snd i)
        (measurable_ofFlat_snd k)))

/-!
## The events on the sequence space
-/

variable (q) (W : ℕ → Set (Fin ((q + 1) + (q + 1)) → ℝ)) (t₀ : ℝ≥0)

/-- The conclusion of the boundary classification at level `q + 1` before `t₀`. -/
def goodSeq : Set (ℕ → CPath ((q + 1) + (q + 1))) :=
  {ŵ | sinf W t₀ ŵ < t₀ → ŵ ∈ llSet W t₀ ∧ IsCorner q (zstar t₀ ŵ)}

/-- No left limit before `t₀`. -/
def badLim : Set (ℕ → CPath ((q + 1) + (q + 1))) :=
  {ŵ | sinf W t₀ ŵ < t₀ ∧ ŵ ∉ llSet W t₀}

/-- A left limit before `t₀` that is neither a corner nor a positive-height collision. -/
def badCorner : Set (ℕ → CPath ((q + 1) + (q + 1))) :=
  {ŵ | sinf W t₀ ŵ < t₀ ∧ ŵ ∈ llSet W t₀ ∧ ¬IsCorner q (zstar t₀ ŵ) ∧ ¬PosColl q (zstar t₀ ŵ)}

/-- A left limit before `t₀` that is a positive-height collision. -/
def collLim : Set (ℕ → CPath ((q + 1) + (q + 1))) :=
  {ŵ | sinf W t₀ ŵ < t₀ ∧ ŵ ∈ llSet W t₀ ∧ PosColl q (zstar t₀ ŵ)}

theorem compl_goodSeq_subset :
    (goodSeq q W t₀)ᶜ ⊆ badLim q W t₀ ∪ badCorner q W t₀ ∪ collLim q W t₀ := by
  intro ŵ hŵ
  simp only [goodSeq, mem_compl_iff, mem_ofPred_eq, not_imp, not_and] at hŵ
  obtain ⟨hlt, hg⟩ := hŵ
  by_cases hl : ŵ ∈ llSet W t₀
  · by_cases hp : PosColl q (zstar t₀ ŵ)
    · exact Or.inr ⟨hlt, hl, hp⟩
    · exact Or.inl (Or.inr ⟨hlt, hl, hg hl, hp⟩)
  · exact Or.inl (Or.inl ⟨hlt, hl⟩)

variable {q W t₀}

theorem measurableSet_sinf_lt (hW : ∀ n, IsOpen (W n)) :
    MeasurableSet {ŵ : ℕ → CPath ((q + 1) + (q + 1)) | sinf W t₀ ŵ < t₀} :=
  measurableSet_lt (measurable_sinf hW) measurable_const

theorem measurableSet_goodSeq (hW : ∀ n, IsOpen (W n)) : MeasurableSet (goodSeq q W t₀) :=
  measurableSet_setOfPred.2 (Measurable.imp (measurableSet_setOfPred.1 (measurableSet_sinf_lt hW))
    (Measurable.and (measurableSet_setOfPred.1 (measurableSet_llSet hW))
      (measurable_isCorner.comp measurable_zstar)))

theorem measurableSet_badLim (hW : ∀ n, IsOpen (W n)) : MeasurableSet (badLim q W t₀) :=
  (measurableSet_sinf_lt hW).inter (measurableSet_llSet hW).compl

theorem measurableSet_badCorner (hW : ∀ n, IsOpen (W n)) : MeasurableSet (badCorner q W t₀) :=
  measurableSet_setOfPred.2 (Measurable.and (measurableSet_setOfPred.1 (measurableSet_sinf_lt hW))
    (Measurable.and (measurableSet_setOfPred.1 (measurableSet_llSet hW))
      (Measurable.and (measurable_isCorner.comp measurable_zstar).not
        (measurable_posColl.comp measurable_zstar).not)))

theorem measurableSet_collLim (hW : ∀ n, IsOpen (W n)) : MeasurableSet (collLim q W t₀) :=
  measurableSet_setOfPred.2 (Measurable.and (measurableSet_setOfPred.1 (measurableSet_sinf_lt hW))
    (Measurable.and (measurableSet_setOfPred.1 (measurableSet_llSet hW))
      (measurable_posColl.comp measurable_zstar)))

end BlockBand.Transmission.Dual.G
