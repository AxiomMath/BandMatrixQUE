module

public import BlockBand.Transmission.Dual.GSeqColl
public import BlockBand.Transmission.Dual.GStopLaw

/-!
# The boundary classification on the sequence space: the induction

Exhaustion `boxExh p n₀ n = flatBox p (n₀ + n)` (`z ∈ W 0` means `z ∈ flatBox p n₀`).
* `GSeq D₀ q`: **the boundary classification at level `q + 1` on the sequence space** — for every
  start `z ∈ flatBox (q+1) n₀`, every `B1Family`, every monotone radii with the boxes inside the
  chart balls and every `t₀`, the stop sequence is a.s. in `goodSeq` (before `t₀` the left limit
  at `ρ_∞` exists and is a paired corner with survivors in `𝒞_q`). `GSeq D₀ 0` is the corner
  limit at level one in this form.
* `A3Seq D₀`: the atomlessness of the level-one lifetime in this form (the level-1 `ρ_∞` has no
  atom before `t₀`).
* `map_stopSeq_eq`: the law of `F.stopSeq W t₀ r` does not depend on the radii (uniqueness for
  stopped martingale problems).
* **`gSeq_succ`**: `GSeq D₀ 0 → A3Seq D₀ → GSeq D₀ q → GSeq D₀ (q + 1)` (domination by
  `dominate_stopSeq`, the corner case by `measure_slotSeq_bad`, collisions by
  `measure_collLim`); **`gSeq_all`**: under these two base cases, the classification holds at
  every level.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.Transmission.Dual
open scoped NNReal ENNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {D0 : ℝ}

/-- The shifted box exhaustion of `𝒞_p`. -/
def boxExh (p n₀ : ℕ) (n : ℕ) : Set (Fin (p + p) → ℝ) := flatBox p (n₀ + n)

theorem isExh_boxExh (p n₀ : ℕ) : IsExh (boxExh p n₀) (flatChamber p) where
  dom n := isInteriorDomain_flatBox p _
  succ n := closure_flatBox_subset_succ p _
  cover x hx := by
    obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_mem_boxOpen (q := p) hx)
    exact ⟨N, hN (n₀ + N) (Nat.le_add_left N n₀)⟩

theorem exists_boxRad (p n₀ : ℕ) : ∃ B : ℕ → ℕ,
    ∀ n, boxExh p n₀ n ⊆ chartQ p '' Metric.ball 0 (B n) := by
  choose B hB using fun n => exists_ball_superset ((isExh_boxExh p n₀).dom n).2.1
    ((isExh_boxExh p n₀).dom n).2.2
  exact ⟨B, fun n => subset_closure.trans (hB n)⟩

/-- **The boundary classification at level `q + 1` on the sequence space.** -/
def GSeq (D0 : ℝ) (q : ℕ) : Prop :=
  ∀ (z : Fin ((q + 1) + (q + 1)) → ℝ) (n₀ : ℕ), z ∈ flatBox (q + 1) n₀ →
    ∀ (F : B1Family D0 (q + 1) z) (r : ℕ → ℕ), Monotone r →
      (∀ n, boxExh (q + 1) n₀ n ⊆ chartQ (q + 1) '' Metric.ball 0 (r n)) → ∀ t₀ : ℝ≥0,
        ∀ᵐ ω ∂Pq (q + 1), F.stopSeq (boxExh (q + 1) n₀) t₀ r ω ∈ goodSeq q (boxExh (q + 1) n₀) t₀

/-- **Atomlessness of the level-one lifetime on the sequence space**: the level-1 `ρ_∞` has no
atom before `t₀`. -/
def A3Seq (D0 : ℝ) : Prop :=
  ∀ (z : Fin (1 + 1) → ℝ) (n₀ : ℕ), z ∈ flatBox 1 n₀ → ∀ (F : B1Family D0 1 z) (r : ℕ → ℕ),
    Monotone r → (∀ n, boxExh 1 n₀ n ⊆ chartQ 1 '' Metric.ball 0 (r n)) → ∀ t₀ u : ℝ≥0, u < t₀ →
      Pq 1 {ω | sinf (boxExh 1 n₀) t₀ (F.stopSeq (boxExh 1 n₀) t₀ r ω) = u} = 0

/-- The law of the stop sequence of a `B1Family` does not depend on the radii. -/
theorem map_stopSeq_eq (hD0 : 0 < D0) {q : ℕ} {z : Fin (q + q) → ℝ} (F : B1Family D0 q z)
    {W : ℕ → Set (Fin (q + q) → ℝ)} (hE : IsExh W (flatChamber q)) (hz : z ∈ W 0) (t₀ : ℝ≥0)
    {r r' : ℕ → ℕ} (hr : Monotone r) (hr' : Monotone r')
    (hb : ∀ n, W n ⊆ chartQ q '' Metric.ball 0 (r n))
    (hb' : ∀ n, W n ⊆ chartQ q '' Metric.ball 0 (r' n)) :
    (Pq q).map (F.stopSeq W t₀ r) = (Pq q).map (F.stopSeq W t₀ r') := by
  have hz' : z ∈ flatChamber q := (hE.dom 0).2.2 (subset_closure hz)
  exact map_eq_of_isMPSolutionOn hD0 hE.dom (F.measurable_stopSeq hE.isOpen r)
    (F.measurable_stopSeq hE.isOpen r') (F.isStopSeq_stopSeq hD0 hE.isOpen hE.mono hr hb)
    (F.isStopSeq_stopSeq hD0 hE.isOpen hE.mono hr' hb') (F.isDualStopAt hD0 hz' hb)
    (F.isDualStopAt hD0 hz' hb')

theorem ae_mem_iff_map {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] {P : Measure Ω}
    {Φ : Ω → α} (hΦ : Measurable Φ) {S : Set α} (hS : MeasurableSet S) :
    (∀ᵐ ω ∂P, Φ ω ∈ S) ↔ P.map Φ Sᶜ = 0 := by
  rw [Measure.map_apply hΦ hS.compl, ae_iff]; rfl

theorem slotJoin_parts {q : ℕ} (j : Fin (q + 1)) (z : Fin ((q + 1) + (q + 1)) → ℝ) :
    slotJoin j (leftPart (z ∘ (slotEquiv j).symm)) (rightPart (z ∘ (slotEquiv j).symm)) = z := by
  have e : (slotEquiv j).symm = slot j := funext fun s => slotEquiv_symm_apply j s
  rw [slotJoin, e]; exact append_slot_comp j z

theorem pair_mem_flatBox {q : ℕ} (j : Fin (q + 1)) {m : ℕ} {w : Fin ((q + 1) + (q + 1)) → ℝ}
    (hw : w ∈ flatBox (q + 1) m) : leftPart (w ∘ (slotEquiv j).symm) ∈ flatBox 1 m := by
  show ofFlat 1 _ ∈ boxOpen 1 m
  rw [ofFlat_left_slot]; exact pair_mem_boxOpen j hw

theorem rest_mem_flatBox {q : ℕ} (j : Fin (q + 1)) {m : ℕ} {w : Fin ((q + 1) + (q + 1)) → ℝ}
    (hw : w ∈ flatBox (q + 1) m) : rightPart (w ∘ (slotEquiv j).symm) ∈ flatBox q m := by
  show ofFlat q _ ∈ boxOpen q m
  rw [ofFlat_right_slot]; exact rest_mem_boxOpen j hw

/-- **The induction step of the boundary classification** on the sequence space. -/
theorem gSeq_succ (hD0 : 0 < D0) (h1 : GSeq D0 0) (hA3 : A3Seq D0) {q : ℕ} (hq : GSeq D0 q) :
    GSeq D0 (q + 1) := by
  intro z n₀ hz F r hr hball t₀
  set W := boxExh ((q + 1) + 1) n₀
  have hE := isExh_boxExh ((q + 1) + 1) n₀
  have hE₁ := isExh_boxExh 1 n₀
  have hE₂ := isExh_boxExh (q + 1) n₀
  have hz' : z ∈ flatChamber ((q + 1) + 1) := (hE.dom 0).2.2 (subset_closure hz)
  have hF₁ := fun j : Fin ((q + 1) + 1) =>
    (nonempty_b1Family hD0 (leftPart (z ∘ (slotEquiv j).symm))).some
  have hF₂ := fun j : Fin ((q + 1) + 1) =>
    (nonempty_b1Family (q := q + 1) hD0 (rightPart (z ∘ (slotEquiv j).symm))).some
  obtain ⟨R, hR⟩ := dominate_stopSeq hD0 hE.dom hE.mono hz F hF₁ hF₂ t₀
  obtain ⟨B, hB⟩ := exists_boxRad ((q + 1) + 1) n₀
  obtain ⟨B₁, hB₁⟩ := exists_boxRad 1 n₀
  obtain ⟨B₂, hB₂⟩ := exists_boxRad (q + 1) n₀
  set r' := majorant fun n => max (R n) (B n)
  set a := majorant fun n => max (R n) (B₁ n)
  set b := majorant fun n => max (R n) (B₂ n)
  have hr' := monotone_majorant fun n => max (R n) (B n)
  have ha := monotone_majorant fun n => max (R n) (B₁ n)
  have hb := monotone_majorant fun n => max (R n) (B₂ n)
  have le_r' : ∀ n, max (R n) (B n) ≤ r' n := le_majorant _
  have le_a : ∀ n, max (R n) (B₁ n) ≤ a n := le_majorant _
  have le_b : ∀ n, max (R n) (B₂ n) ≤ b n := le_majorant _
  have hball' : ∀ n, W n ⊆ chartQ ((q + 1) + 1) '' Metric.ball 0 (r' n) := fun n =>
    (hB n).trans (chartQ_ball_mono ((le_max_right _ _).trans (le_r' n)))
  have hball₁ : ∀ n, boxExh 1 n₀ n ⊆ chartQ 1 '' Metric.ball 0 (a n) := fun n =>
    (hB₁ n).trans (chartQ_ball_mono ((le_max_right _ _).trans (le_a n)))
  have hball₂ : ∀ n, boxExh (q + 1) n₀ n ⊆ chartQ (q + 1) '' Metric.ball 0 (b n) := fun n =>
    (hB₂ n).trans (chartQ_ball_mono ((le_max_right _ _).trans (le_b n)))
  have hS := measurableSet_goodSeq (q := q + 1) (t₀ := t₀) hE.isOpen
  rw [ae_mem_iff_map (F.measurable_stopSeq hE.isOpen r) hS,
    map_stopSeq_eq hD0 F hE hz t₀ hr hr' hball hball']
  refine le_antisymm ((measure_mono (compl_goodSeq_subset _ _ _)).trans
    ((measure_union_le _ _).trans ?_)) bot_le
  rw [measure_collLim hD0 hE hz F hr' hball', add_zero]
  have hdom := hR r' a b hr' ha hb fun n =>
    ⟨(le_max_left _ _).trans (le_r' n), (le_max_left _ _).trans (le_a n),
      (le_max_left _ _).trans (le_b n)⟩
  refine (Measure.le_iff'.1 hdom _).trans (le_of_eq ?_)
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Measure.smul_apply, smul_eq_mul]
  have hz₁ := left_slot_mem hz' j
  have hz₂ := right_slot_mem hz' j
  have hWU : ∀ n, ∀ w ∈ W n, leftPart (w ∘ (slotEquiv j).symm) ∈ boxExh 1 n₀ n ∧
      rightPart (w ∘ (slotEquiv j).symm) ∈ boxExh (q + 1) n₀ n := fun n w hw =>
    ⟨pair_mem_flatBox j hw, rest_mem_flatBox j hw⟩
  have hP1 := h1 _ n₀ (pair_mem_flatBox j hz) (hF₁ j) a ha hball₁ t₀
  have hG := hq _ n₀ (rest_mem_flatBox j hz) (hF₂ j) b hb hball₂ t₀
  have hA := hA3 _ n₀ (pair_mem_flatBox j hz) (hF₁ j) a ha hball₁ t₀
  rw [measure_slotSeq_bad hD0 j (hF₁ j) (hF₂ j) hz₁ hz₂ (by rw [slotJoin_parts]; exact hz) hE hE₁
    hE₂ hWU ha hb hball₁ hball₂ hP1 hG hA, mul_zero]

/-- **The boundary classification at every level**, on the sequence space, from the level-one
corner limit and the atomlessness of the lifetime in that form. -/
theorem gSeq_all (hD0 : 0 < D0) (h1 : GSeq D0 0) (hA3 : A3Seq D0) : ∀ q, GSeq D0 q
  | 0 => h1
  | q + 1 => gSeq_succ hD0 h1 hA3 (gSeq_all hD0 h1 hA3 q)

end BlockBand.Transmission.Dual.G
