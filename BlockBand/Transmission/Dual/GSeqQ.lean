module

public import BlockBand.Transmission.Dual.GSeqSlot
public import BlockBand.Transmission.Dual.GDomPath

/-!
# The corner case of the boundary classification under `Q^{(j)}`

* `B1Family.isNested_stopSeq`, `isNested_slotSeq`: on the consistency event the stop sequences
  of a `B1Family` and of `Q^{(j)}` are nested **pathwise** (the a.s. statements of
  `isStopSeq_stopSeq`, `isStopSeq_slotSeq` at a fixed `ω`).
* `slotRel_slotSeq`: on the consistency event the `Q^{(j)}` stop sequence, the pair stop
  sequence `F₁.stopSeq W₁` and the rest stop sequence `F₂.stopSeq W₂` satisfy `SlotRel`
  (projections `W n → W₁ n, W₂ n`).
* **`measure_slotSeq_bad`**: if the corner limit holds for the pair and the boundary
  classification at level `p − 1` for the rest (a.s. membership of their stop sequences in
  `goodSeq`), and the pair lifetime `ρ_∞(û)` has no atom before `t₀`, then
  `Q^{(j)}(slotSeq ∈ badLim ∪ badCorner) = 0`. The `badLim` part does not use the atomlessness
  (`measure_slotSeq_badLim`). Fubini: `measure_prod_eq_zero_of_atomless`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.Semimartingale (stopTime stopTime_le)
open BlockBand.Transmission.Dual
open scoped NNReal ENNReal

variable {q : ℕ} {D0 : ℝ} {t₀ : ℝ≥0}

theorem pstop_apply_zero {d : ℕ} (W : Set (Fin d → ℝ)) (t₀ : ℝ≥0) (w : CPath d) :
    (pstop W t₀ w).1 0 = w.1 0 := by
  show w.1 (stopTime (pexit W w) (min 0 t₀)) = w.1 0
  rw [min_eq_left zero_le, nonpos_iff_eq_zero.1 (stopTime_le _ _)]

/-!
## Pathwise nestedness
-/

theorem B1Family.isNested_stopSeq {z : Fin (q + q) → ℝ} (F : B1Family D0 q z)
    {W : ℕ → Set (Fin (q + q) → ℝ)} (hW : ∀ n, IsOpen (W n)) (hmono : Monotone W)
    {r : ℕ → ℕ} (hr : Monotone r) (hball : ∀ n, W n ⊆ chartQ q '' Metric.ball 0 (r n))
    {ω : Ωq q} (hc : F.IsConsAt ω) : IsNested W t₀ (F.stopSeq W t₀ r ω) := by
  intro k n hkn
  show pstop (W k) t₀ (F.cpath (r k) ω) = pstop (W k) t₀ (pstop (W n) t₀ (F.cpath (r n) ω))
  rw [pstop_pstop (hW k) (hmono hkn)]
  refine (pstop_congr (hW k) t₀ fun u hu => ?_).symm
  exact F.Yf_eq_of_le hc (hr hkn)
    ((hu.trans (min_le_left _ _)).trans (F.pexit_cpath_le (hball k) ω))

theorem B1Family.stopSeq_zero {z : Fin (q + q) → ℝ} (F : B1Family D0 q z) (hz : z ∈ flatChamber q)
    (W : ℕ → Set (Fin (q + q) → ℝ)) (r : ℕ → ℕ) (ω : Ωq q) :
    (F.stopSeq W t₀ r ω 0).1 0 = z := by
  rw [B1Family.stopSeq, pstop_apply_zero]; exact F.Yf_zero hz _ ω

variable {z₁ : Fin (1 + 1) → ℝ} {z₂ : Fin (q + q) → ℝ}

theorem isNested_slotSeq (j : Fin (q + 1)) (F₁ : B1Family D0 1 z₁) (F₂ : B1Family D0 q z₂)
    {W : ℕ → Set (Fin ((q + 1) + (q + 1)) → ℝ)} (hW : ∀ n, IsOpen (W n)) (hmono : Monotone W)
    {a b : ℕ → ℕ} (ha : Monotone a) (hb : Monotone b)
    (hball : ∀ n, ∀ w ∈ W n, leftPart (w ∘ (slotEquiv j).symm) ∈ chartQ 1 '' Metric.ball 0 (a n) ∧
      rightPart (w ∘ (slotEquiv j).symm) ∈ chartQ q '' Metric.ball 0 (b n))
    {x : Ωq 1 × Ωq q} (hc₁ : F₁.IsConsAt x.1) (hc₂ : F₂.IsConsAt x.2) :
    IsNested W t₀ (slotSeq j F₁ F₂ W t₀ a b x) := by
  intro k n hkn
  show pstop (W k) t₀ (slotCPath j F₁ F₂ (a k) (b k) x) =
    pstop (W k) t₀ (pstop (W n) t₀ (slotCPath j F₁ F₂ (a n) (b n) x))
  rw [pstop_pstop (hW k) (hmono hkn)]
  refine (pstop_congr (hW k) t₀ fun u hu => ?_).symm
  have hu' : (u : WithTop ℝ≥0) ≤ exitTimeFrom (W k) (slotPath j (F₁.Yf (a k)) (F₂.Yf (b k))) x :=
    hu.trans (min_le_left _ _)
  have h₁ : (u : WithTop ℝ≥0) ≤ F₁.e (a k) x.1 :=
    (hu'.trans (exitTimeFrom_slotPath_le_left j (fun w hw => (hball k w hw).1) x)).trans
      (F₁.exitTimeFrom_le_e subset_rfl x.1)
  have h₂ : (u : WithTop ℝ≥0) ≤ F₂.e (b k) x.2 :=
    (hu'.trans (exitTimeFrom_slotPath_le_right j (fun w hw => (hball k w hw).2) x)).trans
      (F₂.exitTimeFrom_le_e subset_rfl x.2)
  show slotPath j (F₁.Yf (a n)) (F₂.Yf (b n)) u x = slotPath j (F₁.Yf (a k)) (F₂.Yf (b k)) u x
  simp only [slotPath, prodPath]
  rw [F₁.Yf_eq_of_le hc₁ (ha hkn) h₁, F₂.Yf_eq_of_le hc₂ (hb hkn) h₂]

/-!
## The slot relation for `Q^{(j)}`
-/

theorem leftPart_slotJoin {q : ℕ} (j : Fin (q + 1)) (p : Fin (1 + 1) → ℝ) (r : Fin (q + q) → ℝ) :
    leftPart (slotJoin j p r ∘ (slotEquiv j).symm) = p := by
  rw [slotJoin_comp_symm]; exact funext fun i => Fin.append_left p r i

theorem rightPart_slotJoin {q : ℕ} (j : Fin (q + 1)) (p : Fin (1 + 1) → ℝ) (r : Fin (q + q) → ℝ) :
    rightPart (slotJoin j p r ∘ (slotEquiv j).symm) = r := by
  rw [slotJoin_comp_symm]; exact funext fun i => Fin.append_right p r i

section SlotRelQ

variable {q : ℕ} {z₁ : Fin (1 + 1) → ℝ} {z₂ : Fin ((q + 1) + (q + 1)) → ℝ}
  {W : ℕ → Set (Fin (((q + 1) + 1) + ((q + 1) + 1)) → ℝ)} {W₁ : ℕ → Set (Fin (1 + 1) → ℝ)}
  {W₂ : ℕ → Set (Fin ((q + 1) + (q + 1)) → ℝ)}

theorem slotRel_slotSeq (j : Fin ((q + 1) + 1)) (F₁ : B1Family D0 1 z₁)
    (F₂ : B1Family D0 (q + 1) z₂) (hz₁ : z₁ ∈ flatChamber 1) (hz₂ : z₂ ∈ flatChamber (q + 1))
    (hz : slotJoin j z₁ z₂ ∈ W 0) (hE : IsExh W (flatChamber ((q + 1) + 1)))
    (hE₁ : IsExh W₁ (flatChamber 1)) (hE₂ : IsExh W₂ (flatChamber (q + 1)))
    (hWU : ∀ n, ∀ w ∈ W n, leftPart (w ∘ (slotEquiv j).symm) ∈ W₁ n ∧
      rightPart (w ∘ (slotEquiv j).symm) ∈ W₂ n)
    {a b : ℕ → ℕ} (ha : Monotone a) (hb : Monotone b)
    (hball₁ : ∀ n, W₁ n ⊆ chartQ 1 '' Metric.ball 0 (a n))
    (hball₂ : ∀ n, W₂ n ⊆ chartQ (q + 1) '' Metric.ball 0 (b n))
    {x : Ωq 1 × Ωq (q + 1)} (hc₁ : F₁.IsConsAt x.1) (hc₂ : F₂.IsConsAt x.2) :
    SlotRel W W₁ W₂ t₀ j (slotSeq j F₁ F₂ W t₀ a b x) (F₁.stopSeq W₁ t₀ a x.1)
      (F₂.stopSeq W₂ t₀ b x.2) := by
  have hle₁ : ∀ n, pexit (W n) (slotCPath j F₁ F₂ (a n) (b n) x) ≤
      pexit (W₁ n) (F₁.cpath (a n) x.1) := fun n =>
    exitTimeFrom_slotPath_le_left j (fun w hw => (hWU n w hw).1) x
  have hle₂ : ∀ n, pexit (W n) (slotCPath j F₁ F₂ (a n) (b n) x) ≤
      pexit (W₂ n) (F₂.cpath (b n) x.2) := fun n =>
    exitTimeFrom_slotPath_le_right j (fun w hw => (hWU n w hw).2) x
  have hs : ∀ n, (srho W t₀ (slotSeq j F₁ F₂ W t₀ a b x) n : WithTop ℝ≥0) =
      min (pexit (W n) (slotCPath j F₁ F₂ (a n) (b n) x)) t₀ := fun n => by
    rw [coe_srho]; exact min_pexit_pstop (hE.isOpen n) _
  have hs₁ : ∀ n, (srho W₁ t₀ (F₁.stopSeq W₁ t₀ a x.1) n : WithTop ℝ≥0) =
      min (pexit (W₁ n) (F₁.cpath (a n) x.1)) t₀ := fun n => by
    rw [coe_srho]; exact min_pexit_pstop (hE₁.isOpen n) _
  have hs₂ : ∀ n, (srho W₂ t₀ (F₂.stopSeq W₂ t₀ b x.2) n : WithTop ℝ≥0) =
      min (pexit (W₂ n) (F₂.cpath (b n) x.2)) t₀ := fun n => by
    rw [coe_srho]; exact min_pexit_pstop (hE₂.isOpen n) _
  have hballQ : ∀ n, ∀ w ∈ W n,
      leftPart (w ∘ (slotEquiv j).symm) ∈ chartQ 1 '' Metric.ball 0 (a n) ∧
      rightPart (w ∘ (slotEquiv j).symm) ∈ chartQ (q + 1) '' Metric.ball 0 (b n) :=
    fun n w hw => ⟨hball₁ n (hWU n w hw).1, hball₂ n (hWU n w hw).2⟩
  refine ⟨isNested_slotSeq j F₁ F₂ hE.isOpen hE.mono ha hb hballQ hc₁ hc₂,
    F₁.isNested_stopSeq hE₁.isOpen hE₁.mono ha hball₁ hc₁,
    F₂.isNested_stopSeq hE₂.isOpen hE₂.mono hb hball₂ hc₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (pstop (W 0) t₀ (slotCPath j F₁ F₂ (a 0) (b 0) x)).1 0 ∈ W 0
    rw [pstop_apply_zero]
    show slotJoin j (F₁.Yf (a 0) 0 x.1) (F₂.Yf (b 0) 0 x.2) ∈ W 0
    rw [F₁.Yf_zero hz₁, F₂.Yf_zero hz₂]; exact hz
  · rw [F₁.stopSeq_zero hz₁]
    have := (hWU 0 _ hz).1
    rwa [leftPart_slotJoin] at this
  · rw [F₂.stopSeq_zero hz₂]
    have := (hWU 0 _ hz).2
    rwa [rightPart_slotJoin] at this
  · intro n t ht
    have h1 : (t : WithTop ℝ≥0) ≤ min (pexit (W n) (slotCPath j F₁ F₂ (a n) (b n) x)) t₀ := by
      rw [← hs]; exact WithTop.coe_le_coe.2 ht
    show (pstop (W n) t₀ (slotCPath j F₁ F₂ (a n) (b n) x)).1 t =
      slotJoin j ((pstop (W₁ n) t₀ (F₁.cpath (a n) x.1)).1 t)
        ((pstop (W₂ n) t₀ (F₂.cpath (b n) x.2)).1 t)
    rw [pstop_apply_of_le h1, pstop_apply_of_le (h1.trans (min_le_min (hle₁ n) le_rfl)),
      pstop_apply_of_le (h1.trans (min_le_min (hle₂ n) le_rfl))]
    rfl
  · intro n
    rw [← WithTop.coe_le_coe, hs, hs₁]; exact min_le_min (hle₁ n) le_rfl
  · intro n
    rw [← WithTop.coe_le_coe, hs, hs₂]; exact min_le_min (hle₂ n) le_rfl

/-!
## The measure of the bad events under `Q^{(j)}`
-/

/-- **Fubini**: two independent lifetimes, one without atoms before `t₀`, do not coincide
before `t₀`. -/
theorem measure_prod_eq_zero_of_atomless {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν] {f : α → ℝ≥0} {g : β → ℝ≥0}
    (hf : Measurable f) (hg : Measurable g) (h : ∀ u < t₀, μ {x | f x = u} = 0) :
    μ.prod ν {x | f x.1 = g x.2 ∧ f x.1 < t₀} = 0 := by
  have hE : MeasurableSet {x : α × β | f x.1 = g x.2 ∧ f x.1 < t₀} :=
    (measurableSet_eq_fun (hf.comp measurable_fst) (hg.comp measurable_snd)).inter
      ((hf.comp measurable_fst) (measurableSet_Iio (a := t₀)))
  rw [Measure.prod_apply_symm hE]
  refine le_antisymm ((lintegral_mono fun y => (?_ : _ ≤ (0 : ℝ≥0∞))).trans lintegral_zero.le)
    bot_le
  by_cases hy : g y < t₀
  · exact (measure_mono fun x hx => hx.1).trans (h (g y) hy).le
  · refine (measure_mono fun x hx => ?_).trans (measure_empty (μ := μ)).le
    exact absurd (hx.1 ▸ hx.2) hy

variable (hD0 : 0 < D0) (j : Fin ((q + 1) + 1)) (F₁ : B1Family D0 1 z₁)
  (F₂ : B1Family D0 (q + 1) z₂) (hz₁ : z₁ ∈ flatChamber 1) (hz₂ : z₂ ∈ flatChamber (q + 1))
  (hz : slotJoin j z₁ z₂ ∈ W 0) (hE : IsExh W (flatChamber ((q + 1) + 1)))
  (hE₁ : IsExh W₁ (flatChamber 1)) (hE₂ : IsExh W₂ (flatChamber (q + 1)))
  (hWU : ∀ n, ∀ w ∈ W n, leftPart (w ∘ (slotEquiv j).symm) ∈ W₁ n ∧
    rightPart (w ∘ (slotEquiv j).symm) ∈ W₂ n)
  {a b : ℕ → ℕ} (ha : Monotone a) (hb : Monotone b)
  (hball₁ : ∀ n, W₁ n ⊆ chartQ 1 '' Metric.ball 0 (a n))
  (hball₂ : ∀ n, W₂ n ⊆ chartQ (q + 1) '' Metric.ball 0 (b n))
  (hP1 : ∀ᵐ ω ∂Pq 1, F₁.stopSeq W₁ t₀ a ω ∈ goodSeq 0 W₁ t₀)
  (hG : ∀ᵐ ω ∂Pq (q + 1), F₂.stopSeq W₂ t₀ b ω ∈ goodSeq q W₂ t₀)
include hD0 hz₁ hz₂ hz hE hE₁ hE₂ hWU ha hb hball₁ hball₂ hP1 hG

/-- **No left limit is `Q^{(j)}`-null** (no atomlessness needed). -/
theorem measure_slotSeq_badLim :
    ((Pq 1).prod (Pq (q + 1))).map (slotSeq j F₁ F₂ W t₀ a b) (badLim (q + 1) W t₀) = 0 := by
  rw [Measure.map_apply (measurable_slotSeq j F₁ F₂ hE.isOpen a b) (measurableSet_badLim hE.isOpen)]
  refine measure_eq_zero_iff_ae_notMem.2 ?_
  filter_upwards [ae_fst (Q₂ := Pq (q + 1)) ((F₁.ae_isConsAt hD0).and hP1),
    ae_snd (Q₁ := Pq 1) ((F₂.ae_isConsAt hD0).and hG)] with x h₁ h₂
  exact (slotRel_slotSeq (t₀ := t₀) j F₁ F₂ hz₁ hz₂ hz hE hE₁ hE₂ hWU ha hb hball₁ hball₂ h₁.1
    h₂.1).notMem_badLim hE hE₁ hE₂ h₁.2 h₂.2

/-- **The corner case**: `Q^{(j)}(slotSeq ∈ badLim ∪ badCorner) = 0`, using that the pair
lifetime has no atoms before `t₀`. -/
theorem measure_slotSeq_bad
    (hA3 : ∀ u < t₀, Pq 1 {ω | sinf W₁ t₀ (F₁.stopSeq W₁ t₀ a ω) = u} = 0) :
    ((Pq 1).prod (Pq (q + 1))).map (slotSeq j F₁ F₂ W t₀ a b)
      (badLim (q + 1) W t₀ ∪ badCorner (q + 1) W t₀) = 0 := by
  have hf : Measurable fun ω => sinf W₁ t₀ (F₁.stopSeq W₁ t₀ a ω) :=
    (measurable_sinf hE₁.isOpen).comp (F₁.measurable_stopSeq hE₁.isOpen a)
  have hg : Measurable fun ω => sinf W₂ t₀ (F₂.stopSeq W₂ t₀ b ω) :=
    (measurable_sinf hE₂.isOpen).comp (F₂.measurable_stopSeq hE₂.isOpen b)
  rw [Measure.map_apply (measurable_slotSeq j F₁ F₂ hE.isOpen a b)
    ((measurableSet_badLim hE.isOpen).union (measurableSet_badCorner hE.isOpen))]
  refine le_antisymm ((measure_mono_ae ?_).trans
    (measure_prod_eq_zero_of_atomless (ν := Pq (q + 1)) hf hg hA3).le) bot_le
  filter_upwards [ae_fst (Q₂ := Pq (q + 1)) ((F₁.ae_isConsAt hD0).and hP1),
    ae_snd (Q₁ := Pq 1) ((F₂.ae_isConsAt hD0).and hG)] with x h₁ h₂ hx
  have hR := slotRel_slotSeq (t₀ := t₀) j F₁ F₂ hz₁ hz₂ hz hE hE₁ hE₂ hWU ha hb hball₁ hball₂
    h₁.1 h₂.1
  rcases hx with hx | hx
  · exact absurd hx (hR.notMem_badLim hE hE₁ hE₂ h₁.2 h₂.2)
  · exact hR.eq_of_mem_badCorner hE hE₁ hE₂ h₁.2 h₂.2 hx

end SlotRelQ

end BlockBand.Transmission.Dual.G
