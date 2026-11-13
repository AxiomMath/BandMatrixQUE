module

public import BlockBand.Transmission.Dual.GB1RPath
public import BlockBand.Transmission.Dual.GR4

/-!
# The boundary classification from a random start, pathwise at the chart explosion time

* `e_le_pexit`, **`iSup_pexit_eq_zeta`**: for an exhaustion `W` of the flat chamber and radii
  `r n ≥ n` with `W n ⊆ chartQ '' ball 0 (r n)`, on a consistent path
  `sup_n τ_{W n}(Yf (r n)) = ζ` (compact images of chart balls lie in some `W n`);
* `coe_sinf_stopSeq` (`ρ_∞ ∧ t₀ = ζ ∧ t₀`) and `sglue_stopSeq_eq_Z` (the glued stop sequence is
  `Z` before `ρ_∞`);
* `ae_goodSeq`: `ae_goodSeq_of_randomStart` applied to `Z n = cpath (r n)`, start `ξ ∘ fst`;
* **`ae_tendsto_corner`** (random-start form of `GSeq.ae_tendsto_corner`): a.s. the family is
  consistent and, if `ζ` is finite, the glued path `Z` has a paired-corner left limit at `ζ`
  with survivors in `𝒞_q`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.NativeSDE BlockBand.Transmission.Dual
open scoped NNReal ENNReal

variable {q : ℕ} {D0 : ℝ}
variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]
  {ξ : S → Fin (q + q) → ℝ}

namespace B1R

variable (F : B1R D0 q μ ξ) {W : ℕ → Set (Fin (q + q) → ℝ)} {r : ℕ → ℕ} {ω : ΩR S q}

theorem norm_X_lt {n : ℕ} {s : ℝ≥0} (hs : (s : WithTop ℝ≥0) < F.e n ω) :
    ‖F.X n s ω‖ < n := by
  by_contra h
  have : F.e n ω ≤ s :=
    iInf₂_le (f := fun t (_ : (n : ℝ) ≤ ‖F.X n t ω‖) => (t : WithTop ℝ≥0)) s (not_lt.1 h)
  exact absurd this (not_le.2 hs)

theorem e_le_pexit (hE : IsExh W (flatChamber q)) (hrn : ∀ n, n ≤ r n) (hc : F.IsConsAt ω)
    (m : ℕ) : ∃ n, F.e m ω ≤ pexit (W n) (F.cpath (r n) ω) := by
  have hK : IsCompact (chartQ q '' Metric.closedBall 0 m) :=
    (isCompact_closedBall _ _).image contDiff_chartQ.continuous
  obtain ⟨n, hn⟩ := hK.elim_directed_cover W hE.isOpen
    (fun _ ⟨w, _, hw⟩ => hw ▸ mem_iUnion.2 (hE.cover _ (chartQ_mem w))) hE.mono.directed_le
  refine ⟨max n m, le_iInf₂ fun t ht => ?_⟩
  by_contra hlt
  push Not at hlt
  apply ht
  show F.Yf (r (max n m)) t ω ∈ W (max n m)
  rw [F.Yf_eq_of_le hc ((le_max_right n m).trans (hrn _)) hlt.le]
  exact hE.mono (le_max_left n m) (hn ⟨F.X m t ω, Metric.mem_closedBall.2 (by
    rw [dist_zero_right]; exact (F.norm_X_lt hlt).le), rfl⟩)

/-- **The exits of the exhaustion exhaust the chart explosion time.** -/
theorem iSup_pexit_eq_zeta (hE : IsExh W (flatChamber q)) (hrn : ∀ n, n ≤ r n)
    (hball : ∀ n, W n ⊆ chartQ q '' Metric.ball 0 (r n)) (hc : F.IsConsAt ω) :
    ⨆ n, pexit (W n) (F.cpath (r n) ω) = F.zeta ω :=
  le_antisymm (iSup_le fun n => (F.pexit_cpath_le (hball n) ω).trans (F.e_le_zeta _ ω))
    (iSup_le fun m => by
      obtain ⟨n, hn⟩ := F.e_le_pexit hE hrn hc m
      exact hn.trans (le_iSup (fun n => pexit (W n) (F.cpath (r n) ω)) n))

theorem coe_sinf_stopSeq (hE : IsExh W (flatChamber q)) (hrn : ∀ n, n ≤ r n)
    (hball : ∀ n, W n ⊆ chartQ q '' Metric.ball 0 (r n)) (hc : F.IsConsAt ω) (t₀ : ℝ≥0) :
    ((sinf W t₀ (F.stopSeq W t₀ r ω) : ℝ≥0) : WithTop ℝ≥0) = min (F.zeta ω) t₀ := by
  rw [sinf, WithTop.coe_iSup _ (bddAbove_srho _)]
  have h : ∀ n, ((srho W t₀ (F.stopSeq W t₀ r ω) n : ℝ≥0) : WithTop ℝ≥0) =
      pexit (W n) (F.cpath (r n) ω) ⊓ t₀ := fun n => by
    rw [coe_srho]; exact min_pexit_pstop (hE.isOpen n) _
  simp_rw [h, ← F.iSup_pexit_eq_zeta hE hrn hball hc]
  exact (iSup_inf_eq _ _).symm

theorem sglue_stopSeq_eq_Z (hE : IsExh W (flatChamber q)) (hr : Monotone r)
    (hball : ∀ n, W n ⊆ chartQ q '' Metric.ball 0 (r n)) (hc : F.IsConsAt ω) {t₀ t : ℝ≥0}
    (ht : t < sinf W t₀ (F.stopSeq W t₀ r ω)) : sglue (F.stopSeq W t₀ r ω) t = F.Z t ω := by
  obtain ⟨n, hn⟩ := exists_lt_srho ht
  have hle' : (t : WithTop ℝ≥0) ≤ min (pexit (W n) (F.cpath (r n) ω)) t₀ := by
    have := (WithTop.coe_le_coe.2 hn.le).trans_eq (coe_srho (W := W) (t₀ := t₀) _ n)
    rwa [stopSeq, min_pexit_pstop (hE.isOpen n)] at this
  have hle : (t : WithTop ℝ≥0) ≤ pexit (W n) (F.cpath (r n) ω) := hle'.trans (min_le_left _ _)
  rw [(F.isNested_stopSeq hE.isOpen hE.mono hr hball hc).sglue_eq hE.isOpen hn.le,
    F.Z_eq hc (hle.trans (F.pexit_cpath_le (hball n) ω))]
  exact pstop_apply_of_le hle'

end B1R

/-!
## The boundary classification
-/

namespace B1R

variable {ξ : S → Fin ((q + 1) + (q + 1)) → ℝ}

/-- **The random-start form of the boundary classification for the family `B1R`.** -/
theorem ae_goodSeq (hD0 : 0 < D0) (hξ : Measurable ξ) (hξc : ∀ s, ξ s ∈ flatChamber (q + 1))
    (F : B1R D0 (q + 1) μ ξ) {n₀ : ℕ} {r : ℕ → ℕ} (hr : Monotone r)
    (hball : ∀ n, boxExh (q + 1) n₀ n ⊆ chartQ (q + 1) '' Metric.ball 0 (r n)) (t₀ : ℝ≥0) :
    ∀ᵐ x ∂PR μ (q + 1), ξ x.1 ∈ flatBox (q + 1) n₀ →
      F.stopSeq (boxExh (q + 1) n₀) t₀ r x ∈ goodSeq q (boxExh (q + 1) n₀) t₀ :=
  ae_goodSeq_of_randomStart hD0 (Z := fun n => F.cpath (r n)) (ξ := fun x => ξ x.1)
    (fun n => isMPSolutionOn_mono (F.isMPSolutionOn_Yf hD0 (r n)) (hball n))
    (fun _ x => F.Yf_zero hξc _ x) (measurable_fst_zero μ hξ) t₀
    (F.isStopSeq_stopSeq hD0 (isExh_boxExh _ _).isOpen (isExh_boxExh _ _).mono hr hball)

/-- **The boundary classification at level `q + 1` from a random start, pathwise at `ζ`.** -/
theorem ae_tendsto_corner (hD0 : 0 < D0) (hξ : Measurable ξ)
    (hξc : ∀ s, ξ s ∈ flatChamber (q + 1)) (F : B1R D0 (q + 1) μ ξ) :
    ∀ᵐ x ∂PR μ (q + 1), F.IsConsAt x ∧ ∀ ζ : ℝ≥0, F.zeta x = ζ →
      ∃ c, IsCorner q c ∧ Tendsto (fun t => F.Z t x) (𝓝[<] ζ) (𝓝 c) := by
  choose B hB using fun n₀ => exists_boxRad (q + 1) n₀
  set r : ℕ → ℕ → ℕ := fun n₀ n => max (majorant (B n₀) n) n
  have hr : ∀ n₀, Monotone (r n₀) := fun n₀ => (monotone_majorant _).max monotone_id
  have hrn : ∀ n₀ n, n ≤ r n₀ n := fun _ _ => le_max_right _ _
  have hball : ∀ n₀ n, boxExh (q + 1) n₀ n ⊆ chartQ (q + 1) '' Metric.ball 0 (r n₀ n) :=
    fun n₀ n => (hB n₀ n).trans (chartQ_ball_mono ((le_majorant _ n).trans (le_max_left _ _)))
  have h1 := ae_all_iff.2 fun n₀ => ae_all_iff.2 fun t₀ : ℕ =>
    F.ae_goodSeq hD0 hξ hξc (hr n₀) (hball n₀) (t₀ : ℝ≥0)
  filter_upwards [h1, F.ae_consistent hD0] with x hx hc
  refine ⟨hc, fun ζ hζ => ?_⟩
  obtain ⟨n₀, hn₀⟩ := (isExh_boxExh (q + 1) 0).cover _ (hξc x.1)
  rw [boxExh, zero_add] at hn₀
  obtain ⟨t₀, ht₀⟩ := exists_nat_gt ζ
  have hE := isExh_boxExh (q + 1) n₀
  set W := boxExh (q + 1) n₀
  have hs : sinf W t₀ (F.stopSeq W t₀ (r n₀) x) = ζ := by
    have := F.coe_sinf_stopSeq hE (hrn n₀) (hball n₀) hc (t₀ : ℝ≥0)
    rw [hζ, min_eq_left (WithTop.coe_le_coe.2 ht₀.le)] at this
    exact WithTop.coe_inj.1 this
  have hlt : sinf W t₀ (F.stopSeq W t₀ (r n₀) x) < t₀ := hs ▸ ht₀
  obtain ⟨hl, hcor⟩ := hx n₀ t₀ hn₀ hlt
  obtain ⟨c, hL⟩ := mem_llSet_iff.1 hl
  have hn := F.isNested_stopSeq (t₀ := (t₀ : ℝ≥0)) hE.isOpen hE.mono (hr n₀) (hball n₀) hc
  have h0 : (F.stopSeq W t₀ (r n₀) x 0).1 0 ∈ W 0 := by
    rw [F.stopSeq_zero hξc]; exact hn₀
  have hT := (hn.tendsto_sglue_iff hE.isOpen hE.mono (hn.srho_lt_sinf hE h0 hlt) c).2 hL
  refine ⟨c, hL.zstar_eq ▸ hcor, ?_⟩
  rw [← hs]
  refine hT.congr' (eventually_nhdsWithin_of_forall fun t ht => ?_)
  exact F.sglue_stopSeq_eq_Z hE (hr n₀) (hball n₀) hc ht

end B1R

end BlockBand.Transmission.Dual.G
