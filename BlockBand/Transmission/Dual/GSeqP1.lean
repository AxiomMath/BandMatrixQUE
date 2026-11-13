module

public import BlockBand.Transmission.Dual.GSeqInd
public import BlockBand.Transmission.Dual.ExistsP1

/-!
# The level-one corner limit on the sequence space: `GSeq D₀ 0`

Transfer of `SolFamily.ae_tendsto` (the corner limit for the `(u, v)`-chart family on `Ω₁`) to
every `B1Family D₀ 1`, through the sequence space.
* `isMPSolutionOn_Yf`: the flat paths of a `SolFamily` solve the flat dual problem in
  `toFlat '' ball 0 m` (`isMPSolutionOn_of_agree` with `SolFamily.isCSM_Yf`), so the `SolFamily`
  stop sequence is a dual stop sequence (`isStopSeq`, `isDualStopAt`).
* `stopSeq_mem_goodSeq` (pathwise decoding): on the corner-limit event, if `ρ_∞ < t₀` then
  the chart lifetime `ζ = sup e_m` is `≤ ρ_∞` (every chart compact lies in some box), and
  `S = x + y → 0` gives the left limit `0`, a corner.
* **`gSeq_zero`**: `GSeq D₀ 0`, by `map_eq_of_isMPSolutionOn` between the two stop sequences.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.Transmission.Dual
open BlockBand.Transmission.Dual.Exists (toFlat fromFlat lgt SolFamily Ω₁ P₁ 𝓖₁)
open BlockBand.SourceProcess.Stochastic.Semimartingale (stopTime)
open scoped NNReal ENNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {D0 : ℝ} {z : Fin 2 → ℝ}

theorem lgt_injective : Function.Injective lgt := fun a b h => by
  have h' : 1 + exp (-a) = 1 + exp (-b) := inv_injective h
  have := exp_injective (add_left_cancel h')
  linarith

theorem toFlat_injective : Function.Injective toFlat := fun a b h => by
  funext i
  fin_cases i
  · exact exp_injective (congrFun h 0)
  · exact lgt_injective (congrFun h 1)

theorem continuousOn_fromFlat : ContinuousOn fromFlat (flatChamber 1) := by
  refine continuousOn_pi.2 fun i => ?_
  fin_cases i
  · refine ContinuousOn.log (continuous_apply 0).continuousOn fun w hw => ?_
    exact (hw.2.2.1 0).ne'
  · refine ContinuousOn.log ((continuous_apply 1).continuousOn.div
      (continuous_const.sub (continuous_apply 1)).continuousOn fun w hw => ?_) fun w hw => ?_
    · exact (sub_pos.2 (hw.2.2.2 0).2).ne'
    · exact (div_pos (hw.2.2.2 0).1 (sub_pos.2 (hw.2.2.2 0).2)).ne'

theorem exists_toFlat_ball_superset {K : Set (Fin 2 → ℝ)} (hK : IsCompact K)
    (hKc : K ⊆ flatChamber 1) : ∃ n : ℕ, K ⊆ toFlat '' Metric.ball 0 n := by
  obtain ⟨R, hR⟩ := (hK.image_of_continuousOn (continuousOn_fromFlat.mono hKc)).isBounded.exists_norm_le
  obtain ⟨n, hn⟩ := exists_nat_gt R
  refine ⟨n, fun w hw => ⟨fromFlat w, ?_, ?_⟩⟩
  · rw [Metric.mem_ball, dist_zero_right]; exact (hR _ ⟨w, hw, rfl⟩).trans_lt hn
  · have h := hKc hw
    exact Exists.toFlat_fromFlat (h.2.2.1 0) (h.2.2.2 0).1 (h.2.2.2 0).2

namespace SolFamilyG

variable (F : SolFamily D0 z)

theorem exitTimeFrom_le_e {m : ℕ} {W : Set (Fin 2 → ℝ)} (hW : W ⊆ toFlat '' Metric.ball 0 m)
    (ω : Ω₁) : exitTimeFrom W (F.Yf m) ω ≤ F.e m ω := by
  refine le_iInf₂ fun t ht => iInf₂_le t fun hmem => ?_
  obtain ⟨w, hw, he⟩ := hW hmem
  have := toFlat_injective he
  rw [this, Metric.mem_ball, dist_zero_right] at hw
  exact absurd ht (not_le.2 hw)

theorem isMPSolutionOn_Yf (hD0 : 0 < D0) (m : ℕ) :
    IsMPSolutionOn P₁ 𝓖₁ (flatDrift D0 1) (flatDiff D0 1) (toFlat '' Metric.ball 0 m) (F.Yf m) := by
  have hsub : toFlat '' Metric.ball 0 m ⊆ flatChamber 1 := by
    rintro _ ⟨w, -, rfl⟩; exact Exists.toFlat_mem w
  refine isMPSolutionOn_of_agree ((continuousOn_flatDrift D0).mono hsub)
    (contDiff_flatDiff D0).continuous.continuousOn (F.isCSM_Yf hD0 m) fun W hW ω s hs => ?_
  have hle : (s : WithTop ℝ≥0) ≤ F.e m ω :=
    hs.trans (exitTimeFrom_le_e F (subset_closure.trans hW.2.2) ω)
  simp only [switchOff, SolFamily.e] at hle ⊢
  exact ⟨ite_eq_left hle, ite_eq_left hle⟩

/-- The `m`-th flat path as a continuous path. -/
def cpath (m : ℕ) (ω : Ω₁) : CPath (1 + 1) := ⟨fun t => F.Yf m t ω, F.continuous_Yf m ω⟩

theorem measurable_cpath (m : ℕ) : Measurable (cpath F m) :=
  Measurable.subtype_mk (measurable_pi_iff.2 fun t => (F.measurable_Yf m t).mono (𝓖₁.le t) le_rfl)

/-- The stop sequence with radii `r`. -/
def stopSeq (W : ℕ → Set (Fin (1 + 1) → ℝ)) (t₀ : ℝ≥0) (r : ℕ → ℕ) (ω : Ω₁) :
    ℕ → CPath (1 + 1) := fun n => pstop (W n) t₀ (cpath F (r n) ω)

variable {W : ℕ → Set (Fin (1 + 1) → ℝ)} {t₀ : ℝ≥0} {r : ℕ → ℕ}

theorem measurable_stopSeq (hW : ∀ n, IsOpen (W n)) (r : ℕ → ℕ) :
    Measurable (stopSeq F W t₀ r) :=
  measurable_pi_iff.2 fun n => (measurable_pstop (hW n) t₀).comp (measurable_cpath F _)

theorem isNested_stopSeq (hW : ∀ n, IsOpen (W n)) (hmono : Monotone W) (hr : Monotone r)
    (hball : ∀ n, W n ⊆ toFlat '' Metric.ball 0 (r n)) {ω : Ω₁} (hc : F.IsCons ω) :
    IsNested W t₀ (stopSeq F W t₀ r ω) := by
  intro k n hkn
  show pstop (W k) t₀ (cpath F (r k) ω) = pstop (W k) t₀ (pstop (W n) t₀ (cpath F (r n) ω))
  rw [pstop_pstop (hW k) (hmono hkn)]
  refine (pstop_congr (hW k) t₀ fun u hu => ?_).symm
  exact (F.Yf_eq_of_cons hc (hr hkn)
    ((hu.trans (min_le_left _ _)).trans (exitTimeFrom_le_e F (hball k) ω))).symm

theorem isStopSeq (hD0 : 0 < D0) (hW : ∀ n, IsOpen (W n)) (hmono : Monotone W)
    (hr : Monotone r) (hball : ∀ n, W n ⊆ toFlat '' Metric.ball 0 (r n)) :
    IsStopSeq P₁ W t₀ (stopSeq F W t₀ r) := by
  intro k n hkn
  filter_upwards [F.ae_consistent hD0] with ω hc
  exact isNested_stopSeq F hW hmono hr hball hc k n hkn

theorem isDualStopAt (hD0 : 0 < D0) (hz : z ∈ flatChamber 1)
    (hball : ∀ n, W n ⊆ toFlat '' Metric.ball 0 (r n)) (n : ℕ) :
    IsDualStopAt (q := 1) P₁ D0 W t₀ z (stopSeq F W t₀ r) n := by
  refine ⟨𝓖₁, F.Yf (r n), isMPSolutionOn_mono (isMPSolutionOn_Yf F hD0 (r n)) (hball n), ?_,
    fun _ => rfl⟩
  have e : F.Yf (r n) 0 = fun _ => z := funext (F.Yf_zero hz (r n))
  rw [e, Measure.map_const, measure_univ, one_smul]

theorem isCorner_zero : IsCorner 0 (0 : Fin ((0 + 1) + (0 + 1)) → ℝ) :=
  ⟨rfl, rfl, ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩⟩

/-- **Pathwise decoding of the corner limit** for the `SolFamily` stop sequence. -/
theorem stopSeq_mem_goodSeq (hE : IsExh W (flatChamber 1)) (hr : Monotone r)
    (hrn : ∀ n, n ≤ r n) (hball : ∀ n, W n ⊆ toFlat '' Metric.ball 0 (r n)) {ω : Ω₁}
    (hc : F.IsCons ω) (hv : F.IsConv ω) : stopSeq F W t₀ r ω ∈ goodSeq 0 W t₀ := by
  intro hlt
  set ŵ := stopSeq F W t₀ r ω
  have hn : IsNested W t₀ ŵ := isNested_stopSeq F hE.isOpen hE.mono hr hball hc
  have hpe : ∀ n, (srho W t₀ ŵ n : WithTop ℝ≥0) = min (pexit (W n) (cpath F (r n) ω)) t₀ :=
    fun n => by rw [coe_srho]; exact min_pexit_pstop (hE.isOpen n) _
  -- the chart lifetime is at most `ρ_∞`
  have hζ : F.zeta ω ≤ (sinf W t₀ ŵ : WithTop ℝ≥0) := by
    refine iSup_le fun m => ?_
    obtain ⟨n₁, hn₁⟩ := (Exists.isCompact_Kset z m).elim_directed_cover W hE.isOpen
      (fun w hw => mem_iUnion.2 (hE.cover w (Exists.Kset_subset z m hw))) hE.mono.directed_le
    set n := max n₁ m
    have hle : F.e m ω ≤ pexit (W n) (cpath F (r n) ω) := by
      refine le_iInf₂ fun t ht => ?_
      by_contra hlt'
      refine ht ?_
      show F.Yf (r n) t ω ∈ W n
      rw [← F.Yf_eq_of_cons hc ((le_max_right n₁ m).trans (hrn n)) (not_le.1 hlt').le]
      exact hE.mono (le_max_left n₁ m) (hn₁ (F.Yf_mem_K m t ω))
    have h1 : min (F.e m ω) t₀ ≤ (sinf W t₀ ŵ : WithTop ℝ≥0) :=
      (min_le_min hle le_rfl).trans ((hpe n).symm.le.trans
        (WithTop.coe_le_coe.2 (srho_le_sinf ŵ n)))
    rcases le_total (F.e m ω) t₀ with h | h
    · rwa [min_eq_left h] at h1
    · rw [min_eq_right h] at h1
      exact absurd (WithTop.coe_le_coe.1 h1) (not_le.2 hlt)
  have hζt : F.zeta ω < ⊤ := hζ.trans_lt (WithTop.coe_lt_top _)
  have hL : LL W t₀ ŵ 0 := by
    intro ε hε
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    obtain ⟨s₀, hs₀, hS⟩ := hv hζt k
    obtain ⟨N, hN⟩ := exists_lt_srho (WithTop.coe_lt_coe.1 (hs₀.trans_le hζ))
    refine ⟨N, fun n hnN t ht => ?_⟩
    set u := stopTime (pexit (W n) (cpath F (r n) ω)) (min t t₀)
    have hu : (u : WithTop ℝ≥0) = min (t : WithTop ℝ≥0) (srho W t₀ ŵ n) := by
      rw [coe_stopTime_min, hpe]
    have hsu : s₀ ≤ u := by
      rw [← WithTop.coe_le_coe, hu]
      exact le_min (WithTop.coe_le_coe.2 (hN.le.trans ht)) (WithTop.coe_le_coe.2
        (hN.le.trans (hn.srho_mono hE.isOpen hE.mono hnN)))
    have hue : (u : WithTop ℝ≥0) ≤ F.e (r n) ω := by
      rw [hu]
      refine (min_le_right _ _).trans ?_
      rw [hpe]
      exact (min_le_left _ _).trans (exitTimeFrom_le_e F (hball n) ω)
    have hSp := hS (r n) u hsu hue
    have hmem := F.Yf_mem (r n) u ω
    show dist (F.Yf (r n) u ω) 0 ≤ ε
    rw [dist_zero_right]
    have h0 : 0 < F.Yf (r n) u ω 0 := hmem.2.2.1 0
    have h1 : 0 < F.Yf (r n) u ω 1 := (hmem.2.2.2 0).1
    have hsum : F.Yf (r n) u ω 0 + F.Yf (r n) u ω 1 < 1 / ((k : ℝ) + 1) := hSp
    refine (pi_norm_le_iff_of_nonneg hε.le).2 (Fin.forall_fin_two.2 ⟨?_, ?_⟩)
    · rw [Real.norm_eq_abs, abs_of_pos h0]; linarith
    · rw [Real.norm_eq_abs, abs_of_pos h1]; linarith
  exact ⟨mem_llSet_iff.2 ⟨0, hL⟩, by rw [hL.zstar_eq]; exact isCorner_zero⟩

end SolFamilyG

/-- **The level-one corner limit on the sequence space** for every `B1Family D₀ 1`. -/
theorem gSeq_zero (hD0 : 0 < D0) : GSeq D0 0 := by
  intro z n₀ hz F r hr hball t₀
  have hE := isExh_boxExh 1 n₀
  have hz' : z ∈ flatChamber 1 := (hE.dom 0).2.2 (subset_closure hz)
  have F' : SolFamily D0 z := (Exists.nonempty_solFamily hD0 z).some
  choose B hB using fun n => exists_toFlat_ball_superset ((hE.dom n).2.1) ((hE.dom n).2.2)
  set r' := majorant fun n => max n (B n)
  have hr' := monotone_majorant fun n => max n (B n)
  have le_r' : ∀ n, max n (B n) ≤ r' n := le_majorant _
  have hball' : ∀ n, boxExh 1 n₀ n ⊆ toFlat '' Metric.ball 0 (r' n) := fun n =>
    subset_closure.trans ((hB n).trans (image_mono (Metric.ball_subset_ball
      (Nat.cast_le.2 ((le_max_right _ _).trans (le_r' n))))))
  have hS := measurableSet_goodSeq (q := 0) (t₀ := t₀) hE.isOpen
  have hsol : (P₁).map (SolFamilyG.stopSeq F' (boxExh 1 n₀) t₀ r') (goodSeq 0 (boxExh 1 n₀) t₀)ᶜ
      = 0 := by
    rw [← ae_mem_iff_map (SolFamilyG.measurable_stopSeq F' hE.isOpen r') hS]
    filter_upwards [F'.ae_tendsto hD0 hz'] with ω hω
    exact SolFamilyG.stopSeq_mem_goodSeq F' hE hr' (fun n => (le_max_left _ _).trans (le_r' n))
      hball' hω.1 hω.2
  rw [ae_mem_iff_map (F.measurable_stopSeq hE.isOpen r) hS]
  rw [← map_eq_of_isMPSolutionOn hD0 hE.dom (SolFamilyG.measurable_stopSeq F' hE.isOpen r')
    (F.measurable_stopSeq hE.isOpen r) (SolFamilyG.isStopSeq F' hD0 hE.isOpen hE.mono hr' hball')
    (F.isStopSeq_stopSeq hD0 hE.isOpen hE.mono hr hball)
    (SolFamilyG.isDualStopAt F' hD0 hz' hball') (F.isDualStopAt hD0 hz' hball)]
  exact hsol

/-- **The boundary classification at every level** on the sequence space, from the
atomlessness of the level-one lifetime in that form. -/
theorem gSeq_all_of_A3 (hD0 : 0 < D0) (hA3 : A3Seq D0) : ∀ q, GSeq D0 q :=
  gSeq_all hD0 (gSeq_zero hD0) hA3

end BlockBand.Transmission.Dual.G
