module

public import BlockBand.Transmission.LawFinite.CoreBond

/-!
# The finite core at length one, with absorption

Hypothesis `PassiveBoundsStatement` (only its `moments` clause, through `fresh_core_step`).

**`core_first`**: `b, κI, κ, δ` first; then `a > 0`, `W₀`; for `W ≥ W₀`, `E ∈ bulkInterval κI`:
`P(q₁ < aW) ≤ δ`. Proof: the past at length `0` is the far bond `B₀`; on
`G = {‖B₀‖ ≤ β₀, #{s_i(B₀)² < c₀} ≤ W/2}` the first input `X₀ = z⁻¹B₀B₀* - iε₁` has
`‖X₀‖ ≤ ξ` and `q(X₀) ≥ Re Tr Y/‖z - X₀‖² ≥ c₀W/(18Li(3+ξ)²)` (`trace_passiveY_le`,
`trace_gram_ge`); `fresh_core_step` handles the fresh layer and `step_prob_le` the Fubini step.
`P(Gᶜ)`: Markov on `ginibre_moment` (`ginibre_norm_tail`) and `smallFraction_prob_le`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawFinite

open Matrix MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open scoped Matrix.Norms.L2Operator ComplexOrder ENNReal

variable {W : ℕ}

/-- Markov for the Ginibre operator norm: `P(‖B‖ > β) ≤ C/β`, uniformly in `W ≥ 1`. -/
theorem ginibre_norm_tail {b : ℝ} (hb : 0 < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : ℕ, 1 ≤ W → ∀ β : ℝ, 0 < β →
      ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W)) {B | β < ‖B‖} ≤
        ENNReal.ofReal (C / β) := by
  obtain ⟨C, hC⟩ := PassiveLayer.ginibre_moment hb (p := 1) le_rfl
  refine ⟨max C 0, le_max_right _ _, fun W hW β hβ => ?_⟩
  set μ := ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))
  have hsub : {B : Matrix (Fin W) (Fin W) ℂ | β < ‖B‖} ⊆ {B | ENNReal.ofReal β ≤ ‖B‖ₑ} :=
    fun B hB => by
      change ENNReal.ofReal β ≤ ‖B‖ₑ
      rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (le_of_lt hB)
  refine (measure_mono hsub).trans ((meas_ge_le_lintegral_div measurable_enorm.aemeasurable
    (by simpa using hβ) ENNReal.ofReal_ne_top).trans ?_)
  have h1 := hC W hW
  simp only [ENNReal.rpow_one] at h1
  rw [ENNReal.ofReal_div_of_pos hβ]
  exact ENNReal.div_le_div_right (h1.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))) _

/-- A bond event has its Ginibre probability. -/
theorem growth_bond_event (b : ℝ) (k : ℕ) {S : Set (Matrix (Fin W) (Fin W) ℂ)}
    (hS : MeasurableSet S) :
    growthPathLaw W b {ω | ω.2 k ∈ S} = ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W)) S := by
  have hm : Measurable fun ω : GrowthPath W => ω.2 k := (measurable_pi_apply k).comp measurable_snd
  rw [← growthPathLaw_map_bond W b k, Measure.map_apply hm hS]; rfl

/-- **The finite core at length one** (with absorption): `b, κI, κ, δ`
first; then `a > 0`, `W₀`; for `W ≥ W₀` and `E ∈ bulkInterval κI`, `P(q₁ < aW) ≤ δ`.
Hypothesis: `PassiveBoundsStatement` (`moments`). -/
theorem core_first (hA : PassiveLayer.PassiveBoundsStatement) {b κI : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hκI : 0 < κI) {κ : ℝ → ℝ} (hκ : IsAbsorptionProfile κ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ a : ℝ, 0 < a ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI,
      growthPathLaw W b {ω | passiveMass b E (pathNearSchur b E κ W 1 ω) < a * W} ≤
        ENNReal.ofReal δ := by
  obtain ⟨-, hκ0, K, hK⟩ := hκ
  set Kκ := max K 0
  have hKκ : ∀ s, κ s ≤ Kκ := fun s => (hK s).trans (le_max_left _ _)
  obtain ⟨CB, hCB0, hCB⟩ := ginibre_norm_tail hb0
  obtain ⟨Cs, hCs⟩ := smallFraction_prob_le ginibreSmallSingularFraction_holds hb0 hb
  set Cs' := max Cs 0
  set β₀ := 4 * CB / δ + 1
  have hβ₀ : 0 < β₀ := by positivity
  set t := 8 * Cs' / δ + 1
  have ht : 0 < t := by positivity
  set c₀ := Real.exp (-t)
  have hc₀ : 0 < c₀ := Real.exp_pos _
  have hc₀1 : c₀ < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hlog : Real.log c₀⁻¹ = t := by rw [← Real.exp_neg, neg_neg, Real.log_exp]
  have hηL : 0 < etaLow b κI := etaLow_pos (by linarith) hκI
  set Li := (etaLow b κI)⁻¹
  have hLi0 : 0 < Li := inv_pos.mpr hηL
  set ξ := β₀ ^ 2 * Li + Kκ
  have hξ : 0 ≤ ξ := by positivity
  set a₀ := c₀ / (18 * Li * (3 + ξ) ^ 2)
  have ha₀ : 0 < a₀ := by positivity
  obtain ⟨a₁, ha₁, W₁, hfr⟩ := fresh_core_step hA hb0 hb hκI (half_pos hδ) ha₀ hξ
  refine ⟨a₁, ha₁, max W₁ 1, fun W hW E hE => ?_⟩
  have hW₁ : W₁ ≤ W := le_of_max_le_left hW
  have hW1 : 1 ≤ W := le_of_max_le_right hW
  have h1 : -2 < E := by linarith [hE.1]
  have h2 : E < 2 := by linarith [hE.2]
  have hη := PassiveCovariance.etaZ_pos b E (by linarith) h1 h2
  have hzD : boundaryZ b E ∈ PassiveLayer.paramDisk b E := Metric.mem_closedBall_self (by positivity)
  have hz3 := (PassiveLayer.disk_bounds hb0 hb hκI hE hzD).2.1
  have hLi : (etaZ b E)⁻¹ ≤ Li := inv_anti₀ hηL (etaLow_le (by linarith) hκI hE)
  -- the good past
  set G : Set (PastSample W 0) := {p | ‖p.2 0‖ ≤ β₀ ∧
    (smallSingularCount c₀ (p.2 0) : ℝ) ≤ 1 / 2 * W}
  have hB : Measurable fun p : PastSample W 0 => p.2 0 := (measurable_pi_apply 0).comp measurable_snd
  have hcnt : Measurable fun B : Matrix (Fin W) (Fin W) ℂ => (smallSingularCount c₀ B : ℝ) :=
    measurable_from_nat.comp (measurable_smallSingularCount c₀)
  have hGm : MeasurableSet G :=
    (measurableSet_le (continuous_norm.measurable.comp hB) measurable_const).inter
      (measurableSet_le (hcnt.comp hB) measurable_const)
  have hgood : ∀ p ∈ G, freshLaw W b {f | passiveMass b E (freshSchur E (bondX b E κ W p) f) <
      a₁ * W} ≤ ENNReal.ofReal (δ / 2) := by
    intro p ⟨hpn, hpm⟩
    obtain ⟨hYp, hTr⟩ := passiveY_bondX (b := b) (E := E) (κ := κ) (W := W) (by linarith) h1 h2 hκ0 p
    have hXn : ‖bondX b E κ W p‖ ≤ ξ := by
      refine (norm_bondX_le (b := b) (E := E) (by linarith) h1 h2 hκ0 hKκ hLi hW1 p).trans ?_
      have : ‖p.2 0‖ ^ 2 ≤ β₀ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hpn 2
      simp only [ξ]; nlinarith
    refine hfr W hW₁ E hE _ hYp hXn ?_
    -- `a₀W ≤ q`
    have hK3 : ‖boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - bondX b E κ W p‖ ≤ 3 + ξ := by
      refine (norm_sub_le _ _).trans (add_le_add ?_ hXn)
      rw [norm_smul]; exact mul_le_of_le_one_right (norm_nonneg _) PassiveLayer.norm_one_le' |>.trans hz3
    have hq := trace_passiveY_le hb0 hb h1 h2 hYp
    have hq0 := PassiveCovariance.passiveMass_nonneg b E hYp
    have hgr := trace_gram_ge (p.2 0) c₀
    have hns : Complex.normSq (boundaryZ b E) ≤ 9 := by
      rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg (boundaryZ b E)]
    have hns0 : 0 < Complex.normSq (boundaryZ b E) :=
      Complex.normSq_pos.mpr (boundaryZ_ne_zero (by linarith) h1 h2)
    have hηLi : 1 ≤ etaZ b E * Li := by
      have := mul_le_mul_of_nonneg_left hLi hη.le
      rwa [mul_inv_cancel₀ hη.ne'] at this
    have hc1 : 1 / (9 * Li) ≤ etaZ b E / Complex.normSq (boundaryZ b E) := by
      rw [div_le_div_iff₀ (by positivity) hns0]; nlinarith
    have hgr' : c₀ * (1 / 2 * W) ≤ (p.2 0 * (p.2 0)ᴴ).trace.re := by
      refine le_trans ?_ hgr
      exact mul_le_mul_of_nonneg_left (by linarith) hc₀.le
    have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg _
    have hY1 : c₀ * W / (18 * Li) ≤ (passiveY (bondX b E κ W p)).trace.re := by
      refine le_trans ?_ hTr
      have hx : 0 ≤ c₀ * (1 / 2 * W) := by positivity
      calc c₀ * W / (18 * Li) = 1 / (9 * Li) * (c₀ * (1 / 2 * W)) := by field_simp; ring
        _ ≤ _ := mul_le_mul hc1 hgr' hx (by positivity)
    have hK2 : ‖boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - bondX b E κ W p‖ ^ 2 ≤
        (3 + ξ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hK3 2
    have : c₀ * W / (18 * Li) ≤ (3 + ξ) ^ 2 * passiveMass b E (bondX b E κ W p) :=
      hY1.trans (hq.trans (mul_le_mul_of_nonneg_right hK2 hq0))
    have e : a₀ * W = c₀ * W / (18 * Li) / (3 + ξ) ^ 2 := by simp only [a₀]; field_simp
    rw [e, div_le_iff₀ (by positivity)]; linarith
  have hstep := step_prob_le (b := b) (E := E) κ 0 (measurable_bondX b E κ)
    (ae_pathNearSchur_one_bond hb h1 h2 hW1 hκ0) hGm hgood
  refine hstep.trans ?_
  -- the bad past
  have hbad : growthPathLaw W b (pastCoords W 0 ⁻¹' Gᶜ) ≤
      ENNReal.ofReal (δ / 4) + ENNReal.ofReal (δ / 4) := by
    have hsub : pastCoords W 0 ⁻¹' Gᶜ ⊆ {ω | ω.2 0 ∈ {B : Matrix (Fin W) (Fin W) ℂ | β₀ < ‖B‖}} ∪
        {ω | ω.2 0 ∈ {B : Matrix (Fin W) (Fin W) ℂ | 1 / 2 * W < (smallSingularCount c₀ B : ℝ)}} := by
      intro ω hω
      simp only [Set.mem_preimage, Set.mem_compl_iff, G, Set.mem_ofPred_eq, not_and_or,
        not_le] at hω
      exact hω
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add ?_ ?_))
    · rw [growth_bond_event b 0 (measurableSet_lt measurable_const continuous_norm.measurable)]
      exact (hCB W hW1 β₀ hβ₀).trans (ENNReal.ofReal_le_ofReal (quarter_bound hCB0 hδ))
    · rw [growth_bond_event b 0 (measurableSet_lt measurable_const hcnt)]
      refine (hCs W (by omega) c₀ (1 / 2) hc₀ hc₀1 (by norm_num)).trans
        (ENNReal.ofReal_le_ofReal ?_)
      rw [hlog, div_le_iff₀ (by positivity)]
      have : Cs ≤ Cs' := le_max_left _ _
      have hC0 : 0 ≤ Cs' := le_max_right _ _
      have : δ / 4 * (1 / 2 * t) = Cs' + δ / 8 := by simp only [t]; field_simp; ring
      linarith
  calc growthPathLaw W b (pastCoords W 0 ⁻¹' Gᶜ) + ENNReal.ofReal (δ / 2)
      ≤ ENNReal.ofReal (δ / 4) + ENNReal.ofReal (δ / 4) + ENNReal.ofReal (δ / 2) := by gcongr
    _ = ENNReal.ofReal δ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

end BlockBand.Transmission.LawFinite
