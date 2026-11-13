module

public import BlockBand.Transmission.DualBoundary.UniqueCouple
public import BlockBand.Transmission.DualFeller.F1

/-!
# Uniqueness at a boundary start: start continuity on the coupled lift

Uses start continuity of the lift (`LiftStartContinuity`) through its proof at a fixed
`(T, R, η, δ)`.
* `abs_lift_sub_le`: on `LP μ` (`μ` on `ℝ² × ℝ²`), for two lifted families from the coupled
  starts and an `L`-Lipschitz `[0,1]`-valued test `g` of the restriction to a finite `I`:
  `|E g(Z̄¹|_I) − E g(Z̄²|_I)| ≤ Lη + 2η`, given the bad event of start continuity (with
  `T = max I`) and `{‖ξ¹‖ > R}` have mass `≤ η` each.
* **`abs_cond_sub_le_at`**: for two boundary realizations from the same start, at a fixed
  `s > 0` with `P_i(postSet) ≥ 1/2`, the conditional post-`s` tests differ by `≤ Lη + 2η`,
  provided `σ(Z̄^i_s)` is within `δ/2` of `σ₀` up to mass `δ/4` (`i = 1, 2`) and within `1` up
  to mass `η/2` (`i = 1`), where `δ` is the closeness of start continuity for
  `(max I, ‖σ₀‖ + 1, η)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualBoundary

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionUniform
open BlockBand.Transmission.Dual BlockBand.Transmission.DualLift BlockBand.Transmission.DualFeller
open scoped NNReal ENNReal

theorem two_mul_ofReal_add {a : ℝ} (ha : 0 ≤ a) :
    2 * ENNReal.ofReal a + 2 * ENNReal.ofReal a = ENNReal.ofReal (4 * a) := by
  have e : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  rw [e, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  ring_nf

theorem two_mul_ofReal_half (a : ℝ) :
    2 * ENNReal.ofReal (a / 2) = ENNReal.ofReal a := by
  have e : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  rw [e, ← ENNReal.ofReal_mul (by norm_num)]
  ring_nf

/-- **The start-continuity estimate for a Lipschitz test of the restricted lift paths.** -/
theorem abs_lift_sub_le {D0 : ℝ} (hD0 : 0 < D0) {μ : Measure CS} [IsProbabilityMeasure μ]
    (F₁ : DualLift.LiftFamily μ D0 cStart₁) (F₂ : DualLift.LiftFamily μ D0 cStart₂)
    (I : Finset ℝ≥0) {g : (I → Fin 2 → ℝ) → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g)
    (h01 : ∀ a, 0 ≤ g a ∧ g a ≤ 1) {R η : ℝ} (hη : 0 < η)
    (hF1 : LP μ {ω | ‖cStart₁ ω‖ ≤ R ∧ ∃ t : ℝ≥0, t ≤ I.sup id ∧
      η ≤ ‖liftZbar F₁ t ω - liftZbar F₂ t ω‖} ≤ ENNReal.ofReal η)
    (hR : LP μ {ω | R < ‖cStart₁ ω‖} ≤ ENNReal.ofReal η) :
    |∫ ω, g (I.restrict (fun u => liftZbar F₁ u ω)) ∂LP μ -
        ∫ ω, g (I.restrict (fun u => liftZbar F₂ u ω)) ∂LP μ| ≤ L * η + 2 * η := by
  set G₁ : LΩ CS → ℝ := fun ω => g (I.restrict (fun u => liftZbar F₁ u ω))
  set G₂ : LΩ CS → ℝ := fun ω => g (I.restrict (fun u => liftZbar F₂ u ω))
  have hgm : Measurable g := hg.continuous.measurable
  have hm₁ : Measurable G₁ := hgm.comp ((Finset.measurable_restrict I).comp
    (measurable_liftZbarPath F₁ hD0 (isLiftStart_cStart₁ μ)))
  have hm₂ : Measurable G₂ := hgm.comp ((Finset.measurable_restrict I).comp
    (measurable_liftZbarPath F₂ hD0 (isLiftStart_cStart₂ μ)))
  have hb : ∀ (G : LΩ CS → ℝ), Measurable G → (∀ ω, 0 ≤ G ω ∧ G ω ≤ 1) → Integrable G (LP μ) :=
    fun G hG h => Integrable.of_bound hG.aestronglyMeasurable 1 (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [h ω])
  have hi₁ := hb G₁ hm₁ fun ω => h01 _
  have hi₂ := hb G₂ hm₂ fun ω => h01 _
  set B := toMeasurable (LP μ) ({ω | ‖cStart₁ ω‖ ≤ R ∧ ∃ t : ℝ≥0, t ≤ I.sup id ∧
      η ≤ ‖liftZbar F₁ t ω - liftZbar F₂ t ω‖} ∪ {ω | R < ‖cStart₁ ω‖}) with hB
  have hBm : MeasurableSet B := measurableSet_toMeasurable _ _
  have hpt : ∀ ω, |G₁ ω - G₂ ω| ≤ L * η + B.indicator 1 ω := fun ω => by
    have hLη : 0 ≤ (L : ℝ) * η := mul_nonneg L.2 hη.le
    by_cases hω : ω ∈ B
    · rw [indicator_of_mem hω, Pi.one_apply]
      have := h01 (I.restrict (fun u => liftZbar F₁ u ω))
      have := h01 (I.restrict (fun u => liftZbar F₂ u ω))
      rw [abs_le]; constructor <;> linarith
    · rw [indicator_of_notMem hω, add_zero]
      have hω' : ω ∉ {ω | ‖cStart₁ ω‖ ≤ R ∧ ∃ t : ℝ≥0, t ≤ I.sup id ∧
          η ≤ ‖liftZbar F₁ t ω - liftZbar F₂ t ω‖} ∪ {ω | R < ‖cStart₁ ω‖} :=
        fun h => hω (subset_toMeasurable _ _ h)
      simp only [mem_union, mem_ofPred_eq, not_or, not_and, not_exists, not_lt] at hω'
      obtain ⟨h1, h2⟩ := hω'
      have hd : dist (I.restrict (fun u => liftZbar F₁ u ω))
          (I.restrict (fun u => liftZbar F₂ u ω)) ≤ η := by
        refine (dist_pi_le_iff hη.le).2 fun b => ?_
        have hbT : (b : ℝ≥0) ≤ I.sup id := Finset.le_sup (f := id) b.2
        have := h1 h2 b hbT
        rw [dist_eq_norm]
        simp only [Finset.restrict]
        exact (not_le.1 this).le
      calc |G₁ ω - G₂ ω| = dist (G₁ ω) (G₂ ω) := (Real.dist_eq _ _).symm
        _ ≤ L * dist (I.restrict (fun u => liftZbar F₁ u ω))
            (I.restrict (fun u => liftZbar F₂ u ω)) := hg.dist_le_mul _ _
        _ ≤ L * η := mul_le_mul_of_nonneg_left hd L.2
  have hBle : (LP μ).real B ≤ 2 * η := by
    have : LP μ B ≤ ENNReal.ofReal (2 * η) := by
      rw [hB, measure_toMeasurable]
      calc _ ≤ _ := measure_union_le _ _
        _ ≤ ENNReal.ofReal η + ENNReal.ofReal η := add_le_add hF1 hR
        _ = ENNReal.ofReal (2 * η) := by
          rw [← ENNReal.ofReal_add hη.le hη.le]; ring_nf
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) this
  rw [← integral_sub hi₁ hi₂]
  calc |∫ ω, (G₁ ω - G₂ ω) ∂LP μ| ≤ ∫ ω, |G₁ ω - G₂ ω| ∂LP μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, ((L : ℝ) * η + B.indicator 1 ω) ∂LP μ := by
        refine integral_mono (hi₁.sub hi₂).abs ((integrable_const _).add
          ((integrable_const 1).indicator hBm)) hpt
    _ = L * η + (LP μ).real B := by
        rw [integral_add (integrable_const _) ((integrable_const 1).indicator hBm),
          integral_indicator_one hBm]
        simp
    _ ≤ L * η + 2 * η := by linarith

/-- **The conditional post-`s` tests of two realizations are close** (start continuity at one
`s`). -/
theorem abs_cond_sub_le_at {D0 : ℝ} (hD0 : 0 < D0) {x y : ℝ}
    {Ω₁ : Type} [MeasurableSpace Ω₁] {P₁ : Measure Ω₁}
    {𝓖₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₁)}
    {N₁ : ℝ≥0 → Ω₁ → ℕ} {X₁ Y₁ : ℝ≥0 → Ω₁ → ℕ → ℝ}
    {Ω₂ : Type} [MeasurableSpace Ω₂] {P₂ : Measure Ω₂}
    {𝓖₂ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₂)}
    {N₂ : ℝ≥0 → Ω₂ → ℕ} {X₂ Y₂ : ℝ≥0 → Ω₂ → ℕ → ℝ}
    (h₁ : IsBoundaryDualProcess P₁ 𝓖₁ D0 ![x] ![y] N₁ X₁ Y₁)
    (h₂ : IsBoundaryDualProcess P₂ 𝓖₂ D0 ![x] ![y] N₂ X₂ Y₂) {s : ℝ≥0} (hs : 0 < s)
    (hA₁ : 2⁻¹ ≤ P₁ (postSet P₁ N₁ X₁ Y₁ s)) (hA₂ : 2⁻¹ ≤ P₂ (postSet P₂ N₂ X₂ Y₂ s))
    (I : Finset ℝ≥0) {g : (I → Fin 2 → ℝ) → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g)
    (h01 : ∀ a, 0 ≤ g a ∧ g a ≤ 1) {σ₀ : Fin 6 → ℝ} {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (hF : ∀ (S : Type) [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
      (ξ ξ' : LΩ S → Fin 6 → ℝ), IsLiftStart μ ξ → IsLiftStart μ ξ' →
      ∀ (F : DualLift.LiftFamily μ D0 ξ) (F' : DualLift.LiftFamily μ D0 ξ'),
      LP μ {ω | δ ≤ ‖ξ ω - ξ' ω‖} ≤ ENNReal.ofReal δ →
      LP μ {ω | ‖ξ ω‖ ≤ ‖σ₀‖ + 1 ∧ ∃ t : ℝ≥0, t ≤ I.sup id ∧
        η ≤ ‖liftZbar F t ω - liftZbar F' t ω‖} ≤ ENNReal.ofReal η)
    (hK₁ : P₁ {ω | δ / 2 ≤ dist (liftSecPt (zbarTr N₁ X₁ Y₁ ω s)) σ₀} ≤ ENNReal.ofReal (δ / 4))
    (hK₂ : P₂ {ω | δ / 2 ≤ dist (liftSecPt (zbarTr N₂ X₂ Y₂ ω s)) σ₀} ≤ ENNReal.ofReal (δ / 4))
    (hR : P₁ {ω | 1 ≤ dist (liftSecPt (zbarTr N₁ X₁ Y₁ ω s)) σ₀} ≤ ENNReal.ofReal (η / 2)) :
    |∫ ω, g (I.restrict (shiftZ N₁ X₁ Y₁ s ω)) ∂P₁[|postSet P₁ N₁ X₁ Y₁ s] -
        ∫ ω, g (I.restrict (shiftZ N₂ X₂ Y₂ s ω)) ∂P₂[|postSet P₂ N₂ X₂ Y₂ s]| ≤
      L * η + 2 * η := by
  have := h₁.prob
  have := h₂.prob
  have hA₁0 : P₁ (postSet P₁ N₁ X₁ Y₁ s) ≠ 0 := (lt_of_lt_of_le (by norm_num) hA₁).ne'
  have hA₂0 : P₂ (postSet P₂ N₂ X₂ Y₂ s) ≠ 0 := (lt_of_lt_of_le (by norm_num) hA₂).ne'
  have := cond_isProbabilityMeasure (μ := P₁) hA₁0
  have := cond_isProbabilityMeasure (μ := P₂) hA₂0
  set μ₁ := (P₁[|postSet P₁ N₁ X₁ Y₁ s]).map (readW X₁ Y₁ s) with hμ₁
  set μ₂ := (P₂[|postSet P₂ N₂ X₂ Y₂ s]).map (readW X₂ Y₂ s) with hμ₂
  have hC₁ : μ₁ (flatChamber 1)ᶜ = 0 := map_readW_compl h₁ hs
  have hC₂ : μ₂ (flatChamber 1)ᶜ = 0 := map_readW_compl h₂ hs
  obtain ⟨F₁⟩ := nonempty_liftFamily hD0 (isLiftStart_cStart₁ (μ₁.prod μ₂))
  obtain ⟨F₂⟩ := nonempty_liftFamily hD0 (isLiftStart_cStart₂ (μ₁.prod μ₂))
  have hgm : Measurable g := hg.continuous.measurable
  rw [integral_cond_eq_lift hD0 h₁ hs hA₁0 (isLiftStart_cStart₁ _) liftProj_cStart₁_mem
      (map_liftProj_cStart₁ hC₁) F₁ I hgm,
    integral_cond_eq_lift hD0 h₂ hs hA₂0 (isLiftStart_cStart₂ _) liftProj_cStart₂_mem
      (map_liftProj_cStart₂ hC₂) F₂ I hgm]
  have hd2 : 0 ≤ δ / 2 := by positivity
  have hKy : LP (μ₁.prod μ₂) {ω | δ ≤ ‖cStart₁ ω - cStart₂ ω‖} ≤ ENNReal.ofReal δ := by
    calc _ ≤ LP (μ₁.prod μ₂) ({ω | δ / 2 ≤ ‖cStart₁ ω - σ₀‖} ∪
          {ω | δ / 2 ≤ ‖cStart₂ ω - σ₀‖}) := by
          refine measure_mono fun ω hω => ?_
          by_contra hc
          simp only [mem_union, mem_ofPred_eq, not_or, not_le] at hc hω
          have := norm_sub_le_norm_sub_add_norm_sub (cStart₁ ω) σ₀ (cStart₂ ω)
          rw [norm_sub_rev σ₀] at this
          linarith
      _ ≤ _ := measure_union_le _ _
      _ = μ₁ {z | δ / 2 ≤ ‖secStart z - σ₀‖} + μ₂ {z | δ / 2 ≤ ‖secStart z - σ₀‖} := by
          rw [LP_cStart₁, LP_cStart₂]
      _ ≤ 2 * ENNReal.ofReal (δ / 4) + 2 * ENNReal.ofReal (δ / 4) :=
          add_le_add ((map_readW_le h₁ hs hA₁ σ₀ _).trans (by gcongr))
            ((map_readW_le h₂ hs hA₂ σ₀ _).trans (by gcongr))
      _ = ENNReal.ofReal δ := by rw [two_mul_ofReal_add (by positivity)]; ring_nf
  have hRR : LP (μ₁.prod μ₂) {ω | ‖σ₀‖ + 1 < ‖cStart₁ ω‖} ≤ ENNReal.ofReal η := by
    calc _ ≤ LP (μ₁.prod μ₂) {ω | 1 ≤ ‖cStart₁ ω - σ₀‖} := by
          refine measure_mono fun ω hω => ?_
          simp only [mem_ofPred_eq] at hω ⊢
          have := norm_le_norm_add_norm_sub' (cStart₁ ω) σ₀
          linarith
      _ = μ₁ {z | 1 ≤ ‖secStart z - σ₀‖} := LP_cStart₁ σ₀ 1
      _ ≤ 2 * ENNReal.ofReal (η / 2) := (map_readW_le h₁ hs hA₁ σ₀ _).trans
          (by gcongr)
      _ = ENNReal.ofReal η := two_mul_ofReal_half η
  exact abs_lift_sub_le hD0 F₁ F₂ I hg h01 hη
    (hF CS (μ₁.prod μ₂) cStart₁ cStart₂ (isLiftStart_cStart₁ _) (isLiftStart_cStart₂ _) F₁ F₂ hKy)
    hRR

end BlockBand.Transmission.DualBoundary
