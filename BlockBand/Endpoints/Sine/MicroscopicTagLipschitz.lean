module

public import BlockBand.Endpoints.Sine.MicroscopicTagIntegrals

/-!
# The microscopic tag comparison for Lipschitz tests and nonnegative weights

Starting from the lead comparison `MicroscopicTagLeadComparison`, this file removes the two
auxiliary ports and passes from the uniform tag to an interior tag, which gives the microscopic tag
comparison for Lipschitz tests and nonnegative weights. The laws are the exact physical law, the
path law `probedClockLaw W b` and Lebesgue measure `du`.

## Main results

* `abs_leadTagSide_sub_pathTagSide_le`: for `w ≥ 0` vanishing off `[-R₀, R₀]` and an
  `L`-Lipschitz `Φ`, if `E a_port(e(u)) ≤ δ` for `|u| ≤ R₀` then
  `|∫ w E[leadAveragedTest] - ∫ w E Φ(Z/M)| ≤ (∫ w)(2Lδ + (6‖Φ‖ + 3L)/n)`: removal of the two
  ports (deletion identity, cost `2 Lip(Φ) a_port`), then passage from the uniform tag to an
  interior tag (cost `O(‖Φ‖/n + Lip(Φ)/n)`).
* `microscopicTag_lipschitz`: the microscopic tag comparison for Lipschitz `Φ` and nonnegative
  `w`, uniformly in the physical tag, given `MicroscopicTagLeadComparison`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Model.Construction
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open scoped ENNReal NNReal BoundedContinuousFunction

theorem abs_test_projIci_sub_le {Φ : Set.Ici (0 : ℝ) →ᵇ ℝ} {L : ℝ≥0} (hL : LipschitzWith L Φ)
    (a b : ℝ) : |Φ (Set.projIci 0 a) - Φ (Set.projIci 0 b)| ≤ L * |a - b| := by
  have h := hL.dist_le_mul (Set.projIci 0 a) (Set.projIci 0 b)
  rw [Real.dist_eq, Subtype.dist_eq, Real.dist_eq, Set.coe_projIci, Set.coe_projIci] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (by rw [max_comm 0 a, max_comm 0 b]; exact abs_max_sub_max_le_abs a b 0) L.2)

/-- Port removal and passage to an interior tag at one energy: the averaged lead test and the
interior tag expectation differ by at most `2L E[a_port] + (6‖Φ‖ + 3L)/n` under the path law. -/
theorem abs_leadExpect_sub_pathTagExpect_le {b e : ℝ} {n W : ℕ} (hn : 4 ≤ n) (hW : 0 < W)
    {Φ : Set.Ici (0 : ℝ) →ᵇ ℝ} {L : ℝ≥0} (hL : LipschitzWith L Φ) :
    |(∫ x, leadAveragedTest b e n W Φ x ∂probedClockLaw W b) - pathTagExpect b e W (n - 3) Φ| ≤
      2 * L * (∫ x, portFraction b e W (n - 3) x ∂probedClockLaw W b) +
        (6 * ‖Φ‖ + 3 * L) / n := by
  have hP := isProbabilityMeasure_probedClockLaw W b
  have hn3 : n - 3 + 3 = n := Nat.sub_add_cancel (by omega)
  have hpt : ∀ x, |leadAveragedTest b e n W Φ x - pathIntegrand b e W (n - 3) Φ x| ≤
      2 * L * portFraction b e W (n - 3) x + (6 * ‖Φ‖ + 3 * L) / n := by
    intro x
    have h := averagedTest_sub_interiorTest_le (r := n - 3) (by omega)
      (fun t => Φ (Set.projIci 0 t)) L ‖Φ‖ (abs_test_projIci_sub_le hL)
      (fun t => norm_test_le Φ _) (fun y => leadPositionMass b e W (n - 3) x.1 x.2 y)
      (fun y => leadPositionMass_nonneg _ _ _ _ _)
    rw [hn3] at h
    have h2 : pathIntegrand b e W (n - 3) Φ x = ((n - 3 : ℕ) : ℝ)⁻¹ * ∑ i : Fin (n - 3),
        Φ (Set.projIci 0 (((n - 3 : ℕ) : ℝ) * leadPositionMass b e W (n - 3) x.1 x.2 (Sum.inl i) /
          ∑ i : Fin (n - 3), leadPositionMass b e W (n - 3) x.1 x.2 (Sum.inl i))) := by
      unfold pathIntegrand
      simp_rw [tagClock_div_meanClock hW]
      rfl
    rw [h2]
    exact h
  have hi0 : Integrable (fun x => leadAveragedTest b e n W Φ x) (probedClockLaw W b) :=
    Integrable.of_bound (measurable_leadAveragedTest_of b n W Φ measurable_const
      measurable_id).aestronglyMeasurable ‖Φ‖ (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact abs_leadAveragedTest_le b e hn W Φ x)
  have hi2 : Integrable (fun x => pathIntegrand b e W (n - 3) Φ x) (probedClockLaw W b) :=
    Integrable.of_bound (measurable_pathIntegrand_of b W (n - 3) Φ measurable_const
      measurable_id).aestronglyMeasurable ‖Φ‖ (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact abs_pathIntegrand_le b e W (n - 3) Φ x)
  have hia : Integrable (fun x => portFraction b e W (n - 3) x) (probedClockLaw W b) :=
    Integrable.of_bound (measurable_portFraction b e W (n - 3)).aestronglyMeasurable 1
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (portFraction_nonneg _ _ _ _ _)]
        exact portFraction_le_one _ _ _ _ _)
  rw [pathTagExpect_eq, ← integral_sub hi0 hi2, ← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hib : Integrable (fun x => 2 * L * portFraction b e W (n - 3) x + (6 * ‖Φ‖ + 3 * L) / n)
      (probedClockLaw W b) := (hia.const_mul _).add (integrable_const _)
  refine (integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _) hib
    (Eventually.of_forall fun x => ?_)).trans (le_of_eq ?_)
  · dsimp only; rw [Real.norm_eq_abs]; exact hpt x
  · rw [integral_add (hia.const_mul _) (integrable_const _), integral_const_mul, integral_const]
    simp

/-- The one-energy estimate `abs_leadExpect_sub_pathTagExpect_le`, integrated against
`w(u) du`. -/
theorem abs_leadTagSide_sub_pathTagSide_le (p : Parameters) (E : ℝ) {w : ℝ → ℝ}
    (hw : ∀ u, 0 ≤ w u) (hwi : Integrable w) {R₀ : ℝ} (hR : ∀ u, u ∉ Set.Icc (-R₀) R₀ → w u = 0)
    {Φ : Set.Ici (0 : ℝ) →ᵇ ℝ} {L : ℝ≥0} (hL : LipschitzWith L Φ) {δ : ℝ}
    (hδ : ∀ u ∈ Set.Icc (-R₀) R₀,
      ∫ x, portFraction p.b (microEnergy p E u) p.W (p.n - 3) x ∂probedClockLaw p.W p.b ≤ δ) :
    |leadTagSide p E w Φ - pathTagSide p E w Φ| ≤
      (∫ u, w u) * (2 * L * δ + (6 * ‖Φ‖ + 3 * L) / p.n) := by
  have hn := p.n_ge_four
  set A₀ := fun u => ∫ x, leadAveragedTest p.b (microEnergy p E u) p.n p.W Φ x
    ∂probedClockLaw p.W p.b
  set A₂ := fun u => pathTagExpect p.b (microEnergy p E u) p.W (p.n - 3) Φ
  have hi : ∀ {A : ℝ → ℝ}, StronglyMeasurable A → (∀ u, |A u| ≤ ‖Φ‖) →
      Integrable (fun u => w u * A u) := fun hA hbA =>
    hwi.mul_bdd hA.aestronglyMeasurable (Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs]; exact hbA u)
  have h0 : Integrable (fun u => w u * A₀ u) :=
    hi (stronglyMeasurable_leadExpect p E Φ) fun u => abs_leadExpect_le _ _ hn _ _
  have h2 : Integrable (fun u => w u * A₂ u) :=
    hi (stronglyMeasurable_pathTagExpect p E Φ) fun u => abs_pathTagExpect_le _ _ _ _ _
  change |(∫ u, w u * A₀ u) - ∫ u, w u * A₂ u| ≤ _
  rw [← integral_sub h0 h2, ← integral_mul_const, ← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun u => norm_nonneg _) (hwi.mul_const _)
    (Eventually.of_forall fun u => ?_))
  simp only [Real.norm_eq_abs]
  rw [← mul_sub, abs_mul, abs_of_nonneg (hw u)]
  by_cases hu : u ∈ Set.Icc (-R₀) R₀
  · refine mul_le_mul_of_nonneg_left ?_ (hw u)
    refine (abs_leadExpect_sub_pathTagExpect_le hn p.W_pos hL).trans ?_
    have := hδ u hu
    have hL0 : (0 : ℝ) ≤ 2 * L := by positivity
    linarith [mul_le_mul_of_nonneg_left this hL0]
  · rw [hR u hu, zero_mul, zero_mul]

theorem tendsto_n_atTop {τ : ℝ} (hτ : 0 < τ) (s : CriticalSequence τ) :
    Tendsto (fun j => (s.n j : ℝ)) atTop atTop := by
  have hWt : Tendsto (fun j => ((s.W j : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp s.width_tendsto
  have h1 : ∀ᶠ j in atTop, τ / 2 ≤ (s.n j : ℝ) / s.W j :=
    s.ratio_tendsto.eventually (le_mem_nhds (by linarith))
  refine tendsto_atTop.2 fun M => ?_
  filter_upwards [h1, hWt.eventually_ge_atTop (2 * |M| / τ)] with j hj hW
  have hW0 : (0 : ℝ) < s.W j := by exact_mod_cast s.W_pos j
  have : τ / 2 * s.W j ≤ s.n j := by rwa [le_div_iff₀ hW0] at hj
  have h2 : 2 * |M| / τ * (τ / 2) = |M| := by field_simp
  have h3 : |M| ≤ τ / 2 * s.W j := by
    have := mul_le_mul_of_nonneg_right hW (show 0 ≤ τ / 2 by linarith)
    linarith
  linarith [le_abs_self M]

theorem exists_bound_of_hasCompactSupport {w : ℝ → ℝ} (hwc : HasCompactSupport w) :
    ∃ R₀ : ℝ, ∀ u, u ∉ Set.Icc (-R₀) R₀ → w u = 0 := by
  obtain ⟨R₀, hR₀⟩ := hwc.isCompact.isBounded.exists_norm_le
  refine ⟨R₀, fun u hu => image_eq_zero_of_notMem_tsupport fun hmem => hu ?_⟩
  have := hR₀ u hmem
  rw [Real.norm_eq_abs] at this
  exact ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩

/-- The microscopic tag comparison for Lipschitz `Φ` and nonnegative `w`, uniformly in the
physical tag, from the lead comparison and `NegativeClockContract`. -/
theorem microscopicTag_lipschitz (hIso : MicroscopicTagLeadComparison)
    (hNeg : NegativeClockContract) (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (E : ℝ)
    (hE1 : -2 < E) (hE2 : E < 2) (w : ℝ → ℝ) (hws : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w)
    (hwc : HasCompactSupport w) (hw0 : ∀ u, 0 ≤ w u) (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ)
    (hΦ : ∃ L : ℝ≥0, LipschitzWith L Φ) (τ : ℝ) (hτ : 0 < τ) (s : CriticalSequence τ)
    (R : ∀ j, (s.parameters b hb hb' j).GaussianRingModel) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ j in atTop, ∀ k : ZMod (s.parameters b hb hb' j).n,
      |physicalTagSide (s.parameters b hb hb' j) (R j) E w Φ k -
          pathTagSide (s.parameters b hb hb' j) E w Φ| ≤ ε := by
  obtain ⟨L, hL⟩ := hΦ
  obtain ⟨R₀, hR₀⟩ := exists_bound_of_hasCompactSupport hwc
  have hwi : Integrable w := hws.continuous.integrable_of_hasCompactSupport hwc
  set Iw := ∫ u, w u
  have hIw : 0 ≤ Iw := integral_nonneg hw0
  set δ := ε / (4 * (2 * L + 1) * (Iw + 1))
  have hδ : 0 < δ := by positivity
  have hiso := hIso b hb hb' E hE1 hE2 w hws hwc hw0 Φ ⟨L, hL⟩ τ hτ s R (ε / 2) (by positivity)
  have hport := portFraction_uniform hNeg hb hb' hE1 hE2 hτ s R₀ hδ
  have hnlarge := (tendsto_n_atTop hτ s).eventually_ge_atTop
    (4 * (Iw + 1) * (6 * ‖Φ‖ + 3 * L) / ε + 1)
  filter_upwards [hiso, hport, hnlarge] with j hj hpj hnj k
  have hlp := abs_leadTagSide_sub_pathTagSide_le (s.parameters b hb hb' j) E hw0 hwi hR₀ hL hpj
  have hn0 : (0 : ℝ) < (s.parameters b hb hb' j).n := by
    have := (s.parameters b hb hb' j).n_ge_four
    exact_mod_cast (show 0 < (s.parameters b hb hb' j).n by omega)
  have hnj' : 4 * (Iw + 1) * (6 * ‖Φ‖ + 3 * L) / ε + 1 ≤ (s.parameters b hb hb' j).n := hnj
  have hC0 : 0 ≤ 6 * ‖Φ‖ + 3 * (L : ℝ) := by positivity
  have e1 : Iw * (2 * L * δ) ≤ ε / 4 := by
    have : Iw * (2 * L * δ) ≤ (Iw + 1) * ((2 * L + 1) * δ) := by
      have hL0 : (0 : ℝ) ≤ L := L.2
      nlinarith
    calc _ ≤ (Iw + 1) * ((2 * L + 1) * δ) := this
      _ = ε / 4 := by simp only [δ]; field_simp
  have e2 : Iw * ((6 * ‖Φ‖ + 3 * L) / (s.parameters b hb hb' j).n) ≤ ε / 4 := by
    rw [mul_div_assoc', div_le_iff₀ hn0]
    have h1 : 4 * (Iw + 1) * (6 * ‖Φ‖ + 3 * L) / ε ≤ (s.parameters b hb hb' j).n := by linarith
    rw [div_le_iff₀ hε] at h1
    nlinarith
  calc _ ≤ |physicalTagSide (s.parameters b hb hb' j) (R j) E w Φ k -
          leadTagSide (s.parameters b hb hb' j) E w Φ| +
        |leadTagSide (s.parameters b hb hb' j) E w Φ -
          pathTagSide (s.parameters b hb hb' j) E w Φ| := abs_sub_le _ _ _
    _ ≤ ε / 2 + (ε / 4 + ε / 4) := by
        refine add_le_add (hj k) (hlp.trans ?_)
        rw [mul_add]; exact add_le_add e1 e2
    _ = ε := by ring

end BlockBand.Endpoints
