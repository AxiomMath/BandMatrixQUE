module

public import BlockBand.Endpoints.Sine.LocalMassFlatPath
public import BlockBand.Endpoints.Sine.LocalMassFlatPhysical
public import BlockBand.Endpoints.Sine.LocalMassFlatDensity

/-!
# Strong local mass flatness

This file proves `LocalMassFlatStatement`. On the matched-lead path of `r = n - 3` blocks,
`E r⁻¹Σ_K min(|Z_{r;K}/M_r - 1|, 1) ≤ C√τ + o(1)` along every clock sequence
(`lmf_pathRatio_eventually`); by a subsequence argument this is uniform for the energies `e(u)`,
`u ∈ supp w` (`lmf_defect_uniform`). Since `min(x,1) ≥ 1 - min(|x-1|, 1)` for `x ≥ 0`, the path
side of the comparison with `Φ = min(·,1)` is `≥ 1 - C√τ - o(1)` (`lmf_pathTagSide_ge`). The exact
identity `E Σ w(u_α)|n p_{αk} - 1| = 2 E Σ w(u_α) - 2 E Σ w(u_α) min(n p_{αk}, 1)`
(`lmf_blockFlatness_eq`, cyclic invariance), `E Σ w(u_α) → ∫ w = 1` (the critical density) and
the microscopic tag comparison give `≤ 2C√τ + o(1)`, uniformly in the block. The pair is at most
the average of its two blocks (`lmf_pairFlatness_le`). The identity `E(Z/M) = 1` for the limit
law is not needed: the bounded inequality `min(x,1) ≥ 1 - min(|x-1|,1)` replaces it.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology
open BlockBand.Model.Construction
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.Inputs
open scoped BoundedContinuousFunction ENNReal

/-!
## The path side of the comparison with `Φ = min(·, 1)`
-/

theorem lmf_min_ge_one_sub (y : ℝ) (hy : 0 ≤ y) : 1 - min |y - 1| 1 ≤ min y 1 := by
  rcases le_total 1 y with h | h
  · rw [min_eq_right h]; linarith [le_min (abs_nonneg (y - 1)) zero_le_one]
  · rw [min_eq_left h, abs_of_nonpos (by linarith), min_eq_left (by linarith)]
    linarith

/-- The averaged path test is measurable jointly in the energy parameter and the sample. -/
theorem lmf_measurable_pathIntegrand (b : ℝ) (W r : ℕ) {α : Type*} [MeasurableSpace α]
    {e : α → ℝ} {x : α → GrowthPath W × (Fin 2 × Fin W → ℂ)} (he : Measurable e)
    (hx : Measurable x) (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) :
    Measurable (fun a => (r : ℝ)⁻¹ * ∑ K : Fin r,
      Φ (Set.projIci 0 (lmf_tagClock b (e a) W r K (x a) / lmf_meanClock b (e a) W r (x a)))) :=
  measurable_const.mul (Finset.measurable_sum _ fun K _ =>
    (Φ.continuous.measurable.comp (lmf_continuous_projIci_zero.measurable.comp
      ((lmf_measurable_tagClock_of b W r K he hx).div
        (lmf_measurable_meanClock_of b W r he hx)))))

/-- `|r⁻¹ Σ_K Φ(·)| ≤ ‖Φ‖`. -/
theorem lmf_abs_pathIntegrand_le {r : ℕ} (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) (y : Fin r → ℝ) :
    |(r : ℝ)⁻¹ * ∑ K, Φ (Set.projIci 0 (y K))| ≤ ‖Φ‖ := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr; simp
  have hr' : (0 : ℝ) < r := Nat.cast_pos.2 hr
  rw [abs_mul, abs_of_pos (inv_pos.2 hr')]
  calc (r : ℝ)⁻¹ * |∑ K, Φ (Set.projIci 0 (y K))| ≤ (r : ℝ)⁻¹ * ∑ _K : Fin r, ‖Φ‖ := by
        gcongr
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun K _ => ?_)
        rw [← Real.norm_eq_abs]
        exact Φ.norm_coe_le_norm _
    _ = ‖Φ‖ := by simp [hr'.ne']

/-- `E_{path,h,K} min(Z/M, 1) ≥ 1 - E_{path,h} r⁻¹Σ_K min(|Z/M - 1|, 1)` (`r > 0`). -/
theorem lmf_pathTagExpect_minOne_ge (b e : ℝ) (W r : ℕ) (hr : 0 < r) :
    1 - lmf_ratioDefect b e W r ≤ lmf_pathTagExpect b e W r lmf_minOne := by
  have := lmf_isProbabilityMeasure_probedClockLaw W b
  have hr' : (0 : ℝ) < r := Nat.cast_pos.2 hr
  have hZm : ∀ K : Fin r, Measurable (fun x => lmf_tagClock b e W r K x) := fun K =>
    lmf_measurable_tagClock_of b W r K (measurable_const (a := e)) measurable_id
  have hMm : Measurable (fun x => lmf_meanClock b e W r x) :=
    lmf_measurable_meanClock_of b W r (measurable_const (a := e)) measurable_id
  have hLm : Measurable (fun x => (r : ℝ)⁻¹ * ∑ K : Fin r,
      min |lmf_tagClock b e W r K x / lmf_meanClock b e W r x - 1| 1) :=
    measurable_const.mul (Finset.measurable_sum _ fun K _ =>
      ((continuous_abs.measurable.comp (((hZm K).div hMm).sub measurable_const)).min
        measurable_const))
  have hLb : ∀ x, ‖(r : ℝ)⁻¹ * ∑ K : Fin r,
      min |lmf_tagClock b e W r K x / lmf_meanClock b e W r x - 1| 1‖ ≤ 1 := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity)
      (Finset.sum_nonneg fun K _ => le_min (abs_nonneg _) zero_le_one))]
    calc (r : ℝ)⁻¹ * ∑ K : Fin r,
          min |lmf_tagClock b e W r K x / lmf_meanClock b e W r x - 1| 1
        ≤ (r : ℝ)⁻¹ * ∑ _K : Fin r, (1 : ℝ) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun K _ => min_le_right _ _)
            (by positivity)
      _ = 1 := by simp [hr'.ne']
  have hLint : Integrable (fun x => (r : ℝ)⁻¹ * ∑ K : Fin r,
      min |lmf_tagClock b e W r K x / lmf_meanClock b e W r x - 1| 1) (probedClockLaw W b) :=
    Integrable.of_bound hLm.aestronglyMeasurable 1 (Eventually.of_forall hLb)
  have hAm := lmf_measurable_pathIntegrand b W r (measurable_const (a := e))
    (measurable_id (α := GrowthPath W × (Fin 2 × Fin W → ℂ))) lmf_minOne
  have hAint : Integrable (fun x => (r : ℝ)⁻¹ * ∑ K : Fin r,
      lmf_minOne (Set.projIci 0 (lmf_tagClock b e W r K x / lmf_meanClock b e W r x)))
      (probedClockLaw W b) :=
    Integrable.of_bound hAm.aestronglyMeasurable ‖lmf_minOne‖
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact lmf_abs_pathIntegrand_le lmf_minOne _)
  unfold lmf_ratioDefect lmf_pathTagExpect
  have h1 : 1 - ∫ x, (r : ℝ)⁻¹ * ∑ K : Fin r,
        min |lmf_tagClock b e W r K x / lmf_meanClock b e W r x - 1| 1 ∂probedClockLaw W b =
      ∫ x, (1 - (r : ℝ)⁻¹ * ∑ K : Fin r,
        min |lmf_tagClock b e W r K x / lmf_meanClock b e W r x - 1| 1) ∂probedClockLaw W b := by
    rw [integral_sub (integrable_const 1) hLint]
    simp
  rw [h1]
  refine integral_mono ((integrable_const 1).sub hLint) hAint fun x => ?_
  have hy : ∀ K : Fin r, 0 ≤ lmf_tagClock b e W r K x / lmf_meanClock b e W r x := fun K =>
    div_nonneg (lmf_tagClock_nonneg b e W r K x) (lmf_meanClock_nonneg b e W r x)
  simp only
  simp_rw [lmf_minOne_projIci (hy _)]
  have e1 : (r : ℝ)⁻¹ * ∑ K : Fin r,
      (1 - min |lmf_tagClock b e W r K x / lmf_meanClock b e W r x - 1| 1) =
      1 - (r : ℝ)⁻¹ * ∑ K : Fin r,
        min |lmf_tagClock b e W r K x / lmf_meanClock b e W r x - 1| 1 := by
    rw [Finset.sum_sub_distrib, mul_sub]
    simp [hr'.ne']
  rw [← e1]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun K _ => lmf_min_ge_one_sub _ (hy K))
    (by positivity)

/-- The path side `∫ w(u) E_{path,h,K} min(Z_{r;K}/M_r, 1)(e(u)) du ≥ 1 - B` when the ratio
defect is at most `B` at every energy `e(u)`, `u ∈ supp w` (`w ≥ 0`, `∫ w = 1`, `r = n - 3 > 0`). -/
theorem lmf_pathTagSide_ge (p : Parameters) (E : ℝ) (w : ℝ → ℝ) (hw : Continuous w)
    (hwc : HasCompactSupport w) (hw0 : ∀ u, 0 ≤ w u) (hw1 : ∫ u, w u = 1) (B : ℝ)
    (hr : 0 < p.n - 3)
    (hD : ∀ u ∈ tsupport w, lmf_ratioDefect p.b (microEnergy p E u) p.W (p.n - 3) ≤ B) :
    1 - B ≤ lmf_pathTagSide p E w lmf_minOne := by
  have := lmf_isProbabilityMeasure_probedClockLaw p.W p.b
  have hwint : Integrable w := hw.integrable_of_hasCompactSupport hwc
  have hme : Measurable (fun u : ℝ => microEnergy p E u) := by
    unfold microEnergy; fun_prop
  have hAm : Measurable (fun u =>
      lmf_pathTagExpect p.b (microEnergy p E u) p.W (p.n - 3) lmf_minOne) := by
    have hj := lmf_measurable_pathIntegrand p.b p.W (p.n - 3) (hme.comp measurable_fst)
      measurable_snd lmf_minOne
    unfold lmf_pathTagExpect
    exact (hj.stronglyMeasurable.integral_prod_right' (ν := probedClockLaw p.W p.b)).measurable
  have hAb : ∀ u, |lmf_pathTagExpect p.b (microEnergy p E u) p.W (p.n - 3) lmf_minOne| ≤
      ‖lmf_minOne‖ := by
    intro u
    unfold lmf_pathTagExpect
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (C := ‖lmf_minOne‖)
      (Eventually.of_forall fun x => ?_)).trans (by simp)
    rw [Real.norm_eq_abs]
    exact lmf_abs_pathIntegrand_le lmf_minOne _
  have hwA : Integrable (fun u => w u *
      lmf_pathTagExpect p.b (microEnergy p E u) p.W (p.n - 3) lmf_minOne) := by
    refine (hwint.mul_const ‖lmf_minOne‖).mono' (hw.measurable.mul hAm).aestronglyMeasurable
      (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 u)]
    exact mul_le_mul_of_nonneg_left (hAb u) (hw0 u)
  have hge : ∀ u, w u * (1 - B) ≤
      w u * lmf_pathTagExpect p.b (microEnergy p E u) p.W (p.n - 3) lmf_minOne := by
    intro u
    by_cases hu : u ∈ tsupport w
    · exact mul_le_mul_of_nonneg_left ((sub_le_sub_left (hD u hu) 1).trans
        (lmf_pathTagExpect_minOne_ge _ _ _ _ hr)) (hw0 u)
    · rw [image_eq_zero_of_notMem_tsupport hu]; simp
  unfold lmf_pathTagSide
  calc 1 - B = ∫ u, w u * (1 - B) := by rw [integral_mul_const, hw1, one_mul]
    _ ≤ _ := integral_mono (hwint.mul_const _) hwA hge

/-- Uniformity in the energy window: the positive and negative limiting moment bounds are uniform
for the energies `e(u)` in the compact window. If the ratio defect is eventually `≤ B + ε` along
every clock sequence, then along a critical sequence it is eventually `≤ B + ε` simultaneously
for all `e(u) = E + u/(Nρ(E))`, `u` in a compact set, on the matched-lead path of `r = n - 3`
blocks. -/
theorem lmf_defect_uniform (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (E : ℝ) (hE : -2 < E)
    (hE' : E < 2) (τ : ℝ) (B : ℝ)
    (hC : ∀ s : ClockSequence τ E, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ j in atTop, lmf_ratioDefect b (s.energy j) (s.W j) (s.n j) ≤ B + ε)
    (s : CriticalSequence τ) (U : Set ℝ) (hU : IsCompact U) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ u ∈ U,
      lmf_ratioDefect b (microEnergy (s.parameters b hb hb' j) E u) (s.W j) (s.n j - 3) ≤
        B + ε := by
  intro ε hε
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  simp only [not_forall, not_le, exists_prop] at hcon
  obtain ⟨φ, hφ, hφP⟩ := extraction_of_frequently_atTop hcon
  choose u hu hgt using hφP
  obtain ⟨Ub, hUb⟩ := hU.isBounded.exists_norm_le
  have hρ : 0 < Parameters.semicircleDensity E := lmf_semicircleDensity_pos hE hE'
  have hWφ : Tendsto (fun j => s.W (φ j)) atTop atTop := s.width_tendsto.comp hφ.tendsto_atTop
  have hWr : Tendsto (fun j => (s.W (φ j) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hWφ
  have hratio : Tendsto (fun j => ((s.n (φ j) - 3 : ℕ) : ℝ) / (s.W (φ j) : ℝ)) atTop (𝓝 τ) := by
    have h1 := s.ratio_tendsto.comp hφ.tendsto_atTop
    have h2 : Tendsto (fun j => (3 : ℝ) / s.W (φ j)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hWr
    have h3 := h1.sub h2
    rw [sub_zero] at h3
    refine h3.congr fun j => ?_
    have h4 := s.n_ge_four (φ j)
    simp only [Function.comp]
    rw [Nat.cast_sub (by omega), sub_div]
    norm_num
  have henergy : Tendsto (fun j => microEnergy (s.parameters b hb hb' (φ j)) E (u j)) atTop
      (𝓝 E) := by
    have hsmall : Tendsto (fun j => u j / ((s.parameters b hb hb' (φ j)).N *
        Parameters.semicircleDensity E)) atTop (𝓝 0) := by
      have hb0 : Tendsto (fun j => max Ub 0 / ((s.W (φ j) : ℝ) * Parameters.semicircleDensity E))
          atTop (𝓝 0) := tendsto_const_nhds.div_atTop (hWr.atTop_mul_const hρ)
      refine squeeze_zero_norm (fun j => ?_) hb0
      have hW0 : (0 : ℝ) < s.W (φ j) := Nat.cast_pos.2 (s.W_pos _)
      have hN : (s.W (φ j) : ℝ) ≤ (s.parameters b hb hb' (φ j)).N := by
        have h4 := s.n_ge_four (φ j)
        change (s.W (φ j) : ℝ) ≤ ((s.n (φ j) * s.W (φ j) : ℕ) : ℝ)
        exact_mod_cast Nat.le_mul_of_pos_left _ (by omega)
      have hNpos : (0 : ℝ) < (s.parameters b hb hb' (φ j)).N := hW0.trans_le hN
      rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (mul_pos hNpos hρ)]
      calc |u j| / ((s.parameters b hb hb' (φ j)).N * Parameters.semicircleDensity E)
          ≤ max Ub 0 / ((s.parameters b hb hb' (φ j)).N * Parameters.semicircleDensity E) := by
            gcongr
            rw [← Real.norm_eq_abs]
            exact (hUb _ (hu j)).trans (le_max_left _ _)
        _ ≤ max Ub 0 / ((s.W (φ j) : ℝ) * Parameters.semicircleDensity E) := by
            gcongr
    have := (tendsto_const_nhds (x := E)).add hsmall
    rw [add_zero] at this
    exact this
  let s' : ClockSequence τ E :=
    { n := fun j => s.n (φ j) - 3
      W := fun j => s.W (φ j)
      energy := fun j => microEnergy (s.parameters b hb hb' (φ j)) E (u j)
      W_pos := fun j => s.W_pos _
      width_tendsto := hWφ
      ratio_tendsto := hratio
      energy_tendsto := henergy }
  obtain ⟨j, hj⟩ := (hC s' (ε / 2) (half_pos hε)).exists
  have := hgt j
  change lmf_ratioDefect b (microEnergy (s.parameters b hb hb' (φ j)) E (u j)) (s.W (φ j))
    (s.n (φ j) - 3) ≤ B + ε / 2 at hj
  linarith

/-- **The local mass flatness theorem**: strong local mass flatness for the original periodic
matrix, for every adjacent pair and every block, with one constant `C = C_{b,E,T₀}` (see
`LocalMassFlatStatement`). Hypotheses: `NegativeClockContract`, `ClockSmallBallContract`,
`CriticalDensity`, the tagged flat bound `LmfTaggedFlat` and the microscopic tag comparison
`LmfMicroscopicTagComparison`.
-/
theorem localMassFlat (hNeg : NegativeClockContract) (hSmall : ClockSmallBallContract)
    (hDens : CriticalDensity) (hTag : LmfTaggedFlat) (hMicro : LmfMicroscopicTagComparison) :
    LocalMassFlatStatement := by
  intro b hb hb' E hE hE' T₀ hT₀
  obtain ⟨C, -, hC⟩ := lmf_pathRatio_eventually hNeg hSmall hTag b hb hb' E hE hE' T₀ hT₀
  refine ⟨2 * C, fun w hws hw τ hτ hτT s R i ε hε => ?_⟩
  obtain ⟨hwc, hwcs, hw0, hw1⟩ := hw
  have hε' : 0 < ε / 6 := by positivity
  have hU := lmf_defect_uniform b hb hb' E hE hE' τ (C * Real.sqrt τ) (hC τ hτ hτT) s
    (tsupport w) hwcs.isCompact (ε / 6) hε'
  have hM := hMicro b hb hb' E hE hE' w hws hwcs lmf_minOne τ hτ s R (ε / 6) hε'
  have hS := (lmf_spectralWindow_tendsto hDens.1 b hb hb' E hE hE' w ⟨hwc, hwcs, hw0, hw1⟩
    τ hτ s R).eventually_lt_const (by linarith : (1 : ℝ) < 1 + ε / 6)
  filter_upwards [hU, hM, hS] with j hUj hMj hSj
  have hr : 0 < (s.parameters b hb hb' j).n - 3 := by
    have := s.n_ge_four j
    change 0 < s.n j - 3
    omega
  have hpath := lmf_pathTagSide_ge (s.parameters b hb hb' j) E w hwc hwcs hw0 hw1
    (C * Real.sqrt τ + ε / 6) hr hUj
  have hblock : ∀ k, lmf_blockFlatness (s.parameters b hb hb' j) (R j) E w k ≤
      2 * C * Real.sqrt τ + ε := by
    intro k
    rw [lmf_blockFlatness_eq (s.parameters b hb hb' j) (R j) E w hwc hwcs k]
    have := (abs_le.1 (hMj k)).1
    linarith
  refine ⟨(lmf_pairFlatness_le (s.parameters b hb hb' j) (R j) E w hwc hwcs hw0 (i j)).trans ?_,
    hblock (i j)⟩
  linarith [hblock (i j), hblock (i j + 1)]

end BlockBand.Endpoints
