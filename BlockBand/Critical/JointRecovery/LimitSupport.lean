module

public import BlockBand.Critical.JointRecovery.FiniteLaw
public import BlockBand.Critical.JointRecovery.GridNull
public import BlockBand.Counting.SimpleSpectralLimitsPhysical

/-!
# Support of a critical entire limit: `D(0) = 1`, real zeros, simple zeros

`limit_ae_goodEntire`: every weak limit of the laws of `D_W` along a critical sequence is carried
by `goodEntire`: `D(0) = 1` (a closed condition), the energy axis is real-rooted (a nonreal zero
is an open condition), and its real zeros are simple (a multiple zero forces nearby functions to
have two close zeros, which the two-point bound of the counting theorem makes rare; the grid
argument `measure_iUnion_null_of_grid` concludes).

Law: `μ` is any weak limit (compact-open Borel topology) of the laws of `D_W` (`finiteEntireLaw`,
family `1, q_1, …, q_k`) along a critical sequence (`W → ∞`, `n/W → τ`, both parities, any
realizations), for fixed `0 < b < 1/2` and bulk `E` (`ρ(E) > 0`). The hypothesis is the external
PSSS input `source`, through `Counting.finiteRealization_markedLaw_Ioo_twoPoint_bound`. No
uniformity in `(b, E, τ)`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Critical.JointRecovery

open Filter Topology Set MeasureTheory Metric
open BlockBand.Critical.Entire BlockBand.Critical.Entire.EntireFunction
open BlockBand.Internal.Contracts.CriticalEntire BlockBand.Model.Construction
open scoped ENNReal

variable {k : ℕ}

/-- The open rectangle `x < Re w < y`, `|Im w| < y - x`. -/
def strip (x y : ℝ) : Set ℂ := {w | x < w.re ∧ w.re < y ∧ |w.im| < y - x}

theorem strip_mono {x y x' y' : ℝ} (hx : x' ≤ x) (hy : y ≤ y') : strip x y ⊆ strip x' y' :=
  fun w ⟨h1, h2, h3⟩ => ⟨by linarith, by linarith, by linarith⟩

theorem ball_subset_strip (x₀ : ℝ) {a : ℝ} : ball (x₀ : ℂ) a ⊆ strip (x₀ - a) (x₀ + a) := by
  intro w hw
  rw [mem_ball, Complex.dist_eq] at hw
  have ha : 0 < a := lt_of_le_of_lt (norm_nonneg _) hw
  have h1 : |w.re - x₀| < a := by
    have := Complex.abs_re_le_norm (w - x₀); simp at this; linarith
  have h2 : |w.im| < a := by
    have := Complex.abs_im_le_norm (w - x₀); simp at this; linarith
  refine ⟨by linarith [(abs_lt.mp h1).1], by linarith [(abs_lt.mp h1).2], by linarith⟩

/-- Axis has a multiple zero or two distinct zeros in the strip. -/
def twoZeroSet (k : ℕ) (x y : ℝ) : Set (EntireFunction (k + 1)) :=
  {G | ∃ w ∈ strip x y, axis G w = 0 ∧
    (deriv (axis G) w = 0 ∨ ∃ w' ∈ strip x y, w' ≠ w ∧ axis G w' = 0)}

theorem twoZeroSet_mono {x y x' y' : ℝ} (hx : x' ≤ x) (hy : y ≤ y') :
    twoZeroSet k x y ⊆ twoZeroSet k x' y' := by
  rintro G ⟨w, hw, hz, h | ⟨w', hw', hne, hz'⟩⟩
  · exact ⟨w, strip_mono hx hy hw, hz, Or.inl h⟩
  · exact ⟨w, strip_mono hx hy hw, hz, Or.inr ⟨w', strip_mono hx hy hw', hne, hz'⟩⟩

/-- The point event "multiple real zero at `x₀`" (with `F(0) ≠ 0`). -/
def multipleZeroAt (k : ℕ) (x₀ : ℝ) : Set (EntireFunction (k + 1)) :=
  {F | F 0 ≠ 0 ∧ axis F x₀ = 0 ∧ deriv (axis F) x₀ = 0}

/-- **Hurwitz (multiple zeros) in the state space**: a multiple real zero at `x₀` forces every nearby entire
function into `twoZeroSet (x₀ - a) (x₀ + a)`. -/
theorem multipleZeroAt_subset_interior (x₀ : ℝ) {a : ℝ} (ha : 0 < a) :
    multipleZeroAt k x₀ ⊆ interior (twoZeroSet k (x₀ - a) (x₀ + a)) := by
  rintro F ⟨hF0, hz, hd⟩
  rw [mem_interior_iff_mem_nhds]
  have hF0' : axis F 0 ≠ 0 := by rwa [axis_zero]
  have h := eventually_multiple_or_two_zeros (tendstoLocallyUniformly_axis
    (tendsto_id : Tendsto (fun G : EntireFunction (k + 1) => G) (𝓝 F) (𝓝 F)))
    (fun G => differentiable_axis G) (differentiable_axis F) hz hd
    (eventually_ne_zero_punctured (differentiable_axis F) hF0' _) ha
  filter_upwards [h] with G ⟨w, hw, hwz, halt⟩
  refine ⟨w, ball_subset_strip x₀ hw, hwz, ?_⟩
  rcases halt with h1 | ⟨w', hw', hne, hz'⟩
  · exact Or.inl h1
  · exact Or.inr ⟨w', ball_subset_strip x₀ hw', hne, hz'⟩

/-- On a good entire function, `twoZeroSet` means two distinct real zeros in `(x, y)`. -/
theorem two_real_zeros_of_mem {x y : ℝ} {G : EntireFunction (k + 1)} (hG : G ∈ goodEntire k)
    (h : G ∈ twoZeroSet k x y) :
    ∃ y₁ y₂ : ℝ, y₁ ≠ y₂ ∧ y₁ ∈ Ioo x y ∧ y₂ ∈ Ioo x y ∧ axis G y₁ = 0 ∧ axis G y₂ = 0 := by
  obtain ⟨w, hw, hz, halt⟩ := h
  have hwr : ((w.re : ℝ) : ℂ) = w := Complex.ext rfl (by simp [hG.1.2 w hz])
  rcases halt with hd | ⟨w', hw', hne, hz'⟩
  · exact absurd (by rw [hwr]; exact hd) (hG.2 w.re (by rw [hwr]; exact hz))
  · have hwr' : ((w'.re : ℝ) : ℂ) = w' := Complex.ext rfl (by simp [hG.1.2 w' hz'])
    refine ⟨w.re, w'.re, fun h => hne ?_, ⟨hw.1, hw.2.1⟩, ⟨hw'.1, hw'.2.1⟩,
      by rw [hwr]; exact hz, by rw [hwr']; exact hz'⟩
    rw [← hwr, ← hwr', h]

/-- `D_W(0) = 1` almost surely. -/
theorem finiteEntireLaw_compl_one {p : Parameters} (R : FiniteRealization p) (E : ℝ)
    (q : Fin k → C(Torus, ℝ)) :
    (finiteEntireLaw R E (fullProfile q) : Measure (EntireFunction (k + 1)))
      {F | F 0 = 1}ᶜ = 0 := by
  change ((R.model.law : Measure p.SiteMatrix).map (finiteEntireDeterminant p E (fullProfile q)))
    {F | F 0 = 1}ᶜ = 0
  rw [Measure.map_apply (measurable_finiteEntireDeterminant E _)
    (isClosed_eq (continuous_eval_const 0) continuous_const).measurableSet.compl]
  refine measure_mono_null (fun H hH => ?_) (ae_iff.mp (ae_finiteFacts R.model E q))
  intro hf
  apply hH
  show finiteEntireDeterminant p E (fullProfile q) H 0 = 1
  rw [coe_finiteEntireDeterminant E q H hf.base, BlockBand.Critical.physicalFiniteDeterminant_zero]

/-- The open set of entire functions with `F(0) ≠ 0` and a nonreal axis zero. -/
theorem isOpen_nonrealZero :
    IsOpen {F : EntireFunction (k + 1) | F 0 ≠ 0 ∧ ¬ RealRooted F} := by
  rw [isOpen_iff_mem_nhds]
  rintro F ⟨hF0, hnr⟩
  simp only [RealRooted, not_forall] at hnr
  obtain ⟨w, hz, him⟩ := hnr
  have hF0' : axis F 0 ≠ 0 := by rwa [axis_zero]
  have hr : 0 < |w.im| / 2 := half_pos (abs_pos.mpr him)
  have h := eventually_exists_zero_mem_ball (tendstoLocallyUniformly_axis
    (tendsto_id : Tendsto (fun G : EntireFunction (k + 1) => G) (𝓝 F) (𝓝 F)))
    (fun G => differentiable_axis G) (differentiable_axis F).continuous hz
    (eventually_ne_zero_punctured (differentiable_axis F) hF0' _) hr
  have h0 : ∀ᶠ G in 𝓝 F, G 0 ≠ 0 :=
    (continuous_eval_const (0 : Fin (k + 1) → ℂ)).continuousAt.eventually_ne hF0
  filter_upwards [h, h0] with G ⟨w', hw', hz'⟩ hG0
  refine ⟨hG0, fun hR => ?_⟩
  have him' := hR w' hz'
  have h1 : |w.im - w'.im| ≤ dist w w' := by
    rw [Complex.dist_eq, ← Complex.sub_im]; exact Complex.abs_im_le_norm _
  rw [him', sub_zero, dist_comm] at h1
  have := mem_ball.mp hw'
  linarith

/-- **Support of critical entire limits.** -/
theorem limit_ae_goodEntire (source : BlockBand.External.PSSS.SourceContract.{0}) {τ : ℝ}
    (s : CriticalSequence τ) (b E : ℝ) (hb : 0 < b) (hb' : b < 1 / 2)
    (hρ : 0 < Parameters.semicircleDensity E)
    (R : ∀ j, FiniteRealization (s.parameters b hb hb' j)) (q : Fin k → C(Torus, ℝ))
    {μ : RandomEntire (k + 1)}
    (hμ : Tendsto (fun j => finiteEntireLaw (R j) E (fullProfile q)) atTop (𝓝 μ)) :
    ∀ᵐ F ∂(μ : Measure (EntireFunction (k + 1))), F ∈ goodEntire k := by
  set μs := fun j => finiteEntireLaw (R j) E (fullProfile q) with hμs
  -- (a) `F(0) = 1`
  have hC : IsClosed {F : EntireFunction (k + 1) | F 0 = 1} :=
    isClosed_eq (continuous_eval_const 0) continuous_const
  have hone : (μ : Measure (EntireFunction (k + 1))) {F | F 0 = 1}ᶜ = 0 := by
    have hj : ∀ j, (μs j : Measure (EntireFunction (k + 1))) {F | F 0 = 1} = 1 := fun j =>
      (prob_compl_eq_zero_iff hC.measurableSet).mp (finiteEntireLaw_compl_one (R j) E q)
    have hls := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμ hC
    simp only [hj, limsup_const] at hls
    exact (prob_compl_eq_zero_iff hC.measurableSet).mpr (le_antisymm prob_le_one hls)
  -- (b) real-rootedness
  have hN := isOpen_nonrealZero (k := k)
  have hreal : (μ : Measure (EntireFunction (k + 1)))
      {F | F 0 ≠ 0 ∧ ¬ RealRooted F} = 0 := by
    have hj : ∀ j, (μs j : Measure (EntireFunction (k + 1)))
        {F | F 0 ≠ 0 ∧ ¬ RealRooted F} = 0 := fun j =>
      measure_mono_null (fun F (hF : F 0 ≠ 0 ∧ ¬ RealRooted F) (hg : F ∈ goodEntire k) =>
        hF.2 hg.1.2) (finiteEntireLaw_compl_goodEntire (R j) E q)
    have hli := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hμ hN
    simp only [hj, liminf_const] at hli
    exact le_antisymm hli bot_le
  -- (c) simple zeros by the grid argument
  set C' := (s.parameters b hb hb' 0).physicalUnfoldedConstant source
    (Parameters.semicircleDensity E) with hC'
  set ρ := Parameters.semicircleDensity E with hρ_def
  have hratio : Tendsto (fun j => ((s.n j : ℝ) / s.W j) * ρ) atTop (𝓝 (τ * ρ)) :=
    s.ratio_tendsto.mul_const ρ
  have hB : ∀ x y, x ≤ y → (μ : Measure (EntireFunction (k + 1)))
      (interior (twoZeroSet k x y)) ≤ ENNReal.ofReal ((C' * (τ * ρ) * (y - x)) ^ 2) := by
    intro x y hxy
    have hli := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hμ
      (isOpen_interior (s := twoZeroSet k x y))
    refine hli.trans ?_
    have hbound : ∀ j, (μs j : Measure (EntireFunction (k + 1))) (interior (twoZeroSet k x y)) ≤
        ENNReal.ofReal ((C' * ((((s.n j : ℝ) / s.W j) * ρ)) * (y - x)) ^ 2) := by
      intro j
      set p := s.parameters b hb hb' j
      set c := ((p.n : ℝ) / p.W) * ρ with hc
      have hcpos : 0 ≤ c := by positivity
      change ((R j).model.law.toMeasure.map (finiteEntireDeterminant p E (fullProfile q)))
        (interior (twoZeroSet k x y)) ≤ _
      rw [Measure.map_apply (measurable_finiteEntireDeterminant E _)
        isOpen_interior.measurableSet]
      have hsub : finiteEntireDeterminant p E (fullProfile q) ⁻¹' interior (twoZeroSet k x y) ⊆
          {H | (1 : ℝ≥0∞) < (physicalOrderedMarkedConfig p E H).spectral.measure
            (Ioo (-c * y) (-c * x))} ∪ {H | ¬ FiniteFacts p E q H} := by
        intro H hH
        by_cases hf : FiniteFacts p E q H
        · left
          obtain ⟨y₁, y₂, hne, h₁, h₂, hz₁, hz₂⟩ :=
            two_real_zeros_of_mem (mem_goodEntire_of_finiteFacts hf) (interior_subset hH)
          exact finite_two_zeros_spectral hρ hf hne h₁ h₂ hz₁ hz₂
        · exact Or.inr hf
      refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
      rw [ae_iff.mp (ae_finiteFacts (R j).model E q), add_zero]
      have hmap := Measure.le_map_apply (μ := (R j).model.law.toMeasure)
        (measurable_physicalOrderedMarkedConfig p E).aemeasurable
        {ξ : MarkedPointMeasure | (1 : ℝ≥0∞) < ξ.spectral.measure (Ioo (-c * y) (-c * x))}
      refine hmap.trans ?_
      have hcan := BlockBand.Model.Construction.finiteRealization_markedLaw_eq_canonical (R j) E
      have htwo := BlockBand.Counting.finiteRealization_markedLaw_Ioo_twoPoint_bound (R j) source
        E hρ (-c * y) (-c * x) (by nlinarith)
      rw [hcan] at htwo
      refine htwo.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
      have : p.physicalUnfoldedConstant source ρ = C' := rfl
      rw [this]
      change _ = (C' * (((p.n : ℝ) / p.W) * ρ) * (y - x)) ^ 2
      rw [← hc]
      ring
    have hlim : Tendsto (fun j => ENNReal.ofReal ((C' * ((((s.n j : ℝ) / s.W j) * ρ)) *
        (y - x)) ^ 2)) atTop (𝓝 (ENNReal.ofReal ((C' * (τ * ρ) * (y - x)) ^ 2))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp
        ((((hratio.const_mul C').mul_const (y - x)).pow 2))
    calc liminf (fun j => (μs j : Measure (EntireFunction (k + 1)))
          (interior (twoZeroSet k x y))) atTop
        ≤ liminf (fun j => ENNReal.ofReal ((C' * ((((s.n j : ℝ) / s.W j) * ρ)) *
            (y - x)) ^ 2)) atTop := liminf_le_liminf (.of_forall hbound)
      _ = ENNReal.ofReal ((C' * (τ * ρ) * (y - x)) ^ 2) := hlim.liminf_eq
  have hgrid := measure_iUnion_null_of_grid (μ : Measure (EntireFunction (k + 1))) (C' * (τ * ρ))
    (fun x y => interior (twoZeroSet k x y))
    (fun x y x' y' hx hy => interior_mono (twoZeroSet_mono hx hy)) hB
    (multipleZeroAt k) (fun x a ha => multipleZeroAt_subset_interior x ha)
  -- assemble
  rw [ae_iff]
  refine measure_mono_null ?_ (measure_union_null (measure_union_null hone hreal) hgrid)
  intro F hF'
  have hF : F ∉ goodEntire k := hF'
  by_cases h1 : F 0 = 1
  · have h0 : F 0 ≠ 0 := by rw [h1]; exact one_ne_zero
    by_cases h2 : RealRooted F
    · right
      have h3 : ¬ SimpleRealZeros F := fun h3 => hF ⟨⟨h0, h2⟩, h3⟩
      simp only [SimpleRealZeros, not_forall, not_not] at h3
      obtain ⟨x, hz, hd⟩ := h3
      exact mem_iUnion.mpr ⟨x, h0, hz, hd⟩
    · exact Or.inl (Or.inr ⟨h0, h2⟩)
  · exact Or.inl (Or.inl h1)

end BlockBand.Critical.JointRecovery
