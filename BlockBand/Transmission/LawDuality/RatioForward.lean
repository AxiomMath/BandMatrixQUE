module

public import BlockBand.Transmission.LawDuality.Entrance

/-!
# Duality principle, forward side: first consequences of the hypotheses

* **`integral_ratio_sub_eq`**: for a ratio martingale, `E F_z(μ_t) - E F_z(μ_s) =
  E ∫_s^t ratioDrift(u, z, μ_u) du` (the martingale clause with the constant test).
* **`continuousOn_integral_ratio`**: `t ↦ E F_{x,y}(μ_t)` is continuous on `(0, ∞)` for every
  `x ≥ 0`, `0 ≤ y < 1` (bounded weakly continuous `F`, a.s. continuous paths).
* **`transmissionRatio_cons`**: `F_{(x₀,x̃),(y₀,ỹ)} = F_{x₀,y₀}·F_{x̃,ỹ}`, and
  **`transmissionRatio_cons_zero`**: at the paired corner `x₀ = y₀ = 0` the ratio is `F_{x̃,ỹ}`
  (at a deleted pair the ratio is one).
* **`abs_transmissionRatio_cons_sub_le`**: `|F_{(x₀,x̃),(y₀,ỹ)}(ν) - F_{x̃,ỹ}(ν)| ≤
  (x₀ + y₀/(1-y₀))·ν[0,1]` (the corner error).
* `dualTransform_zero`, **`continuousOn_lifetime_of_dualLawValue`**: for `κ ≡ 0` the dual side
  of the dual transmission law is `P(ζ ≤ t)` and the left side is continuous in `t`, so the
  identity forces the lifetime `ζ` of the `p`-pair deletion law to have no atom in `(0, ∞)`:
  a dual-side input any proof of `RatioDualityPrinciple` has to supply.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.DualBoundary
open scoped NNReal ENNReal BoundedContinuousFunction

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {μ : ℝ → Ω → FiniteMeasure unitInterval}

theorem integrable_ratio_comp [IsFiniteMeasure P] {p : ℕ} {x y : Fin p → ℝ} (h : IsRatioRange x y)
    {ν : Ω → FiniteMeasure unitInterval} (hν : Measurable ν) :
    Integrable (fun ω => transmissionRatio x y (ν ω)) P :=
  Integrable.of_bound ((measurable_transmissionRatio_vec h).comp hν).aestronglyMeasurable 1
    (Eventually.of_forall fun ω => norm_transmissionRatio_le h (ν ω))

/-- **The expectation identity of the ratio martingale problem.** -/
theorem integral_ratio_sub_eq [IsFiniteMeasure P] {D0 E : ℝ} {κ : ℝ → ℝ}
    (hmeas : ∀ t, 0 < t → Measurable (μ t)) (hM : IsRatioMartingale D0 E κ P μ) {p : ℕ}
    {z : DualCoord p} (hz : z ∈ dualChamber p) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    ∫ ω, transmissionRatio z.1 z.2 (μ t ω) ∂P - ∫ ω, transmissionRatio z.1 z.2 (μ s ω) ∂P =
      ∫ ω, (∫ u in s..t, ratioDrift D0 E κ u z (μ u ω)) ∂P := by
  have ht : 0 < t := hs.trans_le hst
  obtain ⟨hI, horth⟩ := hM p z hz s t (mem_Ioi.2 hs) (mem_Ioi.2 ht) hst
  have h0 := horth 0 (fun l => l.elim0) (fun l => l.elim0) (fun l => l.elim0)
    (BoundedContinuousFunction.const _ 1)
  simp only [BoundedContinuousFunction.const_apply, one_smul] at h0
  have hr := IsRatioParameter.isRatioRange (show IsRatioParameter z.1 z.2 from hz)
  have hFt := integrable_ratio_comp (P := P) hr (hmeas t ht)
  have hFs := integrable_ratio_comp (P := P) hr (hmeas s hs)
  have e : (fun ω => ∫ u in s..t, ratioDrift D0 E κ u z (μ u ω)) = fun ω =>
      (transmissionRatio z.1 z.2 (μ t ω) - transmissionRatio z.1 z.2 (μ s ω)) -
        (transmissionRatio z.1 z.2 (μ t ω) - transmissionRatio z.1 z.2 (μ s ω) -
          ∫ u in s..t, ratioDrift D0 E κ u z (μ u ω)) := by
    funext ω; ring
  have hsub : Integrable (fun ω => transmissionRatio z.1 z.2 (μ t ω) -
      transmissionRatio z.1 z.2 (μ s ω)) P := hFt.sub hFs
  beta_reduce at hI
  rw [e, integral_sub hsub hI, integral_sub hFt hFs, h0, sub_zero]

/-- **`t ↦ E F_{x,y}(μ_t)` is continuous on `(0, ∞)`.** -/
theorem continuousOn_integral_ratio [IsFiniteMeasure P] (hmeas : ∀ t, 0 < t → Measurable (μ t))
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun t => μ t ω) (Ioi 0)) {p : ℕ} {x y : Fin p → ℝ}
    (h : IsRatioRange x y) :
    ContinuousOn (fun t => ∫ ω, transmissionRatio x y (μ t ω) ∂P) (Ioi 0) := by
  refine continuousOn_of_dominated (bound := fun _ => 1) (fun t ht => ?_) (fun t _ => ?_)
    (integrable_const 1) ?_
  · exact ((measurable_transmissionRatio_vec h).comp (hmeas t ht)).aestronglyMeasurable
  · exact Eventually.of_forall fun ω => norm_transmissionRatio_le h (μ t ω)
  · filter_upwards [hcont] with ω hω
    exact (continuous_transmissionRatio_vec h).comp_continuousOn hω

theorem isRatioRange_cons {q : ℕ} {x0 y0 : ℝ} {x y : Fin q → ℝ} (hx0 : 0 ≤ x0) (hy0 : 0 ≤ y0)
    (hy1 : y0 < 1) (h : IsRatioRange x y) :
    IsRatioRange (Fin.cons x0 x : Fin (q + 1) → ℝ) (Fin.cons y0 y) :=
  ⟨fun i => Fin.cases hx0 (fun j => h.1 j) i, fun i => Fin.cases ⟨hy0, hy1⟩ (fun j => h.2 j) i⟩

/-- **`F_{(x₀,x̃),(y₀,ỹ)} = F_{x₀,y₀}·F_{x̃,ỹ}`.** -/
theorem transmissionRatio_cons {q : ℕ} {x0 y0 : ℝ} {x y : Fin q → ℝ} (hx0 : 0 ≤ x0)
    (hy0 : 0 ≤ y0) (hy1 : y0 < 1) (h : IsRatioRange x y) (ν : FiniteMeasure unitInterval) :
    transmissionRatio (Fin.cons x0 x : Fin (q + 1) → ℝ) (Fin.cons y0 y) ν =
      transmissionRatio ![x0] ![y0] ν * transmissionRatio x y ν := by
  rw [transmissionRatio_eq_prod (isRatioRange_cons hx0 hy0 hy1 h), Fin.prod_univ_succ,
    transmissionRatio_eq_prod h]
  simp

theorem transmissionRatio_zero_zero (ν : FiniteMeasure unitInterval) :
    transmissionRatio ![(0 : ℝ)] ![0] ν = 1 := by
  unfold transmissionRatio
  have : (fun t : unitInterval => ratioIntegrand ![(0 : ℝ)] ![0] (t : ℝ)) = fun _ => 0 := by
    funext t; rw [ratioIntegrand_one]; split_ifs <;> simp
  rw [this, integral_zero, Real.exp_zero]

/-- **At the paired corner the ratio is that of the survivors.** -/
theorem transmissionRatio_cons_zero {q : ℕ} {x y : Fin q → ℝ} (h : IsRatioRange x y)
    (ν : FiniteMeasure unitInterval) :
    transmissionRatio (Fin.cons 0 x : Fin (q + 1) → ℝ) (Fin.cons 0 y) ν = transmissionRatio x y ν := by
  rw [transmissionRatio_cons le_rfl le_rfl zero_lt_one h, transmissionRatio_zero_zero, one_mul]

/-- **The corner error**: `|F_{(x₀,x̃),(y₀,ỹ)}(ν) - F_{x̃,ỹ}(ν)| ≤ (x₀ + y₀/(1-y₀))·ν[0,1]`. -/
theorem abs_transmissionRatio_cons_sub_le {q : ℕ} {x0 y0 : ℝ} {x y : Fin q → ℝ} (hx0 : 0 ≤ x0)
    (hy0 : 0 ≤ y0) (hy1 : y0 < 1) (h : IsRatioRange x y) (ν : FiniteMeasure unitInterval) :
    |transmissionRatio (Fin.cons x0 x : Fin (q + 1) → ℝ) (Fin.cons y0 y) ν -
        transmissionRatio x y ν| ≤ (x0 + y0 / (1 - y0)) * (ν : Measure unitInterval).real univ := by
  rw [transmissionRatio_cons hx0 hy0 hy1 h]
  set a := ∫ t, ratioIntegrand ![x0] ![y0] (t : ℝ) ∂(ν : Measure unitInterval)
  have hF : transmissionRatio ![x0] ![y0] ν = Real.exp a := rfl
  have hG := transmissionRatio_mem_vec h ν
  have ha : -((x0 + y0 / (1 - y0)) * (ν : Measure unitInterval).real univ) ≤ a := by
    have := integral_mono (integrable_const (μ := (ν : Measure unitInterval)) (-(x0 + y0 / (1 - y0))))
      ((ratioBCF hx0 hy0 hy1).integrable (ν : Measure unitInterval))
      fun t => (ratioIntegrand_bounds hx0 hy0 hy1 t.2.1 t.2.2).1
    rw [integral_const, smul_eq_mul] at this
    have e : ∫ t, (ratioBCF hx0 hy0 hy1) t ∂(ν : Measure unitInterval) = a := rfl
    rw [e] at this
    linarith
  have ha0 : a ≤ 0 := integral_nonpos fun t => (ratioIntegrand_bounds hx0 hy0 hy1 t.2.1 t.2.2).2
  have h1 : Real.exp a ≤ 1 := Real.exp_le_one_iff.2 ha0
  have h2 := Real.add_one_le_exp a
  rw [hF, show Real.exp a * transmissionRatio x y ν - transmissionRatio x y ν =
    -((1 - Real.exp a) * transmissionRatio x y ν) by ring, abs_neg,
    abs_of_nonneg (mul_nonneg (by linarith) hG.1.le)]
  nlinarith

/-- The homogeneous dual transform is the distribution function of the lifetime `ζ`. -/
theorem dualTransform_zero {Ω' : Type*} [MeasurableSpace Ω'] (E t : ℝ) (P' : Measure Ω')
    (N : ℝ≥0 → Ω' → ℕ) (X Y : ℝ≥0 → Ω' → ℕ → ℝ) :
    dualTransform E (fun _ => 0) t P' N X Y =
      ∫ ω, (if dualExtinction N ω ≤ ENNReal.ofReal t then (1 : ℝ) else 0) ∂P' := by
  simp [dualTransform, absorptionRate]

/-- **The dual identity forces an atomless lifetime.** If a process with
measurable marginals and a.s. continuous paths satisfies the conclusion of
`RatioDualityPrinciple` for `κ ≡ 0`, then for every realization of the dual deletion law the
distribution function `t ↦ P(ζ ≤ t)` is continuous on `(0, ∞)`. So any proof of
`RatioDualityPrinciple` (applied to a process satisfying its hypotheses) must establish that
the lifetime of the `p`-pair deletion law has no atom in `(0, ∞)`. -/
theorem continuousOn_lifetime_of_dualLawValue [IsFiniteMeasure P]
    (hmeas : ∀ t, 0 < t → Measurable (μ t))
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun t => μ t ω) (Ioi 0)) {E D0 : ℝ} {p : ℕ}
    {x y : Fin p → ℝ} (hxy : IsRatioParameter x y)
    (hlaw : ∀ t : ℝ, 0 < t →
      DualLawValue E (fun _ => 0) t D0 x y (∫ ω, transmissionRatio x y (μ t ω) ∂P))
    {Ω' : Type} {m : MeasurableSpace Ω'} {𝓖 : Filtration ℝ≥0 m} {P' : Measure Ω'}
    {N : ℝ≥0 → Ω' → ℕ} {X Y : ℝ≥0 → Ω' → ℕ → ℝ} (hD : IsDualDeletionProcess P' 𝓖 D0 x y N X Y) :
    ContinuousOn (fun t : ℝ =>
      ∫ ω, (if dualExtinction N ω ≤ ENNReal.ofReal t then (1 : ℝ) else 0) ∂P') (Ioi 0) := by
  refine (continuousOn_integral_ratio hmeas hcont (IsRatioParameter.isRatioRange hxy)).congr fun t ht => ?_
  rw [← dualTransform_zero E t P' N X Y]
  exact hlaw t ht Ω' m 𝓖 P' N X Y hD

end BlockBand.Transmission.LawDuality
