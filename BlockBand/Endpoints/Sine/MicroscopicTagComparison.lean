module

public import BlockBand.Endpoints.Sine.MicroscopicTagLipschitz
public import Mathlib.Topology.ContinuousMap.Weierstrass
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# The physical microscopic tag comparison

Theorem (`microscopicTagComparison`): `MicroscopicTagComparisonStatement`. For fixed
`0 < b < 1/2`, bulk `-2 < E < 2`, smooth compactly supported (signed) `w`, `Φ ∈ C_b([0,∞))`,
every `τ > 0`, critical sequence `n/W → τ` and exact physical models, for every `ε > 0`,
eventually, for every physical block `k`,
`|E Σ_α w(u_α)Φ(n p_{αk}) - ∫ w(u) E_{path,h,K}Φ(Z_{r;K}/M_r)(e(u)) du| ≤ ε`, `r = n - 3`, the
path expectation over the matched-lead path prior `growthPathLaw W b` and independent
`h ~ CN(0, I_{2W})`, `K` uniform on the `r` interior positions. The hypotheses are
`MicroscopicTagLeadComparison` (the lead comparison for nonnegative `w` and Lipschitz `Φ`, before
the ports are removed) and `NegativeClockContract` (positivity of every subsequential limit of
`h*Y^{int}h/W²`).

Proof. Starting from the lead comparison `MicroscopicTagLeadComparison`, the ports are removed
(`portFraction_uniform`: Ward bound `h*Y^{port}h ≤ ‖h‖²/(Im z_b)²`, `E‖h‖² = 2W`, lower tail of
the interior clock from `NegativeClockContract` and Prokhorov), then the tag deletion identity and
the change from `n` to `r` positions (cost `O(1/n)`) give the Lipschitz case. For general
bounded continuous tests (this file), a Weierstrass polynomial, clamped to `[0, R₀]`,
approximates `Φ` by a Lipschitz test on `[0, R₀]`; the tags with scaled mass `> R₀/2` are
controlled by a Lipschitz bump `ψ` with `ψ(z) ≤ 2z/R₀`, whose path expectation is `≤ 2/R₀`
because the tag ratios average to one, and whose physical expectation is compared through the
Lipschitz case itself. Finally a signed `w` is written `w = ϖ - (ϖ - w)` with a smooth compactly
supported `ϖ ≥ |w|`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Model.Construction
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open scoped ENNReal NNReal BoundedContinuousFunction Polynomial

/-!
## Tests
-/

theorem abs_max_zero_sub_le (a b : ℝ) : |max 0 a - max 0 b| ≤ |a - b| := by
  rw [max_comm 0 a, max_comm 0 b]; exact abs_max_sub_max_le_abs a b 0

/-- The constant test `1`. -/
def oneTest : Set.Ici (0 : ℝ) →ᵇ ℝ := BoundedContinuousFunction.const _ 1

theorem lipschitz_oneTest : LipschitzWith 0 oneTest :=
  LipschitzWith.of_dist_le_mul fun x y => by simp [oneTest]

/-- The Lipschitz tail bump `ψ_R(z) = clamp(2z/R - 1, 0, 1)`. -/
def tailBump (R : ℝ) : Set.Ici (0 : ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun z => max 0 (min 1 (2 * (z : ℝ) / R - 1))) (by fun_prop) 1 (fun z => by
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · linarith [le_max_left 0 (min 1 (2 * (z : ℝ) / R - 1))]
      · exact max_le zero_le_one (min_le_left _ _))

theorem tailBump_apply (R : ℝ) (z : Set.Ici (0 : ℝ)) :
    tailBump R z = max 0 (min 1 (2 * (z : ℝ) / R - 1)) := rfl

theorem tailBump_nonneg (R : ℝ) (z : Set.Ici (0 : ℝ)) : 0 ≤ tailBump R z := le_max_left _ _

theorem tailBump_le {R : ℝ} (hR : 0 < R) (z : Set.Ici (0 : ℝ)) :
    tailBump R z ≤ 2 / R * (z : ℝ) := by
  rw [tailBump_apply]
  have hz : 0 ≤ (z : ℝ) := z.2
  have h0 : 0 ≤ 2 / R * (z : ℝ) := by positivity
  refine max_le h0 ((min_le_right _ _).trans ?_)
  rw [mul_div_right_comm, div_mul_eq_mul_div]; linarith

theorem tailBump_eq_one {R : ℝ} (hR : 0 < R) {z : Set.Ici (0 : ℝ)} (hz : R ≤ (z : ℝ)) :
    tailBump R z = 1 := by
  rw [tailBump_apply]
  have : 1 ≤ 2 * (z : ℝ) / R - 1 := by
    rw [le_sub_iff_add_le, le_div_iff₀ hR]; linarith
  rw [min_eq_left this, max_eq_right zero_le_one]

theorem lipschitz_tailBump {R : ℝ} (hR : 0 < R) :
    LipschitzWith (Real.toNNReal (2 / R)) (tailBump R) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, Subtype.dist_eq, Real.dist_eq, tailBump_apply, tailBump_apply,
    Real.coe_toNNReal _ (by positivity)]
  refine (abs_max_zero_sub_le _ _).trans ?_
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  rw [sub_self, abs_zero, max_eq_right (abs_nonneg _)]
  rw [show 2 * (x : ℝ) / R - 1 - (2 * (y : ℝ) / R - 1) = 2 / R * ((x : ℝ) - y) by ring, abs_mul,
    abs_of_pos (by positivity)]

/-- A Lipschitz test uniformly within `δ` of `Φ` on `[0, R]` and bounded by `‖Φ‖ + δ`: a
Weierstrass polynomial evaluated at the clamp to `[0, R]`. -/
theorem exists_lipschitz_approx (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) :
    ∃ g : Set.Ici (0 : ℝ) →ᵇ ℝ, (∃ L : ℝ≥0, LipschitzWith L g) ∧
      (∀ z : Set.Ici (0 : ℝ), (z : ℝ) ≤ R → |Φ z - g z| ≤ δ) ∧ ‖g‖ ≤ ‖Φ‖ + δ := by
  have hf : ContinuousOn (fun x : ℝ => Φ (Set.projIci 0 x)) (Set.Icc 0 R) :=
    (Φ.continuous.comp continuous_projIci_zero).continuousOn
  obtain ⟨P, hP⟩ := exists_polynomial_near_of_continuousOn 0 R _ hf δ hδ
  set c : ℝ → ℝ := fun x => (Set.projIcc 0 R hR.le x : ℝ)
  have hc : Continuous c := continuous_subtype_val.comp continuous_projIcc
  have hcmem : ∀ x, c x ∈ Set.Icc 0 R := fun x => (Set.projIcc 0 R hR.le x).2
  have hPb : ∀ x, |P.eval (c x)| ≤ ‖Φ‖ + δ := by
    intro x
    have h1 := (hP (c x) (hcmem x)).le
    have h2 := norm_test_le Φ (Set.projIci 0 (c x))
    calc |P.eval (c x)| ≤ |P.eval (c x) - Φ (Set.projIci 0 (c x))| + |Φ (Set.projIci 0 (c x))| := by
          have := abs_add_le (P.eval (c x) - Φ (Set.projIci 0 (c x))) (Φ (Set.projIci 0 (c x)))
          rwa [sub_add_cancel] at this
      _ ≤ δ + ‖Φ‖ := add_le_add h1 h2
      _ = ‖Φ‖ + δ := add_comm _ _
  let g : Set.Ici (0 : ℝ) →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun z => P.eval (c (z : ℝ))) (P.continuous.comp (hc.comp continuous_subtype_val)) (‖Φ‖ + δ)
    (fun z => by rw [Real.norm_eq_abs]; exact hPb _)
  have hgapp : ∀ z, g z = P.eval (c (z : ℝ)) := fun z => rfl
  refine ⟨g, ?_, ?_, ?_⟩
  · have hPc : ContDiffOn ℝ 1 (fun x : ℝ => P.eval x) (Set.Icc 0 R) := by
      have := (Polynomial.contDiff_aeval (R := ℝ) (𝕜 := ℝ) P 1).contDiffOn (s := Set.Icc 0 R)
      refine this.congr fun x _ => ?_
      simp [Polynomial.coe_aeval_eq_eval]
    obtain ⟨K, hK⟩ := hPc.exists_lipschitzOnWith one_ne_zero (convex_Icc 0 R) isCompact_Icc
    refine ⟨K, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    rw [hgapp, hgapp]
    refine (hK.dist_le_mul _ (hcmem _) _ (hcmem _)).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ K.2
    rw [Real.dist_eq, Subtype.dist_eq, Real.dist_eq]
    simp only [c, Set.coe_projIcc]
    refine (abs_max_zero_sub_le _ _).trans ?_
    refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
    rw [sub_self, abs_zero, max_eq_right (abs_nonneg _)]
  · intro z hz
    rw [hgapp]
    have hzI : (z : ℝ) ∈ Set.Icc 0 R := ⟨z.2, hz⟩
    have hcz : c (z : ℝ) = z := by simp only [c, Set.projIcc_of_mem _ hzI]
    rw [hcz, abs_sub_comm]
    have h1 := (hP z hzI).le
    rwa [Set.projIci_of_mem (show (z : ℝ) ∈ Set.Ici 0 from z.2)] at h1
  · refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun z => ?_
    rw [hgapp, Real.norm_eq_abs]; exact hPb _

/-- Pointwise test bound: `|Φ - g| ≤ δ + (2‖Φ‖ + δ)ψ_R`. -/
theorem test_sub_approx_le (Φ g : Set.Ici (0 : ℝ) →ᵇ ℝ) {R δ : ℝ} (hR : 0 < R) (hδ : 0 ≤ δ)
    (hg : ∀ z : Set.Ici (0 : ℝ), (z : ℝ) ≤ R → |Φ z - g z| ≤ δ) (hgn : ‖g‖ ≤ ‖Φ‖ + δ)
    (z : Set.Ici (0 : ℝ)) :
    |Φ z - g z| ≤ δ + (2 * ‖Φ‖ + δ) * tailBump R z := by
  have hψ := tailBump_nonneg R z
  by_cases hz : (z : ℝ) ≤ R
  · have := hg z hz
    have : 0 ≤ (2 * ‖Φ‖ + δ) * tailBump R z := mul_nonneg (by positivity) hψ
    linarith
  · rw [tailBump_eq_one hR (le_of_lt (not_le.1 hz)), mul_one]
    have h1 := norm_test_le Φ z
    have h2 := norm_test_le g z
    calc |Φ z - g z| ≤ |Φ z| + |g z| := abs_sub _ _
      _ ≤ ‖Φ‖ + (‖Φ‖ + δ) := add_le_add h1 (h2.trans hgn)
      _ ≤ δ + (2 * ‖Φ‖ + δ) := by linarith

/-!
## The two sides as positive functionals
-/

theorem measurable_microCoord (p : Parameters) (E : ℝ) : Measurable (microCoord p E) := by
  unfold microCoord; fun_prop

theorem physicalTagSide_abs_sub_le (p : Parameters) (model : p.GaussianRingModel) (E : ℝ)
    {w : ℝ → ℝ} (hwc : Continuous w) (hw0 : ∀ u, 0 ≤ w u) {B : ℝ} (hB : ∀ u, w u ≤ B)
    (k : ZMod p.n) (Φ₁ Φ₂ Φ₃ : Set.Ici (0 : ℝ) →ᵇ ℝ) {δ K : ℝ}
    (hbd : ∀ y, |Φ₁ y - Φ₂ y| ≤ δ + K * Φ₃ y) :
    |physicalTagSide p model E w Φ₁ k - physicalTagSide p model E w Φ₂ k| ≤
      δ * physicalTagSide p model E w oneTest k + K * physicalTagSide p model E w Φ₃ k := by
  have h := abs_integral_sum_test_sub_le (model.law : Measure p.SiteMatrix)
    (fun H α => w (microCoord p E (physicalOrderedEigenvalue p H α)))
    (fun H α => (p.n : ℝ) * physicalOrderedBlockMass p H α k) (fun _ _ => hw0 _)
    (fun α => hwc.measurable.comp ((measurable_microCoord p E).comp
      (measurable_physicalOrderedEigenvalue p α)))
    (fun α => measurable_const.mul (measurable_physicalOrderedBlockMass p α k))
    (fun _ _ => hB _) Φ₁ Φ₂ Φ₃ hbd
  have h1 : physicalTagSide p model E w oneTest k = ∫ H, ∑ α : Fin p.N,
      w (microCoord p E (physicalOrderedEigenvalue p H α)) ∂(model.law : Measure p.SiteMatrix) := by
    simp [physicalTagSide, oneTest]
  rw [h1]
  exact h

theorem physicalTagSide_nonneg (p : Parameters) (model : p.GaussianRingModel) (E : ℝ)
    {w : ℝ → ℝ} (hw0 : ∀ u, 0 ≤ w u) {Φ : Set.Ici (0 : ℝ) →ᵇ ℝ} (hΦ : ∀ z, 0 ≤ Φ z)
    (k : ZMod p.n) : 0 ≤ physicalTagSide p model E w Φ k :=
  integral_nonneg fun _ => Finset.sum_nonneg fun _ _ => mul_nonneg (hw0 _) (hΦ _)

theorem pathTagExpect_oneTest (b e : ℝ) (W : ℕ) {r : ℕ} (hr : 0 < r) :
    pathTagExpect b e W r oneTest = 1 := by
  have := isProbabilityMeasure_probedClockLaw W b
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  simp [pathTagExpect, oneTest, hr']

theorem pathTagExpect_abs_sub_le (b e : ℝ) {W r : ℕ} (hr : 0 < r)
    (Φ₁ Φ₂ Φ₃ : Set.Ici (0 : ℝ) →ᵇ ℝ) {δ K : ℝ}
    (hbd : ∀ y, |Φ₁ y - Φ₂ y| ≤ δ + K * Φ₃ y) :
    |pathTagExpect b e W r Φ₁ - pathTagExpect b e W r Φ₂| ≤
      δ * pathTagExpect b e W r oneTest + K * pathTagExpect b e W r Φ₃ := by
  have := isProbabilityMeasure_probedClockLaw W b
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have h := abs_integral_sum_test_sub_le (probedClockLaw W b)
    (fun _ (K : Fin r) => (r : ℝ)⁻¹) (fun x K => tagClock b e W r K x / meanClock b e W r x)
    (fun _ _ => by positivity) (fun _ => measurable_const)
    (fun K => measurable_tagRatio_of b W r K measurable_const measurable_id)
    (fun _ _ => le_rfl) Φ₁ Φ₂ Φ₃ hbd
  have hform : ∀ Φ : Set.Ici (0 : ℝ) →ᵇ ℝ, pathTagExpect b e W r Φ = ∫ x, ∑ K : Fin r,
      (r : ℝ)⁻¹ * Φ (Set.projIci 0 (tagClock b e W r K x / meanClock b e W r x))
        ∂probedClockLaw W b := by
    intro Φ; simp only [pathTagExpect, Finset.mul_sum]
  rw [hform, hform, hform Φ₃, pathTagExpect_oneTest b e W hr]
  have h1 : ∫ x : GrowthPath W × (Fin 2 × Fin W → ℂ), ∑ _K : Fin r, (r : ℝ)⁻¹
      ∂probedClockLaw W b = 1 := by simp [hr'.ne']
  rw [h1] at h
  exact h

theorem pathTagSide_oneTest (p : Parameters) (E : ℝ) (w : ℝ → ℝ) :
    pathTagSide p E w oneTest = ∫ u, w u := by
  have hr : 0 < p.n - 3 := by have := p.n_ge_four; omega
  simp only [pathTagSide, pathTagExpect_oneTest _ _ _ hr, mul_one]

theorem pathTagSide_abs_sub_le (p : Parameters) (E : ℝ) {w : ℝ → ℝ} (hw0 : ∀ u, 0 ≤ w u)
    (hwi : Integrable w) (Φ₁ Φ₂ Φ₃ : Set.Ici (0 : ℝ) →ᵇ ℝ) {δ K : ℝ}
    (hbd : ∀ y, |Φ₁ y - Φ₂ y| ≤ δ + K * Φ₃ y) :
    |pathTagSide p E w Φ₁ - pathTagSide p E w Φ₂| ≤
      δ * pathTagSide p E w oneTest + K * pathTagSide p E w Φ₃ := by
  have hr : 0 < p.n - 3 := by have := p.n_ge_four; omega
  set C := max (max ‖Φ₁‖ ‖Φ₂‖) (max ‖oneTest‖ ‖Φ₃‖)
  have hb : ∀ Φ : Set.Ici (0 : ℝ) →ᵇ ℝ, ‖Φ‖ ≤ C → ∀ u,
      |pathTagExpect p.b (microEnergy p E u) p.W (p.n - 3) Φ| ≤ C :=
    fun Φ hΦ u => (abs_pathTagExpect_le _ _ _ _ Φ).trans hΦ
  exact abs_integral_weight_sub_le hw0 hwi (stronglyMeasurable_pathTagExpect p E Φ₁)
    (stronglyMeasurable_pathTagExpect p E Φ₂) (stronglyMeasurable_pathTagExpect p E oneTest)
    (stronglyMeasurable_pathTagExpect p E Φ₃)
    (hb Φ₁ ((le_max_left _ _).trans (le_max_left _ _)))
    (hb Φ₂ ((le_max_right _ _).trans (le_max_left _ _)))
    (hb oneTest ((le_max_left _ _).trans (le_max_right _ _)))
    (hb Φ₃ ((le_max_right _ _).trans (le_max_right _ _)))
    (fun u => pathTagExpect_abs_sub_le _ _ hr Φ₁ Φ₂ Φ₃ hbd)

/-- The tail of the path side: `∫ w E ψ_R(Z/M) ≤ (2/R) ∫ w`. -/
theorem pathTagSide_tailBump_le (p : Parameters) (E : ℝ) {w : ℝ → ℝ} (hw0 : ∀ u, 0 ≤ w u)
    (hwi : Integrable w) {R : ℝ} (hR : 0 < R) :
    pathTagSide p E w (tailBump R) ≤ 2 / R * ∫ u, w u := by
  have hexp : ∀ u, pathTagExpect p.b (microEnergy p E u) p.W (p.n - 3) (tailBump R) ≤ 2 / R := by
    intro u
    have := isProbabilityMeasure_probedClockLaw p.W p.b
    rw [pathTagExpect_eq]
    refine (integral_mono_of_nonneg ?_ (integrable_const (2 / R)) ?_).trans (by simp)
    · exact Eventually.of_forall fun x => mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
        (Finset.sum_nonneg fun K _ => tailBump_nonneg R _)
    · refine Eventually.of_forall fun x => ?_
      have hs := sum_tagRatio_le (b := p.b) (e := microEnergy p E u) (r := p.n - 3) p.W_pos x
      unfold pathIntegrand
      calc ((p.n - 3 : ℕ) : ℝ)⁻¹ * ∑ K : Fin (p.n - 3), tailBump R (Set.projIci 0
            (tagClock p.b (microEnergy p E u) p.W (p.n - 3) K x /
              meanClock p.b (microEnergy p E u) p.W (p.n - 3) x))
          ≤ ((p.n - 3 : ℕ) : ℝ)⁻¹ * ∑ K : Fin (p.n - 3), 2 / R *
            (tagClock p.b (microEnergy p E u) p.W (p.n - 3) K x /
              meanClock p.b (microEnergy p E u) p.W (p.n - 3) x) := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun K _ => ?_) (by positivity)
            refine (tailBump_le hR _).trans (le_of_eq ?_)
            rw [Set.coe_projIci, max_eq_right (tagRatio_nonneg p.W_pos K x)]
        _ = 2 / R * (((p.n - 3 : ℕ) : ℝ)⁻¹ * ∑ K : Fin (p.n - 3),
            tagClock p.b (microEnergy p E u) p.W (p.n - 3) K x /
              meanClock p.b (microEnergy p E u) p.W (p.n - 3) x) := by
            rw [← Finset.mul_sum]; ring
        _ ≤ 2 / R * 1 := mul_le_mul_of_nonneg_left hs (by positivity)
        _ = 2 / R := mul_one _
  unfold pathTagSide
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg ?_ (hwi.const_mul _) (Eventually.of_forall fun u => ?_)
  · refine Eventually.of_forall fun u => mul_nonneg (hw0 u) ?_
    have := isProbabilityMeasure_probedClockLaw p.W p.b
    rw [pathTagExpect_eq]
    exact integral_nonneg fun x => mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun K _ => tailBump_nonneg R _)
  · calc w u * pathTagExpect p.b (microEnergy p E u) p.W (p.n - 3) (tailBump R) ≤ w u * (2 / R) :=
        mul_le_mul_of_nonneg_left (hexp u) (hw0 u)
      _ = 2 / R * w u := mul_comm _ _

/-!
## General bounded continuous tests
-/

/-- The comparison for every `Φ ∈ C_b([0,∞))` and nonnegative `w`. -/
theorem microscopicTag_nonneg (hIso : MicroscopicTagLeadComparison)
    (hNeg : NegativeClockContract) (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (E : ℝ)
    (hE1 : -2 < E) (hE2 : E < 2) (w : ℝ → ℝ) (hws : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w)
    (hwc : HasCompactSupport w) (hw0 : ∀ u, 0 ≤ w u) (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) (τ : ℝ)
    (hτ : 0 < τ) (s : CriticalSequence τ) (R : ∀ j, (s.parameters b hb hb' j).GaussianRingModel)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ j in atTop, ∀ k : ZMod (s.parameters b hb hb' j).n,
      |physicalTagSide (s.parameters b hb hb' j) (R j) E w Φ k -
          pathTagSide (s.parameters b hb hb' j) E w Φ| ≤ ε := by
  have hwi : Integrable w := hws.continuous.integrable_of_hasCompactSupport hwc
  obtain ⟨B, hB⟩ := hwc.exists_bound_of_continuous hws.continuous
  have hB' : ∀ u, w u ≤ B := fun u => (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact hB u)
  set Iw := ∫ u, w u
  have hIw : 0 ≤ Iw := integral_nonneg hw0
  set K₁ := 2 * ‖Φ‖ + 1
  have hK₁ : 0 < K₁ := by positivity
  set δ := min 1 (ε / (8 * (Iw + 1)))
  have hδ : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ ≤ ε / (8 * (Iw + 1)) := min_le_right _ _
  set R₀ := 16 * K₁ * (Iw + 1) / ε + 1
  have hR₀ : 0 < R₀ := by positivity
  set ε₁ := min 1 (ε / (4 * (K₁ + 1)))
  have hε₁ : 0 < ε₁ := lt_min one_pos (by positivity)
  have hε₁1 : ε₁ ≤ 1 := min_le_left _ _
  have hε₁ε : ε₁ ≤ ε / (4 * (K₁ + 1)) := min_le_right _ _
  obtain ⟨g, hgL, hgΦ, hgn⟩ := exists_lipschitz_approx Φ hR₀ hδ
  have hbd := test_sub_approx_le Φ g hR₀ hδ.le hgΦ hgn
  have hg := microscopicTag_lipschitz hIso hNeg b hb hb' E hE1 hE2 w hws hwc hw0 g hgL τ hτ s R
    ε₁ hε₁
  have h1 := microscopicTag_lipschitz hIso hNeg b hb hb' E hE1 hE2 w hws hwc hw0 oneTest
    ⟨0, lipschitz_oneTest⟩ τ hτ s R ε₁ hε₁
  have hψ := microscopicTag_lipschitz hIso hNeg b hb hb' E hE1 hE2 w hws hwc hw0 (tailBump R₀)
    ⟨_, lipschitz_tailBump hR₀⟩ τ hτ s R ε₁ hε₁
  filter_upwards [hg, h1, hψ] with j hgj h1j hψj k
  have hA := physicalTagSide_abs_sub_le (s.parameters b hb hb' j) (R j) E hws.continuous hw0 hB'
    k Φ g (tailBump R₀) hbd
  have hBp := pathTagSide_abs_sub_le (s.parameters b hb hb' j) E hw0 hwi Φ g (tailBump R₀) hbd
  rw [pathTagSide_oneTest] at hBp
  have hψp := pathTagSide_tailBump_le (s.parameters b hb hb' j) E hw0 hwi hR₀
  have h1p := h1j k
  rw [pathTagSide_oneTest] at h1p
  have hgk := hgj k
  have hψk := hψj k
  set aΦ := physicalTagSide (s.parameters b hb hb' j) (R j) E w Φ k
  set ag := physicalTagSide (s.parameters b hb hb' j) (R j) E w g k
  set a1 := physicalTagSide (s.parameters b hb hb' j) (R j) E w oneTest k
  set aψ := physicalTagSide (s.parameters b hb hb' j) (R j) E w (tailBump R₀) k
  set bΦ := pathTagSide (s.parameters b hb hb' j) E w Φ
  set bg := pathTagSide (s.parameters b hb hb' j) E w g
  set bψ := pathTagSide (s.parameters b hb hb' j) E w (tailBump R₀)
  have hbψ0 : 0 ≤ bψ := by
    unfold bψ pathTagSide
    refine integral_nonneg fun u => mul_nonneg (hw0 u) ?_
    have := isProbabilityMeasure_probedClockLaw (s.parameters b hb hb' j).W
      (s.parameters b hb hb' j).b
    rw [pathTagExpect_eq]
    exact integral_nonneg fun x => mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun K _ => tailBump_nonneg R₀ _)
  set K := 2 * ‖Φ‖ + δ
  have hK : 0 ≤ K := by positivity
  have hKK : K ≤ K₁ := by unfold K K₁; linarith
  have ha1 : a1 ≤ Iw + ε₁ := by linarith [(abs_le.1 h1p).1, (abs_le.1 h1p).2]
  have haψ : aψ ≤ bψ + ε₁ := by linarith [(abs_le.1 hψk).1, (abs_le.1 hψk).2]
  have hbψ : bψ ≤ 2 / R₀ * Iw := hψp
  -- the tail term
  have htail : K * (aψ + bψ) ≤ K₁ * (4 / R₀ * Iw) + K₁ * ε₁ := by
    have : aψ + bψ ≤ 4 / R₀ * Iw + ε₁ := by
      have : 2 / R₀ * Iw + 2 / R₀ * Iw = 4 / R₀ * Iw := by ring
      linarith
    have hpos : 0 ≤ aψ + bψ :=
      add_nonneg (physicalTagSide_nonneg _ _ E hw0 (tailBump_nonneg R₀) k) hbψ0
    calc K * (aψ + bψ) ≤ K₁ * (aψ + bψ) := mul_le_mul_of_nonneg_right hKK hpos
      _ ≤ K₁ * (4 / R₀ * Iw + ε₁) := mul_le_mul_of_nonneg_left this hK₁.le
      _ = _ := by ring
  have hR₀' : K₁ * (4 / R₀ * Iw) ≤ ε / 4 := by
    rw [show K₁ * (4 / R₀ * Iw) = 4 * K₁ * Iw / R₀ by ring, div_le_iff₀ hR₀]
    have : 16 * K₁ * (Iw + 1) / ε ≤ R₀ - 1 := by unfold R₀; linarith
    rw [div_le_iff₀ hε] at this
    nlinarith
  have hε₁' : K₁ * ε₁ + ε₁ ≤ ε / 4 := by
    have : (K₁ + 1) * ε₁ ≤ ε / 4 := by
      calc (K₁ + 1) * ε₁ ≤ (K₁ + 1) * (ε / (4 * (K₁ + 1))) :=
            mul_le_mul_of_nonneg_left hε₁ε (by positivity)
        _ = ε / 4 := by field_simp
    linarith
  have hδ' : δ * (a1 + Iw) ≤ ε / 4 := by
    have : a1 + Iw ≤ 2 * (Iw + 1) := by linarith
    have ha10 : 0 ≤ a1 + Iw :=
      add_nonneg (physicalTagSide_nonneg _ _ E hw0 (fun z => by simp [oneTest]) k) hIw
    calc δ * (a1 + Iw) ≤ δ * (2 * (Iw + 1)) := mul_le_mul_of_nonneg_left this hδ.le
      _ ≤ ε / (8 * (Iw + 1)) * (2 * (Iw + 1)) := mul_le_mul_of_nonneg_right hδε (by positivity)
      _ = ε / 4 := by field_simp; ring
  calc |aΦ - bΦ| ≤ |aΦ - ag| + |ag - bg| + |bg - bΦ| :=
        (abs_sub_le aΦ ag bΦ).trans (by have := abs_sub_le ag bg bΦ; linarith)
    _ ≤ (δ * a1 + K * aψ) + ε₁ + (δ * Iw + K * bψ) := by
        refine add_le_add (add_le_add hA hgk) ?_
        rw [abs_sub_comm]; exact hBp
    _ = δ * (a1 + Iw) + K * (aψ + bψ) + ε₁ := by ring
    _ ≤ ε / 4 + (K₁ * (4 / R₀ * Iw) + K₁ * ε₁) + ε₁ := by gcongr
    _ ≤ ε := by linarith

/-!
## Signed weights and the proposition
-/

/-- A smooth compactly supported `ϖ ≥ |w|`. -/
theorem exists_smooth_dominating {w : ℝ → ℝ} (hws : Continuous w) (hwc : HasCompactSupport w) :
    ∃ ϖ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ϖ ∧ HasCompactSupport ϖ ∧
      ∀ u, |w u| ≤ ϖ u := by
  obtain ⟨R₀, hR₀⟩ := exists_bound_of_hasCompactSupport hwc
  obtain ⟨M, hM⟩ := hwc.exists_bound_of_continuous hws
  let φ : ContDiffBump (0 : ℝ) := ⟨|R₀| + 1, |R₀| + 2, by positivity, by linarith⟩
  refine ⟨fun u => max M 0 * φ u, contDiff_const.mul φ.contDiff,
    φ.hasCompactSupport.mul_left, fun u => ?_⟩
  by_cases hu : u ∈ Set.Icc (-R₀) R₀
  · have hmem : u ∈ Metric.closedBall (0 : ℝ) (|R₀| + 1) := by
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le]
      constructor <;> linarith [hu.1, hu.2, le_abs_self R₀, neg_abs_le R₀]
    change |w u| ≤ max M 0 * φ u
    rw [φ.one_of_mem_closedBall hmem, mul_one, ← Real.norm_eq_abs]
    exact (hM u).trans (le_max_left _ _)
  · rw [hR₀ u hu, abs_zero]
    exact mul_nonneg (le_max_right _ _) φ.nonneg

theorem integrable_physicalIntegrand (p : Parameters) (model : p.GaussianRingModel) (E : ℝ)
    {w : ℝ → ℝ} (hws : Continuous w) (hwc : HasCompactSupport w) (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ)
    (k : ZMod p.n) :
    Integrable (fun H => ∑ α : Fin p.N, w (microCoord p E (physicalOrderedEigenvalue p H α)) *
      Φ (Set.projIci 0 ((p.n : ℝ) * physicalOrderedBlockMass p H α k)))
      (model.law : Measure p.SiteMatrix) := by
  obtain ⟨B, hB⟩ := hwc.exists_bound_of_continuous hws
  refine integrable_finsetSum _ fun α _ => ?_
  refine Integrable.of_bound ((hws.measurable.comp ((measurable_microCoord p E).comp
      (measurable_physicalOrderedEigenvalue p α))).mul (Φ.continuous.measurable.comp
      (continuous_projIci_zero.measurable.comp (measurable_const.mul
        (measurable_physicalOrderedBlockMass p α k))))).aestronglyMeasurable (B * ‖Φ‖)
    (Eventually.of_forall fun H => ?_)
  rw [norm_mul]
  exact mul_le_mul (hB _) (Φ.norm_coe_le_norm _) (norm_nonneg _) ((norm_nonneg _).trans (hB 0))

theorem physicalTagSide_sub (p : Parameters) (model : p.GaussianRingModel) (E : ℝ)
    {w₁ w₂ : ℝ → ℝ} (h₁ : Continuous w₁) (h₁c : HasCompactSupport w₁) (h₂ : Continuous w₂)
    (h₂c : HasCompactSupport w₂) (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) (k : ZMod p.n) :
    physicalTagSide p model E (fun u => w₁ u - w₂ u) Φ k =
      physicalTagSide p model E w₁ Φ k - physicalTagSide p model E w₂ Φ k := by
  unfold physicalTagSide
  rw [← integral_sub (integrable_physicalIntegrand p model E h₁ h₁c Φ k)
    (integrable_physicalIntegrand p model E h₂ h₂c Φ k)]
  congr 1; ext H
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun α _ => by ring

theorem pathTagSide_sub (p : Parameters) (E : ℝ) {w₁ w₂ : ℝ → ℝ} (h₁ : Integrable w₁)
    (h₂ : Integrable w₂) (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) :
    pathTagSide p E (fun u => w₁ u - w₂ u) Φ = pathTagSide p E w₁ Φ - pathTagSide p E w₂ Φ := by
  have hA := stronglyMeasurable_pathTagExpect p E Φ
  have hi : ∀ {w : ℝ → ℝ}, Integrable w → Integrable (fun u => w u *
      pathTagExpect p.b (microEnergy p E u) p.W (p.n - 3) Φ) := fun hw =>
    hw.mul_bdd hA.aestronglyMeasurable (Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs]; exact abs_pathTagExpect_le _ _ _ _ Φ)
  unfold pathTagSide
  rw [← integral_sub (hi h₁) (hi h₂)]
  congr 1; ext u; ring

/-- **The microscopic tag comparison** (`MicroscopicTagComparisonStatement`), from the lead
comparison `MicroscopicTagLeadComparison` and `NegativeClockContract`. -/
theorem microscopicTagComparison (hIso : MicroscopicTagLeadComparison)
    (hNeg : NegativeClockContract) : MicroscopicTagComparisonStatement := by
  intro b hb hb' E hE1 hE2 w hws hwc Φ τ hτ s R ε hε
  obtain ⟨ϖ, hϖs, hϖc, hϖ⟩ := exists_smooth_dominating hws.continuous hwc
  have hϖ0 : ∀ u, 0 ≤ ϖ u := fun u => (abs_nonneg _).trans (hϖ u)
  have hd0 : ∀ u, 0 ≤ ϖ u - w u := fun u => by linarith [le_abs_self (w u), hϖ u]
  have hds : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => ϖ u - w u) := hϖs.sub hws
  have hdc : HasCompactSupport (fun u => ϖ u - w u) := hϖc.sub hwc
  have h1 := microscopicTag_nonneg hIso hNeg b hb hb' E hE1 hE2 ϖ hϖs hϖc hϖ0 Φ τ hτ s R
    (ε / 2) (by positivity)
  have h2 := microscopicTag_nonneg hIso hNeg b hb hb' E hE1 hE2 (fun u => ϖ u - w u) hds hdc hd0
    Φ τ hτ s R (ε / 2) (by positivity)
  filter_upwards [h1, h2] with j h1j h2j k
  have hw_eq : w = fun u => ϖ u - (ϖ u - w u) := by funext u; ring
  have hphys := physicalTagSide_sub (s.parameters b hb hb' j) (R j) E hϖs.continuous hϖc
    hds.continuous hdc Φ k
  have hpath := pathTagSide_sub (s.parameters b hb hb' j) E
    (hϖs.continuous.integrable_of_hasCompactSupport hϖc)
    (hds.continuous.integrable_of_hasCompactSupport hdc) Φ
  rw [← hw_eq] at hphys hpath
  rw [hphys, hpath]
  calc _ = |(physicalTagSide (s.parameters b hb hb' j) (R j) E ϖ Φ k -
          pathTagSide (s.parameters b hb hb' j) E ϖ Φ) -
        (physicalTagSide (s.parameters b hb hb' j) (R j) E (fun u => ϖ u - w u) Φ k -
          pathTagSide (s.parameters b hb hb' j) E (fun u => ϖ u - w u) Φ)| := by ring_nf
    _ ≤ ε / 2 + ε / 2 := (abs_sub _ _).trans (add_le_add (h1j k) (h2j k))
    _ = ε := by ring

end BlockBand.Endpoints
