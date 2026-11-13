module

public import Mathlib
public import BlockBand.GaussianBulk.ExternalSineLaplace

/-!
# Microscopic rescaling of determinantal correlation integrals

Deterministic finite-dimensional analysis on
`ℝ^k` with Lebesgue measure; arbitrary continuous kernel `Kern : ℝ → ℝ → ℂ`, real `E`,
scale `s > 0` and arbitrary (not necessarily measurable) real gauge `h`:

* `det_gauge_div`: `det[e^{-h_i} K_ij e^{h_j} / c] = (c⁻¹)^k det K` (from
  `det_exponential_gauge`);
* `integral_withDensity_rescale`: `∫ ∏_j φ(s(x_j-E)) d(withDensity (ofReal Re det[Kern(x_i,x_j)]))
  = ∫ ∏_j φ(ξ_j) · max((s⁻¹)^k Re det[Kern(E+ξ_i/s, E+ξ_j/s)], 0) dξ`;
* `exists_det_close`: uniform continuity of `det` near matrices with entries in `[-1,1]`;
* `exists_pos_forall_lt`: a common positive tolerance for finitely many orders.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.GaussianBulk

open MeasureTheory Set Finset
open scoped NNReal ENNReal

/-- Gauge and scalar normalization of a kernel matrix. -/
theorem det_gauge_div {k : ℕ} (K : Matrix (Fin k) (Fin k) ℂ) (h : Fin k → ℂ) (c : ℂ) :
    (Matrix.of fun i j => Complex.exp (-h i) * K i j * Complex.exp (h j) / c).det =
      c⁻¹ ^ k * K.det := by
  have hm : (Matrix.of fun i j => Complex.exp (-h i) * K i j * Complex.exp (h j) / c) =
      c⁻¹ • (Matrix.of fun i j => Complex.exp (-h i) * K i j * Complex.exp (h j)) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [hm, Matrix.det_smul, Fintype.card_fin]
  congr 1
  exact det_exponential_gauge K h

/-- The microscopic kernel matrix `[Kern(E+ξ_i/s, E+ξ_j/s)]`. -/
def microKernel {k : ℕ} (Kern : ℝ → ℝ → ℂ) (E s : ℝ) (ξ : Fin k → ℝ) :
    Matrix (Fin k) (Fin k) ℂ :=
  fun i j => Kern (E + ξ i / s) (E + ξ j / s)

/-- The microscopic kernel determinant is continuous on `ℝ^k` for continuous `Kern`. -/
theorem continuous_microKernel_det {k : ℕ} (Kern : ℝ → ℝ → ℂ)
    (hK : Continuous (Function.uncurry Kern)) (E s : ℝ) :
    Continuous (fun ξ : Fin k → ℝ => (microKernel Kern E s ξ).det) := by
  apply Continuous.matrix_det
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have h1 : Continuous (fun ξ : Fin k → ℝ => (E + ξ i / s, E + ξ j / s)) := by fun_prop
  exact hK.comp h1

/-- Change of variables `x = E + ξ/s` in a determinantal correlation integral (Lebesgue on
`ℝ^k`, `s > 0`, continuous `Kern` and `φ`). -/
theorem integral_withDensity_rescale {k : ℕ} (Kern : ℝ → ℝ → ℂ)
    (hK : Continuous (Function.uncurry Kern)) (E s : ℝ) (hs : 0 < s) (φ : ℝ → ℝ) :
    (∫ x, unfoldedObservable s E φ x ∂(volume : Measure (Fin k → ℝ)).withDensity
        (fun x => ENNReal.ofReal (Matrix.det (fun i j => Kern (x i) (x j))).re)) =
      ∫ ξ : Fin k → ℝ, (∏ j, φ (ξ j)) *
        max ((s⁻¹) ^ k * (microKernel Kern E s ξ).det.re) 0 := by
  set D : (Fin k → ℝ) → ℝ := fun x => (Matrix.det (fun i j => Kern (x i) (x j))).re with hD
  have hDc : Continuous D := by
    refine Complex.continuous_re.comp (Continuous.matrix_det
      (continuous_pi fun i => continuous_pi fun j => ?_))
    have h1 : Continuous (fun x : Fin k → ℝ => (x i, x j)) := by fun_prop
    exact hK.comp h1
  have h1 : (fun x => ENNReal.ofReal (D x)) = fun x => ((Real.toNNReal (D x) : ℝ≥0) : ℝ≥0∞) :=
    rfl
  rw [show (fun x : Fin k → ℝ => ENNReal.ofReal (Matrix.det (fun i j => Kern (x i) (x j))).re) =
    fun x => ENNReal.ofReal (D x) from rfl, h1,
    integral_withDensity_eq_integral_smul hDc.measurable.real_toNNReal]
  simp_rw [NNReal.smul_def, Real.coe_toNNReal', smul_eq_mul]
  set H : (Fin k → ℝ) → ℝ := fun x => max (D x) 0 * unfoldedObservable s E φ x with hH
  set c : Fin k → ℝ := fun _ => E
  have hcv : (∫ ξ : Fin k → ℝ, H (c + s⁻¹ • ξ)) = s ^ k * ∫ x, H x := by
    rw [Measure.integral_comp_smul (volume : Measure (Fin k → ℝ)) (fun y => H (c + y)) s⁻¹,
      integral_add_left_eq_self H c, Module.finrank_fin_fun, inv_pow, inv_inv,
      abs_of_pos (pow_pos hs k), smul_eq_mul]
  have hsk : s ^ k ≠ 0 := (pow_pos hs k).ne'
  have hH' : (∫ x, H x) = ∫ ξ : Fin k → ℝ, (s ^ k)⁻¹ * H (c + s⁻¹ • ξ) := by
    rw [integral_const_mul, hcv, ← mul_assoc, inv_mul_cancel₀ hsk, one_mul]
  change (∫ x, H x) = _
  rw [hH']
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  have hpt : c + s⁻¹ • ξ = fun j => E + ξ j / s := by
    funext j
    simp only [c, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simp only [hH, hpt, hD, unfoldedObservable]
  have hphi : ∀ j, s * (E + ξ j / s - E) = ξ j := fun j => by
    field_simp
    ring
  simp_rw [hphi]
  rw [mul_comm (max _ _), ← mul_assoc, mul_comm _ (∏ j, φ (ξ j)), mul_assoc,
    mul_max_of_nonneg _ _ (by positivity), mul_zero, inv_pow]
  rfl

/-- Uniform continuity of the determinant near real matrices with entries in `[-1, 1]`. -/
theorem exists_det_close (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ η > 0, ∀ (A : Matrix (Fin k) (Fin k) ℂ) (B : Matrix (Fin k) (Fin k) ℝ),
      (∀ i j, |B i j| ≤ 1) → (∀ i j, ‖A i j - (B i j : ℂ)‖ ≤ η) →
        ‖A.det - (B.det : ℂ)‖ ≤ ε := by
  set d : (Fin k → Fin k → ℂ) → ℂ := fun M => Matrix.det (Matrix.of M)
  have hd : Continuous d := Continuous.matrix_det continuous_id
  have huc := (isCompact_closedBall (0 : Fin k → Fin k → ℂ) 2).uniformContinuousOn_of_continuous
    hd.continuousOn
  obtain ⟨η, hη, hη'⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  refine ⟨min (η / 2) 1, by positivity, fun A B hB hAB => ?_⟩
  set Ac : Fin k → Fin k → ℂ := fun i j => A i j
  set Bc : Fin k → Fin k → ℂ := fun i j => (B i j : ℂ)
  have hBc : ∀ i j, ‖Bc i j‖ ≤ 1 := fun i j => by
    simp only [Bc, Complex.norm_real, Real.norm_eq_abs]
    exact hB i j
  have hAc : ∀ i j, ‖Ac i j‖ ≤ 2 := fun i j => by
    calc ‖Ac i j‖ = ‖(A i j - Bc i j) + Bc i j‖ := by rw [sub_add_cancel]
      _ ≤ ‖A i j - Bc i j‖ + ‖Bc i j‖ := norm_add_le _ _
      _ ≤ 1 + 1 := add_le_add ((hAB i j).trans (min_le_right _ _)) (hBc i j)
      _ = 2 := by norm_num
  have hmem : ∀ M : Fin k → Fin k → ℂ, (∀ i j, ‖M i j‖ ≤ 2) → M ∈ Metric.closedBall 0 2 := by
    intro M hM
    rw [Metric.mem_closedBall, dist_pi_le_iff (by norm_num)]
    intro i
    rw [dist_pi_le_iff (by norm_num)]
    intro j
    simpa using hM i j
  have hdist : dist Ac Bc < η := by
    have : dist Ac Bc ≤ η / 2 := by
      rw [dist_pi_le_iff (by positivity)]
      intro i
      rw [dist_pi_le_iff (by positivity)]
      intro j
      rw [dist_eq_norm]
      exact (hAB i j).trans (min_le_left _ _)
    linarith
  have h := hη' Ac (hmem Ac hAc) Bc (hmem Bc fun i j => (hBc i j).trans (by norm_num)) hdist
  have hdetB : d Bc = (B.det : ℂ) := by
    have := RingHom.map_det Complex.ofRealHom B
    simp only [Complex.ofRealHom_eq_coe] at this
    rw [this]
    rfl
  have hdetA : d Ac = A.det := rfl
  rw [hdetB, hdetA, dist_eq_norm] at h
  exact h.le

/-- A common positive tolerance for the finitely many orders `k < K`. -/
theorem exists_pos_forall_lt (P : ℕ → ℝ → Prop)
    (hmono : ∀ k η η', 0 < η' → η' ≤ η → P k η → P k η')
    (h : ∀ k, ∃ η > 0, P k η) (K : ℕ) : ∃ η > 0, ∀ k < K, P k η := by
  induction K with
  | zero => exact ⟨1, one_pos, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | succ K ih =>
    obtain ⟨η₁, hη₁, h₁⟩ := ih
    obtain ⟨η₂, hη₂, h₂⟩ := h K
    refine ⟨min η₁ η₂, lt_min hη₁ hη₂, fun k hk => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
    · exact hmono k η₁ _ (lt_min hη₁ hη₂) (min_le_left _ _) (h₁ k hk)
    · subst hk
      exact hmono k η₂ _ (lt_min hη₁ hη₂) (min_le_right _ _) h₂

end BlockBand.GaussianBulk
