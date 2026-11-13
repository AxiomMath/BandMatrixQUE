module
public import BlockBand.SourceProcess.Stochastic.Semimartingale.Scheme.Limits
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The Taylor scheme: the martingale transforms have zero mean on `𝓖_s`-sets

Under `SchemeHyp` (probability `Q`, raw filtration `𝓖`), `φ ∈ C²(U)`, `K ⊆ U`, `s ≤ t` and
`A ∈ 𝓖_s`: `E[1_A T¹_n] = 0` and `E[1_A T²_n] = 0` for every grid `n` of `[s, t]`, where
`T¹_n = Σ_k Σ_i ∂_iφ(Z_{t_k}) ΔN^i_k` and `T²_n = Σ_k Σ_{ij} ∂_{ij}φ(Z_{t_k})(ΔN^iΔN^j - Δ∫α^{ij})`.
Both transforms are integrable.
-/

namespace BlockBand.SourceProcess.Stochastic.Semimartingale
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {d : ℕ}
  {Q : Measure Ω} [IsProbabilityMeasure Q] {𝓖 : Filtration ℝ≥0 m₀} {K U : Set (Fin d → ℝ)}
  {Z β : ℝ≥0 → Ω → Fin d → ℝ} {α : ℝ≥0 → Ω → Fin d → Fin d → ℝ}
  {N : Fin d → ℝ≥0 → Ω → ℝ} {B : Fin d → Fin d → ℝ≥0 → Ω → ℝ} {Cβ Cα : ℝ}
  {φ : (Fin d → ℝ) → ℝ} {s t : ℝ≥0}

omit [IsProbabilityMeasure Q] in
theorem aesm_indicator_mul {A : Set Ω}
    (hA : MeasurableSet[𝓖 s] A) (hst : s ≤ t) (n k : ℕ) {g : Ω → ℝ}
    (hg : AEStronglyMeasurable[𝓖 (grid s t n k)] g Q) :
    AEStronglyMeasurable[𝓖 (grid s t n k)] (fun ω => A.indicator (fun _ => (1 : ℝ)) ω * g ω) Q := by
  have hA' : MeasurableSet[𝓖 (grid s t n k)] A := by
    have := grid_mono hst n (Nat.zero_le k)
    rw [grid_zero] at this
    exact 𝓖.mono this A hA
  exact ((stronglyMeasurable_const.indicator hA').aestronglyMeasurable).mul hg

omit [IsProbabilityMeasure Q] in
theorem ae_abs_indicator_mul_le {A : Set Ω} {g : Ω → ℝ} {C : ℝ}
    (hg : ∀ᵐ ω ∂Q, ‖g ω‖ ≤ C) :
    ∀ᵐ ω ∂Q, ‖A.indicator (fun _ => (1 : ℝ)) ω * g ω‖ ≤ C := by
  filter_upwards [hg] with ω h
  by_cases hω : ω ∈ A
  · simpa [hω] using h
  · simp only [hω, not_false_eq_true, Set.indicator_of_notMem, zero_mul, norm_zero]
    exact (norm_nonneg _).trans h

/-- **`E[1_A T¹_n] = 0`.** -/
theorem SchemeHyp.integral_indicator_transform1 (H : SchemeHyp Q 𝓖 K Z β α N B Cβ Cα)
    (hU : IsOpen U) (hKU : K ⊆ U) (hφ : ContDiffOn ℝ 2 φ U) {M₁ : ℝ}
    (hM₁ : ∀ z ∈ K, ‖fderiv ℝ φ z‖ ≤ M₁) (hst : s ≤ t) {A : Set Ω}
    (hA : MeasurableSet[𝓖 s] A) (n : ℕ) :
    Integrable (fun ω => A.indicator (fun _ => (1 : ℝ)) ω * transform1 φ Z N s t n ω) Q ∧
    ∫ ω, A.indicator (fun _ => (1 : ℝ)) ω * transform1 φ Z N s t n ω ∂Q = 0 := by
  set ι := A.indicator (fun _ => (1 : ℝ))
  have hg : ∀ k i, AEStronglyMeasurable[𝓖 (grid s t n k)]
      (fun ω => ι ω * dφ1 φ Z s t n i k ω) Q := fun k i =>
    aesm_indicator_mul hA hst n k (H.aesm_dφ1 hU hKU hφ n i k)
  have hgb : ∀ k i, ∀ᵐ ω ∂Q, ‖ι ω * dφ1 φ Z s t n i k ω‖ ≤ M₁ := fun k i =>
    ae_abs_indicator_mul_le (H.ae_abs_dφ1_le hM₁ n i k)
  have hi : ∀ k i, Integrable (fun ω => ι ω * dφ1 φ Z s t n i k ω * incN N s t n i k ω) Q :=
    fun k i => (H.integrable_incN n k i).bdd_mul ((hg k i).mono (𝓖.le _)) (hgb k i)
  have e : (fun ω => ι ω * transform1 φ Z N s t n ω) = fun ω => ∑ k ∈ Finset.range (n + 1),
      ∑ i, ι ω * dφ1 φ Z s t n i k ω * incN N s t n i k ω := by
    funext ω
    simp only [transform1, Finset.mul_sum, mul_assoc]
  rw [e]
  refine ⟨integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun i _ => hi k i, ?_⟩
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun i _ => hi k i]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [integral_finsetSum _ fun i _ => hi k i]
  exact Finset.sum_eq_zero fun i _ => H.integral_mul_incN hst n k i (hg k i) (hgb k i)

/-- **`E[1_A T²_n] = 0`.** -/
theorem SchemeHyp.integral_indicator_transform2 (H : SchemeHyp Q 𝓖 K Z β α N B Cβ Cα)
    (hU : IsOpen U) (hKU : K ⊆ U) (hφ : ContDiffOn ℝ 2 φ U) {R M₂ : ℝ}
    (hR : ∀ z ∈ K, ‖z‖ ≤ R) (hM₂ : ∀ z ∈ K, ‖fderiv ℝ (fderiv ℝ φ) z‖ ≤ M₂) (hst : s ≤ t)
    {A : Set Ω} (hA : MeasurableSet[𝓖 s] A) (n : ℕ) :
    Integrable (fun ω => A.indicator (fun _ => (1 : ℝ)) ω * transform2 φ Z α N s t n ω) Q ∧
    ∫ ω, A.indicator (fun _ => (1 : ℝ)) ω * transform2 φ Z α N s t n ω ∂Q = 0 := by
  set ι := A.indicator (fun _ => (1 : ℝ))
  have hg : ∀ k i j, AEStronglyMeasurable[𝓖 (grid s t n k)]
      (fun ω => ι ω * dφ2 φ Z s t n i j k ω) Q := fun k i j =>
    aesm_indicator_mul hA hst n k (H.aesm_dφ2 hU hKU hφ n i j k)
  have hgb : ∀ k i j, ∀ᵐ ω ∂Q, ‖ι ω * dφ2 φ Z s t n i j k ω‖ ≤ M₂ := fun k i j =>
    ae_abs_indicator_mul_le (H.ae_abs_dφ2_le hM₂ n i j k)
  have iNN : ∀ k, k < n + 1 → ∀ i j,
      Integrable (fun ω => ι ω * dφ2 φ Z s t n i j k ω *
        (incN N s t n i k ω * incN N s t n j k ω)) Q := fun k hk i j =>
    (Integrable.of_bound (((H.stronglyMeasurable_incN hst n k i).mul
      (H.stronglyMeasurable_incN hst n k j)).mono (𝓖.le _)).aestronglyMeasurable
      ((2 * (2 * R + Cβ * t)) * (2 * (2 * R + Cβ * t)))
      (by filter_upwards [H.ae_abs_incN_le hR hst n hk i, H.ae_abs_incN_le hR hst n hk j]
            with ω h1 h2
          rw [Pi.mul_apply, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
          exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1))).bdd_mul
      ((hg k i j).mono (𝓖.le _)) (hgb k i j)
  have iJ : ∀ k i j, Integrable (fun ω => ι ω * dφ2 φ Z s t n i j k ω *
      incJ α s t n i j k ω) Q := fun k i j =>
    (Integrable.of_bound ((H.aestronglyMeasurable_incJ hst n k i j).mono (𝓖.le _)) _
      ((H.ae_abs_incJ_le hst n i j k).mono fun ω h => by rwa [Real.norm_eq_abs])).bdd_mul
      ((hg k i j).mono (𝓖.le _)) (hgb k i j)
  have hi : ∀ k ∈ Finset.range (n + 1), ∀ i j, Integrable (fun ω => ι ω * dφ2 φ Z s t n i j k ω *
      (incN N s t n i k ω * incN N s t n j k ω - incJ α s t n i j k ω)) Q := fun k hk i j => by
    simp_rw [mul_sub]
    exact (iNN k (Finset.mem_range.1 hk) i j).sub (iJ k i j)
  have e : (fun ω => ι ω * transform2 φ Z α N s t n ω) = fun ω => ∑ k ∈ Finset.range (n + 1),
      ∑ i, ∑ j, ι ω * dφ2 φ Z s t n i j k ω *
        (incN N s t n i k ω * incN N s t n j k ω - incJ α s t n i j k ω) := by
    funext ω
    simp only [transform2, Finset.mul_sum, mul_assoc]
  rw [e]
  refine ⟨integrable_finsetSum _ fun k hk => integrable_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun j _ => hi k hk i j, ?_⟩
  rw [integral_finsetSum _ fun k hk => integrable_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun j _ => hi k hk i j]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hi k hk i j]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hi k hk i j]
  refine Finset.sum_eq_zero fun j _ => ?_
  simp_rw [mul_sub]
  rw [integral_sub (iNN k (Finset.mem_range.1 hk) i j) (iJ k i j), sub_eq_zero]
  exact H.integral_mul_incN_incN hR hst n (Finset.mem_range.1 hk) i j (hg k i j) (hgb k i j)

end BlockBand.SourceProcess.Stochastic.Semimartingale
