module
public import BlockBand.SourceProcess.Stochastic.SemimartingaleIto.Scheme.Errors
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Taylor scheme with integral bounds: zero-mean transforms and vanishing errors

Under `IHyp Q 𝓖 K Z β α N B C` (raw filtration, probability `Q`), `φ ∈ C²(U)`, `K ⊆ U`,
`s ≤ t`, grids of `[s, t]`:

* `integral_indicator_transform1'`, `integral_indicator_transform2'`: `E[1_A T¹_n] = 0`,
  `E[1_A T²_n] = 0` for `A ∈ 𝓖_s`;
* `aesm_integral_gen'`: `∫_s^t 𝓛φ` is `𝓖_t`-a.e.-strongly measurable (a.e. limit of Riemann
  sums);
* `tendsto_integral_riemann_err'`: `E|Riemann_n - ∫_s^t 𝓛φ| → 0`;
* `tendsto_integral_meshMax_sq'`: `E[m_n²] → 0`; `tendsto_integral_sqG`: `E[W_n] → 0`.
-/

namespace BlockBand.SourceProcess.Stochastic.SemimartingaleIto
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal ENNReal

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {d : ℕ}
  {Q : Measure Ω} {𝓖 : Filtration ℝ≥0 m₀} {K U : Set (Fin d → ℝ)}
  {Z β : ℝ≥0 → Ω → Fin d → ℝ} {α : ℝ≥0 → Ω → Fin d → Fin d → ℝ}
  {N : Fin d → ℝ≥0 → Ω → ℝ} {B : Fin d → Fin d → ℝ≥0 → Ω → ℝ} {C : ℝ}
  {φ : (Fin d → ℝ) → ℝ} {s t : ℝ≥0}

theorem IHyp.aesm_riemannSum (H : IHyp Q 𝓖 K Z β α N B C) (hU : IsOpen U)
    (hKU : K ⊆ U) (hφ : ContDiffOn ℝ 2 φ U) (hst : s ≤ t) (n : ℕ) :
    AEStronglyMeasurable[𝓖 t] (riemannSum φ Z β α s t n) Q := by
  unfold riemannSum
  refine aesm_finset_sum _ fun k hk => ?_
  have hk' : k < n + 1 := Finset.mem_range.1 hk
  have l0 := 𝓖.mono (grid_le_last hst n hk'.le)
  have l1 := 𝓖.mono (grid_le_last hst n (Nat.succ_le_of_lt hk'))
  refine AEStronglyMeasurable.add
    (f := fun ω => ∑ i, dφ1 φ Z s t n i k ω * incI β s t n i k ω)
    (g := fun ω => (1 / 2 : ℝ) * ∑ i, ∑ j, dφ2 φ Z s t n i j k ω * incJ α s t n i j k ω) ?_
    (AEStronglyMeasurable.const_mul ?_ _)
  · exact aesm_finset_sum _ fun i _ =>
      ((H.aesm_dφ1 hU hKU hφ n i k).mono l0).mul ((H.aesm_incI hst n k i).mono l1)
  · exact aesm_finset_sum _ fun i _ => aesm_finset_sum _ fun j _ =>
      ((H.aesm_dφ2 hU hKU hφ n i j k).mono l0).mul ((H.aesm_incJ hst n k i j).mono l1)

theorem IHyp.aesm_integral_gen' (H : IHyp Q 𝓖 K Z β α N B C) (hU : IsOpen U)
    (hKU : K ⊆ U) (hφ : ContDiffOn ℝ 2 φ U) (hst : s ≤ t) :
    AEStronglyMeasurable[𝓖 t] (fun ω => ∫ u in (s : ℝ)..t, schemeGen φ Z β α u.toNNReal ω) Q :=
  aestronglyMeasurable_of_tendsto_ae_sub (fun n => H.aesm_riemannSum hU hKU hφ hst n)
    ((H.ae_igood s t).mono fun _ hω => tendsto_riemannSum' hω hU hKU hφ hst)

theorem IHyp.aesm_meshMax (H : IHyp Q 𝓖 K Z β α N B C) (n : ℕ) :
    AEStronglyMeasurable (meshMax Z s t n) Q :=
  aestronglyMeasurable_range_sup' (fun _ => (((H.meas _).mono (𝓖.le _)).sub
    ((H.meas _).mono (𝓖.le _))).norm) n

theorem IHyp.aesm_sqG (H : IHyp Q 𝓖 K Z β α N B C) (n : ℕ) :
    AEStronglyMeasurable (sqG β α s t n) Q := by
  unfold sqG incG
  exact aesm_finset_sum _ fun k _ => ((H.ctrlMeas _).sub (H.ctrlMeas _)).pow 2

theorem meshMax_nonneg {ω : Ω} (n : ℕ) : 0 ≤ meshMax Z s t n ω :=
  (norm_nonneg _).trans (Finset.le_sup' (fun k => ‖Z (grid s t n (k + 1)) ω -
    Z (grid s t n k) ω‖) (Finset.mem_range.2 (Nat.succ_pos n)))

theorem IGood.meshMax_le {ω : Ω} (hω : IGood K Z β α N B C s t ω) {R : ℝ}
    (hR : ∀ z ∈ K, ‖z‖ ≤ R) (n : ℕ) : meshMax Z s t n ω ≤ 2 * R := by
  refine Finset.sup'_le _ _ fun k _ => (norm_sub_le _ _).trans ?_
  have := hR _ (hω.1.1 (grid s t n (k + 1)))
  have := hR _ (hω.1.1 (grid s t n k))
  linarith

variable [IsProbabilityMeasure Q]

/-- **`E[1_A T¹_n] = 0`.** -/
theorem IHyp.integral_indicator_transform1' (H : IHyp Q 𝓖 K Z β α N B C)
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
theorem IHyp.integral_indicator_transform2' (H : IHyp Q 𝓖 K Z β α N B C)
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
  have iNN : ∀ k i j, Integrable (fun ω => ι ω * dφ2 φ Z s t n i j k ω *
        (incN N s t n i k ω * incN N s t n j k ω)) Q := fun k i j =>
    (Integrable.of_bound (((H.stronglyMeasurable_incN hst n k i).mul
      (H.stronglyMeasurable_incN hst n k j)).mono (𝓖.le _)).aestronglyMeasurable
      ((2 * (2 * R + C)) * (2 * (2 * R + C)))
      (by filter_upwards [H.ae_abs_incN_le hR n k i, H.ae_abs_incN_le hR n k j] with ω h1 h2
          rw [Pi.mul_apply, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
          exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1))).bdd_mul
      ((hg k i j).mono (𝓖.le _)) (hgb k i j)
  have iJ : ∀ k i j, Integrable (fun ω => ι ω * dφ2 φ Z s t n i j k ω *
      incJ α s t n i j k ω) Q := fun k i j =>
    (Integrable.of_bound ((H.aesm_incJ hst n k i j).mono (𝓖.le _)) _
      ((H.ae_abs_incJ_le hst n i j k).mono fun ω h => by rwa [Real.norm_eq_abs])).bdd_mul
      ((hg k i j).mono (𝓖.le _)) (hgb k i j)
  have hi : ∀ k i j, Integrable (fun ω => ι ω * dφ2 φ Z s t n i j k ω *
      (incN N s t n i k ω * incN N s t n j k ω - incJ α s t n i j k ω)) Q := fun k i j => by
    simp_rw [mul_sub]
    exact (iNN k i j).sub (iJ k i j)
  have e : (fun ω => ι ω * transform2 φ Z α N s t n ω) = fun ω => ∑ k ∈ Finset.range (n + 1),
      ∑ i, ∑ j, ι ω * dφ2 φ Z s t n i j k ω *
        (incN N s t n i k ω * incN N s t n j k ω - incJ α s t n i j k ω) := by
    funext ω
    simp only [transform2, Finset.mul_sum, mul_assoc]
  rw [e]
  refine ⟨integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun j _ => hi k i j, ?_⟩
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun j _ => hi k i j]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hi k i j]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hi k i j]
  refine Finset.sum_eq_zero fun j _ => ?_
  simp_rw [mul_sub]
  rw [integral_sub (iNN k i j) (iJ k i j), sub_eq_zero]
  exact H.integral_mul_incN_incN hR hst n k i j (hg k i j) (hgb k i j)

/-- **`E|Riemann_n - ∫_s^t 𝓛φ| → 0`.** -/
theorem IHyp.tendsto_integral_riemann_err' (H : IHyp Q 𝓖 K Z β α N B C)
    (hU : IsOpen U) (hKU : K ⊆ U) (hφ : ContDiffOn ℝ 2 φ U) (hst : s ≤ t) {M₁ M₂ : ℝ}
    (hM₁0 : 0 ≤ M₁) (hM₂0 : 0 ≤ M₂)
    (hM₁ : ∀ z ∈ K, ‖fderiv ℝ φ z‖ ≤ M₁) (hM₂ : ∀ z ∈ K, ‖fderiv ℝ (fderiv ℝ φ) z‖ ≤ M₂) :
    Tendsto (fun n => ∫ ω, |riemannSum φ Z β α s t n ω -
      ∫ u in (s : ℝ)..t, schemeGen φ Z β α u.toNNReal ω| ∂Q) atTop (𝓝 0) := by
  have hlim := tendsto_integral_of_dominated_convergence (μ := Q)
    (F := fun n ω => |riemannSum φ Z β α s t n ω -
      ∫ u in (s : ℝ)..t, schemeGen φ Z β α u.toNNReal ω|) (f := fun _ => 0)
    (fun _ => (d * M₁ + d * d * M₂) * C + (M₁ + M₂) * C)
    (fun n => (((H.aesm_riemannSum hU hKU hφ hst n).sub
      (H.aesm_integral_gen' hU hKU hφ hst)).mono (𝓖.le t)).norm)
    (integrable_const _)
    (fun n => (H.ae_igood s t).mono fun ω hω => by
      rw [Real.norm_eq_abs, abs_abs]
      have h1 := hω.abs_riemannSum_le' hst hM₁0 hM₂0 hM₁ hM₂ n
      have h2 := hω.abs_integral_gen_le' hst hM₁0 hM₂0 hM₁ hM₂
      have := abs_sub (riemannSum φ Z β α s t n ω)
        (∫ u in (s : ℝ)..t, schemeGen φ Z β α u.toNNReal ω)
      linarith)
    ((H.ae_igood s t).mono fun ω hω => by
      have := (tendsto_riemannSum' hω hU hKU hφ hst).sub_const
        (∫ u in (s : ℝ)..t, schemeGen φ Z β α u.toNNReal ω)
      rw [sub_self] at this
      simpa using this.abs)
  simpa using hlim

/-- **`E[m_n²] → 0`.** -/
theorem IHyp.tendsto_integral_meshMax_sq' (H : IHyp Q 𝓖 K Z β α N B C)
    (hst : s ≤ t) {R : ℝ} (hR : ∀ z ∈ K, ‖z‖ ≤ R) :
    Tendsto (fun n => ∫ ω, meshMax Z s t n ω ^ 2 ∂Q) atTop (𝓝 0) := by
  have hlim := tendsto_integral_of_dominated_convergence (μ := Q)
    (F := fun n ω => meshMax Z s t n ω ^ 2) (f := fun _ => 0) (fun _ => (2 * R) ^ 2)
    (fun n => (H.aesm_meshMax n).pow 2) (integrable_const _)
    (fun n => (H.ae_igood s t).mono fun ω hω => by
      rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg (meshMax_nonneg n)]
      exact pow_le_pow_left₀ (meshMax_nonneg n) (hω.meshMax_le hR n) 2)
    ((H.ae_igood s t).mono fun ω hω => by
      simpa using (tendsto_meshMax hω.1 hst).pow 2)
  simpa using hlim

/-- **`E[W_n] → 0`** for `W_n = Σ_k (ΔG_k)²`. -/
theorem IHyp.tendsto_integral_sqG (H : IHyp Q 𝓖 K Z β α N B C) (hst : s ≤ t) :
    Tendsto (fun n => ∫ ω, sqG β α s t n ω ∂Q) atTop (𝓝 0) := by
  have hlim := tendsto_integral_of_dominated_convergence (μ := Q)
    (F := fun n ω => sqG β α s t n ω) (f := fun _ => 0) (fun _ => C * C)
    (fun n => H.aesm_sqG n) (integrable_const _)
    (fun n => (H.ae_igood s t).mono fun ω hω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sqG_nonneg n)]
      exact hω.sqG_le hst n)
    ((H.ae_igood s t).mono fun ω hω => hω.tendsto_sqG hst)
  simpa using hlim

end BlockBand.SourceProcess.Stochastic.SemimartingaleIto
