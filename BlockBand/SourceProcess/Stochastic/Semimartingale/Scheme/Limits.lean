module
public import BlockBand.SourceProcess.Stochastic.Semimartingale.Scheme.Measurability
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The Taylor scheme: the two vanishing expectations

Under `SchemeHyp` with `φ ∈ C²(U)`, `K ⊆ U`, for `s ≤ t` and the grids of `[s, t]`:

* `tendsto_integral_riemann_err`: `E|Riemann_n - ∫_s^t 𝓛φ| → 0` (dominated convergence);
* `tendsto_integral_meshMax_sq`: `E[m_n²] → 0` for `m_n = max_k ‖ΔZ_k‖` (path continuity and
  dominated convergence).

Also: `∫_s^t 𝓛φ` is `𝓖_t`-a.e.-strongly measurable and bounded.
-/

namespace BlockBand.SourceProcess.Stochastic.Semimartingale
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {d : ℕ}
  {Q : Measure Ω} {𝓖 : Filtration ℝ≥0 m₀} {K U : Set (Fin d → ℝ)}
  {Z β : ℝ≥0 → Ω → Fin d → ℝ} {α : ℝ≥0 → Ω → Fin d → Fin d → ℝ}
  {N : Fin d → ℝ≥0 → Ω → ℝ} {B : Fin d → Fin d → ℝ≥0 → Ω → ℝ} {Cβ Cα : ℝ}
  {φ : (Fin d → ℝ) → ℝ} {s t : ℝ≥0}

/-- Pathwise bound on the Riemann sums. -/
theorem abs_riemannSum_le {ω : Ω} (hω : GoodPt K Z β α N B s t ω) (hβ : ∀ t ω i, |β t ω i| ≤ Cβ)
    (hα : ∀ t ω i j, |α t ω i j| ≤ Cα) (hst : s ≤ t) {M₁ M₂ : ℝ}
    (hM₁ : ∀ z ∈ K, ‖fderiv ℝ φ z‖ ≤ M₁) (hM₂ : ∀ z ∈ K, ‖fderiv ℝ (fderiv ℝ φ) z‖ ≤ M₂)
    (n : ℕ) :
    |riemannSum φ Z β α s t n ω| ≤
      (t - s : ℝ) * (d * (Cβ * M₁) + (1 / 2) * (d * (d * (Cα * M₂)))) := by
  set Δ : ℝ := (t - s : ℝ) / (n + 1)
  have hnΔ : ((n : ℝ) + 1) * Δ = t - s := by simp only [Δ]; field_simp
  have hcell : ∀ k, |∑ i, dφ1 φ Z s t n i k ω * incI β s t n i k ω +
      (1 / 2 : ℝ) * ∑ i, ∑ j, dφ2 φ Z s t n i j k ω * incJ α s t n i j k ω| ≤
      Δ * (d * (Cβ * M₁) + (1 / 2) * (d * (d * (Cα * M₂)))) := by
    intro k
    have hZ := hω.1 (grid s t n k)
    have b1 : ∀ i, |dφ1 φ Z s t n i k ω * incI β s t n i k ω| ≤ Cβ * M₁ * Δ := fun i => by
      rw [abs_mul]
      have := abs_incI_le hω hβ hst n i k
      have h1 := (abs_clm_ev_le (fderiv ℝ φ (Z (grid s t n k) ω)) i).trans (hM₁ _ hZ)
      calc |dφ1 φ Z s t n i k ω| * |incI β s t n i k ω| ≤ M₁ * (Cβ * Δ) :=
            mul_le_mul h1 this (abs_nonneg _) ((abs_nonneg _).trans h1)
        _ = Cβ * M₁ * Δ := by ring
    have b2 : ∀ i j, |dφ2 φ Z s t n i j k ω * incJ α s t n i j k ω| ≤ Cα * M₂ * Δ := fun i j => by
      rw [abs_mul]
      have := abs_incJ_le hω hα hst n i j k
      have h1 := (abs_bilin_ev_le (fderiv ℝ (fderiv ℝ φ) (Z (grid s t n k) ω)) i j).trans
        (hM₂ _ hZ)
      calc |dφ2 φ Z s t n i j k ω| * |incJ α s t n i j k ω| ≤ M₂ * (Cα * Δ) :=
            mul_le_mul h1 this (abs_nonneg _) ((abs_nonneg _).trans h1)
        _ = Cα * M₂ * Δ := by ring
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have s1 : |∑ i, dφ1 φ Z s t n i k ω * incI β s t n i k ω| ≤ d * (Cβ * M₁ * Δ) :=
      (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun i _ => b1 i).trans
        (by simp))
    have s2 : |∑ i, ∑ j, dφ2 φ Z s t n i j k ω * incJ α s t n i j k ω| ≤
        d * (d * (Cα * M₂ * Δ)) :=
      (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun i _ =>
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => b2 i j)).trans
          (by simp))
    nlinarith
  unfold riemannSum
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun k _ => hcell k).trans ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc]
  push_cast
  rw [hnΔ]

/-- Pathwise bound on `∫_s^t 𝓛φ`. -/
theorem abs_integral_gen_le {ω : Ω} (hω : GoodPt K Z β α N B s t ω)
    (hβ : ∀ t ω i, |β t ω i| ≤ Cβ) (hα : ∀ t ω i j, |α t ω i j| ≤ Cα) {a b : ℝ} (hab : a ≤ b)
    {M₁ M₂ : ℝ} (hM₁ : ∀ z ∈ K, ‖fderiv ℝ φ z‖ ≤ M₁)
    (hM₂ : ∀ z ∈ K, ‖fderiv ℝ (fderiv ℝ φ) z‖ ≤ M₂) :
    |∫ u in a..b, schemeGen φ Z β α u.toNNReal ω| ≤
      (d * (Cβ * M₁) + (1 / 2) * (d * (d * (Cα * M₂)))) * (b - a) :=
  abs_intervalIntegral_le (fun _ => abs_schemeGen_le hβ hα hM₁ hM₂ (hω.1 _)) hab

/-- The pathwise integral of the generator is a.e. the limit of the Riemann sums, hence
`𝓖_t`-a.e.-strongly measurable. -/
theorem SchemeHyp.aesm_integral_gen (H : SchemeHyp Q 𝓖 K Z β α N B Cβ Cα) (hU : IsOpen U)
    (hKU : K ⊆ U) (hφ : ContDiffOn ℝ 2 φ U) (hst : s ≤ t) :
    AEStronglyMeasurable[𝓖 t] (fun ω => ∫ u in (s : ℝ)..t, schemeGen φ Z β α u.toNNReal ω) Q :=
  aestronglyMeasurable_of_tendsto_ae_sub (fun n => H.aesm_riemannSum hU hKU hφ hst n)
    ((H.ae_good s t).mono fun _ hω =>
      tendsto_riemannSum hω H.driftBound H.diffBound hU hKU hφ hst)

/-- `m_n → 0` along every good path. -/
theorem tendsto_meshMax {ω : Ω} (hω : GoodPt K Z β α N B s t ω) (hst : s ≤ t) :
    Tendsto (fun n => meshMax Z s t n ω) atTop (𝓝 0) := by
  have hst' : (s : ℝ) ≤ t := by exact_mod_cast hst
  have hz : ContinuousOn (fun u : ℝ => Z u.toNNReal ω) (Icc (s : ℝ) t) :=
    (hω.2.1.comp continuous_real_toNNReal).continuousOn
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M, hM⟩ := eventually_atTop.1 (eventually_mesh_le hst' hz (half_pos hε))
  refine ⟨M, fun n hn => ?_⟩
  have h0 : 0 ≤ meshMax Z s t n ω :=
    (norm_nonneg _).trans (Finset.le_sup' (fun k => ‖Z (grid s t n (k + 1)) ω -
      Z (grid s t n k) ω‖) (Finset.mem_range.2 (Nat.succ_pos n)))
  have hle : meshMax Z s t n ω ≤ ε / 2 := by
    refine Finset.sup'_le _ _ fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    have := hM n hn k hk' (rgrid s t n (k + 1))
      ⟨rgrid_mono hst' n (Nat.le_succ k), le_rfl⟩
    rwa [toNNReal_rgrid hst, toNNReal_rgrid hst, dist_eq_norm] at this
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  linarith

variable [IsProbabilityMeasure Q]

/-- **`E|Riemann_n - ∫_s^t 𝓛φ| → 0`.** -/
theorem SchemeHyp.tendsto_integral_riemann_err (H : SchemeHyp Q 𝓖 K Z β α N B Cβ Cα)
    (hU : IsOpen U) (hKU : K ⊆ U) (hφ : ContDiffOn ℝ 2 φ U) (hst : s ≤ t) {M₁ M₂ : ℝ}
    (hM₁ : ∀ z ∈ K, ‖fderiv ℝ φ z‖ ≤ M₁) (hM₂ : ∀ z ∈ K, ‖fderiv ℝ (fderiv ℝ φ) z‖ ≤ M₂) :
    Tendsto (fun n => ∫ ω, |riemannSum φ Z β α s t n ω -
      ∫ u in (s : ℝ)..t, schemeGen φ Z β α u.toNNReal ω| ∂Q) atTop (𝓝 0) := by
  have hst' : (s : ℝ) ≤ t := by exact_mod_cast hst
  have hlim := tendsto_integral_of_dominated_convergence (μ := Q)
    (F := fun n ω => |riemannSum φ Z β α s t n ω -
      ∫ u in (s : ℝ)..t, schemeGen φ Z β α u.toNNReal ω|) (f := fun _ => 0)
    (fun _ => 2 * ((t - s : ℝ) * (d * (Cβ * M₁) + (1 / 2) * (d * (d * (Cα * M₂))))))
    (fun n => (((H.aesm_riemannSum hU hKU hφ hst n).sub
      (H.aesm_integral_gen hU hKU hφ hst)).mono (𝓖.le t)).norm)
    (integrable_const _)
    (fun n => (H.ae_good s t).mono fun ω hω => by
      rw [Real.norm_eq_abs, abs_abs]
      have h1 := abs_riemannSum_le hω H.driftBound H.diffBound hst hM₁ hM₂ n
      have h2 := abs_integral_gen_le hω H.driftBound H.diffBound hst' hM₁ hM₂
      have := abs_sub (riemannSum φ Z β α s t n ω)
        (∫ u in (s : ℝ)..t, schemeGen φ Z β α u.toNNReal ω)
      linarith)
    ((H.ae_good s t).mono fun ω hω => by
      have := (tendsto_riemannSum hω H.driftBound H.diffBound hU hKU hφ hst).sub_const
        (∫ u in (s : ℝ)..t, schemeGen φ Z β α u.toNNReal ω)
      rw [sub_self] at this
      simpa using this.abs)
  simpa using hlim

omit [IsProbabilityMeasure Q] in
theorem SchemeHyp.aesm_meshMax (H : SchemeHyp Q 𝓖 K Z β α N B Cβ Cα) (n : ℕ) :
    AEStronglyMeasurable (meshMax Z s t n) Q :=
  aestronglyMeasurable_range_sup' (fun _ => (((H.meas _).mono (𝓖.le _)).sub
    ((H.meas _).mono (𝓖.le _))).norm) n

/-- **`E[m_n²] → 0`.** -/
theorem SchemeHyp.tendsto_integral_meshMax_sq (H : SchemeHyp Q 𝓖 K Z β α N B Cβ Cα)
    (hst : s ≤ t) {R : ℝ} (hR : ∀ z ∈ K, ‖z‖ ≤ R) :
    Tendsto (fun n => ∫ ω, meshMax Z s t n ω ^ 2 ∂Q) atTop (𝓝 0) := by
  have hlim := tendsto_integral_of_dominated_convergence (μ := Q)
    (F := fun n ω => meshMax Z s t n ω ^ 2) (f := fun _ => 0) (fun _ => (2 * R) ^ 2)
    (fun n => (H.aesm_meshMax n).pow 2) (integrable_const _)
    (fun n => (H.ae_good s t).mono fun ω hω => by
      rw [Real.norm_eq_abs, abs_pow]
      have h0 : 0 ≤ meshMax Z s t n ω :=
        (norm_nonneg _).trans (Finset.le_sup' (fun k => ‖Z (grid s t n (k + 1)) ω -
          Z (grid s t n k) ω‖) (Finset.mem_range.2 (Nat.succ_pos n)))
      have hle : meshMax Z s t n ω ≤ 2 * R := by
        refine Finset.sup'_le _ _ fun k _ => (norm_sub_le _ _).trans ?_
        have := hR _ (hω.1 (grid s t n (k + 1)))
        have := hR _ (hω.1 (grid s t n k))
        linarith
      rw [abs_of_nonneg h0]
      exact pow_le_pow_left₀ h0 hle 2)
    ((H.ae_good s t).mono fun ω hω => by
      simpa using (tendsto_meshMax hω hst).pow 2)
  simpa using hlim

end BlockBand.SourceProcess.Stochastic.Semimartingale
