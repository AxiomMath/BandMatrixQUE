module
public import BlockBand.SourceProcess.Stochastic.SemimartingaleIto.Scheme.Decomp
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Taylor scheme with integral bounds: measurability and moments)

Under `IHyp Q 𝓖 K Z β α N B C` (raw filtration, probability `Q`), grid of `[s, t]`:

* the grid quantities `dφ1, dφ2` (at `t_k`) and `incN, incI, incJ` (at `t_{k+1}`) are
  `𝓖`-a.e.-strongly measurable and a.s. bounded (by `M₁`, `M₂`, `2(2R + C)`, `C`, `C`);
* `integral_mul_incN`: `E[g ΔN^i_k] = 0`; `integral_mul_incN_incN`:
  `E[g ΔN^i_k ΔN^j_k] = E[g Δ∫α^{ij}_k]` for bounded `𝓖_{t_k}`-a.e. measurable `g`;
* `integral_sqSum_le'`: `E[S_n] ≤ d C`; `integral_sqSum_sq_le'`:
  `E[S_n²] ≤ (D + 2 d C) d C` with `D = d (2(2R + C))²`, `S_n = Σ_k Σ_i (ΔN^i_k)²`.

The second moment uses `E[c_k c_l] = E[c_k Σ_i Δ∫α^{ii}_l]` (`k < l`) and the pathwise bound
`Σ_{l > k} Σ_i Δ∫α^{ii}_l ≤ d C` (integral control), instead of the cellwise bound
`Δ∫α ≤ Cα Δt` of the pointwise-bounded scheme.
-/

namespace BlockBand.SourceProcess.Stochastic.SemimartingaleIto
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic.Semimartingale
open scoped NNReal ENNReal

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {d : ℕ}
  {Q : Measure Ω} {𝓖 : Filtration ℝ≥0 m₀} {K U : Set (Fin d → ℝ)}
  {Z β : ℝ≥0 → Ω → Fin d → ℝ} {α : ℝ≥0 → Ω → Fin d → Fin d → ℝ}
  {N : Fin d → ℝ≥0 → Ω → ℝ} {B : Fin d → Fin d → ℝ≥0 → Ω → ℝ} {C R : ℝ}
  {φ : (Fin d → ℝ) → ℝ} {s t : ℝ≥0}

theorem IHyp.aesm_comp (H : IHyp Q 𝓖 K Z β α N B C) {F : Type*}
    [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    [TopologicalSpace.PseudoMetrizableSpace F] [Zero F] {f : (Fin d → ℝ) → F}
    (hf : ContinuousOn f K) (u : ℝ≥0) :
    AEStronglyMeasurable[𝓖 u] (fun ω => f (Z u ω)) Q :=
  aestronglyMeasurable_comp_of_continuousOn H.compact.isClosed hf (H.meas u)
    (H.mem.mono fun _ h => h u)

theorem IHyp.aesm_dφ1 (H : IHyp Q 𝓖 K Z β α N B C) (hU : IsOpen U) (hKU : K ⊆ U)
    (hφ : ContDiffOn ℝ 2 φ U) (n : ℕ) (i : Fin d) (k : ℕ) :
    AEStronglyMeasurable[𝓖 (grid s t n k)] (dφ1 φ Z s t n i k) Q :=
  H.aesm_comp (continuousOn_dφ1 hU hKU hφ i) _

theorem IHyp.aesm_dφ2 (H : IHyp Q 𝓖 K Z β α N B C) (hU : IsOpen U) (hKU : K ⊆ U)
    (hφ : ContDiffOn ℝ 2 φ U) (n : ℕ) (i j : Fin d) (k : ℕ) :
    AEStronglyMeasurable[𝓖 (grid s t n k)] (dφ2 φ Z s t n i j k) Q :=
  H.aesm_comp (continuousOn_dφ2 hU hKU hφ i j) _

theorem IHyp.ae_abs_dφ1_le (H : IHyp Q 𝓖 K Z β α N B C) {M₁ : ℝ}
    (hM₁ : ∀ z ∈ K, ‖fderiv ℝ φ z‖ ≤ M₁) (n : ℕ) (i : Fin d) (k : ℕ) :
    ∀ᵐ ω ∂Q, ‖dφ1 φ Z s t n i k ω‖ ≤ M₁ := by
  filter_upwards [H.mem] with ω hω
  rw [Real.norm_eq_abs]; exact (abs_clm_ev_le _ i).trans (hM₁ _ (hω _))

theorem IHyp.ae_abs_dφ2_le (H : IHyp Q 𝓖 K Z β α N B C) {M₂ : ℝ}
    (hM₂ : ∀ z ∈ K, ‖fderiv ℝ (fderiv ℝ φ) z‖ ≤ M₂) (n : ℕ) (i j : Fin d) (k : ℕ) :
    ∀ᵐ ω ∂Q, ‖dφ2 φ Z s t n i j k ω‖ ≤ M₂ := by
  filter_upwards [H.mem] with ω hω
  rw [Real.norm_eq_abs]; exact (abs_bilin_ev_le _ i j).trans (hM₂ _ (hω _))

theorem IHyp.aesm_incI (H : IHyp Q 𝓖 K Z β α N B C) (hst : s ≤ t) (n k : ℕ)
    (i : Fin d) : AEStronglyMeasurable[𝓖 (grid s t n (k + 1))] (incI β s t n i k) Q := by
  have hle := 𝓖.mono (grid_mono hst n (Nat.le_succ k))
  have hZi : ∀ u, AEStronglyMeasurable[𝓖 u] (fun ω => Z u ω i) Q := fun u =>
    (continuous_apply i).comp_aestronglyMeasurable (H.meas u)
  have hm : AEStronglyMeasurable[𝓖 (grid s t n (k + 1))] (fun ω =>
      (Z (grid s t n (k + 1)) ω i - Z 0 ω i - N i (grid s t n (k + 1)) ω) -
      (Z (grid s t n k) ω i - Z 0 ω i - N i (grid s t n k) ω)) Q :=
    (((hZi _).sub ((hZi 0).mono (𝓖.mono zero_le))).sub ((H.mart i).1 _).aestronglyMeasurable).sub
      ((((hZi _).sub ((hZi 0).mono (𝓖.mono zero_le))).sub
        ((H.mart i).1 _).aestronglyMeasurable).mono hle)
  refine hm.congr ?_
  filter_upwards [H.ae_igood s t] with ω hω
  simp only [incI, hω.1.2.2.2.2.1]
  ring

theorem IHyp.stronglyMeasurable_incN (H : IHyp Q 𝓖 K Z β α N B C) (hst : s ≤ t)
    (n k : ℕ) (i : Fin d) : StronglyMeasurable[𝓖 (grid s t n (k + 1))] (incN N s t n i k) :=
  ((H.mart i).1 _).sub (((H.mart i).1 _).mono (𝓖.mono (grid_mono hst n (Nat.le_succ k))))

theorem IHyp.integrable_incN (H : IHyp Q 𝓖 K Z β α N B C) (n k : ℕ) (i : Fin d) :
    Integrable (incN N s t n i k) Q :=
  ((H.mart i).integrable _).sub ((H.mart i).integrable _)

theorem IHyp.ae_abs_incN_le (H : IHyp Q 𝓖 K Z β α N B C) (hR : ∀ z ∈ K, ‖z‖ ≤ R)
    (n k : ℕ) (i : Fin d) : ∀ᵐ ω ∂Q, |incN N s t n i k ω| ≤ 2 * (2 * R + C) := by
  filter_upwards [H.ae_igood s t] with ω hω
  exact hω.abs_incN_le' hR n k i

theorem IHyp.ae_abs_incJ_le (H : IHyp Q 𝓖 K Z β α N B C) (hst : s ≤ t)
    (n : ℕ) (i j : Fin d) (k : ℕ) : ∀ᵐ ω ∂Q, |incJ α s t n i j k ω| ≤ C := by
  filter_upwards [H.ae_igood s t] with ω hω
  exact (hω.abs_incJ_le' hst n i j k).trans (hω.incG_le n k)

theorem IHyp.aesm_incJ (H : IHyp Q 𝓖 K Z β α N B C) (hst : s ≤ t) (n k : ℕ) (i j : Fin d) :
    AEStronglyMeasurable[𝓖 (grid s t n (k + 1))] (incJ α s t n i j k) Q := by
  have hle := 𝓖.mono (grid_mono hst n (Nat.le_succ k))
  have bm : ∀ u, StronglyMeasurable[𝓖 u] fun ω => N i u ω * N j u ω - B i j u ω := fun u =>
    (((H.mart i).1 u).mul ((H.mart j).1 u)).sub ((H.bracket i j).1 u)
  have hm : StronglyMeasurable[𝓖 (grid s t n (k + 1))] fun ω =>
      (N i (grid s t n (k + 1)) ω * N j (grid s t n (k + 1)) ω - B i j (grid s t n (k + 1)) ω) -
      (N i (grid s t n k) ω * N j (grid s t n k) ω - B i j (grid s t n k) ω) :=
    (bm _).sub ((bm _).mono hle)
  refine hm.aestronglyMeasurable.congr ?_
  filter_upwards [H.ae_igood s t] with ω hω
  exact (incJ_eq_bracket hω.1 n i j k).symm

variable [IsProbabilityMeasure Q]

/-- `E[g ΔN^i_k] = 0`. -/
theorem IHyp.integral_mul_incN (H : IHyp Q 𝓖 K Z β α N B C) (hst : s ≤ t)
    (n k : ℕ) (i : Fin d) {g : Ω → ℝ} (hg : AEStronglyMeasurable[𝓖 (grid s t n k)] g Q)
    {C' : ℝ} (hgC : ∀ᵐ ω ∂Q, ‖g ω‖ ≤ C') :
    ∫ ω, g ω * incN N s t n i k ω ∂Q = 0 :=
  martingale_integral_mul_sub_eq_zero (H.mart i) (grid_mono hst n (Nat.le_succ k)) hg hgC

/-- `E[g ΔN^i_k ΔN^j_k] = E[g Δ∫α^{ij}_k]`. -/
theorem IHyp.integral_mul_incN_incN (H : IHyp Q 𝓖 K Z β α N B C)
    (hR : ∀ z ∈ K, ‖z‖ ≤ R) (hst : s ≤ t) (n k : ℕ) (i j : Fin d)
    {g : Ω → ℝ} (hg : AEStronglyMeasurable[𝓖 (grid s t n k)] g Q) {C' : ℝ}
    (hgC : ∀ᵐ ω ∂Q, ‖g ω‖ ≤ C') :
    ∫ ω, g ω * (incN N s t n i k ω * incN N s t n j k ω) ∂Q =
      ∫ ω, g ω * incJ α s t n i j k ω ∂Q := by
  have bd : ∀ (l : ℕ) i, ∀ᵐ ω ∂Q, ‖N i (grid s t n l) ω‖ ≤ 2 * R + C :=
    fun l i => by
      filter_upwards [H.ae_igood s t] with ω hω
      rw [Real.norm_eq_abs]; exact hω.abs_N_grid_le' hR n l i
  have := martingale_integral_mul_incr_incr (H.mart i) (H.mart j) (H.bracket i j)
    (grid_mono hst n (Nat.le_succ k)) (bd k i) (bd (k + 1) i) (bd k j) (bd (k + 1) j) hg hgC
  simp only [incN]
  rw [this]
  refine integral_congr_ae ?_
  filter_upwards [H.ae_igood s t] with ω hω
  rw [incJ_eq_bracket hω.1 n i j k]

omit [IsProbabilityMeasure Q] in
theorem IHyp.stronglyMeasurable_cellSq (H : IHyp Q 𝓖 K Z β α N B C)
    (hst : s ≤ t) (n k : ℕ) : StronglyMeasurable[𝓖 (grid s t n (k + 1))] (cellSq N s t n k) := by
  unfold cellSq
  exact Finset.stronglyMeasurable_fun_sum _ fun i _ => (H.stronglyMeasurable_incN hst n k i).pow 2

omit [IsProbabilityMeasure Q] in
theorem IHyp.ae_cellSq_le (H : IHyp Q 𝓖 K Z β α N B C) (hR : ∀ z ∈ K, ‖z‖ ≤ R)
    (n k : ℕ) :
    ∀ᵐ ω ∂Q, 0 ≤ cellSq N s t n k ω ∧ cellSq N s t n k ω ≤ d * (2 * (2 * R + C)) ^ 2 := by
  filter_upwards [H.ae_igood s t] with ω hω
  refine ⟨Finset.sum_nonneg fun i _ => sq_nonneg _, ?_⟩
  unfold cellSq
  calc ∑ i, incN N s t n i k ω ^ 2 ≤ ∑ _i : Fin d, (2 * (2 * R + C)) ^ 2 :=
        Finset.sum_le_sum fun i _ => by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hω.abs_incN_le' hR n k i) 2
    _ = d * (2 * (2 * R + C)) ^ 2 := by simp

/-- `E[g · cellSq_k] = E[g Σ_i Δ∫α^{ii}_k]` for bounded `𝓖_{t_k}`-a.e. measurable `g`. -/
theorem IHyp.integral_mul_cellSq (H : IHyp Q 𝓖 K Z β α N B C)
    (hR : ∀ z ∈ K, ‖z‖ ≤ R) (hst : s ≤ t) (n k : ℕ)
    {g : Ω → ℝ} (hg : AEStronglyMeasurable[𝓖 (grid s t n k)] g Q) {C' : ℝ}
    (hgC : ∀ᵐ ω ∂Q, ‖g ω‖ ≤ C') :
    ∫ ω, g ω * cellSq N s t n k ω ∂Q = ∫ ω, g ω * ∑ i, incJ α s t n i i k ω ∂Q := by
  have hg' : AEStronglyMeasurable g Q := hg.mono (𝓖.le _)
  have hJi : ∀ i, Integrable (fun ω => g ω * incJ α s t n i i k ω) Q := fun i =>
    (Integrable.of_bound ((H.aesm_incJ hst n k i i).mono (𝓖.le _)) _
      ((H.ae_abs_incJ_le hst n i i k).mono fun ω h => by rwa [Real.norm_eq_abs])).bdd_mul
      hg' hgC
  have hNi : ∀ i, Integrable (fun ω => g ω * (incN N s t n i k ω * incN N s t n i k ω)) Q :=
    fun i => (Integrable.of_bound (((H.stronglyMeasurable_incN hst n k i).mul
      (H.stronglyMeasurable_incN hst n k i)).mono (𝓖.le _)).aestronglyMeasurable
      ((2 * (2 * R + C)) * (2 * (2 * R + C)))
      ((H.ae_abs_incN_le hR n k i).mono fun ω h => by
        rw [Pi.mul_apply, norm_mul, Real.norm_eq_abs]
        exact mul_le_mul h h (abs_nonneg _) ((abs_nonneg _).trans h))).bdd_mul hg' hgC
  unfold cellSq
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ => by simpa [sq] using hNi i,
    integral_finsetSum _ fun i _ => hJi i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← H.integral_mul_incN_incN hR hst n k i i hg hgC]
  simp [sq]

/-- Pathwise: `Σ_{l ∈ S} Σ_i Δ∫α^{ii}_l ≤ d C` for any set `S` of cells. -/
theorem IGood.sum_incJ_diag_le {ω : Ω} (hω : IGood K Z β α N B C s t ω) (hst : s ≤ t) (n : ℕ)
    (S : Finset ℕ) (hS : S ⊆ Finset.range (n + 1)) :
    ∑ l ∈ S, ∑ i, incJ α s t n i i l ω ≤ d * C := by
  calc ∑ l ∈ S, ∑ i, incJ α s t n i i l ω ≤ ∑ l ∈ S, ∑ _i : Fin d, incG β α s t n l ω :=
        Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun i _ =>
          (le_abs_self _).trans (hω.abs_incJ_le' hst n i i l)
    _ = d * ∑ l ∈ S, incG β α s t n l ω := by simp [Finset.mul_sum]
    _ ≤ d * ∑ l ∈ Finset.range (n + 1), incG β α s t n l ω := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hS
          fun l _ _ => hω.incG_nonneg hst n l) (Nat.cast_nonneg d)
    _ ≤ d * C := mul_le_mul_of_nonneg_left (hω.sum_incG_le hst n) (Nat.cast_nonneg d)

theorem IHyp.integrable_cellSq (H : IHyp Q 𝓖 K Z β α N B C) (hR : ∀ z ∈ K, ‖z‖ ≤ R)
    (hst : s ≤ t) (n k : ℕ) : Integrable (cellSq N s t n k) Q :=
  Integrable.of_bound ((H.stronglyMeasurable_cellSq hst n k).mono (𝓖.le _)).aestronglyMeasurable
    _ ((H.ae_cellSq_le hR n k).mono fun ω h => by
      rw [Real.norm_eq_abs, abs_of_nonneg h.1]; exact h.2)

/-- **First moment of `S_n`.** -/
theorem IHyp.integral_sqSum_le' (H : IHyp Q 𝓖 K Z β α N B C)
    (hR : ∀ z ∈ K, ‖z‖ ≤ R) (hst : s ≤ t) (n : ℕ) :
    ∫ ω, sqSum N s t n ω ∂Q ≤ d * C := by
  have e : sqSum N s t n = fun ω => ∑ k ∈ Finset.range (n + 1), cellSq N s t n k ω := rfl
  have hJ : ∀ k, Integrable (fun ω => ∑ i, incJ α s t n i i k ω) Q := fun k =>
    integrable_finsetSum _ fun i _ => Integrable.of_bound
      ((H.aesm_incJ hst n k i i).mono (𝓖.le _)) _
      ((H.ae_abs_incJ_le hst n i i k).mono fun ω h => by rwa [Real.norm_eq_abs])
  have hk : ∀ k, ∫ ω, cellSq N s t n k ω ∂Q = ∫ ω, ∑ i, incJ α s t n i i k ω ∂Q := fun k => by
    have := H.integral_mul_cellSq hR hst n k (g := fun _ => (1 : ℝ))
      aestronglyMeasurable_const (C' := 1) (ae_of_all _ fun _ => by simp)
    simpa using this
  rw [e, integral_finsetSum _ fun k _ => H.integrable_cellSq hR hst n k,
    Finset.sum_congr rfl fun k _ => hk k, ← integral_finsetSum _ fun k _ => hJ k]
  calc ∫ ω, ∑ k ∈ Finset.range (n + 1), ∑ i, incJ α s t n i i k ω ∂Q ≤ ∫ _ω, (d * C : ℝ) ∂Q :=
        integral_mono_ae (integrable_finsetSum _ fun k _ => hJ k) (integrable_const _)
          ((H.ae_igood s t).mono fun ω hω => hω.sum_incJ_diag_le hst n _ le_rfl)
    _ = d * C := by simp

end BlockBand.SourceProcess.Stochastic.SemimartingaleIto
