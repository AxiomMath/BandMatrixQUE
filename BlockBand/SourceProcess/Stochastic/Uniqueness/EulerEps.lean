module
public import BlockBand.SourceProcess.Stochastic.Uniqueness.EulerBound
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The Euler discretisation error in `L²`

Setting as in `EulerBound`. **`lintegral_eulEps_le`**: for every `r ≥ 0`,
`E |X_r - E_{j(r)}|² ≤ 2 d M² (1 + d²) 2^{-m}` (squared Euclidean norm; `M` the coefficient
bound), from `X_r - E_j = (r - t_j) b(E_j) + σ(E_j)(B_r - B_{t_j})`, `0 ≤ r - t_j ≤ 2^{-m}`,
Cauchy–Schwarz and `E (B^k_r - B^k_s)² = r - s` (`integral_sq_incr`).
-/

namespace BlockBand.SourceProcess.Stochastic.Uniqueness
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open BlockBand.SourceProcess.Stochastic.Levy
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ} {d : ℕ}
  {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → Fin d → ℝ}

omit [IsProbabilityMeasure P] in
/-- `E (B^k_t - B^k_s)² = t - s`. -/
theorem integral_sq_incr (hB : IsFiltrationBrownian P 𝓕 B) {s t : ℝ≥0} (hst : s ≤ t)
    (k : Fin d) : ∫ ω, (B t ω k - B s ω k) ^ 2 ∂P = (t : ℝ) - s := by
  have hm := hB.measurable_incr s t
  have hf : Measurable fun x : Fin d → ℝ => (x k) ^ 2 := (measurable_pi_apply k).pow_const 2
  calc ∫ ω, (B t ω k - B s ω k) ^ 2 ∂P
      = ∫ x, (x k) ^ 2 ∂(P.map fun ω => B t ω - B s ω) := by
        rw [integral_map hm.aemeasurable hf.aestronglyMeasurable]; rfl
    _ = ∫ x, (x k) ^ 2 ∂gaussPi d (t - s) := by rw [(hB.hasLaw s t hst).map_eq]
    _ = ∫ y, y ^ 2 ∂gaussianReal 0 (t - s) :=
        integral_comp_coord (t - s) k (f := fun y => y ^ 2) (measurable_id.pow_const 2)
    _ = (t : ℝ) - s := by rw [integral_sq_gaussianReal, NNReal.coe_sub hst]

theorem grid_gap (m : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ (r.toNNReal : ℝ) - gridT m (gridIdx m r.toNNReal) ∧
      (r.toNNReal : ℝ) - gridT m (gridIdx m r.toNNReal) ≤ 1 / 2 ^ m := by
  rcases hr.lt_or_eq with hr | hr
  · have h := mem_grid_of_pos m hr
    have h2 := gridT_succ_sub m (gridIdx m r.toNNReal)
    rw [Real.coe_toNNReal _ hr.le]
    constructor <;> linarith [h.1, h.2]
  · subst hr
    simp only [Real.toNNReal_zero, gridIdx_zero, gridT_zero, NNReal.coe_zero, sub_self, le_refl,
      true_and]
    positivity

/-- **The Euler discretisation error**: `E |X_r - E_{j(r)}|² ≤ 2 d M² (1 + d²) 2^{-m}`. -/
theorem lintegral_eulEps_le (hB : IsFiltrationBrownian P 𝓕 B) (c : LipCoef d) (m : ℕ)
    {ξ : Ω → Fin d → ℝ} {A : Set Ω} (hAP : P Aᶜ = 0) {r : ℝ} (hr : 0 ≤ r) :
    ∫⁻ ω, eulEps c m ξ B A (r, ω) ∂P ≤
      ENNReal.ofReal (2 * d * c.M ^ 2 * (1 + d ^ 2) / 2 ^ m) := by
  set j := gridIdx m r.toNNReal
  set s := gridT m j
  set h : ℝ := (r.toNNReal : ℝ) - s
  obtain ⟨h0, h1⟩ := grid_gap m hr
  have hs : s ≤ r.toNNReal := by
    rw [← NNReal.coe_le_coe]; linarith
  set Δ : Ω → Fin d → ℝ := fun ω => B r.toNNReal ω - B s ω
  set F : Ω → ℝ := fun ω => d * (2 * h ^ 2 * c.M ^ 2 + 2 * d * c.M ^ 2 * ∑ k, Δ ω k ^ 2)
  have hpt : ∀ ω ∈ A, eulEps c m ξ B A (r, ω) ≤ ENNReal.ofReal (F ω) := fun ω hω => by
    have hv : ∀ i, eulXv c m ξ B A (r, ω) i - eulE c m ξ B j ω i =
        h * c.b (eulE c m ξ B j ω) i + ∑ k, c.σ (eulE c m ξ B j ω) i k * Δ ω k := fun i => by
      rw [eulXv_of_mem c m hω r]
      simp only [eulX, eulerX, eulE, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mulVec,
        dotProduct, Pi.sub_apply, Δ, h, s, j]
      ring
    have e : eulEps c m ξ B A (r, ω) =
        ∑ i, ‖eulXv c m ξ B A (r, ω) i - eulE c m ξ B j ω i‖ₑ ^ 2 := rfl
    rw [e]
    simp_rw [hv, enorm_sq_eq_ofReal]
    rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg _]
    refine ENNReal.ofReal_le_ofReal ?_
    have hterm : ∀ i, (h * c.b (eulE c m ξ B j ω) i + ∑ k, c.σ (eulE c m ξ B j ω) i k * Δ ω k) ^ 2
        ≤ 2 * h ^ 2 * c.M ^ 2 + 2 * d * c.M ^ 2 * ∑ k, Δ ω k ^ 2 := fun i => by
      set a := h * c.b (eulE c m ξ B j ω) i
      set b := ∑ k, c.σ (eulE c m ξ B j ω) i k * Δ ω k
      have ha : a ^ 2 ≤ h ^ 2 * c.M ^ 2 := by
        have hb2 : c.b (eulE c m ξ B j ω) i ^ 2 ≤ c.M ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (c.bd_b _ i) 2
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_left hb2 (sq_nonneg _)
      have hb : b ^ 2 ≤ d * c.M ^ 2 * ∑ k, Δ ω k ^ 2 := by
        refine (Finset.sum_mul_sq_le_sq_mul_sq _ _ _).trans (mul_le_mul_of_nonneg_right ?_
          (Finset.sum_nonneg fun k _ => sq_nonneg _))
        calc ∑ k, c.σ (eulE c m ξ B j ω) i k ^ 2 ≤ ∑ _k : Fin d, c.M ^ 2 :=
              Finset.sum_le_sum fun k _ => by
                rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (c.bd_σ _ i k) 2
          _ = d * c.M ^ 2 := by simp
      nlinarith [sq_nonneg (a - b)]
    calc ∑ i, (h * c.b (eulE c m ξ B j ω) i + ∑ k, c.σ (eulE c m ξ B j ω) i k * Δ ω k) ^ 2
        ≤ ∑ _i : Fin d, (2 * h ^ 2 * c.M ^ 2 + 2 * d * c.M ^ 2 * ∑ k, Δ ω k ^ 2) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = F ω := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hΔ : ∀ k, Integrable (fun ω => Δ ω k ^ 2) P := fun k =>
    (hB.memLp_incr hs k).integrable_sq
  have hFi : Integrable F P :=
    ((integrable_const _).add ((integrable_finsetSum _ fun k _ => hΔ k).const_mul _)).const_mul _
  calc ∫⁻ ω, eulEps c m ξ B A (r, ω) ∂P ≤ ∫⁻ ω, ENNReal.ofReal (F ω) ∂P := by
        refine lintegral_mono_ae ?_
        filter_upwards [measure_eq_zero_iff_ae_notMem.1 hAP] with ω hω
        exact hpt ω (by simpa using hω)
    _ = ENNReal.ofReal (∫ ω, F ω ∂P) := (ofReal_integral_eq_lintegral_ofReal hFi
        (Eventually.of_forall fun ω => by positivity)).symm
    _ ≤ ENNReal.ofReal (2 * d * c.M ^ 2 * (1 + d ^ 2) / 2 ^ m) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hE : ∫ ω, F ω ∂P = d * (2 * h ^ 2 * c.M ^ 2 + 2 * d * c.M ^ 2 * (d * h)) := by
          simp only [F]
          rw [integral_const_mul, integral_add (integrable_const _)
            ((integrable_finsetSum _ fun k _ => hΔ k).const_mul _), integral_const,
            integral_const_mul, integral_finsetSum _ fun k _ => hΔ k]
          simp only [Δ, Pi.sub_apply, integral_sq_incr hB hs, probReal_univ, smul_eq_mul,
            one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, h]
        rw [hE]
        have hh : h ≤ 1 := h1.trans (by
          rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num))
        have hh2 : h ^ 2 ≤ 1 / 2 ^ m := by nlinarith
        have hM := sq_nonneg c.M
        have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        have key : h ^ 2 + d ^ 2 * h ≤ (1 + d ^ 2) * (1 / 2 ^ m) := by nlinarith
        calc (d : ℝ) * (2 * h ^ 2 * c.M ^ 2 + 2 * d * c.M ^ 2 * (d * h))
            = 2 * d * c.M ^ 2 * (h ^ 2 + d ^ 2 * h) := by ring
          _ ≤ 2 * d * c.M ^ 2 * ((1 + d ^ 2) * (1 / 2 ^ m)) := by gcongr
          _ = 2 * d * c.M ^ 2 * (1 + d ^ 2) / 2 ^ m := by ring

end BlockBand.SourceProcess.Stochastic.Uniqueness
