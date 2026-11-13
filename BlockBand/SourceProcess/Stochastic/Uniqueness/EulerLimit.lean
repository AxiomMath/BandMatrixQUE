module
public import BlockBand.SourceProcess.Stochastic.Uniqueness.EulerStep
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Almost sure convergence of the Euler schemes

Setting: `(Ω, 𝓕, P)` a probability space with a raw filtration, `B` a `𝓕`-Brownian motion, `ξ`
`𝓕_0`-measurable, `c : LipCoef d`.

* `eulLim c ξ B t ω = lim_m X^m_t(ω)` (`limUnder`, junk where the limit does not exist).
* **`tendsto_eulLim`**: for every `t`, a.s. `X^m_t → eulLim t` (the `L²` increments
  `E|X^{m+1}_t - X^m_t|² ≤ K 2^{-m}` give `∑_m E|X^{m+1}_t - X^m_t| < ∞`).
-/

namespace BlockBand.SourceProcess.Stochastic.Uniqueness
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open BlockBand.SourceProcess.Stochastic.Levy
open scoped NNReal ENNReal

variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
  {B : ℝ≥0 → Ω → Fin d → ℝ} {ξ : Ω → Fin d → ℝ}

theorem measurable_eulX (c : LipCoef d) (m : ℕ) (hB : ∀ t, Measurable (B t))
    (hE : ∀ j, Measurable (eulE c m ξ B j)) (t : ℝ≥0) : Measurable (eulX c m ξ B t) := by
  have h1 := hE (gridIdx m t)
  have hb := c.continuous_b
  have hσ := c.continuous_σ
  have hG : Continuous fun p : (Fin d → ℝ) × (Fin d → ℝ) × (Fin d → ℝ) =>
      p.1 + ((t : ℝ) - gridT m (gridIdx m t)) • c.b p.1 + c.σ p.1 *ᵥ (p.2.1 - p.2.2) := by
    have h1 : Continuous fun p : (Fin d → ℝ) × (Fin d → ℝ) × (Fin d → ℝ) =>
        c.σ p.1 *ᵥ (p.2.1 - p.2.2) := (hσ.comp continuous_fst).matrix_mulVec (by fun_prop)
    fun_prop
  exact hG.measurable.comp (h1.prodMk ((hB t).prodMk (hB _)))

/-- The limit of the Euler schemes. -/
def eulLim (c : LipCoef d) (ξ : Ω → Fin d → ℝ) (B : ℝ≥0 → Ω → Fin d → ℝ) (t : ℝ≥0) (ω : Ω) :
    Fin d → ℝ :=
  limUnder atTop fun m => eulX c m ξ B t ω

theorem enorm_le_of_sq (v : Fin d → ℝ) : ‖v‖ₑ ^ 2 ≤ ∑ i, ‖v i‖ₑ ^ 2 := by
  rw [← ofReal_sum_sq, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (sq_norm_le_sum v)

variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The Euler schemes converge almost surely at every time.** -/
theorem tendsto_eulLim (hB : IsFiltrationBrownian P 𝓕 B) (c : LipCoef d)
    (hξ : Measurable[𝓕 0] ξ) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, Tendsto (fun m => eulX c m ξ B t ω) atTop (𝓝 (eulLim c ξ B t ω)) := by
  have hBm : ∀ t, Measurable (B t) := fun t => ((hB.adapted t).mono (𝓕.le t)).measurable
  have hE : ∀ m j, Measurable (eulE c m ξ B j) := fun m j =>
    (measurable_eulE c m (fun t => (hB.adapted t).measurable) hξ j).mono (𝓕.le _) le_rfl
  have hX : ∀ m, Measurable (eulX c m ξ B t) := fun m => measurable_eulX c m hBm (hE m) t
  set n := ⌈(t : ℝ)⌉₊
  have htn : t ≤ (n : ℝ≥0) := by
    rw [← NNReal.coe_le_coe, NNReal.coe_natCast]; exact Nat.le_ceil _
  set K : ℝ := gronC n (eulLip c) * (2 * eulDelta c)
  have hK : 0 ≤ K := mul_nonneg (gronC_nonneg _ _) (by linarith [eulDelta_nonneg c])
  set Z : ℕ → Ω → ℝ≥0∞ := fun m ω => ‖eulX c (m + 1) ξ B t ω - eulX c m ξ B t ω‖ₑ
  have hZm : ∀ m, Measurable (Z m) := fun m => ((hX (m + 1)).sub (hX m)).enorm
  set a : ℕ → ℝ := fun m => √K * (1 / √2) ^ m
  have ha0 : ∀ m, 0 ≤ a m := fun m => by positivity
  have hsq2 : (0 : ℝ) < √2 := by positivity
  have ha : Summable a := (summable_geometric_of_lt_one (by positivity)
    (by rw [div_lt_one hsq2]; exact Real.one_lt_sqrt_two)).mul_left _
  have hbound : ∀ m, ∫⁻ ω, Z m ω ∂P ≤ ENNReal.ofReal (a m) := fun m => by
    have h1 := NativeSDE.lintegral_sq_le_measure_mul (m := P) (hZm m).aemeasurable
    rw [measure_univ, one_mul] at h1
    have h2 : ∫⁻ ω, Z m ω ^ 2 ∂P ≤ ENNReal.ofReal (K / 2 ^ m) := by
      refine (lintegral_mono fun ω => enorm_le_of_sq _).trans ?_
      refine (lintegral_eulX_succ_sub_le hB c hξ n m htn).trans_eq ?_
      rw [← ENNReal.ofReal_mul (gronC_nonneg _ _)]
      congr 1
      simp only [K]; ring
    have h3 : ENNReal.ofReal (K / 2 ^ m) = ENNReal.ofReal (a m) ^ 2 := by
      rw [← ENNReal.ofReal_pow (ha0 m)]
      congr 1
      simp only [a]
      rw [mul_pow, Real.sq_sqrt hK, ← pow_mul, mul_comm m 2, pow_mul, div_pow, one_pow,
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), one_div, inv_pow, div_eq_mul_inv]
    rw [h3] at h2
    exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 (h1.trans h2)
  have hsum : ∫⁻ ω, ∑' m, Z m ω ∂P ≠ ⊤ := by
    rw [lintegral_tsum fun m => (hZm m).aemeasurable]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
    rw [← ENNReal.ofReal_tsum_of_nonneg ha0 ha]
    exact ENNReal.ofReal_ne_top
  have hTm : Measurable fun ω => ∑' m, Z m ω := by
    simp_rw [ENNReal.tsum_eq_iSup_sum]
    exact .iSup fun s => s.measurable_fun_sum fun i _ => hZm i
  filter_upwards [ae_lt_top hTm hsum] with ω hω
  have hs : Summable fun m => dist (eulX c m ξ B t ω) (eulX c m.succ ξ B t ω) := by
    have := ENNReal.summable_toReal hω.ne
    refine this.congr fun m => ?_
    simp only [Z, toReal_enorm]
    rw [dist_comm, dist_eq_norm]
  exact tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hs))

end BlockBand.SourceProcess.Stochastic.Uniqueness
