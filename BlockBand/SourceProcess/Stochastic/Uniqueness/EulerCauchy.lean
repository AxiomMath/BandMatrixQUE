module
public import BlockBand.SourceProcess.Stochastic.Uniqueness.EulerEps
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Bounds for the `L²` Cauchy property of the Euler schemes

Setting: `(Ω, 𝓕, P)` a probability space with a raw filtration, `B` a `𝓕`-Brownian motion, `ξ`
`𝓕_0`-measurable, `c : LipCoef d` (Lipschitz constant `L`, bound `M`), integer horizon `n`.

This module provides the elementary bounds and the constants `eulDelta`, `eulLip` for the main
estimate, proved in the sibling module, **`lintegral_eulX_succ_sub_le`**: for `t ≤ n`,
`E |X^{m+1}_t - X^m_t|² ≤ C(n, L₃) · 2 δ_c 2^{-m}` with `L₃ = 3 (d + d²) L²`,
`δ_c = 2 d M² (1 + d²)` and `C` the Gronwall constant `gronC` (squared Euclidean norm, `ℝ≥0∞`).
Proof: `lintegral_sq_le_gronwall` with `D = X^{m+1} - X^m` (`eulX_rep` for both schemes, the
same `ξ`), `β = b(E'_{j'}) - b(E_j)`, `γ = σ(E'_{j'}) - σ(E_j)`, the joint versions `eulXv`
and the discretisation errors `ε = eulEps' + eulEps` (`lintegral_eulEps_le`).
-/

namespace BlockBand.SourceProcess.Stochastic.Uniqueness
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open BlockBand.SourceProcess.Stochastic.GeneralIntegral
open BlockBand.SourceProcess.Stochastic.Levy
open BlockBand.SourceProcess.Stochastic.Representation
open scoped NNReal ENNReal

variable {d : ℕ}

theorem sq_norm_le_sum (v : Fin d → ℝ) : ‖v‖ ^ 2 ≤ ∑ i, v i ^ 2 := by
  have h0 : 0 ≤ √(∑ i, v i ^ 2) := Real.sqrt_nonneg _
  have h : ‖v‖ ≤ √(∑ i, v i ^ 2) := (pi_norm_le_iff_of_nonneg h0).2 fun i => by
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun j => v j ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ i))
  calc ‖v‖ ^ 2 ≤ √(∑ i, v i ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem coef_diff_bound (c : LipCoef d) (x y : Fin d → ℝ) :
    (∑ i, (c.b x i - c.b y i) ^ 2) + ∑ i, ∑ l, (c.σ x i l - c.σ y i l) ^ 2 ≤
      (d + d ^ 2) * c.L ^ 2 * ‖x - y‖ ^ 2 := by
  have h : ∀ a : ℝ, |a| ≤ c.L * ‖x - y‖ → a ^ 2 ≤ c.L ^ 2 * ‖x - y‖ ^ 2 := fun a ha => by
    rw [← mul_pow, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) ha 2
  calc (∑ i, (c.b x i - c.b y i) ^ 2) + ∑ i, ∑ l, (c.σ x i l - c.σ y i l) ^ 2
      ≤ (∑ _i : Fin d, c.L ^ 2 * ‖x - y‖ ^ 2) + ∑ _i : Fin d, ∑ _l : Fin d,
          c.L ^ 2 * ‖x - y‖ ^ 2 :=
        add_le_add (Finset.sum_le_sum fun i _ => h _ (c.lip_b x y i))
          (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun l _ => h _ (c.lip_σ x y i l))
    _ = (d + d ^ 2) * c.L ^ 2 * ‖x - y‖ ^ 2 := by simp; ring

theorem sq_norm_sub_le_three (x u v y : Fin d → ℝ) :
    ‖x - y‖ ^ 2 ≤ 3 * ((∑ i, (x - u) i ^ 2) + (∑ i, (u - v) i ^ 2) + ∑ i, (v - y) i ^ 2) := by
  have htri : ‖x - y‖ ≤ ‖x - u‖ + ‖u - v‖ + ‖v - y‖ := by
    calc ‖x - y‖ = ‖(x - u) + (u - v) + (v - y)‖ := by congr 1; abel
      _ ≤ _ := norm_add₃_le
  have h1 := sq_norm_le_sum (x - u)
  have h2 := sq_norm_le_sum (u - v)
  have h3 := sq_norm_le_sum (v - y)
  have hn := pow_le_pow_left₀ (norm_nonneg _) htri 2
  nlinarith [sq_nonneg (‖x - u‖ - ‖u - v‖), sq_nonneg (‖u - v‖ - ‖v - y‖),
    sq_nonneg (‖x - u‖ - ‖v - y‖), norm_nonneg (x - u), norm_nonneg (u - v), norm_nonneg (v - y)]

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}

theorem isBddPred_sub {f g : ℝ × Ω → ℝ} (hf : IsBddPred 𝓕 f) (hg : IsBddPred 𝓕 g) :
    IsBddPred 𝓕 fun p => f p - g p := by
  obtain ⟨C, hC0, hC⟩ := hf.bdd
  obtain ⟨D, hD0, hD⟩ := hg.bdd
  exact ⟨hf.sm.sub hg.sm, C + D, add_nonneg hC0 hD0, fun p =>
    (abs_sub _ _).trans (add_le_add (hC p) (hD p))⟩

theorem bpL2_sub' {μ : Measure (ℝ × Ω)} [IsFiniteMeasure μ] {f g : ℝ × Ω → ℝ}
    (hf : IsBddPred 𝓕 f) (hg : IsBddPred 𝓕 g) :
    bpL2 μ (isBddPred_sub hf hg) = bpL2 μ hf - bpL2 μ hg := by
  refine predL2_ext 𝓕 ?_
  rw [Submodule.coe_sub]
  filter_upwards [bpL2_coeFn (μ := μ) (isBddPred_sub hf hg), bpL2_coeFn (μ := μ) hf,
    bpL2_coeFn (μ := μ) hg,
    Lp.coeFn_sub ((bpL2 μ hf : PredL2 𝓕 μ) : Lp ℝ 2 μ) ((bpL2 μ hg : PredL2 𝓕 μ) : Lp ℝ 2 μ)]
    with p h1 h2 h3 h4
  rw [h1, h4, Pi.sub_apply, h2, h3]

theorem gridT_succ_mul_pow (m n : ℕ) : gridT (m + 1) (n * 2 ^ (m + 1)) = gridT m (n * 2 ^ m) := by
  rw [gridT_mul_pow, gridT_mul_pow]

/-- The Euler error constant `δ_c = 2 d M² (1 + d²)`. -/
def eulDelta (c : LipCoef d) : ℝ := 2 * d * c.M ^ 2 * (1 + d ^ 2)

theorem eulDelta_nonneg (c : LipCoef d) : 0 ≤ eulDelta c := by unfold eulDelta; positivity

/-- The Gronwall constant `3 (d + d²) L²` of the Euler comparison. -/
def eulLip (c : LipCoef d) : ℝ≥0 := ⟨3 * (d + d ^ 2) * c.L ^ 2, by positivity⟩

theorem ofReal_sum_sq (v : Fin d → ℝ) : ENNReal.ofReal (∑ i, v i ^ 2) = ∑ i, ‖v i‖ₑ ^ 2 := by
  rw [ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg _]
  simp_rw [enorm_sq_eq_ofReal]

/-- The pointwise Gronwall bound for two Euler grid values `x, y` and interpolants `u, v`. -/
theorem coefSq_euler_bound (c : LipCoef d) (x y u v : Fin d → ℝ) :
    ((∑ i, ‖c.b x i - c.b y i‖ₑ ^ 2) + ∑ i, ∑ l, ‖c.σ x i l - c.σ y i l‖ₑ ^ 2) ≤
      (eulLip c : ℝ≥0∞) * ((∑ i, ‖(u - v) i‖ₑ ^ 2) +
        ((∑ i, ‖u i - x i‖ₑ ^ 2) + ∑ i, ‖v i - y i‖ₑ ^ 2)) := by
  have h1 : ((∑ i, ‖c.b x i - c.b y i‖ₑ ^ 2) + ∑ i, ∑ l, ‖c.σ x i l - c.σ y i l‖ₑ ^ 2) =
      ENNReal.ofReal ((∑ i, (c.b x i - c.b y i) ^ 2) + ∑ i, ∑ l, (c.σ x i l - c.σ y i l) ^ 2) := by
    rw [ENNReal.ofReal_add (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _),
      ofReal_sum_sq (fun i => c.b x i - c.b y i),
      ENNReal.ofReal_sum_of_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ofReal_sum_sq (fun l => c.σ x i l - c.σ y i l)]
  have h2 : (eulLip c : ℝ≥0∞) * ((∑ i, ‖(u - v) i‖ₑ ^ 2) +
      ((∑ i, ‖u i - x i‖ₑ ^ 2) + ∑ i, ‖v i - y i‖ₑ ^ 2)) =
      ENNReal.ofReal (3 * (d + d ^ 2) * c.L ^ 2 * ((∑ i, (u - v) i ^ 2) +
        ((∑ i, (u i - x i) ^ 2) + ∑ i, (v i - y i) ^ 2))) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (Finset.sum_nonneg fun _ _ =>
      sq_nonneg _) (by positivity), ENNReal.ofReal_add (Finset.sum_nonneg fun _ _ =>
      sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _), ofReal_sum_sq (u - v),
      ofReal_sum_sq (fun i => u i - x i), ofReal_sum_sq (fun i => v i - y i)]
    congr 1
    exact (ENNReal.ofReal_coe_nnreal).symm
  rw [h1, h2]
  refine ENNReal.ofReal_le_ofReal ((coef_diff_bound c x y).trans ?_)
  have h3 := sq_norm_sub_le_three x u v y
  have e1 : ∑ i, (x - u) i ^ 2 = ∑ i, (u i - x i) ^ 2 :=
    Finset.sum_congr rfl fun i _ => by simp only [Pi.sub_apply]; ring
  have e3 : ∑ i, (v - y) i ^ 2 = ∑ i, (v i - y i) ^ 2 :=
    Finset.sum_congr rfl fun i _ => by simp only [Pi.sub_apply]
  rw [e1, e3] at h3
  have hL : 0 ≤ (d + d ^ 2 : ℝ) * c.L ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h3 hL]

end BlockBand.SourceProcess.Stochastic.Uniqueness
