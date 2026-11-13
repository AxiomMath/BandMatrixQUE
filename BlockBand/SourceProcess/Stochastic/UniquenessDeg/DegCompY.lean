module
public import BlockBand.SourceProcess.Stochastic.UniquenessDeg.DegSetup
public import BlockBand.SourceProcess.Stochastic.UniquenessDeg.DegMeas
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The regularized Euler scheme versus the degenerate stopped solution

Setting: a `DegSetup c W P`, Euler grid `m`, regularization
`ε_n = regSeq n`, integer horizon `N`.

* `degErr S n N = E ∫_{(0,N]} 1_{[[0,τ]]} 2 d² M² frob(tikX(c.σ Y) ε_n - pinvX(c.σ Y))`:
  the regularization error, finite (`degErr_ne_top`).

The comparison is proved in the sibling module, **`lintegral_degX_stop_sub_le`**: for `t ≤ N`,
`E |X^{m,n}_{t∧τ} - Y_{t∧τ}|² ≤ gronCI(N, degLip c) (N δ_c 2^{-m} + degErr S n N)`
(`lintegral_sq_le_gronwall_abs` against the joint integrator; isometry
`lintegral_sq_vecCont_gen`; pointwise bound `coefSq_vsY`).
-/

namespace BlockBand.SourceProcess.Stochastic.UniquenessDeg
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.GeneralIntegral
open BlockBand.SourceProcess.Stochastic.Levy
open BlockBand.SourceProcess.Stochastic.Representation
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.SourceProcess.Stochastic.Uniqueness
open BlockBand.SourceProcess.FiniteDriverIntegration.ContinuousIto
open scoped NNReal ENNReal

variable {d : ℕ} {c : LipCoef d} {W : Set (Fin d → ℝ)} {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- The regularization error at level `n` up to the horizon `N`. -/
def degErr (S : DegSetup c W P) (n N : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, (∫⁻ r in Ioc (0 : ℝ) N, (stopSet S.τ).indicator (fun p => ENNReal.ofReal
    (2 * d ^ 2 * c.M ^ 2 * frob (fun k c' => tikX (c.σ (S.Y p.1.toNNReal p.2)) (regSeq n) k c' +
      -pinvX (c.σ (S.Y p.1.toNNReal p.2)) k c'))) (r, ω)) ∂P

theorem quad_nonneg_zDens (s : Matrix (Fin d) (Fin d) ℝ) (u : Fin d ⊕ Fin (d + d) → ℝ) :
    0 ≤ ∑ c₁, ∑ c₂, u c₁ * u c₂ * zDens s c₁ c₂ := by
  rw [quad_zDens]; positivity

theorem sigma_entry_measurable (c : LipCoef d) {X : Type*} [MeasurableSpace X]
    {f : X → Fin d → ℝ} (hf : Measurable f) (i j : Fin d) :
    Measurable fun x => c.σ (f x) i j :=
  ((continuous_id.matrix_elem i j).comp c.continuous_σ).measurable.comp hf

theorem sq2_sub_le (c : LipCoef d) (x y : Fin d → ℝ) :
    sq2 (fun i k => c.σ x i k - c.σ y i k) ≤ d ^ 2 * (2 * c.M) ^ 2 := by
  unfold sq2
  calc ∑ i, ∑ k, (c.σ x i k - c.σ y i k) ^ 2 ≤ ∑ _i : Fin d, ∑ _k : Fin d, (2 * c.M) ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => by
          rw [← sq_abs]
          refine pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans ?_) 2
          linarith [c.bd_σ x i k, c.bd_σ y i k]
    _ = d ^ 2 * (2 * c.M) ^ 2 := by simp; ring

theorem degErr_ne_top (S : DegSetup c W P) (n N : ℕ) : degErr S n N ≠ ⊤ := by
  refine ne_top_of_le_ne_top (b := ∫⁻ _ω, (∫⁻ _r in Ioc (0 : ℝ) N,
    ENNReal.ofReal (2 * d ^ 2 * c.M ^ 2 * (4 * d))) ∂P) ?_ (lintegral_mono fun ω =>
      lintegral_mono fun r => ?_)
  · simp [lintegral_const, ENNReal.mul_eq_top]
  · classical
    rw [indicator_apply]
    split_ifs
    · refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        (frob_tikX_sub_pinvX_le _ (regSeq_pos n)) (by positivity))
    · exact zero_le

end BlockBand.SourceProcess.Stochastic.UniquenessDeg
