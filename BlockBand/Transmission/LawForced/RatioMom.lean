module

public import BlockBand.Transmission.LawForced.RatioBrQ

/-!
# Moments of the expansion size `M`

Abstract law `μ` (probability), `0 ⪯ T ⪯ I`, a measurable `Z` with bilinear `L^p` bounds
`‖u*Zv‖_p ≤ B|u||v|` (the shape of `oneStepFluctuation_bulk` at `Z = U − Ū`), `t = ts_lam hT`,
`g = Re Tr T`.
* `linB_sand_eq`: `linB z t (sand T Z) = −Σ_k t_kΛ_k Re Z'_{kk}`;
* **`eLpNorm_linB_sand_le`**: `‖linB z t (sand T Z)‖_p ≤ BΛ̂g` (Minkowski; note that
  `|linB| ≤ C‖·‖_HS` is false in general, so this separate bound is needed);
* `ratioMf_le`: `M ≤ (|linB(sand T U⁰)| + hs(T,U⁰)) + (|linB B̄| + hs(T,Ū − 1))`;
* **`ratioMf_moment`**: `M^k ∈ L¹` and `E M^k ≤ (B(Λ̂+1)g + c₀)^k`, `c₀ = |linB B̄| + hs(T,Ū−1)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open Matrix Finset MeasureTheory
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers
open BlockBand.Transmission.LawDuality BlockBand.Transmission.Generator
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.PassiveCovariance
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator ENNReal

variable {p W : ℕ} {T : Matrix (Fin W) (Fin W) ℂ} {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω}

theorem linB_sand_eq (z : DualCoord p) (hT : T.PosSemidef) (Z : Matrix (Fin W) (Fin W) ℂ) :
    linB z (ts_lam hT) (sand hT Z) =
      -∑ k, ts_lam hT k * dualLam z (ts_lam hT k) * (ts_ent hT Z k k).re := by
  rw [linB_eq_dualLam]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sand_apply, Real.mul_self_sqrt (ts_lam_nonneg hT k), Complex.re_ofReal_mul]
  ring

theorem continuous_linB (z : DualCoord p) (t : Fin W → ℝ) :
    Continuous (linB z t) := by
  unfold linB
  refine continuous_finsetSum _ fun i _ => ?_
  refine (continuous_const.mul (Complex.continuous_re.comp ?_)).sub
    (continuous_const.mul (Complex.continuous_re.comp ?_)) <;>
  exact (continuous_const.matrix_mul continuous_id).matrix_trace

/-- **`L^p` bound of the first-order fluctuation.** -/
theorem eLpNorm_linB_sand_le {z : DualCoord p} (hz : IsRatioRange z.1 z.2) (hT : T.PosSemidef)
    (ht1 : ∀ i, ts_lam hT i ≤ 1) {Z : Ω → Matrix (Fin W) (Fin W) ℂ} (hZ : Measurable Z)
    {q : ℝ≥0∞} (hq : 1 ≤ q)
    {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ u v : Fin W → ℂ, eLpNorm (fun ω => bilinear u (Z ω) v) q μ ≤
      ENNReal.ofReal (B * vecNorm u * vecNorm v)) :
    eLpNorm (fun ω => linB z (ts_lam hT) (sand hT (Z ω))) q μ ≤
      ENNReal.ofReal (B * (lamHat z * T.trace.re)) := by
  set t := ts_lam hT
  have ht0 := ts_lam_nonneg hT
  set w : Fin W → ℝ := fun k => t k * dualLam z (t k)
  have hw : ∀ k, 0 ≤ w k := fun k => mul_nonneg (ht0 k) (dualLam_nonneg hz (ht0 k) (ht1 k))
  have e : (fun ω => linB z t (sand hT (Z ω))) =
      -∑ k, fun ω => w k * (ts_ent hT (Z ω) k k).re := by
    funext ω; rw [linB_sand_eq]; simp only [Pi.neg_apply, Finset.sum_apply]; rfl
  rw [e, eLpNorm_neg]
  refine (eLpNorm_sum_le hq).trans ?_
  have hk : ∀ k, eLpNorm (fun ω => w k * (ts_ent hT (Z ω) k k).re) q μ ≤
      ENNReal.ofReal (w k * B) := fun k => by
    have h1 : eLpNorm (fun ω => w k * (ts_ent hT (Z ω) k k).re) q μ ≤
        eLpNorm (((w k : ℝ) : ℂ) • fun ω => ts_ent hT (Z ω) k k) q μ := by
      refine eLpNorm_mono (((Complex.measurable_re.comp
        (ts_measurable_ent hT hZ k k)).const_mul _).aestronglyMeasurable) fun ω => ?_
      simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by positivity)
    rw [eLpNorm_const_smul] at h1
    refine h1.trans ?_
    have h2 := hB (ts_vec hT k) (ts_vec hT k)
    rw [ts_vecNorm, mul_one, mul_one] at h2
    have h3 : eLpNorm (fun ω => ts_ent hT (Z ω) k k) q μ ≤ ENNReal.ofReal B := h2
    calc ‖((w k : ℝ) : ℂ)‖ₑ * eLpNorm (fun ω => ts_ent hT (Z ω) k k) q μ
        ≤ ENNReal.ofReal (w k) * ENNReal.ofReal B := by
          refine mul_le_mul' (le_of_eq ?_) h3
          rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (hw k)]
      _ = ENNReal.ofReal (w k * B) := (ENNReal.ofReal_mul (hw k)).symm
  refine (Finset.sum_le_sum fun k _ => hk k).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg fun k _ => mul_nonneg (hw k) hB0]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Finset.sum_mul, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ hB0
  have := (sum_t_dualLam_le hz ht0 ht1).2
  rwa [ts_sum_lam hT] at this

theorem ratioMf_le (z : DualCoord p) (hT : T.PosSemidef) (U Ub : Matrix (Fin W) (Fin W) ℂ) :
    ratioMf z (ts_lam hT) (sand hT U) ≤
      (|linB z (ts_lam hT) (sand hT (U - Ub))| + hsSandwich T (U - Ub)) +
        (|linB z (ts_lam hT) (sand hT Ub - dmat (ts_lam hT))| + hsSandwich T (Ub - 1)) := by
  set t := ts_lam hT
  have hD : dmat t = sand hT 1 := by rw [sand_one]; rfl
  have e1 : sand hT U - dmat t = sand hT (U - Ub) + (sand hT Ub - dmat t) := by
    rw [sand_sub]; abel
  have e2 : Real.sqrt (frobSq (sand hT U - dmat t)) = hsSandwich T (U - 1) := by
    rw [hD, ← sand_sub, frobSq_sand,
      Real.sqrt_sq (show 0 ≤ hsSandwich T (U - 1) from Real.sqrt_nonneg _)]
  have e3 : U - 1 = (U - Ub) + (Ub - 1) := by abel
  unfold ratioMf
  rw [linR_eq_linB, e2, e1, linB_add, e3]
  have := abs_add_le (linB z t (sand hT (U - Ub))) (linB z t (sand hT Ub - dmat t))
  have := hsSandwich_add_le hT (U - Ub) (Ub - 1)
  linarith

theorem continuous_ratioMf (z : DualCoord p) (t : Fin W → ℝ) :
    Continuous (ratioMf z t) := by
  unfold ratioMf
  have hs : Continuous fun S : Matrix (Fin W) (Fin W) ℂ => S - dmat t :=
    continuous_id.sub continuous_const
  exact ((continuous_linB z t).comp hs).abs.add
    (Real.continuous_sqrt.comp (continuous_frobSq.comp hs))

/-- **Moments of `M`.** -/
theorem ratioMf_moment [IsProbabilityMeasure μ] {z : DualCoord p} (hz : IsRatioRange z.1 z.2)
    (hT : T.PosSemidef) (ht1 : ∀ i, ts_lam hT i ≤ 1) {U : Ω → Matrix (Fin W) (Fin W) ℂ}
    (hU : Measurable U) (k : ℕ) (hk : 2 ≤ k) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ u v : Fin W → ℂ, eLpNorm (fun ω => bilinear u (U ω - matrixExpect μ U) v)
      (ENNReal.ofReal (k : ℝ)) μ ≤ ENNReal.ofReal (B * vecNorm u * vecNorm v)) :
    Integrable (fun ω => ratioMf z (ts_lam hT) (sand hT (U ω)) ^ k) μ ∧
      ∫ ω, ratioMf z (ts_lam hT) (sand hT (U ω)) ^ k ∂μ ≤
        (B * (lamHat z * T.trace.re) + B * T.trace.re +
          (|linB z (ts_lam hT) (sand hT (matrixExpect μ U) - dmat (ts_lam hT))| +
            hsSandwich T (matrixExpect μ U - 1))) ^ k := by
  set t := ts_lam hT
  set Ub := matrixExpect μ U
  set c₀ := |linB z t (sand hT Ub - dmat t)| + hsSandwich T (Ub - 1)
  have hc₀ : 0 ≤ c₀ := add_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  have hg0 : 0 ≤ T.trace.re := by
    rw [← ts_sum_lam hT]; exact Finset.sum_nonneg fun k _ => ts_lam_nonneg hT k
  have hZ : Measurable fun ω => U ω - Ub := hU.sub_const _
  have hq2 : (2 : ℝ≥0∞) ≤ ENNReal.ofReal (k : ℝ) := by
    rw [ENNReal.ofReal_natCast]; exact_mod_cast hk
  have hq : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (k : ℝ) := le_trans (by norm_num) hq2
  have hL := eLpNorm_linB_sand_le hz hT ht1 hZ hq hB0 hB
  have hH := eLpNorm_hsSandwich_le μ hT hZ hq2 hB0 hB
  have hLm : Measurable fun ω => linB z t (sand hT (U ω - Ub)) :=
    (continuous_linB z t).measurable.comp ((continuous_sand hT).measurable.comp hZ)
  have hHm : Measurable fun ω => hsSandwich T (U ω - Ub) := by
    have : (fun ω => hsSandwich T (U ω - Ub)) =
        fun ω => Real.sqrt (frobSq (sand hT (U ω - Ub))) := funext fun ω => by
      rw [frobSq_sand, Real.sqrt_sq (show 0 ≤ hsSandwich T (U ω - Ub) from Real.sqrt_nonneg _)]
    rw [this]
    exact (Real.continuous_sqrt.comp continuous_frobSq).measurable.comp
      ((continuous_sand hT).measurable.comp hZ)
  set Mf := fun ω => ratioMf z t (sand hT (U ω))
  have hMm : Measurable Mf := (continuous_ratioMf z t).measurable.comp
    ((continuous_sand hT).measurable.comp hU)
  have hM0 : ∀ ω, 0 ≤ Mf ω := fun ω => add_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  set σ := B * (lamHat z * T.trace.re) + B * T.trace.re + c₀
  have hσ : 0 ≤ σ := by have := lamHat_nonneg hz; positivity
  have hN : eLpNorm (fun ω => |linB z t (sand hT (U ω - Ub))| + hsSandwich T (U ω - Ub) + c₀)
      (ENNReal.ofReal (k : ℝ)) μ ≤ ENNReal.ofReal σ := by
    refine (eLpNorm_add_le hq).trans ?_
    have hc : eLpNorm (fun _ : Ω => c₀) (ENNReal.ofReal (k : ℝ)) μ = ENNReal.ofReal c₀ := by
      rw [eLpNorm_const _ (by positivity) (IsProbabilityMeasure.ne_zero μ), measure_univ,
        ENNReal.one_rpow, mul_one, ← ofReal_norm, Real.norm_of_nonneg hc₀]
    have h1 := eLpNorm_add_le (μ := μ) (f := fun ω => |linB z t (sand hT (U ω - Ub))|)
      (g := fun ω => hsSandwich T (U ω - Ub)) hq
    have h2 : eLpNorm (fun ω => |linB z t (sand hT (U ω - Ub))|) (ENNReal.ofReal (k : ℝ)) μ ≤
        ENNReal.ofReal (B * (lamHat z * T.trace.re)) :=
      (eLpNorm_mono hLm.abs.aestronglyMeasurable fun ω => by
        simp only [Real.norm_eq_abs, abs_abs]; exact le_rfl).trans hL
    rw [hc]
    have := add_le_add (h1.trans (add_le_add h2 hH)) (le_refl (ENNReal.ofReal c₀))
    refine this.trans (le_of_eq ?_)
    have := lamHat_nonneg hz
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) hc₀]
  have hMle : eLpNorm Mf (ENNReal.ofReal (k : ℝ)) μ ≤ ENNReal.ofReal σ := by
    refine (eLpNorm_mono hMm.aestronglyMeasurable fun ω => ?_).trans hN
    have h0 : 0 ≤ hsSandwich T (U ω - Ub) := Real.sqrt_nonneg _
    rw [Real.norm_of_nonneg (hM0 ω), Real.norm_of_nonneg (by positivity)]
    have := ratioMf_le z hT (U ω) Ub
    linarith
  refine ⟨?_, mp_integral_pow_le (Filter.Eventually.of_forall hM0) k (by omega) hσ hMle⟩
  have hmem : MemLp Mf (k : ℝ≥0∞) μ := by
    rw [← ENNReal.ofReal_natCast]; exact hMle.trans_lt ENNReal.ofReal_lt_top
  refine (hmem.integrable_norm_pow').congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Real.norm_of_nonneg (hM0 ω), Mf]

end BlockBand.Transmission.LawForced
