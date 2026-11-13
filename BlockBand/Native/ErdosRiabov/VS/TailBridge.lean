module

public import BlockBand.Native.ErdosRiabov.VS.Tail
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

set_option autoImplicit false

/-!
# Drift linearity and integration by parts for martingale parts

Setting: `linComb c φ (t, y) = ∑_α c_α(t) φ_α(t, y)` with `C²` coefficients and
`C²` test functions; the Itô drift `itoDrift` at zero drift and covariance `A`.

* **`itoDrift_linComb`**: `itoDrift (∑ c_α φ_α) y t 0 A = ∑_α (c_α'(t) φ_α(t, y) + c_α(t)
  itoDrift φ_α y t 0 A)` (the time derivative of the coefficients appears; the spatial parts
  are linear: `partialSpace2_linComb`, by slicing).
* `integral_mul_primitive`: `∫_0^t c b = c(t) ∫_0^t b - ∫_0^t c'(s) (∫_0^s b) ds` for `C¹`
  `c` and integrable `b` (Mathlib's integration by parts for absolutely continuous functions).
* **`smCompensated_linComb_path`** (pathwise, every sample with continuous path and integrable
  drifts): the martingale part of `linComb c φ (t, Y_t)` is
  `∑_α (c_α(t) M^α_t - ∫_0^t c_α'(s) M^α_s ds)`, `M^α` the martingale part of `φ_α(t, Y_t)`.
* **`smCompensated_linComb_vs`**: the same a.s. along `Y_t - Y_0 = vsNoise p t`.
-/

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.VS
open MeasureTheory Set Filter Topology Matrix Function
open BlockBand.Internal.Contracts.Transmission
open BlockBand.SourceProcess
open BlockBand.SourceProcess.FiniteDriverIntegration
open BlockBand.SourceProcess.Stochastic
open BlockBand.Native.ErdosRiabov.Stochastic
open scoped NNReal

/-!
### Linearity of the derivatives
-/

section Deriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*} [Fintype ι]

/-- Second derivative of a constant-coefficient combination. -/
theorem fderiv_fderiv_sum_mul {g : ι → E → ℝ} (hg : ∀ α, ContDiff ℝ 2 (g α)) (a : ι → ℝ)
    (y u w : E) :
    fderiv ℝ (fderiv ℝ (fun y => ∑ α, a α * g α y)) y u w =
      ∑ α, a α * fderiv ℝ (fderiv ℝ (g α)) y u w := by
  have h1 : fderiv ℝ (fun y => ∑ α, a α * g α y) = fun y => ∑ α, a α • fderiv ℝ (g α) y :=
    funext fun y => (HasFDerivAt.fun_sum (u := Finset.univ) fun α _ =>
      (((hg α).differentiable (by norm_num) y).hasFDerivAt.const_mul (a α))).fderiv
  have hd : ∀ α, Differentiable ℝ (fderiv ℝ (g α)) := fun α =>
    ((hg α).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h2 : fderiv ℝ (fun y => ∑ α, a α • fderiv ℝ (g α) y) y =
      ∑ α, a α • fderiv ℝ (fderiv ℝ (g α)) y :=
    (HasFDerivAt.fun_sum (u := Finset.univ) fun α _ =>
      ((hd α y).hasFDerivAt.const_smul (a α))).fderiv
  rw [h1, h2]
  simp

end Deriv

section LinComb

variable {d : ℕ} {ι : Type*} [Fintype ι]

theorem partialTime_linComb {c : ι → ℝ → ℝ} {φ : ι → ℝ × (Fin d → ℝ) → ℝ}
    {q : ℝ × (Fin d → ℝ)} (hc : ∀ α, DifferentiableAt ℝ (c α) q.1)
    (hφ : ∀ α, DifferentiableAt ℝ (φ α) q) :
    partialTime (linComb c φ) q =
      ∑ α, (deriv (c α) q.1 * φ α q + c α q.1 * partialTime (φ α) q) := by
  rw [partialTime, (hasFDerivAt_linComb hc hφ).fderiv]
  simp only [FunLike.coe_sum, Finset.sum_apply, _root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', smul_eq_mul, partialTime]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [fderiv_apply_one_eq_deriv]
  ring

theorem partialSpace2_linComb {c : ι → ℝ → ℝ} {φ : ι → ℝ × (Fin d → ℝ) → ℝ}
    (hc : ∀ α, ContDiff ℝ 2 (c α)) (hφ : ∀ α, ContDiff ℝ 2 (φ α)) (t : ℝ) (y : Fin d → ℝ)
    (i j : Fin d) :
    partialSpace2 (linComb c φ) (t, y) i j = ∑ α, c α t * partialSpace2 (φ α) (t, y) i j := by
  rw [partialSpace2_eq_slice (contDiff_linComb hc hφ).contDiffAt]
  have hs : (fun y' => linComb c φ (t, y')) = fun y' => ∑ α, c α t * φ α (t, y') := rfl
  rw [hs, fderiv_fderiv_sum_mul (g := fun α y' => φ α (t, y'))
    (fun α => (hφ α).comp (contDiff_const.prodMk contDiff_id))]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [partialSpace2_eq_slice (hφ α).contDiffAt]

/-- **Drift of a time-dependent linear combination.** -/
theorem itoDrift_linComb {c : ι → ℝ → ℝ} {φ : ι → ℝ × (Fin d → ℝ) → ℝ}
    (hc : ∀ α, ContDiff ℝ 2 (c α)) (hφ : ∀ α, ContDiff ℝ 2 (φ α)) (y : Fin d → ℝ) (t : ℝ≥0)
    (A : Matrix (Fin d) (Fin d) ℝ) :
    itoDrift (linComb c φ) y t 0 A =
      ∑ α, (deriv (c α) t * φ α ((t : ℝ), y) + c α t * itoDrift (φ α) y t 0 A) := by
  have hcd : ∀ α, DifferentiableAt ℝ (c α) ((t : ℝ), y).1 := fun α =>
    (hc α).differentiable (by norm_num) _
  have hφd : ∀ α, DifferentiableAt ℝ (φ α) ((t : ℝ), y) := fun α =>
    (hφ α).differentiable (by norm_num) _
  simp only [itoDrift, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
  rw [partialTime_linComb hcd hφd]
  simp only [partialSpace2_linComb hc hφ]
  have hs : ∑ i, ∑ j, A i j * ∑ α, c α t * partialSpace2 (φ α) ((t : ℝ), y) i j =
      ∑ α, c α t * ∑ i, ∑ j, A i j * partialSpace2 (φ α) ((t : ℝ), y) i j := by
    simp only [Finset.mul_sum]
    calc ∑ i, ∑ j, ∑ α, A i j * (c α t * partialSpace2 (φ α) ((t : ℝ), y) i j)
        = ∑ i, ∑ α, ∑ j, A i j * (c α t * partialSpace2 (φ α) ((t : ℝ), y) i j) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ α, ∑ i, ∑ j, A i j * (c α t * partialSpace2 (φ α) ((t : ℝ), y) i j) :=
          Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun i _ =>
          Finset.sum_congr rfl fun j _ => by ring
  rw [hs, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  ring

end LinComb

/-!
### Integration by parts against a primitive
-/

/-- `∫_0^t c b = c(t) ∫_0^t b - ∫_0^t c'(s) (∫_0^s b) ds` (`c` `C¹`, `b` integrable). -/
theorem integral_mul_primitive {c b : ℝ → ℝ} (hc : ContDiff ℝ 1 c) {t : ℝ}
    (hb : IntervalIntegrable b volume 0 t) :
    ∫ s in (0 : ℝ)..t, c s * b s =
      c t * (∫ s in (0 : ℝ)..t, b s) -
        ∫ s in (0 : ℝ)..t, deriv c s * ∫ r in (0 : ℝ)..s, b r := by
  have hI := hb.absolutelyContinuousOnInterval_intervalIntegral (c := 0) left_mem_uIcc
  have hcA : AbsolutelyContinuousOnInterval c 0 t := hc.contDiffOn.absolutelyContinuousOnInterval
  have h := hcA.integral_mul_deriv_eq_deriv_mul hI
  have hderiv : ∀ᵐ s, s ∈ Set.uIoc (0 : ℝ) t →
      c s * deriv (fun x => ∫ r in (0 : ℝ)..x, b r) s = c s * b s := by
    filter_upwards [hb.ae_hasDerivAt_integral] with s hs hsI
    rw [(hs (uIoc_subset_uIcc hsI) 0 left_mem_uIcc).deriv]
  rw [intervalIntegral.integral_congr_ae hderiv] at h
  simp only [intervalIntegral.integral_same, mul_zero, sub_zero] at h
  exact h

/-- **Pathwise core identity.** For continuous `f`, integrable `b` and `C¹` `c`, with
`M(s) = f(s) - f(0) - ∫_0^s b`:
`c(t) f(t) - c(0) f(0) - ∫_0^t (c' f + c b) = c(t) M(t) - ∫_0^t c'(s) M(s) ds`. -/
theorem ibp_martingalePart {c f b : ℝ → ℝ} (hc : ContDiff ℝ 1 c) (hf : Continuous f) {t : ℝ}
    (ht : 0 ≤ t) (hb : IntervalIntegrable b volume 0 t) :
    c t * f t - c 0 * f 0 - ∫ s in (0 : ℝ)..t, (deriv c s * f s + c s * b s) =
      c t * (f t - f 0 - ∫ s in (0 : ℝ)..t, b s) -
        ∫ s in (0 : ℝ)..t, deriv c s * (f s - f 0 - ∫ r in (0 : ℝ)..s, b r) := by
  have hc' : Continuous (deriv c) := hc.continuous_deriv le_rfl
  have hcc : Continuous c := hc.continuous
  have hbI : IntegrableOn b (uIcc 0 t) volume := by
    rw [uIcc_of_le ht, integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).1 hb
  have hPc : ContinuousOn (fun s => ∫ r in (0 : ℝ)..s, b r) (uIcc 0 t) :=
    intervalIntegral.continuousOn_primitive_interval hbI
  have i1 : IntervalIntegrable (fun s => deriv c s * f s) volume 0 t :=
    (hc'.mul hf).intervalIntegrable 0 t
  have i2 : IntervalIntegrable (fun s => c s * b s) volume 0 t :=
    hb.continuousOn_mul hcc.continuousOn
  have i3 : IntervalIntegrable (fun s => deriv c s * f 0) volume 0 t :=
    (hc'.mul continuous_const).intervalIntegrable 0 t
  have i4 : IntervalIntegrable (fun s => deriv c s * ∫ r in (0 : ℝ)..s, b r) volume 0 t :=
    (hc'.continuousOn.mul hPc).intervalIntegrable
  have hsplit : ∫ s in (0 : ℝ)..t, deriv c s * (f s - f 0 - ∫ r in (0 : ℝ)..s, b r) =
      (∫ s in (0 : ℝ)..t, deriv c s * f s) - (∫ s in (0 : ℝ)..t, deriv c s * f 0) -
        ∫ s in (0 : ℝ)..t, deriv c s * ∫ r in (0 : ℝ)..s, b r := by
    rw [← intervalIntegral.integral_sub i1 i3, ← intervalIntegral.integral_sub (i1.sub i3) i4]
    refine intervalIntegral.integral_congr fun s _ => ?_
    ring
  have hfund : ∫ s in (0 : ℝ)..t, deriv c s * f 0 = (c t - c 0) * f 0 := by
    rw [intervalIntegral.integral_mul_const,
      intervalIntegral.integral_deriv_eq_sub (fun x _ => hc.differentiable (by norm_num) x)
        (hc'.intervalIntegrable 0 t)]
  rw [intervalIntegral.integral_add i1 i2, integral_mul_primitive hc hb, hsplit, hfund]
  ring

/-!
### The pathwise identity for martingale parts
-/

section Path

variable {Ω : Type*} {d : ℕ} {ι : Type*} [Fintype ι]

/-- The real process `φ(t, Y_t)` in one coordinate. -/
abbrev testProc (φ : ℝ × (Fin d → ℝ) → ℝ) (Y : ℝ≥0 → Ω → Fin d → ℝ) :
    ℝ≥0 → Ω → Fin 1 → ℝ :=
  fun t ω _ => φ ((t : ℝ), Y t ω)

/-- The Itô drift `itoDrift φ (Y_t) t 0 A` in one coordinate. -/
abbrev testDrift (φ : ℝ × (Fin d → ℝ) → ℝ) (Y : ℝ≥0 → Ω → Fin d → ℝ)
    (A : Matrix (Fin d) (Fin d) ℝ) : ℝ≥0 → Ω → Fin 1 → ℝ :=
  fun t ω _ => itoDrift φ (Y t ω) t 0 A

theorem integral_Ioc_toNNReal_eq {g : ℝ → ℝ} {s : ℝ} (hs : 0 ≤ s) :
    ∫ r in Ioc (0 : ℝ) (s.toNNReal : ℝ), g r = ∫ r in (0 : ℝ)..s, g r := by
  rw [Real.coe_toNNReal _ hs, intervalIntegral.integral_of_le hs]

/-- **Pathwise integration by parts for martingale parts.** On a sample
with continuous path `t ↦ Y_t ω` and drifts `itoDrift φ_α` integrable on `(0, t]`, the
martingale part of `linComb c φ (t, Y_t)` is `∑_α (c_α(t) M^α_t - ∫_0^t c_α'(s) M^α_s ds)`. -/
theorem smCompensated_linComb_path (Y : ℝ≥0 → Ω → Fin d → ℝ) (A : Matrix (Fin d) (Fin d) ℝ)
    {ω : Ω} (hY : Continuous fun t => Y t ω) {c : ι → ℝ → ℝ} {φ : ι → ℝ × (Fin d → ℝ) → ℝ}
    (hc : ∀ α, ContDiff ℝ 2 (c α)) (hφ : ∀ α, ContDiff ℝ 2 (φ α)) (t : ℝ≥0)
    (hβ : ∀ α, IntegrableOn (fun s : ℝ => itoDrift (φ α) (Y s.toNNReal ω) s.toNNReal 0 A)
      (Ioc 0 t)) :
    smCompensated (testProc (linComb c φ) Y) (testDrift (linComb c φ) Y A) 0 t ω =
      ∑ α, (c α t * smCompensated (testProc (φ α) Y) (testDrift (φ α) Y A) 0 t ω -
        ∫ s in (0 : ℝ)..t, deriv (c α) s *
          smCompensated (testProc (φ α) Y) (testDrift (φ α) Y A) 0 s.toNNReal ω) := by
  set f : ι → ℝ → ℝ := fun α s => φ α ((s.toNNReal : ℝ), Y s.toNNReal ω) with hf
  set b : ι → ℝ → ℝ := fun α s => itoDrift (φ α) (Y s.toNNReal ω) s.toNNReal 0 A with hb
  have ht0 : (0 : ℝ) ≤ t := t.2
  have hfc : ∀ α, Continuous (f α) := fun α =>
    (hφ α).continuous.comp ((NNReal.continuous_coe.comp continuous_real_toNNReal).prodMk
      (hY.comp continuous_real_toNNReal))
  have hbi : ∀ α, IntervalIntegrable (b α) volume 0 t := fun α =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht0).2 (hβ α)
  have hc1 : ∀ α, ContDiff ℝ 1 (c α) := fun α => (hc α).of_le (by norm_num)
  -- the drift of the combination, rewritten
  have hdrift : ∀ s ∈ Ioc (0 : ℝ) t, itoDrift (linComb c φ) (Y s.toNNReal ω) s.toNNReal 0 A =
      ∑ α, (deriv (c α) s * f α s + c α s * b α s) := fun s hs => by
    rw [itoDrift_linComb hc hφ]
    simp only [hf, hb, Real.coe_toNNReal _ hs.1.le]
  have hint : ∀ α, IntervalIntegrable (fun s => deriv (c α) s * f α s + c α s * b α s)
      volume 0 t := fun α =>
    (((hc α).continuous_deriv (by norm_num)).mul (hfc α)).intervalIntegrable 0 t |>.add
      ((hbi α).continuousOn_mul (hc α).continuous.continuousOn)
  have hlhs : smCompensated (testProc (linComb c φ) Y) (testDrift (linComb c φ) Y A) 0 t ω =
      ∑ α, (c α t * f α t - c α 0 * f α 0 -
        ∫ s in (0 : ℝ)..t, (deriv (c α) s * f α s + c α s * b α s)) := by
    simp only [smCompensated, testProc, testDrift]
    rw [setIntegral_congr_fun measurableSet_Ioc hdrift, ← intervalIntegral.integral_of_le ht0,
      intervalIntegral.integral_finsetSum fun α _ => hint α]
    simp only [linComb, hf, Real.toNNReal_coe, NNReal.coe_zero, Real.toNNReal_zero]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  rw [hlhs]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [ibp_martingalePart (hc1 α) (hfc α) ht0 (hbi α)]
  have hM : ∀ s : ℝ, 0 ≤ s →
      smCompensated (testProc (φ α) Y) (testDrift (φ α) Y A) 0 s.toNNReal ω =
        f α s - f α 0 - ∫ r in (0 : ℝ)..s, b α r := fun s hs => by
    simp only [smCompensated, testProc, testDrift, hf, Real.toNNReal_zero, NNReal.coe_zero]
    rw [integral_Ioc_toNNReal_eq hs]
  have hMt := hM t ht0
  rw [Real.toNNReal_coe] at hMt
  rw [hMt]
  congr 1
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le ht0] at hs
  rw [hM s hs.1]

end Path

/-!
### Along the VS coordinates
-/

variable {p : BlockBand.Parameters} {ι : Type*} [Fintype ι]

/-- **Integration by parts for martingale parts along `Y_t - Y_0`**: a.s., for every `t`, the
martingale part of
`linComb c φ (t, Y_t - Y_0)` is `∑_α (c_α(t) M^α_t - ∫_0^t c_α'(s) M^α_s ds)`. -/
theorem smCompensated_linComb_vs (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ]
    {c : ι → ℝ → ℝ} {φ : ι → ℝ × (Fin (ringDim p) → ℝ) → ℝ} (hc : ∀ α, ContDiff ℝ 2 (c α))
    (hφm : ∀ α, Measurable (φ α)) (hφ : ∀ α, ContDiff ℝ 2 (φ α)) :
    ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ t : ℝ≥0,
      smCompensated (testProc (linComb c φ) (vsNoise p))
          (testDrift (linComb c φ) (vsNoise p) (diagonal (ringVariance p))) 0 t x =
        ∑ α, (c α t * smCompensated (testProc (φ α) (vsNoise p))
            (testDrift (φ α) (vsNoise p) (diagonal (ringVariance p))) 0 t x -
          ∫ s in (0 : ℝ)..t, deriv (c α) s * smCompensated (testProc (φ α) (vsNoise p))
            (testDrift (φ α) (vsNoise p) (diagonal (ringVariance p))) 0 s.toNNReal x) := by
  have H : ∀ α, IsContinuousSemimartingale (d := 1) (driverLaw (κ := Fin (ringDim p)) μ)
      (driverAugmented (κ := Fin (ringDim p)) μ) (testProc (φ α) (vsNoise p))
      (testDrift (φ α) (vsNoise p) (diagonal (ringVariance p)))
      (fun t x => Matrix.of fun (_ _ : Fin 1) =>
        itoBracket (φ α) (vsNoise p t x) t (diagonal (ringVariance p))) := fun α =>
    vsNoise_itoFormula μ isOpen_univ (ae_of_all _ fun _ _ => Set.mem_univ _) (hφm α)
      (hφ α).contDiffOn
  have hall : ∀ᵐ x ∂driverLaw (κ := Fin (ringDim p)) μ, ∀ α, ∀ t : ℝ≥0,
      IntegrableOn (fun s : ℝ => itoDrift (φ α) (vsNoise p s.toNNReal x) s.toNNReal 0
        (diagonal (ringVariance p))) (Ioc 0 t) := by
    rw [ae_all_iff]
    intro α
    filter_upwards [(H α).integrable] with x hx t
    exact (hx t).1 0
  filter_upwards [hall] with x hx t
  exact smCompensated_linComb_path (vsNoise p) _ (continuous_vsNoise p x) hc hφ t
    fun α => hx α t

end BlockBand.Native.ErdosRiabov.VS
