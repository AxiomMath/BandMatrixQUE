module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Complex conditional-expectation tools for `generator`

* `integral_mul_condExp_C`, `integral_mul_sub_condExp_C`: complex pull-out,
  `∫ ξ E[f|m] = ∫ ξ f` and `∫ ξ (f - E[f|m]) = 0` for `m`-measurable `ξ`;
* `lintegral_sq_condExp_le`: `E|E[f|m]|² ≤ E|f|²`;
* `memLp_two_of_lintegral`, `lintegral_enorm_sq_eq`: `L²` bookkeeping;
* **`lintegral_sq_mart_le`**: for complex martingale differences `m_j = D_j - E[D_j|G_j]`,
  `E|Σ_{a≤j<n} m_j|² ≤ 4 Σ_{a≤j<n} E|D_j|²` (orthogonality of increments).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceGenerator

open MeasureTheory Finset
open scoped ENNReal ComplexConjugate

variable {Ω : Type*} {m m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Complex pull-out, integral form**: `∫ ξ E[f|m] = ∫ ξ f`. -/
theorem integral_mul_condExp_C (hm : m ≤ m0) [IsFiniteMeasure μ] {ξ f : Ω → ℂ}
    (hξ : AEStronglyMeasurable[m] ξ μ) (hξf : Integrable (fun ω => ξ ω * f ω) μ)
    (hf : Integrable f μ) :
    ∫ ω, ξ ω * μ[f | m] ω ∂μ = ∫ ω, ξ ω * f ω ∂μ := by
  have : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim hm
  have hξf' : Integrable (fun ω => ContinuousLinearMap.mul ℝ ℂ (ξ ω) (f ω)) μ := by simpa using hξf
  have h := condExp_bilin_of_aestronglyMeasurable_left (m := m) (μ := μ)
    (ContinuousLinearMap.mul ℝ ℂ) hξ hξf' hf
  simp only [ContinuousLinearMap.mul_apply'] at h
  rw [← integral_condExp hm (f := fun ω => ξ ω * f ω)]
  exact (integral_congr_ae h).symm

theorem integrable_mul_condExp_C {ξ f : Ω → ℂ} (hξ : AEStronglyMeasurable[m] ξ μ)
    (hξf : Integrable (fun ω => ξ ω * f ω) μ) (hf : Integrable f μ) :
    Integrable (fun ω => ξ ω * μ[f | m] ω) μ := by
  have hξf' : Integrable (fun ω => ContinuousLinearMap.mul ℝ ℂ (ξ ω) (f ω)) μ := by simpa using hξf
  have h := condExp_bilin_of_aestronglyMeasurable_left (m := m) (μ := μ)
    (ContinuousLinearMap.mul ℝ ℂ) hξ hξf' hf
  simp only [ContinuousLinearMap.mul_apply'] at h
  exact integrable_condExp.congr h

/-- `∫ ξ (f - E[f|m]) = 0` for `m`-measurable `ξ`. -/
theorem integral_mul_sub_condExp_C (hm : m ≤ m0) [IsFiniteMeasure μ] {ξ f : Ω → ℂ}
    (hξ : AEStronglyMeasurable[m] ξ μ) (hξf : Integrable (fun ω => ξ ω * f ω) μ)
    (hf : Integrable f μ) :
    ∫ ω, ξ ω * (f ω - μ[f | m] ω) ∂μ = 0 := by
  simp only [mul_sub]
  rw [integral_sub hξf (integrable_mul_condExp_C hξ hξf hf), integral_mul_condExp_C hm hξ hξf hf,
    sub_self]

theorem enorm_sq_eq_ofReal {E : Type*} [NormedAddCommGroup E] (x : E) :
    ‖x‖ₑ ^ 2 = ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [ENNReal.ofReal_pow (norm_nonneg x), ofReal_norm]

theorem memLp_two_of_lintegral {E : Type*} [NormedAddCommGroup E] {f : Ω → E}
    (hf : AEStronglyMeasurable f μ) (h : ∫⁻ ω, ‖f ω‖ₑ ^ 2 ∂μ ≠ ⊤) : MemLp f 2 μ := by
  rw [memLp_two_iff_integrable_sq_norm hf]
  refine ⟨(hf.norm.pow 2), ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun ω => ?_)) h.lt_top
  rw [enorm_pow, enorm_norm]

theorem lintegral_enorm_sq_eq {E : Type*} [NormedAddCommGroup E] {f : Ω → E} (hf : MemLp f 2 μ) :
    ∫⁻ ω, ‖f ω‖ₑ ^ 2 ∂μ = ENNReal.ofReal (∫ ω, ‖f ω‖ ^ 2 ∂μ) := by
  rw [ofReal_integral_eq_lintegral_ofReal ((memLp_two_iff_integrable_sq_norm
    hf.aestronglyMeasurable).mp hf) (Filter.Eventually.of_forall fun ω => by positivity)]
  exact lintegral_congr fun ω => enorm_sq_eq_ofReal _

theorem lintegral_enorm_sq_lt_top {E : Type*} [NormedAddCommGroup E] {f : Ω → E}
    (hf : MemLp f 2 μ) : ∫⁻ ω, ‖f ω‖ₑ ^ 2 ∂μ < ⊤ := by
  rw [lintegral_enorm_sq_eq hf]; exact ENNReal.ofReal_lt_top

theorem eLpNorm_two_eq {E : Type*} [NormedAddCommGroup E] {f : Ω → E}
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ = (∫⁻ ω, ‖f ω‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hf]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]

/-- `E|E[f|m]|² ≤ E|f|²`. -/
theorem lintegral_sq_condExp_le (hm : m ≤ m0) [IsFiniteMeasure μ] {f : Ω → ℂ}
    (hf : AEStronglyMeasurable f μ) :
    ∫⁻ ω, ‖μ[f | m] ω‖ₑ ^ 2 ∂μ ≤ ∫⁻ ω, ‖f ω‖ₑ ^ 2 ∂μ := by
  have h := eLpNorm_condExp_le_eLpNorm (m := m) (μ := μ) f (p := 2) one_le_two
  rw [eLpNorm_two_eq ((stronglyMeasurable_condExp.mono hm).aestronglyMeasurable),
    eLpNorm_two_eq hf] at h
  exact (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 1 / 2)).mp h

theorem integrable_mul_of_memLp {f g : Ω → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun ω => f ω * g ω) μ :=
  memLp_one_iff_integrable.mp (by simpa [mul_comm] using hg.fun_mul hf (p := 2) (q := 2) (r := 1))

/-- One orthogonal step: `E|S + (D - E[D|m])|² = E|S|² + E|D - E[D|m]|²` for `m`-measurable `S`. -/
theorem lintegral_sq_add_mart (hm : m ≤ m0) [IsFiniteMeasure μ] {S D : Ω → ℂ}
    (hSm : StronglyMeasurable[m] S) (hS : MemLp S 2 μ) (hD : MemLp D 2 μ) :
    ∫⁻ ω, ‖S ω + (D ω - μ[D | m] ω)‖ₑ ^ 2 ∂μ =
      ∫⁻ ω, ‖S ω‖ₑ ^ 2 ∂μ + ∫⁻ ω, ‖D ω - μ[D | m] ω‖ₑ ^ 2 ∂μ := by
  have hc : MemLp (μ[D | m]) 2 μ := hD.condExp one_le_two
  have hmd : MemLp (fun ω => D ω - μ[D | m] ω) 2 μ := hD.sub hc
  have hsum : MemLp (fun ω => S ω + (D ω - μ[D | m] ω)) 2 μ := hS.add hmd
  have hcS : MemLp (fun ω => conj (S ω)) 2 μ :=
    hS.congr_norm (Complex.continuous_conj.comp_aestronglyMeasurable hS.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => (Complex.norm_conj _).symm)
  have horth : ∫ ω, conj (S ω) * (D ω - μ[D | m] ω) ∂μ = 0 :=
    integral_mul_sub_condExp_C hm
      ((Complex.continuous_conj.comp_stronglyMeasurable hSm).aestronglyMeasurable)
      (integrable_mul_of_memLp hcS hD) (memLp_one_iff_integrable.mp (hD.mono_exponent one_le_two))
  have hcross : Integrable (fun ω => S ω * conj (D ω - μ[D | m] ω)) μ := by
    exact integrable_mul_of_memLp hS (hmd.congr_norm
      (Complex.continuous_conj.comp_aestronglyMeasurable hmd.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => (Complex.norm_conj _).symm))
  have hre : ∫ ω, (S ω * conj (D ω - μ[D | m] ω)).re ∂μ = 0 := by
    have e1 : ∫ ω, (S ω * conj (D ω - μ[D | m] ω)).re ∂μ =
        (∫ ω, S ω * conj (D ω - μ[D | m] ω) ∂μ).re := integral_re hcross
    have e2 : ∫ ω, S ω * conj (D ω - μ[D | m] ω) ∂μ =
        conj (∫ ω, conj (S ω) * (D ω - μ[D | m] ω) ∂μ) := by
      rw [← integral_conj]; congr 1; funext ω; simp [mul_comm]
    rw [e1, e2, horth]; simp
  have hS2 := (memLp_two_iff_integrable_sq_norm hS.aestronglyMeasurable).mp hS
  have hm2 := (memLp_two_iff_integrable_sq_norm hmd.aestronglyMeasurable).mp hmd
  have hpt : ∀ ω, ‖S ω + (D ω - μ[D | m] ω)‖ ^ 2 = ‖S ω‖ ^ 2 + ‖D ω - μ[D | m] ω‖ ^ 2 +
      2 * (S ω * conj (D ω - μ[D | m] ω)).re := by
    intro ω
    simp only [← Complex.normSq_eq_norm_sq]
    exact Complex.normSq_add _ _
  rw [lintegral_enorm_sq_eq hsum, lintegral_enorm_sq_eq hS, lintegral_enorm_sq_eq hmd,
    ← ENNReal.ofReal_add (integral_nonneg fun _ => by positivity)
      (integral_nonneg fun _ => by positivity)]
  congr 1
  simp_rw [hpt]
  have hre' : Integrable (fun ω => (S ω * conj (D ω - μ[D | m] ω)).re) μ := hcross.re
  have h1 := integral_add (μ := μ) (hS2.add hm2) (hre'.const_mul 2)
  have h2 := integral_add (μ := μ) hS2 hm2
  simp only [Pi.add_apply] at h1 h2
  rw [h1, h2, integral_const_mul, hre, mul_zero, add_zero]

/-- `E|D - E[D|m]|² ≤ 4 E|D|²`. -/
theorem lintegral_sq_sub_condExp_le (hm : m ≤ m0) [IsFiniteMeasure μ] {D : Ω → ℂ}
    (hD : AEStronglyMeasurable D μ) :
    ∫⁻ ω, ‖D ω - μ[D | m] ω‖ₑ ^ 2 ∂μ ≤ 4 * ∫⁻ ω, ‖D ω‖ₑ ^ 2 ∂μ := by
  have hpt : ∀ ω, ‖D ω - μ[D | m] ω‖ₑ ^ 2 ≤ 2 * ‖D ω‖ₑ ^ 2 + 2 * ‖μ[D | m] ω‖ₑ ^ 2 := by
    intro ω
    rw [enorm_sq_eq_ofReal, enorm_sq_eq_ofReal, enorm_sq_eq_ofReal, ← ENNReal.ofReal_ofNat 2,
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := norm_sub_le (D ω) (μ[D | m] ω)
    nlinarith [norm_nonneg (D ω), norm_nonneg (μ[D | m] ω),
      norm_nonneg (D ω - μ[D | m] ω), sq_nonneg (‖D ω‖ - ‖μ[D | m] ω‖)]
  calc ∫⁻ ω, ‖D ω - μ[D | m] ω‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ ω, (2 * ‖D ω‖ₑ ^ 2 + 2 * ‖μ[D | m] ω‖ₑ ^ 2) ∂μ := lintegral_mono hpt
    _ = ∫⁻ ω, 2 * ‖D ω‖ₑ ^ 2 ∂μ + ∫⁻ ω, 2 * ‖μ[D | m] ω‖ₑ ^ 2 ∂μ :=
        lintegral_add_left' ((hD.enorm.pow_const 2).const_mul 2) _
    _ = 2 * ∫⁻ ω, ‖D ω‖ₑ ^ 2 ∂μ + 2 * ∫⁻ ω, ‖μ[D | m] ω‖ₑ ^ 2 ∂μ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofNat_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]
    _ ≤ 2 * ∫⁻ ω, ‖D ω‖ₑ ^ 2 ∂μ + 2 * ∫⁻ ω, ‖D ω‖ₑ ^ 2 ∂μ := by
        gcongr 2 * ∫⁻ ω, ‖D ω‖ₑ ^ 2 ∂μ + 2 * ?_; exact lintegral_sq_condExp_le hm hD
    _ = 4 * ∫⁻ ω, ‖D ω‖ₑ ^ 2 ∂μ := by rw [← add_mul]; norm_num

/-- **Orthogonality of martingale increments**:
`E|Σ_{a≤j<n} (D_j - E[D_j|G_j])|² ≤ 4 Σ_{a≤j<n} E|D_j|²`. -/
theorem lintegral_sq_mart_le [IsFiniteMeasure μ] (G : ℕ → MeasurableSpace Ω) (hG : Monotone G)
    (hle : ∀ j, G j ≤ m0) (D : ℕ → Ω → ℂ) (hDm : ∀ j, StronglyMeasurable[G (j + 1)] (D j))
    (hD : ∀ j, MemLp (D j) 2 μ) (a n : ℕ) :
    ∫⁻ ω, ‖∑ j ∈ Ico a n, (D j ω - μ[D j | G j] ω)‖ₑ ^ 2 ∂μ ≤
      4 * ∑ j ∈ Ico a n, ∫⁻ ω, ‖D j ω‖ₑ ^ 2 ∂μ := by
  have hmm : ∀ j, StronglyMeasurable[G (j + 1)] fun ω => D j ω - μ[D j | G j] ω := fun j =>
    (hDm j).sub (stronglyMeasurable_condExp.mono (hG (Nat.le_succ j)))
  have hSm : ∀ n, StronglyMeasurable[G n] fun ω => ∑ j ∈ Ico a n, (D j ω - μ[D j | G j] ω) := by
    intro n
    exact Finset.stronglyMeasurable_fun_sum _ fun j hj => (hmm j).mono (hG (Finset.mem_Ico.mp hj).2)
  have hSL : ∀ n, MemLp (fun ω => ∑ j ∈ Ico a n, (D j ω - μ[D j | G j] ω)) 2 μ := fun n =>
    memLp_finsetSum _ fun j _ => (hD j).sub ((hD j).condExp one_le_two)
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases han : a ≤ n
    · have e : ∀ ω, ∑ j ∈ Ico a (n + 1), (D j ω - μ[D j | G j] ω) =
          ∑ j ∈ Ico a n, (D j ω - μ[D j | G j] ω) + (D n ω - μ[D n | G n] ω) := fun ω =>
        Finset.sum_Ico_succ_top han _
      simp_rw [e]
      rw [Finset.sum_Ico_succ_top han (fun k => ∫⁻ ω, ‖D k ω‖ₑ ^ 2 ∂μ),
        lintegral_sq_add_mart (hle n) (hSm n) (hSL n) (hD n), mul_add]
      exact add_le_add ih (lintegral_sq_sub_condExp_le (hle n) (hD n).aestronglyMeasurable)
    · have : Ico a (n + 1) = ∅ := Finset.Ico_eq_empty (by omega)
      simp [this]

end BlockBand.SourceProcess.FullSourceGenerator
