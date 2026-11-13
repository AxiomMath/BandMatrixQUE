module

public import BlockBand.SourceProcess.Stochastic.SDE.DiscreteDoob
public import BlockBand.Transmission.Generator.ModFour
public import BlockBand.SourceProcess.PhysApprox.B3MomK

/-!
# Doob and a crude Burkholder bound for complex `L⁴` martingale sums

Generic setting: a finite measure `μ`, a filtration `ℱ : Filtration ℕ m0`, steps `Z i` that are
`ℱ (i + 1)`-measurable and in `L⁴` for `i ∈ S`. The centred sum
`martSum ℱ μ S Z n = Σ_{i < n, i ∈ S} (Z i − E[Z i | ℱ i])` is a martingale
(`martingale_martSum`), and

* **`mart_integral_pow_four_le`** (real martingales, `X 0 = 0`, `X n ∈ L⁴`):
  `E X_n⁴ ≤ 16(n + 1) Σ_{i<n} E(X_{i+1} − X_i)⁴`. The recursion of
  `Generator.integral_modSum_pow_four_le` (`add_pow_four_step` with `c = j + 1`; orthogonality
  kills `4X_j³D_j`), without its boundedness hypothesis;
* `mart_lintegral_pow_four_le`: the complex version, constant `64`, through the real and
  imaginary parts;
* `mart_lintegral_runMax_le`: Doob's `L⁴` maximal inequality
  (`Stochastic.SDE.DoobLp.martingale_eLpNorm_runMax_norm_le`, `(4/3)⁴ ≤ 4`);
* **`lintegral_runMax_martSum_le`**: `E max_{k ≤ N}|martSum k|⁴ ≤ 4096 (N + 1) Σ_{i<N, i∈S} E|Z i|⁴`
  (`E|Z − E[Z|ℱ]|⁴ ≤ 16 E|Z|⁴`, conditional Jensen in `L⁴`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Filter Finset
open scoped NNReal ENNReal

section MartGeneric

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-!
## Real fourth powers
-/

theorem mart_integrable_pow_four {f : Ω → ℝ} (hf : MemLp f 4 μ) :
    Integrable (fun ω => f ω ^ 4) μ := by
  have h : MemLp f ((4 : ℕ) : ℝ≥0∞) μ := by exact_mod_cast hf
  refine (h.integrable_norm_pow (by norm_num)).congr (ae_of_all _ fun ω => ?_)
  simp only [Real.norm_eq_abs]
  exact Even.pow_abs (by decide) _

theorem mart_lintegral_pow_four_eq {f : Ω → ℝ} (hf : MemLp f 4 μ) :
    ∫⁻ ω, ‖f ω‖ₑ ^ 4 ∂μ = ENNReal.ofReal (∫ ω, f ω ^ 4 ∂μ) := by
  rw [ofReal_integral_eq_lintegral_ofReal (mart_integrable_pow_four hf)
    (Eventually.of_forall fun ω => Even.pow_nonneg (by decide) (f ω))]
  refine lintegral_congr fun ω => ?_
  rw [← enorm_pow, Real.enorm_of_nonneg (Even.pow_nonneg (by decide) _)]

theorem mart_abs_pow_three_mul_le (x y : ℝ) : |x ^ 3 * y| ≤ x ^ 4 + y ^ 4 := by
  rw [abs_mul, abs_pow, ← Even.pow_abs (by decide : Even 4) x,
    ← Even.pow_abs (by decide : Even 4) y]
  have ha := abs_nonneg x
  have hc := abs_nonneg y
  rcases le_total |x| |y| with h | h
  · have : |x| ^ 3 * |y| ≤ |y| ^ 3 * |y| :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha h 3) hc
    nlinarith [pow_nonneg ha 4]
  · have : |x| ^ 3 * |y| ≤ |x| ^ 3 * |x| := mul_le_mul_of_nonneg_left h (pow_nonneg ha 3)
    nlinarith [pow_nonneg hc 4]

theorem mart_integrable_pow_three_mul {f g : Ω → ℝ} (hf : MemLp f 4 μ) (hg : MemLp g 4 μ) :
    Integrable (fun ω => f ω ^ 3 * g ω) μ :=
  ((mart_integrable_pow_four hf).add (mart_integrable_pow_four hg)).mono'
    ((hf.aestronglyMeasurable.pow 3).mul hg.aestronglyMeasurable) (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]
      exact mart_abs_pow_three_mul_le _ _)

/-!
## The fourth moment of a real `L⁴` martingale
-/

/-- **Crude Burkholder for real `L⁴` martingales**: `E X_n⁴ ≤ 16(n + 1) Σ_{i<n} E D_i⁴`,
`D_i = X_{i+1} − X_i`, `X_0 = 0`. -/
theorem mart_integral_pow_four_le [IsFiniteMeasure μ] (ℱ : Filtration ℕ m0) {X : ℕ → Ω → ℝ}
    (hX : Martingale X ℱ μ) (h0 : X 0 = 0) (hL : ∀ n, MemLp (X n) 4 μ) (n : ℕ) :
    ∫ ω, X n ω ^ 4 ∂μ ≤
      16 * ((n : ℝ) + 1) * ∑ i ∈ range n, ∫ ω, (X (i + 1) ω - X i ω) ^ 4 ∂μ := by
  induction n with
  | zero => simp [h0]
  | succ j ih =>
    have hDL : MemLp (X (j + 1) - X j) 4 μ := (hL (j + 1)).sub (hL j)
    have hDi : Integrable (X (j + 1) - X j) μ := hDL.integrable (by norm_num)
    have hcD : μ[X (j + 1) - X j | ℱ j] =ᵐ[μ] 0 := by
      have h1 := condExp_sub (hX.integrable (j + 1)) (hX.integrable j) (ℱ j)
      have h2 := hX.condExp_ae_eq (Nat.le_succ j)
      have h3 := condExp_of_stronglyMeasurable (ℱ.le j) (hX.stronglyAdapted j) (hX.integrable j)
      filter_upwards [h1, h2] with ω e1 e2
      rw [e1, Pi.sub_apply, e2, h3, sub_self, Pi.zero_apply]
    have hNm : Integrable ((fun ω => X j ω ^ 3) * (X (j + 1) - X j)) μ :=
      mart_integrable_pow_three_mul (hL j) hDL
    have hO : ∫ ω, X j ω ^ 3 * (X (j + 1) ω - X j ω) ∂μ = 0 := by
      calc ∫ ω, X j ω ^ 3 * (X (j + 1) ω - X j ω) ∂μ
          = ∫ ω, (μ[(fun ω => X j ω ^ 3) * (X (j + 1) - X j) | ℱ j]) ω ∂μ :=
            (integral_condExp (ℱ.le j)).symm
        _ = ∫ ω, ((fun ω => X j ω ^ 3) * μ[X (j + 1) - X j | ℱ j]) ω ∂μ :=
            integral_congr_ae (condExp_mul_of_stronglyMeasurable_left
              ((hX.stronglyAdapted j).pow 3) hNm hDi)
        _ = ∫ _, (0 : ℝ) ∂μ := by
            refine integral_congr_ae ?_
            filter_upwards [hcD] with ω h
            rw [Pi.mul_apply, h, Pi.zero_apply, mul_zero]
        _ = 0 := integral_zero _ _
    have hc : (0 : ℝ) < j + 1 := by positivity
    have iN := mart_integrable_pow_four (hL j)
    have im : Integrable (fun ω => (X (j + 1) ω - X j ω) ^ 4) μ := mart_integrable_pow_four hDL
    have iS := mart_integrable_pow_four (hL (j + 1))
    have k1 : Integrable (fun ω => (1 + 1 / ((j : ℝ) + 1)) * X j ω ^ 4) μ := iN.const_mul _
    have k2 : Integrable (fun ω => 4 * (X j ω ^ 3 * (X (j + 1) ω - X j ω))) μ :=
      hNm.const_mul 4
    have k3 : Integrable (fun ω => (16 * ((j : ℝ) + 1) + 3) * (X (j + 1) ω - X j ω) ^ 4) μ :=
      im.const_mul _
    have k12 : Integrable (fun ω => (1 + 1 / ((j : ℝ) + 1)) * X j ω ^ 4 +
        4 * (X j ω ^ 3 * (X (j + 1) ω - X j ω))) μ := k1.add k2
    have hI : ∫ ω, X (j + 1) ω ^ 4 ∂μ ≤
        ∫ ω, ((1 + 1 / ((j : ℝ) + 1)) * X j ω ^ 4 +
          4 * (X j ω ^ 3 * (X (j + 1) ω - X j ω)) +
          (16 * ((j : ℝ) + 1) + 3) * (X (j + 1) ω - X j ω) ^ 4) ∂μ := by
      refine integral_mono iS (k12.add k3) fun ω => ?_
      have h := BlockBand.Transmission.Generator.add_pow_four_step (X j ω)
        (X (j + 1) ω - X j ω) hc
      have e : X (j + 1) ω = X j ω + (X (j + 1) ω - X j ω) := by ring
      have e2 : (1 + 1 / ((j : ℝ) + 1)) * X j ω ^ 4 = X j ω ^ 4 + X j ω ^ 4 / ((j : ℝ) + 1) := by
        ring
      show X (j + 1) ω ^ 4 ≤ (1 + 1 / ((j : ℝ) + 1)) * X j ω ^ 4 +
          4 * (X j ω ^ 3 * (X (j + 1) ω - X j ω)) +
          (16 * ((j : ℝ) + 1) + 3) * (X (j + 1) ω - X j ω) ^ 4
      rw [e2]
      calc X (j + 1) ω ^ 4 = (X j ω + (X (j + 1) ω - X j ω)) ^ 4 := by rw [← e]
        _ ≤ _ := h
        _ = _ := by ring
    rw [integral_add k12 k3, integral_add k1 k2, integral_const_mul, integral_const_mul,
      integral_const_mul, hO, mul_zero, add_zero] at hI
    rw [sum_range_succ]
    set x := ∫ ω, X j ω ^ 4 ∂μ
    set A := ∑ i ∈ range j, ∫ ω, (X (i + 1) ω - X i ω) ^ 4 ∂μ
    set a := ∫ ω, (X (j + 1) ω - X j ω) ^ 4 ∂μ
    have ha : 0 ≤ a := integral_nonneg fun ω => Even.pow_nonneg (by decide) _
    have hxc : x / ((j : ℝ) + 1) ≤ 16 * A := by
      rw [div_le_iff₀ hc]; linarith
    have e3 : (1 + 1 / ((j : ℝ) + 1)) * x = x + x / ((j : ℝ) + 1) := by ring
    have h2 : (16 * ((j : ℝ) + 1) + 3) * a ≤ 16 * ((j : ℝ) + 2) * a := by nlinarith
    push_cast
    nlinarith

/-!
## Complex martingales: real and imaginary parts
-/

theorem mart_martingale_clm [IsFiniteMeasure μ] (ℱ : Filtration ℕ m0) (T : ℂ →L[ℝ] ℝ)
    {M : ℕ → Ω → ℂ} (hM : Martingale M ℱ μ) : Martingale (fun n => T ∘ M n) ℱ μ :=
  ⟨fun n => T.continuous.comp_stronglyMeasurable (hM.stronglyAdapted n), fun _ j hij =>
    (T.comp_condExp_comm (hM.integrable j)).symm.trans ((hM.condExp_ae_eq hij).fun_comp T)⟩

theorem mart_enorm_pow_four_le (z : ℂ) : ‖z‖ₑ ^ 4 ≤ 2 * (‖z.re‖ₑ ^ 4 + ‖z.im‖ₑ ^ 4) := by
  have h : ‖z‖ ^ 4 ≤ 2 * (z.re ^ 4 + z.im ^ 4) := by
    have e : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have e' : ‖z‖ ^ 4 = (z.re ^ 2 + z.im ^ 2) ^ 2 := by rw [← e]; ring
    rw [e']
    nlinarith [sq_nonneg (z.re ^ 2 - z.im ^ 2)]
  have h1 : 0 ≤ z.re ^ 4 := Even.pow_nonneg (by decide) _
  have h2 : 0 ≤ z.im ^ 4 := Even.pow_nonneg (by decide) _
  calc ‖z‖ₑ ^ 4 = ENNReal.ofReal (‖z‖ ^ 4) := by
        rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
    _ ≤ ENNReal.ofReal (2 * (z.re ^ 4 + z.im ^ 4)) := ENNReal.ofReal_le_ofReal h
    _ = 2 * (‖z.re‖ₑ ^ 4 + ‖z.im‖ₑ ^ 4) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add h1 h2,
          ← Real.enorm_of_nonneg h1, ← Real.enorm_of_nonneg h2, enorm_pow, enorm_pow,
          ENNReal.ofReal_ofNat]

theorem mart_enorm_re_le (z : ℂ) : ‖z.re‖ₑ ≤ ‖z‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, Real.norm_eq_abs]
  exact ENNReal.ofReal_le_ofReal (Complex.abs_re_le_norm z)

theorem mart_enorm_im_le (z : ℂ) : ‖z.im‖ₑ ≤ ‖z‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, Real.norm_eq_abs]
  exact ENNReal.ofReal_le_ofReal (Complex.abs_im_le_norm z)

theorem mart_ofReal_sixteen (n : ℕ) :
    ENNReal.ofReal (16 * ((n : ℝ) + 1)) = 16 * ((n : ℝ≥0∞) + 1) := by
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (by positivity) zero_le_one,
    ENNReal.ofReal_natCast, ENNReal.ofReal_one, ENNReal.ofReal_ofNat]

/-- The real crude Burkholder bound in `lintegral` form. -/
theorem mart_lintegral_real_le [IsFiniteMeasure μ] (ℱ : Filtration ℕ m0) {X : ℕ → Ω → ℝ}
    (hX : Martingale X ℱ μ) (h0 : X 0 = 0) (hL : ∀ n, MemLp (X n) 4 μ) (n : ℕ) :
    ∫⁻ ω, ‖X n ω‖ₑ ^ 4 ∂μ ≤
      16 * ((n : ℝ≥0∞) + 1) * ∑ i ∈ range n, ∫⁻ ω, ‖X (i + 1) ω - X i ω‖ₑ ^ 4 ∂μ := by
  have hDL : ∀ i, MemLp (fun ω => X (i + 1) ω - X i ω) 4 μ := fun i => (hL (i + 1)).sub (hL i)
  have e : ∑ i ∈ range n, ∫⁻ ω, ‖X (i + 1) ω - X i ω‖ₑ ^ 4 ∂μ =
      ENNReal.ofReal (∑ i ∈ range n, ∫ ω, (X (i + 1) ω - X i ω) ^ 4 ∂μ) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun i _ =>
      integral_nonneg fun ω => Even.pow_nonneg (by decide) _]
    exact sum_congr rfl fun i _ => mart_lintegral_pow_four_eq (hDL i)
  rw [e, mart_lintegral_pow_four_eq (hL n), ← mart_ofReal_sixteen, ← ENNReal.ofReal_mul
    (by positivity)]
  exact ENNReal.ofReal_le_ofReal (mart_integral_pow_four_le ℱ hX h0 hL n)

/-- **Crude Burkholder for complex `L⁴` martingales**: `E|M_n|⁴ ≤ 64(n + 1) Σ_{i<n} E|D_i|⁴`. -/
theorem mart_lintegral_pow_four_le [IsFiniteMeasure μ] (ℱ : Filtration ℕ m0) {M : ℕ → Ω → ℂ}
    (hM : Martingale M ℱ μ) (h0 : M 0 = 0) (hL : ∀ n, MemLp (M n) 4 μ) (n : ℕ) :
    ∫⁻ ω, ‖M n ω‖ₑ ^ 4 ∂μ ≤
      64 * ((n : ℝ≥0∞) + 1) * ∑ i ∈ range n, ∫⁻ ω, ‖M (i + 1) ω - M i ω‖ₑ ^ 4 ∂μ := by
  have hre : Martingale (fun n ω => (M n ω).re) ℱ μ := by
    simpa [Function.comp_def] using mart_martingale_clm ℱ Complex.reCLM hM
  have him : Martingale (fun n ω => (M n ω).im) ℱ μ := by
    simpa [Function.comp_def] using mart_martingale_clm ℱ Complex.imCLM hM
  have hLre : ∀ n, MemLp (fun ω => (M n ω).re) 4 μ := fun n =>
    (hL n).mono (Complex.continuous_re.comp_aestronglyMeasurable (hL n).aestronglyMeasurable)
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _)
  have hLim : ∀ n, MemLp (fun ω => (M n ω).im) 4 μ := fun n =>
    (hL n).mono (Complex.continuous_im.comp_aestronglyMeasurable (hL n).aestronglyMeasurable)
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]; exact Complex.abs_im_le_norm _)
  have h0re : (fun n ω => (M n ω).re) 0 = 0 := by funext ω; simp [h0]
  have h0im : (fun n ω => (M n ω).im) 0 = 0 := by funext ω; simp [h0]
  have b1 := mart_lintegral_real_le ℱ hre h0re hLre n
  have b2 := mart_lintegral_real_le ℱ him h0im hLim n
  have hsum : ∀ (g : ℂ → ℝ), (∀ z, ‖g z‖ₑ ≤ ‖z‖ₑ) → (∀ z w, g z - g w = g (z - w)) →
      ∑ i ∈ range n, ∫⁻ ω, ‖g (M (i + 1) ω) - g (M i ω)‖ₑ ^ 4 ∂μ ≤
        ∑ i ∈ range n, ∫⁻ ω, ‖M (i + 1) ω - M i ω‖ₑ ^ 4 ∂μ := by
    intro g hg hsub
    refine sum_le_sum fun i _ => lintegral_mono fun ω => ?_
    rw [hsub]
    exact pow_le_pow_left₀ zero_le (hg _) 4
  have c1 := hsum Complex.re mart_enorm_re_le fun z w => (Complex.sub_re z w).symm
  have c2 := hsum Complex.im mart_enorm_im_le fun z w => (Complex.sub_im z w).symm
  have hm1 : AEMeasurable (fun ω => ‖(M n ω).re‖ₑ ^ 4) μ :=
    (hLre n).aestronglyMeasurable.aemeasurable.enorm.pow_const 4
  calc ∫⁻ ω, ‖M n ω‖ₑ ^ 4 ∂μ
      ≤ ∫⁻ ω, 2 * (‖(M n ω).re‖ₑ ^ 4 + ‖(M n ω).im‖ₑ ^ 4) ∂μ :=
        lintegral_mono fun ω => mart_enorm_pow_four_le _
    _ = 2 * (∫⁻ ω, ‖(M n ω).re‖ₑ ^ 4 ∂μ + ∫⁻ ω, ‖(M n ω).im‖ₑ ^ 4 ∂μ) := by
        rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_left' hm1]
    _ ≤ 2 * (16 * ((n : ℝ≥0∞) + 1) * ∑ i ∈ range n, ∫⁻ ω, ‖M (i + 1) ω - M i ω‖ₑ ^ 4 ∂μ +
          16 * ((n : ℝ≥0∞) + 1) * ∑ i ∈ range n, ∫⁻ ω, ‖M (i + 1) ω - M i ω‖ₑ ^ 4 ∂μ) := by
        gcongr
        · exact b1.trans (by gcongr)
        · exact b2.trans (by gcongr)
    _ = 64 * ((n : ℝ≥0∞) + 1) * ∑ i ∈ range n, ∫⁻ ω, ‖M (i + 1) ω - M i ω‖ₑ ^ 4 ∂μ := by ring

/-!
## Doob's `L⁴` maximal inequality in `lintegral` form
-/

theorem mart_rpow_four (x : ℝ≥0∞) : x ^ ((4 : ℝ≥0) : ℝ) = x ^ (4 : ℕ) := by
  rw [show ((4 : ℝ≥0) : ℝ) = ((4 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]

theorem mart_eLpNorm_pow_four {E : Type*} [NormedAddCommGroup E] {f : Ω → E}
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 4 μ ^ 4 = ∫⁻ ω, ‖f ω‖ₑ ^ 4 ∂μ := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (p := 4) (by norm_num) hf
  simp only [mart_rpow_four, ENNReal.coe_ofNat] at h
  exact h

/-- **Doob's `L⁴` inequality**: `E max_{k ≤ N}|M_k|⁴ ≤ 4 E|M_N|⁴` (`(4/3)⁴ ≤ 4`). -/
theorem mart_lintegral_runMax_le [IsFiniteMeasure μ] (ℱ : Filtration ℕ m0) {M : ℕ → Ω → ℂ}
    (hM : Martingale M ℱ μ) (N : ℕ) :
    ∫⁻ ω, ‖(range (N + 1)).sup' nonempty_range_add_one (fun k => ‖M k ω‖)‖ₑ ^ 4 ∂μ ≤
      4 * ∫⁻ ω, ‖M N ω‖ₑ ^ 4 ∂μ := by
  have hD := Stochastic.SDE.DoobLp.martingale_eLpNorm_runMax_norm_le hM (p := 4)
    (by norm_num) N
  rw [ENNReal.ofReal_ofNat] at hD
  have hgm : AEStronglyMeasurable
      (fun ω => (range (N + 1)).sup' nonempty_range_add_one (fun k => ‖M k ω‖)) μ :=
    (Finset.measurable_range_sup'' fun k _ =>
      ((hM.stronglyMeasurable k).mono (ℱ.le k)).norm.measurable).aestronglyMeasurable
  have hMN : AEStronglyMeasurable (M N) μ :=
    ((hM.stronglyMeasurable N).mono (ℱ.le N)).aestronglyMeasurable
  rw [← mart_eLpNorm_pow_four hgm, ← mart_eLpNorm_pow_four hMN]
  have hc : ENNReal.ofReal (4 / (4 - 1)) ^ 4 ≤ 4 := by
    rw [← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_ofNat 4]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  calc _ ≤ (ENNReal.ofReal (4 / (4 - 1)) * eLpNorm (M N) 4 μ) ^ 4 :=
        pow_le_pow_left₀ zero_le hD 4
    _ = ENNReal.ofReal (4 / (4 - 1)) ^ 4 * eLpNorm (M N) 4 μ ^ 4 := mul_pow _ _ _
    _ ≤ 4 * eLpNorm (M N) 4 μ ^ 4 := by gcongr

/-!
## The centred sum of `ℱ (i + 1)`-measurable steps
-/

/-- The centred sum `Σ_{i < n, i ∈ S} (Z i − E[Z i | ℱ i])`. -/
def martSum (ℱ : Filtration ℕ m0) (μ : Measure Ω) (S : Finset ℕ) (Z : ℕ → Ω → ℂ) (n : ℕ) :
    Ω → ℂ :=
  ∑ i ∈ (range n).filter (· ∈ S), (Z i - μ[Z i | ℱ i])

variable (ℱ : Filtration ℕ m0) (S : Finset ℕ) (Z : ℕ → Ω → ℂ)

theorem martSum_zero : martSum ℱ μ S Z 0 = 0 := by simp [martSum]

theorem martSum_succ (n : ℕ) :
    martSum ℱ μ S Z (n + 1) =
      martSum ℱ μ S Z n + if n ∈ S then Z n - μ[Z n | ℱ n] else 0 := by
  unfold martSum
  rw [range_add_one, filter_insert]
  split_ifs with h
  · rw [sum_insert (by simp), add_comm]
  · rw [add_zero]

variable {ℱ S Z}

theorem martingale_martSum [IsFiniteMeasure μ]
    (hZm : ∀ i ∈ S, StronglyMeasurable[ℱ (i + 1)] (Z i))
    (hZi : ∀ i ∈ S, Integrable (Z i) μ) : Martingale (martSum ℱ μ S Z) ℱ μ := by
  refine martingale_of_condExp_sub_eq_zero_nat (fun n => ?_) (fun n => ?_) (fun n => ?_)
  · unfold martSum
    refine Finset.stronglyMeasurable_sum _ fun i hi => ?_
    obtain ⟨hi1, hi2⟩ := mem_filter.1 hi
    have hin : i + 1 ≤ n := mem_range.1 hi1
    exact ((hZm i hi2).mono (ℱ.mono hin)).sub
      (stronglyMeasurable_condExp.mono (ℱ.mono (by omega)))
  · unfold martSum
    exact integrable_finsetSum' _ fun i hi => (hZi i (mem_filter.1 hi).2).sub integrable_condExp
  · rw [martSum_succ, add_sub_cancel_left]
    split_ifs with h
    · have h1 := condExp_sub (m := ℱ n) (hZi n h) (integrable_condExp (m := ℱ n) (f := Z n))
      have h2 : μ[μ[Z n | ℱ n] | ℱ n] = μ[Z n | ℱ n] :=
        condExp_of_stronglyMeasurable (ℱ.le n) stronglyMeasurable_condExp integrable_condExp
      filter_upwards [h1] with ω e
      rw [e, Pi.sub_apply, h2, sub_self, Pi.zero_apply]
    · rw [condExp_zero]

theorem memLp_martSum (hZ4 : ∀ i ∈ S, MemLp (Z i) 4 μ) (n : ℕ) :
    MemLp (martSum ℱ μ S Z n) 4 μ :=
  memLp_finsetSum' _ fun i hi =>
    (hZ4 i (mem_filter.1 hi).2).sub ((hZ4 i (mem_filter.1 hi).2).condExp (by norm_num))

/-- `E|Z − E[Z|ℱ i]|⁴ ≤ 16 E|Z|⁴`. -/
theorem lintegral_sub_condExp_pow_four_le {f : Ω → ℂ} (hf : AEStronglyMeasurable f μ)
    (i : ℕ) :
    ∫⁻ ω, ‖f ω - μ[f | ℱ i] ω‖ₑ ^ 4 ∂μ ≤ 16 * ∫⁻ ω, ‖f ω‖ₑ ^ 4 ∂μ := by
  have hc : ∫⁻ ω, ‖μ[f | ℱ i] ω‖ₑ ^ 4 ∂μ ≤ ∫⁻ ω, ‖f ω‖ₑ ^ 4 ∂μ := by
    rw [← mart_eLpNorm_pow_four hf, ← mart_eLpNorm_pow_four integrable_condExp.aestronglyMeasurable]
    exact pow_le_pow_left₀ zero_le (eLpNorm_condExp_le_eLpNorm f (by norm_num)) 4
  have hm : AEMeasurable (fun ω => ‖f ω‖ₑ ^ 4) μ := hf.aemeasurable.enorm.pow_const 4
  calc ∫⁻ ω, ‖f ω - μ[f | ℱ i] ω‖ₑ ^ 4 ∂μ
      ≤ ∫⁻ ω, 8 * (‖f ω‖ₑ ^ 4 + ‖μ[f | ℱ i] ω‖ₑ ^ 4) ∂μ :=
        lintegral_mono fun ω => (pow_le_pow_left₀ zero_le enorm_sub_le 4).trans
          (add_pow_four_le _ _)
    _ = 8 * (∫⁻ ω, ‖f ω‖ₑ ^ 4 ∂μ + ∫⁻ ω, ‖μ[f | ℱ i] ω‖ₑ ^ 4 ∂μ) := by
        rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_left' hm]
    _ ≤ 8 * (∫⁻ ω, ‖f ω‖ₑ ^ 4 ∂μ + ∫⁻ ω, ‖f ω‖ₑ ^ 4 ∂μ) := by gcongr
    _ = 16 * ∫⁻ ω, ‖f ω‖ₑ ^ 4 ∂μ := by ring

/-- **Doob + crude Burkholder for the centred sum**:
`E max_{k ≤ N}|martSum k|⁴ ≤ 4096 (N + 1) Σ_{i < N, i ∈ S} E|Z i|⁴`. -/
theorem lintegral_runMax_martSum_le [IsFiniteMeasure μ]
    (hZm : ∀ i ∈ S, StronglyMeasurable[ℱ (i + 1)] (Z i))
    (hZ4 : ∀ i ∈ S, MemLp (Z i) 4 μ) (N : ℕ) :
    ∫⁻ ω, ‖(range (N + 1)).sup' nonempty_range_add_one
        (fun k => ‖martSum ℱ μ S Z k ω‖)‖ₑ ^ 4 ∂μ ≤
      4096 * ((N : ℝ≥0∞) + 1) * ∑ i ∈ (range N).filter (· ∈ S), ∫⁻ ω, ‖Z i ω‖ₑ ^ 4 ∂μ := by
  have hM := martingale_martSum hZm fun i hi => (hZ4 i hi).integrable (by norm_num)
  have hstep : ∑ i ∈ range N, ∫⁻ ω, ‖martSum ℱ μ S Z (i + 1) ω - martSum ℱ μ S Z i ω‖ₑ ^ 4 ∂μ =
      ∑ i ∈ (range N).filter (· ∈ S), ∫⁻ ω, ‖Z i ω - μ[Z i | ℱ i] ω‖ₑ ^ 4 ∂μ := by
    rw [sum_filter]
    refine sum_congr rfl fun i _ => ?_
    split_ifs with h
    · simp only [martSum_succ, h, ↓reduceIte, Pi.add_apply, Pi.sub_apply, add_sub_cancel_left]
    · simp [martSum_succ, h]
  calc _ ≤ 4 * ∫⁻ ω, ‖martSum ℱ μ S Z N ω‖ₑ ^ 4 ∂μ := mart_lintegral_runMax_le ℱ hM N
    _ ≤ 4 * (64 * ((N : ℝ≥0∞) + 1) * ∑ i ∈ range N,
          ∫⁻ ω, ‖martSum ℱ μ S Z (i + 1) ω - martSum ℱ μ S Z i ω‖ₑ ^ 4 ∂μ) := by
        gcongr
        exact mart_lintegral_pow_four_le ℱ hM (martSum_zero ℱ S Z) (memLp_martSum hZ4) N
    _ ≤ 4 * (64 * ((N : ℝ≥0∞) + 1) * ∑ i ∈ (range N).filter (· ∈ S),
          16 * ∫⁻ ω, ‖Z i ω‖ₑ ^ 4 ∂μ) := by
        rw [hstep]
        gcongr with i hi
        exact lintegral_sub_condExp_pow_four_le (hZ4 i (mem_filter.1 hi).2).aestronglyMeasurable i
    _ = 4096 * ((N : ℝ≥0∞) + 1) * ∑ i ∈ (range N).filter (· ∈ S), ∫⁻ ω, ‖Z i ω‖ₑ ^ 4 ∂μ := by
        rw [← mul_sum]; ring

end MartGeneric

end BlockBand.SourceProcess.PhysApprox.B3
