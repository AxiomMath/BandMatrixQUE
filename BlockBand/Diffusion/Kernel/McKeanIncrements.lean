module

public import BlockBand.Diffusion.Kernel.McKeanContinuity

/-!
# Fourth increment moment of `pX`

Main result `mk_integral_kernelX_incr_le`: for `D₀ > 0`, `t > 0`, `x ≥ 0`, the function
`x' ↦ pX t x x' (x' - x)⁴` is integrable on `[0, ∞)` and
`∫_{[0,∞)} pX t x x' (x' - x)⁴ dx' ≤ 480√2 (1+x)⁴ (D₀t)² e^{81 D₀ t / 4}`.

Proof: `(x' - x)⁴ ≤ (1+2x)⁴ cosh² d (cosh d - 1)²` (`mk_incr_le_hypCos`, from
`2ab(cosh d - 1) ≥ (a-b)²` and `b ≤ 2a cosh d`), the isometry invariance, and
`∫_1^∞ K_T(c) c²(c-1)² dc ≤ 60√2/π · T² e^{-T/4} e^{81T/2}` via the Gamma integral
`∫_0^∞ s⁶ e^{-s²/(8T)} ds`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory Filter Topology Set Real
open scoped ENNReal

/-- `(x' - x)⁴ ≤ (1+2x)⁴ cosh² d (cosh d - 1)²` for `x, x' ≥ 0`. -/
theorem mk_incr_le_hypCos {x x' : ℝ} (hx : 0 ≤ x) (hx' : 0 ≤ x') (θ : ℝ) :
    (x' - x) ^ 4 ≤ (1 + 2 * x) ^ 4 * (mkHypCos x x' θ ^ 2 * (mkHypCos x x' θ - 1) ^ 2) := by
  obtain ⟨h1, h2⟩ := mk_hypCos_sub_one hx hx' θ
  have hb := mk_b_le_hypCos hx hx' θ
  set c := mkHypCos x x' θ
  set a := 1 + 2 * x
  set b := 1 + 2 * x'
  have ha : 1 ≤ a := by simp only [a]; linarith
  have hb1 : 1 ≤ b := by simp only [b]; linarith
  have hd : (x' - x) ^ 4 = ((a - b) ^ 2) ^ 2 / 16 := by simp only [a, b]; ring
  have hsq : ((a - b) ^ 2) ^ 2 ≤ (2 * a * b * (c - 1)) ^ 2 :=
    pow_le_pow_left₀ (sq_nonneg _) h2 2
  have hb2 : b ^ 2 ≤ (2 * a * c) ^ 2 := pow_le_pow_left₀ (by linarith) hb 2
  have hc1 : 0 ≤ (c - 1) ^ 2 := sq_nonneg _
  rw [hd]
  have : (2 * a * b * (c - 1)) ^ 2 ≤ 4 * a ^ 2 * (c - 1) ^ 2 * (2 * a * c) ^ 2 := by
    have : (2 * a * b * (c - 1)) ^ 2 = 4 * a ^ 2 * (c - 1) ^ 2 * b ^ 2 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hb2 (by positivity)
  nlinarith

/-- The pointwise majorant of the `s`-integrand of the fourth increment moment. -/
theorem mk_incr_integrand_le {T : ℝ} (hT : 0 < T) {s : ℝ} (hs : 0 < s) :
    |Real.sinh s| * (Real.sqrt (Real.cosh s - 1) *
        (mkMcKeanG T (Real.cosh s) * (Real.cosh s ^ 2 * (Real.cosh s - 1) ^ 2))) ≤
      Real.sqrt 2 / 4 * Real.exp (2 * (9 / 2 : ℝ) ^ 2 * T) *
        (s ^ (6 : ℝ) * Real.exp (-(1 / (8 * T)) * s ^ (2 : ℝ))) := by
  have hsh : 0 < Real.sinh s := Real.sinh_pos_iff.2 hs
  have hs2 : 0 < Real.sinh (s / 2) := Real.sinh_pos_iff.2 (by linarith)
  have hcm : Real.cosh s - 1 = 2 * Real.sinh (s / 2) ^ 2 := by
    have := Real.cosh_two_mul (s / 2)
    rw [show 2 * (s / 2) = s by ring, Real.cosh_sq] at this
    linarith
  unfold mkMcKeanG mkSdivSinh
  rw [Real.arcosh_cosh hs.le, abs_of_pos hsh, mk_sqrt_cosh_sub_one hs.le, hcm]
  simp only [ne_of_gt hs, ↓reduceIte]
  rw [Real.rpow_two, show (6 : ℝ) = (6 : ℕ) by norm_num, Real.rpow_natCast]
  have hid : Real.sinh s * (Real.sqrt 2 * Real.sinh (s / 2) *
      (2 * (s / Real.sinh s) * Real.exp (-s ^ 2 / (4 * T)) *
        (Real.cosh s ^ 2 * (2 * Real.sinh (s / 2) ^ 2) ^ 2))) =
      8 * Real.sqrt 2 * s * Real.sinh (s / 2) ^ 5 * Real.cosh s ^ 2 *
        Real.exp (-s ^ 2 / (4 * T)) := by
    field_simp
    norm_num
  rw [hid]
  have h1 : Real.sinh (s / 2) ^ 5 ≤ (s / 2 * Real.exp (s / 2)) ^ 5 :=
    pow_le_pow_left₀ hs2.le (mk_sinh_le_mul_exp _) 5
  have h2 : Real.cosh s ^ 2 ≤ Real.exp s ^ 2 :=
    pow_le_pow_left₀ (Real.cosh_pos s).le (mk_cosh_le_exp hs.le) 2
  have h3 : Real.exp (s / 2) ^ 5 * Real.exp s ^ 2 * Real.exp (-s ^ 2 / (4 * T)) ≤
      Real.exp (2 * (9 / 2 : ℝ) ^ 2 * T) * Real.exp (-(1 / (8 * T)) * s ^ 2) := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have h8 : 0 < 8 * T := by positivity
    have : ((5 : ℕ) : ℝ) * (s / 2) + ((2 : ℕ) : ℝ) * s + -s ^ 2 / (4 * T) -
        (2 * (9 / 2 : ℝ) ^ 2 * T + -(1 / (8 * T)) * s ^ 2) =
        -((s - 4 * (9 / 2) * T) ^ 2 / (8 * T)) := by
      push_cast; field_simp; ring
    have : 0 ≤ (s - 4 * (9 / 2) * T) ^ 2 / (8 * T) := by positivity
    linarith
  have hc0 : 0 ≤ Real.cosh s ^ 2 := by positivity
  have he0 := Real.exp_pos (-s ^ 2 / (4 * T))
  calc 8 * Real.sqrt 2 * s * Real.sinh (s / 2) ^ 5 * Real.cosh s ^ 2 *
        Real.exp (-s ^ 2 / (4 * T))
      ≤ 8 * Real.sqrt 2 * s * (s / 2 * Real.exp (s / 2)) ^ 5 * Real.exp s ^ 2 *
          Real.exp (-s ^ 2 / (4 * T)) := by gcongr
    _ = Real.sqrt 2 / 4 * s ^ 6 * (Real.exp (s / 2) ^ 5 * Real.exp s ^ 2 *
          Real.exp (-s ^ 2 / (4 * T))) := by ring
    _ ≤ Real.sqrt 2 / 4 * s ^ 6 * (Real.exp (2 * (9 / 2 : ℝ) ^ 2 * T) *
          Real.exp (-(1 / (8 * T)) * s ^ 2)) := by gcongr
    _ = _ := by ring

/-- `∫_1^∞ K_T(c) c² (c-1)² dc ≤ (√2/4) A_T e^{81T/2} (8T)^{7/2} Γ(7/2)/2`. -/
theorem mk_lintegral_hypKernel_incr_le {T : ℝ} (hT : 0 < T) :
    ∫⁻ c in Ioi (1 : ℝ), ENNReal.ofReal (mkHypKernel T c * (c ^ 2 * (c - 1) ^ 2)) ≤
      ENNReal.ofReal (mkA T * (Real.sqrt 2 / 4 * Real.exp (2 * (9 / 2 : ℝ) ^ 2 * T) *
        ((1 / (8 * T)) ^ (-((6 : ℝ) + 1) / 2) * (1 / 2) * Real.Gamma ((6 + 1) / 2)))) := by
  have hA := mk_mkA_pos hT
  set φ : ℝ → ℝ := fun c => c ^ 2 * (c - 1) ^ 2
  have hφ : ∀ {c w : ℝ}, 1 ≤ c → c ≤ w → φ c ≤ φ w := fun {c w} hc hcw => by
    simp only [φ]
    have h1 : c ^ 2 ≤ w ^ 2 := pow_le_pow_left₀ (by linarith) hcw 2
    have h2 : (c - 1) ^ 2 ≤ (w - 1) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    exact mul_le_mul h1 h2 (sq_nonneg _) (sq_nonneg _)
  have h1 : ∀ c ∈ Ioi (1 : ℝ), ENNReal.ofReal (mkHypKernel T c * φ c) ≤
      ENNReal.ofReal (mkA T) * ∫⁻ v in Ioi (0 : ℝ),
        ENNReal.ofReal (mkMcKeanG T (c + v ^ 2) * φ (c + v ^ 2)) := by
    intro c hc
    have hc1 : (1 : ℝ) ≤ c := le_of_lt hc
    rw [ENNReal.ofReal_mul (mk_hypKernel_pos hT c).le, mk_ofReal_hypKernel hT hc1, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ zero_le
    rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun v => ?_
    rw [← ENNReal.ofReal_mul (mk_mcKeanG_pos _ _).le]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (hφ hc1 (by nlinarith [sq_nonneg v])) (mk_mcKeanG_pos _ _).le)
  refine (setLIntegral_mono' measurableSet_Ioi h1).trans ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hgm : Measurable fun w => ENNReal.ofReal (mkMcKeanG T w * φ w) :=
    ((mk_mcKeanG_measurable T).mul (by simp only [φ]; fun_prop)).ennreal_ofReal
  rw [mk_lintegral_swap_sqrt (g := fun w => ENNReal.ofReal (mkMcKeanG T w * φ w)) hgm]
  have him := lintegral_image_eq_lintegral_abs_deriv_mul (s := Ioi (0 : ℝ)) (f := Real.cosh)
    (f' := Real.sinh) measurableSet_Ioi (fun s _ => (Real.hasDerivAt_cosh s).hasDerivWithinAt)
    (Real.cosh_injOn.mono Ioi_subset_Ici_self)
    (fun w => ENNReal.ofReal (Real.sqrt (w - 1)) * ENNReal.ofReal (mkMcKeanG T w * φ w))
  rw [mk_cosh_image_Ioi] at him
  rw [him]
  set C := Real.sqrt 2 / 4 * Real.exp (2 * (9 / 2 : ℝ) ^ 2 * T)
  have hint := (integrableOn_rpow_mul_exp_neg_mul_rpow (s := 6) (p := 2) (b := 1 / (8 * T))
    (by norm_num) (by norm_num) (by positivity))
  rw [ENNReal.ofReal_mul hA.le]
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  rw [← integral_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) (by positivity),
    ← integral_const_mul, ofReal_integral_eq_lintegral_ofReal (hint.const_mul C)
      ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun s hs => by
        have : (0 : ℝ) < s := hs; positivity))]
  refine setLIntegral_mono' measurableSet_Ioi fun s hs => ?_
  have hs0 : (0 : ℝ) < s := hs
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), ← ENNReal.ofReal_mul (abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (mk_incr_integrand_le hT hs0)

theorem mk_incr_const {T : ℝ} (hT : 0 < T) :
    2 * π * (mkA T * (Real.sqrt 2 / 4 * Real.exp (2 * (9 / 2 : ℝ) ^ 2 * T) *
        ((1 / (8 * T)) ^ (-((6 : ℝ) + 1) / 2) * (1 / 2) * Real.Gamma ((6 + 1) / 2)))) =
      120 * Real.sqrt 2 * T ^ 2 * Real.exp (-T / 4) * Real.exp (2 * (9 / 2 : ℝ) ^ 2 * T) := by
  have hG : Real.Gamma ((6 + 1) / 2) = 15 / 8 * Real.sqrt π := by
    rw [show ((6 : ℝ) + 1) / 2 = 1 / 2 + 1 + 1 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
      Real.Gamma_add_one (by norm_num), Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
    ring
  have h8 : 0 < 8 * T := by positivity
  have hr : (1 / (8 * T)) ^ (-((6 : ℝ) + 1) / 2) = (8 * T) ^ 2 * (8 * T) ^ (3 / 2 : ℝ) := by
    rw [show -((6 : ℝ) + 1) / 2 = -(2 + 3 / 2) by norm_num, Real.rpow_neg (by positivity),
      one_div, Real.inv_rpow h8.le, inv_inv, Real.rpow_add h8,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hpi := Real.pi_pos
  unfold mkA
  rw [hG, hr, mk_rpow_three_halves h8.le, mk_rpow_three_halves (by positivity : 0 ≤ 4 * π * T)]
  have hs8 : Real.sqrt (8 * T) = Real.sqrt 2 * Real.sqrt (4 * π * T) / Real.sqrt π := by
    rw [← Real.sqrt_mul (by norm_num), show 2 * (4 * π * T) = π * (8 * T) by ring,
      Real.sqrt_mul hpi.le]
    field_simp
  rw [hs8]
  have h1 : 0 < Real.sqrt (4 * π * T) := Real.sqrt_pos.2 (by positivity)
  have h2 : 0 < Real.sqrt π := Real.sqrt_pos.2 hpi
  field_simp
  have h3 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h4 : Real.sqrt π ^ 2 = π := Real.sq_sqrt hpi.le
  nlinarith [h3, h4]

/-- **Fourth increment moment (lower-integral form).** For `D₀ > 0`, `t > 0`, `x ≥ 0`:
`∫_{[0,∞)} pX t x x' (x' - x)⁴ dx' ≤ 480√2 (1+x)⁴ (D₀t)² e^{81 D₀ t / 4}`. -/
theorem mk_lintegral_kernelX_incr_le {D0 t x : ℝ} (hD0 : 0 < D0) (ht : 0 < t) (hx : 0 ≤ x) :
    ∫⁻ x' in Ici (0 : ℝ), ENNReal.ofReal (mkKernelX D0 t x x' * (x' - x) ^ 4) ≤
      ENNReal.ofReal (480 * Real.sqrt 2 * (1 + x) ^ 4 * (D0 * t) ^ 2 *
        Real.exp (81 * (D0 * t) / 4)) := by
  set T := D0 * t / 2 with hTdef
  have hT : 0 < T := by positivity
  set B := (1 + 2 * x) ^ 4 with hB
  have hB0 : 0 ≤ B := by positivity
  have hpt : ∀ x' ∈ Ioi (0 : ℝ), ENNReal.ofReal (mkKernelX D0 t x x' * (x' - x) ^ 4) ≤
      ENNReal.ofReal 2 * ENNReal.ofReal B * ∫⁻ θ in Ioo (-π) π,
        ENNReal.ofReal (mkHypKernel T (mkHypCos x x' θ) *
          (mkHypCos x x' θ ^ 2 * (mkHypCos x x' θ - 1) ^ 2)) := by
    intro x' hx'
    have hx'0 : 0 ≤ x' := le_of_lt hx'
    rw [mk_kernelX_eq ht hx'0, ENNReal.ofReal_mul (mk_hypRadial_nonneg hT x x'),
      mk_ofReal_hypRadial hT, mul_assoc, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ zero_le
    rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun θ => ?_
    rw [← ENNReal.ofReal_mul (mk_hypKernel_pos hT _).le, ← ENNReal.ofReal_mul hB0]
    refine ENNReal.ofReal_le_ofReal ?_
    have := mk_incr_le_hypCos hx hx'0 θ
    have hK := (mk_hypKernel_pos hT (mkHypCos x x' θ)).le
    calc mkHypKernel T (mkHypCos x x' θ) * (x' - x) ^ 4
        ≤ mkHypKernel T (mkHypCos x x' θ) *
            (B * (mkHypCos x x' θ ^ 2 * (mkHypCos x x' θ - 1) ^ 2)) :=
          mul_le_mul_of_nonneg_left this hK
      _ = _ := by ring
  have hgm : Measurable fun c => ENNReal.ofReal (mkHypKernel T c * (c ^ 2 * (c - 1) ^ 2)) :=
    ((mk_hypKernel_continuous hT).measurable.mul (by fun_prop)).ennreal_ofReal
  rw [setLIntegral_congr Ioi_ae_eq_Ici.symm]
  refine (setLIntegral_mono' measurableSet_Ioi hpt).trans ?_
  rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top),
    mk_lintegral_hypCos hx hgm]
  refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (mk_lintegral_hypKernel_incr_le hT) zero_le) zero_le).trans ?_
  rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hc := mk_incr_const hT
  have he : Real.exp (2 * (9 / 2 : ℝ) ^ 2 * T) = Real.exp (81 * (D0 * t) / 4) := by
    rw [hTdef]; congr 1; ring
  have hel : Real.exp (-T / 4) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hB' : B ≤ 16 * (1 + x) ^ 4 := by
    rw [hB, show (16 : ℝ) = 2 ^ 4 by norm_num, ← mul_pow]
    exact pow_le_pow_left₀ (by linarith) (by linarith) 4
  have hE0 := Real.exp_pos (81 * (D0 * t) / 4)
  have hT2 : T ^ 2 = (D0 * t) ^ 2 / 4 := by rw [hTdef]; ring
  calc 2 * B * (π * (mkA T * (Real.sqrt 2 / 4 * Real.exp (2 * (9 / 2 : ℝ) ^ 2 * T) *
        ((1 / (8 * T)) ^ (-((6 : ℝ) + 1) / 2) * (1 / 2) * Real.Gamma ((6 + 1) / 2)))))
      = B * (120 * Real.sqrt 2 * T ^ 2 * Real.exp (-T / 4) *
          Real.exp (2 * (9 / 2 : ℝ) ^ 2 * T)) := by rw [← hc]; ring
    _ ≤ (16 * (1 + x) ^ 4) * (120 * Real.sqrt 2 * T ^ 2 * 1 *
          Real.exp (2 * (9 / 2 : ℝ) ^ 2 * T)) := by gcongr
    _ = _ := by rw [he, hT2]; ring

/-- **Fourth increment moment, Bochner form**: integrability and
`∫_{[0,∞)} pX t x x' (x' - x)⁴ dx' ≤ 480√2 (1+x)⁴ (D₀t)² e^{81 D₀ t / 4}`. -/
theorem mk_integral_kernelX_incr_le {D0 t x : ℝ} (hD0 : 0 < D0) (ht : 0 < t) (hx : 0 ≤ x) :
    IntegrableOn (fun x' => mkKernelX D0 t x x' * (x' - x) ^ 4) (Ici 0) ∧
      ∫ x' in Ici (0 : ℝ), mkKernelX D0 t x x' * (x' - x) ^ 4 ≤
        480 * Real.sqrt 2 * (1 + x) ^ 4 * (D0 * t) ^ 2 * Real.exp (81 * (D0 * t) / 4) := by
  have hnn' : 0 ≤ᵐ[volume.restrict (Ici (0 : ℝ))] fun x' => mkKernelX D0 t x x' * (x' - x) ^ 4 :=
    ae_of_all _ fun x' => mul_nonneg (mk_kernelX_nonneg hD0 t x x')
      (by positivity)
  have hm : AEStronglyMeasurable (fun x' => mkKernelX D0 t x x' * (x' - x) ^ 4)
      (volume.restrict (Ici (0 : ℝ))) :=
    ((mk_kernelX_measurable_snd D0 t x).mul (by fun_prop)).aestronglyMeasurable
  have hle := mk_lintegral_kernelX_incr_le hD0 ht hx
  refine ⟨⟨hm, (hasFiniteIntegral_iff_ofReal hnn').2 (hle.trans_lt ENNReal.ofReal_lt_top)⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn' hm]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hle

end BlockBand.Diffusion
