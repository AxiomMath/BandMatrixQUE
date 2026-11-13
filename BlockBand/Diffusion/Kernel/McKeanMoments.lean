module

public import BlockBand.Diffusion.Kernel.McKeanApproxId
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.Gamma

/-!
# Polynomial moments of `pX`

Main result `mk_integral_kernelX_moment_le`: for `D₀ > 0`, `t > 0`, `x ≥ 0`,
`k ∈ ℕ`, the function `x' ↦ pX t x x' (1+x')^k` is integrable on `[0, ∞)` and
`∫_{[0,∞)} pX t x x' (1+x')^k dx' ≤ 2√2 · 4^k (1+x)^k e^{(k+1/2)² D₀ t}`.

Proof: `1 + x' ≤ 4(1+x) cosh d` (`mk_b_le_hypCos`, i.e. `cosh r' ≤ 2 cosh r cosh d`) inside the
angle integral, then the isometry invariance reduces to `2π ∫_1^∞ K_T(c) c^k dc`; with
`c^k ≤ (c+v²)^k`, `w = c + v²`, `w = cosh s`, `sinh(s/2) ≤ (s/2)e^{s/2}`, `cosh s ≤ e^s` and
`βs - s²/(4T) ≤ 2β²T - s²/(8T)` this is at most `2√2 e^{-T/4} e^{2β²T}` (`β = k + 1/2`,
`T = D₀t/2`), via the Gamma integral `∫_0^∞ s² e^{-s²/(8T)} ds`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory Filter Topology Set Real
open scoped ENNReal

/-- `cosh r' ≤ 2 cosh r cosh d` in the `x`-coordinates: `1 + 2x' ≤ 2(1+2x) cosh d`. -/
theorem mk_b_le_hypCos {x x' : ℝ} (hx : 0 ≤ x) (hx' : 0 ≤ x') (θ : ℝ) :
    1 + 2 * x' ≤ 2 * (1 + 2 * x) * mkHypCos x x' θ := by
  set S := 4 * Real.sqrt (x * (1 + x) * (x' * (1 + x'))) with hS
  have hS0 : 0 ≤ S := by positivity
  have hS2 : S ^ 2 = 16 * (x * (1 + x) * (x' * (1 + x'))) := by
    rw [hS, mul_pow, Real.sq_sqrt (by positivity)]; ring
  set a := 1 + 2 * x
  set b := 1 + 2 * x'
  have ha : 1 ≤ a := by simp only [a]; linarith
  have hb : 1 ≤ b := by simp only [b]; linarith
  have hu : 0 ≤ b * (2 * a ^ 2 - 1) := by nlinarith
  have hkey : (2 * a * S) ^ 2 ≤ (b * (2 * a ^ 2 - 1)) ^ 2 := by
    have : (2 * a * S) ^ 2 = 4 * a ^ 2 * (a ^ 2 - 1) * (b ^ 2 - 1) := by
      rw [mul_pow, hS2]; simp only [a, b]; ring
    rw [this]; nlinarith [sq_nonneg b, sq_nonneg (a ^ 2 - 1)]
  have hle : 2 * a * S ≤ b * (2 * a ^ 2 - 1) :=
    (pow_le_pow_iff_left₀ (by positivity) hu two_ne_zero).1 hkey
  have hc : a * b - S ≤ mkHypCos x x' θ := by
    have := Real.cos_le_one θ
    show a * b - S ≤ a * b - S * Real.cos θ
    nlinarith
  nlinarith

theorem mk_pow_le_hypCos {x x' : ℝ} (hx : 0 ≤ x) (hx' : 0 ≤ x') (θ : ℝ) (k : ℕ) :
    (1 + x') ^ k ≤ (4 * (1 + x)) ^ k * mkHypCos x x' θ ^ k := by
  rw [← mul_pow]
  have h1 := (mk_hypCos_sub_one hx hx' θ).1
  apply pow_le_pow_left₀ (by linarith)
  nlinarith [mk_b_le_hypCos hx hx' θ]

theorem mk_sinh_le_mul_exp (y : ℝ) : Real.sinh y ≤ y * Real.exp y := by
  have h := Real.add_one_le_exp (-(2 * y))
  have he : Real.exp (-(2 * y)) = Real.exp (-y) / Real.exp y := by
    rw [show -(2 * y) = -y - y by ring, Real.exp_sub]
  rw [he] at h
  have hp := Real.exp_pos y
  rw [Real.sinh_eq]
  have : Real.exp (-y) ≥ Real.exp y * (1 - 2 * y) := by
    rw [le_div_iff₀ hp] at h; linarith
  nlinarith

theorem mk_cosh_le_exp {s : ℝ} (hs : 0 ≤ s) : Real.cosh s ≤ Real.exp s := by
  rw [Real.cosh_eq]
  have : Real.exp (-s) ≤ Real.exp s := Real.exp_le_exp.2 (by linarith)
  linarith

/-- The pointwise majorant of the `s`-integrand of the `k`-th moment. -/
theorem mk_moment_integrand_le {T : ℝ} (hT : 0 < T) (k : ℕ) {s : ℝ} (hs : 0 < s) :
    |Real.sinh s| * (Real.sqrt (Real.cosh s - 1) *
        (mkMcKeanG T (Real.cosh s) * Real.cosh s ^ k)) ≤
      Real.sqrt 2 * Real.exp (2 * ((k : ℝ) + 1 / 2) ^ 2 * T) *
        (s ^ (2 : ℝ) * Real.exp (-(1 / (8 * T)) * s ^ (2 : ℝ))) := by
  have hsh : 0 < Real.sinh s := Real.sinh_pos_iff.2 hs
  have hs2 : 0 < Real.sinh (s / 2) := Real.sinh_pos_iff.2 (by linarith)
  unfold mkMcKeanG mkSdivSinh
  rw [Real.arcosh_cosh hs.le, abs_of_pos hsh, mk_sqrt_cosh_sub_one hs.le]
  simp only [ne_of_gt hs, ↓reduceIte]
  rw [Real.rpow_two]
  set β := (k : ℝ) + 1 / 2
  have hid : Real.sinh s * (Real.sqrt 2 * Real.sinh (s / 2) *
      (2 * (s / Real.sinh s) * Real.exp (-s ^ 2 / (4 * T)) * Real.cosh s ^ k)) =
      2 * Real.sqrt 2 * s * Real.sinh (s / 2) * Real.cosh s ^ k * Real.exp (-s ^ 2 / (4 * T)) := by
    field_simp
  rw [hid]
  have h1 : Real.sinh (s / 2) ≤ s / 2 * Real.exp (s / 2) := mk_sinh_le_mul_exp _
  have h2 : Real.cosh s ^ k ≤ Real.exp (k * s) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.cosh_pos s).le (mk_cosh_le_exp hs.le) k
  have h3 : Real.exp (s / 2) * Real.exp (k * s) * Real.exp (-s ^ 2 / (4 * T)) ≤
      Real.exp (2 * β ^ 2 * T) * Real.exp (-(1 / (8 * T)) * s ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have h8 : 0 < 8 * T := by positivity
    have : s / 2 + k * s + -s ^ 2 / (4 * T) - (2 * β ^ 2 * T + -(1 / (8 * T)) * s ^ 2) =
        -((s - 4 * β * T) ^ 2 / (8 * T)) := by
      simp only [β]; field_simp; ring
    have : 0 ≤ (s - 4 * β * T) ^ 2 / (8 * T) := by positivity
    linarith
  have hc0 : 0 ≤ Real.cosh s ^ k := pow_nonneg (Real.cosh_pos s).le k
  have he0 := Real.exp_pos (-s ^ 2 / (4 * T))
  calc 2 * Real.sqrt 2 * s * Real.sinh (s / 2) * Real.cosh s ^ k * Real.exp (-s ^ 2 / (4 * T))
      ≤ 2 * Real.sqrt 2 * s * (s / 2 * Real.exp (s / 2)) * Real.exp (k * s) *
          Real.exp (-s ^ 2 / (4 * T)) := by gcongr
    _ = Real.sqrt 2 * s ^ 2 * (Real.exp (s / 2) * Real.exp (k * s) *
          Real.exp (-s ^ 2 / (4 * T))) := by ring
    _ ≤ Real.sqrt 2 * s ^ 2 * (Real.exp (2 * β ^ 2 * T) * Real.exp (-(1 / (8 * T)) * s ^ 2)) := by
        gcongr
    _ = _ := by ring

theorem mk_mkA_mul_rpow {T : ℝ} (hT : 0 < T) :
    mkA T * (1 / (8 * T)) ^ (-((2 : ℝ) + 1) / 2) =
      Real.sqrt 2 * Real.exp (-T / 4) * (2 / π) ^ (3 / 2 : ℝ) := by
  unfold mkA
  have h4 : 0 < 4 * π * T := by positivity
  have h8 : 0 < 8 * T := by positivity
  rw [show -((2 : ℝ) + 1) / 2 = -(3 / 2) by norm_num, Real.rpow_neg (by positivity),
    one_div, Real.inv_rpow h8.le, inv_inv,
    show (2 / π : ℝ) = 8 * T / (4 * π * T) by field_simp; ring,
    Real.div_rpow h8.le h4.le]
  have := Real.rpow_pos_of_pos h4 (3 / 2 : ℝ)
  field_simp

/-- Polynomial moments of McKean's kernel against `dc` on `(1, ∞)`. -/
theorem mk_lintegral_hypKernel_pow_le {T : ℝ} (hT : 0 < T) (k : ℕ) :
    ∫⁻ c in Ioi (1 : ℝ), ENNReal.ofReal (mkHypKernel T c * c ^ k) ≤
      ENNReal.ofReal (2 * Real.exp (-T / 4) * (2 / π) ^ (3 / 2 : ℝ) *
        Real.exp (2 * ((k : ℝ) + 1 / 2) ^ 2 * T) * ((1 / 2) * Real.Gamma ((2 + 1) / 2))) := by
  have hA := mk_mkA_pos hT
  -- step 1: pointwise in `c`
  have h1 : ∀ c ∈ Ioi (1 : ℝ), ENNReal.ofReal (mkHypKernel T c * c ^ k) ≤
      ENNReal.ofReal (mkA T) * ∫⁻ v in Ioi (0 : ℝ),
        ENNReal.ofReal (mkMcKeanG T (c + v ^ 2) * (c + v ^ 2) ^ k) := by
    intro c hc
    have hc1 : (1 : ℝ) ≤ c := le_of_lt hc
    rw [ENNReal.ofReal_mul (mk_hypKernel_pos hT c).le, mk_ofReal_hypKernel hT hc1, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ zero_le
    rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun v => ?_
    rw [← ENNReal.ofReal_mul (mk_mcKeanG_pos _ _).le]
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (mk_mcKeanG_pos _ _).le)
    exact pow_le_pow_left₀ (by linarith) (by nlinarith [sq_nonneg v]) k
  refine (setLIntegral_mono' measurableSet_Ioi h1).trans ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hgm : Measurable fun w => ENNReal.ofReal (mkMcKeanG T w * w ^ k) :=
    ((mk_mcKeanG_measurable T).mul (measurable_id.pow_const k)).ennreal_ofReal
  rw [mk_lintegral_swap_sqrt (g := fun w => ENNReal.ofReal (mkMcKeanG T w * w ^ k)) hgm]
  -- step 2: `w = cosh s`
  have him := lintegral_image_eq_lintegral_abs_deriv_mul (s := Ioi (0 : ℝ)) (f := Real.cosh)
    (f' := Real.sinh) measurableSet_Ioi (fun s _ => (Real.hasDerivAt_cosh s).hasDerivWithinAt)
    (Real.cosh_injOn.mono Ioi_subset_Ici_self)
    (fun w => ENNReal.ofReal (Real.sqrt (w - 1)) * ENNReal.ofReal (mkMcKeanG T w * w ^ k))
  rw [mk_cosh_image_Ioi] at him
  rw [him]
  -- step 3: Gaussian majorant
  set C := Real.sqrt 2 * Real.exp (2 * ((k : ℝ) + 1 / 2) ^ 2 * T)
  have hC : 0 ≤ C := by positivity
  have hint := (integrableOn_rpow_mul_exp_neg_mul_rpow (s := 2) (p := 2) (b := 1 / (8 * T))
    (by norm_num) (by norm_num) (by positivity))
  have h3 : ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal |Real.sinh s| *
      (ENNReal.ofReal (Real.sqrt (Real.cosh s - 1)) *
        ENNReal.ofReal (mkMcKeanG T (Real.cosh s) * Real.cosh s ^ k)) ≤
      ENNReal.ofReal (C * ((1 / (8 * T)) ^ (-((2 : ℝ) + 1) / 2) * (1 / 2) *
        Real.Gamma ((2 + 1) / 2))) := by
    rw [← integral_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) (by positivity),
      ← integral_const_mul, ofReal_integral_eq_lintegral_ofReal (hint.const_mul C)
        ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun s hs => by
          have : (0 : ℝ) < s := hs; positivity))]
    refine setLIntegral_mono' measurableSet_Ioi fun s hs => ?_
    have hs0 : (0 : ℝ) < s := hs
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), ← ENNReal.ofReal_mul (abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (mk_moment_integrand_le hT k hs0)
  refine (mul_le_mul_of_nonneg_left h3 zero_le).trans ?_
  rw [← ENNReal.ofReal_mul hA.le]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  have := mk_mkA_mul_rpow hT
  simp only [C]
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  linear_combination (Real.sqrt 2 * Real.exp (2 * ((k : ℝ) + 1 / 2) ^ 2 * T) * (1 / 2) *
    Real.Gamma ((2 + 1) / 2)) * this + (Real.exp (2 * ((k : ℝ) + 1 / 2) ^ 2 * T) *
      Real.Gamma ((2 + 1) / 2) * Real.exp (-T / 4) * (2 / π) ^ (3 / 2 : ℝ) * (1 / 2)) * h2

theorem mk_rpow_three_halves {y : ℝ} (hy : 0 ≤ y) : y ^ (3 / 2 : ℝ) = y * Real.sqrt y := by
  rcases hy.eq_or_lt with h | h
  · subst h; simp
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add h, Real.rpow_one,
    Real.sqrt_eq_rpow]

theorem mk_moment_const {T : ℝ} (k : ℕ) :
    2 * π * (2 * Real.exp (-T / 4) * (2 / π) ^ (3 / 2 : ℝ) *
        Real.exp (2 * ((k : ℝ) + 1 / 2) ^ 2 * T) * ((1 / 2) * Real.Gamma ((2 + 1) / 2))) =
      2 * Real.sqrt 2 * Real.exp (-T / 4) * Real.exp (2 * ((k : ℝ) + 1 / 2) ^ 2 * T) := by
  have hG : Real.Gamma ((2 + 1) / 2) = Real.sqrt π / 2 := by
    rw [show ((2 : ℝ) + 1) / 2 = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
      Real.Gamma_one_half_eq]
    ring
  have hpi := Real.pi_pos
  have hsp : 0 < Real.sqrt π := Real.sqrt_pos.2 hpi
  rw [hG, Real.div_rpow (by norm_num) hpi.le, mk_rpow_three_halves (by norm_num),
    mk_rpow_three_halves hpi.le]
  field_simp

/-- **Polynomial moments.** For `D₀ > 0`, `t > 0`, `x ≥ 0`, `k ∈ ℕ`:
`∫_{[0,∞)} pX t x x' (1+x')^k dx' ≤ 2√2 · 4^k (1+x)^k e^{(k+1/2)² D₀ t}` (lower-integral form). -/
theorem mk_lintegral_kernelX_moment_le {D0 t x : ℝ} (hD0 : 0 < D0) (ht : 0 < t) (hx : 0 ≤ x)
    (k : ℕ) :
    ∫⁻ x' in Ici (0 : ℝ), ENNReal.ofReal (mkKernelX D0 t x x' * (1 + x') ^ k) ≤
      ENNReal.ofReal (2 * Real.sqrt 2 * 4 ^ k * (1 + x) ^ k *
        Real.exp (((k : ℝ) + 1 / 2) ^ 2 * D0 * t)) := by
  set T := D0 * t / 2 with hTdef
  have hT : 0 < T := by positivity
  set B := (4 * (1 + x)) ^ k with hB
  have hB0 : 0 ≤ B := by positivity
  have hpt : ∀ x' ∈ Ioi (0 : ℝ), ENNReal.ofReal (mkKernelX D0 t x x' * (1 + x') ^ k) ≤
      ENNReal.ofReal 2 * ENNReal.ofReal B * ∫⁻ θ in Ioo (-π) π,
        ENNReal.ofReal (mkHypKernel T (mkHypCos x x' θ) * mkHypCos x x' θ ^ k) := by
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
    have := mk_pow_le_hypCos hx hx'0 θ k
    have hK := (mk_hypKernel_pos hT (mkHypCos x x' θ)).le
    calc mkHypKernel T (mkHypCos x x' θ) * (1 + x') ^ k
        ≤ mkHypKernel T (mkHypCos x x' θ) * (B * mkHypCos x x' θ ^ k) :=
          mul_le_mul_of_nonneg_left this hK
      _ = _ := by ring
  have hgm : Measurable fun c => ENNReal.ofReal (mkHypKernel T c * c ^ k) :=
    ((mk_hypKernel_continuous hT).measurable.mul (measurable_id.pow_const k)).ennreal_ofReal
  rw [setLIntegral_congr Ioi_ae_eq_Ici.symm]
  refine (setLIntegral_mono' measurableSet_Ioi hpt).trans ?_
  rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top),
    mk_lintegral_hypCos hx hgm]
  refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (mk_lintegral_hypKernel_pow_le hT k) zero_le) zero_le).trans ?_
  rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hc := mk_moment_const (T := T) k
  have he : Real.exp (2 * ((k : ℝ) + 1 / 2) ^ 2 * T) =
      Real.exp (((k : ℝ) + 1 / 2) ^ 2 * D0 * t) := by
    rw [hTdef]; congr 1; ring
  have hel : Real.exp (-T / 4) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hB' : B = 4 ^ k * (1 + x) ^ k := by rw [hB, mul_pow]
  have hE0 := Real.exp_pos (((k : ℝ) + 1 / 2) ^ 2 * D0 * t)
  calc 2 * B * (π * (2 * Real.exp (-T / 4) * (2 / π) ^ (3 / 2 : ℝ) *
        Real.exp (2 * ((k : ℝ) + 1 / 2) ^ 2 * T) * ((1 / 2) * Real.Gamma ((2 + 1) / 2))))
      = B * (2 * Real.sqrt 2 * Real.exp (-T / 4) * Real.exp (2 * ((k : ℝ) + 1 / 2) ^ 2 * T)) := by
        rw [← hc]; ring
    _ ≤ B * (2 * Real.sqrt 2 * 1 * Real.exp (2 * ((k : ℝ) + 1 / 2) ^ 2 * T)) := by gcongr
    _ = _ := by rw [he, hB']; ring

/-- **Polynomial moments, Bochner form**: integrability and the bound. -/
theorem mk_integral_kernelX_moment_le {D0 t x : ℝ} (hD0 : 0 < D0) (ht : 0 < t) (hx : 0 ≤ x)
    (k : ℕ) :
    IntegrableOn (fun x' => mkKernelX D0 t x x' * (1 + x') ^ k) (Ici 0) ∧
      ∫ x' in Ici (0 : ℝ), mkKernelX D0 t x x' * (1 + x') ^ k ≤
        2 * Real.sqrt 2 * 4 ^ k * (1 + x) ^ k * Real.exp (((k : ℝ) + 1 / 2) ^ 2 * D0 * t) := by
  have hnn : ∀ x' ∈ Ici (0 : ℝ), 0 ≤ mkKernelX D0 t x x' * (1 + x') ^ k := fun x' hx' =>
    mul_nonneg (mk_kernelX_nonneg hD0 t x x')
      (pow_nonneg (by have : (0 : ℝ) ≤ x' := hx'; linarith) k)
  have hnn' : 0 ≤ᵐ[volume.restrict (Ici (0 : ℝ))] fun x' => mkKernelX D0 t x x' * (1 + x') ^ k :=
    (ae_restrict_iff' measurableSet_Ici).2 (ae_of_all _ hnn)
  have hm : AEStronglyMeasurable (fun x' => mkKernelX D0 t x x' * (1 + x') ^ k)
      (volume.restrict (Ici (0 : ℝ))) :=
    ((mk_kernelX_measurable_snd D0 t x).mul ((measurable_const.add measurable_id).pow_const k))
      |>.aestronglyMeasurable
  have hle := mk_lintegral_kernelX_moment_le hD0 ht hx k
  refine ⟨⟨hm, (hasFiniteIntegral_iff_ofReal hnn').2 (hle.trans_lt ENNReal.ofReal_lt_top)⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn' hm]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hle

end BlockBand.Diffusion
