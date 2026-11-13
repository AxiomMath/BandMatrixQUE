module

public import BlockBand.Diffusion.Kernel.McKeanRadialMass
public import BlockBand.Diffusion.Kernel.McKeanInvariance
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Mass one, symmetry and the on-diagonal bound of `pX`

* **KA1** `mk_integral_kernelX`: `∫_{[0,∞)} pX t x x' dx' = 1` for `t > 0`, `x ≥ 0`
  (Lebesgue measure); `mk_integrableOn_kernelX`; the lower-integral form `mk_lintegral_kernelX`.
  Proof: move the angle window to `(-π, π)` (periodicity), apply the isometry invariance
  `mk_lintegral_hypCos` and the radial mass `∫_1^∞ K_T = 1/(2π)`.
* **KA2** `mk_kernelX_comm`: `pX t x x' = pX t x' x` for `x, x' ≥ 0` (all `t`). Off the
  half-line it fails (`mk_kernelX_not_comm`: `pX t 0 (-1) = 0 < pX t (-1) 0`), because of the
  indicator of `x' ≥ 0` in the definition.
* **KA6 (on-diagonal)** `mk_kernelX_le_diag`: `pX t x x' ≤ C(D₀t/2)` for all real `x, x'`,
  `t > 0`, with the explicit `C(T) = 4π² A_T e^T`, `A_T = √2 e^{-T/4}(4πT)^{-3/2}`
  (`mkDiagBound`, continuous on `(0, ∞)`); `mk_kernelX_bdd_of_isCompact`: a uniform bound for
  `t` in a compact subset of `(0, ∞)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory Filter Topology Set Real
open scoped ENNReal

/-- Moving the angle window from `[0, 2π]` to `(-π, π)`. -/
theorem mk_hypRadial_eq_Ioo (T x x' : ℝ) :
    mkHypRadial T x x' = 2 * ∫ θ in Ioo (-π) π, mkHypKernel T (mkHypCos x x' θ) := by
  unfold mkHypRadial
  have hper : Function.Periodic (fun φ => mkHypKernel T (mkHypCos x x' φ)) (2 * π) := by
    intro φ; simp only [mkHypCos, Real.cos_add_two_pi]
  have h := hper.intervalIntegral_add_eq 0 (-π)
  rw [zero_add, show -π + 2 * π = π by ring] at h
  rw [h, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    integral_Ioc_eq_integral_Ioo]

theorem mk_hypKernel_comp_continuous {T : ℝ} (hT : 0 < T) (x x' : ℝ) :
    Continuous fun θ => mkHypKernel T (mkHypCos x x' θ) :=
  (mk_hypKernel_continuous hT).comp (by unfold mkHypCos; fun_prop)

theorem mk_ofReal_hypRadial {T : ℝ} (hT : 0 < T) (x x' : ℝ) :
    ENNReal.ofReal (mkHypRadial T x x') =
      ENNReal.ofReal 2 * ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal (mkHypKernel T (mkHypCos x x' θ)) := by
  rw [mk_hypRadial_eq_Ioo, ENNReal.ofReal_mul (by norm_num),
    ofReal_integral_eq_lintegral_ofReal
      (((mk_hypKernel_comp_continuous hT x x').integrableOn_Icc).mono_set Ioo_subset_Icc_self)
      (ae_of_all _ fun θ => (mk_hypKernel_pos hT _).le)]

/-- **Mass one (lower integral form).** -/
theorem mk_lintegral_kernelX {D0 t x : ℝ} (hD0 : 0 < D0) (ht : 0 < t) (hx : 0 ≤ x) :
    ∫⁻ x' in Ici (0 : ℝ), ENNReal.ofReal (mkKernelX D0 t x x') = 1 := by
  have hT : 0 < D0 * t / 2 := by positivity
  rw [setLIntegral_congr Ioi_ae_eq_Ici.symm,
    setLIntegral_congr_fun measurableSet_Ioi fun x' hx' => by
      rw [mk_kernelX_eq ht (le_of_lt hx'), mk_ofReal_hypRadial hT],
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    mk_lintegral_hypCos hx (g := fun c => ENNReal.ofReal (mkHypKernel (D0 * t / 2) c))
      (mk_hypKernel_continuous hT).measurable.ennreal_ofReal,
    mk_lintegral_hypKernel hT, ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_mul (by positivity)]
  rw [show 2 * π * (1 / (2 * π)) = 1 by field_simp, ENNReal.ofReal_one]

theorem mk_kernelX_measurable_snd (D0 t x : ℝ) : Measurable (mkKernelX D0 t x) :=
  (mk_kernelX_measurable D0).comp (f := fun x' : ℝ => (t, x, x')) (by fun_prop)

/-- **Integrability** of `x' ↦ pX t x x'` on `[0, ∞)`. -/
theorem mk_integrableOn_kernelX {D0 t x : ℝ} (hD0 : 0 < D0) (ht : 0 < t) (hx : 0 ≤ x) :
    IntegrableOn (mkKernelX D0 t x) (Ici 0) := by
  refine ⟨(mk_kernelX_measurable_snd D0 t x).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x' => mk_kernelX_nonneg hD0 t x x'),
    mk_lintegral_kernelX hD0 ht hx]
  exact ENNReal.one_lt_top

/-- **KA1: mass one.** For `D₀ > 0`, `t > 0`, `x ≥ 0`: `∫_{[0,∞)} pX t x x' dx' = 1`. -/
theorem mk_integral_kernelX {D0 t x : ℝ} (hD0 : 0 < D0) (ht : 0 < t) (hx : 0 ≤ x) :
    ∫ x' in Ici (0 : ℝ), mkKernelX D0 t x x' = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x' => mk_kernelX_nonneg hD0 t x x')
    (mk_kernelX_measurable_snd D0 t x).aestronglyMeasurable, mk_lintegral_kernelX hD0 ht hx,
    ENNReal.toReal_one]

/-- **KA1 on the whole line**: `pX t x x' = 0` for `x' < 0`, so `∫_ℝ pX t x x' dx' = 1`. -/
theorem mk_integral_kernelX_univ {D0 t x : ℝ} (hD0 : 0 < D0) (ht : 0 < t) (hx : 0 ≤ x) :
    ∫ x', mkKernelX D0 t x x' = 1 := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ici 0) fun x' hx' => by
    have : ¬ 0 ≤ x' := hx'
    simp [mkKernelX, this]]
  exact mk_integral_kernelX hD0 ht hx

/-- Symmetry of the law of cosines. -/
theorem mk_hypCos_comm (x x' φ : ℝ) : mkHypCos x x' φ = mkHypCos x' x φ := by
  unfold mkHypCos
  rw [show x * (1 + x) * (x' * (1 + x')) = x' * (1 + x') * (x * (1 + x)) by ring]
  ring

theorem mk_hypRadial_comm (T x x' : ℝ) : mkHypRadial T x x' = mkHypRadial T x' x := by
  unfold mkHypRadial
  simp_rw [mk_hypCos_comm x x']

/-- **KA2: symmetry** on the half-line: `pX t x x' = pX t x' x` for `x, x' ≥ 0` (any `t`). -/
theorem mk_kernelX_comm {D0 t x x' : ℝ} (hx : 0 ≤ x) (hx' : 0 ≤ x') :
    mkKernelX D0 t x x' = mkKernelX D0 t x' x := by
  unfold mkKernelX
  by_cases ht : 0 < t
  · simp only [ht, hx, hx', and_self, ↓reduceIte, mk_hypRadial_comm]
  · simp [ht]

/-- Symmetry fails off the half-line: `pX t (-1) 0 > 0 = pX t 0 (-1)`. -/
theorem mk_kernelX_not_comm {D0 t : ℝ} (hD0 : 0 < D0) (ht : 0 < t) :
    mkKernelX D0 t 0 (-1) = 0 ∧ 0 < mkKernelX D0 t (-1) 0 :=
  ⟨by simp [mkKernelX], mk_kernelX_zero_pos hD0 ht (-1)⟩

/-- The normalising constant `A_T = √2 e^{-T/4} (4πT)^{-3/2}`. -/
def mkA (T : ℝ) : ℝ := Real.sqrt 2 * Real.exp (-T / 4) / (4 * π * T) ^ (3 / 2 : ℝ)

/-- The explicit on-diagonal bound `C(T) = 4π² A_T e^T`. -/
def mkDiagBound (T : ℝ) : ℝ := 4 * π ^ 2 * mkA T * Real.exp T

theorem mk_hypKernel_le {T : ℝ} (hT : 0 < T) (c : ℝ) :
    mkHypKernel T c ≤ mkA T * (π * Real.exp T) := by
  unfold mkHypKernel
  have hA : 0 ≤ Real.sqrt 2 * Real.exp (-T / 4) / (4 * π * T) ^ (3 / 2 : ℝ) := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hA
  have hb : IntegrableOn (fun v : ℝ => 2 * Real.exp T * (1 + v ^ 2)⁻¹) (Ioi 0) :=
    (integrable_inv_one_add_sq.const_mul _).integrableOn
  calc ∫ v in Ioi (0 : ℝ), mkMcKeanG T (max c 1 + v ^ 2)
      ≤ ∫ v in Ioi (0 : ℝ), 2 * Real.exp T * (1 + v ^ 2)⁻¹ :=
        setIntegral_mono_on (mk_integrableOn_G hT c) hb measurableSet_Ioi fun v _ =>
          mk_mcKeanG_le hT (by linarith [le_max_right c 1])
    _ = π * Real.exp T := by
        rw [integral_const_mul, integral_Ioi_inv_one_add_sq, Real.arctan_zero]; ring

/-- **KA6 (on-diagonal bound).** `pX t x x' ≤ C(D₀t/2)` for all `x, x'` and `t > 0`. -/
theorem mk_kernelX_le_diag {D0 t : ℝ} (hD0 : 0 < D0) (ht : 0 < t) (x x' : ℝ) :
    mkKernelX D0 t x x' ≤ mkDiagBound (D0 * t / 2) := by
  have hT : 0 < D0 * t / 2 := by positivity
  have hC : 0 ≤ mkDiagBound (D0 * t / 2) := by unfold mkDiagBound mkA; positivity
  unfold mkKernelX
  split_ifs with h
  · rw [mk_hypRadial_eq_Ioo]
    have hI : ∫ θ in Ioo (-π) π, mkHypKernel (D0 * t / 2) (mkHypCos x x' θ) ≤
        ∫ θ in Ioo (-π) π, mkA (D0 * t / 2) * (π * Real.exp (D0 * t / 2)) :=
      setIntegral_mono_on
        (((mk_hypKernel_comp_continuous hT x x').integrableOn_Icc).mono_set Ioo_subset_Icc_self)
        (continuous_const.integrableOn_Icc.mono_set Ioo_subset_Icc_self) measurableSet_Ioo
        fun θ _ => mk_hypKernel_le hT _
    rw [setIntegral_const, Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos]),
      smul_eq_mul] at hI
    unfold mkDiagBound
    nlinarith [hI]
  · exact hC

theorem mk_diagBound_continuousOn : ContinuousOn mkDiagBound (Ioi 0) := by
  unfold mkDiagBound mkA
  refine ContinuousOn.mul (ContinuousOn.mul continuousOn_const (ContinuousOn.div
    (by fun_prop) ?_ ?_)) (by fun_prop)
  · exact fun T hT => (ContinuousAt.rpow_const (by fun_prop)
      (Or.inl (by have : 0 < T := hT; positivity))).continuousWithinAt
  · intro T hT; have : 0 < T := hT; positivity

/-- **KA6 (on-diagonal bound, compact time sets).** -/
theorem mk_kernelX_bdd_of_isCompact {D0 : ℝ} (hD0 : 0 < D0) {K : Set ℝ} (hK : IsCompact K)
    (hK0 : K ⊆ Ioi 0) : ∃ C, ∀ t ∈ K, ∀ x x' : ℝ, mkKernelX D0 t x x' ≤ C := by
  have hc : ContinuousOn (fun t => mkDiagBound (D0 * t / 2)) K :=
    mk_diagBound_continuousOn.comp (by fun_prop) fun t ht => by
      have : 0 < t := hK0 ht; show 0 < D0 * t / 2; positivity
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨C, fun t ht x x' => (mk_kernelX_le_diag hD0 (hK0 ht) x x').trans ?_⟩
  exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC t ht)

end BlockBand.Diffusion
