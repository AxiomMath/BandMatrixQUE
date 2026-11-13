module

public import BlockBand.Diffusion.Comparison.RadialGaussElementary

/-!
# Two-sided Gaussian bounds for McKean's pole kernel (package K-B′)

With the planar comparison profile
`gcPoleGauss T ρ = (4πT)⁻¹ e^{-ρ²/(4T)} √σ(ρ)` (`σ = gcSdivSinh`), McKean's kernel satisfies,
for every `T > 0`, `ρ ≥ 0`:

* `gc_hypKernel_cosh_le` : `K_T(cosh ρ) ≤ 2√π · gcPoleGauss T ρ`;
* `gc_hypKernel_cosh_ge` : for `T ≤ T₀`, `gcPoleLow T₀ · gcPoleGauss T ρ ≤ K_T(cosh ρ)` with
  `gcPoleLow T₀ = e^{-T₀/4} e^{-3/2} / (√(1+2T₀) √π) > 0`.

*Mechanism.* In McKean's integral `∫_0^∞ 2σ(s) e^{-s²/(4T)} dv`, `cosh s = cosh ρ + v²`, the
tangent-line inequalities of `cosh √·` give `2σ(s)v² ≤ s² - ρ² ≤ 2σ(ρ)v²`. Upper bound:
`σ(s) e^{-σ(s)v²/(2T)} ≤ σ(s)/(1 + σ(s)v²/(2T)) ≤ σ(ρ)/(1 + σ(ρ)v²/(2T))` (the last map is
increasing in `σ(s) ≤ σ(ρ)`), a Cauchy profile of width `√(2T/σ(ρ))`. Lower bound: on
`v ≤ √(T/(σ(ρ)(1+2T₀)))` one has `s - ρ ≤ 1`, hence `σ(s) ≥ σ(ρ)/e`, and
`s² - ρ² ≤ 2T`; integrate the constant over that interval.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory Set Real

/-- The planar comparison profile `(4πT)⁻¹ e^{-ρ²/(4T)} √σ(ρ)`. -/
def gcPoleGauss (T ρ : ℝ) : ℝ :=
  (4 * π * T)⁻¹ * Real.exp (-ρ ^ 2 / (4 * T)) * Real.sqrt (gcSdivSinh ρ)

/-- The lower pole constant on `(0, T₀]`. -/
def gcPoleLow (T₀ : ℝ) : ℝ :=
  Real.exp (-T₀ / 4) * Real.exp (-(3 / 2)) / (Real.sqrt (1 + 2 * T₀) * Real.sqrt π)

theorem gc_poleLow_pos {T₀ : ℝ} (hT₀ : 0 ≤ T₀) : 0 < gcPoleLow T₀ := by
  unfold gcPoleLow
  have h1 : 0 < Real.sqrt (1 + 2 * T₀) := Real.sqrt_pos.2 (by linarith)
  have h2 : 0 < Real.sqrt π := Real.sqrt_pos.2 Real.pi_pos
  positivity

theorem gc_poleGauss_nonneg {T : ℝ} (hT : 0 < T) (ρ : ℝ) : 0 ≤ gcPoleGauss T ρ := by
  unfold gcPoleGauss
  have := Real.pi_pos
  positivity

theorem gc_rpow_three_halves {T : ℝ} (hT : 0 < T) :
    (4 * π * T) ^ (3 / 2 : ℝ) = 4 * π * T * (2 * Real.sqrt π * Real.sqrt T) := by
  have hb : 0 < 4 * π * T := by have := Real.pi_pos; positivity
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hb, Real.rpow_one,
    ← Real.sqrt_eq_rpow, Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num),
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

theorem gc_alg_up (w p t q e₁ E π' T' b' : ℝ) (hw : w * w = 2) (hp' : p * p = π')
    (ht' : t * t = T') (hq' : q * q = b') (hp : 0 < p) (ht : 0 < t) (hq : 0 < q) :
    w * e₁ / (4 * π' * T' * (2 * p * t)) * (2 * E * b' * (π' / (q / (w * t)))) =
      e₁ * (2 * p * ((4 * π' * T')⁻¹ * E * q)) := by
  subst hp' ht' hq'
  field_simp
  linear_combination (e₁ * E) * hw

theorem gc_alg_low (w p t q e₁ e₃ E s₀ π' T' b' : ℝ) (hp' : p * p = π') (hq' : q * q = b')
    (hp : 0 < p) (ht : 0 < t) (hq : 0 < q) (hs₀ : 0 < s₀) (hT' : 0 < T') :
    w * e₁ * e₃ / (s₀ * p) * ((4 * π' * T')⁻¹ * E * q) =
      w * e₁ / (4 * π' * T' * (2 * p * t)) * (t / (q * s₀) * (2 * b' * e₃ * E)) := by
  subst hp' hq'
  field_simp

/-- The substituted variable `s = arcosh(cosh ρ + v²)`: `cosh s = cosh ρ + v²` and `ρ ≤ s`. -/
theorem gc_arc_facts {ρ : ℝ} (hρ : 0 ≤ ρ) (v : ℝ) :
    Real.cosh (Real.arcosh (Real.cosh ρ + v ^ 2)) = Real.cosh ρ + v ^ 2 ∧
      ρ ≤ Real.arcosh (Real.cosh ρ + v ^ 2) := by
  have h1 : 1 ≤ Real.cosh ρ + v ^ 2 := by nlinarith [Real.one_le_cosh ρ, sq_nonneg v]
  have hc := Real.cosh_arcosh h1
  refine ⟨hc, ?_⟩
  have hs := Real.arcosh_nonneg h1
  have : Real.cosh ρ ≤ Real.cosh (Real.arcosh (Real.cosh ρ + v ^ 2)) := by
    rw [hc]; nlinarith [sq_nonneg v]
  rw [Real.cosh_le_cosh, abs_of_nonneg hρ, abs_of_nonneg hs] at this
  exact this

theorem gc_mcKeanG_cosh_eq (T ρ v : ℝ) :
    gcMcKeanG T (max (Real.cosh ρ) 1 + v ^ 2) =
      2 * gcSdivSinh (Real.arcosh (Real.cosh ρ + v ^ 2)) *
        Real.exp (-(Real.arcosh (Real.cosh ρ + v ^ 2)) ^ 2 / (4 * T)) := by
  rw [max_eq_left (Real.one_le_cosh ρ)]
  rfl

/-- Pointwise Cauchy majorant of McKean's integrand. -/
theorem gc_mcKeanG_cosh_le {T ρ : ℝ} (hT : 0 < T) (hρ : 0 ≤ ρ) (v : ℝ) :
    gcMcKeanG T (max (Real.cosh ρ) 1 + v ^ 2) ≤
      2 * Real.exp (-ρ ^ 2 / (4 * T)) * gcSdivSinh ρ *
        (1 + (Real.sqrt (gcSdivSinh ρ / (2 * T)) * v) ^ 2)⁻¹ := by
  rw [gc_mcKeanG_cosh_eq]
  obtain ⟨hc, hρs⟩ := gc_arc_facts hρ v
  set s := Real.arcosh (Real.cosh ρ + v ^ 2)
  set a := gcSdivSinh s
  set b := gcSdivSinh ρ
  have ha : 0 < a := gc_sdivSinh_pos s
  have hb : 0 < b := gc_sdivSinh_pos ρ
  have hab : a ≤ b := gc_sdivSinh_anti hρ hρs
  have h1 := gc_cosh_sub_le hρ hρs
  rw [hc] at h1
  -- `2 a v² ≤ s² - ρ²`
  have hv : 2 * a * v ^ 2 ≤ s ^ 2 - ρ ^ 2 := by
    have : Real.cosh ρ + v ^ 2 - Real.cosh ρ = v ^ 2 := by ring
    rw [this] at h1; linarith
  set X := v ^ 2 / (2 * T) with hX
  have hX0 : 0 ≤ X := by positivity
  have hexp : Real.exp (-s ^ 2 / (4 * T)) ≤ Real.exp (-ρ ^ 2 / (4 * T)) * Real.exp (-(a * X)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have e1 : a * X = 2 * a * v ^ 2 / (4 * T) := by rw [hX]; field_simp; ring
    have e2 : -s ^ 2 / (4 * T) = -ρ ^ 2 / (4 * T) - (s ^ 2 - ρ ^ 2) / (4 * T) := by ring
    have e3 : 2 * a * v ^ 2 / (4 * T) ≤ (s ^ 2 - ρ ^ 2) / (4 * T) :=
      div_le_div_of_nonneg_right hv (by positivity)
    rw [e1]
    linarith
  have hinv : Real.exp (-(a * X)) ≤ (1 + a * X)⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ (by positivity) (by linarith [Real.add_one_le_exp (a * X)])
  have hmono : a * (1 + a * X)⁻¹ ≤ b * (1 + b * X)⁻¹ := by
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hsq : (Real.sqrt (b / (2 * T)) * v) ^ 2 = b * X := by
    rw [mul_pow, Real.sq_sqrt (by positivity), hX]; ring
  rw [hsq]
  have hE := Real.exp_pos (-ρ ^ 2 / (4 * T))
  calc 2 * a * Real.exp (-s ^ 2 / (4 * T))
      ≤ 2 * a * (Real.exp (-ρ ^ 2 / (4 * T)) * (1 + a * X)⁻¹) := by
        gcongr; exact hexp.trans (by gcongr)
    _ = 2 * Real.exp (-ρ ^ 2 / (4 * T)) * (a * (1 + a * X)⁻¹) := by ring
    _ ≤ 2 * Real.exp (-ρ ^ 2 / (4 * T)) * (b * (1 + b * X)⁻¹) := by gcongr
    _ = _ := by ring

/-- **Upper pole bound**: `K_T(cosh ρ) ≤ 2√π (4πT)⁻¹ e^{-ρ²/(4T)} √σ(ρ)`. -/
theorem gc_hypKernel_cosh_le {T ρ : ℝ} (hT : 0 < T) (hρ : 0 ≤ ρ) :
    gcHypKernel T (Real.cosh ρ) ≤ 2 * Real.sqrt π * gcPoleGauss T ρ := by
  set b := gcSdivSinh ρ
  have hb : 0 < b := gc_sdivSinh_pos ρ
  set β := Real.sqrt (b / (2 * T))
  have hβ : 0 < β := Real.sqrt_pos.2 (by positivity)
  set E := Real.exp (-ρ ^ 2 / (4 * T))
  have hE : 0 < E := Real.exp_pos _
  have hint : Integrable fun v : ℝ => 2 * E * b * (1 + (β * v) ^ 2)⁻¹ :=
    (integrable_inv_one_add_mul_sq hβ.ne').const_mul _
  have hI : ∫ v in Ioi (0 : ℝ), gcMcKeanG T (max (Real.cosh ρ) 1 + v ^ 2) ≤
      2 * E * b * (π / β) := by
    calc ∫ v in Ioi (0 : ℝ), gcMcKeanG T (max (Real.cosh ρ) 1 + v ^ 2)
        ≤ ∫ v in Ioi (0 : ℝ), 2 * E * b * (1 + (β * v) ^ 2)⁻¹ :=
          setIntegral_mono_on (gc_integrableOn_G hT _) hint.integrableOn measurableSet_Ioi
            fun v _ => gc_mcKeanG_cosh_le hT hρ v
      _ ≤ ∫ v, 2 * E * b * (1 + (β * v) ^ 2)⁻¹ :=
          setIntegral_le_integral hint (ae_of_all _ fun v => by positivity)
      _ = 2 * E * b * (π / β) := by
          rw [integral_const_mul, integral_univ_inv_one_add_mul_sq, abs_of_pos hβ]
  unfold gcHypKernel gcPoleGauss
  rw [gc_rpow_three_halves hT]
  have hp : 0 < Real.sqrt π := Real.sqrt_pos.2 Real.pi_pos
  have ht : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have hq : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  have hπ := Real.pi_pos
  have hβe : β = Real.sqrt b / (Real.sqrt 2 * Real.sqrt T) := by
    simp only [β]; rw [Real.sqrt_div hb.le, Real.sqrt_mul (by norm_num)]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hpp : Real.sqrt π * Real.sqrt π = π := Real.mul_self_sqrt hπ.le
  have htt : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hT.le
  have hqq : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt hb.le
  have hE1 : Real.exp (-T / 4) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hcoef : 0 ≤ Real.sqrt 2 * Real.exp (-T / 4) /
      (4 * π * T * (2 * Real.sqrt π * Real.sqrt T)) := by positivity
  calc Real.sqrt 2 * Real.exp (-T / 4) / (4 * π * T * (2 * Real.sqrt π * Real.sqrt T)) *
        ∫ v in Ioi (0 : ℝ), gcMcKeanG T (max (Real.cosh ρ) 1 + v ^ 2)
      ≤ Real.sqrt 2 * Real.exp (-T / 4) / (4 * π * T * (2 * Real.sqrt π * Real.sqrt T)) *
          (2 * E * b * (π / β)) := mul_le_mul_of_nonneg_left hI hcoef
    _ = Real.exp (-T / 4) * (2 * Real.sqrt π * ((4 * π * T)⁻¹ * E * Real.sqrt b)) := by
        rw [hβe]
        exact gc_alg_up _ _ _ _ _ _ _ _ _ h2 hpp htt hqq hp ht hq
    _ ≤ 1 * (2 * Real.sqrt π * ((4 * π * T)⁻¹ * E * Real.sqrt b)) := by
        gcongr
    _ = _ := one_mul _

/-- **Lower pole bound**: `gcPoleLow T₀ · (4πT)⁻¹ e^{-ρ²/(4T)} √σ(ρ) ≤ K_T(cosh ρ)` on
`0 < T ≤ T₀`. -/
theorem gc_hypKernel_cosh_ge {T₀ T ρ : ℝ} (hT : 0 < T) (hTT₀ : T ≤ T₀) (hρ : 0 ≤ ρ) :
    gcPoleLow T₀ * gcPoleGauss T ρ ≤ gcHypKernel T (Real.cosh ρ) := by
  set b := gcSdivSinh ρ
  have hb : 0 < b := gc_sdivSinh_pos ρ
  set E := Real.exp (-ρ ^ 2 / (4 * T))
  have hE : 0 < E := Real.exp_pos _
  have hT₀ : 0 < T₀ := hT.trans_le hTT₀
  set m := Real.sqrt (T / (b * (1 + 2 * T₀)))
  have hm : 0 < m := Real.sqrt_pos.2 (by positivity)
  have hmm : m ^ 2 = T / (b * (1 + 2 * T₀)) := Real.sq_sqrt (by positivity)
  have hbm : 2 * b * m ^ 2 ≤ 2 * T / (1 + 2 * T₀) := by
    rw [hmm]; apply le_of_eq; field_simp
  have hbm1 : 2 * T / (1 + 2 * T₀) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have hbm2 : 2 * T / (1 + 2 * T₀) ≤ 2 * T := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  set g₀ := 2 * b * Real.exp (-(3 / 2)) * E
  have hpt : ∀ v ∈ Ioc (0 : ℝ) m, g₀ ≤ gcMcKeanG T (max (Real.cosh ρ) 1 + v ^ 2) := by
    intro v hv
    rw [gc_mcKeanG_cosh_eq]
    obtain ⟨hc, hρs⟩ := gc_arc_facts hρ v
    set s := Real.arcosh (Real.cosh ρ + v ^ 2)
    have h2 := gc_le_cosh_sub hρ hρs
    rw [hc, show Real.cosh ρ + v ^ 2 - Real.cosh ρ = v ^ 2 by ring] at h2
    have hv2 : v ^ 2 ≤ m ^ 2 := by nlinarith [hv.1, hv.2]
    have hss : s ^ 2 - ρ ^ 2 ≤ 2 * T / (1 + 2 * T₀) := by nlinarith
    have hsr : s - ρ ≤ 1 := by nlinarith
    have hσ := gc_sdivSinh_le_mul_exp hρ hρs
    have hσ' : b * Real.exp (-1) ≤ gcSdivSinh s := by
      have h3 : Real.exp (s - ρ) ≤ Real.exp 1 := Real.exp_le_exp.2 hsr
      have h4 : b ≤ gcSdivSinh s * Real.exp 1 :=
        hσ.trans (mul_le_mul_of_nonneg_left h3 (gc_sdivSinh_pos s).le)
      have h5 : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (-1), Real.exp_pos 1]
    have hexp : E * Real.exp (-(1 / 2)) ≤ Real.exp (-s ^ 2 / (4 * T)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      rw [div_add' _ _ _ (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have he : Real.exp (-(3 / 2)) = Real.exp (-1) * Real.exp (-(1 / 2)) := by
      rw [← Real.exp_add]; norm_num
    have hs0 := gc_sdivSinh_pos s
    calc g₀ = 2 * (b * Real.exp (-1)) * (E * Real.exp (-(1 / 2))) := by
          simp only [g₀]; rw [he]; ring
      _ ≤ 2 * gcSdivSinh s * Real.exp (-s ^ 2 / (4 * T)) := by
          gcongr
  have hI : m * g₀ ≤ ∫ v in Ioi (0 : ℝ), gcMcKeanG T (max (Real.cosh ρ) 1 + v ^ 2) := by
    calc m * g₀ = ∫ _ in Ioc (0 : ℝ) m, g₀ := by
          rw [setIntegral_const, Real.volume_real_Ioc, sub_zero, max_eq_left hm.le,
            smul_eq_mul]
      _ ≤ ∫ v in Ioc (0 : ℝ) m, gcMcKeanG T (max (Real.cosh ρ) 1 + v ^ 2) :=
          setIntegral_mono_on (integrableOn_const (by simp))
            ((gc_integrableOn_G hT _).mono_set Ioc_subset_Ioi_self) measurableSet_Ioc hpt
      _ ≤ _ := setIntegral_mono_set (gc_integrableOn_G hT _)
          (ae_of_all _ fun v => (gc_mcKeanG_pos _ _).le)
          (Filter.Eventually.of_forall Ioc_subset_Ioi_self)
  unfold gcHypKernel gcPoleGauss gcPoleLow
  rw [gc_rpow_three_halves hT]
  have hp : 0 < Real.sqrt π := Real.sqrt_pos.2 Real.pi_pos
  have ht : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have hq : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  have hs0 : 0 < Real.sqrt (1 + 2 * T₀) := Real.sqrt_pos.2 (by positivity)
  have hπ := Real.pi_pos
  have hme : m = Real.sqrt T / (Real.sqrt b * Real.sqrt (1 + 2 * T₀)) := by
    simp only [m]; rw [Real.sqrt_div hT.le, Real.sqrt_mul hb.le]
  have h2 : 1 ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  have hpp : Real.sqrt π * Real.sqrt π = π := Real.mul_self_sqrt hπ.le
  have htt : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hT.le
  have hqq : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt hb.le
  have hE0 : Real.exp (-T₀ / 4) ≤ Real.exp (-T / 4) := Real.exp_le_exp.2 (by linarith)
  have hcoef : 0 ≤ Real.sqrt 2 * Real.exp (-T / 4) /
      (4 * π * T * (2 * Real.sqrt π * Real.sqrt T)) := by positivity
  calc Real.exp (-T₀ / 4) * Real.exp (-(3 / 2)) / (Real.sqrt (1 + 2 * T₀) * Real.sqrt π) *
        ((4 * π * T)⁻¹ * E * Real.sqrt b)
      ≤ Real.sqrt 2 * Real.exp (-T / 4) * Real.exp (-(3 / 2)) /
          (Real.sqrt (1 + 2 * T₀) * Real.sqrt π) * ((4 * π * T)⁻¹ * E * Real.sqrt b) := by
        gcongr
        nlinarith [Real.exp_pos (-T₀ / 4)]
    _ = Real.sqrt 2 * Real.exp (-T / 4) / (4 * π * T * (2 * Real.sqrt π * Real.sqrt T)) *
          (m * g₀) := by
        rw [hme]
        exact gc_alg_low _ _ _ _ _ _ _ _ _ _ _ hpp hqq hp ht hq hs0 hT
    _ ≤ _ := mul_le_mul_of_nonneg_left hI hcoef

end BlockBand.Diffusion
