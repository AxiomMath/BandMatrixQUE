module

public import BlockBand.Diffusion.Comparison.RadialGaussAngle
public import BlockBand.Diffusion.Comparison.RadialGaussIntegrals

/-!
# The two-sided radial Gaussian comparison

`gcHypRadialGaussCompare` proves `GcLbkHypRadialGaussCompare` with the constants
`c = gcPoleLow T₀ / 4 = e^{-T₀/4} e^{-3/2} / (4 √(1+2T₀) √π)`, `C = 4 √π e^{T₀/2}`.

(These are not the sharp constants `e^{-T₀/3}`, `1` of the Feynman–Kac sketch; the Prop asks
only for some positive constants.)

**Proof (deterministic, no Feynman–Kac).** Both kernels are angle integrals; by the symmetries
`φ ↦ 2π - φ`, `φ ↦ -φ` they are `4 ∫_{(0,π)}` of their integrands (`gc_hypRadial_eq`,
`gc_euclRadial_eq`). For `r, r' > 0` the hyperbolic half integral is rewritten by the angle
substitution `φ = Φ(ψ)`, which matches the hyperbolic distance at
angle `φ` with the planar distance `√y(ψ)` at angle `ψ`. Then the pole bounds
and the Jacobian bounds give pointwise in `ψ`

* `Φ' K ≥ gcPoleLow T₀ (4πT)⁻¹ √(σ(r)σ(r')) cos(ψ/2) e^{-y/(4T)}`, and the `cos(ψ/2)` weight
  costs at most a factor `4` (`gc_integral_cos_half_ge`);
* `Φ' K ≤ 2√π (4πT)⁻¹ √(σ(r)σ(r')) e^{-y/(4T)} e^{(ρ-δ)/2}`, and
  `e^{(ρ-δ)/2 - (y-δ²)/(8T)} ≤ e^{T/2}` (`(ρ-δ)² ≤ y - δ²`, AM–GM) leaves the Gaussian at
  doubled temperature, which costs at most a factor `2` (`gc_integral_doubling`).

For `r r' = 0` both integrands are constant in the angle and the pole bounds apply directly.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory Set Real

theorem gc_Ioo_eq_interval (f : ℝ → ℝ) :
    ∫ x in Ioo 0 π, f x = ∫ x in (0 : ℝ)..π, f x := by
  rw [intervalIntegral.integral_of_le Real.pi_pos.le, integral_Ioc_eq_integral_Ioo]

theorem gc_hypRadial_eq {T r r' : ℝ} (hT : 0 < T) (hr : 0 ≤ r) (hr' : 0 ≤ r') :
    gcHypRadial T (gcX r) (gcX r') = 4 * ∫ φ in Ioo 0 π, gcHypKernel T
      (Real.cosh r * Real.cosh r' - Real.sinh r * Real.sinh r' * Real.cos φ) := by
  unfold gcHypRadial
  simp only [gc_hypCos_X hr hr']
  have hc : Continuous fun φ => gcHypKernel T
      (Real.cosh r * Real.cosh r' - Real.sinh r * Real.sinh r' * Real.cos φ) :=
    (gc_hypKernel_continuous hT).comp (by fun_prop)
  rw [gc_integral_two_pi_eq hc (fun x => by simp only [Real.cos_two_pi_sub]),
    gc_Ioo_eq_interval]
  ring

theorem gc_euclRadial_eq (T r r' : ℝ) :
    gcEuclRadial T r r' = 4 * (4 * π * T)⁻¹ * Real.sqrt (gcSdivSinh r * gcSdivSinh r') *
      ∫ φ in Ioo 0 π, Real.exp (-(r ^ 2 + r' ^ 2 - 2 * r * r' * Real.cos φ) / (4 * T)) := by
  unfold gcEuclRadial
  rw [gc_integral_Ioo_neg_pi_eq (by fun_prop) (fun x => by simp only [Real.cos_neg])]
  ring

/-- The exponent bookkeeping of the upper bound. -/
theorem gc_exponent_le {T ρ δ y d2 : ℝ} (hT : 0 < T) (hδ : 0 ≤ δ) (hδρ : δ ≤ ρ)
    (hρ2 : ρ ^ 2 = y) (hδ2 : δ ^ 2 = d2) :
    -ρ ^ 2 / (4 * T) + (ρ - δ) / 2 ≤ T / 2 + (-d2 / (4 * T) - (y - d2) / (8 * T)) := by
  have ht : (ρ - δ) ^ 2 ≤ y - d2 := by rw [← hρ2, ← hδ2]; nlinarith
  have e : -ρ ^ 2 / (4 * T) + (ρ - δ) / 2 - (T / 2 + (-d2 / (4 * T) - (y - d2) / (8 * T))) =
      (4 * T * (ρ - δ) - 4 * T ^ 2 - (y - d2)) / (8 * T) := by
    rw [← hρ2]; field_simp; ring
  have : (4 * T * (ρ - δ) - 4 * T ^ 2 - (y - d2)) / (8 * T) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (ρ - δ - 2 * T)]) (by positivity)
  linarith

/-- Degenerate configuration `r r' = 0`: the integrands do not depend on the angle. -/
theorem gc_degenerate {r r' : ℝ} (hr : 0 ≤ r) (hr' : 0 ≤ r') (h0 : r = 0 ∨ r' = 0) (φ : ℝ) :
    Real.cosh r * Real.cosh r' - Real.sinh r * Real.sinh r' * Real.cos φ = Real.cosh (r + r') ∧
      r ^ 2 + r' ^ 2 - 2 * r * r' * Real.cos φ = (r + r') ^ 2 ∧
      gcSdivSinh r * gcSdivSinh r' = gcSdivSinh (r + r') := by
  rcases h0 with h | h <;> subst h <;> simp [gc_sdivSinh_zero]

theorem gc_integrableOn_Ioo_of_continuous {f : ℝ → ℝ} (hf : Continuous f) :
    IntegrableOn f (Ioo 0 π) :=
  (hf.integrableOn_Icc (a := 0) (b := π)).mono_set Ioo_subset_Icc_self

/-- **Lower half-angle bound.** -/
theorem gc_half_lower {T₀ T r r' : ℝ} (hT : 0 < T) (hTT₀ : T ≤ T₀) (hr : 0 ≤ r)
    (hr' : 0 ≤ r') :
    gcPoleLow T₀ * (4 * π * T)⁻¹ * Real.sqrt (gcSdivSinh r * gcSdivSinh r') *
        (1 / 4 * ∫ φ in Ioo 0 π, Real.exp (-(r ^ 2 + r' ^ 2 - 2 * r * r' * Real.cos φ) / (4 * T)))
      ≤ ∫ φ in Ioo 0 π, gcHypKernel T
        (Real.cosh r * Real.cosh r' - Real.sinh r * Real.sinh r' * Real.cos φ) := by
  have hlam := gc_poleLow_pos (hT.le.trans hTT₀)
  have hπ := Real.pi_pos
  have hk : 0 ≤ gcPoleLow T₀ * (4 * π * T)⁻¹ * Real.sqrt (gcSdivSinh r * gcSdivSinh r') := by
    positivity
  set e : ℝ → ℝ := fun φ => Real.exp (-(r ^ 2 + r' ^ 2 - 2 * r * r' * Real.cos φ) / (4 * T))
    with he
  have hec : Continuous e := by simp only [he]; fun_prop
  have hE0 : 0 ≤ ∫ φ in Ioo 0 π, e φ :=
    setIntegral_nonneg measurableSet_Ioo fun _ _ => (Real.exp_pos _).le
  have hKc : Continuous fun φ => gcHypKernel T
      (Real.cosh r * Real.cosh r' - Real.sinh r * Real.sinh r' * Real.cos φ) :=
    (gc_hypKernel_continuous hT).comp (by fun_prop)
  by_cases h0 : r = 0 ∨ r' = 0
  · -- degenerate case: pointwise
    calc gcPoleLow T₀ * (4 * π * T)⁻¹ * Real.sqrt (gcSdivSinh r * gcSdivSinh r') *
          (1 / 4 * ∫ φ in Ioo 0 π, e φ)
        ≤ gcPoleLow T₀ * (4 * π * T)⁻¹ * Real.sqrt (gcSdivSinh r * gcSdivSinh r') *
          ∫ φ in Ioo 0 π, e φ := by gcongr; linarith
      _ = ∫ φ in Ioo 0 π, gcPoleLow T₀ * (4 * π * T)⁻¹ *
          Real.sqrt (gcSdivSinh r * gcSdivSinh r') * e φ := (integral_const_mul _ _).symm
      _ ≤ _ := by
          refine setIntegral_mono_on (gc_integrableOn_Ioo_of_continuous (by fun_prop))
            (gc_integrableOn_Ioo_of_continuous hKc) measurableSet_Ioo fun φ _ => ?_
          obtain ⟨h1, h2, h3⟩ := gc_degenerate hr hr' h0 φ
          simp only [he]
          rw [h1, h2, h3]
          have := gc_hypKernel_cosh_ge (ρ := r + r') hT hTT₀ (by positivity)
          unfold gcPoleGauss at this
          linarith
  push Not at h0
  have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm h0.1)
  have hrp' : 0 < r' := lt_of_le_of_ne hr' (Ne.symm h0.2)
  rw [gc_half_hyp_eq hrp hrp']
  have hsym : ∀ x ∈ Icc 0 (π / 2), e (π - x) ≤ e x := by
    intro x hx
    simp only [he]
    apply Real.exp_le_exp.2
    have hc : 0 ≤ Real.cos x := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hx.1], hx.2⟩
    rw [Real.cos_pi_sub]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [mul_nonneg hr hr']
  have hcos := gc_integral_cos_half_ge hec (fun x => (Real.exp_pos _).le) hsym
  rw [← gc_Ioo_eq_interval, ← gc_Ioo_eq_interval] at hcos
  calc gcPoleLow T₀ * (4 * π * T)⁻¹ * Real.sqrt (gcSdivSinh r * gcSdivSinh r') *
        (1 / 4 * ∫ φ in Ioo 0 π, e φ)
      ≤ gcPoleLow T₀ * (4 * π * T)⁻¹ * Real.sqrt (gcSdivSinh r * gcSdivSinh r') *
          ∫ ψ in Ioo 0 π, Real.cos (ψ / 2) * e ψ := by gcongr
    _ = ∫ ψ in Ioo 0 π, gcPoleLow T₀ * (4 * π * T)⁻¹ *
          Real.sqrt (gcSdivSinh r * gcSdivSinh r') * (Real.cos (ψ / 2) * e ψ) :=
        (integral_const_mul _ _).symm
    _ ≤ _ := by
        refine setIntegral_mono_on (gc_integrableOn_Ioo_of_continuous (by fun_prop))
          (gc_half_hyp_integrableOn hT hrp hrp') measurableSet_Ioo fun ψ hψ => ?_
        have hD := gc_angPhiD_pos hrp hrp' hψ
        have hJ := gc_angJac_lower hrp hrp' hψ
        have hy0 : 0 ≤ gcAngY r r' ψ :=
          le_trans (sq_nonneg _) (gc_angY_bounds hr hr' ψ).1
        have hK := gc_hypKernel_cosh_ge (ρ := Real.sqrt (gcAngY r r' ψ)) hT hTT₀
          (Real.sqrt_nonneg _)
        unfold gcPoleGauss at hK
        rw [Real.sq_sqrt hy0] at hK
        have hey : e ψ = Real.exp (-gcAngY r r' ψ / (4 * T)) := rfl
        rw [hey]
        have hE := Real.exp_pos (-gcAngY r r' ψ / (4 * T))
        have hA : 0 ≤ gcPoleLow T₀ * (4 * π * T)⁻¹ * Real.exp (-gcAngY r r' ψ / (4 * T)) := by
          positivity
        calc gcPoleLow T₀ * (4 * π * T)⁻¹ * Real.sqrt (gcSdivSinh r * gcSdivSinh r') *
              (Real.cos (ψ / 2) * Real.exp (-gcAngY r r' ψ / (4 * T)))
            = gcPoleLow T₀ * (4 * π * T)⁻¹ * Real.exp (-gcAngY r r' ψ / (4 * T)) *
              (Real.sqrt (gcSdivSinh r * gcSdivSinh r') * Real.cos (ψ / 2)) := by ring
          _ ≤ gcPoleLow T₀ * (4 * π * T)⁻¹ * Real.exp (-gcAngY r r' ψ / (4 * T)) *
              (gcAngPhiD r r' ψ * Real.sqrt (gcSdivSinh (Real.sqrt (gcAngY r r' ψ)))) := by
              gcongr
          _ = gcAngPhiD r r' ψ * (gcPoleLow T₀ * ((4 * π * T)⁻¹ *
              Real.exp (-gcAngY r r' ψ / (4 * T)) *
                Real.sqrt (gcSdivSinh (Real.sqrt (gcAngY r r' ψ))))) := by ring
          _ ≤ _ := by gcongr

/-- **Upper half-angle bound.** -/
theorem gc_half_upper {T r r' : ℝ} (hT : 0 < T) (hr : 0 ≤ r) (hr' : 0 ≤ r') :
    ∫ φ in Ioo 0 π, gcHypKernel T
        (Real.cosh r * Real.cosh r' - Real.sinh r * Real.sinh r' * Real.cos φ) ≤
      2 * Real.sqrt π * (4 * π * T)⁻¹ * Real.sqrt (gcSdivSinh r * gcSdivSinh r') *
        Real.exp (T / 2) *
        (2 * ∫ φ in Ioo 0 π, Real.exp (-(r ^ 2 + r' ^ 2 - 2 * r * r' * Real.cos φ) / (4 * T))) := by
  have hπ := Real.pi_pos
  set M := 2 * Real.sqrt π * (4 * π * T)⁻¹ * Real.sqrt (gcSdivSinh r * gcSdivSinh r') with hM
  have hM0 : 0 ≤ M := by positivity
  set e : ℝ → ℝ := fun φ => Real.exp (-(r ^ 2 + r' ^ 2 - 2 * r * r' * Real.cos φ) / (4 * T))
    with he
  have hE0 : 0 ≤ ∫ φ in Ioo 0 π, e φ :=
    setIntegral_nonneg measurableSet_Ioo fun _ _ => (Real.exp_pos _).le
  have hKc : Continuous fun φ => gcHypKernel T
      (Real.cosh r * Real.cosh r' - Real.sinh r * Real.sinh r' * Real.cos φ) :=
    (gc_hypKernel_continuous hT).comp (by fun_prop)
  have hT2 : 1 ≤ Real.exp (T / 2) := Real.one_le_exp (by positivity)
  by_cases h0 : r = 0 ∨ r' = 0
  · calc ∫ φ in Ioo 0 π, gcHypKernel T
          (Real.cosh r * Real.cosh r' - Real.sinh r * Real.sinh r' * Real.cos φ)
        ≤ ∫ φ in Ioo 0 π, M * e φ := by
          refine setIntegral_mono_on (gc_integrableOn_Ioo_of_continuous hKc)
            (gc_integrableOn_Ioo_of_continuous (by fun_prop)) measurableSet_Ioo fun φ _ => ?_
          obtain ⟨h1, h2, h3⟩ := gc_degenerate hr hr' h0 φ
          simp only [he, hM]
          rw [h1, h2, h3]
          have := gc_hypKernel_cosh_le (ρ := r + r') hT (by positivity)
          unfold gcPoleGauss at this
          linarith
      _ = M * ∫ φ in Ioo 0 π, e φ := integral_const_mul _ _
      _ ≤ M * Real.exp (T / 2) * (2 * ∫ φ in Ioo 0 π, e φ) := by
          have : M * ∫ φ in Ioo 0 π, e φ ≤ M * (Real.exp (T / 2) * (2 * ∫ φ in Ioo 0 π, e φ)) :=
            mul_le_mul_of_nonneg_left (by nlinarith) hM0
          linarith
  push Not at h0
  have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm h0.1)
  have hrp' : 0 < r' := lt_of_le_of_ne hr' (Ne.symm h0.2)
  rw [gc_half_hyp_eq hrp hrp']
  set μ := r * r' / (4 * T) with hμ
  have hμ0 : 0 ≤ μ := by positivity
  set d := Real.exp (-(r - r') ^ 2 / (4 * T))
  have hd0 : 0 < d := Real.exp_pos _
  -- `e = d · e^{-2μ(1 - cos)}`
  have he2 : ∀ ψ, e ψ = d * Real.exp (-(2 * μ * (1 - Real.cos ψ))) := by
    intro ψ
    simp only [he, d, hμ]
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  have hdbl := gc_integral_doubling hμ0
  rw [← gc_Ioo_eq_interval, ← gc_Ioo_eq_interval] at hdbl
  have hEeq : ∫ φ in Ioo 0 π, e φ =
      d * ∫ ψ in Ioo 0 π, Real.exp (-(2 * μ * (1 - Real.cos ψ))) := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioo fun ψ _ => he2 ψ
  calc ∫ ψ in Ioo 0 π, gcAngPhiD r r' ψ * gcHypKernel T (Real.cosh (Real.sqrt (gcAngY r r' ψ)))
      ≤ ∫ ψ in Ioo 0 π, M * Real.exp (T / 2) * d * Real.exp (-(μ * (1 - Real.cos ψ))) := by
        refine setIntegral_mono_on (gc_half_hyp_integrableOn hT hrp hrp')
          (gc_integrableOn_Ioo_of_continuous (by fun_prop)) measurableSet_Ioo fun ψ hψ => ?_
        have hD := gc_angPhiD_pos hrp hrp' hψ
        have hJ := gc_angJac_upper hrp hrp' hψ
        have hy0 : 0 ≤ gcAngY r r' ψ :=
          le_trans (sq_nonneg _) (gc_angY_bounds hr hr' ψ).1
        set ρ := Real.sqrt (gcAngY r r' ψ)
        have hK := gc_hypKernel_cosh_le (ρ := ρ) hT (Real.sqrt_nonneg _)
        unfold gcPoleGauss at hK
        obtain ⟨hδρ, _⟩ := gc_ang_sqrt_bounds hr hr' ψ
        have hexp : Real.exp (-ρ ^ 2 / (4 * T)) * Real.exp ((ρ - |r - r'|) / 2) ≤
            Real.exp (T / 2) * d * Real.exp (-(μ * (1 - Real.cos ψ))) := by
          rw [← Real.exp_add, mul_assoc, ← Real.exp_add, ← Real.exp_add]
          apply Real.exp_le_exp.2
          have h := gc_exponent_le hT (abs_nonneg (r - r')) hδρ (Real.sq_sqrt hy0) (sq_abs _)
          have e1 : -(μ * (1 - Real.cos ψ)) = -((gcAngY r r' ψ - (r - r') ^ 2) / (8 * T)) := by
            rw [gc_angY_sub, hμ]; field_simp; ring
          rw [e1]
          linarith
        have hE := Real.exp_pos (-ρ ^ 2 / (4 * T))
        calc gcAngPhiD r r' ψ * gcHypKernel T (Real.cosh ρ)
            ≤ gcAngPhiD r r' ψ * (2 * Real.sqrt π * ((4 * π * T)⁻¹ *
                Real.exp (-ρ ^ 2 / (4 * T)) * Real.sqrt (gcSdivSinh ρ))) := by gcongr
          _ = 2 * Real.sqrt π * (4 * π * T)⁻¹ * Real.exp (-ρ ^ 2 / (4 * T)) *
                (gcAngPhiD r r' ψ * Real.sqrt (gcSdivSinh ρ)) := by ring
          _ ≤ 2 * Real.sqrt π * (4 * π * T)⁻¹ * Real.exp (-ρ ^ 2 / (4 * T)) *
                (Real.sqrt (gcSdivSinh r * gcSdivSinh r') *
                  Real.exp ((ρ - |r - r'|) / 2)) := by gcongr
          _ = M * (Real.exp (-ρ ^ 2 / (4 * T)) * Real.exp ((ρ - |r - r'|) / 2)) := by
                simp only [hM]; ring
          _ ≤ M * (Real.exp (T / 2) * d * Real.exp (-(μ * (1 - Real.cos ψ)))) := by gcongr
          _ = _ := by ring
    _ = M * Real.exp (T / 2) * d * ∫ ψ in Ioo 0 π, Real.exp (-(μ * (1 - Real.cos ψ))) :=
        integral_const_mul _ _
    _ ≤ M * Real.exp (T / 2) * d *
          (2 * ∫ ψ in Ioo 0 π, Real.exp (-(2 * μ * (1 - Real.cos ψ)))) := by gcongr
    _ = M * Real.exp (T / 2) * (2 * ∫ φ in Ioo 0 π, e φ) := by rw [hEeq]; ring

/-- **The two-sided radial Gaussian comparison**, hypothesis-free
(`c = gcPoleLow T₀ / 4`, `C = 4√π e^{T₀/2}`). -/
theorem gcHypRadialGaussCompare : GcLbkHypRadialGaussCompare := by
  intro T₀ hT₀
  have hlam := gc_poleLow_pos hT₀.le
  refine ⟨gcPoleLow T₀ / 4, by positivity, 4 * Real.sqrt π * Real.exp (T₀ / 2),
    by have := Real.sqrt_pos.2 Real.pi_pos; positivity, ?_⟩
  rintro T ⟨hT, hTT₀⟩ r r' hr hr'
  have hπ := Real.pi_pos
  rw [gc_hypRadial_eq hT hr hr', gc_euclRadial_eq]
  have hL := gc_half_lower hT hTT₀ hr hr'
  have hU := gc_half_upper hT hr hr'
  set Eh := ∫ φ in Ioo 0 π, Real.exp (-(r ^ 2 + r' ^ 2 - 2 * r * r' * Real.cos φ) / (4 * T))
  set Hh := ∫ φ in Ioo 0 π, gcHypKernel T
    (Real.cosh r * Real.cosh r' - Real.sinh r * Real.sinh r' * Real.cos φ)
  have hEh : 0 ≤ Eh := setIntegral_nonneg measurableSet_Ioo fun _ _ => (Real.exp_pos _).le
  set k := (4 * π * T)⁻¹ * Real.sqrt (gcSdivSinh r * gcSdivSinh r')
  have hk : 0 ≤ k := by positivity
  have hex : Real.exp (T / 2) ≤ Real.exp (T₀ / 2) := Real.exp_le_exp.2 (by linarith)
  constructor
  · calc gcPoleLow T₀ / 4 * (4 * (4 * π * T)⁻¹ * Real.sqrt (gcSdivSinh r * gcSdivSinh r') * Eh)
        = 4 * (gcPoleLow T₀ * (4 * π * T)⁻¹ * Real.sqrt (gcSdivSinh r * gcSdivSinh r') *
            (1 / 4 * Eh)) := by ring
      _ ≤ 4 * Hh := by gcongr
  · have hs := Real.sqrt_nonneg π
    calc 4 * Hh ≤ 4 * (2 * Real.sqrt π * (4 * π * T)⁻¹ *
          Real.sqrt (gcSdivSinh r * gcSdivSinh r') * Real.exp (T / 2) * (2 * Eh)) := by gcongr
      _ = 16 * Real.sqrt π * k * Eh * Real.exp (T / 2) := by simp only [k]; ring
      _ ≤ 16 * Real.sqrt π * k * Eh * Real.exp (T₀ / 2) := by gcongr
      _ = _ := by simp only [k]; ring

end BlockBand.Diffusion
