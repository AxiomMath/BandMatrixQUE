module

public import BlockBand.Diffusion.Kernel.McKeanMoments

/-!
# Continuity of `P_t f` up to the boundary

We prove decay and continuity estimates for McKean's kernel and deduce that the semigroup `P_t f`
of the radial factor `pX` is continuous up to `t = 0` and up to the boundary `x = 0`.

* `mk_hypKernel_le_cube`: `K_T(c) ≤ A_T π e^{16T} c^{-3}` (`c ≥ 1`), hence the integrable
  majorant `pX t x x' ≤ 4π² A_T e^{16T} (2(1+2x))³ (1+2x')^{-3}` (`mk_hypRadial_le_decay`,
  `x, x' ≥ 0`, `T = D₀t/2`);
* `mk_hypKernel_continuousAt`: `(T, c) ↦ K_T(c)` is jointly continuous at every `T > 0`;
  `mk_kernelX_continuousAt`: `(t, x) ↦ pX t x x'` is continuous at every `t > 0` (`x ∈ ℝ`,
  fixed `x' ≥ 0`);
* `mk_kernelX_integral_continuousOn`: for bounded measurable `f`,
  `(t, x) ↦ ∫_{[0,∞)} pX t x x' f(x') dx'` is continuous on `(0, ∞) × [0, ∞)`;
* `mk_semigroupX_continuousOn`: for bounded continuous `f`, the map `mkSemigroupX D0 f`
  (`= P_t f(x)` for `t > 0`, `= f(x)` for `t ≤ 0`) is continuous on `[0, ∞) × [0, ∞)`
  (uses the approximate identity `mk_kernelX_approxId`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory Filter Topology Set Real
open scoped ENNReal

theorem mk_mcKeanG_le_pow {T w : ℝ} (hT : 0 < T) (hw : 1 ≤ w) :
    mkMcKeanG T w ≤ 2 * Real.exp (16 * T) * (w ^ 4)⁻¹ := by
  have hw0 : 0 < w := by linarith
  set s := Real.arcosh w
  have hs : Real.exp (-s ^ 2 / (4 * T)) ≤ Real.exp (16 * T) * (w ^ 4)⁻¹ := by
    have hes : w ≤ Real.exp s := by
      rw [Real.exp_arcosh hw]; linarith [Real.sqrt_nonneg (w ^ 2 - 1)]
    have h4 : (w ^ 4)⁻¹ ≥ Real.exp (-(4 * s)) := by
      rw [Real.exp_neg, ge_iff_le]
      apply inv_anti₀ (by positivity)
      rw [show 4 * s = (4 : ℕ) * s by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ hw0.le hes 4
    have hq : -s ^ 2 / (4 * T) ≤ 16 * T + -(4 * s) := by
      have : 0 ≤ (s - 8 * T) ^ 2 / (4 * T) := by positivity
      have : (s - 8 * T) ^ 2 / (4 * T) = s ^ 2 / (4 * T) - 4 * s + 16 * T := by
        field_simp; ring
      rw [neg_div]; linarith
    calc Real.exp (-s ^ 2 / (4 * T)) ≤ Real.exp (16 * T + -(4 * s)) := Real.exp_le_exp.2 hq
      _ = Real.exp (16 * T) * Real.exp (-(4 * s)) := Real.exp_add _ _
      _ ≤ _ := by gcongr
  have hσ0 := (mk_sdivSinh_pos s).le
  have hσ1 := mk_sdivSinh_le_one s
  unfold mkMcKeanG
  calc 2 * mkSdivSinh s * Real.exp (-s ^ 2 / (4 * T))
      ≤ 2 * 1 * (Real.exp (16 * T) * (w ^ 4)⁻¹) := by gcongr
    _ = _ := by ring

/-- Cubic decay of McKean's kernel: `K_T(c) ≤ A_T π e^{16T} c^{-3}` for `c ≥ 1`. -/
theorem mk_hypKernel_le_cube {T c : ℝ} (hT : 0 < T) (hc : 1 ≤ c) :
    mkHypKernel T c ≤ mkA T * (π * Real.exp (16 * T) * (c ^ 3)⁻¹) := by
  rw [mk_hypKernel_eq_mkA, max_eq_left hc]
  refine mul_le_mul_of_nonneg_left ?_ (mk_mkA_pos hT).le
  have hc0 : 0 < c := by linarith
  have hb : IntegrableOn (fun v : ℝ => 2 * Real.exp (16 * T) * (c ^ 3)⁻¹ * (1 + v ^ 2)⁻¹)
      (Ioi 0) :=
    (integrable_inv_one_add_sq.const_mul (2 * Real.exp (16 * T) * (c ^ 3)⁻¹)).integrableOn
  have hG := mk_integrableOn_G hT c
  rw [max_eq_left hc] at hG
  calc ∫ v in Ioi (0 : ℝ), mkMcKeanG T (c + v ^ 2)
      ≤ ∫ v in Ioi (0 : ℝ), 2 * Real.exp (16 * T) * (c ^ 3)⁻¹ * (1 + v ^ 2)⁻¹ := by
        refine setIntegral_mono_on hG hb measurableSet_Ioi fun v _ => ?_
        have hinv : ((c + v ^ 2) ^ 4)⁻¹ ≤ (c ^ 3)⁻¹ * (1 + v ^ 2)⁻¹ := by
          rw [← mul_inv]
          apply inv_anti₀ (by positivity)
          have h1 : c ^ 3 * (1 + v ^ 2) ≤ c ^ 3 * (c + v ^ 2) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          have h2 : c ^ 3 ≤ (c + v ^ 2) ^ 3 :=
            pow_le_pow_left₀ hc0.le (by nlinarith [sq_nonneg v]) 3
          nlinarith [mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ c + v ^ 2)]
        calc mkMcKeanG T (c + v ^ 2) ≤ 2 * Real.exp (16 * T) * ((c + v ^ 2) ^ 4)⁻¹ :=
              mk_mcKeanG_le_pow hT (by nlinarith [sq_nonneg v])
          _ ≤ 2 * Real.exp (16 * T) * ((c ^ 3)⁻¹ * (1 + v ^ 2)⁻¹) :=
              mul_le_mul_of_nonneg_left hinv (by positivity)
          _ = _ := by ring
    _ = π * Real.exp (16 * T) * (c ^ 3)⁻¹ := by
        rw [integral_const_mul, integral_Ioi_inv_one_add_sq, Real.arctan_zero]; ring

/-- An integrable majorant of `pX` in `x'`: `pX ≤ 4π² A_T e^{16T} (2(1+2x))³ (1+2x')⁻³`. -/
theorem mk_hypRadial_le_decay {T x x' : ℝ} (hT : 0 < T) (hx : 0 ≤ x) (hx' : 0 ≤ x') :
    mkHypRadial T x x' ≤
      4 * π ^ 2 * mkA T * Real.exp (16 * T) * (2 * (1 + 2 * x)) ^ 3 * ((1 + 2 * x') ^ 3)⁻¹ := by
  rw [mk_hypRadial_eq_Ioo]
  set B := mkA T * (π * Real.exp (16 * T) * ((1 + 2 * x') ^ 3)⁻¹ * (2 * (1 + 2 * x)) ^ 3)
  have hpt : ∀ θ, mkHypKernel T (mkHypCos x x' θ) ≤ B := fun θ => by
    have h1 := (mk_hypCos_sub_one hx hx' θ).1
    have hb := mk_b_le_hypCos hx hx' θ
    refine (mk_hypKernel_le_cube hT h1).trans (mul_le_mul_of_nonneg_left ?_ (mk_mkA_pos hT).le)
    have hb0 : 0 < 1 + 2 * x' := by linarith
    have hc0 : 0 < mkHypCos x x' θ := by linarith
    have hinv : (mkHypCos x x' θ ^ 3)⁻¹ ≤ ((1 + 2 * x') ^ 3)⁻¹ * (2 * (1 + 2 * x)) ^ 3 := by
      rw [← div_eq_inv_mul, ← one_div, ← div_pow, ← one_pow 3, ← div_pow, one_pow]
      apply pow_le_pow_left₀ (by positivity)
      rw [div_le_div_iff₀ hc0 hb0]
      linarith
    calc π * Real.exp (16 * T) * (mkHypCos x x' θ ^ 3)⁻¹
        ≤ π * Real.exp (16 * T) * (((1 + 2 * x') ^ 3)⁻¹ * (2 * (1 + 2 * x)) ^ 3) :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = _ := by ring
  have hI : ∫ θ in Ioo (-π) π, mkHypKernel T (mkHypCos x x' θ) ≤ ∫ θ in Ioo (-π) π, B :=
    setIntegral_mono_on
      (((mk_hypKernel_comp_continuous hT x x').integrableOn_Icc).mono_set Ioo_subset_Icc_self)
      ((continuous_const : Continuous fun _ : ℝ => B).integrableOn_Icc.mono_set
        Ioo_subset_Icc_self) measurableSet_Ioo fun θ _ => hpt θ
  rw [setIntegral_const, Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos]),
    smul_eq_mul] at hI
  have : (π - -π) * B = 2 * π * B := by ring
  calc 2 * ∫ θ in Ioo (-π) π, mkHypKernel T (mkHypCos x x' θ) ≤ 2 * ((π - -π) * B) := by linarith
    _ = _ := by simp only [B]; ring

theorem mk_mkA_continuousOn : ContinuousOn mkA (Ioi 0) := by
  unfold mkA
  refine ContinuousOn.div (by fun_prop) ?_ ?_
  · exact fun T hT => (ContinuousAt.rpow_const (by fun_prop)
      (Or.inl (by have : 0 < T := hT; positivity))).continuousWithinAt
  · intro T hT; have : 0 < T := hT; positivity

/-- Joint continuity of McKean's kernel in `(T, c)` for `T > 0`. -/
theorem mk_hypKernel_continuousAt {T₀ c₀ : ℝ} (hT₀ : 0 < T₀) :
    ContinuousAt (fun p : ℝ × ℝ => mkHypKernel p.1 p.2) (T₀, c₀) := by
  simp_rw [mk_hypKernel_eq_mkA]
  refine ContinuousAt.mul (ContinuousAt.comp (g := mkA) (f := fun p : ℝ × ℝ => p.1)
    (x := (T₀, c₀)) (mk_mkA_continuousOn.continuousAt (Ioi_mem_nhds hT₀))
    continuous_fst.continuousAt) ?_
  have hev : ∀ᶠ p : ℝ × ℝ in 𝓝 (T₀, c₀), p.1 ∈ Ioo (T₀ / 2) (2 * T₀) :=
    continuous_fst.continuousAt.preimage_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith))
  refine continuousAt_of_dominated (bound := fun v => 2 * Real.exp (2 * T₀) * (1 + v ^ 2)⁻¹)
    ?_ ?_ (integrable_inv_one_add_sq.const_mul _).integrableOn ?_
  · filter_upwards [hev] with p hp
    exact ((mk_G_continuous p.1).comp (continuous_const.prodMk continuous_id :
      Continuous fun v : ℝ => (p.2, v))).aestronglyMeasurable
  · filter_upwards [hev] with p hp
    refine ae_of_all _ fun v => (mk_G_le (by linarith [hp.1]) p.2 v).trans ?_
    gcongr
    linarith [hp.2]
  · refine ae_of_all _ fun v => ?_
    have harc : Continuous fun p : ℝ × ℝ => Real.arcosh (max p.2 1 + v ^ 2) :=
      mk_arc_continuous.comp (continuous_snd.prodMk continuous_const)
    unfold mkMcKeanG
    refine ((continuous_const.mul (mk_sdivSinh_continuous.comp harc)).continuousAt).mul ?_
    refine Real.continuous_exp.continuousAt.comp ?_
    exact ((harc.pow 2).neg.continuousAt).div (continuous_const.mul continuous_fst).continuousAt
      (by simp; linarith)

theorem mk_hypKernel_continuousOn :
    ContinuousOn (fun p : ℝ × ℝ => mkHypKernel p.1 p.2) (Ioi 0 ×ˢ univ) :=
  fun p hp => (mk_hypKernel_continuousAt (c₀ := p.2) hp.1).continuousWithinAt

/-- Continuity of `(T, x) ↦ pX` (radial form) at `T₀ > 0`, for fixed `x'`. -/
theorem mk_hypRadial_continuousAt {T₀ x₀ : ℝ} (hT₀ : 0 < T₀) (x' : ℝ) :
    ContinuousAt (fun p : ℝ × ℝ => mkHypRadial p.1 p.2 x') (T₀, x₀) := by
  set K' : ℝ × ℝ → ℝ := fun q => mkHypKernel (max q.1 (T₀ / 2)) q.2
  have hK' : Continuous K' := by
    have h := mk_hypKernel_continuousOn.comp_continuous
      (f := fun q : ℝ × ℝ => (max q.1 (T₀ / 2), q.2)) (by fun_prop)
      (fun q => ⟨lt_of_lt_of_le (half_pos hT₀) (le_max_right _ _), mem_univ _⟩)
    exact h
  have hc : Continuous fun q : (ℝ × ℝ) × ℝ => K' (q.1.1, mkHypCos q.1.2 x' q.2) :=
    hK'.comp (by unfold mkHypCos; fun_prop)
  have hcont : Continuous fun p : ℝ × ℝ => 2 * ∫ φ in (0 : ℝ)..(2 * π),
      K' (p.1, mkHypCos p.2 x' φ) :=
    continuous_const.mul (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (p : ℝ × ℝ) (φ : ℝ) => K' (p.1, mkHypCos p.2 x' φ)) hc continuous_const)
  refine hcont.continuousAt.congr ?_
  have hev : ∀ᶠ p : ℝ × ℝ in 𝓝 (T₀, x₀), T₀ / 2 < p.1 :=
    continuous_fst.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (by linarith))
  filter_upwards [hev] with p hp
  simp only [K', mkHypRadial, max_eq_left hp.le]

theorem mk_kernelX_continuousAt {D0 t₀ x₀ x' : ℝ} (hD0 : 0 < D0) (ht₀ : 0 < t₀) (hx' : 0 ≤ x') :
    ContinuousAt (fun p : ℝ × ℝ => mkKernelX D0 p.1 p.2 x') (t₀, x₀) := by
  have h := (mk_hypRadial_continuousAt (x₀ := x₀) (by positivity : 0 < D0 * t₀ / 2) x').comp
    (f := fun p : ℝ × ℝ => (D0 * p.1 / 2, p.2)) (x := (t₀, x₀)) (by fun_prop)
  refine h.congr ?_
  have hev : ∀ᶠ p : ℝ × ℝ in 𝓝 (t₀, x₀), 0 < p.1 :=
    continuous_fst.continuousAt.preimage_mem_nhds (Ioi_mem_nhds ht₀)
  filter_upwards [hev] with p hp
  simp [Function.comp_apply, mk_kernelX_eq hp hx']

theorem mk_inv_cube_le {y : ℝ} (hy : 0 ≤ y) : ((1 + 2 * y) ^ 3)⁻¹ ≤ (1 + y ^ 2)⁻¹ :=
  inv_anti₀ (by positivity) (by nlinarith [sq_nonneg y, pow_nonneg hy 3])

/-- **Continuity of the semigroup.** For `D₀ > 0` and a bounded measurable `f`,
`u(t, x) = ∫_{[0,∞)} pX t x x' f(x') dx'` is continuous on `(0, ∞) × [0, ∞)`. -/
theorem mk_kernelX_integral_continuousOn {D0 : ℝ} (hD0 : 0 < D0) {f : ℝ → ℝ}
    (hf : Measurable f) {M : ℝ} (hM : ∀ y, |f y| ≤ M) :
    ContinuousOn (fun p : ℝ × ℝ => ∫ x' in Ici (0 : ℝ), mkKernelX D0 p.1 p.2 x' * f x')
      (Ioi 0 ×ˢ Ici 0) := by
  rintro ⟨t₀, x₀⟩ ⟨ht₀, hx₀⟩
  have ht₀' : 0 < t₀ := ht₀
  have hx₀' : 0 ≤ x₀ := hx₀
  set U : Set (ℝ × ℝ) := Ioo (t₀ / 2) (2 * t₀) ×ˢ Iio (x₀ + 1)
  set S' : Set (ℝ × ℝ) := Icc (t₀ / 2) (2 * t₀) ×ˢ Icc 0 (x₀ + 1)
  have hU : U ∈ 𝓝 (t₀, x₀) :=
    (isOpen_Ioo.prod isOpen_Iio).mem_nhds ⟨⟨by linarith, by linarith⟩, by
      show x₀ < x₀ + 1; linarith⟩
  have hsub : Ioi 0 ×ˢ Ici 0 ∩ U ⊆ S' := fun p hp =>
    ⟨⟨hp.2.1.1.le, hp.2.1.2.le⟩, ⟨hp.1.2, (show p.2 < x₀ + 1 from hp.2.2).le⟩⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  -- a uniform bound for `mkA` on the time window
  have hTw : Icc (D0 * (t₀ / 2) / 2) (D0 * (2 * t₀) / 2) ⊆ Ioi 0 := fun T hT =>
    lt_of_lt_of_le (by positivity) hT.1
  obtain ⟨Am, hAm⟩ := (isCompact_Icc).exists_bound_of_continuousOn
    (mk_mkA_continuousOn.mono hTw)
  set C := M * (4 * π ^ 2 * Am * Real.exp (16 * (D0 * (2 * t₀) / 2)) *
    (2 * (1 + 2 * (x₀ + 1))) ^ 3)
  have hcont : ContinuousOn (fun p : ℝ × ℝ => ∫ x' in Ici (0 : ℝ), mkKernelX D0 p.1 p.2 x' * f x')
      S' := by
    refine continuousOn_of_dominated (bound := fun x' => C * (1 + x' ^ 2)⁻¹) ?_ ?_
      ((integrable_inv_one_add_sq.const_mul C).integrableOn) ?_
    · intro p _
      exact ((mk_kernelX_measurable_snd D0 p.1 p.2).mul hf).aestronglyMeasurable
    · intro p hp
      refine (ae_restrict_iff' measurableSet_Ici).2 (ae_of_all _ fun x' hx' => ?_)
      have hx'0 : 0 ≤ x' := hx'
      have hp1 : 0 < p.1 := lt_of_lt_of_le (by positivity) hp.1.1
      have hT : 0 < D0 * p.1 / 2 := by positivity
      have hTI : D0 * p.1 / 2 ∈ Icc (D0 * (t₀ / 2) / 2) (D0 * (2 * t₀) / 2) :=
        ⟨by have := hp.1.1; gcongr, by have := hp.1.2; gcongr⟩
      have hA : mkA (D0 * p.1 / 2) ≤ Am := (le_abs_self _).trans (by
        simpa [Real.norm_eq_abs] using hAm _ hTI)
      have hx2 : p.2 ≤ x₀ + 1 := hp.2.2
      have hx20 : 0 ≤ p.2 := hp.2.1
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mk_kernelX_nonneg hD0 _ _ _),
        mk_kernelX_eq hp1 hx'0]
      have hdec := mk_hypRadial_le_decay hT hx20 hx'0
      have hI := mk_inv_cube_le hx'0
      have hR0 := mk_hypRadial_nonneg hT p.2 x'
      have hE : Real.exp (16 * (D0 * p.1 / 2)) ≤ Real.exp (16 * (D0 * (2 * t₀) / 2)) :=
        Real.exp_le_exp.2 (by have := hTI.2; linarith)
      have hX : (2 * (1 + 2 * p.2)) ^ 3 ≤ (2 * (1 + 2 * (x₀ + 1))) ^ 3 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 3
      have hA0 : 0 ≤ mkA (D0 * p.1 / 2) := (mk_mkA_pos hT).le
      have hR : mkHypRadial (D0 * p.1 / 2) p.2 x' ≤
          4 * π ^ 2 * Am * Real.exp (16 * (D0 * (2 * t₀) / 2)) *
            (2 * (1 + 2 * (x₀ + 1))) ^ 3 * (1 + x' ^ 2)⁻¹ := by
        refine hdec.trans ?_
        have hpi : 0 ≤ 4 * π ^ 2 := by positivity
        have hAm0 : 0 ≤ Am := hA0.trans hA
        have hK0 : 0 ≤ 4 * π ^ 2 * Am * Real.exp (16 * (D0 * (2 * t₀) / 2)) *
            (2 * (1 + 2 * (x₀ + 1))) ^ 3 :=
          mul_nonneg (mul_nonneg (mul_nonneg hpi hAm0) (Real.exp_pos _).le)
            (pow_nonneg (by linarith) 3)
        have hinv0 : 0 ≤ ((1 + 2 * x') ^ 3)⁻¹ := by positivity
        calc 4 * π ^ 2 * mkA (D0 * p.1 / 2) * Real.exp (16 * (D0 * p.1 / 2)) *
              (2 * (1 + 2 * p.2)) ^ 3 * ((1 + 2 * x') ^ 3)⁻¹
            ≤ 4 * π ^ 2 * Am * Real.exp (16 * (D0 * (2 * t₀) / 2)) *
              (2 * (1 + 2 * (x₀ + 1))) ^ 3 * (1 + x' ^ 2)⁻¹ := by gcongr
          _ = _ := rfl
      calc mkHypRadial (D0 * p.1 / 2) p.2 x' * |f x'|
          ≤ (4 * π ^ 2 * Am * Real.exp (16 * (D0 * (2 * t₀) / 2)) *
            (2 * (1 + 2 * (x₀ + 1))) ^ 3 * (1 + x' ^ 2)⁻¹) * M :=
            mul_le_mul hR (hM x') (abs_nonneg _) (hR0.trans hR)
        _ = C * (1 + x' ^ 2)⁻¹ := by simp only [C]; ring
    · refine (ae_restrict_iff' measurableSet_Ici).2 (ae_of_all _ fun x' hx' => ?_)
      intro p hp
      have hp1 : 0 < p.1 := lt_of_lt_of_le (by positivity) hp.1.1
      exact ((mk_kernelX_continuousAt (x₀ := p.2) hD0 hp1 hx').mul
        continuousAt_const).continuousWithinAt
  exact (continuousWithinAt_inter hU).1 ((hcont _ (hsub ⟨⟨ht₀, hx₀⟩, mem_of_mem_nhds hU⟩)).mono
    hsub)

/-- The semigroup applied to `f`, extended by `f` at `t ≤ 0`. -/
def mkSemigroupX (D0 : ℝ) (f : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  if 0 < p.1 then ∫ x' in Ici (0 : ℝ), mkKernelX D0 p.1 p.2 x' * f x' else f p.2

/-- **Continuity up to `t = 0`.** For `D₀ > 0` and a bounded continuous `f`,
`(t, x) ↦ P_t f(x)` (with `P_0 f = f`) is continuous on `[0, ∞) × [0, ∞)`. -/
theorem mk_semigroupX_continuousOn {D0 : ℝ} (hD0 : 0 < D0) {f : ℝ → ℝ} (hf : Continuous f)
    {M : ℝ} (hM : ∀ y, |f y| ≤ M) :
    ContinuousOn (mkSemigroupX D0 f) (Ici 0 ×ˢ Ici 0) := by
  rintro ⟨t₀, x₀⟩ ⟨ht₀, hx₀⟩
  have ht₀' : 0 ≤ t₀ := ht₀
  have hx₀' : 0 ≤ x₀ := hx₀
  rcases ht₀'.eq_or_lt with h0 | hpos
  · -- the boundary `t = 0`
    subst h0
    rw [ContinuousWithinAt, Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    have hU := mk_kernelX_approxId hD0 hf hM (x₀ + 1)
    rw [Metric.tendstoUniformlyOn_iff] at hU
    obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.eventually_nhds_iff.1
      (eventually_nhdsWithin_iff.1 (hU (ε / 2) (by positivity)))
    obtain ⟨δ₂, hδ₂, hδ₂'⟩ := Metric.continuousAt_iff.1 hf.continuousAt (ε / 2) (by positivity)
    refine ⟨min (min δ₁ δ₂) 1, by positivity, fun p hp hpd => ?_⟩
    rw [Prod.dist_eq] at hpd
    have hd1 : dist p.1 0 < δ₁ := lt_of_le_of_lt (le_max_left _ _)
      (lt_of_lt_of_le hpd ((min_le_left _ _).trans (min_le_left _ _)))
    have hd2 : dist p.2 x₀ < δ₂ := lt_of_le_of_lt (le_max_right _ _)
      (lt_of_lt_of_le hpd ((min_le_left _ _).trans (min_le_right _ _)))
    have hd3 : dist p.2 x₀ < 1 := lt_of_le_of_lt (le_max_right _ _)
      (lt_of_lt_of_le hpd (min_le_right _ _))
    have hp2 : p.2 ∈ Icc 0 (x₀ + 1) := ⟨hp.2, by
      rw [Real.dist_eq] at hd3; linarith [(abs_lt.1 hd3).2]⟩
    have hf2 : dist (f p.2) (f x₀) < ε / 2 := hδ₂' hd2
    have h00 : mkSemigroupX D0 f (0, x₀) = f x₀ := by simp [mkSemigroupX]
    rw [h00]
    by_cases hp1 : 0 < p.1
    · have hu := hδ₁' hd1 hp1 p.2 hp2
      simp only [mkSemigroupX, hp1, ↓reduceIte]
      calc dist (∫ x' in Ici (0 : ℝ), mkKernelX D0 p.1 p.2 x' * f x') (f x₀)
          ≤ dist (∫ x' in Ici (0 : ℝ), mkKernelX D0 p.1 p.2 x' * f x') (f p.2) +
            dist (f p.2) (f x₀) := dist_triangle _ _ _
        _ < ε / 2 + ε / 2 := by rw [dist_comm] at hu; linarith
        _ = ε := by ring
    · simp only [mkSemigroupX, hp1, ↓reduceIte]
      linarith
  · -- the interior `t > 0`
    have hc := mk_kernelX_integral_continuousOn hD0 hf.measurable hM (t₀, x₀) ⟨hpos, hx₀⟩
    have hN : Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) ∈ 𝓝 (t₀, x₀) :=
      (isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hpos, mem_univ _⟩
    rw [← continuousWithinAt_inter hN]
    have hset : Ici (0 : ℝ) ×ˢ Ici (0 : ℝ) ∩ Ioi 0 ×ˢ univ = Ioi 0 ×ˢ Ici 0 := by
      ext q; simp only [mem_inter_iff, mem_prod, mem_Ici, mem_Ioi, mem_univ, and_true]
      constructor
      · rintro ⟨⟨_, h2⟩, h1⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1.le, h2⟩, h1⟩
    rw [hset]
    refine hc.congr (fun q hq => ?_) ?_
    · simp [mkSemigroupX, show (0 : ℝ) < q.1 from hq.1]
    · simp [mkSemigroupX, hpos]

end BlockBand.Diffusion
