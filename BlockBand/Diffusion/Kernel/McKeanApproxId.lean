module

public import BlockBand.Diffusion.Kernel.McKeanMass

/-!
# Approximate identity for `pX`

Headline **KA4** `mk_kernelX_approxId`: for `D₀ > 0`, a continuous `f : ℝ → ℝ` with
`|f| ≤ M` and any `X`,
`TendstoUniformlyOn (fun t x => ∫_{[0,∞)} pX t x x' f(x') dx') f (𝓝[>] 0) (Icc 0 X)`.

* `mk_hypCos_sub_one`: `cosh d ≥ 1` and `2ab(cosh d - 1) ≥ (a - b)²`, `a = 1+2x`, `b = 1+2x'`
  (`x, x' ≥ 0`, every angle);
* `mk_hypCos_far`: if `x ∈ [0, X]`, `x' ≥ 0`, `|x' - x| ≥ δ > 0` then
  `cosh d ≥ 1 + min(1/4, δ²/(1+2X)²)`;
* `mk_hypKernel_le_tail`: for `c ≥ 1 + η` (`η > 0`), `K_T(c) ≤ τ_η(T) K_{2T}(c)` with
  `τ_η(T) = 2^{3/2} e^{T/4} e^{-arcosh(1+η)²/(8T)} → 0` as `T → 0⁺` (`mk_tail_tendsto`);
* hence far from the diagonal `pX t ≤ τ pX (2t)` (`mk_kernelX_le_tail`), whose integral is
  `τ` by mass one at time `2t`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory Filter Topology Set Real
open scoped ENNReal

/-- `cosh d ≥ 1` with the quantitative bound `2ab(cosh d - 1) ≥ (a - b)²`,
`a = 1+2x`, `b = 1+2x'`. -/
theorem mk_hypCos_sub_one {x x' : ℝ} (hx : 0 ≤ x) (hx' : 0 ≤ x') (θ : ℝ) :
    1 ≤ mkHypCos x x' θ ∧
      ((1 + 2 * x) - (1 + 2 * x')) ^ 2 ≤
        2 * (1 + 2 * x) * (1 + 2 * x') * (mkHypCos x x' θ - 1) := by
  set S := 4 * Real.sqrt (x * (1 + x) * (x' * (1 + x'))) with hS
  have hS0 : 0 ≤ S := by positivity
  have hS2 : S ^ 2 = 16 * (x * (1 + x) * (x' * (1 + x'))) := by
    rw [hS, mul_pow, Real.sq_sqrt (by positivity)]; ring
  set a := 1 + 2 * x
  set b := 1 + 2 * x'
  have ha : 1 ≤ a := by simp only [a]; linarith
  have hb : 1 ≤ b := by simp only [b]; linarith
  have hkey : (a * b - 1) ^ 2 - S ^ 2 = (a - b) ^ 2 := by rw [hS2]; simp only [a, b]; ring
  have hu : 0 ≤ a * b - 1 := by nlinarith
  have hSle : S ≤ a * b - 1 :=
    (pow_le_pow_iff_left₀ hS0 hu two_ne_zero).1 (by nlinarith [sq_nonneg (a - b)])
  have hc : a * b - S ≤ mkHypCos x x' θ := by
    have := Real.cos_le_one θ
    show a * b - S ≤ a * b - S * Real.cos θ
    nlinarith
  have hm : 1 ≤ a * b - S := by linarith
  refine ⟨by linarith, ?_⟩
  have h1 : (a - b) ^ 2 = (a * b - S - 1) * (a * b + S - 1) := by rw [← hkey]; ring
  have h2 : (a * b - S - 1) * (a * b + S - 1) ≤ (mkHypCos x x' θ - 1) * (2 * a * b) := by
    apply mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  linarith

/-- Far from the diagonal, `cosh d - 1` is bounded below uniformly for starts in `[0, X]`. -/
theorem mk_hypCos_far {x x' δ X : ℝ} (hx : 0 ≤ x) (hxX : x ≤ X) (hx' : 0 ≤ x') (hδ : 0 < δ)
    (hfar : δ ≤ |x' - x|) (θ : ℝ) :
    1 + min (1 / 4) (δ ^ 2 / (1 + 2 * X) ^ 2) ≤ mkHypCos x x' θ := by
  obtain ⟨_, h⟩ := mk_hypCos_sub_one hx hx' θ
  set q := mkHypCos x x' θ - 1
  set a := 1 + 2 * x
  set b := 1 + 2 * x'
  set A := 1 + 2 * X
  have ha : 1 ≤ a := by simp only [a]; linarith
  have hb : 1 ≤ b := by simp only [b]; linarith
  have haA : a ≤ A := by simp only [a, A]; linarith
  have hd : 4 * δ ^ 2 ≤ (a - b) ^ 2 := by
    have : (a - b) ^ 2 = 4 * (x' - x) ^ 2 := by simp only [a, b]; ring
    rw [this, ← sq_abs (x' - x)]
    nlinarith
  suffices hq : min (1 / 4) (δ ^ 2 / A ^ 2) ≤ q by simp only [q] at hq; linarith
  have hq0 : 0 ≤ q := by nlinarith [sq_nonneg (a - b)]
  by_cases hba : 2 * a ≤ b
  · refine (min_le_left _ _).trans ?_
    by_contra hlt
    push Not at hlt
    have hab : 0 < 2 * a * b := by nlinarith
    have h3 : 2 * a * b * q < 2 * a * b * (1 / 4) := mul_lt_mul_of_pos_left hlt hab
    nlinarith
  · push Not at hba
    refine (min_le_right _ _).trans ?_
    have hA : 0 < A ^ 2 := by have : (1 : ℝ) ≤ A := ha.trans haA; positivity
    rw [div_le_iff₀ hA]
    have h4 : 2 * a * b * q ≤ 4 * a ^ 2 * q := by nlinarith
    have h5 : a ^ 2 * q ≤ A ^ 2 * q := mul_le_mul_of_nonneg_right (by nlinarith) hq0
    nlinarith

theorem mk_hypKernel_eq_mkA (T c : ℝ) :
    mkHypKernel T c = mkA T * ∫ v in Ioi (0 : ℝ), mkMcKeanG T (max c 1 + v ^ 2) := rfl

theorem mk_mkA_pos {T : ℝ} (hT : 0 < T) : 0 < mkA T := by
  unfold mkA
  have := Real.rpow_pos_of_pos (by positivity : 0 < 4 * π * T) (3 / 2 : ℝ)
  positivity

theorem mk_mkA_ratio {T : ℝ} (hT : 0 < T) :
    mkA T / mkA (2 * T) = (2 : ℝ) ^ (3 / 2 : ℝ) * Real.exp (T / 4) := by
  unfold mkA
  have h4 : 0 < 4 * π * T := by positivity
  have hr : (4 * π * (2 * T)) ^ (3 / 2 : ℝ) =
      (2 : ℝ) ^ (3 / 2 : ℝ) * (4 * π * T) ^ (3 / 2 : ℝ) := by
    rw [show 4 * π * (2 * T) = 2 * (4 * π * T) by ring, Real.mul_rpow (by norm_num) h4.le]
  have hp := Real.rpow_pos_of_pos h4 (3 / 2 : ℝ)
  have hp2 := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (3 / 2 : ℝ)
  have he : Real.exp (-(2 * T) / 4) * Real.exp (T / 4) = Real.exp (-T / 4) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hr, ← he]
  field_simp

/-- The tail factor `τ_η(T) = (A_T / A_{2T}) e^{-arcosh(1+η)²/(8T)}`. -/
def mkTail (T η : ℝ) : ℝ := mkA T / mkA (2 * T) * Real.exp (-Real.arcosh (1 + η) ^ 2 / (8 * T))

theorem mk_tail_nonneg {T : ℝ} (hT : 0 < T) (η : ℝ) : 0 ≤ mkTail T η := by
  unfold mkTail
  have := mk_mkA_pos hT
  have := mk_mkA_pos (by positivity : 0 < 2 * T)
  positivity

/-- Gaussian tail comparison of McKean's kernel with the kernel at doubled time. -/
theorem mk_hypKernel_le_tail {T η c : ℝ} (hT : 0 < T) (hη : 0 < η) (hc : 1 + η ≤ c) :
    mkHypKernel T c ≤ mkTail T η * mkHypKernel (2 * T) c := by
  have hT2 : 0 < 2 * T := by positivity
  set E := Real.exp (-Real.arcosh (1 + η) ^ 2 / (8 * T))
  have hI : ∫ v in Ioi (0 : ℝ), mkMcKeanG T (max c 1 + v ^ 2) ≤
      ∫ v in Ioi (0 : ℝ), E * mkMcKeanG (2 * T) (max c 1 + v ^ 2) := by
    refine setIntegral_mono_on (mk_integrableOn_G hT c) ((mk_integrableOn_G hT2 c).const_mul E)
      measurableSet_Ioi fun v _ => ?_
    have hw : 1 + η ≤ max c 1 + v ^ 2 := by nlinarith [le_max_left c 1, sq_nonneg v]
    have hs0 : 0 ≤ Real.arcosh (1 + η) := Real.arcosh_nonneg (by linarith)
    have hs : Real.arcosh (1 + η) ≤ Real.arcosh (max c 1 + v ^ 2) :=
      (Real.arcosh_le_arcosh (by linarith) (by linarith)).2 hw
    have hsq : Real.arcosh (1 + η) ^ 2 ≤ Real.arcosh (max c 1 + v ^ 2) ^ 2 := by
      gcongr
    unfold mkMcKeanG
    set s := Real.arcosh (max c 1 + v ^ 2)
    have hsplit : Real.exp (-s ^ 2 / (4 * T)) =
        Real.exp (-s ^ 2 / (8 * T)) * Real.exp (-s ^ 2 / (4 * (2 * T))) := by
      rw [← Real.exp_add]; congr 1; field_simp; ring
    have hE : Real.exp (-s ^ 2 / (8 * T)) ≤ E := by
      apply Real.exp_le_exp.2
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith
    have hσ := (mk_sdivSinh_pos s).le
    rw [hsplit]
    calc 2 * mkSdivSinh s * (Real.exp (-s ^ 2 / (8 * T)) * Real.exp (-s ^ 2 / (4 * (2 * T))))
        ≤ 2 * mkSdivSinh s * (E * Real.exp (-s ^ 2 / (4 * (2 * T)))) := by gcongr
      _ = _ := by ring
  rw [integral_const_mul] at hI
  rw [mk_hypKernel_eq_mkA, mk_hypKernel_eq_mkA]
  have hA := mk_mkA_pos hT
  have hA2 := mk_mkA_pos hT2
  unfold mkTail
  calc mkA T * ∫ v in Ioi (0 : ℝ), mkMcKeanG T (max c 1 + v ^ 2)
      ≤ mkA T * (E * ∫ v in Ioi (0 : ℝ), mkMcKeanG (2 * T) (max c 1 + v ^ 2)) :=
        mul_le_mul_of_nonneg_left hI hA.le
    _ = _ := by field_simp; simp only [E]; ring_nf

theorem mk_tail_tendsto {η : ℝ} (hη : 0 < η) :
    Tendsto (fun T => mkTail T η) (𝓝[>] 0) (𝓝 0) := by
  have hs : 0 < Real.arcosh (1 + η) := Real.arcosh_pos (by linarith)
  have h1 : Tendsto (fun T : ℝ => -Real.arcosh (1 + η) ^ 2 / 8 * T⁻¹) (𝓝[>] 0) atBot :=
    tendsto_inv_nhdsGT_zero.const_mul_atTop_of_neg (by
      have := pow_pos hs 2; linarith)
  have h2 := Real.tendsto_exp_atBot.comp h1
  have h3 : Tendsto (fun T : ℝ => (2 : ℝ) ^ (3 / 2 : ℝ) * Real.exp (T / 4)) (𝓝[>] 0)
      (𝓝 ((2 : ℝ) ^ (3 / 2 : ℝ) * Real.exp (0 / 4))) :=
    ((continuous_const.mul (Real.continuous_exp.comp (continuous_id.div_const 4))).tendsto
      0).mono_left nhdsWithin_le_nhds
  have h4 := h3.mul h2
  rw [mul_zero] at h4
  refine h4.congr' (eventually_nhdsWithin_of_forall fun T hT => ?_)
  have hT0 : 0 < T := hT
  simp only [Function.comp_apply, mkTail, mk_mkA_ratio hT0]
  congr 2
  field_simp

/-- Far from the diagonal, `pX` at time `t` is dominated by `τ(D₀t/2) pX` at time `2t`. -/
theorem mk_kernelX_le_tail {D0 t x x' δ X : ℝ} (hD0 : 0 < D0) (ht : 0 < t) (hx : 0 ≤ x)
    (hxX : x ≤ X) (hδ : 0 < δ) (hfar : δ ≤ |x' - x|) :
    mkKernelX D0 t x x' ≤
      mkTail (D0 * t / 2) (min (1 / 4) (δ ^ 2 / (1 + 2 * X) ^ 2)) * mkKernelX D0 (2 * t) x x' := by
  have hT : 0 < D0 * t / 2 := by positivity
  have hη : 0 < min (1 / 4 : ℝ) (δ ^ 2 / (1 + 2 * X) ^ 2) := by
    have : 0 < 1 + 2 * X := by linarith
    exact lt_min (by norm_num) (by positivity)
  unfold mkKernelX
  by_cases hx' : 0 ≤ x'
  · have ht2 : 0 < 2 * t := by positivity
    simp only [ht, hx', ht2, and_self, ↓reduceIte]
    rw [mk_hypRadial_eq_Ioo, mk_hypRadial_eq_Ioo,
      show D0 * (2 * t) / 2 = 2 * (D0 * t / 2) by ring]
    have hint := fun T (hT : 0 < T) =>
      ((mk_hypKernel_comp_continuous hT x x').integrableOn_Icc (μ := volume)).mono_set
        (Ioo_subset_Icc_self (a := -π) (b := π))
    have := setIntegral_mono_on (hint _ hT) ((hint _ (by positivity)).const_mul
      (mkTail (D0 * t / 2) (min (1 / 4) (δ ^ 2 / (1 + 2 * X) ^ 2)))) measurableSet_Ioo
      fun θ _ => mk_hypKernel_le_tail hT hη (mk_hypCos_far hx hxX hx' hδ hfar θ)
    rw [integral_const_mul] at this
    linarith
  · simp [hx']

theorem mk_time_tendsto {D0 : ℝ} (hD0 : 0 < D0) :
    Tendsto (fun h : ℝ => D0 * h / 2) (𝓝[>] 0) (𝓝[>] 0) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, eventually_nhdsWithin_of_forall fun h hh => ?_⟩
  · have : Tendsto (fun h : ℝ => D0 * h / 2) (𝓝 0) (𝓝 (D0 * 0 / 2)) :=
      ((continuous_const.mul continuous_id).div_const 2).tendsto 0
    rw [mul_zero, zero_div] at this
    exact this.mono_left nhdsWithin_le_nhds
  · have : 0 < h := hh
    show 0 < D0 * h / 2
    positivity

theorem mk_kernelX_approxId_of_nonneg {D0 : ℝ} (hD0 : 0 < D0) {f : ℝ → ℝ} (hf : Continuous f)
    {M : ℝ} (hM : ∀ y, |f y| ≤ M) {X : ℝ} (hX : 0 ≤ X) :
    TendstoUniformlyOn (fun t x => ∫ x' in Ici (0 : ℝ), mkKernelX D0 t x x' * f x') f
      (𝓝[>] 0) (Icc 0 X) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  obtain ⟨δ₀, hδ₀, hδ⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_Icc (a := (0 : ℝ)) (b := X + 1)).uniformContinuousOn_of_continuous
      hf.continuousOn) (ε / 2) (by positivity)
  set δ := min δ₀ 1 with hδdef
  have hδpos : 0 < δ := lt_min hδ₀ one_pos
  set η := min (1 / 4 : ℝ) (δ ^ 2 / (1 + 2 * X) ^ 2) with hηdef
  have hη : 0 < η := by
    have : 0 < 1 + 2 * X := by linarith
    exact lt_min (by norm_num) (by positivity)
  have htail : ∀ᶠ t in 𝓝[>] (0 : ℝ), 2 * M * mkTail (D0 * t / 2) η < ε / 2 := by
    have h := ((mk_tail_tendsto hη).comp (mk_time_tendsto hD0)).const_mul (2 * M)
    rw [mul_zero] at h
    exact h.eventually (gt_mem_nhds (by positivity))
  filter_upwards [htail, self_mem_nhdsWithin] with t ht htpos
  have htpos : 0 < t := htpos
  have ht2 : 0 < 2 * t := by positivity
  intro x hx
  obtain ⟨hx0, hxX⟩ := hx
  set τ := mkTail (D0 * t / 2) η with hτdef
  have hτ : 0 ≤ τ := mk_tail_nonneg (by positivity) η
  have hp := mk_integrableOn_kernelX hD0 htpos hx0
  have hp2 := mk_integrableOn_kernelX hD0 ht2 hx0
  have hmass := mk_integral_kernelX hD0 htpos hx0
  have hmass2 := mk_integral_kernelX hD0 ht2 hx0
  have hpf : IntegrableOn (fun x' => mkKernelX D0 t x x' * f x') (Ici 0) :=
    hp.mul_bdd hf.aestronglyMeasurable (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs]; exact hM y)
  have hpd : IntegrableOn (fun x' => mkKernelX D0 t x x' * (f x - f x')) (Ici 0) :=
    hp.mul_bdd (c := 2 * M) (continuous_const.sub hf).aestronglyMeasurable
      (ae_of_all _ fun y => by
        rw [Real.norm_eq_abs]
        exact (abs_sub (f x) (f y)).trans (by linarith [hM x, hM y]))
  have hrepr : f x - ∫ x' in Ici (0 : ℝ), mkKernelX D0 t x x' * f x' =
      ∫ x' in Ici (0 : ℝ), mkKernelX D0 t x x' * (f x - f x') := by
    simp_rw [mul_sub]
    rw [integral_sub (hp.mul_const _) hpf, integral_mul_const, hmass, one_mul]
  rw [Real.dist_eq, hrepr]
  have hpt : ∀ x' ∈ Ici (0 : ℝ), |mkKernelX D0 t x x' * (f x - f x')| ≤
      ε / 2 * mkKernelX D0 t x x' + 2 * M * τ * mkKernelX D0 (2 * t) x x' := by
    intro x' hx'
    have hx'0 : 0 ≤ x' := hx'
    have hp0 := mk_kernelX_nonneg hD0 t x x'
    have hp20 := mk_kernelX_nonneg hD0 (2 * t) x x'
    have hsec : 0 ≤ 2 * M * τ * mkKernelX D0 (2 * t) x x' := by positivity
    rw [abs_mul, abs_of_nonneg hp0]
    by_cases hnear : |x' - x| < δ
    · have hδ1 : δ ≤ 1 := min_le_right _ _
      have hx'1 : x' ∈ Icc 0 (X + 1) :=
        ⟨hx'0, by have := (abs_lt.1 hnear).2; linarith⟩
      have hxI : x ∈ Icc 0 (X + 1) := ⟨hx0, by linarith⟩
      have hd : dist (f x) (f x') < ε / 2 := hδ x hxI x' hx'1 (by
        rw [Real.dist_eq, abs_sub_comm]; exact lt_of_lt_of_le hnear (min_le_left _ _))
      rw [Real.dist_eq] at hd
      have : mkKernelX D0 t x x' * |f x - f x'| ≤ ε / 2 * mkKernelX D0 t x x' := by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_right hd.le hp0
      linarith
    · push Not at hnear
      have hk := mk_kernelX_le_tail hD0 htpos hx0 hxX hδpos hnear
      have hf2 : |f x - f x'| ≤ 2 * M :=
        (abs_sub (f x) (f x')).trans (by linarith [hM x, hM x'])
      have : mkKernelX D0 t x x' * |f x - f x'| ≤ 2 * M * τ * mkKernelX D0 (2 * t) x x' := by
        calc _ ≤ mkKernelX D0 t x x' * (2 * M) := mul_le_mul_of_nonneg_left hf2 hp0
          _ ≤ τ * mkKernelX D0 (2 * t) x x' * (2 * M) :=
            mul_le_mul_of_nonneg_right hk (by positivity)
          _ = _ := by ring
      have : 0 ≤ ε / 2 * mkKernelX D0 t x x' := by positivity
      linarith
  calc |∫ x' in Ici (0 : ℝ), mkKernelX D0 t x x' * (f x - f x')|
      ≤ ∫ x' in Ici (0 : ℝ), |mkKernelX D0 t x x' * (f x - f x')| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ x' in Ici (0 : ℝ),
          (ε / 2 * mkKernelX D0 t x x' + 2 * M * τ * mkKernelX D0 (2 * t) x x') :=
        setIntegral_mono_on hpd.abs ((hp.const_mul _).add (hp2.const_mul _)) measurableSet_Ici hpt
    _ = ε / 2 + 2 * M * τ := by
        rw [integral_add (hp.const_mul _) (hp2.const_mul _), integral_const_mul,
          integral_const_mul, hmass, hmass2]
        ring
    _ < ε := by linarith

/-- **KA4: approximate identity.** For `D₀ > 0`, `f` bounded and continuous and any `X`,
`∫_{[0,∞)} pX t x x' f(x') dx' → f(x)` as `t → 0⁺`, uniformly in `x ∈ [0, X]`. -/
theorem mk_kernelX_approxId {D0 : ℝ} (hD0 : 0 < D0) {f : ℝ → ℝ} (hf : Continuous f)
    {M : ℝ} (hM : ∀ y, |f y| ≤ M) (X : ℝ) :
    TendstoUniformlyOn (fun t x => ∫ x' in Ici (0 : ℝ), mkKernelX D0 t x x' * f x') f
      (𝓝[>] 0) (Icc 0 X) :=
  (mk_kernelX_approxId_of_nonneg hD0 hf hM (le_max_right X 0)).mono
    (Icc_subset_Icc le_rfl (le_max_left X 0))

end BlockBand.Diffusion
