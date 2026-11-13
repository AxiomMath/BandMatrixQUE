module

public import BlockBand.Diffusion.Kernel.McKeanPDEEndpoint

/-!
# The backward equation for `pX` including the diagonal; joint continuity of its derivatives

Lebesgue measure on `[0, 2π]` in `θ`; `D₀ > 0`; `T = D₀t/2`. For `x > 0`, `x' ≥ 0` and
`θ ∈ (0, 2π)` one has `mkHypCos x x' θ > 1` (`mk_one_lt_hypCos_Ioo`, also on the diagonal
`x = x'`); the exceptional angles `θ ∈ {0, 2π}` are null. With the global bounds of
`McKeanPDEEndpoint` (`∂_cK`, `∂_c²K`, `∂_TK` bounded on `(1, ∞)`, locally uniformly in `T`),
dominated convergence gives, for every `x' ≥ 0`, `T > 0`, `x > 0`:
* `mk_hasDerivAt_hypRadial_x'`: `∂_x mkHypRadial T x x' = mkPX1 T x x'`;
* `mk_hasDerivAt_px1'`: `∂_x mkPX1 T x x' = mkPX2 T x x'`;
* `mk_hasDerivAt_hypRadial_T'`: `∂_T mkHypRadial T x x' = mkPXT T x x'`;
* `mk_px1_continuousAt`, `mk_px2_continuousAt`, `mk_pxT_continuousAt`: joint continuity in
  `(T, x)` on `(0,∞) × (0,∞)`;
* `mk_px_identity'`: `x(1+x) mkPX2 + (1+2x) mkPX1 = mkPXT` (by continuity across the diagonal).

**KP2.** For `D₀ > 0`, `x' ≥ 0`, on `U = (0,∞) × (0,∞)` in `(t, x)`:
`mk_kernelX_pde'`: `∂_t pX = (D₀/2)[x(1+x) ∂_x² pX + (1+2x) ∂_x pX]` at every point of `U`
(diagonal included), and `mk_kernelX_derivs_continuousOn`: `pX`, `∂_x pX`, `∂_x² pX`, `∂_t pX`
are jointly continuous on `U` (with the derivatives identified by `HasDerivAt` at every point).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory Filter Topology Set Real
open scoped Interval

/-!
### Generic a.e. tools on `[0, 2π]`
-/

theorem mk_ae_Ioo (P : ℝ → Prop) (h : ∀ θ ∈ Ioo (0 : ℝ) (2 * π), P θ) :
    ∀ᵐ θ ∂(volume : Measure ℝ), θ ∈ Ι (0 : ℝ) (2 * π) → P θ := by
  have hne : ∀ᵐ θ ∂(volume : Measure ℝ), θ ∉ ({2 * π} : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.1 (measure_singleton _)
  filter_upwards [hne] with θ hθ hmem
  rw [Set.uIoc_of_le Real.two_pi_pos.le] at hmem
  exact h θ ⟨hmem.1, lt_of_le_of_ne hmem.2 fun h' => hθ (by simp [h'])⟩

/-- Differentiation under `∫_0^{2π}` with bounds and differentiability only for
`θ ∈ (0, 2π)`. -/
theorem mk_hasDerivAt_angular {F F' : ℝ → ℝ → ℝ} {x₀ δ M : ℝ} (hδ : 0 < δ)
    (hFm : ∀ x ∈ Icc (x₀ - δ) (x₀ + δ), Measurable (F x))
    (hint : IntervalIntegrable (F x₀) volume 0 (2 * π)) (hF'm : Measurable (F' x₀))
    (hb : ∀ θ ∈ Ioo (0 : ℝ) (2 * π), ∀ x ∈ Icc (x₀ - δ) (x₀ + δ), |F' x θ| ≤ M)
    (hd : ∀ θ ∈ Ioo (0 : ℝ) (2 * π), ∀ x ∈ Icc (x₀ - δ) (x₀ + δ),
      HasDerivAt (fun y => F y θ) (F' x θ) x) :
    HasDerivAt (fun x => ∫ θ in (0 : ℝ)..(2 * π), F x θ) (∫ θ in (0 : ℝ)..(2 * π), F' x₀ θ)
      x₀ := by
  have hs : Icc (x₀ - δ) (x₀ + δ) ∈ 𝓝 x₀ := Icc_mem_nhds (by linarith) (by linarith)
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := fun _ => M) hs
    (eventually_of_mem hs fun x hx => (hFm x hx).aestronglyMeasurable) hint
    hF'm.aestronglyMeasurable
    (mk_ae_Ioo (fun θ => ∀ x ∈ Icc (x₀ - δ) (x₀ + δ), ‖F' x θ‖ ≤ M)
      fun θ hθ x hx => by rw [Real.norm_eq_abs]; exact hb θ hθ x hx)
    intervalIntegrable_const
    (mk_ae_Ioo (fun θ => ∀ x ∈ Icc (x₀ - δ) (x₀ + δ), HasDerivAt (fun y => F y θ) (F' x θ) x)
      fun θ hθ x hx => hd θ hθ x hx)).2

/-- Continuity of `∫_0^{2π}` in a parameter `p ∈ ℝ²` with bounds and continuity only for
`θ ∈ (0, 2π)`. -/
theorem mk_continuousAt_angular {F : ℝ × ℝ → ℝ → ℝ} {p₀ : ℝ × ℝ} {N : Set (ℝ × ℝ)} {M : ℝ}
    (hN : N ∈ 𝓝 p₀) (hFm : ∀ p ∈ N, Measurable (F p))
    (hb : ∀ p ∈ N, ∀ θ ∈ Ioo (0 : ℝ) (2 * π), |F p θ| ≤ M)
    (hc : ∀ θ ∈ Ioo (0 : ℝ) (2 * π), ContinuousAt (fun p => F p θ) p₀) :
    ContinuousAt (fun p => ∫ θ in (0 : ℝ)..(2 * π), F p θ) p₀ :=
  intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => M)
    (eventually_of_mem hN fun p hp => (hFm p hp).aestronglyMeasurable)
    (eventually_of_mem hN fun p hp => mk_ae_Ioo (fun θ => ‖F p θ‖ ≤ M) fun θ hθ => by
      rw [Real.norm_eq_abs]; exact hb p hp θ hθ)
    intervalIntegrable_const (mk_ae_Ioo (fun θ => ContinuousAt (fun p => F p θ) p₀) hc)

theorem mk_intervalIntegrable_of_bound {f : ℝ → ℝ} {M : ℝ} (hf : Measurable f)
    (hb : ∀ θ ∈ Ioo (0 : ℝ) (2 * π), |f θ| ≤ M) : IntervalIntegrable f volume 0 (2 * π) :=
  (intervalIntegrable_const (c := M)).mono_fun' hf.aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_uIoc).2 (mk_ae_Ioo (fun θ => ‖f θ‖ ≤ M)
      fun θ hθ => by rw [Real.norm_eq_abs]; exact hb θ hθ))

theorem mk_bound_of_continuousAt {f : ℝ × ℝ → ℝ} {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hf : ∀ p ∈ K, ContinuousAt f p) : ∃ M, ∀ p ∈ K, |f p| ≤ M := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn fun p hp => (hf p hp).continuousWithinAt
  exact ⟨M, fun p hp => by rw [← Real.norm_eq_abs]; exact hM p hp⟩

theorem mk_bound_of_continuousAt₁ {f : ℝ → ℝ} {a b : ℝ} (hf : ∀ x ∈ Icc a b, ContinuousAt f x) :
    ∃ M, ∀ x ∈ Icc a b, |f x| ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn fun x hx =>
    (hf x hx).continuousWithinAt
  exact ⟨M, fun x hx => by rw [← Real.norm_eq_abs]; exact hM x hx⟩

/-!
### Pointwise facts
-/

/-- For `x > 0`, `x' ≥ 0` and `θ ∈ (0, 2π)`, `cosh d > 1` (also when `x = x'`). -/
theorem mk_one_lt_hypCos_Ioo {x x' θ : ℝ} (hx : 0 < x) (hx' : 0 ≤ x')
    (hθ : θ ∈ Ioo (0 : ℝ) (2 * π)) : 1 < mkHypCos x x' θ := by
  by_cases hne : x = x'
  · subst hne
    have hcos : Real.cos θ < 1 := by
      refine lt_of_le_of_ne (Real.cos_le_one θ) fun h => ?_
      have := (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [hθ.1, Real.pi_pos]) hθ.2).1 h
      linarith [hθ.1]
    have hsq : Real.sqrt (x * (1 + x) * (x * (1 + x))) = x * (1 + x) :=
      Real.sqrt_mul_self (by positivity)
    rw [mkHypCos, hsq]
    have : 0 < x * (1 + x) := by positivity
    nlinarith
  · exact mk_one_lt_hypCos hx.le hx' hne θ

theorem mk_cx_continuous {x : ℝ} (hx : 0 < x) (x' : ℝ) : Continuous fun θ => mkCx x x' θ :=
  continuous_iff_continuousAt.2 fun θ =>
    (mk_cx_continuousAt hx θ).comp (f := fun φ : ℝ => (x, φ)) (x := θ) (by fun_prop)

theorem mk_cxx_continuous {x : ℝ} (hx : 0 < x) (x' : ℝ) : Continuous fun θ => mkCxx x x' θ :=
  continuous_iff_continuousAt.2 fun θ =>
    (mk_cxx_continuousAt hx θ).comp (f := fun φ : ℝ => (x, φ)) (x := θ) (by fun_prop)

theorem mk_hypCos_continuous_θ (x x' : ℝ) : Continuous fun θ => mkHypCos x x' θ := by
  unfold mkHypCos; fun_prop

/-- Uniform bounds of `|∂_cK|, |∂_c²K|, |∂_TK|` on `T ∈ [T₀/2, 3T₀/2]`, `c > 1`. -/
theorem mk_k_box {T₀ : ℝ} (hT₀ : 0 < T₀) :
    ∃ Kb, ∀ T ∈ Icc (T₀ - T₀ / 2) (T₀ + T₀ / 2), ∀ c, 1 < c →
      |mkK1 T c| ≤ Kb ∧ |mkK2 T c| ≤ Kb ∧ |mkKT T c| ≤ Kb := by
  have hpos : ∀ T ∈ Icc (T₀ - T₀ / 2) (T₀ + T₀ / 2), 0 < T := fun T hT => by linarith [hT.1]
  obtain ⟨A, hA⟩ := mk_bound_of_continuousAt₁ fun T hT => mk_mkA_continuousAt (hpos T hT)
  obtain ⟨A1, hA1⟩ := mk_bound_of_continuousAt₁ fun T hT => mk_mkA1_continuousAt (hpos T hT)
  set B := mkBdG (T₀ - T₀ / 2) (T₀ + T₀ / 2) * (π / 2)
  have hB : 0 ≤ B := by have := mk_bdG_nonneg (T₂ := T₀ + T₀ / 2) (by linarith : 0 < T₀ - T₀ / 2)
                        positivity
  refine ⟨(A + A1) * B, fun T hT c hc => ?_⟩
  obtain ⟨b1, b2, bT, -, -⟩ := mk_k_global (by linarith : 0 < T₀ - T₀ / 2) hT.1 hT.2 hc
  have hc5 : (c ^ 5)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hc.le)
  have hA0 : |mkA T| ≤ A := hA T hT
  have hA10 : |mkA1 T| ≤ A1 := hA1 T hT
  have hAA : 0 ≤ |mkA1 T| := abs_nonneg _
  have hAn : 0 ≤ A := (abs_nonneg _).trans hA0
  have hA1n : 0 ≤ A1 := (abs_nonneg _).trans hA10
  have hBc : B * (c ^ 5)⁻¹ ≤ B := mul_le_of_le_one_right hB hc5
  have e : mkBdG (T₀ - T₀ / 2) (T₀ + T₀ / 2) * (π / 2) * (c ^ 5)⁻¹ = B * (c ^ 5)⁻¹ := rfl
  rw [e] at b1 b2 bT
  have hB' : 0 ≤ B * (c ^ 5)⁻¹ := by positivity
  refine ⟨?_, ?_, ?_⟩
  · calc |mkK1 T c| ≤ |mkA T| * (B * (c ^ 5)⁻¹) := b1
      _ ≤ (A + A1) * B := by gcongr; linarith
  · calc |mkK2 T c| ≤ |mkA T| * (B * (c ^ 5)⁻¹) := b2
      _ ≤ (A + A1) * B := by gcongr; linarith
  · calc |mkKT T c| ≤ (|mkA1 T| + |mkA T|) * (B * (c ^ 5)⁻¹) := bT
      _ ≤ (A1 + A) * B := by gcongr
      _ = (A + A1) * B := by ring

/-- Uniform bounds of `|C_x|, |C_xx|` on `x ∈ [x₀/2, 3x₀/2]`, `θ ∈ [0, 2π]`. -/
theorem mk_cx_box {x₀ : ℝ} (hx₀ : 0 < x₀) (x' : ℝ) :
    ∃ M, ∀ x ∈ Icc (x₀ - x₀ / 2) (x₀ + x₀ / 2), ∀ θ ∈ Icc (0 : ℝ) (2 * π),
      |mkCx x x' θ| ≤ M ∧ |mkCxx x x' θ| ≤ M := by
  have hK : IsCompact (Icc (x₀ - x₀ / 2) (x₀ + x₀ / 2) ×ˢ Icc (0 : ℝ) (2 * π)) :=
    isCompact_Icc.prod isCompact_Icc
  have hpos : ∀ p ∈ Icc (x₀ - x₀ / 2) (x₀ + x₀ / 2) ×ˢ Icc (0 : ℝ) (2 * π), 0 < p.1 :=
    fun p hp => by linarith [hp.1.1]
  obtain ⟨M1, hM1⟩ := mk_bound_of_continuousAt hK fun p hp =>
    mk_cx_continuousAt (x' := x') (hpos p hp) p.2
  obtain ⟨M2, hM2⟩ := mk_bound_of_continuousAt hK fun p hp =>
    mk_cxx_continuousAt (x' := x') (hpos p hp) p.2
  exact ⟨max M1 M2, fun x hx θ hθ => ⟨(hM1 (x, θ) ⟨hx, hθ⟩).trans (le_max_left _ _),
    (hM2 (x, θ) ⟨hx, hθ⟩).trans (le_max_right _ _)⟩⟩

/-!
### Derivatives of `mkHypRadial` at every `x > 0`
-/

/-- `∂_x mkHypRadial T x x' = mkPX1 T x x'` for `T > 0`, `x > 0`, `x' ≥ 0` (diagonal included). -/
theorem mk_hasDerivAt_hypRadial_x' {T x x' : ℝ} (hT : 0 < T) (hx : 0 < x) (hx' : 0 ≤ x') :
    HasDerivAt (fun z => mkHypRadial T z x') (mkPX1 T x x') x := by
  obtain ⟨Kb, hKb⟩ := mk_k_box hT
  obtain ⟨Mc, hMc⟩ := mk_cx_box hx x'
  have hTT : T ∈ Icc (T - T / 2) (T + T / 2) := ⟨by linarith, by linarith⟩
  have hδ : 0 < x / 2 := by linarith
  have hk := mk_k_measurable T
  unfold mkHypRadial mkPX1
  refine HasDerivAt.const_mul 2 (mk_hasDerivAt_angular
    (F := fun z θ => mkHypKernel T (mkHypCos z x' θ))
    (F' := fun z θ => mkK1 T (mkHypCos z x' θ) * mkCx z x' θ) (M := Kb * Mc) hδ
    (fun z _ => (mk_hypKernel_comp_continuous hT z x').measurable)
    ((mk_hypKernel_comp_continuous hT x x').intervalIntegrable _ _)
    ((hk.1.comp (mk_hypCos_continuous_θ x x').measurable).mul
      (mk_cx_continuous hx x').measurable) (fun θ hθ z hz => ?_) (fun θ hθ z hz => ?_))
  · have hz0 : 0 < z := by linarith [hz.1]
    have hC := mk_one_lt_hypCos_Ioo hz0 hx' hθ
    rw [abs_mul]
    exact mul_le_mul (hKb T hTT _ hC).1 (hMc z hz θ (Ioo_subset_Icc_self hθ)).1 (abs_nonneg _)
      ((abs_nonneg _).trans (hKb T hTT _ hC).1)
  · have hz0 : 0 < z := by linarith [hz.1]
    exact HasDerivAt.comp (h₂ := mkHypKernel T) (h := fun y => mkHypCos y x' θ) z
      (mk_hasDerivAt_hypKernel hT (mk_one_lt_hypCos_Ioo hz0 hx' hθ))
      (mk_hasDerivAt_hypCos_x hz0 x' θ)

/-- `∂_x mkPX1 T x x' = mkPX2 T x x'` for `T > 0`, `x > 0`, `x' ≥ 0` (diagonal included). -/
theorem mk_hasDerivAt_px1' {T x x' : ℝ} (hT : 0 < T) (hx : 0 < x) (hx' : 0 ≤ x') :
    HasDerivAt (fun z => mkPX1 T z x') (mkPX2 T x x') x := by
  obtain ⟨Kb, hKb⟩ := mk_k_box hT
  obtain ⟨Mc, hMc⟩ := mk_cx_box hx x'
  have hTT : T ∈ Icc (T - T / 2) (T + T / 2) := ⟨by linarith, by linarith⟩
  have hδ : 0 < x / 2 := by linarith
  have hk := mk_k_measurable T
  have hKb0 : 0 ≤ Kb := (abs_nonneg _).trans (hKb T hTT 2 (by norm_num)).1
  have hMc0 : 0 ≤ Mc := (abs_nonneg _).trans (hMc x ⟨by linarith, by linarith⟩ 0
    ⟨le_rfl, Real.two_pi_pos.le⟩).1
  have hmeas : ∀ z, 0 < z → Measurable fun θ => mkK1 T (mkHypCos z x' θ) * mkCx z x' θ :=
    fun z hz => (hk.1.comp (mk_hypCos_continuous_θ z x').measurable).mul
      (mk_cx_continuous hz x').measurable
  unfold mkPX1 mkPX2
  refine HasDerivAt.const_mul 2 (mk_hasDerivAt_angular
    (F := fun z θ => mkK1 T (mkHypCos z x' θ) * mkCx z x' θ)
    (F' := fun z θ => mkK2 T (mkHypCos z x' θ) * mkCx z x' θ ^ 2 +
      mkK1 T (mkHypCos z x' θ) * mkCxx z x' θ) (M := Kb * Mc ^ 2 + Kb * Mc) hδ
    (fun z hz => hmeas z (by linarith [hz.1]))
    (mk_intervalIntegrable_of_bound (M := Kb * Mc) (hmeas x hx) fun θ hθ => ?_)
    (((hk.2.1.comp (mk_hypCos_continuous_θ x x').measurable).mul
      ((mk_cx_continuous hx x').measurable.pow_const 2)).add
      ((hk.1.comp (mk_hypCos_continuous_θ x x').measurable).mul
        (mk_cxx_continuous hx x').measurable)) (fun θ hθ z hz => ?_) (fun θ hθ z hz => ?_))
  · have hC := mk_one_lt_hypCos_Ioo hx hx' hθ
    rw [abs_mul]
    exact mul_le_mul (hKb T hTT _ hC).1 (hMc x ⟨by linarith, by linarith⟩ θ
      (Ioo_subset_Icc_self hθ)).1 (abs_nonneg _) hKb0
  · have hz0 : 0 < z := by linarith [hz.1]
    have hC := mk_one_lt_hypCos_Ioo hz0 hx' hθ
    obtain ⟨k1, k2, -⟩ := hKb T hTT _ hC
    obtain ⟨c1, c2⟩ := hMc z hz θ (Ioo_subset_Icc_self hθ)
    have hc2 : |mkCx z x' θ ^ 2| ≤ Mc ^ 2 := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) c1 2
    have hKb0' : 0 ≤ Kb := (abs_nonneg _).trans k1
    calc |mkK2 T (mkHypCos z x' θ) * mkCx z x' θ ^ 2 + mkK1 T (mkHypCos z x' θ) * mkCxx z x' θ|
        ≤ |mkK2 T (mkHypCos z x' θ)| * |mkCx z x' θ ^ 2| +
            |mkK1 T (mkHypCos z x' θ)| * |mkCxx z x' θ| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ Kb * Mc ^ 2 + Kb * Mc := by gcongr
  · have hz0 : 0 < z := by linarith [hz.1]
    have hC := mk_one_lt_hypCos_Ioo hz0 hx' hθ
    have h := ((mk_hasDerivAt_k1 hT hC).comp z (mk_hasDerivAt_hypCos_x hz0 x' θ)).mul
      (mk_hasDerivAt_cx hz0 x' θ)
    convert h using 1
    · rfl
    · simp only [Function.comp_apply]; ring

/-- `∂_T mkHypRadial T x x' = mkPXT T x x'` for `T > 0`, `x > 0`, `x' ≥ 0` (diagonal
included). -/
theorem mk_hasDerivAt_hypRadial_T' {T x x' : ℝ} (hT : 0 < T) (hx : 0 < x) (hx' : 0 ≤ x') :
    HasDerivAt (fun T' => mkHypRadial T' x x') (mkPXT T x x') T := by
  obtain ⟨Kb, hKb⟩ := mk_k_box hT
  have hδ : 0 < T / 2 := by linarith
  unfold mkHypRadial mkPXT
  refine HasDerivAt.const_mul 2 (mk_hasDerivAt_angular
    (F := fun T' θ => mkHypKernel T' (mkHypCos x x' θ))
    (F' := fun T' θ => mkKT T' (mkHypCos x x' θ)) (M := Kb) hδ
    (fun T' hT' => (mk_hypKernel_comp_continuous (by linarith [hT'.1]) x x').measurable)
    ((mk_hypKernel_comp_continuous hT x x').intervalIntegrable _ _)
    ((mk_k_measurable T).2.2.1.comp (mk_hypCos_continuous_θ x x').measurable)
    (fun θ hθ T' hT' => (hKb T' hT' _ (mk_one_lt_hypCos_Ioo hx hx' hθ)).2.2)
    (fun θ hθ T' hT' => ?_))
  exact mk_hasDerivAt_hypKernel_T (by linarith [hT'.1]) (mk_one_lt_hypCos_Ioo hx hx' hθ)

/-!
### Joint continuity in `(T, x)`
-/

theorem mk_box_nhds {T₀ x₀ : ℝ} (hT₀ : 0 < T₀) (hx₀ : 0 < x₀) :
    Icc (T₀ - T₀ / 2) (T₀ + T₀ / 2) ×ˢ Icc (x₀ - x₀ / 2) (x₀ + x₀ / 2) ∈ 𝓝 (T₀, x₀) :=
  prod_mem_nhds (Icc_mem_nhds (by linarith) (by linarith))
    (Icc_mem_nhds (by linarith) (by linarith))

theorem mk_hypCos_param_continuousAt {T₀ x₀ x' θ : ℝ} :
    ContinuousAt (fun p : ℝ × ℝ => (p.1, mkHypCos p.2 x' θ)) (T₀, x₀) := by
  unfold mkHypCos; fun_prop

theorem mk_px1_continuousAt {T₀ x₀ x' : ℝ} (hT₀ : 0 < T₀) (hx₀ : 0 < x₀) (hx' : 0 ≤ x') :
    ContinuousAt (fun p : ℝ × ℝ => mkPX1 p.1 p.2 x') (T₀, x₀) := by
  obtain ⟨Kb, hKb⟩ := mk_k_box hT₀
  obtain ⟨Mc, hMc⟩ := mk_cx_box hx₀ x'
  unfold mkPX1
  refine continuousAt_const.mul (mk_continuousAt_angular
    (F := fun p θ => mkK1 p.1 (mkHypCos p.2 x' θ) * mkCx p.2 x' θ) (M := Kb * Mc)
    (mk_box_nhds hT₀ hx₀) (fun p hp => ?_) (fun p hp θ hθ => ?_) (fun θ hθ => ?_))
  · have hp0 : 0 < p.2 := by linarith [hp.2.1]
    exact ((mk_k_measurable p.1).1.comp (mk_hypCos_continuous_θ p.2 x').measurable).mul
      (mk_cx_continuous hp0 x').measurable
  · have hp0 : 0 < p.2 := by linarith [hp.2.1]
    have hC := mk_one_lt_hypCos_Ioo hp0 hx' hθ
    rw [abs_mul]
    exact mul_le_mul (hKb p.1 hp.1 _ hC).1 (hMc p.2 hp.2 θ (Ioo_subset_Icc_self hθ)).1
      (abs_nonneg _) ((abs_nonneg _).trans (hKb p.1 hp.1 _ hC).1)
  · have hC := mk_one_lt_hypCos_Ioo hx₀ hx' hθ
    exact ((mk_k1_continuousAt hT₀ hC).comp (f := fun p : ℝ × ℝ => (p.1, mkHypCos p.2 x' θ))
      (x := (T₀, x₀)) mk_hypCos_param_continuousAt).mul
      ((mk_cx_continuousAt hx₀ θ).comp (f := fun p : ℝ × ℝ => (p.2, θ)) (x := (T₀, x₀))
        (by fun_prop))

theorem mk_px2_continuousAt {T₀ x₀ x' : ℝ} (hT₀ : 0 < T₀) (hx₀ : 0 < x₀) (hx' : 0 ≤ x') :
    ContinuousAt (fun p : ℝ × ℝ => mkPX2 p.1 p.2 x') (T₀, x₀) := by
  obtain ⟨Kb, hKb⟩ := mk_k_box hT₀
  obtain ⟨Mc, hMc⟩ := mk_cx_box hx₀ x'
  unfold mkPX2
  refine continuousAt_const.mul (mk_continuousAt_angular
    (F := fun p θ => mkK2 p.1 (mkHypCos p.2 x' θ) * mkCx p.2 x' θ ^ 2 +
      mkK1 p.1 (mkHypCos p.2 x' θ) * mkCxx p.2 x' θ) (M := Kb * Mc ^ 2 + Kb * Mc)
    (mk_box_nhds hT₀ hx₀) (fun p hp => ?_) (fun p hp θ hθ => ?_) (fun θ hθ => ?_))
  · have hp0 : 0 < p.2 := by linarith [hp.2.1]
    have hk := mk_k_measurable p.1
    exact ((hk.2.1.comp (mk_hypCos_continuous_θ p.2 x').measurable).mul
      ((mk_cx_continuous hp0 x').measurable.pow_const 2)).add
      ((hk.1.comp (mk_hypCos_continuous_θ p.2 x').measurable).mul
        (mk_cxx_continuous hp0 x').measurable)
  · have hp0 : 0 < p.2 := by linarith [hp.2.1]
    have hC := mk_one_lt_hypCos_Ioo hp0 hx' hθ
    obtain ⟨k1, k2, -⟩ := hKb p.1 hp.1 _ hC
    obtain ⟨c1, c2⟩ := hMc p.2 hp.2 θ (Ioo_subset_Icc_self hθ)
    have hc2 : |mkCx p.2 x' θ ^ 2| ≤ Mc ^ 2 := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) c1 2
    have hKb0 : 0 ≤ Kb := (abs_nonneg _).trans k1
    calc _ ≤ |mkK2 p.1 (mkHypCos p.2 x' θ)| * |mkCx p.2 x' θ ^ 2| +
            |mkK1 p.1 (mkHypCos p.2 x' θ)| * |mkCxx p.2 x' θ| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ Kb * Mc ^ 2 + Kb * Mc := by gcongr
  · have hC := mk_one_lt_hypCos_Ioo hx₀ hx' hθ
    have hpc := mk_hypCos_param_continuousAt (T₀ := T₀) (x₀ := x₀) (x' := x') (θ := θ)
    have hsn : ContinuousAt (fun p : ℝ × ℝ => (p.2, θ)) (T₀, x₀) := by fun_prop
    exact (((mk_k2_continuousAt hT₀ hC).comp (x := (T₀, x₀)) hpc).mul
      (((mk_cx_continuousAt hx₀ θ).comp (x := (T₀, x₀)) hsn).pow 2)).add
      (((mk_k1_continuousAt hT₀ hC).comp (x := (T₀, x₀)) hpc).mul
        ((mk_cxx_continuousAt hx₀ θ).comp (x := (T₀, x₀)) hsn))

theorem mk_pxT_continuousAt {T₀ x₀ x' : ℝ} (hT₀ : 0 < T₀) (hx₀ : 0 < x₀) (hx' : 0 ≤ x') :
    ContinuousAt (fun p : ℝ × ℝ => mkPXT p.1 p.2 x') (T₀, x₀) := by
  obtain ⟨Kb, hKb⟩ := mk_k_box hT₀
  unfold mkPXT
  refine continuousAt_const.mul (mk_continuousAt_angular
    (F := fun p θ => mkKT p.1 (mkHypCos p.2 x' θ)) (M := Kb)
    (mk_box_nhds hT₀ hx₀) (fun p hp => ?_) (fun p hp θ hθ => ?_) (fun θ hθ => ?_))
  · exact (mk_k_measurable p.1).2.2.1.comp (mk_hypCos_continuous_θ p.2 x').measurable
  · have hp0 : 0 < p.2 := by linarith [hp.2.1]
    exact (hKb p.1 hp.1 _ (mk_one_lt_hypCos_Ioo hp0 hx' hθ)).2.2
  · exact (mk_kT_continuousAt hT₀ (mk_one_lt_hypCos_Ioo hx₀ hx' hθ)).comp
      (x := (T₀, x₀)) mk_hypCos_param_continuousAt

/-- **The identity on all of `x > 0`.** `x(1+x) mkPX2 + (1+2x) mkPX1 = mkPXT` for `T > 0`,
`x > 0`, `x' ≥ 0` (on the diagonal by continuity). -/
theorem mk_px_identity' {T x x' : ℝ} (hT : 0 < T) (hx : 0 < x) (hx' : 0 ≤ x') :
    x * (1 + x) * mkPX2 T x x' + (1 + 2 * x) * mkPX1 T x x' = mkPXT T x x' := by
  by_cases hne : x = x'
  · set h : ℝ → ℝ := fun z => z * (1 + z) * mkPX2 T z x' + (1 + 2 * z) * mkPX1 T z x' -
      mkPXT T z x' with hh
    have hsn : ContinuousAt (fun z : ℝ => (T, z)) x := by fun_prop
    have hc : ContinuousAt h x := by
      have h1 := (mk_px1_continuousAt hT hx hx').comp (x := x) hsn
      have h2 := (mk_px2_continuousAt hT hx hx').comp (x := x) hsn
      have h3 := (mk_pxT_continuousAt hT hx hx').comp (x := x) hsn
      exact ((((continuousAt_id.mul (continuousAt_const.add continuousAt_id)).mul h2).add
        ((continuousAt_const.add (continuousAt_const.mul continuousAt_id)).mul h1)).sub h3)
    have hev : h =ᶠ[𝓝[≠] x] fun _ => 0 := by
      have : ∀ᶠ z in 𝓝[≠] x, 0 < z ∧ z ≠ x :=
        (eventually_nhdsWithin_of_eventually_nhds (lt_mem_nhds hx)).and self_mem_nhdsWithin
      filter_upwards [this] with z hz
      simp only [hh]
      rw [mk_px_identity hT hz.1 hx' (hne ▸ hz.2)]
      ring
    have hlim := tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' hev.symm)
    have : h x = 0 := hlim
    simp only [hh] at this
    linarith
  · exact mk_px_identity hT hx hx' hne

/-!
### KP2 for `pX` on `(0, ∞) × (0, ∞)`
-/

/-- `∂_x pX_t(x, x') = mkPX1 (D₀t/2) x x'` for `t > 0`, `x > 0`, `x' ≥ 0`. -/
theorem mk_hasDerivAt_kernelX_x' {D0 t x x' : ℝ} (hD0 : 0 < D0) (ht : 0 < t) (hx : 0 < x)
    (hx' : 0 ≤ x') :
    HasDerivAt (fun z => mkKernelX D0 t z x') (mkPX1 (D0 * t / 2) x x') x := by
  rw [mk_kernelX_eq_fun ht hx']
  exact mk_hasDerivAt_hypRadial_x' (by positivity) hx hx'

/-- `∂_x² pX_t(x, x') = mkPX2 (D₀t/2) x x'` for `t > 0`, `x > 0`, `x' ≥ 0`. -/
theorem mk_hasDerivAt_kernelX_xx' {D0 t x x' : ℝ} (hD0 : 0 < D0) (ht : 0 < t) (hx : 0 < x)
    (hx' : 0 ≤ x') :
    HasDerivAt (fun z => mkPX1 (D0 * t / 2) z x') (mkPX2 (D0 * t / 2) x x') x :=
  mk_hasDerivAt_px1' (by positivity) hx hx'

/-- `∂_t pX_t(x, x') = (D₀/2) mkPXT (D₀t/2) x x'` for `t > 0`, `x > 0`, `x' ≥ 0`. -/
theorem mk_hasDerivAt_kernelX_t' {D0 t x x' : ℝ} (hD0 : 0 < D0) (ht : 0 < t) (hx : 0 < x)
    (hx' : 0 ≤ x') :
    HasDerivAt (fun s => mkKernelX D0 s x x') (D0 / 2 * mkPXT (D0 * t / 2) x x') t := by
  have heq : (fun s => mkKernelX D0 s x x') =ᶠ[𝓝 t] fun s => mkHypRadial (D0 * s / 2) x x' := by
    filter_upwards [lt_mem_nhds ht] with s hs
    exact mk_kernelX_eq hs hx'
  have hlin : HasDerivAt (fun s : ℝ => D0 * s / 2) (D0 / 2) t := by
    convert ((hasDerivAt_id t).const_mul D0).div_const 2 using 1
    · rfl
    · ring
  have h := (mk_hasDerivAt_hypRadial_T' (by positivity) hx hx').comp t hlin
  refine (h.congr_of_eventuallyEq heq).congr_deriv ?_
  ring

/-- **KP2 (backward equation on `(0,∞) × (0,∞)`, diagonal included).** For `D₀ > 0`, `t > 0`,
`x > 0`, `x' ≥ 0`:
`∂_t pX_t(x, x') = (D₀/2) [x(1+x) ∂_x² pX_t(x, x') + (1+2x) ∂_x pX_t(x, x')]`. -/
theorem mk_kernelX_pde' {D0 t x x' : ℝ} (hD0 : 0 < D0) (ht : 0 < t) (hx : 0 < x)
    (hx' : 0 ≤ x') :
    deriv (fun s => mkKernelX D0 s x x') t =
      D0 / 2 * (x * (1 + x) * deriv (deriv fun z => mkKernelX D0 t z x') x +
        (1 + 2 * x) * deriv (fun z => mkKernelX D0 t z x') x) := by
  have hT : 0 < D0 * t / 2 := by positivity
  have hd1 : deriv (fun z => mkKernelX D0 t z x') =ᶠ[𝓝 x] fun z => mkPX1 (D0 * t / 2) z x' := by
    filter_upwards [lt_mem_nhds hx] with z hz
    exact (mk_hasDerivAt_kernelX_x' hD0 ht hz hx').deriv
  rw [(mk_hasDerivAt_kernelX_t' hD0 ht hx hx').deriv, hd1.deriv_eq,
    (mk_hasDerivAt_kernelX_xx' hD0 ht hx hx').deriv,
    (mk_hasDerivAt_kernelX_x' hD0 ht hx hx').deriv, ← mk_px_identity' hT hx hx']

/-- **KP2 (joint continuity).** For `D₀ > 0` and `x' ≥ 0`, on `U = (0,∞) × (0,∞)` the maps
`(t, x) ↦ pX_t(x, x')`, `∂_x pX = mkPX1 (D₀t/2) x x'`, `∂_x² pX = mkPX2 (D₀t/2) x x'` and
`∂_t pX = (D₀/2) mkPXT (D₀t/2) x x'` are continuous. -/
theorem mk_kernelX_derivs_continuousOn {D0 x' : ℝ} (hD0 : 0 < D0) (hx' : 0 ≤ x') :
    ContinuousOn (fun p : ℝ × ℝ => mkKernelX D0 p.1 p.2 x') (Ioi 0 ×ˢ Ioi 0) ∧
      ContinuousOn (fun p : ℝ × ℝ => mkPX1 (D0 * p.1 / 2) p.2 x') (Ioi 0 ×ˢ Ioi 0) ∧
      ContinuousOn (fun p : ℝ × ℝ => mkPX2 (D0 * p.1 / 2) p.2 x') (Ioi 0 ×ˢ Ioi 0) ∧
      ContinuousOn (fun p : ℝ × ℝ => D0 / 2 * mkPXT (D0 * p.1 / 2) p.2 x')
        (Ioi 0 ×ˢ Ioi 0) := by
  have hlin : ∀ p : ℝ × ℝ, ContinuousAt (fun q : ℝ × ℝ => (D0 * q.1 / 2, q.2)) p :=
    fun p => by fun_prop
  refine ⟨fun p hp => (mk_kernelX_continuousAt hD0 hp.1 hx').continuousWithinAt,
    fun p hp => ?_, fun p hp => ?_, fun p hp => ?_⟩
  · have hT : 0 < D0 * p.1 / 2 := by have := hp.1; simp only [mem_Ioi] at this; positivity
    exact ((mk_px1_continuousAt hT hp.2 hx').comp (x := p) (hlin p)).continuousWithinAt
  · have hT : 0 < D0 * p.1 / 2 := by have := hp.1; simp only [mem_Ioi] at this; positivity
    exact ((mk_px2_continuousAt hT hp.2 hx').comp (x := p) (hlin p)).continuousWithinAt
  · have hT : 0 < D0 * p.1 / 2 := by have := hp.1; simp only [mem_Ioi] at this; positivity
    exact (continuousAt_const.mul
      ((mk_pxT_continuousAt hT hp.2 hx').comp (x := p) (hlin p))).continuousWithinAt

end BlockBand.Diffusion
