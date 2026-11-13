module

public import BlockBand.Diffusion.Kernel.McKeanPDEAngular
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Backward equation for the McKean factor `pX` off the diagonal

Lebesgue measure on `[0, 2π]` in the angle `θ`; `D₀ > 0`; `T = D₀t/2`. For `x' ≥ 0` and `x` in
the open set `{x > 0, x ≠ x'}` (off the diagonal `cosh d = mkHypCos x x' θ > 1` for every `θ`,
so the clamp of `mkHypKernel` is never active) we differentiate
`mkHypRadial T x x' = 2 ∫_0^{2π} K_T(C(x, θ)) dθ` under the integral:
* `mk_hasDerivAt_hypRadial_x`: `∂_x = mkPX1 T x x' = 2 ∫ ∂_cK(C) C_x dθ`;
* `mk_hasDerivAt_px1`: `∂_x mkPX1 = mkPX2 T x x' = 2 ∫ (∂_c²K(C) C_x² + ∂_cK(C) C_xx) dθ`;
* `mk_hasDerivAt_hypRadial_T` (also on the diagonal's complement with `x = 0` allowed):
  `∂_T = mkPXT T x x' = 2 ∫ ∂_TK(C) dθ`;
* `mk_px_identity`: `x(1+x) mkPX2 + (1+2x) mkPX1 = mkPXT` — the angular identities of
  `McKeanPDEAngular` plus `∫_0^{2π} ∂_θ[∂_cK(C) C_θ] dθ = 0` (`C_θ = 0` at `θ = 0, 2π`).

**KP2 (off the diagonal).** For `D₀ > 0`, `t > 0`, `x > 0`, `x' ≥ 0`, `x ≠ x'`
(`mk_kernelX_pde`):
`∂_t pX_t(x, x') = (D₀/2) [x(1+x) ∂_x² pX_t(x, x') + (1+2x) ∂_x pX_t(x, x')]`,
with the derivatives given by `mk_hasDerivAt_kernelX_t`, `mk_hasDerivAt_kernelX_x`,
`mk_hasDerivAt_kernelX_xx`.

Dominated differentiation uses a compactness bound (`mk_hasDerivAt_intervalIntegral`): the
`θ`-integrand's parameter derivative is jointly continuous on a compact box.
The extension to the diagonal and to joint continuity is in `McKeanPDEDiag` (`mk_kernelX_pde'`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory Filter Topology Set Real

/-!
### A generic differentiation lemma for interval integrals
-/

/-- Differentiation under `∫_a^b` with a parameter `x`, assuming the parameter-derivative is
jointly continuous on `[x₀ - δ, x₀ + δ] × ℝ`. -/
theorem mk_hasDerivAt_intervalIntegral {F F' : ℝ → ℝ → ℝ} {x₀ δ a b : ℝ} (hδ : 0 < δ)
    (hab : a ≤ b) (hF : ∀ x ∈ Icc (x₀ - δ) (x₀ + δ), Continuous (F x))
    (hF' : ∀ x ∈ Icc (x₀ - δ) (x₀ + δ), ∀ θ,
      ContinuousAt (fun p : ℝ × ℝ => F' p.1 p.2) (x, θ))
    (hd : ∀ x ∈ Icc (x₀ - δ) (x₀ + δ), ∀ θ, HasDerivAt (fun y => F y θ) (F' x θ) x) :
    HasDerivAt (fun x => ∫ θ in a..b, F x θ) (∫ θ in a..b, F' x₀ θ) x₀ := by
  have hK : IsCompact (Icc (x₀ - δ) (x₀ + δ) ×ˢ Icc a b) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (f := fun p : ℝ × ℝ => F' p.1 p.2)
    fun p hp => (hF' p.1 hp.1 p.2).continuousWithinAt
  have hx₀ : x₀ ∈ Icc (x₀ - δ) (x₀ + δ) := ⟨by linarith, by linarith⟩
  have hs : Icc (x₀ - δ) (x₀ + δ) ∈ 𝓝 x₀ := Icc_mem_nhds (by linarith) (by linarith)
  have hF'x₀ : Continuous (F' x₀) := continuous_iff_continuousAt.2 fun θ =>
    (hF' x₀ hx₀ θ).comp (f := fun φ : ℝ => (x₀, φ)) (x := θ) (by fun_prop)
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := fun _ => M) hs
    (eventually_of_mem hs fun x hx => (hF x hx).aestronglyMeasurable)
    ((hF x₀ hx₀).intervalIntegrable a b) hF'x₀.aestronglyMeasurable
    (ae_of_all _ fun θ hθ x hx => ?_) intervalIntegrable_const
    (ae_of_all _ fun θ _ x hx => hd x hx θ)).2
  rw [Set.uIoc_of_le hab] at hθ
  exact hM (x, θ) ⟨hx, Ioc_subset_Icc_self hθ⟩

/-- A neighbourhood `[x - δ, x + δ]` of an off-diagonal point `x > 0`, `x ≠ x'`, staying in
the open set `{z > 0, z ≠ x'}`. -/
theorem mk_offdiag_nhds {x x' : ℝ} (hx : 0 < x) (hne : x ≠ x') :
    ∃ δ > 0, ∀ z ∈ Icc (x - δ) (x + δ), 0 < z ∧ z ≠ x' := by
  have hd : 0 < |x - x'| := abs_pos.2 (sub_ne_zero.2 hne)
  refine ⟨min x |x - x'| / 2, by positivity, fun z hz => ⟨?_, ?_⟩⟩
  · have := min_le_left x |x - x'|
    linarith [hz.1]
  · intro hzx
    subst hzx
    have h1 := min_le_right x |x - z|
    have h2 : |x - z| ≤ min x |x - z| / 2 := by
      rw [abs_le]; constructor <;> linarith [hz.1, hz.2]
    linarith

/-!
### Continuity of the angular integrands
-/

theorem mk_hypCos_continuous₂ (x' : ℝ) :
    Continuous fun p : ℝ × ℝ => mkHypCos p.1 x' p.2 := by
  unfold mkHypCos; fun_prop

theorem mk_comp_hypCos_continuousAt {f : ℝ → ℝ} (hf : ∀ c, 1 < c → ContinuousAt f c)
    {x x' : ℝ} (hx : 0 ≤ x) (hx' : 0 ≤ x') (hne : x ≠ x') (θ : ℝ) :
    ContinuousAt (fun p : ℝ × ℝ => f (mkHypCos p.1 x' p.2)) (x, θ) :=
  (hf _ (mk_one_lt_hypCos hx hx' hne θ)).comp (f := fun p : ℝ × ℝ => mkHypCos p.1 x' p.2)
    (x := (x, θ)) (mk_hypCos_continuous₂ x').continuousAt

theorem mk_comp_hypCos_continuous {f : ℝ → ℝ} (hf : ∀ c, 1 < c → ContinuousAt f c)
    {x x' : ℝ} (hx : 0 ≤ x) (hx' : 0 ≤ x') (hne : x ≠ x') :
    Continuous fun θ => f (mkHypCos x x' θ) :=
  continuous_iff_continuousAt.2 fun θ =>
    (hf _ (mk_one_lt_hypCos hx hx' hne θ)).comp (f := fun φ => mkHypCos x x' φ) (x := θ)
      (by unfold mkHypCos; fun_prop)

theorem mk_cx_continuousAt {x x' : ℝ} (hx : 0 < x) (θ : ℝ) :
    ContinuousAt (fun p : ℝ × ℝ => mkCx p.1 x' p.2) (x, θ) := by
  have hα := (mk_al_pos hx).ne'
  unfold mkCx
  fun_prop (disch := simp [hα])

theorem mk_cxx_continuousAt {x x' : ℝ} (hx : 0 < x) (θ : ℝ) :
    ContinuousAt (fun p : ℝ × ℝ => mkCxx p.1 x' p.2) (x, θ) := by
  have hα := (mk_al_pos hx).ne'
  unfold mkCxx
  fun_prop (disch := simp [hα])

theorem mk_k1_continuousAt_c {T : ℝ} (hT : 0 < T) (c : ℝ) (hc : 1 < c) :
    ContinuousAt (mkK1 T) c :=
  (mk_hasDerivAt_k1 hT hc).continuousAt

theorem mk_k2_continuousAt_c {T : ℝ} (hT : 0 < T) (c : ℝ) (hc : 1 < c) :
    ContinuousAt (mkK2 T) c :=
  (mk_k2_continuousAt hT hc).comp (f := fun c' : ℝ => (T, c')) (x := c) (by fun_prop)

theorem mk_kT_continuousAt_c {T : ℝ} (hT : 0 < T) (c : ℝ) (hc : 1 < c) :
    ContinuousAt (mkKT T) c :=
  (mk_kT_continuousAt hT hc).comp (f := fun c' : ℝ => (T, c')) (x := c) (by fun_prop)

/-!
### The derivatives of `mkHypRadial`
-/

/-- `∂_x mkHypRadial T x x'` off the diagonal. -/
def mkPX1 (T x x' : ℝ) : ℝ :=
  2 * ∫ θ in (0 : ℝ)..(2 * π), mkK1 T (mkHypCos x x' θ) * mkCx x x' θ

/-- `∂_x² mkHypRadial T x x'` off the diagonal. -/
def mkPX2 (T x x' : ℝ) : ℝ :=
  2 * ∫ θ in (0 : ℝ)..(2 * π),
    (mkK2 T (mkHypCos x x' θ) * mkCx x x' θ ^ 2 + mkK1 T (mkHypCos x x' θ) * mkCxx x x' θ)

/-- `∂_T mkHypRadial T x x'` off the diagonal. -/
def mkPXT (T x x' : ℝ) : ℝ := 2 * ∫ θ in (0 : ℝ)..(2 * π), mkKT T (mkHypCos x x' θ)

theorem mk_hasDerivAt_hypRadial_x {T x x' : ℝ} (hT : 0 < T) (hx : 0 < x) (hx' : 0 ≤ x')
    (hne : x ≠ x') : HasDerivAt (fun z => mkHypRadial T z x') (mkPX1 T x x') x := by
  obtain ⟨δ, hδ, hz⟩ := mk_offdiag_nhds hx hne
  unfold mkHypRadial mkPX1
  refine HasDerivAt.const_mul 2 (mk_hasDerivAt_intervalIntegral (x₀ := x) (a := 0)
    (b := 2 * π) (F := fun z θ => mkHypKernel T (mkHypCos z x' θ))
    (F' := fun z θ => mkK1 T (mkHypCos z x' θ) * mkCx z x' θ)
    hδ Real.two_pi_pos.le (fun z _ => mk_hypKernel_comp_continuous hT z x') (fun z hzs θ => ?_)
    (fun z hzs θ => ?_))
  · obtain ⟨hz0, hzne⟩ := hz z hzs
    exact (mk_comp_hypCos_continuousAt (fun c hc => mk_k1_continuousAt_c hT c hc) hz0.le hx'
      hzne θ).mul (mk_cx_continuousAt hz0 θ)
  · obtain ⟨hz0, hzne⟩ := hz z hzs
    exact HasDerivAt.comp (h₂ := mkHypKernel T) (h := fun y => mkHypCos y x' θ) z
      (mk_hasDerivAt_hypKernel hT (mk_one_lt_hypCos hz0.le hx' hzne θ))
      (mk_hasDerivAt_hypCos_x hz0 x' θ)

theorem mk_hasDerivAt_px1 {T x x' : ℝ} (hT : 0 < T) (hx : 0 < x) (hx' : 0 ≤ x')
    (hne : x ≠ x') : HasDerivAt (fun z => mkPX1 T z x') (mkPX2 T x x') x := by
  obtain ⟨δ, hδ, hz⟩ := mk_offdiag_nhds hx hne
  unfold mkPX1 mkPX2
  refine HasDerivAt.const_mul 2 (mk_hasDerivAt_intervalIntegral (x₀ := x) (a := 0)
    (b := 2 * π) (F := fun z θ => mkK1 T (mkHypCos z x' θ) * mkCx z x' θ)
    (F' := fun z θ => mkK2 T (mkHypCos z x' θ) * mkCx z x' θ ^ 2 +
      mkK1 T (mkHypCos z x' θ) * mkCxx z x' θ)
    hδ Real.two_pi_pos.le (fun z hzs => ?_) (fun z hzs θ => ?_) (fun z hzs θ => ?_))
  · obtain ⟨hz0, hzne⟩ := hz z hzs
    exact (mk_comp_hypCos_continuous (fun c hc => mk_k1_continuousAt_c hT c hc) hz0.le hx'
      hzne).mul (continuous_iff_continuousAt.2 fun θ =>
        (mk_cx_continuousAt hz0 θ).comp (f := fun φ : ℝ => (z, φ)) (x := θ) (by fun_prop))
  · obtain ⟨hz0, hzne⟩ := hz z hzs
    have h1 := mk_comp_hypCos_continuousAt (fun c hc => mk_k1_continuousAt_c hT c hc) hz0.le hx'
      hzne θ
    have h2 := mk_comp_hypCos_continuousAt (fun c hc => mk_k2_continuousAt_c hT c hc) hz0.le hx'
      hzne θ
    exact (h2.mul ((mk_cx_continuousAt hz0 θ).pow 2)).add (h1.mul (mk_cxx_continuousAt hz0 θ))
  · obtain ⟨hz0, hzne⟩ := hz z hzs
    have hC := mk_one_lt_hypCos hz0.le hx' hzne θ
    have h := ((mk_hasDerivAt_k1 hT hC).comp z (mk_hasDerivAt_hypCos_x hz0 x' θ)).mul
      (mk_hasDerivAt_cx hz0 x' θ)
    convert h using 1
    · rfl
    · simp only [Function.comp_apply]; ring

theorem mk_hasDerivAt_hypRadial_T {T x x' : ℝ} (hT : 0 < T) (hx : 0 ≤ x) (hx' : 0 ≤ x')
    (hne : x ≠ x') : HasDerivAt (fun T' => mkHypRadial T' x x') (mkPXT T x x') T := by
  unfold mkHypRadial mkPXT
  have hδ : 0 < T / 2 := by linarith
  refine HasDerivAt.const_mul 2 (mk_hasDerivAt_intervalIntegral (x₀ := T) (a := 0)
    (b := 2 * π) (F := fun T' θ => mkHypKernel T' (mkHypCos x x' θ))
    (F' := fun T' θ => mkKT T' (mkHypCos x x' θ))
    hδ Real.two_pi_pos.le (fun T' hT' => mk_hypKernel_comp_continuous (by linarith [hT'.1]) x x')
    (fun T' hT' θ => ?_) (fun T' hT' θ => ?_))
  · have hT'0 : 0 < T' := by linarith [hT'.1]
    exact (mk_kT_continuousAt hT'0 (mk_one_lt_hypCos hx hx' hne θ)).comp
      (f := fun p : ℝ × ℝ => (p.1, mkHypCos x x' p.2)) (x := (T', θ))
      (by unfold mkHypCos; fun_prop)
  · have hT'0 : 0 < T' := by linarith [hT'.1]
    exact mk_hasDerivAt_hypKernel_T hT'0 (mk_one_lt_hypCos hx hx' hne θ)

/-!
### The identity `x(1+x) ∂_x² + (1+2x) ∂_x = ∂_T`
-/

theorem mk_angular_boundary {T x x' : ℝ} (hT : 0 < T) (hx : 0 < x) (hx' : 0 ≤ x')
    (hne : x ≠ x') :
    ∫ θ in (0 : ℝ)..(2 * π), (mkK2 T (mkHypCos x x' θ) * mkCth x x' θ * mkCth x x' θ +
      mkK1 T (mkHypCos x x' θ) * mkCthth x x' θ) = 0 := by
  have hc1 := mk_comp_hypCos_continuous (fun c hc => mk_k1_continuousAt_c hT c hc) hx.le hx'
    hne
  have hc2 := mk_comp_hypCos_continuous (fun c hc => mk_k2_continuousAt_c hT c hc) hx.le hx'
    hne
  have hcth : Continuous fun θ => mkCth x x' θ := by unfold mkCth; fun_prop
  have hcthth : Continuous fun θ => mkCthth x x' θ := by unfold mkCthth; fun_prop
  have hderiv : ∀ θ ∈ uIcc (0 : ℝ) (2 * π),
      HasDerivAt (fun φ => mkK1 T (mkHypCos x x' φ) * mkCth x x' φ)
        (mkK2 T (mkHypCos x x' θ) * mkCth x x' θ * mkCth x x' θ +
          mkK1 T (mkHypCos x x' θ) * mkCthth x x' θ) θ := fun θ _ => by
    have h := ((mk_hasDerivAt_k1 hT (mk_one_lt_hypCos hx.le hx' hne θ)).comp θ
      (mk_hasDerivAt_hypCos_θ x x' θ)).mul (mk_hasDerivAt_cth x x' θ)
    exact h
  have hint : IntervalIntegrable (fun θ => mkK2 T (mkHypCos x x' θ) * mkCth x x' θ *
      mkCth x x' θ + mkK1 T (mkHypCos x x' θ) * mkCthth x x' θ) volume 0 (2 * π) :=
    (((hc2.mul hcth).mul hcth).add (hc1.mul hcthth)).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp [mk_cth_zero, mk_cth_two_pi]

/-- **The integrated angular identity.** Off the diagonal (`x > 0`, `x' ≥ 0`, `x ≠ x'`),
`x(1+x) mkPX2 + (1+2x) mkPX1 = mkPXT`. -/
theorem mk_px_identity {T x x' : ℝ} (hT : 0 < T) (hx : 0 < x) (hx' : 0 ≤ x') (hne : x ≠ x') :
    x * (1 + x) * mkPX2 T x x' + (1 + 2 * x) * mkPX1 T x x' = mkPXT T x x' := by
  have hc1 := mk_comp_hypCos_continuous (fun c hc => mk_k1_continuousAt_c hT c hc) hx.le hx'
    hne
  have hc2 := mk_comp_hypCos_continuous (fun c hc => mk_k2_continuousAt_c hT c hc) hx.le hx'
    hne
  have hcT := mk_comp_hypCos_continuous (fun c hc => mk_kT_continuousAt_c hT c hc) hx.le hx'
    hne
  have hcx : Continuous fun θ => mkCx x x' θ := continuous_iff_continuousAt.2 fun θ =>
    (mk_cx_continuousAt hx θ).comp (f := fun φ : ℝ => (x, φ)) (x := θ) (by fun_prop)
  have hcxx : Continuous fun θ => mkCxx x x' θ := continuous_iff_continuousAt.2 fun θ =>
    (mk_cxx_continuousAt hx θ).comp (f := fun φ : ℝ => (x, φ)) (x := θ) (by fun_prop)
  have hcth : Continuous fun θ => mkCth x x' θ := by unfold mkCth; fun_prop
  have hcthth : Continuous fun θ => mkCthth x x' θ := by unfold mkCthth; fun_prop
  have hQ := mk_angular_boundary hT hx hx' hne
  have hpt : ∀ θ, x * (1 + x) * (mkK2 T (mkHypCos x x' θ) * mkCx x x' θ ^ 2 +
      mkK1 T (mkHypCos x x' θ) * mkCxx x x' θ) +
      (1 + 2 * x) * (mkK1 T (mkHypCos x x' θ) * mkCx x x' θ) =
      mkKT T (mkHypCos x x' θ) - (mkK2 T (mkHypCos x x' θ) * mkCth x x' θ * mkCth x x' θ +
        mkK1 T (mkHypCos x x' θ) * mkCthth x x' θ) / (4 * (x * (1 + x))) := fun θ => by
    rw [mk_angular_pde hx hx' θ (mkK1 T (mkHypCos x x' θ)) (mkK2 T (mkHypCos x x' θ)), mkKT]
    ring
  have i2 : IntervalIntegrable (fun θ => x * (1 + x) * (mkK2 T (mkHypCos x x' θ) *
      mkCx x x' θ ^ 2 + mkK1 T (mkHypCos x x' θ) * mkCxx x x' θ)) volume 0 (2 * π) :=
    (((hc2.mul (hcx.pow 2)).add (hc1.mul hcxx)).intervalIntegrable 0 (2 * π)).const_mul
      (x * (1 + x))
  have i1 : IntervalIntegrable (fun θ => (1 + 2 * x) * (mkK1 T (mkHypCos x x' θ) *
      mkCx x x' θ)) volume 0 (2 * π) :=
    ((hc1.mul hcx).intervalIntegrable 0 (2 * π)).const_mul (1 + 2 * x)
  have iT := hcT.intervalIntegrable (μ := volume) 0 (2 * π)
  have iQ : IntervalIntegrable (fun θ => mkK2 T (mkHypCos x x' θ) * mkCth x x' θ *
      mkCth x x' θ + mkK1 T (mkHypCos x x' θ) * mkCthth x x' θ) volume 0 (2 * π) :=
    (((hc2.mul hcth).mul hcth).add (hc1.mul hcthth)).intervalIntegrable 0 (2 * π)
  unfold mkPX2 mkPX1 mkPXT
  calc x * (1 + x) * (2 * ∫ θ in (0 : ℝ)..(2 * π), (mkK2 T (mkHypCos x x' θ) *
        mkCx x x' θ ^ 2 + mkK1 T (mkHypCos x x' θ) * mkCxx x x' θ)) +
      (1 + 2 * x) * (2 * ∫ θ in (0 : ℝ)..(2 * π), mkK1 T (mkHypCos x x' θ) * mkCx x x' θ)
      = 2 * ∫ θ in (0 : ℝ)..(2 * π), (x * (1 + x) * (mkK2 T (mkHypCos x x' θ) *
        mkCx x x' θ ^ 2 + mkK1 T (mkHypCos x x' θ) * mkCxx x x' θ) +
        (1 + 2 * x) * (mkK1 T (mkHypCos x x' θ) * mkCx x x' θ)) := by
        rw [intervalIntegral.integral_add i2 i1, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
        ring
    _ = 2 * ∫ θ in (0 : ℝ)..(2 * π), (mkKT T (mkHypCos x x' θ) -
        (mkK2 T (mkHypCos x x' θ) * mkCth x x' θ * mkCth x x' θ +
          mkK1 T (mkHypCos x x' θ) * mkCthth x x' θ) / (4 * (x * (1 + x)))) := by
        congr 1
        exact intervalIntegral.integral_congr fun θ _ => hpt θ
    _ = 2 * ∫ θ in (0 : ℝ)..(2 * π), mkKT T (mkHypCos x x' θ) := by
        rw [intervalIntegral.integral_sub iT (iQ.div_const _), intervalIntegral.integral_div,
          hQ, zero_div, sub_zero]

/-!
### KP2 for `pX`
-/

theorem mk_kernelX_eq_fun {D0 t x' : ℝ} (ht : 0 < t) (hx' : 0 ≤ x') :
    (fun z => mkKernelX D0 t z x') = fun z => mkHypRadial (D0 * t / 2) z x' :=
  funext fun _ => mk_kernelX_eq ht hx'

/-- `∂_x pX_t(x, x') = mkPX1 (D₀t/2) x x'` off the diagonal. -/
theorem mk_hasDerivAt_kernelX_x {D0 t x x' : ℝ} (hD0 : 0 < D0) (ht : 0 < t) (hx : 0 < x)
    (hx' : 0 ≤ x') (hne : x ≠ x') :
    HasDerivAt (fun z => mkKernelX D0 t z x') (mkPX1 (D0 * t / 2) x x') x := by
  rw [mk_kernelX_eq_fun ht hx']
  exact mk_hasDerivAt_hypRadial_x (by positivity) hx hx' hne

/-- `∂_x² pX_t(x, x') = mkPX2 (D₀t/2) x x'` off the diagonal. -/
theorem mk_hasDerivAt_kernelX_xx {D0 t x x' : ℝ} (hD0 : 0 < D0) (ht : 0 < t) (hx : 0 < x)
    (hx' : 0 ≤ x') (hne : x ≠ x') :
    HasDerivAt (fun z => mkPX1 (D0 * t / 2) z x') (mkPX2 (D0 * t / 2) x x') x :=
  mk_hasDerivAt_px1 (by positivity) hx hx' hne

/-- `∂_t pX_t(x, x') = (D₀/2) mkPXT (D₀t/2) x x'` off the diagonal (`x ≥ 0` allowed). -/
theorem mk_hasDerivAt_kernelX_t {D0 t x x' : ℝ} (hD0 : 0 < D0) (ht : 0 < t) (hx : 0 ≤ x)
    (hx' : 0 ≤ x') (hne : x ≠ x') :
    HasDerivAt (fun s => mkKernelX D0 s x x') (D0 / 2 * mkPXT (D0 * t / 2) x x') t := by
  have heq : (fun s => mkKernelX D0 s x x') =ᶠ[𝓝 t] fun s => mkHypRadial (D0 * s / 2) x x' := by
    filter_upwards [lt_mem_nhds ht] with s hs
    exact mk_kernelX_eq hs hx'
  have hlin : HasDerivAt (fun s : ℝ => D0 * s / 2) (D0 / 2) t := by
    convert ((hasDerivAt_id t).const_mul D0).div_const 2 using 1
    · rfl
    · ring
  have h := (mk_hasDerivAt_hypRadial_T (by positivity) hx hx' hne).comp t hlin
  refine (h.congr_of_eventuallyEq heq).congr_deriv ?_
  ring

/-- **KP2 (backward equation off the diagonal).** For `D₀ > 0`, `t > 0`, `x > 0`, `x' ≥ 0`
with `x ≠ x'`:
`∂_t pX_t(x, x') = (D₀/2) [x(1+x) ∂_x² pX_t(x, x') + (1+2x) ∂_x pX_t(x, x')]`. -/
theorem mk_kernelX_pde {D0 t x x' : ℝ} (hD0 : 0 < D0) (ht : 0 < t) (hx : 0 < x)
    (hx' : 0 ≤ x') (hne : x ≠ x') :
    deriv (fun s => mkKernelX D0 s x x') t =
      D0 / 2 * (x * (1 + x) * deriv (deriv fun z => mkKernelX D0 t z x') x +
        (1 + 2 * x) * deriv (fun z => mkKernelX D0 t z x') x) := by
  have hT : 0 < D0 * t / 2 := by positivity
  have hd1 : deriv (fun z => mkKernelX D0 t z x') =ᶠ[𝓝 x] fun z => mkPX1 (D0 * t / 2) z x' := by
    have hopen : IsOpen {z : ℝ | 0 < z ∧ z ≠ x'} := isOpen_Ioi.inter isOpen_ne
    filter_upwards [hopen.mem_nhds ⟨hx, hne⟩] with z hz
    exact (mk_hasDerivAt_kernelX_x hD0 ht hz.1 hx' hz.2).deriv
  rw [(mk_hasDerivAt_kernelX_t hD0 ht hx.le hx' hne).deriv, hd1.deriv_eq,
    (mk_hasDerivAt_kernelX_xx hD0 ht hx hx' hne).deriv,
    (mk_hasDerivAt_kernelX_x hD0 ht hx hx' hne).deriv, ← mk_px_identity hT hx hx' hne]

end BlockBand.Diffusion
