module

public import BlockBand.Palm.ReferenceFlowBackwardIto
public import BlockBand.Palm.ReferenceFlowBackwardGen
public import BlockBand.Palm.ReferenceFlowAssembly

/-!
# The backward Kolmogorov equation of the reference flow

**Statement** (`backwardEquation_holds`). Measure: `driverLaw μ` on `DriverSample S (RotIdx N)`
(auxiliary noise), `μ` any probability law on `S`; `G ~ matCircularLaw N p`. For continuous
symmetric nonnegative rates `r`, continuous nonnegative damping `κ` with a floor `b > 0` on
`[a,c]`, a rotation flow `𝓝` started at `a` with the time-reflected coefficients, whose kernel
`K_s = (𝓝_{c-s})ᴴ` contracts (`KernelContracts`), and `L_s = (I - K_s K_sᴴ)^{1/2}`
(`refFactor`): for every bounded-`C²` test `f`, `s ∈ (a,c)` and `z`,
`∂_s g_s(z) = -refGenerator r κ s g_s z` with `g_s = refSemigroup μ K L f s`.
Hypotheses: Itô's formula `ItoFormulaFor` on `Matrix (Fin N) (Fin N) ℂ` and
`MultivariateGaussianIBP`.

**Proof.** Put `t = c - s` and `Φ(t) = g_{c-t}(z) = E Ftil f z (𝓝_t)` with
`Ftil f z n = E_G f(nᴴ z + (1 - nᴴ n)^{1/2} G)`. Fix
`t₀ = c - s₀`. The contraction keeps `𝓝_t` a.s. in `{opNorm (nᴴ n) ≤ e^{-bt}}`, so for
`t ≥ t₀/2` the process stays where `Ftil f z` agrees with the globally `C²`, compactly supported
cutoff `φ = χ · Ftil f z` (`exists_cutoff`). Itô's formula for `φ(𝓝_t)`
(`isNativeItoProcess_comp`) and the mean identity (`hasDerivAt_mean_of_ito`) give
`Φ'(t₀) = E[Dφ(𝓝)[D𝓝] + ½ Σ_α D²φ(𝓝)[σ_α𝓝, σ_α𝓝]]` at `t₀`. Near the a.s. values of `𝓝_{t₀}`,
`φ = Ftil f z`, and the drift identity `drift_eq_refGenerator` turns the integrand into
`refGenerator r κ s₀ h_y z` with `h_y(z') = E_G f(K_{s₀} z' + L_{s₀} G)`; averaging over `y`
(`integral_refGenerator_gauss`) gives `refGenerator r κ s₀ g_{s₀} z`. Composing with
`s ↦ c - s` gives the sign.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.ReferenceFlow

open MeasureTheory Set Filter Matrix BlockBand.Palm.ReferenceFlow.Backward
open BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionFlow (IsRotationFlow rotationNoise rotationDrift
  clampTime)
open BlockBand.SourceProcess.FiniteDriverIntegration BlockBand.SourceProcess.Stochastic
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

local instance (priority := high) frobUnifB {n : Type*} [Fintype n] :
    UniformSpace (Matrix n n ℂ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := n) (n := n) (α := ℂ)).toUniformSpace

local instance (priority := high) frobTopB {n : Type*} [Fintype n] :
    TopologicalSpace (Matrix n n ℂ) :=
  (frobUnifB (n := n)).toTopologicalSpace

local instance bwBorelB {N : ℕ} : BorelSpace (Matrix (Fin N) (Fin N) ℂ) :=
  ⟨by exact (inferInstance : BorelSpace (Fin N → Fin N → ℂ)).measurable_eq⟩

variable {N p : ℕ}

namespace Backward

/-!
## Averages over the auxiliary noise
-/

theorem aestronglyMeasurable_integral_gauss {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {K L : Ω → Matrix (Fin N) (Fin N) ℂ} (hK : Measurable K) (hL : Measurable L)
    {Ψ : Matrix (Fin N) (Fin N) ℂ × Matrix (Fin N) (Fin N) ℂ × RefState N p → ℝ}
    (hΨ : Continuous Ψ) :
    AEStronglyMeasurable (fun x => ∫ G, Ψ (K x, L x, G) ∂matCircularLaw N p) P := by
  refine (StronglyMeasurable.integral_prod_right (f := fun x G => Ψ (K x, L x, G)) ?_).aestronglyMeasurable
  exact (hΨ.measurable.comp ((hK.comp measurable_fst).prodMk
    ((hL.comp measurable_fst).prodMk measurable_snd))).stronglyMeasurable

theorem continuous_affine_triple (z : RefState N p) :
    Continuous fun q : Matrix (Fin N) (Fin N) ℂ × Matrix (Fin N) (Fin N) ℂ × RefState N p =>
      lmul q.1 z + lmul q.2.1 q.2.2 :=
  (continuous_lmul_joint.comp (continuous_fst.prodMk continuous_const)).add
    (continuous_lmul_joint.comp ((continuous_fst.comp continuous_snd).prodMk
      (continuous_snd.comp continuous_snd)))

theorem continuous_lmul_fst (u : RefState N p) :
    Continuous fun q : Matrix (Fin N) (Fin N) ℂ × Matrix (Fin N) (Fin N) ℂ × RefState N p =>
      lmul q.1 u :=
  continuous_lmul_joint.comp (continuous_fst.prodMk continuous_const)

/-- **The generator commutes with the auxiliary average** of the Gaussian averages
`h_y(z') = E_G f(K_y z' + L_y G)`, for measurable `K, L` with `|(K_y)_{ij}| ≤ 1` a.s. -/
theorem integral_refGenerator_gauss {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {K L : Ω → Matrix (Fin N) (Fin N) ℂ} (hK : Measurable K)
    (hL : Measurable L) (hKb : ∀ᵐ x ∂P, ∀ i j, ‖K x i j‖ ≤ 1) {C : ℝ}
    {f : RefState N p → ℝ} (hf : IsC2BoundedBy C f) (r : ℝ → Fin N → Fin N → ℝ)
    (κ : ℝ → Fin N → ℝ) (s : ℝ) (z : RefState N p) :
    ∫ x, refGenerator r κ s (fun z' => ∫ G, f (lmul (K x) z' + lmul (L x) G)
        ∂matCircularLaw N p) z ∂P =
      refGenerator r κ s (fun z' => ∫ x, ∫ G, f (lmul (K x) z' + lmul (L x) G)
        ∂matCircularLaw N p ∂P) z := by
  set h : Ω → RefState N p → ℝ := fun x z' => ∫ G, f (lmul (K x) z' + lmul (L x) G)
    ∂matCircularLaw N p with hh
  have hC : 0 ≤ C := (abs_nonneg _).trans (hf.bound 0)
  have hD := fun x => gaussAvg_derivs hf (K x) (L x)
  have hf1c : Continuous (fderiv ℝ f) := hf.contDiff.continuous_fderiv (by norm_num)
  have hf2c : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    (hf.contDiff.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  -- bounds
  have hb1 : ∀ᵐ x ∂P, ∀ z', ‖fderiv ℝ (h x) z'‖ ≤ C * N := by
    filter_upwards [hKb] with x hx z'
    have hKn := norm_lmulL_le (p := p) hx
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
    rw [(hD x).2.1]
    refine (norm_integral_le_of_norm_le_const (C := C * N * ‖u‖)
      (Eventually.of_forall fun G => ?_)).trans (by simp)
    rw [Real.norm_eq_abs]
    refine (abs_fderiv_apply_le hf _ _).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hC
    calc ‖lmul (K x) u‖ = ‖lmulL (K x) u‖ := rfl
      _ ≤ ‖(lmulL (K x) : RefState N p →L[ℝ] RefState N p)‖ * ‖u‖ := (lmulL (K x)).le_opNorm u
      _ ≤ N * ‖u‖ := mul_le_mul_of_nonneg_right hKn (norm_nonneg _)
  have hb2 : ∀ᵐ x ∂P, ∀ z', ‖fderiv ℝ (fderiv ℝ (h x)) z'‖ ≤ C * N * N := by
    filter_upwards [hKb] with x hx z'
    have hKn := norm_lmulL_le (p := p) hx
    have hK' : ∀ u : RefState N p, ‖lmul (K x) u‖ ≤ N * ‖u‖ := fun u =>
      ((lmulL (K x)).le_opNorm u).trans (mul_le_mul_of_nonneg_right hKn (norm_nonneg _))
    refine ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) fun u v => ?_
    have e := (hD x).2.2 z' u v
    unfold D2 at e
    rw [e]
    refine (norm_integral_le_of_norm_le_const (C := C * N * N * ‖u‖ * ‖v‖)
      (Eventually.of_forall fun G => ?_)).trans (by simp)
    rw [Real.norm_eq_abs]
    refine (abs_D2_le hf _ _ _).trans ?_
    have h1 := hK' u
    have h2 := hK' v
    have hu := norm_nonneg (lmul (K x) u)
    calc C * ‖lmul (K x) u‖ * ‖lmul (K x) v‖ ≤ C * (N * ‖u‖) * (N * ‖v‖) := by gcongr
      _ = C * N * N * ‖u‖ * ‖v‖ := by ring
  -- measurability
  have hm0 : ∀ z', AEStronglyMeasurable (fun x => h x z') P := fun z' =>
    aestronglyMeasurable_integral_gauss hK hL (hf.contDiff.continuous.comp
      (continuous_affine_triple z'))
  have hi : ∀ z', Integrable (fun x => h x z') P := fun z' =>
    Integrable.of_bound (hm0 z') C (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]
      refine (abs_integral_le_integral_abs).trans ?_
      refine (integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
        (integrable_const C) (Eventually.of_forall fun G => hf.bound _)).trans ?_
      simp)
  have hm1 : ∀ z', AEStronglyMeasurable (fun x => fderiv ℝ (h x) z') P := by
    intro z'
    refine aestronglyMeasurable_clm_of_apply fun u => ?_
    have he : (fun x => fderiv ℝ (h x) z' u) = fun x => ∫ G,
        fderiv ℝ f (lmul (K x) z' + lmul (L x) G) (lmul (K x) u) ∂matCircularLaw N p :=
      funext fun x => (hD x).2.1 z' u
    rw [he]
    exact aestronglyMeasurable_integral_gauss
      (Ψ := fun q => fderiv ℝ f (lmul q.1 z' + lmul q.2.1 q.2.2) (lmul q.1 u)) hK hL
      ((hf1c.comp (continuous_affine_triple z')).clm_apply (continuous_lmul_fst u))
  have hm2 : ∀ z', AEStronglyMeasurable (fun x => fderiv ℝ (fderiv ℝ (h x)) z') P := by
    intro z'
    refine aestronglyMeasurable_clm_of_apply fun u => ?_
    refine aestronglyMeasurable_clm_of_apply fun v => ?_
    have he : (fun x => fderiv ℝ (fderiv ℝ (h x)) z' u v) = fun x => ∫ G,
        fderiv ℝ (fderiv ℝ f) (lmul (K x) z' + lmul (L x) G) (lmul (K x) u) (lmul (K x) v)
          ∂matCircularLaw N p :=
      funext fun x => (hD x).2.2 z' u v
    rw [he]
    exact aestronglyMeasurable_integral_gauss
      (Ψ := fun q => fderiv ℝ (fderiv ℝ f) (lmul q.1 z' + lmul q.2.1 q.2.2) (lmul q.1 u)
        (lmul q.1 v)) hK hL
      (((hf2c.comp (continuous_affine_triple z')).clm_apply (continuous_lmul_fst u)).clm_apply
        (continuous_lmul_fst v))
  obtain ⟨-, hd1, hd2⟩ := integral_contDiff_two (P := P) (h := h)
    (Eventually.of_forall fun x => (hD x).1) hb1 hb2 hm0 hi hm1 hm2
  exact integral_refGenerator r κ s z (hm1 z) (hm2 z) (hb1.mono fun x hx => hx z)
    (hb2.mono fun x hx => hx z) (hd1 z) (hd2 z)

/-!
## The reflected flow
-/

variable {S : Type} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]
  {r : ℝ → Fin N → Fin N → ℝ} {κ : ℝ → Fin N → ℝ} {a c : ℝ}
  {𝓝 : ℝ≥0 → DriverSample S (RotIdx N) → Matrix (Fin N) (Fin N) ℂ}

omit [MeasurableSpace S] in
theorem refSemigroup_integrand (f : RefState N p → ℝ) (s : ℝ) (y : DriverSample S (RotIdx N))
    (z' : RefState N p) :
    ∫ G, f (lmul (refKernel c 𝓝 s y) z' + lmul (refFactor c 𝓝 s y) G) ∂matCircularLaw N p =
      Ftil f z' (𝓝 (c - s).toNNReal y) := by
  simp only [refFactor, refKernel, conjTranspose_conjTranspose]
  rfl

omit [IsProbabilityMeasure μ] in
/-- The contraction along the flow: `opNorm (𝓝_tᴴ 𝓝_t) ≤ e^{-bt}` for `t ∈ [0, c-a]`, a.s. -/
theorem ae_opNorm_gram_le (hcon : KernelContracts μ κ a c (refKernel c 𝓝)) {b : ℝ}
    (hfloor : ∀ x ∈ Icc a c, ∀ k, b ≤ κ x k) :
    ∀ᵐ y ∂driverLaw (κ := RotIdx N) μ, ∀ t ∈ Icc 0 (c - a),
      opNorm (gram (𝓝 t.toNNReal y)) ≤ Real.exp (-(b * t)) := by
  filter_upwards [opNorm_kernel_le hcon hfloor] with y hy t ht
  have hs : c - t ∈ Icc a c := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have h := hy (c - t) hs
  simp only [refKernel, sub_sub_cancel, conjTranspose_conjTranspose] at h
  exact h

theorem driftC_eq {t : ℝ} (ht : t ∈ Icc 0 (c - a)) :
    driftC a c r κ t.toNNReal = rotationDrift (r (c - t)) (κ (c - t)) := by
  unfold driftC reflectRate reflectDamp
  rw [Real.coe_toNNReal _ ht.1, bwClampTime_of_mem ⟨by linarith [ht.1], by linarith [ht.2]⟩]
  ring_nf

theorem noiseC_eq {t : ℝ} (ht : t ∈ Icc 0 (c - a)) (α : RotIdx N) :
    noiseC a c r α t.toNNReal = rotationNoise (r (c - t)) α := by
  unfold noiseC reflectRate
  rw [Real.coe_toNNReal _ ht.1, bwClampTime_of_mem ⟨by linarith [ht.1], by linarith [ht.2]⟩]
  ring_nf

theorem stronglyMeasurable_flow
    (h𝓝 : IsRotationFlow μ (reflectRate a c r) (reflectDamp a c κ) a c a 𝓝) (t : ℝ≥0) :
    StronglyMeasurable (𝓝 t) :=
  (h𝓝.1.adapted t).mono ((driverAugmented (κ := RotIdx N) μ).le t)

/-- **The reflected backward function has the generator as derivative** at `t₀ ∈ (0, c-a)`:
`d/dt g_{c-t}(z) = refGenerator r κ (c-t) g_{c-t} z`. -/
theorem hasDerivAt_refSemigroup_reflected
    (hIto : ItoFormulaFor (S := S) (κ := RotIdx N) μ (Matrix (Fin N) (Fin N) ℂ) ℝ)
    (hIBP : MultivariateGaussianIBP) {b : ℝ} (hac : a ≤ c) (hb0 : 0 < b)
    (hr : ContinuousOn r (Icc a c)) (hκ : ContinuousOn κ (Icc a c))
    (hrs : ∀ x k l, r x k l = r x l k) (hr0 : ∀ x k l, 0 ≤ r x k l) (hκ0 : ∀ x k, 0 ≤ κ x k)
    (hfloor : ∀ x ∈ Icc a c, ∀ k, b ≤ κ x k)
    (h𝓝 : IsRotationFlow μ (reflectRate a c r) (reflectDamp a c κ) a c a 𝓝)
    (hcon : KernelContracts μ κ a c (refKernel c 𝓝)) {C : ℝ} {f : RefState N p → ℝ}
    (hf : IsC2BoundedBy C f) (z : RefState N p) {t₀ : ℝ} (ht₀ : 0 < t₀) (ht₀a : t₀ < c - a) :
    HasDerivAt (fun t => refSemigroup μ (refKernel c 𝓝) (refFactor c 𝓝) f (c - t) z)
      (refGenerator r κ (c - t₀) (refSemigroup μ (refKernel c 𝓝) (refFactor c 𝓝) f (c - t₀))
        z) t₀ := by
  set P := driverLaw (κ := RotIdx N) μ with hP
  have hgram := ae_opNorm_gram_le hcon hfloor
  set ρ₁ := Real.exp (-(b * (t₀ / 2))) with hρ₁
  have hρ₁1 : ρ₁ < 1 := by
    have : 0 < b * (t₀ / 2) := by positivity
    rw [hρ₁, ← Real.exp_zero]
    exact Real.exp_lt_exp.2 (by linarith)
  have hle_ρ : ∀ t, t₀ / 2 ≤ t → Real.exp (-(b * t)) ≤ ρ₁ := fun t ht =>
    Real.exp_le_exp.2 (by nlinarith)
  obtain ⟨χ, hχd, hχr, hχc, hχs, hχ1⟩ := exists_cutoff (N := N) hρ₁1
  set φ := cutF χ f z with hφdef
  have hφ : ContDiff ℝ 2 φ := contDiff_cutF hχd hχs hf z
  have hφc : HasCompactSupport φ := hχc.mul_right
  -- Itô's formula and the mean identity
  have hX := isNativeItoProcess_comp hIto h𝓝 hφ
  obtain ⟨CB, hCB⟩ := exists_driftFn_bound hac hr hκ hφ hφc
  have hcont : Continuous fun s : ℝ => ∫ x, driftFn φ (driftC a c r κ s.toNNReal)
      (fun α => noiseC a c r α s.toNNReal) (𝓝 s.toNNReal x) ∂P := by
    refine continuous_of_dominated (bound := fun _ => CB) (fun s => ?_)
      (fun s => Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hCB _ _)
      (integrable_const CB) ?_
    · exact (continuous_driftFn hφ).comp_aestronglyMeasurable
        (aestronglyMeasurable_const.prodMk (aestronglyMeasurable_const.prodMk
          (stronglyMeasurable_flow h𝓝 _).aestronglyMeasurable))
    · filter_upwards [h𝓝.1.continuous] with x hx
      exact (continuous_driftFn hφ).comp ((continuous_driftC hac hr hκ).prodMk
        ((continuous_pi fun α => continuous_noiseC hac hr α).prodMk
          (hx.comp continuous_real_toNNReal)))
  have hderiv := hasDerivAt_mean_of_ito hX (fun t x => abs_cutF_le hχr hf z (𝓝 t x))
    (fun t x => hCB t (𝓝 t x)) hcont ht₀
  -- the backward function agrees with `E φ(𝓝_t)` near `t₀`
  have hfeq : ∀ t ∈ Icc (t₀ / 2) (c - a),
      refSemigroup μ (refKernel c 𝓝) (refFactor c 𝓝) f (c - t) z =
        ∫ x, φ (𝓝 t.toNNReal x) ∂P := by
    intro t ht
    have ht' : t ∈ Icc 0 (c - a) := ⟨by linarith [ht.1], ht.2⟩
    unfold refSemigroup
    simp only [refSemigroup_integrand, sub_sub_cancel]
    refine integral_congr_ae ?_
    filter_upwards [hgram] with y hy
    have hn := (hy t ht').trans (hle_ρ t ht.1)
    exact ((cutF_eventuallyEq (f := f) (z := z) (hχ1 _ hn)).eq_of_nhds).symm
  have hΦ : HasDerivAt (fun t => refSemigroup μ (refKernel c 𝓝) (refFactor c 𝓝) f (c - t) z)
      (∫ x, driftFn φ (driftC a c r κ t₀.toNNReal) (fun α => noiseC a c r α t₀.toNNReal)
        (𝓝 t₀.toNNReal x) ∂P) t₀ := by
    refine hderiv.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds (show t₀ / 2 < t₀ by linarith) ht₀a] with t ht
    exact hfeq t ⟨ht.1.le, ht.2.le⟩
  refine hΦ.congr_deriv ?_
  -- identification of the mean drift
  have ht₀m : t₀ ∈ Icc 0 (c - a) := ⟨ht₀.le, ht₀a.le⟩
  have hpt : ∀ᵐ x ∂P, driftFn φ (driftC a c r κ t₀.toNNReal)
      (fun α => noiseC a c r α t₀.toNNReal) (𝓝 t₀.toNNReal x) =
      refGenerator r κ (c - t₀) (fun z' => ∫ G, f (lmul (refKernel c 𝓝 (c - t₀) x) z' +
        lmul (refFactor c 𝓝 (c - t₀) x) G) ∂matCircularLaw N p) z := by
    filter_upwards [hgram] with x hx
    set n := 𝓝 t₀.toNNReal x with hn
    have hnρ : opNorm (gram n) ≤ ρ₁ := (hx t₀ ht₀m).trans (hle_ρ t₀ (by linarith))
    have hn1 : opNorm (gram n) < 1 := hnρ.trans_lt hρ₁1
    have heq : φ =ᶠ[nhds n] Ftil f z := cutF_eventuallyEq (hχ1 n hnρ)
    have h1 : fderiv ℝ φ n = fderiv ℝ (Ftil f z) n := heq.fderiv_eq
    have h2 : fderiv ℝ (fderiv ℝ φ) n = fderiv ℝ (fderiv ℝ (Ftil f z)) n := heq.fderiv.fderiv_eq
    have hfun : (fun z' => ∫ G, f (lmul (refKernel c 𝓝 (c - t₀) x) z' +
        lmul (refFactor c 𝓝 (c - t₀) x) G) ∂matCircularLaw N p) =
        fun z' => ∫ G, f (lmul nᴴ z' + lmul (sqrtOneSub (nᴴ * n)) G) ∂matCircularLaw N p := by
      funext z'
      rw [refSemigroup_integrand, sub_sub_cancel]
      rfl
    rw [hfun]
    unfold driftFn
    rw [h1, h2, driftC_eq ht₀m]
    simp only [noiseC_eq ht₀m]
    exact drift_eq_refGenerator hIBP hf z hn1 (r (c - t₀)) (κ (c - t₀)) (hrs _) (hr0 _)
      (hκ0 _)
  rw [integral_congr_ae hpt]
  have hs : c - t₀ ∈ Icc a c := ⟨by linarith, by linarith⟩
  exact integral_refGenerator_gauss (measurable_refKernel h𝓝 _) (measurable_refFactor h𝓝 _)
    (kernel_entry_le hκ0 hcon _ hs) hf r κ (c - t₀) z

end Backward

/-- **The backward Kolmogorov equation of the reference flow.** For the reflected rotation flow
`𝓝` with contracting kernel `K_s = (𝓝_{c-s})ᴴ` and the factor `L_s = (I - K_s K_sᴴ)^{1/2}`,
every bounded-`C²` test satisfies `∂_s g_s(z) = -refGenerator r κ s g_s z` on `(a,c)`. -/
theorem backwardEquation_holds
    (hIto : ∀ (S : Type) [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ],
      ItoFormulaFor (S := S) (κ := RotIdx N) μ (Matrix (Fin N) (Fin N) ℂ) ℝ)
    (hIBP : MultivariateGaussianIBP)
    {S : Type} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]
    {r : ℝ → Fin N → Fin N → ℝ} {κ : ℝ → Fin N → ℝ} {a c b : ℝ} (hac : a ≤ c) (hb0 : 0 < b)
    (hr : ContinuousOn r (Icc a c)) (hκ : ContinuousOn κ (Icc a c))
    (hrs : ∀ x k l, r x k l = r x l k) (hr0 : ∀ x k l, 0 ≤ r x k l) (hκ0 : ∀ x k, 0 ≤ κ x k)
    (hfloor : ∀ x ∈ Icc a c, ∀ k, b ≤ κ x k)
    {𝓝 : ℝ≥0 → DriverSample S (RotIdx N) → Matrix (Fin N) (Fin N) ℂ}
    (h𝓝 : IsRotationFlow μ (reflectRate a c r) (reflectDamp a c κ) a c a 𝓝)
    (hcon : KernelContracts μ κ a c (refKernel c 𝓝)) :
    BackwardEquationHolds μ r κ a c (refKernel c 𝓝) (refFactor c 𝓝) := by
  intro p C f hf s₀ hs₀ z
  have h := hasDerivAt_refSemigroup_reflected (hIto S μ) hIBP hac hb0 hr hκ hrs hr0 hκ0 hfloor
    h𝓝 hcon hf z (t₀ := c - s₀) (by linarith [hs₀.2]) (by linarith [hs₀.1])
  rw [sub_sub_cancel] at h
  have hc : HasDerivAt (fun x : ℝ => c - x) (-1) s₀ := by
    simpa using (hasDerivAt_id s₀).const_sub c
  have h2 := h.comp s₀ hc
  simp only [Function.comp_def, sub_sub_cancel, mul_neg, mul_one] at h2
  exact h2

end BlockBand.Palm.ReferenceFlow
