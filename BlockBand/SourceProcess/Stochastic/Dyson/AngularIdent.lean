module

public import BlockBand.SourceProcess.Stochastic.Dyson.AngularState

/-!
# Zero Itô drift of the exponential test functions on the augmented Dyson state

On the augmented state `y = (λ, X, V₀, V₁, t)` with characteristics `plusDrift θ f`, `plusCov`:
* `Phi h θ y = e^{c_θ t} h(θ·λ - V₀)` with `c_θ = |θ|²/(2N)` and `h'' = -h` (`h = cos, sin`):
  this is the real/imaginary part of `exp(iθ·W_t + |θ|²t/(2N))` with `W = λ - ∫ b(λ)`;
* `Pfun h θ f = Phi h θ · (f(X) - V₁)`, `V₁ = ∫ 𝒜 f`.
Both have zero Itô drift at **every** state (`itoDrift_Phi`, `itoDrift_Pfun`): the `λ`-noise
cancels the clock, the drift of `V₀` cancels the eigenvalue drift, `𝒜 f` is the overlap
generator (`angularGenerator_eq`), and the cross terms vanish because the `λ`–`X` covariance
block of `dysonStateCov` is zero.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson.Angular
open Filter Topology
open scoped NNReal ContDiff
open BlockBand.Internal.Contracts.Transmission BlockBand.SourceProcess.Stochastic.Bridges

variable {N : ℕ}

/-- `c_θ = |θ|² / (2N)`. -/
def cθ (θ : Fin N → ℝ) : ℝ := (∑ i, θ i ^ 2) / (2 * N)

/-- Clock factor `e^{c t}`. -/
def Efun (N : ℕ) (c : ℝ) (y : Fin ((N + N) + 3) → ℝ) : ℝ := Real.exp (c * prV N 2 y)

/-- `e^{c_θ t} h(θ·λ - V₀)`. -/
def Phi (h : ℝ → ℝ) (θ : Fin N → ℝ) (y : Fin ((N + N) + 3) → ℝ) : ℝ :=
  Efun N (cθ θ) y * h (ell θ y)

/-- `f(X) - V₁`. -/
def g2 (f : (Fin N → ℝ) → ℝ) (y : Fin ((N + N) + 3) → ℝ) : ℝ := f (prX N y) - prV N 1 y

/-- `Phi · (f(X) - V₁)`. -/
def Pfun (h : ℝ → ℝ) (θ : Fin N → ℝ) (f : (Fin N → ℝ) → ℝ) (y : Fin ((N + N) + 3) → ℝ) : ℝ :=
  Phi h θ y * g2 f y

/-- Admissible trigonometric profiles: `h' = Dh`, `h'' = -h`. -/
structure Trig (h h' : ℝ → ℝ) : Prop where
  d : ∀ x, HasDerivAt h (h' x) x
  d' : ∀ x, HasDerivAt h' (-h x) x
  cont : Continuous h

theorem trig_cos : Trig Real.cos (fun x => -Real.sin x) :=
  ⟨Real.hasDerivAt_cos, fun x => (Real.hasDerivAt_sin x).neg, Real.continuous_cos⟩

theorem trig_sin : Trig Real.sin Real.cos :=
  ⟨Real.hasDerivAt_sin, Real.hasDerivAt_cos, Real.continuous_sin⟩

/-!
### Smoothness and derivatives
-/

theorem hasDerivAt_exp_mul (c x : ℝ) :
    HasDerivAt (fun x => Real.exp (c * x)) (c * Real.exp (c * x)) x := by
  have := ((hasDerivAt_id x).const_mul c).exp
  simpa [mul_comm] using this

theorem hasDerivAt_c_exp_mul (c x : ℝ) :
    HasDerivAt (fun x => c * Real.exp (c * x)) (c * (c * Real.exp (c * x))) x :=
  (hasDerivAt_exp_mul c x).const_mul c

theorem contDiff_Efun (c : ℝ) : ContDiff ℝ 2 (Efun N c) :=
  Real.contDiff_exp.comp (contDiff_const.mul (prV N 2).contDiff)

theorem contDiff_trig {h h' : ℝ → ℝ} (hh : Trig h h') : ContDiff ℝ 2 h :=
  contDiff_real_of_deriv hh.d hh.d' hh.cont.neg

theorem contDiff_hell {h h' : ℝ → ℝ} (hh : Trig h h') (θ : Fin N → ℝ) :
    ContDiff ℝ 2 fun y => h (ell θ y) :=
  (contDiff_trig hh).comp (ell θ).contDiff

theorem contDiff_g2 {f : (Fin N → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) : ContDiff ℝ 2 (g2 f) :=
  (hf.comp (prX N).contDiff).sub (prV N 1).contDiff

theorem contDiff_Phi {h h' : ℝ → ℝ} (hh : Trig h h') (θ : Fin N → ℝ) :
    ContDiff ℝ 2 (Phi h θ) :=
  (contDiff_Efun _).mul (contDiff_hell hh θ)

theorem contDiff_Pfun {h h' : ℝ → ℝ} (hh : Trig h h') (θ : Fin N → ℝ)
    {f : (Fin N → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) : ContDiff ℝ 2 (Pfun h θ f) :=
  (contDiff_Phi hh θ).mul (contDiff_g2 hf)

theorem fderiv_Efun (c : ℝ) (y v : Fin ((N + N) + 3) → ℝ) :
    fderiv ℝ (Efun N c) y v = c * Efun N c y * v (cV N 2) := by
  rw [show Efun N c = fun y => (fun x => Real.exp (c * x)) (prV N 2 y) from rfl,
    fderiv_comp_clm_apply (prV N 2) (hasDerivAt_exp_mul c _).differentiableAt,
    fderiv_real_apply (hasDerivAt_exp_mul c)]
  simp

theorem fderiv2_Efun (c : ℝ) (y u v : Fin ((N + N) + 3) → ℝ) :
    fderiv ℝ (fderiv ℝ (Efun N c)) y u v = c * (c * Efun N c y) * u (cV N 2) * v (cV N 2) := by
  have hc2 : ContDiff ℝ 2 fun x : ℝ => Real.exp (c * x) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  rw [show Efun N c = fun y => (fun x => Real.exp (c * x)) (prV N 2 y) from rfl,
    fderiv2_comp_clm_apply (h := fun x => Real.exp (c * x)) (prV N 2) hc2.contDiffAt,
    fderiv2_real_apply (hasDerivAt_exp_mul c) (hasDerivAt_c_exp_mul c)]
  simp

theorem fderiv_hell {h h' : ℝ → ℝ} (hh : Trig h h') (θ : Fin N → ℝ)
    (y v : Fin ((N + N) + 3) → ℝ) :
    fderiv ℝ (fun y => h (ell θ y)) y v = h' (ell θ y) * ell θ v := by
  rw [fderiv_comp_clm_apply (ell θ) (hh.d _).differentiableAt, fderiv_real_apply hh.d]

theorem fderiv2_hell {h h' : ℝ → ℝ} (hh : Trig h h') (θ : Fin N → ℝ)
    (y u v : Fin ((N + N) + 3) → ℝ) :
    fderiv ℝ (fderiv ℝ fun y => h (ell θ y)) y u v = -h (ell θ y) * ell θ u * ell θ v := by
  rw [fderiv2_comp_clm_apply (ell θ) (contDiff_trig hh).contDiffAt,
    fderiv2_real_apply hh.d hh.d']

theorem fderiv_g2 {f : (Fin N → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (y v : Fin ((N + N) + 3) → ℝ) :
    fderiv ℝ (g2 f) y v = fderiv ℝ f (prX N y) (prX N v) - v (cV N 1) := by
  have h1 : DifferentiableAt ℝ (fun y => f (prX N y)) y :=
    (hf.comp (prX N).contDiff).contDiffAt.differentiableAt (by norm_num)
  rw [show g2 f = fun y => f (prX N y) - prV N 1 y from rfl,
    fderiv_fun_sub h1 (prV N 1).differentiableAt]
  simp only [FunLike.coe_sub, Pi.sub_apply, ContinuousLinearMap.fderiv, prV_apply]
  rw [fderiv_comp_clm_apply (prX N) (hf.contDiffAt.differentiableAt (by norm_num))]

theorem fderiv2_g2 {f : (Fin N → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (y u v : Fin ((N + N) + 3) → ℝ) :
    fderiv ℝ (fderiv ℝ (g2 f)) y u v = fderiv ℝ (fderiv ℝ f) (prX N y) (prX N u) (prX N v) := by
  have hF : ContDiff ℝ 2 fun y => f (prX N y) := hf.comp (prX N).contDiff
  have hev : fderiv ℝ (g2 f) = fun y' => fderiv ℝ (fun y => f (prX N y)) y' - prV N 1 := by
    funext y'
    rw [show g2 f = fun y => f (prX N y) - prV N 1 y from rfl,
      fderiv_fun_sub (hF.contDiffAt.differentiableAt (by norm_num)) (prV N 1).differentiableAt,
      ContinuousLinearMap.fderiv]
  rw [hev, fderiv_sub_const, fderiv2_comp_clm_apply (prX N) hf.contDiffAt]

/-!
### Generators
-/

variable (θ : Fin N → ℝ) (f : (Fin N → ℝ) → ℝ) (y : Fin ((N + N) + 3) → ℝ)

theorem genL_Efun (c : ℝ) : genL (Efun N c) y (plusDrift θ f y) (plusCov y) = c * Efun N c y := by
  unfold genL
  rw [fderiv_Efun, plusDrift_cV2]
  simp_rw [fderiv2_Efun]
  rw [sum_plusCov]
  simp [single_cV_cL, single_cV_cX]

theorem genL_hell {h h' : ℝ → ℝ} (hh : Trig h h') :
    genL (fun y => h (ell θ y)) y (plusDrift θ f y) (plusCov y) = -(cθ θ * h (ell θ y)) := by
  unfold genL
  rw [fderiv_hell hh, ell_plusDrift]
  simp_rw [fderiv2_hell hh]
  rw [sum_plusCov]
  simp only [ell_single_cL, ell_single_cX, mul_zero, Finset.sum_const_zero, add_zero, cθ]
  have : ∀ i, -h (ell θ y) * θ i * θ i = -h (ell θ y) * θ i ^ 2 := fun i => by ring
  simp_rw [this, ← Finset.mul_sum]
  ring

theorem genL_g2 {f : (Fin N → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) :
    genL (g2 f) y (plusDrift θ f y) (plusCov y) = 0 := by
  unfold genL
  rw [fderiv_g2 hf, plusDrift_cV1, prX_plusDrift]
  simp_rw [fderiv2_g2 hf]
  rw [sum_plusCov]
  simp only [prX_single_cL, prX_single_cX, map_zero, Finset.sum_const_zero, mul_zero, zero_add]
  rw [angularGenerator_eq hf, prX_eq_xOf]
  ring

variable {θ y}

theorem fderiv_Phi_cX {h h' : ℝ → ℝ} (hh : Trig h h') (i : Fin N) :
    fderiv ℝ (Phi h θ) y (Pi.single (cX i) 1) = 0 := by
  rw [show Phi h θ = fun y => Efun N (cθ θ) y * h (ell θ y) from rfl,
    fderiv_mul_apply ((contDiff_Efun _).differentiable (by norm_num) _)
      ((contDiff_hell hh θ).differentiable (by norm_num) _), fderiv_Efun, fderiv_hell hh,
    ell_single_cX, single_cV_cX]
  ring

theorem fderiv_g2_cL {f : (Fin N → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (i : Fin N) :
    fderiv ℝ (g2 f) y (Pi.single (cL i) 1) = 0 := by
  rw [fderiv_g2 hf, prX_single_cL, single_cV_cL]; simp

variable (θ y)

theorem genL_Phi {h h' : ℝ → ℝ} (hh : Trig h h') :
    genL (Phi h θ) y (plusDrift θ f y) (plusCov y) = 0 := by
  rw [show Phi h θ = fun y => Efun N (cθ θ) y * h (ell θ y) from rfl,
    genL_mul (contDiff_Efun _).contDiffAt (contDiff_hell hh θ).contDiffAt, genL_Efun,
    genL_hell θ f y hh, sum_plusCov]
  simp only [fderiv_Efun, fderiv_hell hh, ell_single_cX, single_cV_cL, single_cV_cX, mul_zero,
    zero_mul, add_zero, Finset.sum_const_zero]
  ring

theorem genL_Pfun {h h' : ℝ → ℝ} (hh : Trig h h') {f : (Fin N → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) :
    genL (Pfun h θ f) y (plusDrift θ f y) (plusCov y) = 0 := by
  rw [show Pfun h θ f = fun y => Phi h θ y * g2 f y from rfl,
    genL_mul (contDiff_Phi hh θ).contDiffAt (contDiff_g2 hf).contDiffAt, genL_g2 θ y hf,
    genL_Phi θ f y hh, sum_plusCov]
  simp only [fderiv_g2_cL hf, fderiv_Phi_cX hh, mul_zero, zero_mul, add_zero,
    Finset.sum_const_zero]

/-- **Zero Itô drift of `Phi`.** -/
theorem itoDrift_Phi {h h' : ℝ → ℝ} (hh : Trig h h') (t : ℝ≥0) :
    itoDrift (fun p : ℝ × (Fin ((N + N) + 3) → ℝ) => Phi h θ p.2) y t (plusDrift θ f y)
      (plusCov y) = 0 := by
  rw [itoDrift_eq_genL (contDiff_Phi hh θ).contDiffAt, genL_Phi θ f y hh]

/-- **Zero Itô drift of `Pfun`.** -/
theorem itoDrift_Pfun {h h' : ℝ → ℝ} (hh : Trig h h') {f : (Fin N → ℝ) → ℝ}
    (hf : ContDiff ℝ 2 f) (t : ℝ≥0) :
    itoDrift (fun p : ℝ × (Fin ((N + N) + 3) → ℝ) => Pfun h θ f p.2) y t (plusDrift θ f y)
      (plusCov y) = 0 := by
  rw [itoDrift_eq_genL (contDiff_Pfun hh θ hf).contDiffAt, genL_Pfun θ y hh hf]

end BlockBand.SourceProcess.Stochastic.Dyson.Angular
