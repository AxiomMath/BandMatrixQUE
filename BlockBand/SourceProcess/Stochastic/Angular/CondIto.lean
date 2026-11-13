module

public import BlockBand.SourceProcess.Stochastic.Angular.CondState
public import BlockBand.SourceProcess.Stochastic.Dyson.ItoIdentities

/-!
# Complex angular martingale problem: zero Itô drift of the conditioning test functions

On the conditioning state `z = (y, V₀, V₁, t)`, with drift `condDrift θ A` and covariance
`condCov N`, the test functions are:
* `Phic h θ z = e^{c_θ t} h(θ·λ(y) - V₀)` with `c_θ = |θ|²/(2N)` and `h'' = -h`;
* `Pcond h θ φ z = Phic h θ z · (φ(y) - V₁)`.

Both have zero Itô drift at every state with `y ∈ simpleSet N` (`itoDrift_Phic`,
`itoDrift_Pcond`), for `0 < N`. The inputs are `lapl_lam`, `sum_fderiv_lam_mul`, and the two
hypotheses `Δφ = 2N A`, `⟨∇φ, ∇λ_i⟩ = 0` of `GenericConditioning`. The tool is the second-order
chain rule `fderiv2_comp_real_apply` for `h ∘ k` with a nonlinear `k`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.ComplexAngular
open Matrix Filter Topology
open scoped NNReal
open BlockBand.Internal.Contracts.Transmission BlockBand.SourceProcess.Stochastic.Bridges
open BlockBand.SourceProcess.Stochastic.Dyson
open BlockBand.SourceProcess.Stochastic.Dyson.Angular (genL genL_mul itoDrift_eq_genL
  fderiv_mul_apply fderiv2_eq diff_fderiv_apply fderiv_real_apply fderiv_comp_clm_apply
  fderiv2_comp_clm_apply Trig cθ contDiff_trig)

/-!
### Second-order chain rule with a one-variable outer function
-/

section Chain
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_comp_real_apply {h h' : ℝ → ℝ} (hd : ∀ x, HasDerivAt h (h' x) x) {k : E → ℝ}
    {y : E} (hk : DifferentiableAt ℝ k y) (v : E) :
    fderiv ℝ (fun y => h (k y)) y v = h' (k y) * fderiv ℝ k y v := by
  rw [show (fun y => h (k y)) = h ∘ k from rfl,
    fderiv_comp y (hd (k y)).differentiableAt hk]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
  exact fderiv_real_apply hd _ _

theorem fderiv2_comp_real_apply {h h' h'' : ℝ → ℝ} (hd : ∀ x, HasDerivAt h (h' x) x)
    (hd' : ∀ x, HasDerivAt h' (h'' x) x) (hc : ContDiff ℝ 2 h) {k : E → ℝ} {y : E}
    (hk : ContDiffAt ℝ 2 k y) (u v : E) :
    fderiv ℝ (fderiv ℝ fun y => h (k y)) y u v =
      h'' (k y) * fderiv ℝ k y u * fderiv ℝ k y v + h' (k y) * fderiv ℝ (fderiv ℝ k) y u v := by
  have hhk : ContDiffAt ℝ 2 (fun y => h (k y)) y := hc.contDiffAt.comp y hk
  rw [fderiv2_eq hhk, fderiv2_eq hk]
  have hev : (fun y' => fderiv ℝ (fun y => h (k y)) y' v) =ᶠ[𝓝 y]
      fun y' => h' (k y') * fderiv ℝ k y' v := by
    filter_upwards [hk.eventually (by simp)] with y' hy'
    exact fderiv_comp_real_apply hd (hy'.differentiableAt (by norm_num)) v
  rw [hev.fderiv_eq]
  have d1 : DifferentiableAt ℝ (fun y' => h' (k y')) y :=
    (hd' (k y)).differentiableAt.comp y (hk.differentiableAt (by norm_num))
  rw [fderiv_mul_apply d1 (diff_fderiv_apply hk v) u,
    fderiv_comp_real_apply hd' (hk.differentiableAt (by norm_num)) u]
  ring

variable {d : ℕ}

/-- **Chain rule for the generator.** -/
theorem genL_comp_real {h h' h'' : ℝ → ℝ} (hd : ∀ x, HasDerivAt h (h' x) x)
    (hd' : ∀ x, HasDerivAt h' (h'' x) x) (hc : ContDiff ℝ 2 h) {k : (Fin d → ℝ) → ℝ}
    {y : Fin d → ℝ} (hk : ContDiffAt ℝ 2 k y) (b : Fin d → ℝ) (a : Matrix (Fin d) (Fin d) ℝ) :
    genL (fun y => h (k y)) y b a = h' (k y) * genL k y b a +
      (1 / 2 : ℝ) * h'' (k y) * ∑ i, ∑ j, a i j *
        (fderiv ℝ k y (Pi.single i 1) * fderiv ℝ k y (Pi.single j 1)) := by
  unfold genL
  rw [fderiv_comp_real_apply hd (hk.differentiableAt (by norm_num))]
  simp_rw [fderiv2_comp_real_apply hd hd' hc hk]
  have e : ∀ i j, a i j * (h'' (k y) * fderiv ℝ k y (Pi.single i 1) *
      fderiv ℝ k y (Pi.single j 1) + h' (k y) * fderiv ℝ (fderiv ℝ k) y (Pi.single i 1)
        (Pi.single j 1)) = h'' (k y) * (a i j * (fderiv ℝ k y (Pi.single i 1) *
      fderiv ℝ k y (Pi.single j 1))) +
        h' (k y) * (a i j * fderiv ℝ (fderiv ℝ k) y (Pi.single i 1) (Pi.single j 1)) :=
    fun _ _ => by ring
  simp_rw [e, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end Chain

variable {N : ℕ}

/-!
### `θ·λ`
-/

theorem contDiffAt_thLam {θ : Fin N → ℝ} {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) :
    ContDiffAt ℝ 2 (thLam θ) y := by
  unfold thLam
  exact ContDiffAt.sum fun i _ => contDiffAt_const.mul (contDiffAt_eigenvalue hy i)

theorem fderiv_thLam_eq {θ : Fin N → ℝ} {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) :
    fderiv ℝ (thLam θ) y = ∑ i, θ i • fderiv ℝ (lam N i) y := by
  have hd : ∀ i, DifferentiableAt ℝ (lam N i) y := fun i =>
    (contDiffAt_eigenvalue (n := 1) hy i).differentiableAt (by norm_num)
  rw [show thLam θ = fun y => ∑ i, θ i * lam N i y from rfl,
    fderiv_fun_sum fun i _ => (hd i).const_mul (θ i)]
  exact Finset.sum_congr rfl fun i _ => fderiv_const_mul (hd i) (θ i)

theorem fderiv_thLam {θ : Fin N → ℝ} {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N)
    (v : Fin (N * N) → ℝ) : fderiv ℝ (thLam θ) y v = ∑ i, θ i * fderiv ℝ (lam N i) y v := by
  rw [fderiv_thLam_eq hy]; simp

theorem fderiv2_thLam {θ : Fin N → ℝ} {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N)
    (u v : Fin (N * N) → ℝ) : fderiv ℝ (fderiv ℝ (thLam θ)) y u v =
      ∑ i, θ i * fderiv ℝ (fderiv ℝ (lam N i)) y u v := by
  have hev : fderiv ℝ (thLam θ) =ᶠ[𝓝 y] fun y' => ∑ i, θ i • fderiv ℝ (lam N i) y' := by
    filter_upwards [isOpen_simpleSet.mem_nhds hy] with y' hy' using fderiv_thLam_eq hy'
  have hd : ∀ i, DifferentiableAt ℝ (fderiv ℝ (lam N i)) y := fun i =>
    ((contDiffAt_eigenvalue (n := 2) hy i).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)
  have hs : HasFDerivAt (fun y' => ∑ i, θ i • fderiv ℝ (lam N i) y')
      (∑ i, θ i • fderiv ℝ (fderiv ℝ (lam N i)) y) y :=
    HasFDerivAt.fun_sum fun i _ => (hd i).hasFDerivAt.const_smul (θ i)
  rw [hev.fderiv_eq, hs.fderiv]
  simp

/-- `|∇(θ·λ)|² = |θ|²`. -/
theorem sum_fderiv_thLam_sq {θ : Fin N → ℝ} {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) :
    ∑ a, fderiv ℝ (thLam θ) y (Pi.single a 1) * fderiv ℝ (thLam θ) y (Pi.single a 1) =
      ∑ i, θ i ^ 2 := by
  simp_rw [fderiv_thLam hy, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  have e : ∀ j, ∑ a, θ i * fderiv ℝ (lam N i) y (Pi.single a 1) *
      (θ j * fderiv ℝ (lam N j) y (Pi.single a 1)) = θ i * θ j * (if i = j then 1 else 0) :=
    fun j => by
      rw [← sum_fderiv_lam_mul hy i j, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by ring
  simp_rw [e]; simp [sq]

/-- `Δ(θ·λ) = 2N θ·b(λ)`. -/
theorem lapl_thLam (hN : (N : ℝ) ≠ 0) {θ : Fin N → ℝ} {y : Fin (N * N) → ℝ}
    (hy : y ∈ simpleSet N) :
    ∑ a, fderiv ℝ (fderiv ℝ (thLam θ)) y (Pi.single a 1) (Pi.single a 1) =
      2 * N * ∑ i, θ i * dysonDrift N (fun j => lam N j y) i := by
  simp_rw [fderiv2_thLam hy]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, lapl_lam hy]
  conv_rhs => rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : (N : ℝ) * (N : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hN
  simp only [dysonDrift, one_div]
  linear_combination (-(2 * θ i * ∑ j ∈ Finset.univ.erase i, (lam N i y - lam N j y)⁻¹)) * h1

/-!
### The test functions on the state
-/

/-- The clock factor `e^{c t}`. -/
def Ec (N : ℕ) (c : ℝ) (z : Fin (N * N + 3) → ℝ) : ℝ := Real.exp (c * stW N 2 z)

/-- A scalar of the coordinates minus an auxiliary coordinate: `ψ(y) - V_k`. -/
def yfun (ψ : (Fin (N * N) → ℝ) → ℝ) (k : Fin 3) (z : Fin (N * N + 3) → ℝ) : ℝ :=
  ψ (stY N z) - stW N k z

/-- `e^{c_θ t} h(θ·λ(y) - V₀)`. -/
def Phic (h : ℝ → ℝ) (θ : Fin N → ℝ) (z : Fin (N * N + 3) → ℝ) : ℝ :=
  Ec N (cθ θ) z * h (yfun (thLam θ) 0 z)

/-- `Phic · (φ(y) - V₁)`. -/
def Pcond (h : ℝ → ℝ) (θ : Fin N → ℝ) (φ : (Fin (N * N) → ℝ) → ℝ)
    (z : Fin (N * N + 3) → ℝ) : ℝ :=
  Phic h θ z * yfun φ 1 z

theorem contDiff_Ec (c : ℝ) : ContDiff ℝ 2 (Ec N c) :=
  Real.contDiff_exp.comp (contDiff_const.mul (stW N 2).contDiff)

theorem contDiffAt_yfun {ψ : (Fin (N * N) → ℝ) → ℝ} {z : Fin (N * N + 3) → ℝ}
    (hψ : ContDiffAt ℝ 2 ψ (stY N z)) (k : Fin 3) : ContDiffAt ℝ 2 (yfun ψ k) z :=
  (hψ.comp z (stY N).contDiff.contDiffAt).sub (stW N k).contDiff.contDiffAt

theorem fderiv_yfun {ψ : (Fin (N * N) → ℝ) → ℝ} {z : Fin (N * N + 3) → ℝ}
    (hψ : DifferentiableAt ℝ ψ (stY N z)) (k : Fin 3) (v : Fin (N * N + 3) → ℝ) :
    fderiv ℝ (yfun ψ k) z v = fderiv ℝ ψ (stY N z) (stY N v) - v (cstW N k) := by
  have hc : DifferentiableAt ℝ (fun z => ψ (stY N z)) z := hψ.comp z (stY N).differentiableAt
  rw [show yfun ψ k = fun z => ψ (stY N z) - stW N k z from rfl,
    fderiv_fun_sub hc (stW N k).differentiableAt,
    _root_.sub_apply, fderiv_comp_clm_apply (stY N) hψ,
    ContinuousLinearMap.fderiv, stW_apply]

theorem fderiv2_yfun {ψ : (Fin (N * N) → ℝ) → ℝ} {z : Fin (N * N + 3) → ℝ}
    (hψ : ContDiffAt ℝ 2 ψ (stY N z)) (k : Fin 3) (u v : Fin (N * N + 3) → ℝ) :
    fderiv ℝ (fderiv ℝ (yfun ψ k)) z u v =
      fderiv ℝ (fderiv ℝ ψ) (stY N z) (stY N u) (stY N v) := by
  have hc : ContDiffAt ℝ 2 (fun z => ψ (stY N z)) z := hψ.comp z (stY N).contDiff.contDiffAt
  have hev : fderiv ℝ (yfun ψ k) =ᶠ[𝓝 z] fun z' =>
      fderiv ℝ (fun z => ψ (stY N z)) z' - stW N k := by
    filter_upwards [hc.eventually (by simp)] with z' hz'
    rw [show yfun ψ k = fun z => ψ (stY N z) - stW N k z from rfl,
      fderiv_fun_sub (hz'.differentiableAt (by norm_num)) (stW N k).differentiableAt,
      ContinuousLinearMap.fderiv]
  rw [hev.fderiv_eq, fderiv_sub_const, fderiv2_comp_clm_apply (stY N) hψ]

theorem fderiv_yfun_cstY {ψ : (Fin (N * N) → ℝ) → ℝ} {z : Fin (N * N + 3) → ℝ}
    (hψ : DifferentiableAt ℝ ψ (stY N z)) (k : Fin 3) (a : Fin (N * N)) :
    fderiv ℝ (yfun ψ k) z (Pi.single (cstY a) 1) = fderiv ℝ ψ (stY N z) (Pi.single a 1) := by
  rw [fderiv_yfun hψ, stY_single_cstY, single_cstW_cstY, sub_zero]

theorem fderiv_Ec (c : ℝ) (z v : Fin (N * N + 3) → ℝ) :
    fderiv ℝ (Ec N c) z v = c * Ec N c z * v (cstW N 2) := by
  rw [show Ec N c = fun z => (fun x => Real.exp (c * x)) (stW N 2 z) from rfl,
    fderiv_comp_clm_apply (stW N 2) (Angular.hasDerivAt_exp_mul c _).differentiableAt,
    fderiv_real_apply (Angular.hasDerivAt_exp_mul c)]
  simp

theorem fderiv2_Ec (c : ℝ) (z u v : Fin (N * N + 3) → ℝ) :
    fderiv ℝ (fderiv ℝ (Ec N c)) z u v = c * (c * Ec N c z) * u (cstW N 2) * v (cstW N 2) := by
  have hc2 : ContDiff ℝ 2 fun x : ℝ => Real.exp (c * x) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  rw [show Ec N c = fun z => (fun x => Real.exp (c * x)) (stW N 2 z) from rfl,
    fderiv2_comp_clm_apply (h := fun x => Real.exp (c * x)) (stW N 2) hc2.contDiffAt,
    Angular.fderiv2_real_apply (Angular.hasDerivAt_exp_mul c) (Angular.hasDerivAt_c_exp_mul c)]
  simp

theorem fderiv_Ec_cstY (c : ℝ) (z : Fin (N * N + 3) → ℝ) (a : Fin (N * N)) :
    fderiv ℝ (Ec N c) z (Pi.single (cstY a) 1) = 0 := by
  rw [fderiv_Ec, single_cstW_cstY, mul_zero]

/-!
### Generators
-/

variable (θ : Fin N → ℝ) (A : (Fin (N * N) → ℝ) → ℝ) {z : Fin (N * N + 3) → ℝ}

theorem genL_yfun {ψ : (Fin (N * N) → ℝ) → ℝ} (hψ : ContDiffAt ℝ 2 ψ (stY N z)) (k : Fin 3) :
    genL (yfun ψ k) z (condDrift θ A z) (condCov N) = (1 / 2 : ℝ) * ((1 / (N : ℝ)) *
      ∑ a, fderiv ℝ (fderiv ℝ ψ) (stY N z) (Pi.single a 1) (Pi.single a 1)) -
        condVd θ A (stY N z) k := by
  unfold genL
  rw [fderiv_yfun (hψ.differentiableAt (by norm_num)), stY_condDrift, condDrift_cstW, map_zero]
  simp_rw [fderiv2_yfun hψ]
  rw [sum_condCov]
  simp only [stY_single_cstY]
  ring

theorem genL_Ec (c : ℝ) : genL (Ec N c) z (condDrift θ A z) (condCov N) = c * Ec N c z := by
  unfold genL
  rw [fderiv_Ec, condDrift_cstW]
  simp_rw [fderiv2_Ec]
  rw [sum_condCov]
  simp [single_cstW_cstY, condVd]

theorem genL_hk (hN : (N : ℝ) ≠ 0) {h h' : ℝ → ℝ} (hh : Trig h h') (hz : stY N z ∈ simpleSet N) :
    genL (fun z => h (yfun (thLam θ) 0 z)) z (condDrift θ A z) (condCov N) =
      -(cθ θ * h (yfun (thLam θ) 0 z)) := by
  have hk := contDiffAt_yfun (contDiffAt_thLam (θ := θ) hz) 0
  rw [genL_comp_real hh.d hh.d' (contDiff_trig hh) hk, genL_yfun θ A (contDiffAt_thLam hz),
    lapl_thLam hN hz, sum_condCov]
  simp only [fderiv_yfun_cstY ((contDiffAt_thLam (θ := θ) hz).differentiableAt (by norm_num))]
  rw [sum_fderiv_thLam_sq hz]
  simp only [condVd, Matrix.cons_val_zero, cθ]
  field_simp
  ring

theorem genL_Phic (hN : (N : ℝ) ≠ 0) {h h' : ℝ → ℝ} (hh : Trig h h')
    (hz : stY N z ∈ simpleSet N) :
    genL (Phic h θ) z (condDrift θ A z) (condCov N) = 0 := by
  have hk := contDiffAt_yfun (contDiffAt_thLam (θ := θ) hz) 0
  have hhk : ContDiffAt ℝ 2 (fun z => h (yfun (thLam θ) 0 z)) z := (contDiff_trig hh).contDiffAt.comp z hk
  rw [show Phic h θ = fun z => Ec N (cθ θ) z * h (yfun (thLam θ) 0 z) from rfl,
    genL_mul (contDiff_Ec _).contDiffAt hhk, genL_Ec, genL_hk θ A hN hh hz, sum_condCov]
  simp only [fderiv_Ec_cstY, zero_mul, mul_zero, add_zero, Finset.sum_const_zero]
  ring

theorem fderiv_Phic_cstY {h h' : ℝ → ℝ} (hh : Trig h h') (hz : stY N z ∈ simpleSet N)
    (a : Fin (N * N)) :
    fderiv ℝ (Phic h θ) z (Pi.single (cstY a) 1) = Ec N (cθ θ) z *
      (h' (yfun (thLam θ) 0 z) * fderiv ℝ (thLam θ) (stY N z) (Pi.single a 1)) := by
  have hk := contDiffAt_yfun (contDiffAt_thLam (θ := θ) hz) 0
  have hhk : ContDiffAt ℝ 2 (fun z => h (yfun (thLam θ) 0 z)) z :=
    (contDiff_trig hh).contDiffAt.comp z hk
  rw [show Phic h θ = fun z => Ec N (cθ θ) z * h (yfun (thLam θ) 0 z) from rfl,
    fderiv_mul_apply ((contDiff_Ec _).differentiable (by norm_num) _)
      (hhk.differentiableAt (by norm_num)),
    fderiv_Ec_cstY, fderiv_comp_real_apply hh.d (hk.differentiableAt (by norm_num)),
    fderiv_yfun_cstY ((contDiffAt_thLam (θ := θ) hz).differentiableAt (by norm_num))]
  ring

/-- **Zero generator of `Pcond`** on `simpleSet × ℝ³`. -/
theorem genL_Pcond (hN : (N : ℝ) ≠ 0) {h h' : ℝ → ℝ} (hh : Trig h h')
    (hz : stY N z ∈ simpleSet N) {φ : (Fin (N * N) → ℝ) → ℝ} (hφ : ContDiffAt ℝ 2 φ (stY N z))
    (hΔ : ∑ a, fderiv ℝ (fderiv ℝ φ) (stY N z) (Pi.single a 1) (Pi.single a 1) =
      2 * N * A (stY N z))
    (hx : ∀ i : Fin N, ∑ a, fderiv ℝ φ (stY N z) (Pi.single a 1) *
      fderiv ℝ (lam N i) (stY N z) (Pi.single a 1) = 0) :
    genL (Pcond h θ φ) z (condDrift θ A z) (condCov N) = 0 := by
  have hk := contDiffAt_yfun (contDiffAt_thLam (θ := θ) hz) 0
  have hP : ContDiffAt ℝ 2 (Phic h θ) z :=
    (contDiff_Ec _).contDiffAt.mul ((contDiff_trig hh).contDiffAt.comp z hk)
  rw [show Pcond h θ φ = fun z => Phic h θ z * yfun φ 1 z from rfl,
    genL_mul hP (contDiffAt_yfun hφ 1), genL_Phic θ A hN hh hz, genL_yfun θ A hφ, hΔ, sum_condCov]
  simp only [fderiv_Phic_cstY θ hh hz, fderiv_yfun_cstY (hφ.differentiableAt (by norm_num)),
    fderiv_thLam hz]
  have hcross : ∑ a, (∑ i, θ i * fderiv ℝ (lam N i) (stY N z) (Pi.single a 1)) *
      fderiv ℝ φ (stY N z) (Pi.single a 1) = 0 := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← mul_zero (θ i), ← hx i, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  have e : ∀ a, Ec N (cθ θ) z * (h' (yfun (thLam θ) 0 z) *
      ∑ i, θ i * fderiv ℝ (lam N i) (stY N z) (Pi.single a 1)) *
        fderiv ℝ φ (stY N z) (Pi.single a 1) + fderiv ℝ φ (stY N z) (Pi.single a 1) *
      (Ec N (cθ θ) z * (h' (yfun (thLam θ) 0 z) *
        ∑ i, θ i * fderiv ℝ (lam N i) (stY N z) (Pi.single a 1))) =
      2 * Ec N (cθ θ) z * h' (yfun (thLam θ) 0 z) *
        ((∑ i, θ i * fderiv ℝ (lam N i) (stY N z) (Pi.single a 1)) *
          fderiv ℝ φ (stY N z) (Pi.single a 1)) := fun a => by ring
  simp_rw [e, ← Finset.mul_sum, hcross]
  simp only [condVd, Matrix.cons_val_one, Matrix.cons_val_zero]
  field_simp
  ring

/-- **Zero Itô drift of `Phic`.** -/
theorem itoDrift_Phic (hN : (N : ℝ) ≠ 0) {h h' : ℝ → ℝ} (hh : Trig h h')
    (hz : stY N z ∈ simpleSet N) (t : ℝ≥0) :
    itoDrift (fun p : ℝ × (Fin (N * N + 3) → ℝ) => Phic h θ p.2) z t (condDrift θ A z)
      (condCov N) = 0 := by
  have hk := contDiffAt_yfun (contDiffAt_thLam (θ := θ) hz) 0
  have hP : ContDiffAt ℝ 2 (Phic h θ) z :=
    (contDiff_Ec _).contDiffAt.mul ((contDiff_trig hh).contDiffAt.comp z hk)
  rw [itoDrift_eq_genL hP, genL_Phic θ A hN hh hz]

/-- **Zero Itô drift of `Pcond`.** -/
theorem itoDrift_Pcond (hN : (N : ℝ) ≠ 0) {h h' : ℝ → ℝ} (hh : Trig h h')
    (hz : stY N z ∈ simpleSet N) {φ : (Fin (N * N) → ℝ) → ℝ} (hφ : ContDiffAt ℝ 2 φ (stY N z))
    (hΔ : ∑ a, fderiv ℝ (fderiv ℝ φ) (stY N z) (Pi.single a 1) (Pi.single a 1) =
      2 * N * A (stY N z))
    (hx : ∀ i : Fin N, ∑ a, fderiv ℝ φ (stY N z) (Pi.single a 1) *
      fderiv ℝ (lam N i) (stY N z) (Pi.single a 1) = 0) (t : ℝ≥0) :
    itoDrift (fun p : ℝ × (Fin (N * N + 3) → ℝ) => Pcond h θ φ p.2) z t (condDrift θ A z)
      (condCov N) = 0 := by
  have hk := contDiffAt_yfun (contDiffAt_thLam (θ := θ) hz) 0
  have hP : ContDiffAt ℝ 2 (Phic h θ) z :=
    (contDiff_Ec _).contDiffAt.mul ((contDiff_trig hh).contDiffAt.comp z hk)
  have hQ : ContDiffAt ℝ 2 (Pcond h θ φ) z := hP.mul (contDiffAt_yfun hφ 1)
  rw [itoDrift_eq_genL hQ, genL_Pcond θ A hN hh hz hφ hΔ hx]

end BlockBand.SourceProcess.Stochastic.ComplexAngular
