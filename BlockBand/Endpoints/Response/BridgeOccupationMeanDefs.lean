module

public import BlockBand.Endpoints.Response.BridgeOccupationCKY
public import BlockBand.Endpoints.Response.BridgeOccupationMeanGauss

/-!
# The radial Gaussian comparison for the hyperbolic heat kernel

This file states `LbkHypRadialGaussCompare`, a pointwise two-sided comparison of the hyperbolic
radial heat kernel with the `h`-conjugated planar radial kernel. It is proved as
`lbkHypRadialGaussCompare_holds`, and the hyperbolic bridge-mean bounds are derived from it
(`lbkHypBridgeMeanLower_of_gaussCompare`, `lbkHypBridgeMeanUpper_of_gaussCompare`).

The hyperbolic radial generator `½(∂²_r + coth r ∂_r)` is the planar Bessel generator
`L_B = ½(∂²_r + r⁻¹∂_r)` conjugated by `h(r) = (sinh r / r)^{1/2}` with the bounded potential
`V = L_B h / h = 1/8 + (1/8)(r⁻² - sinh⁻² r) ∈ (1/8, 1/6]`. By Feynman–Kac, at the level of
transition densities this gives a pointwise two-sided comparison of the hyperbolic radial heat
kernel with the `h`-conjugated planar radial (Bessel) kernel; in the bridge the `h(r')` factors
cancel and only the bounded density factor `e^{±D₀τ osc V}` survives, and the planar bridge marginal
is Gaussian.

With `σ(r) = r / sinh r` (`lbkSdivSinh`) and
`bomEuclRadial T r r' = (2/(4πT)) √(σ(r)σ(r')) ∫_{-π}^{π} exp(-(r² + r'² - 2rr' cos φ)/(4T)) dφ`
(the planar heat kernel of `e^{TΔ}`, angle-integrated, conjugated by `h` and written as a density
in `x' = (cosh r' - 1)/2`), the statement is: for every `T₀ > 0` there are `c, C > 0` with
`c · bomEuclRadial T r r' ≤ lbkHypRadial T x(r) x(r') ≤ C · bomEuclRadial T r r'` for
`T ∈ (0, T₀]`, `r, r' ≥ 0`, `x(r) = (cosh r - 1)/2`.

*Why it holds.* Write `q^H_t(r,r')` (resp. `q^B_t`) for the transition density w.r.t. `dr'` of the
radial process with generator `½(∂² + coth ∂)` (resp. the 2-d Bessel process). Conjugation and
Feynman–Kac give
`q^H_t(r,r') = (h(r')/h(r)) q^B_t(r,r') E^{BES-bridge}_{r→r',t}[exp(-∫_0^t V)]`, and
`V ∈ (1/8, 1/6]` puts the expectation in `[e^{-t/6}, e^{-t/8}]`. At time `t = 2T` (since
`e^{TΔ} = e^{2T·½Δ}`) and in the density w.r.t. `dx' = (sinh r'/2) dr'` this is exactly
`e^{-T/3} bomEuclRadial ≤ lbkHypRadial ≤ e^{-T/4} bomEuclRadial`. The statement asks only for some
constants on `(0, T₀]`.

The statement is pointwise, about one transition kernel at one time, whereas the bridge-mean bounds
are ratios of `x'`-integrals of products of two kernels. Deriving them from it uses the
change of variables `x' ↔ r' ↔ ℝ²`, the polar-coordinate identification of the angle-integrated
planar kernels with a planar Gaussian bridge weight, completion of the square, a symmetrisation
lower bound (Jensen) and a Gaussian exponential moment.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Set Real
open scoped ENNReal

/-- The radial coordinate change `x(r) = (cosh r - 1)/2`. -/
def bomX (r : ℝ) : ℝ := (Real.cosh r - 1) / 2

/-- The `h`-conjugated planar radial heat kernel of `e^{TΔ}` on `ℝ²` as a density in
`x' = (cosh r' - 1)/2`:
`(2/(4πT)) √(σ(r)σ(r')) ∫_{-π}^{π} exp(-(r² + r'² - 2rr' cos φ)/(4T)) dφ`, `σ(r) = r / sinh r`. -/
def bomEuclRadial (T r r' : ℝ) : ℝ :=
  2 / (4 * π * T) * Real.sqrt (lbkSdivSinh r * lbkSdivSinh r') *
    ∫ φ in Ioo (-π) π, Real.exp (-(r ^ 2 + r' ^ 2 - 2 * r * r' * Real.cos φ) / (4 * T))

/-- Two-sided Gaussian comparison of the hyperbolic radial heat kernel with the `h`-conjugated
planar radial kernel, in pointwise transition-density form. It holds with `c = e^{-T₀/3}`, `C = 1`
(see the module docstring). -/
def LbkHypRadialGaussCompare : Prop :=
  ∀ T₀ : ℝ, 0 < T₀ → ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
    ∀ T ∈ Ioc 0 T₀, ∀ r r' : ℝ, 0 ≤ r → 0 ≤ r' →
      c * bomEuclRadial T r r' ≤ lbkHypRadial T (bomX r) (bomX r') ∧
        lbkHypRadial T (bomX r) (bomX r') ≤ C * bomEuclRadial T r r'

/-- The radial integral `∫_{r' ≥ 0} (sinh r'/2) g(r') k(r') dr'` (the `dx'` integral after
`x' = (cosh r' - 1)/2`). -/
def bomRadialInt (g : ℝ → ℝ≥0∞) (k : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ r in Ici (0 : ℝ), ENNReal.ofReal (Real.sinh r / 2) * (g r * ENNReal.ofReal (k r))

theorem bom_X_zero : bomX 0 = 0 := by simp [bomX]

theorem bom_X_nonneg (r : ℝ) : 0 ≤ bomX r := by
  unfold bomX
  linarith [Real.one_le_cosh r]

theorem bom_sdivSinh_zero : lbkSdivSinh 0 = 1 := by simp [lbkSdivSinh]

theorem bom_sdivSinh_mul_sinh (r : ℝ) : lbkSdivSinh r * Real.sinh r = r := by
  unfold lbkSdivSinh
  split_ifs with h
  · simp [h]
  · exact div_mul_cancel₀ r (fun hs => h (Real.sinh_eq_zero.1 hs))

theorem bom_eucl_integrand_le_one {T r r' : ℝ} (hT : 0 < T) (φ : ℝ) :
    Real.exp (-(r ^ 2 + r' ^ 2 - 2 * r * r' * Real.cos φ) / (4 * T)) ≤ 1 := by
  rw [Real.exp_le_one_iff, div_nonpos_iff]
  right
  refine ⟨?_, by positivity⟩
  have h1 : r * r' * Real.cos φ ≤ |r * r'| := by
    calc r * r' * Real.cos φ ≤ |r * r' * Real.cos φ| := le_abs_self _
      _ = |r * r'| * |Real.cos φ| := abs_mul _ _
      _ ≤ |r * r'| * 1 := by gcongr; exact Real.abs_cos_le_one φ
      _ = |r * r'| := mul_one _
  have h2 : 2 * |r * r'| ≤ r ^ 2 + r' ^ 2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|r| - |r'|), sq_abs r, sq_abs r']
  linarith

theorem bom_eucl_integrand_continuous (T r r' : ℝ) :
    Continuous fun φ : ℝ => Real.exp (-(r ^ 2 + r' ^ 2 - 2 * r * r' * Real.cos φ) / (4 * T)) := by
  fun_prop

theorem bom_eucl_integrableOn (T r r' : ℝ) :
    IntegrableOn (fun φ : ℝ => Real.exp (-(r ^ 2 + r' ^ 2 - 2 * r * r' * Real.cos φ) / (4 * T)))
      (Ioo (-π) π) :=
  ((bom_eucl_integrand_continuous T r r').integrableOn_Icc).mono_set Ioo_subset_Icc_self

theorem bom_euclRadial_nonneg {T : ℝ} (hT : 0 < T) (r r' : ℝ) : 0 ≤ bomEuclRadial T r r' := by
  unfold bomEuclRadial
  have h := setIntegral_nonneg (μ := volume) measurableSet_Ioo (fun φ (_ : φ ∈ Ioo (-π) π) =>
    (Real.exp_pos (-(r ^ 2 + r' ^ 2 - 2 * r * r' * Real.cos φ) / (4 * T))).le)
  have := Real.pi_pos
  positivity

end BlockBand.Endpoints
