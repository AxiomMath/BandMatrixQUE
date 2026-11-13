module
public import BlockBand.GaussianBulk.SaddleIdentities
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The sine kernel as an oriented segment residue

The residue produced by the contour deformation is an exponential integral over the upward
vertical segment from `x - iy` to `x + iy`. With `y = tπρ` and the real microscopic gauge, its
normalization is exactly the sine kernel `sinc(π(ξ - ζ))`, with diagonal value `1`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.GaussianBulk
open MeasureTheory

/-- The sine kernel `sinc(π(ξ - ζ))`, continuous with diagonal value `1`. -/
def unitSineKernel (xi zeta : ℝ) : ℝ := Real.sinc (Real.pi*(xi-zeta))

/-- The integral of `exp(kz)` over the upward segment `z = x + iys`, `s ∈ [-1, 1]`. -/
def upwardExponentialSegment (x y k : ℝ) : ℂ :=
  ∫ s in (-1:ℝ)..1, Complex.exp ((k:ℂ)*((x:ℂ)+((y*s:ℝ):ℂ)*Complex.I))*
    ((y:ℂ)*Complex.I)

/-- The real microscopic gauge `ξ(x - E)/(tρ) - ξ²/(2Ntρ²)`. -/
def realSineGauge (N : ℕ) (E t rho x xi : ℝ) : ℝ :=
  xi*(x-E)/(t*rho)-xi^2/(2*(N:ℝ)*t*rho^2)

/-- The normalized segment residue: the upward segment integral with the microscopic prefactor
and the factor `1/(2πitρ)`. -/
def normalizedSegmentResidue (N : ℕ) (E t rho x y xi zeta : ℝ) : ℂ :=
  Complex.exp (((N:ℝ)*((E+zeta/((N:ℝ)*rho))^2-(E+xi/((N:ℝ)*rho))^2)/(2*t):ℝ):ℂ) /
    (((2*Real.pi*t*rho:ℝ):ℂ)*Complex.I) *
      upwardExponentialSegment x y ((xi-zeta)/(t*rho))

/-- `∫_{-1}^{1} exp(irs) ds = 2 sinc r`, for every real `r` (including `r = 0`). -/
theorem integral_unit_exp_imaginary (r : ℝ) :
    (∫ s in (-1:ℝ)..1, Complex.exp (((r*s:ℝ):ℂ)*Complex.I)) =
      (2:ℂ)*(Real.sinc r:ℂ) := by
  by_cases hr : r=0
  · norm_num [hr]
  · rw [intervalIntegral.integral_comp_mul_left (fun a : ℝ => Complex.exp ((a:ℂ)*Complex.I)) hr]
    simp only [mul_neg_one,mul_one]
    rw [integral_exp_mul_I_eq_sinc]
    rw [Complex.real_smul]
    have hh : (1/r)*(2*r*Real.sinc r)=2*Real.sinc r := by
      field_simp [hr]
    simpa only [one_div,Complex.ofReal_mul,Complex.ofReal_ofNat] using
      congrArg Complex.ofReal hh

/-- The upward segment integral is `exp(kx) · 2iy · sinc(ky)`. -/
theorem upwardExponentialSegment_eq (x y k : ℝ) :
    upwardExponentialSegment x y k =
      Complex.exp ((k*x:ℝ):ℂ)*(2*(y:ℂ)*Complex.I)*(Real.sinc (k*y):ℂ) := by
  have he (s : ℝ) : (k:ℂ)*((x:ℂ)+((y*s:ℝ):ℂ)*Complex.I)=
      ((k*x:ℝ):ℂ)+(((k*y*s:ℝ):ℂ)*Complex.I) := by push_cast;ring
  unfold upwardExponentialSegment
  simp_rw [he,Complex.exp_add]
  rw [intervalIntegral.integral_mul_const,intervalIntegral.integral_const_mul,
    integral_unit_exp_imaginary]
  ring

/-- The microscopic phase gauge identity, for `N > 0`, `t > 0`, `ρ > 0`. -/
theorem microscopic_phase_gauge_identity (N : ℕ) (hN : 0 < N)
    (E t rho x xi zeta : ℝ) (ht : 0 < t) (hrho : 0 < rho) :
    (N:ℝ)*((E+zeta/((N:ℝ)*rho))^2-(E+xi/((N:ℝ)*rho))^2)/(2*t)+
      ((xi-zeta)/(t*rho))*x =
        realSineGauge N E t rho x xi-realSineGauge N E t rho x zeta := by
  unfold realSineGauge
  field_simp [ne_of_gt ht,ne_of_gt hrho,Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)]
  ring

/-- If `y = tπρ`, the normalized segment residue is the sine kernel conjugated by the real
gauge. -/
theorem normalizedSegmentResidue_eq (N : ℕ) (hN : 0 < N)
    (E t rho x y xi zeta : ℝ) (ht : 0 < t) (hrho : 0 < rho)
    (hy : y=t*Real.pi*rho) :
    normalizedSegmentResidue N E t rho x y xi zeta =
      Complex.exp ((realSineGauge N E t rho x xi-realSineGauge N E t rho x zeta:ℝ):ℂ)*
        (unitSineKernel xi zeta:ℂ) := by
  let beta := (N:ℝ)*((E+zeta/((N:ℝ)*rho))^2-(E+xi/((N:ℝ)*rho))^2)/(2*t)
  let k := (xi-zeta)/(t*rho)
  let D : ℂ := ((2*Real.pi*t*rho:ℝ):ℂ)*Complex.I
  have hD : D ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity)) Complex.I_ne_zero
  have hky : k*y=Real.pi*(xi-zeta) := by
    dsimp only [k]
    rw [hy]
    field_simp [ne_of_gt ht,ne_of_gt hrho]
  have hyD : 2*(y:ℂ)*Complex.I=D := by
    dsimp only [D]
    rw [hy]
    push_cast
    ring
  have he : beta+k*x=realSineGauge N E t rho x xi-realSineGauge N E t rho x zeta :=
    microscopic_phase_gauge_identity N hN E t rho x xi zeta ht hrho
  change Complex.exp ((beta:ℝ):ℂ)/D*upwardExponentialSegment x y k = _
  rw [upwardExponentialSegment_eq,hyD,hky]
  have heq : Complex.exp ((beta:ℝ):ℂ)/D*
      (Complex.exp ((k*x:ℝ):ℂ)*D*(Real.sinc (Real.pi*(xi-zeta)):ℂ)) =
        Complex.exp ((beta:ℝ):ℂ)*Complex.exp ((k*x:ℝ):ℂ)*
          (Real.sinc (Real.pi*(xi-zeta)):ℂ) := by field_simp
  rw [heq,← Complex.exp_add,← Complex.ofReal_add,he]
  rfl

/-- If `y = tπρ`, the normalized segment residue has diagonal value `1`. -/
theorem normalizedSegmentResidue_diagonal (N : ℕ) (hN : 0 < N)
    (E t rho x y xi : ℝ) (ht : 0 < t) (hrho : 0 < rho) (hy : y=t*Real.pi*rho) :
    normalizedSegmentResidue N E t rho x y xi xi=1 := by
  rw [normalizedSegmentResidue_eq N hN E t rho x y xi xi ht hrho hy]
  simp [unitSineKernel]

end BlockBand.GaussianBulk
