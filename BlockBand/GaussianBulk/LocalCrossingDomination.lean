module
public import BlockBand.GaussianBulk.LevelTransversality
public import BlockBand.GaussianBulk.LocalKernelEnvelope
public import BlockBand.GaussianBulk.GaussianContourIntegration
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Domination of the local crossing amplitude

Near the upper saddle, the amplitude `‖G(z, w)‖ · |z'| / ‖w - z‖` of the gauged Johansson
integrand, with `z` on the level graph and `w` on the vertical saddle line, is dominated by an
explicit constant times the integrable planar Gaussian singularity `gaussianCrossingMajorant`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.GaussianBulk
open MeasureTheory Set

/-- Completing the square: `-ν(a² + b²) + k|a| ≤ -(ν/2)(a² + b²) + k²/(2ν)`. -/
theorem microscopic_gaussian_absorption (nu k a b : ℝ) (hnu : 0 < nu) :
    -nu*(a^2+b^2)+k*|a| ≤ -(nu/2)*(a^2+b^2)+k^2/(2*nu) := by
  have hsq := sq_nonneg (nu*|a|-k)
  have habs : |a|^2=a^2 := sq_abs a
  have hb := mul_nonneg (sq_nonneg nu) (sq_nonneg b)
  have hc : 2*nu*k*|a| ≤ nu^2*(a^2+b^2)+k^2 := by nlinarith
  have hdiv : k*|a|-(nu/2)*(a^2+b^2) ≤ k^2/(2*nu) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*nu)).mpr
    nlinarith
  linarith

/-- The local crossing amplitude `‖G(z, w)‖ · ‖z'‖ / ‖w - z‖` for `z = x + i y(x)` on the graph
and `w = x₀ + iv` on the vertical line, in local coordinates `p = (x - x₀) + i(v - y)`. The
value at `p = 0` is `0` (Lean's division by zero), a null set for the Lebesgue integral. -/
def localGraphVerticalAmplitude {N : ℕ} (d : Fin N → ℝ)
    (E t rho x₀ y xi zeta : ℝ) (p : ℂ) : ℝ :=
  let x := x₀+p.re
  let v := y+p.im
  let z : ℂ := (x:ℂ)+(levelHeight d t x:ℂ)*Complex.I
  let w : ℂ := (x₀:ℂ)+(v:ℂ)*Complex.I
  ‖gaugedJohanssonExp d E t rho x₀ xi zeta z w‖*
    ‖levelGraphVelocity d t x‖/‖w-z‖

/-- The constant from the transverse denominator and the graph speed. -/
def localCrossingConstant (eta tmax : ℝ) : ℝ :=
  Real.sqrt (2*(1+(2*Real.sqrt tmax/eta)^2))*
    Real.sqrt (1+(2*Real.sqrt tmax/eta)^2)

/-- On the local crossing box, the amplitude is at most `localCrossingConstant` times
`exp((|ξ|/(tρ))²/(2N η²/(16 tmax²)))` times `gaussianCrossingMajorant (η²/(32 tmax²)) N`. -/
theorem localGraphVerticalAmplitude_le {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t tmax rho eta x₀ y xi zeta : ℝ) (ht : 0 < t) (htmax : t ≤ tmax)
    (hrho : 0 < rho) (heta : 0 < eta) (hr : PositiveLevelRoot d t x₀ y)
    (hheight : eta ≤ y) (hpsi : levelPsi d t x₀=E) (p : ℂ)
    (ha : |p.re| ≤ eta^2/(4*Real.sqrt tmax)) (hb : |p.im| ≤ eta/2) :
    localGraphVerticalAmplitude d E t rho x₀ y xi zeta p ≤
      localCrossingConstant eta tmax*
        Real.exp ((|xi|/(t*rho))^2/(2*((N:ℝ)*eta^2/(16*tmax^2))))*
          gaussianCrossingMajorant (eta^2/(32*tmax^2)) (N:ℝ) p := by
  let x := x₀+p.re
  let v := y+p.im
  let z : ℂ := (x:ℂ)+(levelHeight d t x:ℂ)*Complex.I
  let w : ℂ := (x₀:ℂ)+(v:ℂ)*Complex.I
  let L := 2*Real.sqrt tmax/eta
  let A := Real.sqrt (2*(1+L^2))
  let B := Real.sqrt (1+L^2)
  let c := eta^2/(16*tmax^2)
  let nu := (N:ℝ)*c
  let k := |xi|/(t*rho)
  have htm : 0 < tmax := lt_of_lt_of_le ht htmax
  have hc : 0 < c := by dsimp only [c];positivity
  have hn : 0 < (N:ℝ) := Nat.cast_pos.mpr hN
  have hnu : 0 < nu := mul_pos hn hc
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hAsq : A^2=2*(1+L^2) := Real.sq_sqrt (by positivity)
  have hBsq : B^2=1+L^2 := Real.sq_sqrt (by positivity)
  have hy := levelHeight_eq_of_root hN d t x₀ y ht hr
  have hheight' : eta ≤ levelHeight d t x₀ := by rwa [hy]
  have hx : |x-x₀| ≤ eta^2/(4*Real.sqrt tmax) := by simpa only [x,add_sub_cancel_left] using ha
  have hv : v ∈ Icc (y/2) (3*y/2) := by
    rcases abs_le.mp hb with ⟨hl,hu⟩
    dsimp only [v]
    constructor <;> linarith
  have hrad : ‖p‖^2=p.re^2+p.im^2 := by rw [Complex.sq_norm,Complex.normSq_apply];ring
  have hd := levelGraph_vertical_transverse_sq hN d t tmax eta x₀ x v ht htmax heta hheight'
  rw [hy] at hd
  have hd' : ‖p‖^2 ≤ A^2*‖w-z‖^2 := by
    rw [hAsq,hrad]
    simpa only [L,w,z,x,v,add_sub_cancel_left] using hd
  have hrD : ‖p‖ ≤ A*‖w-z‖ := by nlinarith [norm_nonneg p,norm_nonneg (w-z),mul_nonneg hA (norm_nonneg (w-z))]
  have hs := levelGraphVelocity_norm_sq_le hN d t tmax eta x₀ x ht htmax heta hheight' hx
  have hsB : ‖levelGraphVelocity d t x‖ ≤ B := by
    change ‖levelGraphVelocity d t x‖^2 ≤ 1+L^2 at hs
    nlinarith [norm_nonneg (levelGraphVelocity d t x)]
  by_cases hp : p=0
  · subst p
    simp [localGraphVerticalAmplitude,hy,gaussianCrossingMajorant]
  · have hpn : 0 < ‖p‖ := norm_pos_iff.mpr hp
    have hDn : 0 < ‖w-z‖ := by
      have hh := mul_nonneg hA (norm_nonneg (w-z))
      by_contra hnot
      have hzD : ‖w-z‖=0 := le_antisymm (le_of_not_gt hnot) (norm_nonneg _)
      rw [hzD,mul_zero] at hrD
      linarith
    have hratio : ‖levelGraphVelocity d t x‖/‖w-z‖ ≤ (A*B)/‖p‖ := by
      apply (div_le_div_iff₀ hDn hpn).mpr
      have hmul := mul_le_mul_of_nonneg_left hrD (norm_nonneg (levelGraphVelocity d t x))
      have hspeed := mul_le_mul_of_nonneg_right hsB (mul_nonneg hA (norm_nonneg (w-z)))
      nlinarith
    have hphase := gaugedJohanssonExp_local_bound hN d E t tmax rho eta x₀ y x v xi zeta
      ht htmax hrho heta hr hheight hpsi hx hv
    have hphase' : ‖gaugedJohanssonExp d E t rho x₀ xi zeta z w‖ ≤
        Real.exp (-nu*‖p‖^2+k*|p.re|) := by
      rw [hrad]
      convert hphase using 1
      dsimp only [z,w,nu,c,k,x,v]
      ring
    have hgauss : Real.exp (-nu*‖p‖^2+k*|p.re|) ≤
        Real.exp (k^2/(2*nu))*Real.exp (-(nu/2)*‖p‖^2) := by
      rw [← Real.exp_add,hrad]
      exact Real.exp_le_exp.mpr (by linarith [microscopic_gaussian_absorption nu k p.re p.im hnu])
    change ‖gaugedJohanssonExp d E t rho x₀ xi zeta z w‖*
      ‖levelGraphVelocity d t x‖/‖w-z‖ ≤ _
    calc
      _ = ‖gaugedJohanssonExp d E t rho x₀ xi zeta z w‖*
          (‖levelGraphVelocity d t x‖/‖w-z‖) := by ring
      _ ≤ (Real.exp (k^2/(2*nu))*Real.exp (-(nu/2)*‖p‖^2))*((A*B)/‖p‖) :=
        mul_le_mul (le_trans hphase' hgauss) hratio
          (div_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
      _ = _ := by
        dsimp only [A,B,L,k,nu,c,localCrossingConstant,gaussianCrossingMajorant]
        have hpen : (|xi|/(t*rho))^2/(2*((N:ℝ)*(eta^2/(16*tmax^2))))=
            (|xi|/(t*rho))^2/(2*((N:ℝ)*eta^2/(16*tmax^2))) := by ring
        have hexp : -((N:ℝ)*(eta^2/(16*tmax^2))/2)*‖p‖^2=
            -(eta^2/(32*tmax^2))*(N:ℝ)*‖p‖^2 := by ring
        rw [hpen,hexp]
        ring

end BlockBand.GaussianBulk
