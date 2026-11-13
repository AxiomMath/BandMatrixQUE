module
public import BlockBand.GaussianBulk.LocalCrossingDomination
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# The integral of the local crossing amplitude

Over the local crossing box `|a| ≤ η²/(4√tmax)`, `|b| ≤ η/2`, the local crossing amplitude is
measurable and integrable, and its integral is at most an explicit constant times `N^{-1/2}`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.GaussianBulk
open MeasureTheory Set

/-- The local crossing box in the coordinates `p = a + ib`. -/
def localCrossingBox (eta tmax : ℝ) : Set ℂ :=
  {p | |p.re| ≤ eta^2/(4*Real.sqrt tmax) ∧ |p.im| ≤ eta/2}

/-- The crossing box is a closed, hence Borel, set. -/
theorem measurableSet_localCrossingBox (eta tmax : ℝ) :
    MeasurableSet (localCrossingBox eta tmax) := by
  exact (isClosed_le (Complex.continuous_re.abs) continuous_const).measurableSet.inter
    (isClosed_le (Complex.continuous_im.abs) continuous_const).measurableSet

/-- The local crossing amplitude is Borel measurable. -/
theorem measurable_localGraphVerticalAmplitude {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (E t rho x₀ y xi zeta : ℝ) (ht : 0 < t) :
    Measurable (localGraphVerticalAmplitude d E t rho x₀ y xi zeta) := by
  have hheight := (levelHeight_continuous hN d t ht).measurable
  have hderiv := measurable_deriv (levelHeight d t)
  have hx : Measurable (fun p : ℂ => x₀+p.re) := by fun_prop
  have hv : Measurable (fun p : ℂ => y+p.im) := by fun_prop
  have hY := hheight.comp hx
  have hD := hderiv.comp hx
  have hz : Measurable (fun p : ℂ => ((x₀+p.re:ℝ):ℂ)+
      ((levelHeight d t (x₀+p.re):ℝ):ℂ)*Complex.I) := by fun_prop
  have hw : Measurable (fun p : ℂ => (x₀:ℂ)+((y+p.im:ℝ):ℂ)*Complex.I) := by fun_prop
  have hphase : Measurable (saddlePhase d E t) := by
    unfold saddlePhase complexMean
    fun_prop
  have hgauge : Measurable (fun p : ℂ => gaugedJohanssonExp d E t rho x₀ xi zeta
      (((x₀+p.re:ℝ):ℂ)+((levelHeight d t (x₀+p.re):ℝ):ℂ)*Complex.I)
      ((x₀:ℂ)+((y+p.im:ℝ):ℂ)*Complex.I)) := by
    unfold gaugedJohanssonExp
    have hzw := hphase.comp hw
    have hzz := hphase.comp hz
    fun_prop
  have hspeed : Measurable (fun p : ℂ => levelGraphVelocity d t (x₀+p.re)) := by
    unfold levelGraphVelocity
    fun_prop
  exact hgauge.norm.mul hspeed.norm |>.div (hw.sub hz).norm

/-- The local crossing amplitude is integrable over the crossing box. -/
theorem integrable_localGraphVerticalAmplitude {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (E t tmax rho eta x₀ y xi zeta : ℝ) (ht : 0 < t)
    (htmax : t ≤ tmax) (hrho : 0 < rho) (heta : 0 < eta)
    (hr : PositiveLevelRoot d t x₀ y) (hheight : eta ≤ y) (hpsi : levelPsi d t x₀=E) :
    IntegrableOn (localGraphVerticalAmplitude d E t rho x₀ y xi zeta)
      (localCrossingBox eta tmax) := by
  have htm : 0 < tmax := lt_of_lt_of_le ht htmax
  have hc : 0 < eta^2/(32*tmax^2) := by positivity
  have hn : 0 < (N:ℝ) := Nat.cast_pos.mpr hN
  let C := localCrossingConstant eta tmax*
    Real.exp ((|xi|/(t*rho))^2/(2*((N:ℝ)*eta^2/(16*tmax^2))))
  have hC : 0 ≤ C := by dsimp only [C,localCrossingConstant];positivity
  have hi := (integrable_gaussianCrossingMajorant (eta^2/(32*tmax^2)) (N:ℝ) hc hn).const_mul C
  apply hi.integrableOn.mono' (measurable_localGraphVerticalAmplitude hN d E t rho x₀ y xi zeta ht).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (measurableSet_localCrossingBox eta tmax)] with p hp
  rw [Real.norm_eq_abs,abs_of_nonneg (by unfold localGraphVerticalAmplitude;positivity)]
  exact localGraphVerticalAmplitude_le hN d E t tmax rho eta x₀ y xi zeta ht htmax hrho heta hr hheight hpsi p hp.1 hp.2

/-- The integral of the local crossing amplitude over the crossing box is at most
`localCrossingConstant · exp((|ξ|/(tρ))²/(2N η²/(16 tmax²))) · π^(3/2)/√(η² N/(32 tmax²))`. -/
theorem integral_localGraphVerticalAmplitude_le {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (E t tmax rho eta x₀ y xi zeta : ℝ) (ht : 0 < t)
    (htmax : t ≤ tmax) (hrho : 0 < rho) (heta : 0 < eta)
    (hr : PositiveLevelRoot d t x₀ y) (hheight : eta ≤ y) (hpsi : levelPsi d t x₀=E) :
    (∫ p in localCrossingBox eta tmax, localGraphVerticalAmplitude d E t rho x₀ y xi zeta p) ≤
      localCrossingConstant eta tmax*
        Real.exp ((|xi|/(t*rho))^2/(2*((N:ℝ)*eta^2/(16*tmax^2))))*
          (Real.pi*Real.sqrt Real.pi/Real.sqrt ((eta^2/(32*tmax^2))*(N:ℝ))) := by
  have htm : 0 < tmax := lt_of_lt_of_le ht htmax
  have hc : 0 < eta^2/(32*tmax^2) := by positivity
  have hn : 0 < (N:ℝ) := Nat.cast_pos.mpr hN
  let C := localCrossingConstant eta tmax*
    Real.exp ((|xi|/(t*rho))^2/(2*((N:ℝ)*eta^2/(16*tmax^2))))
  have hC : 0 ≤ C := by dsimp only [C,localCrossingConstant];positivity
  have hf := integrable_localGraphVerticalAmplitude hN d E t tmax rho eta x₀ y xi zeta
    ht htmax hrho heta hr hheight hpsi
  have hg := (integrable_gaussianCrossingMajorant (eta^2/(32*tmax^2)) (N:ℝ) hc hn).const_mul C
  have hm : (∫ p in localCrossingBox eta tmax,localGraphVerticalAmplitude d E t rho x₀ y xi zeta p) ≤
      ∫ p in localCrossingBox eta tmax,C*gaussianCrossingMajorant (eta^2/(32*tmax^2)) (N:ℝ) p := by
    apply integral_mono_ae hf hg.integrableOn
    filter_upwards [ae_restrict_mem (measurableSet_localCrossingBox eta tmax)] with p hp
    exact localGraphVerticalAmplitude_le hN d E t tmax rho eta x₀ y xi zeta
      ht htmax hrho heta hr hheight hpsi p hp.1 hp.2
  rw [integral_const_mul] at hm
  exact le_trans hm (mul_le_mul_of_nonneg_left
    (integral_gaussianCrossingMajorant_restrict_le (eta^2/(32*tmax^2)) (N:ℝ) hc hn _) hC)

end BlockBand.GaussianBulk
