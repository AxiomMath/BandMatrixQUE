module
public import BlockBand.GaussianBulk.OrientedSineResidue
public import BlockBand.GaussianBulk.LevelHorizontalBarrier
public import BlockBand.GaussianBulk.LevelVerticalNeighborhood

/-!
# The gauged Johansson exponential near the upper saddle

Defines the gauged exponential factor `gaugedJohanssonExp` of the Johansson kernel, computes its
modulus between the level graph and the vertical saddle line, and bounds it near the upper
saddle by `exp(-N η²/(16 tmax²) ((x - x₀)² + (v - y)²) + (|ξ|/(tρ))|x - x₀|)`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.GaussianBulk
open Set

/-- The exponential factor of the Johansson kernel with its prefactor and the real microscopic
gauge. -/
def gaugedJohanssonExp {N : ℕ} (d : Fin N → ℝ)
    (E t rho x₀ xi zeta : ℝ) (z w : ℂ) : ℂ :=
  let beta : ℝ := (N:ℝ)*((E+zeta/((N:ℝ)*rho))^2-(E+xi/((N:ℝ)*rho))^2)/(2*t)
  Complex.exp (((beta-realSineGauge N E t rho x₀ xi+realSineGauge N E t rho x₀ zeta:ℝ):ℂ)+
    (N:ℂ)*(saddlePhase d E t w-saddlePhase d E t z)+
    ((xi/(t*rho):ℝ):ℂ)*z-((zeta/(t*rho):ℝ):ℂ)*w)

/-- The real gauge cancels the prefactor: between the graph point over `x` and `x₀ + iv`, the
modulus is the exponential of `N` times the action difference plus `ξ(x - x₀)/(tρ)`. -/
theorem norm_gaugedJohanssonExp_graph_vertical {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (E t rho x₀ x v xi zeta : ℝ) (ht : 0 < t) (hrho : 0 < rho) :
    ‖gaugedJohanssonExp d E t rho x₀ xi zeta
      ((x:ℂ)+(levelHeight d t x:ℂ)*Complex.I) ((x₀:ℂ)+(v:ℂ)*Complex.I)‖ =
      Real.exp ((N:ℝ)*(verticalRealAction d E t x₀ v-levelAction d E t x)+
        xi*(x-x₀)/(t*rho)) := by
  have hg := microscopic_phase_gauge_identity N hN E t rho x₀ xi zeta ht hrho
  have he : (N:ℝ)*((E+zeta/((N:ℝ)*rho))^2-(E+xi/((N:ℝ)*rho))^2)/(2*t)-
      realSineGauge N E t rho x₀ xi+realSineGauge N E t rho x₀ zeta+
        xi/(t*rho)*x-zeta/(t*rho)*x₀=xi*(x-x₀)/(t*rho) := by
    linear_combination hg
  unfold gaugedJohanssonExp
  rw [Complex.norm_exp]
  simp only [Complex.sub_re,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.natCast_im,
    mul_zero,zero_mul,sub_zero,add_zero]
  rw [← levelAction_eq_saddlePhase_re d E t x,
    ← verticalRealAction_eq_saddlePhase_re d E t x₀ v]
  congr 1
  linear_combination he

/-- Paired quadratic phase drop near the upper saddle:
`(η²/(16 tmax²))((x - x₀)² + (v - y)²) ≤ Λ(x) - S(v)`. -/
theorem graph_vertical_local_phase_drop {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t tmax eta x₀ y x v : ℝ) (ht : 0 < t) (htmax : t ≤ tmax)
    (heta : 0 < eta) (hr : PositiveLevelRoot d t x₀ y) (hheight : eta ≤ y)
    (hpsi : levelPsi d t x₀=E)
    (hx : |x-x₀| ≤ eta^2/(4*Real.sqrt tmax))
    (hv : v ∈ Icc (y/2) (3*y/2)) :
    eta^2/(16*tmax^2)*((x-x₀)^2+(v-y)^2) ≤
      levelAction d E t x-verticalRealAction d E t x₀ v := by
  have hy := levelHeight_eq_of_root hN d t x₀ y ht hr
  have hb : eta ≤ levelHeight d t x₀ := by rwa [hy]
  have hh := levelAction_horizontal_barrier hN d E t tmax eta x₀ x ht htmax heta hb hpsi
  have ha : (x-x₀)^2 ≤ (eta^2/(4*Real.sqrt tmax))*|x-x₀| := by
    have h := mul_le_mul_of_nonneg_right hx (abs_nonneg (x-x₀))
    simpa only [← pow_two,sq_abs] using h
  rw [min_eq_left ha] at hh
  have hvdrop := verticalRealAction_neighborhood_quadratic_drop hN d E t tmax x₀ y eta v
    ht htmax hr heta hheight hv
  have hid : levelAction d E t x₀=verticalRealAction d E t x₀ y := by
    rw [levelAction_eq_saddlePhase_re,verticalRealAction_eq_saddlePhase_re,hy]
  rw [← hid] at hvdrop
  have hc : 0 ≤ eta^2/(16*tmax^2) := by positivity
  have he : eta^2/(2*tmax^2)=8*(eta^2/(16*tmax^2)) := by ring
  rw [he] at hh
  nlinarith [mul_nonneg hc (sq_nonneg (x-x₀))]

/-- Near the upper saddle, the gauged exponential is at most
`exp(-N η²/(16 tmax²)((x - x₀)² + (v - y)²) + (|ξ|/(tρ))|x - x₀|)`. -/
theorem gaugedJohanssonExp_local_bound {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t tmax rho eta x₀ y x v xi zeta : ℝ) (ht : 0 < t) (htmax : t ≤ tmax)
    (hrho : 0 < rho) (heta : 0 < eta) (hr : PositiveLevelRoot d t x₀ y)
    (hheight : eta ≤ y) (hpsi : levelPsi d t x₀=E)
    (hx : |x-x₀| ≤ eta^2/(4*Real.sqrt tmax)) (hv : v ∈ Icc (y/2) (3*y/2)) :
    ‖gaugedJohanssonExp d E t rho x₀ xi zeta
      ((x:ℂ)+(levelHeight d t x:ℂ)*Complex.I) ((x₀:ℂ)+(v:ℂ)*Complex.I)‖ ≤
      Real.exp (-((N:ℝ)*eta^2/(16*tmax^2))*((x-x₀)^2+(v-y)^2)+
        (|xi|/(t*rho))*|x-x₀|) := by
  rw [norm_gaugedJohanssonExp_graph_vertical hN d E t rho x₀ x v xi zeta ht hrho]
  apply Real.exp_le_exp.mpr
  have hd := graph_vertical_local_phase_drop hN d E t tmax eta x₀ y x v
    ht htmax heta hr hheight hpsi hx hv
  have hn : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
  have hscaled := mul_le_mul_of_nonneg_left hd hn
  have hmic : xi*(x-x₀)/(t*rho) ≤ (|xi|/(t*rho))*|x-x₀| := by
    calc
      _ ≤ |xi*(x-x₀)|/(t*rho) := div_le_div_of_nonneg_right (le_abs_self _) (by positivity)
      _ = (|xi|/(t*rho))*|x-x₀| := by rw [abs_mul];ring
  have hphase : (N:ℝ)*(verticalRealAction d E t x₀ v-levelAction d E t x) ≤
      -((N:ℝ)*eta^2/(16*tmax^2))*((x-x₀)^2+(v-y)^2) := by
    calc
      _ = -((N:ℝ)*(levelAction d E t x-verticalRealAction d E t x₀ v)) := by ring
      _ ≤ -((N:ℝ)*(eta^2/(16*tmax^2)*((x-x₀)^2+(v-y)^2))) := neg_le_neg hscaled
      _ = _ := by ring
  exact add_le_add hphase hmic

end BlockBand.GaussianBulk
