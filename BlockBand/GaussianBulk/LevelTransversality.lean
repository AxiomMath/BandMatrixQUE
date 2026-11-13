module
public import BlockBand.GaussianBulk.LevelHorizontalBarrier
public import BlockBand.GaussianBulk.LevelVerticalNeighborhood
public import BlockBand.GaussianBulk.GaussianContourIntegration

/-!
# Transversality of the level graph and the vertical saddle line

If the level height at `x₀` is at least `η` and `t ≤ tmax`, the height is `(2√tmax/η)`-Lipschitz
relative to `x₀`. Consequently the distance from a point `x₀ + iv` of the vertical line to the
graph point over `x` controls `(x - x₀)² + (v - y(x₀))²` up to the factor
`2(1 + (2√tmax/η)²)`, and the graph velocity is uniformly bounded near `x₀`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.GaussianBulk
open Set

/-- If the height at `x₀` is at least `η`, then `|y(x) - y(x₀)| ≤ (2√tmax/η)|x - x₀|` for every
real `x` (also in the real gaps). -/
theorem levelHeight_abs_sub_base_le {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t tmax eta x₀ x : ℝ) (ht : 0 < t) (htmax : t ≤ tmax) (heta : 0 < eta)
    (hheight : eta ≤ levelHeight d t x₀) :
    |levelHeight d t x-levelHeight d t x₀| ≤
      (2*Real.sqrt tmax/eta)*|x-x₀| := by
  have hn := (levelHeight_bounds hN d t x ht).1
  have hb := (levelHeight_bounds hN d t x₀ ht).1
  have hs := levelHeight_sq_abs_sub_le hN d t x₀ x ht
  have hs' : |(levelHeight d t x)^2-(levelHeight d t x₀)^2| ≤
      2*Real.sqrt tmax*|x-x₀| :=
    le_trans hs (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt htmax) (by norm_num)) (abs_nonneg _))
  have he : |(levelHeight d t x)^2-(levelHeight d t x₀)^2| =
      |levelHeight d t x-levelHeight d t x₀| *
        (levelHeight d t x+levelHeight d t x₀) := by
    rw [show (levelHeight d t x)^2-(levelHeight d t x₀)^2=
      (levelHeight d t x-levelHeight d t x₀)*(levelHeight d t x+levelHeight d t x₀) by ring,
      abs_mul,abs_of_nonneg (add_nonneg hn hb)]
  rw [he] at hs'
  have hm : |levelHeight d t x-levelHeight d t x₀| *eta ≤
      2*Real.sqrt tmax*|x-x₀| :=
    le_trans (mul_le_mul_of_nonneg_left
      (by linarith : eta ≤ levelHeight d t x+levelHeight d t x₀) (abs_nonneg _)) hs'
  calc
    _ ≤ (2*Real.sqrt tmax*|x-x₀|)/eta := (le_div_iff₀ heta).mpr hm
    _ = (2*Real.sqrt tmax/eta)*|x-x₀| := by ring

/-- The squared distance between `x₀ + iv` and the graph point over `x`. -/
theorem levelGraph_vertical_norm_sq {N : ℕ} (d : Fin N → ℝ) (t x₀ x v : ℝ) :
    ‖((x₀:ℂ)+(v:ℂ)*Complex.I)-((x:ℂ)+(levelHeight d t x:ℂ)*Complex.I)‖^2 =
      (x-x₀)^2+(v-levelHeight d t x)^2 := by
  rw [Complex.sq_norm]
  simp [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.add_re,
    Complex.add_im,Complex.mul_re,Complex.mul_im]
  ring

/-- Transversality: `(x - x₀)² + (v - y(x₀))² ≤ 2(1 + (2√tmax/η)²)` times the squared distance from
`x₀ + iv` to the graph point over `x`. -/
theorem levelGraph_vertical_transverse_sq {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t tmax eta x₀ x v : ℝ) (ht : 0 < t) (htmax : t ≤ tmax) (heta : 0 < eta)
    (hheight : eta ≤ levelHeight d t x₀) :
    (x-x₀)^2+(v-levelHeight d t x₀)^2 ≤
      2*(1+(2*Real.sqrt tmax/eta)^2)*
        ‖((x₀:ℂ)+(v:ℂ)*Complex.I)-((x:ℂ)+(levelHeight d t x:ℂ)*Complex.I)‖^2 := by
  rw [levelGraph_vertical_norm_sq]
  have h := transverse_distance_sq (x-x₀) (v-levelHeight d t x₀)
    (levelHeight d t x-levelHeight d t x₀) (2*Real.sqrt tmax/eta)
    (levelHeight_abs_sub_base_le hN d t tmax eta x₀ x ht htmax heta hheight)
  convert h using 1
  ring

/-- The graph velocity `1 + i y'(x)`. -/
def levelGraphVelocity {N : ℕ} (d : Fin N → ℝ) (t x : ℝ) : ℂ :=
  (1:ℂ)+((deriv (levelHeight d t) x:ℝ):ℂ)*Complex.I

/-- On `|x - x₀| ≤ η²/(4√tmax)`, the squared graph velocity is at most `1 + (2√tmax/η)²`. -/
theorem levelGraphVelocity_norm_sq_le {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t tmax eta x₀ x : ℝ) (ht : 0 < t) (htmax : t ≤ tmax) (heta : 0 < eta)
    (hheight : eta ≤ levelHeight d t x₀)
    (hclose : |x-x₀| ≤ eta^2/(4*Real.sqrt tmax)) :
    ‖levelGraphVelocity d t x‖^2 ≤ 1+(2*Real.sqrt tmax/eta)^2 := by
  have hy := levelHeight_neighborhood_lower hN d t tmax eta x₀ x ht htmax heta hheight hclose
  have hd := abs_deriv_levelHeight_uniform hN d t x (eta/2) tmax ht htmax (by linarith) hy
  have hd' : |deriv (levelHeight d t) x| ≤ 2*Real.sqrt tmax/eta := by
    convert hd using 1
    ring
  have hh := mul_self_le_mul_self (abs_nonneg _) hd'
  rw [← pow_two,← pow_two,sq_abs] at hh
  unfold levelGraphVelocity
  rw [Complex.sq_norm]
  simp only [Complex.normSq_apply]
  simp
  nlinarith

end BlockBand.GaussianBulk
