module

public import BlockBand.Transmission.PathJet.JetMeanDeriv

/-!
# The differentiated mean equations: residual derivatives by Cauchy estimates

For `Y = Y₀ + ε` (`Y₀ ⪰ 0`, `ε > 0`), the mean residuals
`r₁(w) = u(w)(w - bv(w)) - 1` and `r₂(w) = v(w) - f(ζ(w))` (`resid1`, `resid2`) are
holomorphic wherever `Im w > 0` and `Im ζ(w) > 0`. `residual_derivs`: if on the parameter disk
`Im ζ(w) ≥ ι₀ > 0` and `|r_i(w)| ≤ ε'`, then at `z`
* `|r_i'(z)| ≤ ε'/(η/4)` (Cauchy on the circle of radius `η/4`);
* `r₁'(z) = u'D + u - buv'`, `r₂'(z) = v'(1+cφ) + bφu'`, with `u' = deriv u z`,
  `v' = deriv v z`, `D = z - bv(z)`, `φ = f'(ζ(z)) = -crossTr X ζ ζ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PathJet

open MeasureTheory Matrix Metric
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PathScalar
open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `ζ(w) = -E - cv(w) - bu(w)`. -/
abbrev zetaW (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (w : ℂ) : ℂ :=
  zetaOf b E (vW b E w X) (uW b E w X)

/-- The port residual `r₁(w) = u(w)(w - bv(w)) - 1`. -/
def resid1 (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (w : ℂ) : ℂ :=
  uW b E w X * (w - (b : ℂ) * vW b E w X) - 1

/-- The physical residual `r₂(w) = v(w) - f(ζ(w))`. -/
def resid2 (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (w : ℂ) : ℂ :=
  vW b E w X - stieltjes X (zetaW b E X w)

section
variable {b E : ℝ} {X Y₀ : Matrix (Fin W) (Fin W) ℂ} {ε : ℝ} (hε : 0 < ε) (hY₀ : Y₀.PosSemidef)
  (hYe : passiveY X = Y₀ + ε • (1 : Matrix (Fin W) (Fin W) ℂ))
include hε hY₀ hYe

theorem passiveY_of_reg : (passiveY X).PosSemidef := by
  rw [hYe]; exact hY₀.add (Matrix.PosSemidef.one.smul hε.le)

theorem hasDerivAt_resid1 {w : ℂ} (hw : 0 < w.im) :
    HasDerivAt (resid1 b E X)
      (deriv (fun w => uW b E w X) w * (w - (b : ℂ) * vW b E w X) + uW b E w X -
        (b : ℂ) * uW b E w X * deriv (fun w => vW b E w X) w) w := by
  have hu := (hasDerivAt_uW b E hε hY₀ hYe hw).differentiableAt.hasDerivAt
  have hv := (hasDerivAt_vW b E hε hY₀ hYe hw).differentiableAt.hasDerivAt
  have h := (hu.mul ((hasDerivAt_id w).sub (hv.const_mul (b : ℂ)))).sub_const 1
  exact h.congr_deriv (by simp only [Pi.sub_apply, id_eq]; ring)

theorem hasDerivAt_zetaW {w : ℂ} (hw : 0 < w.im) :
    HasDerivAt (zetaW b E X)
      (-(((1 - 2 * b : ℝ) : ℂ) * deriv (fun w => vW b E w X) w) -
        (b : ℂ) * deriv (fun w => uW b E w X) w) w := by
  have hu := (hasDerivAt_uW b E hε hY₀ hYe hw).differentiableAt.hasDerivAt
  have hv := (hasDerivAt_vW b E hε hY₀ hYe hw).differentiableAt.hasDerivAt
  have h := ((hasDerivAt_const w (-(E : ℂ))).sub (hv.const_mul ((1 - 2 * b : ℝ) : ℂ))).sub
    (hu.const_mul (b : ℂ))
  exact h.congr_deriv (by ring)

theorem hasDerivAt_resid2 {w : ℂ} (hw : 0 < w.im) (hζ : 0 < (zetaW b E X w).im) :
    HasDerivAt (resid2 b E X)
      (deriv (fun w => vW b E w X) w * (1 + ((1 - 2 * b : ℝ) : ℂ) * -crossTr X (zetaW b E X w)
        (zetaW b E X w)) + (b : ℂ) * -crossTr X (zetaW b E X w) (zetaW b E X w) *
          deriv (fun w => uW b E w X) w) w := by
  have hv := (hasDerivAt_vW b E hε hY₀ hYe hw).differentiableAt.hasDerivAt
  have hf := hasDerivAt_stieltjes (passiveY_of_reg hε hY₀ hYe) hζ
  have h := hv.sub (hf.comp w (hasDerivAt_zetaW hε hY₀ hYe hw))
  exact h.congr_deriv (by ring)

/-- **The differentiated mean equations at `z`.** -/
theorem residual_derivs (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) {ι₀ ε' : ℝ}
    (hι₀ : 0 < ι₀)
    (hbund : ∀ w ∈ paramDisk b E, ι₀ ≤ (zetaW b E X w).im ∧ ‖resid1 b E X w‖ ≤ ε' ∧
      ‖resid2 b E X w‖ ≤ ε') :
    ‖deriv (resid1 b E X) (boundaryZ b E)‖ ≤ ε' / (etaZ b E / 4) ∧
      ‖deriv (resid2 b E X) (boundaryZ b E)‖ ≤ ε' / (etaZ b E / 4) ∧
      deriv (resid1 b E X) (boundaryZ b E) =
        deriv (fun w => uW b E w X) (boundaryZ b E) *
          (boundaryZ b E - (b : ℂ) * vW b E (boundaryZ b E) X) + uW b E (boundaryZ b E) X -
          (b : ℂ) * uW b E (boundaryZ b E) X * deriv (fun w => vW b E w X) (boundaryZ b E) ∧
      deriv (resid2 b E X) (boundaryZ b E) =
        deriv (fun w => vW b E w X) (boundaryZ b E) * (1 + ((1 - 2 * b : ℝ) : ℂ) *
          -crossTr X (zetaW b E X (boundaryZ b E)) (zetaW b E X (boundaryZ b E))) +
          (b : ℂ) * -crossTr X (zetaW b E X (boundaryZ b E)) (zetaW b E X (boundaryZ b E)) *
          deriv (fun w => uW b E w X) (boundaryZ b E) := by
  set z := boundaryZ b E
  have hη : 0 < etaZ b E := etaZ_pos b E (by linarith) h1 h2
  set R := etaZ b E / 4
  have hR : 0 < R := by positivity
  have hsub : closedBall z R ⊆ paramDisk b E := by
    intro w hw
    rw [mem_closedBall] at hw
    rw [paramDisk, mem_closedBall]; simp only [R] at hw; linarith
  have him : ∀ w ∈ closedBall z R, 0 < w.im ∧ 0 < (zetaW b E X w).im := by
    intro w hw
    have hD := hsub hw
    exact ⟨lt_of_lt_of_le (by positivity) (paramDisk_bounds hb0 (by linarith) h1 h2 hD).1,
      lt_of_lt_of_le hι₀ (hbund w hD).1⟩
  have hcl : closure (ball z R) = closedBall z R := closure_ball z hR.ne'
  have hd1 : DiffContOnCl ℂ (resid1 b E X) (ball z R) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [hcl]
    intro w hw
    exact (hasDerivAt_resid1 hε hY₀ hYe (him w hw).1).differentiableAt.differentiableWithinAt
  have hd2 : DiffContOnCl ℂ (resid2 b E X) (ball z R) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [hcl]
    intro w hw
    exact (hasDerivAt_resid2 hε hY₀ hYe (him w hw).1 (him w hw).2).differentiableAt.differentiableWithinAt
  have hs : ∀ w ∈ sphere z R, w ∈ paramDisk b E := fun w hw => hsub (sphere_subset_closedBall hw)
  have hz : z ∈ closedBall z R := mem_closedBall_self hR.le
  refine ⟨Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hd1 fun w hw => (hbund w (hs w hw)).2.1,
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hd2 fun w hw => (hbund w (hs w hw)).2.2,
    (hasDerivAt_resid1 hε hY₀ hYe (him z hz).1).deriv,
    (hasDerivAt_resid2 hε hY₀ hYe (him z hz).1 (him z hz).2).deriv⟩

end

end BlockBand.Transmission.PathJet
