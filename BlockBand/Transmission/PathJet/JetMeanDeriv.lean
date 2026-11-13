module

public import BlockBand.Transmission.PathJet.JetMeanScalar

/-!
# The jet mean step: the old jet, the residual derivatives (Cauchy estimates)

* `crossTr_self_eq`, `hasDerivAt_stieltjes`: `f'(ζ) = -W⁻¹Tr(ζ - X)⁻²` for passive `X`,
  `Im ζ > 0` (`f = stieltjes X`, so the old jet is `t = f'(z)` and `δ₁ = ‖t - s‖`);
* `norm_crossTr_sub_le`: `|f'(ζ) - f'(z)| ≤ |ζ - z|(ι⁻²η⁻¹ + ι⁻¹η⁻²)`;
* `norm_oldJet_le`: `|f'(z)| ≤ d_* + δ₀/η` (Herglotz mass bound and `η = -(1-b)Im a`);
* proved in the sibling module, `residual_derivs`: for `Y = Y₀ + ε` and the disk mean equations, the residuals
  `r₁(w) = u(w)(w - bv(w)) - 1`, `r₂(w) = v(w) - f(ζ(w))` are holomorphic on the closed disk of
  radius `η/4` about `z`, their derivatives at `z` are `≤ 4C/(ηW²)` (Cauchy), and they equal
  `u'D + u - buv'` and `v'(1+cφ) + bφu'` with `φ = f'(ζ(z))`.
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

theorem crossTr_self_eq (X : Matrix (Fin W) (Fin W) ℂ) (ζ : ℂ) :
    crossTr X ζ ζ = (W : ℂ)⁻¹ * (((ζ • (1 : Matrix (Fin W) (Fin W) ℂ) - X)⁻¹) *
      (ζ • (1 : Matrix (Fin W) (Fin W) ℂ) - X)⁻¹).trace := by
  simp [crossTr, Matrix.trace, Matrix.diag, Matrix.mul_apply]

theorem hasDerivAt_stieltjes {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef)
    {ζ : ℂ} (hζ : 0 < ζ.im) : HasDerivAt (stieltjes X) (-crossTr X ζ ζ) ζ := by
  have hK := (passive_inverse_constructed _ _ hζ hY (im_pencil X ζ)).1
  have hK' : IsUnit (-X + ζ • (1 : Matrix (Fin W) (Fin W) ℂ)) := by rwa [neg_add_eq_sub]
  have hd := affineInverse_hasDerivAt (-X) 1 ζ hK'
  have ht := ((Matrix.traceLinearMap (Fin W) ℂ ℂ).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt
    _ hd).const_mul (W : ℂ)⁻¹
  have hfun : stieltjes X = fun y => (W : ℂ)⁻¹ * ((Matrix.traceLinearMap (Fin W) ℂ ℂ).toContinuousLinearMap ∘
      fun t : ℂ => (-X + t • (1 : Matrix (Fin W) (Fin W) ℂ))⁻¹) y := by
    funext y; simp [stieltjes, neg_add_eq_sub]
  rw [hfun]
  convert ht using 1
  simp only [LinearMap.coe_toContinuousLinearMap', Matrix.traceLinearMap_apply,
    neg_add_eq_sub, Matrix.mul_one, trace_neg, mul_neg, crossTr_self_eq]

theorem deriv_stieltjes {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef)
    {ζ : ℂ} (hζ : 0 < ζ.im) : deriv (stieltjes X) ζ = -crossTr X ζ ζ :=
  (hasDerivAt_stieltjes hY hζ).deriv

theorem norm_crossTr_sub_le {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef)
    {ζ z : ℂ} {ι η : ℝ} (hι : 0 < ι) (hη : 0 < η) (hζ : ι ≤ ζ.im) (hz : η ≤ z.im) :
    ‖crossTr X ζ ζ - crossTr X z z‖ ≤ ‖ζ - z‖ * (ι⁻¹ ^ 2 * η⁻¹ + ι⁻¹ * η⁻¹ ^ 2) := by
  set K₁ := ζ • (1 : Matrix (Fin W) (Fin W) ℂ) - X
  set K₂ := z • (1 : Matrix (Fin W) (Fin W) ℂ) - X
  have h₁ : 0 < ζ.im := lt_of_lt_of_le hι hζ
  have h₂ : 0 < z.im := lt_of_lt_of_le hη hz
  have hK₁ := passive_inverse_constructed K₁ _ h₁ hY (im_pencil X ζ)
  have hK₂ := passive_inverse_constructed K₂ _ h₂ hY (im_pencil X z)
  have hM : ‖K₁⁻¹‖ ≤ ι⁻¹ := (norm_inv_le_of_im K₁ _ h₁ hY (im_pencil X ζ)).trans
    (inv_anti₀ hι hζ)
  have hR : ‖K₂⁻¹‖ ≤ η⁻¹ := (norm_inv_le_of_im K₂ _ h₂ hY (im_pencil X z)).trans
    (inv_anti₀ hη hz)
  have hid : K₁⁻¹ - K₂⁻¹ = -(ζ - z) • (K₁⁻¹ * K₂⁻¹) := by
    have : K₁⁻¹ - K₂⁻¹ = K₁⁻¹ * (K₂ - K₁) * K₂⁻¹ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, hK₁.2.2, Matrix.one_mul, Matrix.mul_assoc, hK₂.2.1,
        Matrix.mul_one]
    rw [this, show K₂ - K₁ = -(ζ - z) • (1 : Matrix (Fin W) (Fin W) ℂ) by
      simp only [K₁, K₂]; rw [neg_sub, sub_smul]; abel]
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  have hsq : K₁⁻¹ * K₁⁻¹ - K₂⁻¹ * K₂⁻¹ =
      -(ζ - z) • (K₁⁻¹ * (K₁⁻¹ * K₂⁻¹) + K₁⁻¹ * K₂⁻¹ * K₂⁻¹) := by
    have e : K₁⁻¹ * K₁⁻¹ - K₂⁻¹ * K₂⁻¹ = K₁⁻¹ * (K₁⁻¹ - K₂⁻¹) + (K₁⁻¹ - K₂⁻¹) * K₂⁻¹ := by
      simp only [Matrix.mul_sub, Matrix.sub_mul]; abel
    rw [e, hid, Matrix.mul_smul, Matrix.smul_mul, ← smul_add]
  rw [crossTr_self_eq, crossTr_self_eq, ← mul_sub, ← Matrix.trace_sub]
  refine (norm_normTrace_le _).trans ?_
  rw [hsq, norm_smul, norm_neg]
  gcongr
  refine (norm_add_le _ _).trans ?_
  have hM0 := norm_nonneg K₁⁻¹
  have hR0 := norm_nonneg K₂⁻¹
  have e1 : ‖K₁⁻¹ * (K₁⁻¹ * K₂⁻¹)‖ ≤ ι⁻¹ ^ 2 * η⁻¹ := by
    refine (norm_mul_le _ _).trans ?_
    calc ‖K₁⁻¹‖ * ‖K₁⁻¹ * K₂⁻¹‖ ≤ ι⁻¹ * (ι⁻¹ * η⁻¹) :=
          mul_le_mul hM ((norm_mul_le _ _).trans (mul_le_mul hM hR hR0 (by positivity)))
            (norm_nonneg _) (by positivity)
      _ = ι⁻¹ ^ 2 * η⁻¹ := by ring
  have e2 : ‖K₁⁻¹ * K₂⁻¹ * K₂⁻¹‖ ≤ ι⁻¹ * η⁻¹ ^ 2 := by
    refine (norm_mul_le _ _).trans ?_
    calc ‖K₁⁻¹ * K₂⁻¹‖ * ‖K₂⁻¹‖ ≤ (ι⁻¹ * η⁻¹) * η⁻¹ :=
          mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul hM hR hR0 (by positivity))) hR hR0
            (by positivity)
      _ = ι⁻¹ * η⁻¹ ^ 2 := by ring
  linarith

/-- `|f'(z)| ≤ d_* + δ₀/η`: the old jet lies in the `δ₀/η`-neighbourhood of `|s| ≤ d_*`. -/
theorem norm_oldJet_le {b E : ℝ} (hb : b < 1) (h1 : -2 < E) (h2 : E < 2)
    {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef) :
    ‖crossTr X (boundaryZ b E) (boundaryZ b E)‖ ≤ dStar b + jetDistance0 b E X / etaZ b E := by
  have hη : 0 < etaZ b E := etaZ_pos b E hb h1 h2
  have hc := norm_crossTr_le X (boundaryZ b E) (boundaryZ b E)
  rw [← Real.sqrt_mul (sqMass_nonneg _ _), Real.sqrt_mul_self (sqMass_nonneg _ _)] at hc
  have hm := im_mul_sqMass_le hY (ζ := boundaryZ b E) hη
  have hδ : -(stieltjes X (boundaryZ b E)).im ≤ -(matchedA E).im + jetDistance0 b E X := by
    have := Complex.abs_im_le_norm (stieltjes X (boundaryZ b E) - matchedA E)
    rw [Complex.sub_im] at this
    have e : jetDistance0 b E X = ‖stieltjes X (boundaryZ b E) - matchedA E‖ := rfl
    rw [e]; linarith [(abs_le.mp this).1]
  have hea := etaZ_eq b E h1 h2
  have h1b : 0 < 1 - b := by linarith
  have hsq : sqMass X (boundaryZ b E) ≤ dStar b + jetDistance0 b E X / etaZ b E := by
    have hdS : etaZ b E * dStar b = -(matchedA E).im := by
      rw [hea, dStar]; field_simp
    have hm' : etaZ b E * sqMass X (boundaryZ b E) ≤ -(stieltjes X (boundaryZ b E)).im := hm
    have : etaZ b E * sqMass X (boundaryZ b E) ≤ etaZ b E * (dStar b + jetDistance0 b E X / etaZ b E) := by
      rw [mul_add, mul_div_cancel₀ _ hη.ne', hdS]
      linarith
    exact le_of_mul_le_mul_left this hη
  exact hc.trans hsq

end BlockBand.Transmission.PathJet
