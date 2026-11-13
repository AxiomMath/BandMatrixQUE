module

public import BlockBand.Endpoints.Clock.CavityMeanMap

/-!
# Stability of the cavity solution

An approximate pair `(v̄, ū)` with `Im v̄ ≤ 0`, `|ū| ≥ a_*`, the port lower bound
`-Im ū ≥ η |ū|²`, and residuals `‖v̄ - f(-e - c v̄ - b ū)‖ ≤ ε`, `‖ū - (z' - b v̄)⁻¹‖ ≤ ε`, is
within `C ε` of the exact solution: `‖v̄ - v‖ + ‖ū - u‖ ≤ C ε`, where `C` depends only on
`(b, c, η, M, a_*)` (`cavity_stability`): it is uniform over all finite laws (index type, weights,
points), all `e` and all `z'` with `Im z' ≥ η`, `|z'| ≤ M`. As in the paper, the approximate pair has
the same gap as an exact solution up to `O(ε)`, obtained from the imaginary identity
`cavity_approx_identity` with the port lower bound, without dividing by `-Im v̄`; the uniqueness
comparison then has a coefficient `≤ 1 - γ`. This is the deterministic Step 5 of the cavity-mean
lemma; it is applied in `condMean_large` to the approximate pair `(v̄, ū) = (E⟨𝒢₁₁⟩, E⟨𝒢₂₂⟩)` with
`ε = O(W⁻²)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open Complex

namespace CavityMean

/-!
## Constants of the stability bound
-/

/-- `s̄ = b η a_*²`, a lower bound for `Im(-e - c v̄ - b ū)`. -/
def stabS (b η a : ℝ) : ℝ := b * η * a ^ 2
/-- `V̄ = s̄⁻¹ + 1`, a bound for `|v̄|` when `ε ≤ 1`. -/
def stabV (b η a : ℝ) : ℝ := 1 / stabS b η a + 1
/-- `P = c + b² η⁻²`, a bound for `c + b²|ũ|²`. -/
def stabP (b c η : ℝ) : ℝ := c + b ^ 2 * (1 / η) ^ 2
/-- `β₀ = b η (M + b V̄)⁻²`, a lower bound for `b |ũ|² Im z'`. -/
def stabBeta (b η M a : ℝ) : ℝ := b * η / (M + b * stabV b η a) ^ 2
/-- `D = 1 + b s̄⁻²`. -/
def stabD (b η a : ℝ) : ℝ := 1 + b * (1 / stabS b η a ^ 2)
/-- The gap of an approximate pair, `γ₂ = β₀ / (2 (P V̄ + β₀))`. -/
def stabGamma (b c η M a : ℝ) : ℝ :=
  stabBeta b η M a / (2 * (stabP b c η * stabV b η a + stabBeta b η M a))
/-- The threshold `ε₀ = min(1, β₀/(2 P D))` for small residuals. -/
def stabEps (b c η M a : ℝ) : ℝ := min 1 (stabBeta b η M a / (2 * stabP b c η * stabD b η a))
/-- `C₁ = (1 + b s̄⁻¹ c^{-1/2}) / min(δ, γ₂)`. -/
def stabC1 (b c η M a : ℝ) : ℝ :=
  (1 + b * (1 / stabS b η a) * (1 / Real.sqrt c)) / min (cavityGapConst b c η M) (stabGamma b c η M a)
/-- The trivial bound `B = s̄⁻¹ + c^{-1/2} + 2/η` for large residuals. -/
def stabB (b c η a : ℝ) : ℝ := 1 / stabS b η a + 1 / Real.sqrt c + 2 / η
/-- The stability constant. -/
def stabConst (b c η M a : ℝ) : ℝ :=
  (stabC1 b c η M a * (1 + b * (1 / η) ^ 2) + 1) + (1 + stabB b c η a / stabEps b c η M a)

section Pos

variable {b c η M a : ℝ}

theorem stab_pos (hb : 0 < b) (hc : 0 < c) (hη : 0 < η) (hM : 0 ≤ M) (ha : 0 < a) :
    0 < stabS b η a ∧ 0 < stabV b η a ∧ 0 < stabP b c η ∧ 0 < stabBeta b η M a ∧
      0 < stabD b η a ∧ 0 < stabGamma b c η M a ∧ 0 < stabEps b c η M a ∧
      0 < stabC1 b c η M a ∧ 0 < stabB b c η a ∧ 0 < stabConst b c η M a := by
  have hS : 0 < stabS b η a := by unfold stabS; positivity
  have hV : 0 < stabV b η a := by unfold stabV; positivity
  have hP : 0 < stabP b c η := by unfold stabP; positivity
  have hβ : 0 < stabBeta b η M a := by unfold stabBeta; positivity
  have hD : 0 < stabD b η a := by unfold stabD; positivity
  have hγ : 0 < stabGamma b c η M a := by unfold stabGamma; positivity
  have hε : 0 < stabEps b c η M a := lt_min one_pos (by positivity)
  have hγ₁ := cavityGapConst_pos hb hc hη hM
  have hsc := Real.sqrt_pos.mpr hc
  have hC : 0 < stabC1 b c η M a := by
    unfold stabC1; have := lt_min hγ₁ hγ; positivity
  have hB : 0 < stabB b c η a := by unfold stabB; positivity
  refine ⟨hS, hV, hP, hβ, hD, hγ, hε, hC, hB, ?_⟩
  unfold stabConst; positivity

end Pos

/-- The approximate gap, as a real inequality: if `A (K y + β) = y + E` with `K ≤ P`,
`β ≥ β₀ > 0`, `0 ≤ y ≤ V`, `E ≤ ε D` and `ε ≤ β₀/(2 P D)`, then `A K ≤ 1 - β₀/(2(PV + β₀))`. -/
theorem approx_gap_real {A K β y E ε P V β₀ D : ℝ} (_hA : 0 ≤ A) (hK0 : 0 < K) (hK : K ≤ P)
    (hβ : β₀ ≤ β) (hβ₀ : 0 < β₀) (hy0 : 0 ≤ y) (hy : y ≤ V) (hE : E ≤ ε * D) (hε : 0 ≤ ε)
    (hD : 0 < D) (hP : 0 < P) (hε2 : ε ≤ β₀ / (2 * P * D)) (hid : A * (K * y + β) = y + E) :
    A * K ≤ 1 - β₀ / (2 * (P * V + β₀)) := by
  have hV : 0 ≤ V := hy0.trans hy
  have hden : 0 < K * y + β := by nlinarith
  have hAK : A * K * (K * y + β) = K * (y + E) := by linear_combination K * hid
  have hKE : K * E ≤ β₀ / 2 := by
    have h1 : K * E ≤ P * (ε * D) := by
      rcases le_or_gt 0 E with hE0 | hE0
      · exact mul_le_mul hK hE hE0 hP.le
      · nlinarith [mul_nonneg hε hD.le]
    have h3 : P * (ε * D) ≤ β₀ / 2 := by
      have := mul_le_mul_of_nonneg_left hε2 (mul_nonneg hP.le hD.le)
      calc P * (ε * D) = P * D * ε := by ring
        _ ≤ P * D * (β₀ / (2 * P * D)) := this
        _ = β₀ / 2 := by field_simp
    linarith
  set γ := β₀ / (2 * (P * V + β₀)) with hγ
  have hγ0 : 0 ≤ γ := by positivity
  have hγK : γ * (K * y + β) ≤ β / 2 := by
    have hγ2 : γ * (P * V + β) ≤ β / 2 := by
      rw [hγ, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) two_pos]
      nlinarith [mul_le_mul_of_nonneg_left hβ (mul_nonneg hP.le hV)]
    have : K * y ≤ P * V := mul_le_mul hK hy hy0 hP.le
    nlinarith
  rw [← mul_le_mul_iff_of_pos_right hden, hAK]
  nlinarith

/-- The imaginary identity for an approximate pair : with `ζ̄ = -e - c v̄ - b ū`, `ũ = (z' - b v̄)⁻¹`, `ε₁ = v̄ - f(ζ̄)`, `ε₂ = ū - ũ`:
`Ā ((c + b²|ũ|²) ȳ + b |ũ|² Im z') = ȳ + Im ε₁ + Ā b Im ε₂`, `ȳ = -Im v̄`. -/
theorem cavity_approx_identity {ι : Type*} [Fintype ι] (p x : ι → ℝ) (b c e : ℝ) (z' vbar ubar : ℂ) :
    cavitySq p x (-e - c * vbar - b * ubar) *
        ((c + b ^ 2 * ‖cavityPort b z' vbar‖ ^ 2) * (-vbar.im) +
          b * ‖cavityPort b z' vbar‖ ^ 2 * z'.im) =
      -vbar.im + (vbar - cavityStieltjes p x (-e - c * vbar - b * ubar)).im +
        cavitySq p x (-e - c * vbar - b * ubar) * b * (ubar - cavityPort b z' vbar).im := by
  have h1 := im_cavityStieltjes p x (-e - c * vbar - b * ubar)
  have h2 : (cavityPort b z' vbar).im = -(z'.im - b * vbar.im) * ‖cavityPort b z' vbar‖ ^ 2 := by
    unfold cavityPort; rw [inv_im_eq, im_sub_mul]
  have h3 : (-(e : ℂ) - c * vbar - b * ubar).im = -c * vbar.im - b * ubar.im := by simp
  rw [h3] at h1
  simp only [Complex.sub_im]
  rw [h1]
  linear_combination (cavitySq p x (-e - c * vbar - b * ubar) * b) * h2

end CavityMean

open CavityMean

section Stability

variable {ι : Type*} [Fintype ι] {p x : ι → ℝ} {b c e η M astar : ℝ} {z' v u vbar ubar : ℂ}
  {ε : ℝ}

theorem stab_arg_im (hb : 0 < b) (hc : 0 < c) (hη : 0 < η) (ha : 0 < astar)
    (hvb : vbar.im ≤ 0) (hua : astar ≤ ‖ubar‖) (hport : η * ‖ubar‖ ^ 2 ≤ -ubar.im) :
    stabS b η astar ≤ (-(e : ℂ) - c * vbar - b * ubar).im := by
  have : (-(e : ℂ) - c * vbar - b * ubar).im = c * (-vbar.im) + b * (-ubar.im) := by simp; ring
  rw [this]
  have h1' : b * (η * astar ^ 2) ≤ b * (-ubar.im) := by
    refine mul_le_mul_of_nonneg_left (le_trans ?_ hport) hb.le
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.le hua 2) hη.le
  have : 0 ≤ c * (-vbar.im) := mul_nonneg hc.le (by linarith)
  unfold stabS; nlinarith

/-- The approximate gap: `Ā (c + b²|ũ|²) ≤ 1 - γ₂` for `ε ≤ ε₀`. -/
theorem stab_approx_gap (hp : IsCavityWeights p) (hb : 0 < b) (hc : 0 < c) (hη : 0 < η)
    (ha : 0 < astar) (hz : η ≤ z'.im) (hM : ‖z'‖ ≤ M)
    (hvb : vbar.im ≤ 0) (hua : astar ≤ ‖ubar‖) (hport : η * ‖ubar‖ ^ 2 ≤ -ubar.im)
    (h1 : ‖vbar - cavityStieltjes p x (-e - c * vbar - b * ubar)‖ ≤ ε)
    (h2 : ‖ubar - (z' - b * vbar)⁻¹‖ ≤ ε) (hεs : ε ≤ stabEps b c η M astar) :
    ‖vbar‖ ≤ stabV b η astar ∧
    cavitySq p x (-e - c * vbar - b * ubar) * (c + b ^ 2 * ‖cavityPort b z' vbar‖ ^ 2) ≤
      1 - stabGamma b c η M astar := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  obtain ⟨hS, hV, hP, hβ₀, hD, hγ₂, -, -, -, -⟩ := stab_pos hb hc hη hM0 ha
  have hε : 0 ≤ ε := (norm_nonneg _).trans h1
  have hε1 : ε ≤ 1 := hεs.trans (min_le_left _ _)
  have hε2 : ε ≤ stabBeta b η M astar / (2 * stabP b c η * stabD b η astar) :=
    hεs.trans (min_le_right _ _)
  have hζb_im := stab_arg_im (e := e) hb hc hη ha hvb hua hport
  have hid := cavity_approx_identity p x b c e z' vbar ubar
  generalize hζb : (-(e : ℂ) - c * vbar - b * ubar) = ζb at hζb_im h1 hid
  have hζb_pos : 0 < ζb.im := hS.trans_le hζb_im
  have hSb : ‖cavityStieltjes p x ζb‖ ≤ 1 / stabS b η astar :=
    (norm_cavityStieltjes_le x hp hζb_pos).trans (one_div_le_one_div_of_le hS hζb_im)
  have hAb : cavitySq p x ζb ≤ 1 / stabS b η astar ^ 2 :=
    (cavitySq_le x hp hζb_pos).trans
      (one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hS.le hζb_im 2))
  have hAb0 : 0 ≤ cavitySq p x ζb := cavitySq_nonneg x hp _
  have hvbar : ‖vbar‖ ≤ stabV b η astar := by
    have := norm_le_insert' vbar (cavityStieltjes p x ζb)
    unfold stabV; linarith
  refine ⟨hvbar, ?_⟩
  obtain ⟨-, -, hut_le, -⟩ := port_facts hb.le hη hz hvb
  have hKt : c + b ^ 2 * ‖cavityPort b z' vbar‖ ^ 2 ≤ stabP b c η := by
    have := pow_le_pow_left₀ (norm_nonneg _) hut_le 2
    unfold stabP; nlinarith [sq_nonneg b]
  have hβt : stabBeta b η M astar ≤ b * ‖cavityPort b z' vbar‖ ^ 2 * z'.im := by
    have h := port_term_ge (z' := z') hb hη hz hvb hvbar
    have h' : b * ‖cavityPort b z' vbar‖ ^ 2 * η ≤ b * ‖cavityPort b z' vbar‖ ^ 2 * z'.im :=
      mul_le_mul_of_nonneg_left hz (by positivity)
    have hMz : stabBeta b η M astar ≤ b * η / (‖z'‖ + b * stabV b η astar) ^ 2 := by
      unfold stabBeta
      refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
      exact pow_le_pow_left₀ (by positivity) (by linarith) 2
    exact hMz.trans (h.trans h')
  have hyb : -vbar.im ≤ stabV b η astar := by
    have := Complex.abs_im_le_norm vbar; rw [abs_le] at this; linarith
  have hyb0 : 0 ≤ -vbar.im := by linarith
  have hE : (vbar - cavityStieltjes p x ζb).im +
      cavitySq p x ζb * b * (ubar - cavityPort b z' vbar).im ≤ ε * stabD b η astar := by
    have h2' : ‖ubar - cavityPort b z' vbar‖ ≤ ε := h2
    have e1 : (vbar - cavityStieltjes p x ζb).im ≤ ε := by
      have := Complex.abs_im_le_norm (vbar - cavityStieltjes p x ζb); rw [abs_le] at this
      linarith
    have e3 : cavitySq p x ζb * b * (ubar - cavityPort b z' vbar).im ≤
        1 / stabS b η astar ^ 2 * b * ε := by
      have := Complex.abs_im_le_norm (ubar - cavityPort b z' vbar)
      calc cavitySq p x ζb * b * (ubar - cavityPort b z' vbar).im
          ≤ cavitySq p x ζb * b * |(ubar - cavityPort b z' vbar).im| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
        _ ≤ 1 / stabS b η astar ^ 2 * b * ε :=
            mul_le_mul (mul_le_mul_of_nonneg_right hAb hb.le) (this.trans h2') (abs_nonneg _)
              (by positivity)
    unfold stabD; nlinarith
  exact approx_gap_real hAb0 (by positivity) hKt hβt hβ₀ hyb0 hyb hE hε hD hP hε2
    (by linarith [hid])

/-- The comparison coefficient (the two Cauchy–Schwarz inequalities of `cavityMap_sub_sq_le`):
`|K (c + b² ũ u)| ≤ 1 - γ` when `|K|² ≤ Ā A` and both gap quantities are `≤ 1 - γ`. -/
theorem stab_coeff_le {A A' c b γ : ℝ} {K ut u : ℂ} (hb : 0 < b) (hc : 0 < c) (hA : 0 ≤ A)
    (hA' : 0 ≤ A') (hK : ‖K‖ ^ 2 ≤ A * A') (h1 : A * (c + b ^ 2 * ‖ut‖ ^ 2) ≤ 1 - γ)
    (h2 : A' * (c + b ^ 2 * ‖u‖ ^ 2) ≤ 1 - γ) :
    ‖K * (c + b ^ 2 * ut * u)‖ ≤ 1 - γ := by
  have hnorm : ‖(c : ℂ) + b ^ 2 * ut * u‖ ^ 2 ≤
      (c + b ^ 2 * ‖ut‖ ^ 2) * (c + b ^ 2 * ‖u‖ ^ 2) := by
    have h1 : ‖(c : ℂ) + b ^ 2 * ut * u‖ ≤ c + b ^ 2 * (‖ut‖ * ‖u‖) := by
      refine (norm_add_le _ _).trans (le_of_eq ?_)
      rw [Complex.norm_real, Real.norm_of_nonneg hc.le, norm_mul, norm_mul, norm_pow,
        Complex.norm_real, Real.norm_of_nonneg hb.le]
      ring
    refine (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans ?_
    nlinarith [mul_nonneg (mul_nonneg hc.le (sq_nonneg b)) (sq_nonneg (‖ut‖ - ‖u‖))]
  have hγle : 0 ≤ 1 - γ := le_trans (by positivity) h1
  have : ‖K * (c + b ^ 2 * ut * u)‖ ^ 2 ≤ (1 - γ) ^ 2 := by
    rw [norm_mul, mul_pow]
    calc ‖K‖ ^ 2 * ‖(c : ℂ) + b ^ 2 * ut * u‖ ^ 2
        ≤ (A * A') * ((c + b ^ 2 * ‖ut‖ ^ 2) * (c + b ^ 2 * ‖u‖ ^ 2)) :=
          mul_le_mul hK hnorm (sq_nonneg _) (by positivity)
      _ = (A * (c + b ^ 2 * ‖ut‖ ^ 2)) * (A' * (c + b ^ 2 * ‖u‖ ^ 2)) := by ring
      _ ≤ (1 - γ) * (1 - γ) := mul_le_mul h1 h2 (by positivity) hγle
      _ = (1 - γ) ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hγle two_ne_zero).mp this

/-- The stability bound for small residuals `ε ≤ ε₀`. -/
theorem cavity_stability_small (hp : IsCavityWeights p) (hb : 0 < b) (hc : 0 < c) (hη : 0 < η)
    (ha : 0 < astar) (hz : η ≤ z'.im) (hM : ‖z'‖ ≤ M) (hsol : IsCavitySolution p x b c e z' v u)
    (hvb : vbar.im ≤ 0) (hua : astar ≤ ‖ubar‖) (hport : η * ‖ubar‖ ^ 2 ≤ -ubar.im)
    (h1 : ‖vbar - cavityStieltjes p x (-e - c * vbar - b * ubar)‖ ≤ ε)
    (h2 : ‖ubar - (z' - b * vbar)⁻¹‖ ≤ ε) (hεs : ε ≤ stabEps b c η M astar) :
    ‖vbar - v‖ ≤ stabC1 b c η M astar * ε ∧
      ‖ubar - u‖ ≤ ε + b * (1 / η) ^ 2 * (stabC1 b c η M astar * ε) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  obtain ⟨hS, -, -, -, -, hγ₂, -, -, -, -⟩ := stab_pos hb hc hη hM0 ha
  have hγ₁ := cavityGapConst_pos hb hc hη hM0
  have hsc := Real.sqrt_pos.mpr hc
  have hε : 0 ≤ ε := (norm_nonneg _).trans h1
  obtain ⟨-, hgap₂⟩ := stab_approx_gap hp hb hc hη ha hz hM hvb hua hport h1 h2 hεs
  have hζb_im := stab_arg_im (e := e) hb hc hη ha hvb hua hport
  generalize hζb : (-(e : ℂ) - c * vbar - b * ubar) = ζb at hζb_im h1 hgap₂
  have hζb_pos : 0 < ζb.im := hS.trans_le hζb_im
  have hAb : cavitySq p x ζb ≤ 1 / stabS b η astar ^ 2 :=
    (cavitySq_le x hp hζb_pos).trans
      (one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hS.le hζb_im 2))
  obtain ⟨-, hAc, -, huu⟩ := cavity_apriori_bounds hp hb hc hη hz hM hsol
  have hgap₁ := cavity_gap_lower_bound hp hb hc hη hz hM hsol
  obtain ⟨hv1, hu2, hvim, huim⟩ := hsol
  obtain ⟨hut1, -, hut_le, -⟩ := port_facts hb.le hη hz hvb
  have hutd : cavityPort b z' vbar * (z' - b * vbar) = 1 :=
    port_mul z' vbar b (ne_zero_of_im_pos (hη.trans_le hut1))
  have huu' : u * (z' - b * v) = 1 := by
    rw [hu2]; exact inv_mul_cancel₀ (ne_zero_of_im_pos (by
      have := (port_facts hb.le hη hz hvim.le).1; linarith))
  have h2' : ‖ubar - cavityPort b z' vbar‖ ≤ ε := h2
  clear h2
  generalize hut : cavityPort b z' vbar = ut at hutd hgap₂ hut_le h2'
  have hζ_pos : 0 < (-(e : ℂ) - c * v - b * u).im := by
    have : (-(e : ℂ) - c * v - b * u).im = c * (-v.im) + b * (-u.im) := by simp; ring
    rw [this]
    have := mul_pos hc (neg_pos.mpr hvim); have := mul_pos hb (neg_pos.mpr huim); linarith
  obtain ⟨Kc, hKc, hKc2⟩ := cavityStieltjes_sub x hp hζb_pos hζ_pos
  have hutu : ut - u = b * ut * u * (vbar - v) := by
    linear_combination u * hutd - ut * huu'
  have hrel : (vbar - v) * (1 - Kc * (c + b ^ 2 * ut * u)) =
      Kc * b * (ubar - ut) + (vbar - cavityStieltjes p x ζb) := by
    rw [← hv1] at hKc
    have hζd : (-(e : ℂ) - c * v - b * u) - ζb =
        c * (vbar - v) + b * ((ubar - ut) + (ut - u)) := by
      rw [← hζb]; ring
    rw [hζd, hutu] at hKc
    linear_combination hKc
  have hγ0 : 0 < min (cavityGapConst b c η M) (stabGamma b c η M astar) := lt_min hγ₁ hγ₂
  have hT : ‖Kc * (c + b ^ 2 * ut * u)‖ ≤
      1 - min (cavityGapConst b c η M) (stabGamma b c η M astar) := by
    refine stab_coeff_le hb hc (cavitySq_nonneg x hp _) (cavitySq_nonneg x hp _) hKc2 ?_ ?_
    · have := min_le_right (cavityGapConst b c η M) (stabGamma b c η M astar); linarith
    · have := min_le_left (cavityGapConst b c η M) (stabGamma b c η M astar); linarith
  have hKc_le : ‖Kc‖ ≤ 1 / stabS b η astar * (1 / Real.sqrt c) := by
    have : ‖Kc‖ ^ 2 ≤ (1 / stabS b η astar * (1 / Real.sqrt c)) ^ 2 := by
      refine hKc2.trans ?_
      rw [mul_pow, one_div_pow, one_div_pow, Real.sq_sqrt hc.le]
      exact mul_le_mul hAb hAc (cavitySq_nonneg x hp _) (by positivity)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp this
  generalize hγ : min (cavityGapConst b c η M) (stabGamma b c η M astar) = γ at hγ0 hT
  have hδ : ‖vbar - v‖ ≤ stabC1 b c η M astar * ε := by
    have h1T : γ ≤ ‖1 - Kc * (c + b ^ 2 * ut * u)‖ := by
      have := norm_sub_norm_le (1 : ℂ) (Kc * (c + b ^ 2 * ut * u))
      rw [norm_one] at this; linarith
    have hrhs : ‖Kc * b * (ubar - ut) + (vbar - cavityStieltjes p x ζb)‖ ≤
        (1 + b * (1 / stabS b η astar) * (1 / Real.sqrt c)) * ε := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hb.le]
      have := mul_le_mul (mul_le_mul_of_nonneg_right hKc_le hb.le) h2' (norm_nonneg _)
        (by positivity)
      nlinarith
    have : ‖vbar - v‖ * γ ≤ (1 + b * (1 / stabS b η astar) * (1 / Real.sqrt c)) * ε := by
      calc ‖vbar - v‖ * γ ≤ ‖vbar - v‖ * ‖1 - Kc * (c + b ^ 2 * ut * u)‖ :=
            mul_le_mul_of_nonneg_left h1T (norm_nonneg _)
        _ = ‖(vbar - v) * (1 - Kc * (c + b ^ 2 * ut * u))‖ := (norm_mul _ _).symm
        _ ≤ _ := by rw [hrel]; exact hrhs
    unfold stabC1
    rw [hγ, div_mul_eq_mul_div, le_div_iff₀ hγ0]
    linarith
  refine ⟨hδ, ?_⟩
  have : ubar - u = (ubar - ut) + b * ut * u * (vbar - v) := by rw [← hutu]; ring
  rw [this]
  refine (norm_add_le _ _).trans (add_le_add h2' ?_)
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hb.le]
  calc b * ‖ut‖ * ‖u‖ * ‖vbar - v‖ = b * (‖ut‖ * ‖u‖) * ‖vbar - v‖ := by ring
    _ ≤ b * ((1 / η) * (1 / η)) * (stabC1 b c η M astar * ε) := by
        gcongr
    _ = b * (1 / η) ^ 2 * (stabC1 b c η M astar * ε) := by ring

/-- **Stability of the cavity solution** for one finite law. -/
theorem cavity_stability_of (hp : IsCavityWeights p) (hb : 0 < b) (hc : 0 < c) (hη : 0 < η)
    (ha : 0 < astar) (hz : η ≤ z'.im) (hM : ‖z'‖ ≤ M) (hsol : IsCavitySolution p x b c e z' v u)
    (hvb : vbar.im ≤ 0) (hua : astar ≤ ‖ubar‖) (hport : η * ‖ubar‖ ^ 2 ≤ -ubar.im)
    (h1 : ‖vbar - cavityStieltjes p x (-e - c * vbar - b * ubar)‖ ≤ ε)
    (h2 : ‖ubar - (z' - b * vbar)⁻¹‖ ≤ ε) :
    ‖vbar - v‖ + ‖ubar - u‖ ≤ stabConst b c η M astar * ε := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  obtain ⟨hS, -, -, -, -, -, hε₀, hC1, hB, -⟩ := stab_pos hb hc hη hM0 ha
  have hε : 0 ≤ ε := (norm_nonneg _).trans h1
  have hsc := Real.sqrt_pos.mpr hc
  by_cases hεs : ε ≤ stabEps b c η M astar
  · obtain ⟨h1', h2'⟩ := cavity_stability_small hp hb hc hη ha hz hM hsol hvb hua hport h1 h2 hεs
    have : 0 ≤ (1 + stabB b c η astar / stabEps b c η M astar) * ε := by positivity
    unfold stabConst
    nlinarith
  · rw [not_le] at hεs
    -- trivial bounds
    have hubar_le : ‖ubar‖ ≤ 1 / η := by
      have hu0 : 0 < ‖ubar‖ := ha.trans_le hua
      have : η * ‖ubar‖ ^ 2 ≤ ‖ubar‖ := by
        refine hport.trans ?_
        have := Complex.abs_im_le_norm ubar; rw [abs_le] at this; linarith
      rw [le_div_iff₀ hη]; nlinarith
    have hζb_im : stabS b η astar ≤ (-(e : ℂ) - c * vbar - b * ubar).im := by
      have : (-(e : ℂ) - c * vbar - b * ubar).im = c * (-vbar.im) + b * (-ubar.im) := by
        simp; ring
      rw [this]
      have h1' : b * (η * astar ^ 2) ≤ b * (-ubar.im) := by
        refine mul_le_mul_of_nonneg_left (le_trans ?_ hport) hb.le
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.le hua 2) hη.le
      have : 0 ≤ c * (-vbar.im) := mul_nonneg hc.le (by linarith)
      unfold stabS; nlinarith
    have hSb := (norm_cavityStieltjes_le x hp (hS.trans_le hζb_im)).trans
      (one_div_le_one_div_of_le hS hζb_im)
    have hvbar : ‖vbar‖ ≤ 1 / stabS b η astar + ε := by
      have := norm_le_insert' vbar (cavityStieltjes p x (-e - c * vbar - b * ubar))
      linarith
    obtain ⟨hvA, hAc, -, huu⟩ := cavity_apriori_bounds hp hb hc hη hz hM hsol
    have hvc : ‖v‖ ≤ 1 / Real.sqrt c := by
      rw [← Real.sqrt_sq (norm_nonneg v), one_div, ← Real.sqrt_inv]
      exact Real.sqrt_le_sqrt (by rw [← one_div]; linarith)
    have e1 : ‖vbar - v‖ ≤ ‖vbar‖ + ‖v‖ := norm_sub_le _ _
    have e2 : ‖ubar - u‖ ≤ ‖ubar‖ + ‖u‖ := norm_sub_le _ _
    have hB' : ‖vbar - v‖ + ‖ubar - u‖ ≤ ε + stabB b c η astar := by
      unfold stabB
      have : 2 / η = 1 / η + 1 / η := by ring
      linarith
    have hBε : stabB b c η astar ≤ stabB b c η astar / stabEps b c η M astar * ε := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hε₀]; nlinarith
    have : 0 ≤ (stabC1 b c η M astar * (1 + b * (1 / η) ^ 2) + 1) * ε := by positivity
    unfold stabConst
    nlinarith

/-- **Stability of the cavity solution**: there is
`C = C(b, c, η, M, a_*)` such that for every finite law `(p, x)` (any index type), every `e`,
every `z'` with `Im z' ≥ η`, `|z'| ≤ M`, the exact solution `(v, u)` and every approximate pair
`(v̄, ū)` with `Im v̄ ≤ 0`, `|ū| ≥ a_*`, `-Im ū ≥ η|ū|²` and residuals at most `ε`:
`|v̄ - v| + |ū - u| ≤ C ε`. -/
theorem cavity_stability {b c η M astar : ℝ} (hb : 0 < b) (hc : 0 < c) (hη : 0 < η)
    (hM : 0 ≤ M) (ha : 0 < astar) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ι : Type) [Fintype ι] (p x : ι → ℝ) (e : ℝ) (z' v u vbar ubar : ℂ)
      (ε : ℝ), IsCavityWeights p → η ≤ z'.im → ‖z'‖ ≤ M →
      IsCavitySolution p x b c e z' v u → vbar.im ≤ 0 → astar ≤ ‖ubar‖ →
      η * ‖ubar‖ ^ 2 ≤ -ubar.im →
      ‖vbar - cavityStieltjes p x (-e - c * vbar - b * ubar)‖ ≤ ε →
      ‖ubar - (z' - b * vbar)⁻¹‖ ≤ ε →
      ‖vbar - v‖ + ‖ubar - u‖ ≤ C * ε :=
  ⟨stabConst b c η M astar, (stab_pos hb hc hη hM ha).2.2.2.2.2.2.2.2.2,
    fun _ _ _ _ _ _ _ _ _ _ _ hp hz hM' hsol hvb hua hport h1 h2 =>
      cavity_stability_of hp hb hc hη ha hz hM' hsol hvb hua hport h1 h2⟩

end Stability

end BlockBand.Endpoints.Clock
