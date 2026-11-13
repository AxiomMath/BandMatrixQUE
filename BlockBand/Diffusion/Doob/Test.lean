module

public import BlockBand.Diffusion.Doob.MP
public import BlockBand.Diffusion.Base.TransitionLawHolds

/-!
# The duality functions of the `H` transform

Test pairs (`IsDkTestPair g k`): `g, k : ℝ → ℝ` continuous with values in `[0, 1]`, and `g = 0`
on `[R, ∞)` for some `R`. For a terminal time `t` put, in `Fin 2` coordinates
`w = (w₀, w₁)`, `ℓ(w) = w₀ + w₁ = H(w)⁻¹`,
`dkU D0 g k t (s, w) = ℓ(w) · P_{t-s}g(w₀) · P_{t-s}k(w₁)` (the product solution
`exProdSol`: `mkSemigroupX`, `skSemigroupY0`, with `P₀ = id`), i.e.
`u(s, ·) = H⁻¹ P_{t-s}(f H)` for `f = ℓ (g ⊗ k)`.

## Main results

For `D₀ > 0`:
* `dkU_isC02On_spGen`: `u` is `C^{0,2}` on `(0, t) × openStripFin` and solves
  `∂ₛu + 𝓛_H u = 0` there, `𝓛_H = mpGenerator (dkHDrift D0) (baseCov D0)`: the product rule
  `spGen_H(ℓ v) = ℓ spGen_0(v)` (`spGen_dkHDrift_mul`; it uses `Σᵢ (b_H)ᵢ = 0` and
  `(b_H)ᵢ - bᵢ = -aᵢᵢ/ℓ`, i.e. `𝒟₀H = 0` off the corner) and the product solution
  (`exProd_tmInputs`, `isC02On_prodU`, `spGen_prodU`);
* continuity on `(0, t] × openStripFin`, continuity within it at `(0, z)` for `z` in the closed
  strip (start continuity), `u(s, 0) = 0`, `|u(s, w)| ≤ 2 |w|`;
* `dkU_le`: **uniform boundedness** `0 ≤ u ≤ max R 0 + 1` on `[0, t] × openStripFin`, from the named
  hypothesis `DkLbkCornerHeatIdentity D0` (it gives `P_τ H ≤ H`, and `g ⊗ k ≤ (max R 0 + 1) H` on
  the strip minus the corner);
* `dkU_eq_integral`: `u(s, w) = ℓ(w) ∫ p_{t-s}(w, z') g(z'₁) k(z'₂) dz'` for `s < t`, and
  `u(t, w) = ℓ(w) g(w₀) k(w₁)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

/-!
### `C^{0,2}` data times a linear function of space
-/

section MulLin

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {v vt : ℝ × E → ℝ}
  {v1 : ℝ × E → E →L[ℝ] ℝ} {v2 : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ} {S : Set (ℝ × E)}

/-- `ℓ v` for a continuous linear `ℓ`. -/
theorem IsC02On.mul_lin (hv : IsC02On v vt v1 v2 S) (ℓ : E →L[ℝ] ℝ) :
    IsC02On (fun p => ℓ p.2 * v p) (fun p => ℓ p.2 * vt p) (fun p => ℓ p.2 • v1 p + v p • ℓ)
      (fun p => ℓ.smulRight (v1 p) + ℓ p.2 • v2 p + (v1 p).smulRight ℓ) S where
  hasDerivAt_time p hp := (hv.hasDerivAt_time p hp).const_mul (ℓ p.2)
  hasFDerivAt_space p hp := by
    have := (ℓ.hasFDerivAt (x := p.2)).mul (hv.hasFDerivAt_space p hp)
    exact this
  hasFDerivAt_space2 p hp := by
    have h1 := (ℓ.hasFDerivAt (x := p.2)).smul (hv.hasFDerivAt_space2 p hp)
    have h2 := (hv.hasFDerivAt_space p hp).smul_const ℓ
    have := h1.add h2
    convert this using 1
    abel
  continuousOn := (ℓ.continuous.comp continuous_snd).continuousOn.mul hv.continuousOn
  continuousOn_time := (ℓ.continuous.comp continuous_snd).continuousOn.mul hv.continuousOn_time
  continuousOn_space :=
    ((ℓ.continuous.comp continuous_snd).continuousOn.smul hv.continuousOn_space).add
      (hv.continuousOn.smul continuousOn_const)
  continuousOn_space2 :=
    ((((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ) ℓ).continuous.comp_continuousOn
      hv.continuousOn_space)).add
      ((ℓ.continuous.comp continuous_snd).continuousOn.smul hv.continuousOn_space2)).add
      (((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)).flip ℓ).continuous.comp_continuousOn
        hv.continuousOn_space)

end MulLin

/-- `ℓ(w) = w₀ + w₁`. -/
def dkEll : (Fin 2 → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0 +
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1

@[simp] theorem dkEll_apply (w : Fin 2 → ℝ) : dkEll w = w 0 + w 1 := rfl

/-- **The product rule for the `H` transform**: `spGen_H(ℓ v) = ℓ spGen_0(v)` on the open
strip. -/
theorem spGen_dkHDrift_mul (D0 : ℝ) {vt : ℝ × (Fin 2 → ℝ) → ℝ}
    {v1 : ℝ × (Fin 2 → ℝ) → (Fin 2 → ℝ) →L[ℝ] ℝ}
    {v2 : ℝ × (Fin 2 → ℝ) → (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) →L[ℝ] ℝ} (v : ℝ × (Fin 2 → ℝ) → ℝ)
    {p : ℝ × (Fin 2 → ℝ)} (hp : p.2 ∈ openStripFin) :
    spGen (dkHDrift D0) (baseCov D0) (fun p => dkEll p.2 * vt p)
        (fun p => dkEll p.2 • v1 p + v p • dkEll)
        (fun p => dkEll.smulRight (v1 p) + dkEll p.2 • v2 p + (v1 p).smulRight dkEll) p =
      dkEll p.2 * spGen (baseDrift D0) (baseCov D0) vt v1 v2 p := by
  have hne : p.2 0 + p.2 1 ≠ 0 := by have := hp.1; have := hp.2.1; positivity
  simp only [spGen, Fin.sum_univ_two, dkHDrift_apply]
  simp [baseDrift, baseCov]
  field_simp
  ring

/-!
### Test pairs and the duality function
-/

/-- Test pairs: continuous, values in `[0, 1]`, the first vanishing on `[R, ∞)`. -/
structure IsDkTestPair (g k : ℝ → ℝ) : Prop where
  contg : Continuous g
  contk : Continuous k
  g_nonneg : ∀ x, 0 ≤ g x
  g_le : ∀ x, g x ≤ 1
  k_nonneg : ∀ x, 0 ≤ k x
  k_le : ∀ x, k x ≤ 1
  supp : ∃ R : ℝ, ∀ x, R ≤ x → g x = 0

theorem IsDkTestPair.mul_le_one {g k : ℝ → ℝ} (hgk : IsDkTestPair g k) (x y : ℝ) :
    g x * k y ≤ 1 :=
  (mul_le_mul (hgk.g_le x) (hgk.k_le y) (hgk.k_nonneg y) zero_le_one).trans (by norm_num)

theorem IsDkTestPair.abs_le {g k : ℝ → ℝ} (hgk : IsDkTestPair g k) (x : ℝ) :
    |g x| ≤ 1 ∧ |k x| ≤ 1 :=
  ⟨by rw [abs_of_nonneg (hgk.g_nonneg x)]; exact hgk.g_le x,
    by rw [abs_of_nonneg (hgk.k_nonneg x)]; exact hgk.k_le x⟩

/-- The duality function `u(s, w) = ℓ(w) P_{t-s}g(w₀) P_{t-s}k(w₁)`. -/
def dkU (D0 : ℝ) (g k : ℝ → ℝ) (t : ℝ) (p : ℝ × (Fin 2 → ℝ)) : ℝ :=
  dkEll p.2 * prodU t (fun τ x => mkSemigroupX D0 g (τ, x)) (fun τ y => skSemigroupY0 D0 k (τ, y)) p

theorem dkU_eq_exProdSol (D0 : ℝ) (g k : ℝ → ℝ) (t : ℝ) (p : ℝ × (Fin 2 → ℝ)) :
    dkU D0 g k t p = dkEll p.2 * exProdSol D0 g k t (p.1, finProd p.2) := rfl

theorem dkU_zero (D0 : ℝ) (g k : ℝ → ℝ) (t r : ℝ) : dkU D0 g k t (r, 0) = 0 := by
  simp [dkU]

/-- `u(s, w) = ℓ(w) ∫ p_{t-s}(w, z') g(z'₁) k(z'₂) dz'` for `s < t`. -/
theorem dkU_eq_integral (D0 : ℝ) (g k : ℝ → ℝ) {s t : ℝ} (hst : s < t) (w : Fin 2 → ℝ) :
    dkU D0 g k t (s, w) = dkEll w *
      ∫ z', exKernel D0 (t - s) (finProd w) z' * (g z'.1 * k z'.2) := by
  rw [dkU_eq_exProdSol, exProdSol_eq_integral D0 g k hst]

theorem dkU_terminal (D0 : ℝ) (g k : ℝ → ℝ) (t : ℝ) (w : Fin 2 → ℝ) :
    dkU D0 g k t (t, w) = dkEll w * (g (w 0) * k (w 1)) := by
  rw [dkU_eq_exProdSol, exProdSol_terminal]; rfl

section Props

variable {D0 : ℝ} (hD0 : 0 < D0) {g k : ℝ → ℝ} (hgk : IsDkTestPair g k)
include hD0 hgk

theorem dkU_isC02On_spGen (t : ℝ≥0) {z : ℝ × ℝ} (hz : z ∈ exBaseStrip) :
    ∃ ut : ℝ × (Fin 2 → ℝ) → ℝ, ∃ u1 : ℝ × (Fin 2 → ℝ) → (Fin 2 → ℝ) →L[ℝ] ℝ,
      ∃ u2 : ℝ × (Fin 2 → ℝ) → (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) →L[ℝ] ℝ,
        IsC02On (dkU D0 g k t) ut u1 u2 (Ioo 0 (t : ℝ) ×ˢ openStripFin) ∧
        (∀ p ∈ Ioo 0 (t : ℝ) ×ˢ openStripFin,
          spGen (dkHDrift D0) (baseCov D0) ut u1 u2 p = 0) ∧
        ContinuousOn (dkU D0 g k t) (Ioc 0 (t : ℝ) ×ˢ openStripFin) ∧
        ContinuousWithinAt (dkU D0 g k t) (Ioc 0 (t : ℝ) ×ˢ openStripFin)
          (0, finProd.symm z) := by
  have hM : ∀ y, |g y| ≤ 1 := fun y => (hgk.abs_le y).1
  have hM' : ∀ y, |k y| ≤ 1 := fun y => (hgk.abs_le y).2
  obtain ⟨uXt, uX1, uX2, uYt, uY1, uY2, hX, hY, hXpde, hYpde, hXc, hYc, hX0, hY0, -, -⟩ :=
    exProd_tmInputs hD0 (mcKeanBackwardFacts_holds D0 hD0) hgk.contg hgk.contk hM hM'
      (NNReal.coe_nonneg t) hz
  have hX' : IsC02On1 _ uXt uX1 uX2 (Ioo 0 (t : ℝ)) (Ioi 0) :=
    ⟨hX.1, hX.2, hX.3, hX.4, hX.5, hX.6, hX.7⟩
  have hY' : IsC02On1 _ uYt uY1 uY2 (Ioo 0 (t : ℝ)) (Ioo 0 1) :=
    ⟨hY.1, hY.2, hY.3, hY.4, hY.5, hY.6, hY.7⟩
  have hv := isC02On_prodU hX' hY'
  refine ⟨_, _, _, hv.mul_lin dkEll, fun p hp => ?_, ?_, ?_⟩
  · rw [spGen_dkHDrift_mul D0 _ hp.2, spGen_prodU hXpde hYpde hp, mul_zero]
  · exact (dkEll.continuous.comp continuous_snd).continuousOn.mul (continuousOn_prodU hXc hYc)
  · exact (dkEll.continuous.comp continuous_snd).continuousWithinAt.mul
      (continuousWithinAt_prodU hX0 hY0)

theorem abs_prodU_le_one (t : ℝ) {p : ℝ × (Fin 2 → ℝ)} (hp : p.2 ∈ openStripFin) :
    |exProdSol D0 g k t (p.1, finProd p.2)| ≤ 1 := by
  have h := abs_exProdSol_le hD0 (fun y => (hgk.abs_le y).1)
    (fun y => (hgk.abs_le y).2) t (p := (p.1, finProd p.2))
    ⟨le_of_lt hp.1, hp.2.1.le, hp.2.2.le⟩
  simpa using h

theorem dkU_lin (t : ℝ) {p : ℝ × (Fin 2 → ℝ)} (hp : p.2 ∈ openStripFin) :
    |dkU D0 g k t p| ≤ 2 * ‖p.2 - 0‖ := by
  rw [dkU_eq_exProdSol, abs_mul, sub_zero]
  have h1 : |dkEll p.2| ≤ 2 * ‖p.2‖ := by
    rw [dkEll_apply]
    have h0 := norm_le_pi_norm p.2 0
    have h1 := norm_le_pi_norm p.2 1
    rw [Real.norm_eq_abs] at h0 h1
    calc |p.2 0 + p.2 1| ≤ |p.2 0| + |p.2 1| := abs_add_le _ _
      _ ≤ 2 * ‖p.2‖ := by linarith
  calc |dkEll p.2| * |exProdSol D0 g k t (p.1, finProd p.2)| ≤ (2 * ‖p.2‖) * 1 :=
        mul_le_mul h1 (abs_prodU_le_one hD0 hgk t hp) (abs_nonneg _) (by positivity)
    _ = 2 * ‖p.2‖ := mul_one _

end Props

/-!
### Uniform boundedness from the corner heat identity
-/

theorem exKernel_eq_zero_of_notMem {D0 t : ℝ} {w z' : ℝ × ℝ} (hz' : z' ∉ exBaseStrip) :
    exKernel D0 t w z' = 0 := by
  unfold exKernel
  simp only [exBaseStrip, mem_prod, mem_Ici, not_and_or] at hz'
  rcases hz' with h | h
  · simp [mkKernelX, h]
  · simp [skKernelY, h]

/-- `P_τ(g ⊗ k)(w) ≤ (max R 0 + 1) H(w)` from the corner heat identity. -/
theorem integral_exKernel_le_harm {D0 : ℝ} (hD0 : 0 < D0) (hCH : DkLbkCornerHeatIdentity D0)
    {g k : ℝ → ℝ} (hgk : IsDkTestPair g k) {R : ℝ} (hR : ∀ x, R ≤ x → g x = 0) {τ : ℝ}
    (hτ : 0 < τ) {w : ℝ × ℝ} (hw : w ∈ exBaseStrip) (hw0 : w ≠ (0, 0)) :
    ∫ z', exKernel D0 τ w z' * (g z'.1 * k z'.2) ≤ (max R 0 + 1) * dkHarm w := by
  set B := max R 0 + 1 with hB
  have hB0 : 0 < B := by positivity
  set F : ℝ × ℝ → ℝ := fun z' => g z'.1 * k z'.2 with hF
  have hF0 : ∀ z', 0 ≤ F z' := fun z' => mul_nonneg (hgk.g_nonneg _) (hgk.k_nonneg _)
  have hFm : Measurable F := (hgk.contg.measurable.comp measurable_fst).mul
    (hgk.contk.measurable.comp measurable_snd)
  have hint : Integrable fun z' => exKernel D0 τ w z' * F z' :=
    integrable_exKernel_mul hD0 hτ hw hFm.aestronglyMeasurable (C := 1) fun z' => by
      rw [abs_of_nonneg (hF0 z')]
      exact hgk.mul_le_one _ _
  have hpt : ∀ z', z' ≠ (0, 0) → ENNReal.ofReal (exKernel D0 τ w z' * F z') ≤
      ENNReal.ofReal B * (ENNReal.ofReal (exKernel D0 τ w z') *
        ENNReal.ofReal (dkHarm z')) := fun z' hz' => by
    by_cases hs : z' ∈ exBaseStrip
    · obtain ⟨hx, hy0, hy1⟩ : 0 ≤ z'.1 ∧ 0 ≤ z'.2 ∧ z'.2 ≤ 1 := ⟨hs.1, hs.2.1, hs.2.2⟩
      have hpos : 0 < z'.1 + z'.2 := by
        rcases (add_nonneg hx hy0).lt_or_eq with h | h
        · exact h
        · exfalso; apply hz'
          have h1 : z'.1 = 0 := by linarith
          have h2 : z'.2 = 0 := by linarith
          exact Prod.ext h1 h2
      have hFB : F z' ≤ B * dkHarm z' := by
        rw [dkHarm, ← div_eq_mul_inv, le_div_iff₀ hpos]
        by_cases hxR : R ≤ z'.1
        · simp only [hF, hR _ hxR, zero_mul]; exact hB0.le
        · push Not at hxR
          calc F z' * (z'.1 + z'.2) ≤ 1 * (z'.1 + z'.2) :=
                mul_le_mul_of_nonneg_right (hgk.mul_le_one _ _) hpos.le
            _ ≤ B := by
                rw [one_mul, hB]
                have : z'.1 ≤ max R 0 := hxR.le.trans (le_max_left _ _)
                linarith
      have hp0 := exKernel_nonneg hD0 τ w z'
      rw [← ENNReal.ofReal_mul hp0, ← ENNReal.ofReal_mul hB0.le]
      refine ENNReal.ofReal_le_ofReal ?_
      calc exKernel D0 τ w z' * F z' ≤ exKernel D0 τ w z' * (B * dkHarm z') :=
            mul_le_mul_of_nonneg_left hFB hp0
        _ = B * (exKernel D0 τ w z' * dkHarm z') := by ring
    · simp [exKernel_eq_zero_of_notMem hs]
  have hae : ∀ᵐ z' ∂(volume : Measure (ℝ × ℝ)), z' ≠ (0, 0) :=
    (measure_eq_zero_iff_ae_notMem.1 (measure_singleton ((0 : ℝ), (0 : ℝ)))).mono fun z' h => h
  have hL : ∫⁻ z', ENNReal.ofReal (exKernel D0 τ w z' * F z') ≤
      ENNReal.ofReal B * ENNReal.ofReal (dkHarm w) := by
    calc ∫⁻ z', ENNReal.ofReal (exKernel D0 τ w z' * F z')
        ≤ ∫⁻ z', ENNReal.ofReal B * (ENNReal.ofReal (exKernel D0 τ w z') *
            ENNReal.ofReal (dkHarm z')) :=
          lintegral_mono_ae (hae.mono fun z' hz' => hpt z' hz')
      _ = ENNReal.ofReal B * ∫⁻ z', ENNReal.ofReal (exKernel D0 τ w z') *
            ENNReal.ofReal (dkHarm z') := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal B * ENNReal.ofReal (dkHarm w) := by
          have := hCH w hw hw0 τ hτ
          gcongr
          rw [← this]
          exact le_self_add
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z' =>
    mul_nonneg (exKernel_nonneg hD0 _ _ _) (hF0 z')) hint.aestronglyMeasurable]
  have hHw : 0 ≤ dkHarm w := by rw [dkHarm]; exact inv_nonneg.2 (add_nonneg hw.1 hw.2.1)
  calc (∫⁻ z', ENNReal.ofReal (exKernel D0 τ w z' * F z')).toReal
      ≤ (ENNReal.ofReal B * ENNReal.ofReal (dkHarm w)).toReal :=
        ENNReal.toReal_mono (by finiteness) hL
    _ = B * dkHarm w := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB0.le, ENNReal.toReal_ofReal hHw]

/-- **Uniform boundedness of the duality function**: `0 ≤ u ≤ max R 0 + 1` on
`[0, t] × openStripFin`. -/
theorem dkU_le {D0 : ℝ} (hD0 : 0 < D0) (hCH : DkLbkCornerHeatIdentity D0) {g k : ℝ → ℝ}
    (hgk : IsDkTestPair g k) {R : ℝ} (hR : ∀ x, R ≤ x → g x = 0) {t : ℝ}
    {p : ℝ × (Fin 2 → ℝ)} (hpt : p.1 ≤ t) (hp : p.2 ∈ openStripFin) :
    0 ≤ dkU D0 g k t p ∧ dkU D0 g k t p ≤ max R 0 + 1 := by
  have hℓ : 0 < dkEll p.2 := by rw [dkEll_apply]; have := hp.1; have := hp.2.1; positivity
  have hstrip : finProd p.2 ∈ exBaseStrip := ⟨le_of_lt hp.1, hp.2.1.le, hp.2.2.le⟩
  have hne : finProd p.2 ≠ (0, 0) := fun h => by
    have : (finProd p.2).1 = 0 := by rw [h]
    have h0 := hp.1
    simp at this
    linarith
  rcases hpt.lt_or_eq with hlt | heq
  · rw [show p = (p.1, p.2) from rfl, dkU_eq_integral D0 g k hlt]
    have hI0 : 0 ≤ ∫ z', exKernel D0 (t - p.1) (finProd p.2) z' * (g z'.1 * k z'.2) :=
      integral_nonneg fun z' => mul_nonneg (exKernel_nonneg hD0 _ _ _)
        (mul_nonneg (hgk.g_nonneg _) (hgk.k_nonneg _))
    refine ⟨mul_nonneg hℓ.le hI0, ?_⟩
    have hI := integral_exKernel_le_harm hD0 hCH hgk hR (sub_pos.2 hlt) hstrip hne
    have hH : dkEll p.2 * dkHarm (finProd p.2) = 1 := by
      rw [dkHarm]; simp only [dkEll_apply] at hℓ ⊢
      have : (finProd p.2).1 + (finProd p.2).2 = p.2 0 + p.2 1 := rfl
      rw [this]; field_simp
    calc dkEll p.2 * ∫ z', exKernel D0 (t - p.1) (finProd p.2) z' * (g z'.1 * k z'.2)
        ≤ dkEll p.2 * ((max R 0 + 1) * dkHarm (finProd p.2)) :=
          mul_le_mul_of_nonneg_left hI hℓ.le
      _ = max R 0 + 1 := by rw [mul_left_comm, hH, mul_one]
  · rw [show p = (t, p.2) by rw [← heq], dkU_terminal D0 g k]
    have h01 := hp.2.2
    have hgk1 : g (p.2 0) * k (p.2 1) ≤ 1 := hgk.mul_le_one _ _
    have hgk0 : 0 ≤ g (p.2 0) * k (p.2 1) := mul_nonneg (hgk.g_nonneg _) (hgk.k_nonneg _)
    refine ⟨mul_nonneg hℓ.le hgk0, ?_⟩
    by_cases hxR : R ≤ p.2 0
    · simp [hR _ hxR]; positivity
    · push Not at hxR
      calc dkEll p.2 * (g (p.2 0) * k (p.2 1)) ≤ dkEll p.2 * 1 :=
            mul_le_mul_of_nonneg_left hgk1 hℓ.le
        _ ≤ max R 0 + 1 := by
            rw [mul_one, dkEll_apply]
            have : p.2 0 ≤ max R 0 := hxR.le.trans (le_max_left _ _)
            linarith

end BlockBand.Diffusion
