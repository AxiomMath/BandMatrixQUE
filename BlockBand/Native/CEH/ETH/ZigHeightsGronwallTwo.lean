module

public import BlockBand.Native.CEH.ETH.ZigHeights

/-!
# CEH ETH, two-resolvent zig: the two-height modulus Grönwall

Grönwall bounds whose rate is the sum of the reciprocal heights of two resolvents along the
flow, with closed forms in terms of the product of the heights.

Setting. Variance time `u ≤ s`, heights `η_{i,u} = zigHeight η_i c_i s u` (`η_i > 0`, `c_i ≥ 0`),
product `P_u = zigHeightProd η₁ c₁ η₂ c₂ s u`, and the two-height rate
`twoHeightRate u = c₁ / η_{1,u} + c₂ / η_{2,u}`. The linear drift coefficient `a` (for the
A-chain `a = ⟨M^I⟩`) is abstract: the only input is the hypothesis
`‖a u‖ ≤ twoHeightRate u / 2` on `[0, T]` (`norm_NTrace_twoResApprox_one_le_mde` has this shape
up to unfolding `zigHeight`).
The chain coefficient is `k a` with `k = 1` (A-chain) or `k = 2` (I-chain).

Contents (`k ≥ 0` real, `T ≤ s`, all statements on `[0, T]`).
* `exp_integral_twoHeightRate`: `exp ∫_r^t (k/2) twoHeightRate = (P_r / P_t)^{k/2}`.
* `gronwall_twoHeight`: if `x t ≤ F t + ∫_0^t (k/2) twoHeightRate u · x u du` (`x, F`
  continuous), then `x t ≤ F t + ∫_0^t F r (k/2) twoHeightRate r (P_r / P_t)^{k/2} dr`.
* `gronwall_twoHeight_closed_add`: if moreover `F t ≤ K / (N P_t)^{k/2} + G t` (`N > 0`, `G`
  continuous; `F` need not be continuous), then
  `x t ≤ K / (N P_t)^{k/2} · (1 + (k/2) log (P_0 / P_t)) +
    (G t + ∫_0^t G r (k/2) twoHeightRate r (P_r / P_t)^{k/2} dr)`.
  The first term is exact: the Grönwall bound evaluates to it with equality.
* `gronwall_twoHeight_closed`: the case `G = 0`,
  `x t ≤ K / (N P_t)^{k/2} · (1 + (k/2) log (P_0 / P_t))`.
* Conversions from the complex form:
  `norm_le_integral_of_decomposition` (`X = E + ∫_0 k a X` gives
  `‖X t‖ ≤ ‖E t‖ + ∫_0^t k ‖a‖ ‖X‖`) and `norm_le_of_coeff_le_twoHeightRate` (with
  `‖a‖ ≤ twoHeightRate / 2` this becomes the hypothesis of `gronwall_twoHeight`, using
  `‖X‖ ≥ 0`).
* Headline: `norm_le_twoHeight_of_decomposition` (general `k`, additive `G`), and
  `norm_le_twoHeight_A` (`k = 1`: `‖E t‖ ≤ K / √(N P_t)` gives
  `‖X t‖ ≤ K / √(N P_t) · (1 + log (P_0 / P_t) / 2)`) and `norm_le_twoHeight_I` (`k = 2`,
  coefficient `2 a`: `‖E t‖ ≤ K / (N P_t)` gives `‖Y t‖ ≤ K / (N P_t) · (1 + log (P_0 / P_t))`).

The logarithm is the loss CEH absorb into the `N^{ξ}` margin in (7.6).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.ETH

open Set MeasureTheory intervalIntegral
open BlockBand.Native.CEH.Zig BlockBand.Native.CEH.Phase1

/-- The two-height rate `c₁ / η_{1,u} + c₂ / η_{2,u}` (`= -P'_u / P_u`). -/
def twoHeightRate (η₁ c₁ η₂ c₂ s u : ℝ) : ℝ :=
  c₁ / zigHeight η₁ c₁ s u + c₂ / zigHeight η₂ c₂ s u

variable {η₁ c₁ η₂ c₂ s : ℝ}

theorem twoHeightRate_nonneg (hη₁ : 0 < η₁) (hc₁ : 0 ≤ c₁) (hη₂ : 0 < η₂) (hc₂ : 0 ≤ c₂)
    {u : ℝ} (hu : u ≤ s) : 0 ≤ twoHeightRate η₁ c₁ η₂ c₂ s u := by
  have := zigHeight_pos hη₁ hc₁ hu
  have := zigHeight_pos hη₂ hc₂ hu
  unfold twoHeightRate
  positivity

theorem continuousOn_twoHeightRate (hη₁ : 0 < η₁) (hc₁ : 0 ≤ c₁) (hη₂ : 0 < η₂)
    (hc₂ : 0 ≤ c₂) {S : Set ℝ} (hS : ∀ r ∈ S, r ≤ s) :
    ContinuousOn (twoHeightRate η₁ c₁ η₂ c₂ s) S :=
  (continuousOn_const.div continuous_zigHeight.continuousOn fun r hr =>
      (zigHeight_pos hη₁ hc₁ (hS r hr)).ne').add
    (continuousOn_const.div continuous_zigHeight.continuousOn fun r hr =>
      (zigHeight_pos hη₂ hc₂ (hS r hr)).ne')

/-- `exp ∫_r^t (k/2) twoHeightRate = (P_r / P_t)^{k/2}` for `r, t ≤ s` (any order, any `k`). -/
theorem exp_integral_twoHeightRate (hη₁ : 0 < η₁) (hc₁ : 0 ≤ c₁) (hη₂ : 0 < η₂)
    (hc₂ : 0 ≤ c₂) {r t : ℝ} (hr : r ≤ s) (ht : t ≤ s) (k : ℝ) :
    Real.exp (∫ q in r..t, k / 2 * twoHeightRate η₁ c₁ η₂ c₂ s q) =
      (zigHeightProd η₁ c₁ η₂ c₂ s r / zigHeightProd η₁ c₁ η₂ c₂ s t) ^ (k / 2) := by
  rw [intervalIntegral.integral_const_mul]
  unfold twoHeightRate
  rw [integral_zigHeightProd_log hη₁ hc₁ hη₂ hc₂ hr ht,
    Real.rpow_def_of_pos (div_pos (zigHeightProd_pos hη₁ hc₁ hη₂ hc₂ hr)
      (zigHeightProd_pos hη₁ hc₁ hη₂ hc₂ ht)), mul_comm]

/-- `∫_0^t (k/2) twoHeightRate = (k/2) log (P_0 / P_t)` for `0, t ≤ s`. -/
theorem integral_twoHeightRate_zero (hη₁ : 0 < η₁) (hc₁ : 0 ≤ c₁) (hη₂ : 0 < η₂)
    (hc₂ : 0 ≤ c₂) {t : ℝ} (h0 : 0 ≤ s) (ht : t ≤ s) (k : ℝ) :
    ∫ q in (0 : ℝ)..t, k / 2 * twoHeightRate η₁ c₁ η₂ c₂ s q =
      k / 2 * Real.log (zigHeightProd η₁ c₁ η₂ c₂ s 0 / zigHeightProd η₁ c₁ η₂ c₂ s t) := by
  rw [intervalIntegral.integral_const_mul]
  unfold twoHeightRate
  rw [integral_zigHeightProd_log hη₁ hc₁ hη₂ hc₂ h0 ht]

/-!
## The two-height modulus Grönwall
-/

/-- **Two-height Grönwall.** Let `k ≥ 0`, `T ≤ s`, `x, F` continuous on `[0, T]` and
`x t ≤ F t + ∫_0^t (k/2) twoHeightRate u · x u du` on `[0, T]`. Then on `[0, T]`
`x t ≤ F t + ∫_0^t F r · (k/2) twoHeightRate r · (P_r / P_t)^{k/2} dr`. -/
theorem gronwall_twoHeight {x F : ℝ → ℝ} {k T : ℝ} (hη₁ : 0 < η₁) (hc₁ : 0 ≤ c₁)
    (hη₂ : 0 < η₂) (hc₂ : 0 ≤ c₂) (hk : 0 ≤ k) (hT : T ≤ s) (hx : ContinuousOn x (Icc 0 T))
    (hF : ContinuousOn F (Icc 0 T))
    (hle : ∀ t ∈ Icc 0 T,
      x t ≤ F t + ∫ u in (0 : ℝ)..t, k / 2 * twoHeightRate η₁ c₁ η₂ c₂ s u * x u) :
    ∀ t ∈ Icc 0 T, x t ≤ F t + ∫ r in (0 : ℝ)..t, F r * (k / 2 * twoHeightRate η₁ c₁ η₂ c₂ s r) *
      (zigHeightProd η₁ c₁ η₂ c₂ s r / zigHeightProd η₁ c₁ η₂ c₂ s t) ^ (k / 2) := by
  intro t ht
  have hA : ContinuousOn (fun u => k / 2 * twoHeightRate η₁ c₁ η₂ c₂ s u) (Icc 0 T) :=
    continuousOn_const.mul (continuousOn_twoHeightRate hη₁ hc₁ hη₂ hc₂ fun r hr => hr.2.trans hT)
  have hA0 : ∀ r ∈ Icc (0 : ℝ) T, 0 ≤ k / 2 * twoHeightRate η₁ c₁ η₂ c₂ s r := fun r hr =>
    mul_nonneg (by positivity) (twoHeightRate_nonneg hη₁ hc₁ hη₂ hc₂ (hr.2.trans hT))
  refine (gronwall_integral hx hA hF hA0 hle t ht).trans (le_of_eq ?_)
  congr 1
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le ht.1] at hr
  rw [exp_integral_twoHeightRate hη₁ hc₁ hη₂ hc₂ (hr.2.trans (ht.2.trans hT)) (ht.2.trans hT)]

/-- **Two-height Grönwall, closed form with an additive forcing.** Let `k ≥ 0`, `N > 0`,
`T ≤ s`, `x, G` continuous on `[0, T]`, `F t ≤ K / (N P_t)^{k/2} + G t` and
`x t ≤ F t + ∫_0^t (k/2) twoHeightRate u · x u du` on `[0, T]`. Then on `[0, T]`
`x t ≤ K / (N P_t)^{k/2} · (1 + (k/2) log (P_0 / P_t)) +
  (G t + ∫_0^t G r · (k/2) twoHeightRate r · (P_r / P_t)^{k/2} dr)`. -/
theorem gronwall_twoHeight_closed_add {x F G : ℝ → ℝ} {k T N K : ℝ} (hη₁ : 0 < η₁)
    (hc₁ : 0 ≤ c₁) (hη₂ : 0 < η₂) (hc₂ : 0 ≤ c₂) (hk : 0 ≤ k) (hN : 0 < N) (hT : T ≤ s)
    (hx : ContinuousOn x (Icc 0 T)) (hG : ContinuousOn G (Icc 0 T))
    (hF : ∀ t ∈ Icc 0 T, F t ≤ K / (N * zigHeightProd η₁ c₁ η₂ c₂ s t) ^ (k / 2) + G t)
    (hle : ∀ t ∈ Icc 0 T,
      x t ≤ F t + ∫ u in (0 : ℝ)..t, k / 2 * twoHeightRate η₁ c₁ η₂ c₂ s u * x u) :
    ∀ t ∈ Icc 0 T, x t ≤ K / (N * zigHeightProd η₁ c₁ η₂ c₂ s t) ^ (k / 2) *
        (1 + k / 2 * Real.log (zigHeightProd η₁ c₁ η₂ c₂ s 0 / zigHeightProd η₁ c₁ η₂ c₂ s t)) +
      (G t + ∫ r in (0 : ℝ)..t, G r * (k / 2 * twoHeightRate η₁ c₁ η₂ c₂ s r) *
        (zigHeightProd η₁ c₁ η₂ c₂ s r / zigHeightProd η₁ c₁ η₂ c₂ s t) ^ (k / 2)) := by
  intro t ht
  have hts : t ≤ s := ht.2.trans hT
  have h0s : (0 : ℝ) ≤ s := ht.1.trans hts
  set P := zigHeightProd η₁ c₁ η₂ c₂ s with hPdef
  set A : ℝ → ℝ := fun u => k / 2 * twoHeightRate η₁ c₁ η₂ c₂ s u with hAdef
  have hP : ∀ r, r ≤ s → 0 < P r := fun r hr => zigHeightProd_pos hη₁ hc₁ hη₂ hc₂ hr
  set B : ℝ → ℝ := fun r => K / (N * P r) ^ (k / 2) with hBdef
  have hBc : ContinuousOn B (Icc 0 T) := by
    refine continuousOn_const.div ((continuousOn_const.mul
      continuous_zigHeightProd.continuousOn).rpow_const fun r hr => Or.inl ?_) fun r hr => ?_
    · exact (mul_pos hN (hP r (hr.2.trans hT))).ne'
    · exact (Real.rpow_pos_of_pos (mul_pos hN (hP r (hr.2.trans hT))) _).ne'
  have hle' : ∀ u ∈ Icc 0 T, x u ≤ (fun r => B r + G r) u +
      ∫ q in (0 : ℝ)..u, A q * x q := fun u hu => by
    have := hF u hu
    have := hle u hu
    simp only [hBdef, hAdef]
    linarith
  have h : x t ≤ B t + G t + ∫ r in (0 : ℝ)..t, (B r + G r) * A r * (P r / P t) ^ (k / 2) :=
    gronwall_twoHeight hη₁ hc₁ hη₂ hc₂ hk hT hx (hBc.add hG) hle' t ht
  have hsub : uIcc 0 t ⊆ Icc 0 T := by
    rw [uIcc_of_le ht.1]
    exact Icc_subset_Icc_right ht.2
  have hAc : ContinuousOn A (Icc 0 T) :=
    continuousOn_const.mul (continuousOn_twoHeightRate hη₁ hc₁ hη₂ hc₂ fun r hr => hr.2.trans hT)
  have hRc : ContinuousOn (fun r => (P r / P t) ^ (k / 2)) (Icc 0 T) :=
    (continuous_zigHeightProd.continuousOn.div continuousOn_const fun _ _ =>
      (hP t hts).ne').rpow_const fun _ _ => Or.inr (by positivity)
  have i1 : IntervalIntegrable (fun r => B r * A r * (P r / P t) ^ (k / 2)) volume 0 t :=
    (((hBc.mul hAc).mul hRc).mono hsub).intervalIntegrable
  have i2 : IntervalIntegrable (fun r => G r * A r * (P r / P t) ^ (k / 2)) volume 0 t :=
    (((hG.mul hAc).mul hRc).mono hsub).intervalIntegrable
  have esplit : ∫ r in (0 : ℝ)..t, (B r + G r) * A r * (P r / P t) ^ (k / 2) =
      (∫ r in (0 : ℝ)..t, B r * A r * (P r / P t) ^ (k / 2)) +
        ∫ r in (0 : ℝ)..t, G r * A r * (P r / P t) ^ (k / 2) := by
    rw [← intervalIntegral.integral_add i1 i2]
    refine intervalIntegral.integral_congr fun r _ => ?_
    ring
  have eB : ∫ r in (0 : ℝ)..t, B r * A r * (P r / P t) ^ (k / 2) =
      B t * ∫ r in (0 : ℝ)..t, A r := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le ht.1] at hr
    have hPr := hP r (hr.2.trans hts)
    have hPt := hP t hts
    simp only [hBdef]
    rw [Real.mul_rpow hN.le hPr.le, Real.mul_rpow hN.le hPt.le, Real.div_rpow hPr.le hPt.le]
    have : 0 < N ^ (k / 2) := Real.rpow_pos_of_pos hN _
    have : 0 < P r ^ (k / 2) := Real.rpow_pos_of_pos hPr _
    have : 0 < P t ^ (k / 2) := Real.rpow_pos_of_pos hPt _
    field_simp
  have eA : ∫ r in (0 : ℝ)..t, A r = k / 2 * Real.log (P 0 / P t) :=
    integral_twoHeightRate_zero hη₁ hc₁ hη₂ hc₂ h0s hts k
  rw [esplit, eB, eA] at h
  have e2 : B t * (k / 2 * Real.log (P 0 / P t)) + B t =
      B t * (1 + k / 2 * Real.log (P 0 / P t)) := by ring
  simp only [hBdef] at h e2
  linarith

/-- **Two-height Grönwall, closed form.** Let `k ≥ 0`, `N > 0`, `T ≤ s`, `x` continuous on
`[0, T]`, `F t ≤ K / (N P_t)^{k/2}` and `x t ≤ F t + ∫_0^t (k/2) twoHeightRate u · x u du` on
`[0, T]`. Then on `[0, T]`, `x t ≤ K / (N P_t)^{k/2} · (1 + (k/2) log (P_0 / P_t))`. -/
theorem gronwall_twoHeight_closed {x F : ℝ → ℝ} {k T N K : ℝ} (hη₁ : 0 < η₁)
    (hc₁ : 0 ≤ c₁) (hη₂ : 0 < η₂) (hc₂ : 0 ≤ c₂) (hk : 0 ≤ k) (hN : 0 < N) (hT : T ≤ s)
    (hx : ContinuousOn x (Icc 0 T))
    (hF : ∀ t ∈ Icc 0 T, F t ≤ K / (N * zigHeightProd η₁ c₁ η₂ c₂ s t) ^ (k / 2))
    (hle : ∀ t ∈ Icc 0 T,
      x t ≤ F t + ∫ u in (0 : ℝ)..t, k / 2 * twoHeightRate η₁ c₁ η₂ c₂ s u * x u) :
    ∀ t ∈ Icc 0 T, x t ≤ K / (N * zigHeightProd η₁ c₁ η₂ c₂ s t) ^ (k / 2) *
        (1 + k / 2 *
          Real.log (zigHeightProd η₁ c₁ η₂ c₂ s 0 / zigHeightProd η₁ c₁ η₂ c₂ s t)) := by
  intro t ht
  have h := gronwall_twoHeight_closed_add (G := fun _ => 0) hη₁ hc₁ hη₂ hc₂ hk hN hT hx
    continuousOn_const (fun u hu => by simpa using hF u hu) hle t ht
  simpa using h

/-!
## From the complex form
-/

/-- **Complex form to modulus form.** If `k ≥ 0` and
`X t = E t + ∫_0^t k a(u) X u du` on `[0, T]`, then
`‖X t‖ ≤ ‖E t‖ + ∫_0^t k ‖a u‖ ‖X u‖ du` on `[0, T]`. -/
theorem norm_le_integral_of_decomposition {X E a : ℝ → ℂ} {k T : ℝ} (hk : 0 ≤ k)
    (hdec : ∀ t ∈ Icc 0 T, X t = E t + ∫ u in (0 : ℝ)..t, (k : ℂ) * a u * X u) :
    ∀ t ∈ Icc 0 T, ‖X t‖ ≤ ‖E t‖ + ∫ u in (0 : ℝ)..t, k * ‖a u‖ * ‖X u‖ := by
  intro t ht
  rw [hdec t ht]
  refine (norm_add_le _ _).trans (add_le_add_right ?_ _)
  refine (intervalIntegral.norm_integral_le_integral_norm ht.1).trans (le_of_eq ?_)
  refine intervalIntegral.integral_congr fun u _ => ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hk]

/-- **Coefficient bound.** If `X, a` are continuous on `[0, T]`, `T ≤ s`, `k ≥ 0`,
`‖a u‖ ≤ twoHeightRate u / 2` on `[0, T]` and `‖X t‖ ≤ F t + ∫_0^t k ‖a u‖ ‖X u‖ du` on
`[0, T]`, then `‖X t‖ ≤ F t + ∫_0^t (k/2) twoHeightRate u · ‖X u‖ du` on `[0, T]`. -/
theorem norm_le_of_coeff_le_twoHeightRate {X a : ℝ → ℂ} {F : ℝ → ℝ} {k T : ℝ}
    (hη₁ : 0 < η₁) (hc₁ : 0 ≤ c₁) (hη₂ : 0 < η₂) (hc₂ : 0 ≤ c₂) (hk : 0 ≤ k) (hT : T ≤ s)
    (hX : ContinuousOn X (Icc 0 T)) (ha : ContinuousOn a (Icc 0 T))
    (hab : ∀ u ∈ Icc 0 T, ‖a u‖ ≤ twoHeightRate η₁ c₁ η₂ c₂ s u / 2)
    (hle : ∀ t ∈ Icc 0 T, ‖X t‖ ≤ F t + ∫ u in (0 : ℝ)..t, k * ‖a u‖ * ‖X u‖) :
    ∀ t ∈ Icc 0 T,
      ‖X t‖ ≤ F t + ∫ u in (0 : ℝ)..t, k / 2 * twoHeightRate η₁ c₁ η₂ c₂ s u * ‖X u‖ := by
  intro t ht
  have hsub : uIcc 0 t ⊆ Icc 0 T := by
    rw [uIcc_of_le ht.1]
    exact Icc_subset_Icc_right ht.2
  refine (hle t ht).trans (add_le_add_right ?_ _)
  refine intervalIntegral.integral_mono_on ht.1
    (((continuousOn_const.mul ha.norm).mul hX.norm).mono hsub).intervalIntegrable
    (((continuousOn_const.mul (continuousOn_twoHeightRate hη₁ hc₁ hη₂ hc₂
      fun r hr => hr.2.trans hT)).mul hX.norm).mono hsub).intervalIntegrable fun u hu => ?_
  have huT : u ∈ Icc 0 T := ⟨hu.1, hu.2.trans ht.2⟩
  have h1 : k * ‖a u‖ ≤ k / 2 * twoHeightRate η₁ c₁ η₂ c₂ s u := by
    have := mul_le_mul_of_nonneg_left (hab u huT) hk
    linarith
  exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)

/-- **Headline, general `k`.** Let `η_i > 0`, `c_i ≥ 0`, `k ≥ 0`, `N > 0`, `T ≤ s`, `X, a`
continuous on `[0, T]`, `G` continuous on `[0, T]`, with
* `X t = E t + ∫_0^t k a(u) X u du` (complex form),
* `‖a u‖ ≤ (c₁ / η_{1,u} + c₂ / η_{2,u}) / 2` (coefficient bound),
* `‖E t‖ ≤ K / (N P_t)^{k/2} + G t` (forcing),
on `[0, T]`. Then on `[0, T]`
`‖X t‖ ≤ K / (N P_t)^{k/2} · (1 + (k/2) log (P_0 / P_t)) +
  (G t + ∫_0^t G r · (k/2) twoHeightRate r · (P_r / P_t)^{k/2} dr)`. -/
theorem norm_le_twoHeight_of_decomposition {X E a : ℝ → ℂ} {G : ℝ → ℝ} {k T N K : ℝ}
    (hη₁ : 0 < η₁) (hc₁ : 0 ≤ c₁) (hη₂ : 0 < η₂) (hc₂ : 0 ≤ c₂) (hk : 0 ≤ k) (hN : 0 < N)
    (hT : T ≤ s) (hX : ContinuousOn X (Icc 0 T)) (ha : ContinuousOn a (Icc 0 T))
    (hG : ContinuousOn G (Icc 0 T))
    (hdec : ∀ t ∈ Icc 0 T, X t = E t + ∫ u in (0 : ℝ)..t, (k : ℂ) * a u * X u)
    (hab : ∀ u ∈ Icc 0 T,
      ‖a u‖ ≤ (c₁ / zigHeight η₁ c₁ s u + c₂ / zigHeight η₂ c₂ s u) / 2)
    (hE : ∀ t ∈ Icc 0 T, ‖E t‖ ≤ K / (N * zigHeightProd η₁ c₁ η₂ c₂ s t) ^ (k / 2) + G t) :
    ∀ t ∈ Icc 0 T, ‖X t‖ ≤ K / (N * zigHeightProd η₁ c₁ η₂ c₂ s t) ^ (k / 2) *
        (1 + k / 2 * Real.log (zigHeightProd η₁ c₁ η₂ c₂ s 0 / zigHeightProd η₁ c₁ η₂ c₂ s t)) +
      (G t + ∫ r in (0 : ℝ)..t, G r * (k / 2 * twoHeightRate η₁ c₁ η₂ c₂ s r) *
        (zigHeightProd η₁ c₁ η₂ c₂ s r / zigHeightProd η₁ c₁ η₂ c₂ s t) ^ (k / 2)) :=
  gronwall_twoHeight_closed_add hη₁ hc₁ hη₂ hc₂ hk hN hT hX.norm hG hE
    (norm_le_of_coeff_le_twoHeightRate hη₁ hc₁ hη₂ hc₂ hk hT hX ha hab
      (norm_le_integral_of_decomposition hk hdec))

/-- **A-chain (`k = 1`).** Under the hypotheses of `norm_le_twoHeight_of_decomposition` with
`X t = E t + ∫_0^t a(u) X u du` and `‖E t‖ ≤ K / √(N P_t)` on `[0, T]`, on `[0, T]`
`‖X t‖ ≤ K / √(N P_t) · (1 + log (P_0 / P_t) / 2)`. -/
theorem norm_le_twoHeight_A {X E a : ℝ → ℂ} {T N K : ℝ}
    (hη₁ : 0 < η₁) (hc₁ : 0 ≤ c₁) (hη₂ : 0 < η₂) (hc₂ : 0 ≤ c₂) (hN : 0 < N)
    (hT : T ≤ s) (hX : ContinuousOn X (Icc 0 T)) (ha : ContinuousOn a (Icc 0 T))
    (hdec : ∀ t ∈ Icc 0 T, X t = E t + ∫ u in (0 : ℝ)..t, a u * X u)
    (hab : ∀ u ∈ Icc 0 T,
      ‖a u‖ ≤ (c₁ / zigHeight η₁ c₁ s u + c₂ / zigHeight η₂ c₂ s u) / 2)
    (hE : ∀ t ∈ Icc 0 T, ‖E t‖ ≤ K / Real.sqrt (N * zigHeightProd η₁ c₁ η₂ c₂ s t)) :
    ∀ t ∈ Icc 0 T, ‖X t‖ ≤ K / Real.sqrt (N * zigHeightProd η₁ c₁ η₂ c₂ s t) *
      (1 + Real.log (zigHeightProd η₁ c₁ η₂ c₂ s 0 / zigHeightProd η₁ c₁ η₂ c₂ s t) / 2) := by
  intro t ht
  have h := norm_le_twoHeight_of_decomposition (k := 1) (G := fun _ => 0) (K := K) hη₁ hc₁ hη₂
    hc₂ zero_le_one hN hT hX ha continuousOn_const (fun u hu => by simpa using hdec u hu) hab
    (fun u hu => by rw [add_zero, ← Real.sqrt_eq_rpow]; exact hE u hu) t ht
  simp only [← Real.sqrt_eq_rpow, zero_mul, intervalIntegral.integral_zero, add_zero] at h
  refine h.trans (le_of_eq ?_)
  ring

/-- **I-chain (`k = 2`, coefficient `2 a`).** Under the hypotheses of
`norm_le_twoHeight_of_decomposition` with `Y t = E t + ∫_0^t 2 a(u) Y u du` and
`‖E t‖ ≤ K / (N P_t)` on `[0, T]`, on `[0, T]`
`‖Y t‖ ≤ K / (N P_t) · (1 + log (P_0 / P_t))`. -/
theorem norm_le_twoHeight_I {Y E a : ℝ → ℂ} {T N K : ℝ}
    (hη₁ : 0 < η₁) (hc₁ : 0 ≤ c₁) (hη₂ : 0 < η₂) (hc₂ : 0 ≤ c₂) (hN : 0 < N)
    (hT : T ≤ s) (hY : ContinuousOn Y (Icc 0 T)) (ha : ContinuousOn a (Icc 0 T))
    (hdec : ∀ t ∈ Icc 0 T, Y t = E t + ∫ u in (0 : ℝ)..t, 2 * a u * Y u)
    (hab : ∀ u ∈ Icc 0 T,
      ‖a u‖ ≤ (c₁ / zigHeight η₁ c₁ s u + c₂ / zigHeight η₂ c₂ s u) / 2)
    (hE : ∀ t ∈ Icc 0 T, ‖E t‖ ≤ K / (N * zigHeightProd η₁ c₁ η₂ c₂ s t)) :
    ∀ t ∈ Icc 0 T, ‖Y t‖ ≤ K / (N * zigHeightProd η₁ c₁ η₂ c₂ s t) *
      (1 + Real.log (zigHeightProd η₁ c₁ η₂ c₂ s 0 / zigHeightProd η₁ c₁ η₂ c₂ s t)) := by
  intro t ht
  have h := norm_le_twoHeight_of_decomposition (k := 2) (G := fun _ => 0) hη₁ hc₁ hη₂ hc₂
    zero_le_two hN hT hY ha continuousOn_const (fun u hu => by simpa using hdec u hu) hab
    (fun u hu => by simpa using hE u hu) t ht
  simpa using h

end BlockBand.Native.CEH.ETH
