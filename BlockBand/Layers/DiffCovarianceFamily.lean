module

public import BlockBand.Layers.DiffCovariance
public import BlockBand.Layers.WeightedLayer

/-!
# The differentiated conditional covariance along curved and energy families

`DiffCovarianceStatement` differentiates along the exactly linear source family `X - hS`. The
differentiated-covariance lemma covers every family `X(h) = X - hS + O(h²)`, and the tagged-trace
lemma differentiates along

* curved source families (`∂_{ξ_g}` of the old Schur input), and
* the energy family `E ↦ (E, z_∂(E), X(E))`, in which `E`, the port parameter and the old input
  move together.

This module states both as `DiffCovarianceFamilyStatement` and proves it
(`diffCovarianceFamily_holds`) from the same inputs as `diffCovariance_holds`.

Proof.
1. **Abstract curved family** (`tgt_hasDerivAt_cov_family`): if `G_h - G₀ = -G_h Δ(h) G₀` with a
   deterministic insertion `Δ`, `Δ(0) = 0`, `Δ'(0) = P`, and `E‖G_h‖⁴` is bounded for `|h| ≤ δ`,
   then `h ↦ Cov(τ(G_h), G_h)` has derivative `Cov(τ(𝒢̇), G₀) + Cov(τ(G₀), 𝒢̇)`, `𝒢̇ = -G₀PG₀`.
   This is the remainder proof of `dcv_hasDerivAt_cov` with one extra term:
   `G_h - G₀ - h𝒢̇ = -(G_h - G₀)Δ(h)G₀ - G₀(Δ(h) - hP)G₀`, where `‖Δ(h) - hP‖ = o(h)`
   (`tgt_expand_le`, `tgt_quad_alg`, `tgt_hasDerivAt_of_rem`). Only `HasDerivAt` of the
   deterministic family is needed, not a quadratic remainder.
2. **Layer families** (`tgt_layer_family`): the layer matrix of the family is `𝒢(0)⁻¹ + Δ(h)`.
   For the curved family `Δ(h) = diag(X - X(h), 0)`, so `Δ'(0) = Ŝ`. For the energy family
   `Δ(t) = diag(-t + X(E₀) - X(E₀ + t), z_∂(E₀ + t) - z_∂(E₀))`, so
   `Δ'(0) = diag(-(I + X'), z_∂' I) = -Ŝ + D₀` with `S = X'(E₀)` and `D₀ = tgtD0 z_∂'`.
   The pointwise derivative of `W⁻¹ Tr(D𝒢)` uses invertibility at the base point only
   (`tgt_hasDerivAt_inv_family`).
3. **Scalars** (`tgt_hasDerivAt_matchedA`, `tgt_hasDerivAt_boundaryZ`, `tgt_energy_cancel`):
   `a' = a²/(1 - a²)`, `z_∂' = (b - a⁻²)a'` and `1 + (1-b)a' + z_∂' = 0` on `(-2, 2)`
   (checked), with `|z_∂'| ≤ (b + 1)/√(2κ)` on `bulkInterval κ`.
4. **Bounds.** The derivative values are the same objects as in `DiffCovarianceStatement`, so
   the bounds are taken from `dcv_cov_clause` and `dcv_noise_clause`. For the energy direction
   `-Ŝ + D₀ = -(Ŝ + (-D₀))`, linearity (`tgt_dcvCovDir_neg`) and the insertion clause with
   `‖-D₀‖ ≤ 1 + (b+1)/√(2κ)` give `C(1+u)/W` and `C_p(1+u)/√W`. The moments near `E₀` come
   from the Gaussian absorption lemma on `bulkInterval (κ/2)`.

Scope: separate-port layers at `z = z_∂(E)` only, as in `DiffCovarianceStatement` and
`WeightedLayerContract`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix Filter Topology Asymptotics
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs (GaussianLpGradient ConditionalBlockGUECount)
open scoped ENNReal NNReal ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

/-!
## 1. The scalar energy derivatives
-/

/-- `a'(E) = a²/(1 - a²)`, the energy derivative of the matched value `a = matchedA E`. -/
def tgtAd (E : ℝ) : ℂ := matchedA E ^ 2 / (1 - matchedA E ^ 2)

/-- `z_∂'(E) = (b - a⁻²) a'`, the energy derivative of `z_∂ = a⁻¹ + b a`. -/
def tgtZd (b E : ℝ) : ℂ := ((b : ℂ) - ((matchedA E)⁻¹) ^ 2) * tgtAd E

/-- `a = -E/2 - i√(4-E²)/2` as a sum of real and imaginary parts. -/
theorem tgt_matchedA_eq (E : ℝ) :
    matchedA E = ((-E / 2 : ℝ) : ℂ) + ((-Real.sqrt (4 - E ^ 2) / 2 : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [matchedA]

/-- `a ≠ 0` for `|E| ≤ 2` (`|a| = 1`). -/
theorem tgt_matchedA_ne_zero {E : ℝ} (hE : |E| ≤ 2) : matchedA E ≠ 0 := by
  intro h; have := norm_matchedA hE; rw [h, norm_zero] at this; exact zero_ne_one this

/-- `a² ≠ 1` for `|E| < 2` (`Im a < 0`). -/
theorem tgt_one_sub_sq_ne_zero {E : ℝ} (hE : |E| < 2) : 1 - matchedA E ^ 2 ≠ 0 := by
  intro h
  have him := matchedA_im_neg hE
  have h2 : (matchedA E - 1) * (matchedA E + 1) = 0 := by linear_combination -h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · have : matchedA E = 1 := sub_eq_zero.mp h3
    rw [this, Complex.one_im] at him; exact lt_irrefl 0 him
  · have : matchedA E = -1 := eq_neg_of_add_eq_zero_left h3
    rw [this] at him; simp at him

/-- Some explicit derivative of `matchedA` at `|E| < 2`. -/
theorem tgt_hasDerivAt_matchedA_aux {E : ℝ} (hE : |E| < 2) :
    ∃ v : ℂ, HasDerivAt matchedA v E := by
  have hpos : 0 < 4 - E ^ 2 := by
    have := abs_lt.mp hE; nlinarith
  have h1 : HasDerivAt (fun x : ℝ => 4 - x ^ 2) (-(2 * E)) E := by
    simpa using (hasDerivAt_pow 2 E).const_sub 4
  have h2 := h1.sqrt hpos.ne'
  have h3 : HasDerivAt (fun x : ℝ => ((-x / 2 : ℝ) : ℂ) +
      ((-Real.sqrt (4 - x ^ 2) / 2 : ℝ) : ℂ) * Complex.I) _ E :=
    (((hasDerivAt_id E).neg.div_const 2).ofReal_comp).add
      (((h2.neg.div_const 2).ofReal_comp).mul_const Complex.I)
  have e : matchedA = fun x : ℝ => ((-x / 2 : ℝ) : ℂ) +
      ((-Real.sqrt (4 - x ^ 2) / 2 : ℝ) : ℂ) * Complex.I := funext tgt_matchedA_eq
  exact ⟨_, by rw [e]; exact h3⟩

/-- `a' = a²/(1 - a²)` on the open bulk (the tagged-trace lemma). -/
theorem tgt_hasDerivAt_matchedA {E : ℝ} (hE : E ∈ Set.Ioo (-2 : ℝ) 2) :
    HasDerivAt matchedA (tgtAd E) E := by
  have hE' : |E| < 2 := abs_lt.mpr hE
  obtain ⟨v, hv⟩ := tgt_hasDerivAt_matchedA_aux hE'
  have ha0 := tgt_matchedA_ne_zero hE'.le
  have hs : HasDerivAt (fun x => matchedA x + (matchedA x)⁻¹) (v + -v / matchedA E ^ 2) E :=
    hv.add (hv.inv ha0)
  have hev : (fun x => matchedA x + (matchedA x)⁻¹) =ᶠ[𝓝 E] fun x => -((x : ℝ) : ℂ) := by
    filter_upwards [Ioo_mem_nhds hE.1 hE.2] with x hx
    exact matchedA_add_inv (abs_lt.mpr hx).le
  have hm : HasDerivAt (fun x : ℝ => -((x : ℝ) : ℂ)) (-1) E := by
    have h := ((hasDerivAt_id E).ofReal_comp).neg
    exact h
  have hu : v + -v / matchedA E ^ 2 = -1 := (hs.congr_of_eventuallyEq hev.symm).unique hm
  have h1 := tgt_one_sub_sq_ne_zero hE'
  have hv' : v = tgtAd E := by
    unfold tgtAd
    rw [eq_div_iff h1]
    have ha2 : matchedA E ^ 2 ≠ 0 := pow_ne_zero 2 ha0
    field_simp at hu
    linear_combination -hu
  rw [← hv']; exact hv

/-- `z_∂' = (b - a⁻²) a'` on the open bulk. -/
theorem tgt_hasDerivAt_boundaryZ (b : ℝ) {E : ℝ} (hE : E ∈ Set.Ioo (-2 : ℝ) 2) :
    HasDerivAt (boundaryZ b) (tgtZd b E) E := by
  have hE' : |E| < 2 := abs_lt.mpr hE
  have ha0 := tgt_matchedA_ne_zero hE'.le
  have hv := tgt_hasDerivAt_matchedA hE
  have h := (hv.inv ha0).add (hv.const_mul (b : ℂ))
  have e : boundaryZ b = fun x => (matchedA x)⁻¹ + (b : ℂ) * matchedA x := by
    funext x; rfl
  rw [e]
  convert h using 1
  unfold tgtZd
  field_simp
  ring

/-- **The energy cancellation** `1 + (1 - b) a' + z' = 0`. -/
theorem tgt_energy_cancel (b : ℝ) {E : ℝ} (hE : E ∈ Set.Ioo (-2 : ℝ) 2) :
    1 + (1 - (b : ℂ)) * tgtAd E + tgtZd b E = 0 := by
  have hE' : |E| < 2 := abs_lt.mpr hE
  have ha0 := tgt_matchedA_ne_zero hE'.le
  have h1 := tgt_one_sub_sq_ne_zero hE'
  unfold tgtZd tgtAd
  field_simp
  ring

/-- `|1 - a²|² = 4 - E²` for `|E| ≤ 2`. -/
theorem tgt_norm_one_sub_sq {E : ℝ} (hE : |E| ≤ 2) :
    ‖1 - matchedA E ^ 2‖ ^ 2 = 4 - E ^ 2 := by
  rw [matchedA_sq hE, Complex.sq_norm, Complex.normSq_apply]
  have hs := sqrt_four_sub_sq_sq hE
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
  linear_combination ((E ^ 2) / 4) * hs

/-- Uniform bound `‖z_∂'‖ ≤ (b + 1)/√(2κ)` on `bulkInterval κ`. -/
theorem tgt_norm_tgtZd_le {b κ E : ℝ} (hb : 0 ≤ b) (hκ : 0 < κ) (hE : E ∈ bulkInterval κ) :
    ‖tgtZd b E‖ ≤ (b + 1) / Real.sqrt (2 * κ) := by
  have hE2 := abs_le_of_mem_bulkInterval hE
  have hE1 : |E| ≤ 2 := by linarith
  have hk2 : κ ≤ 2 := by linarith [abs_nonneg E]
  have hsq := sq_le_of_mem_bulkInterval hE
  have hn1 := norm_matchedA hE1
  have hlow : 2 * κ ≤ ‖1 - matchedA E ^ 2‖ ^ 2 := by
    rw [tgt_norm_one_sub_sq hE1]; nlinarith
  have hs0 : 0 < Real.sqrt (2 * κ) := Real.sqrt_pos.mpr (by linarith)
  have hlow' : Real.sqrt (2 * κ) ≤ ‖1 - matchedA E ^ 2‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (1 - matchedA E ^ 2))]; exact Real.sqrt_le_sqrt hlow
  have hb1 : ‖(b : ℂ) - ((matchedA E)⁻¹) ^ 2‖ ≤ b + 1 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_pow, norm_inv, hn1, Complex.norm_real, Real.norm_of_nonneg hb]; norm_num
  unfold tgtZd tgtAd
  rw [norm_mul, norm_div, norm_pow, hn1, one_pow, one_div]
  calc ‖(b : ℂ) - ((matchedA E)⁻¹) ^ 2‖ * ‖1 - matchedA E ^ 2‖⁻¹
      ≤ (b + 1) * (Real.sqrt (2 * κ))⁻¹ :=
        mul_le_mul hb1 (inv_anti₀ hs0 hlow') (by positivity) (by linarith)
    _ = (b + 1) / Real.sqrt (2 * κ) := by ring

/-!
## 2. The covariance derivative along a curved family
-/

/-- `HasDerivAt` from a remainder bound `K (t² + r t)` on `|t| ≤ δ` with `r = o(t)`. -/
theorem tgt_hasDerivAt_of_rem {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {φ : ℝ → F}
    {φ' : F} {δ K : ℝ} (hδ : 0 < δ) {r : ℝ → ℝ} (hr0 : ∀ t, 0 ≤ r t)
    (hr : r =o[𝓝 0] fun t => t)
    (h : ∀ t : ℝ, |t| ≤ δ → ‖φ t - φ 0 - t • φ'‖ ≤ K * (t ^ 2 + r t)) :
    HasDerivAt φ φ' 0 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have hO : (fun t : ℝ => φ (0 + t) - φ 0 - t • φ') =O[𝓝 0] fun t : ℝ => t ^ 2 + r t := by
    refine IsBigO.of_bound K ?_
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) hδ] with t ht
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at ht
    rw [zero_add, Real.norm_of_nonneg (add_nonneg (sq_nonneg t) (hr0 t))]
    exact h t ht
  have hs : (fun t : ℝ => t ^ 2 + r t) =o[𝓝 0] fun t => t :=
    (isLittleO_pow_id (by norm_num : 1 < 2)).add hr
  exact hO.trans_isLittleO hs

section Abs
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The real arithmetic of `tgt_expand_le`. -/
theorem tgt_expand_real {a c p d e h c₁ cτ : ℝ} (ha0 : 0 ≤ a) (hc0 : 0 ≤ c) (hp0 : 0 ≤ p)
    (hd0 : 0 ≤ d) (he0 : 0 ≤ e) (hc₁ : 0 ≤ c₁) (hcτ : 0 ≤ cτ) (hΔ : d ≤ c₁ * |h|) :
    a * d * c ≤ |h| * (c₁ * (1 + a ^ 4 + c ^ 4)) ∧
    d ^ 2 * (a * c ^ 2) + e * c ^ 2 ≤ (h ^ 2 + e) * ((c₁ ^ 2 + 1) * (1 + a ^ 4 + c ^ 4)) ∧
    cτ * (d ^ 2 * (a * c ^ 2) + e * c ^ 2) * a + (cτ * c) * (d ^ 2 * (a * c ^ 2) + e * c ^ 2) +
        |h| * (cτ * (p * c ^ 2)) * (a * d * c) ≤
      (h ^ 2 + e) * (cτ * (2 * c₁ ^ 2 + p * c₁ + 2) * (1 + a ^ 4 + c ^ 4)) := by
  set Q := 1 + a ^ 4 + c ^ 4 with hQ
  have hh0 : 0 ≤ |h| := abs_nonneg h
  have hh2 : |h| ^ 2 = h ^ 2 := sq_abs h
  have q11 : a * c ≤ Q := by simpa using dcv_mono_le ha0 hc0 (i := 1) (j := 1) (by norm_num)
  have q02 : c ^ 2 ≤ Q := by simpa using dcv_mono_le ha0 hc0 (i := 0) (j := 2) (by norm_num)
  have q12 : a * c ^ 2 ≤ Q := by simpa using dcv_mono_le ha0 hc0 (i := 1) (j := 2) (by norm_num)
  have q03 : c ^ 3 ≤ Q := by simpa using dcv_mono_le ha0 hc0 (i := 0) (j := 3) (by norm_num)
  have q22 : a ^ 2 * c ^ 2 ≤ Q := dcv_mono_le ha0 hc0 (by norm_num)
  have q13 : a * c ^ 3 ≤ Q := by simpa using dcv_mono_le ha0 hc0 (i := 1) (j := 3) (by norm_num)
  have hQ0 : 0 ≤ Q := by positivity
  have hd2 : d ^ 2 ≤ c₁ ^ 2 * h ^ 2 := by
    have := pow_le_pow_left₀ hd0 hΔ 2
    rwa [mul_pow, hh2] at this
  have hhd : |h| * d ≤ c₁ * h ^ 2 := by
    have := mul_le_mul_of_nonneg_left hΔ hh0
    rw [← hh2]; linarith [show |h| * (c₁ * |h|) = c₁ * |h| ^ 2 by ring]
  refine ⟨?_, ?_, ?_⟩
  · calc a * d * c = d * (a * c) := by ring
      _ ≤ (c₁ * |h|) * Q := mul_le_mul hΔ q11 (by positivity) (by positivity)
      _ = |h| * (c₁ * Q) := by ring
  · have u0 : d ^ 2 * (a * c ^ 2) ≤ c₁ ^ 2 * h ^ 2 * Q :=
      mul_le_mul hd2 q12 (by positivity) (by positivity)
    have u2 : e * c ^ 2 ≤ e * Q := mul_le_mul_of_nonneg_left q02 he0
    have : c₁ ^ 2 * h ^ 2 * Q + e * Q ≤ (h ^ 2 + e) * ((c₁ ^ 2 + 1) * Q) := by
      have : 0 ≤ e * c₁ ^ 2 * Q + h ^ 2 * Q := by positivity
      nlinarith
    linarith
  · have s1 : cτ * (d ^ 2 * (a * c ^ 2) + e * c ^ 2) * a =
        cτ * d ^ 2 * (a ^ 2 * c ^ 2) + cτ * e * (a * c ^ 2) := by ring
    have s2 : (cτ * c) * (d ^ 2 * (a * c ^ 2) + e * c ^ 2) =
        cτ * d ^ 2 * (a * c ^ 3) + cτ * e * c ^ 3 := by ring
    have s3 : |h| * (cτ * (p * c ^ 2)) * (a * d * c) = (cτ * p * (a * c ^ 3)) * (|h| * d) := by
      ring
    have v1 : cτ * d ^ 2 * (a ^ 2 * c ^ 2) ≤ cτ * (c₁ ^ 2 * h ^ 2) * Q :=
      mul_le_mul (mul_le_mul_of_nonneg_left hd2 hcτ) q22 (by positivity) (by positivity)
    have v2 : cτ * e * (a * c ^ 2) ≤ cτ * e * Q := mul_le_mul_of_nonneg_left q12 (by positivity)
    have v3 : cτ * d ^ 2 * (a * c ^ 3) ≤ cτ * (c₁ ^ 2 * h ^ 2) * Q :=
      mul_le_mul (mul_le_mul_of_nonneg_left hd2 hcτ) q13 (by positivity) (by positivity)
    have v4 : cτ * e * c ^ 3 ≤ cτ * e * Q := mul_le_mul_of_nonneg_left q03 (by positivity)
    have v5 : (cτ * p * (a * c ^ 3)) * (|h| * d) ≤ (cτ * p * Q) * (c₁ * h ^ 2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left q13 (by positivity)) hhd (by positivity)
        (by positivity)
    rw [s1, s2, s3]
    have fin : cτ * (c₁ ^ 2 * h ^ 2) * Q + cτ * e * Q + cτ * (c₁ ^ 2 * h ^ 2) * Q + cτ * e * Q +
        (cτ * p * Q) * (c₁ * h ^ 2) ≤ (h ^ 2 + e) * (cτ * (2 * c₁ ^ 2 + p * c₁ + 2) * Q) := by
      have : 0 ≤ cτ * e * Q * (2 * c₁ ^ 2 + p * c₁) + cτ * h ^ 2 * Q * 2 := by positivity
      nlinarith
    linarith

/-- **Second-order expansion along a curved family** (deterministic): if
`G_h - G₀ = -G_h Δ G₀` with `‖Δ‖ ≤ c₁|h|` and `e = ‖Δ - hP‖`, then with `𝒢̇ = -G₀PG₀` and
`Q = 1 + ‖G_h‖⁴ + ‖G₀‖⁴` the four remainders are `O(|h|)`, resp. `O(h² + e)`. -/
theorem tgt_expand_le (τ : Matrix ι ι ℂ →L[ℝ] ℂ) {cτ : ℝ} (hcτ : 0 ≤ cτ)
    (hτ : ∀ N, ‖τ N‖ ≤ cτ * ‖N‖) {Gh G0 P Δ : Matrix ι ι ℂ} {h c₁ : ℝ} (hc₁ : 0 ≤ c₁)
    (hres : Gh - G0 = -(Gh * Δ * G0)) (hΔ : ‖Δ‖ ≤ c₁ * |h|) :
    ‖Gh - G0‖ ≤ |h| * (c₁ * (1 + ‖Gh‖ ^ 4 + ‖G0‖ ^ 4)) ∧
    ‖Gh - G0 - (h : ℂ) • -(G0 * P * G0)‖ ≤
      (h ^ 2 + ‖Δ - (h : ℂ) • P‖) * ((c₁ ^ 2 + 1) * (1 + ‖Gh‖ ^ 4 + ‖G0‖ ^ 4)) ∧
    ‖τ Gh - τ G0 - (h : ℂ) * τ (-(G0 * P * G0))‖ ≤
      (h ^ 2 + ‖Δ - (h : ℂ) • P‖) * (cτ * (c₁ ^ 2 + 1) * (1 + ‖Gh‖ ^ 4 + ‖G0‖ ^ 4)) ∧
    ‖τ Gh • Gh - τ G0 • G0 - (h : ℂ) • (τ (-(G0 * P * G0)) • G0 + τ G0 • -(G0 * P * G0))‖ ≤
      (h ^ 2 + ‖Δ - (h : ℂ) • P‖) *
        (cτ * (2 * c₁ ^ 2 + ‖P‖ * c₁ + 2) * (1 + ‖Gh‖ ^ 4 + ‖G0‖ ^ 4)) := by
  obtain ⟨r1, r2, r3⟩ := tgt_expand_real (norm_nonneg Gh) (norm_nonneg G0) (norm_nonneg P)
    (norm_nonneg Δ) (norm_nonneg (Δ - (h : ℂ) • P)) hc₁ hcτ hΔ
  have hhc : ‖(h : ℂ)‖ = |h| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have m3 : ∀ A B C : Matrix ι ι ℂ, ‖A * B * C‖ ≤ ‖A‖ * ‖B‖ * ‖C‖ := fun A B C =>
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
  have e1' : ‖Gh - G0‖ ≤ ‖Gh‖ * ‖Δ‖ * ‖G0‖ := by rw [hres, norm_neg]; exact m3 _ _ _
  have e2eq : Gh - G0 - (h : ℂ) • -(G0 * P * G0) =
      -((Gh - G0) * Δ * G0) - G0 * (Δ - (h : ℂ) • P) * G0 := by
    have : -((Gh - G0) * Δ * G0) - G0 * (Δ - (h : ℂ) • P) * G0 =
        -(Gh * Δ * G0) + (h : ℂ) • (G0 * P * G0) := by
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_smul, Matrix.smul_mul]
      abel
    rw [this, ← hres, smul_neg, sub_neg_eq_add]
  have e2' : ‖Gh - G0 - (h : ℂ) • -(G0 * P * G0)‖ ≤
      ‖Δ‖ ^ 2 * (‖Gh‖ * ‖G0‖ ^ 2) + ‖Δ - (h : ℂ) • P‖ * ‖G0‖ ^ 2 := by
    rw [e2eq]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_neg]
    have t0 := m3 (Gh - G0) Δ G0
    have t0' : ‖Gh - G0‖ * ‖Δ‖ * ‖G0‖ ≤ (‖Gh‖ * ‖Δ‖ * ‖G0‖) * ‖Δ‖ * ‖G0‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right e1' (norm_nonneg _)) (norm_nonneg _)
    have t2 := m3 G0 (Δ - (h : ℂ) • P) G0
    have e3 : (‖Gh‖ * ‖Δ‖ * ‖G0‖) * ‖Δ‖ * ‖G0‖ = ‖Δ‖ ^ 2 * (‖Gh‖ * ‖G0‖ ^ 2) := by ring
    have e4 : ‖G0‖ * ‖Δ - (h : ℂ) • P‖ * ‖G0‖ = ‖Δ - (h : ℂ) • P‖ * ‖G0‖ ^ 2 := by ring
    linarith
  have hτs : ∀ N : Matrix ι ι ℂ, τ ((h : ℂ) • N) = (h : ℂ) * τ N := fun N => by
    rw [Complex.coe_smul, map_smul, Complex.real_smul]
  have e3eq : τ Gh - τ G0 - (h : ℂ) * τ (-(G0 * P * G0)) =
      τ (Gh - G0 - (h : ℂ) • -(G0 * P * G0)) := by
    rw [map_sub, map_sub, hτs]
  have e3' : ‖τ Gh - τ G0 - (h : ℂ) * τ (-(G0 * P * G0))‖ ≤
      cτ * (‖Δ‖ ^ 2 * (‖Gh‖ * ‖G0‖ ^ 2) + ‖Δ - (h : ℂ) • P‖ * ‖G0‖ ^ 2) := by
    rw [e3eq]; exact (hτ _).trans (mul_le_mul_of_nonneg_left e2' hcτ)
  refine ⟨e1'.trans r1, e2'.trans r2, ?_, ?_⟩
  · refine e3'.trans ?_
    have := mul_le_mul_of_nonneg_left r2 hcτ
    calc _ ≤ cτ * ((h ^ 2 + ‖Δ - (h : ℂ) • P‖) * ((c₁ ^ 2 + 1) * (1 + ‖Gh‖ ^ 4 + ‖G0‖ ^ 4))) :=
          this
      _ = _ := by ring
  · set Gd := -(G0 * P * G0) with hGd
    have e4eq : τ Gh • Gh - τ G0 • G0 - (h : ℂ) • (τ Gd • G0 + τ G0 • Gd) =
        (τ Gh - τ G0 - (h : ℂ) * τ Gd) • Gh + τ G0 • (Gh - G0 - (h : ℂ) • Gd) +
          ((h : ℂ) * τ Gd) • (Gh - G0) := by module
    have hGdn : ‖Gd‖ ≤ ‖P‖ * ‖G0‖ ^ 2 := by
      rw [hGd, norm_neg]; exact (m3 _ _ _).trans (le_of_eq (by ring))
    have hτGd : ‖τ Gd‖ ≤ cτ * (‖P‖ * ‖G0‖ ^ 2) :=
      (hτ _).trans (mul_le_mul_of_nonneg_left hGdn hcτ)
    have hτG0 : ‖τ G0‖ ≤ cτ * ‖G0‖ := hτ _
    rw [e4eq]
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
    rw [norm_smul, norm_smul, norm_smul, norm_mul, hhc]
    have t1 := mul_le_mul_of_nonneg_right e3' (norm_nonneg Gh)
    have t2 := mul_le_mul hτG0 e2' (norm_nonneg _) (by positivity)
    have t3 : |h| * ‖τ Gd‖ * ‖Gh - G0‖ ≤ |h| * (cτ * (‖P‖ * ‖G0‖ ^ 2)) * (‖Gh‖ * ‖Δ‖ * ‖G0‖) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hτGd (abs_nonneg h)) e1' (norm_nonneg _)
        (by positivity)
    linarith

/-- `dcv_quad_alg` with remainders `A ρ`, `t² ≤ ρ`. -/
theorem tgt_quad_alg {M : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M] (t ρ : ℝ)
    (Ft F0 F1 F2 Mt M0 M' : M) (mt m0 m' : ℂ) {A1 A2 A3 A4 B1 B2 B3 : ℝ} (hB2 : 0 ≤ B2)
    (hA4 : 0 ≤ A4) (hρ : t ^ 2 ≤ ρ)
    (h1 : ‖Ft - F0 - (t : ℂ) • (F1 + F2)‖ ≤ A1 * ρ)
    (h2 : ‖mt - m0 - (t : ℂ) * m'‖ ≤ A2 * ρ) (h3 : ‖Mt‖ ≤ B1) (h4 : ‖m0‖ ≤ B2)
    (h5 : ‖Mt - M0 - (t : ℂ) • M'‖ ≤ A3 * ρ) (h6 : ‖m'‖ ≤ B3) (h7 : ‖Mt - M0‖ ≤ A4 * |t|) :
    ‖(Ft - mt • Mt) - (F0 - m0 • M0) - t • ((F1 - m' • M0) + (F2 - m0 • M'))‖ ≤
      (A1 + A2 * B1 + B2 * A3 + B3 * A4) * ρ := by
  rw [← Complex.coe_smul]
  have e : (Ft - mt • Mt) - (F0 - m0 • M0) - (t : ℂ) • ((F1 - m' • M0) + (F2 - m0 • M')) =
      (Ft - F0 - (t : ℂ) • (F1 + F2)) - ((mt - m0 - (t : ℂ) * m') • Mt +
        m0 • (Mt - M0 - (t : ℂ) • M') + ((t : ℂ) * m') • (Mt - M0)) := by module
  rw [e]
  have hA2 : 0 ≤ A2 * ρ := (norm_nonneg _).trans h2
  have hB3 : 0 ≤ B3 := (norm_nonneg _).trans h6
  refine (norm_sub_le _ _).trans ?_
  refine (add_le_add le_rfl ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl))).trans ?_
  rw [norm_smul, norm_smul, norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have t1 : ‖mt - m0 - (t : ℂ) * m'‖ * ‖Mt‖ ≤ A2 * ρ * B1 :=
    mul_le_mul h2 h3 (norm_nonneg _) hA2
  have t2 : ‖m0‖ * ‖Mt - M0 - (t : ℂ) • M'‖ ≤ B2 * (A3 * ρ) :=
    mul_le_mul h4 h5 (norm_nonneg _) hB2
  have t3 : |t| * ‖m'‖ * ‖Mt - M0‖ ≤ |t| * B3 * (A4 * |t|) :=
    mul_le_mul (mul_le_mul_of_nonneg_left h6 (abs_nonneg t)) h7 (norm_nonneg _)
      (mul_nonneg (abs_nonneg t) hB3)
  have s3 : |t| * B3 * (A4 * |t|) = B3 * A4 * t ^ 2 := by rw [← sq_abs t]; ring
  have s4 : B3 * A4 * t ^ 2 ≤ B3 * A4 * ρ := mul_le_mul_of_nonneg_left hρ (mul_nonneg hB3 hA4)
  nlinarith

/-- `‖Δ t‖ ≤ (‖P‖ + 1)|t|` and `‖Δ t - tP‖ = o(t)` near `0` for `HasDerivAt Δ P 0`, `Δ 0 = 0`. -/
theorem tgt_small_of_hasDerivAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {Δ : ℝ → F} {P : F} (hΔ : HasDerivAt Δ P 0) (hΔ0 : Δ 0 = 0) :
    (fun t : ℝ => ‖Δ t - (t : ℂ) • P‖) =o[𝓝 0] (fun t => t) ∧
      ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ t : ℝ, |t| ≤ δ₁ → ‖Δ t‖ ≤ (‖P‖ + 1) * |t| := by
  have hlo := hasDerivAt_iff_isLittleO_nhds_zero.mp hΔ
  have e : (fun t : ℝ => Δ (0 + t) - Δ 0 - t • P) = fun t : ℝ => Δ t - (t : ℂ) • P := by
    funext t; rw [zero_add, hΔ0, sub_zero, Complex.coe_smul]
  rw [e] at hlo
  have he := hlo.norm_left
  refine ⟨he, ?_⟩
  have h1 := he.def (zero_lt_one' ℝ)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp h1
  refine ⟨ε / 2, by positivity, fun t ht => ?_⟩
  have hd : dist t 0 < ε := by rw [Real.dist_eq, sub_zero]; linarith
  have h2 := hball hd
  rw [Real.norm_of_nonneg (norm_nonneg _), one_mul, Real.norm_eq_abs] at h2
  have h3 : ‖Δ t‖ ≤ ‖(t : ℂ) • P‖ + ‖Δ t - (t : ℂ) • P‖ := by
    have := norm_add_le ((t : ℂ) • P) (Δ t - (t : ℂ) • P)
    rwa [add_sub_cancel] at this
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs] at h3
  nlinarith [abs_nonneg t, norm_nonneg P]

set_option maxHeartbeats 400000 in
/-- **Derivative of the covariance along a curved family** (abstract form of Steps 1 and 3 of the
proof for `X(h) = X - hS + O(h²)`): for a family `G_h` with the resolvent identity
`G_h - G₀ = -G_h Δ(h) G₀` a.e., where the deterministic insertion `Δ` has `Δ(0) = 0` and
`Δ'(0) = P`, and `E‖G_h‖⁴ ≤ C₄` for `|h| ≤ δ`, the map `h ↦ Cov(τ(G_h), G_h)` is differentiable
at `0` with derivative `Cov(τ(𝒢̇), G₀) + Cov(τ(G₀), 𝒢̇)`, `𝒢̇ = -G₀ P G₀` (the same value as for
the linear family). -/
theorem tgt_hasDerivAt_cov_family {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (G : ℝ → Ω → Matrix ι ι ℂ) (Δ : ℝ → Matrix ι ι ℂ)
    (P : Matrix ι ι ℂ) (hΔ : HasDerivAt Δ P 0) (hΔ0 : Δ 0 = 0)
    (τ : Matrix ι ι ℂ →L[ℝ] ℂ) {cτ : ℝ} (hcτ : 0 ≤ cτ) (hτ : ∀ N, ‖τ N‖ ≤ cτ * ‖N‖)
    (hGm : ∀ h, Measurable (G h)) {δ : ℝ} (hδ : 0 < δ)
    (hres : ∀ h : ℝ, |h| ≤ δ → ∀ᵐ ω ∂μ, G h ω - G 0 ω = -(G h ω * Δ h * G 0 ω))
    {C4 : ℝ} (hmom : ∀ h : ℝ, |h| ≤ δ →
      Integrable (fun ω => ‖G h ω‖ ^ 4) μ ∧ ∫ ω, ‖G h ω‖ ^ 4 ∂μ ≤ C4) :
    HasDerivAt (fun h : ℝ => dcvCov μ (fun ω => τ (G h ω)) (G h))
      (dcvCov μ (fun ω => τ (-(G 0 ω * P * G 0 ω))) (G 0) +
        dcvCov μ (fun ω => τ (G 0 ω)) (fun ω => -(G 0 ω * P * G 0 ω))) 0 := by
  set p := ‖P‖ with hp
  have hp0 : 0 ≤ p := norm_nonneg _
  obtain ⟨he, δ₁, hδ₁, hsmall⟩ := tgt_small_of_hasDerivAt hΔ hΔ0
  set c₁ := p + 1 with hc₁
  have hc₁0 : 0 ≤ c₁ := by positivity
  set k2 := c₁ ^ 2 + 1 with hk2
  set k4 := 2 * c₁ ^ 2 + p * c₁ + 2 with hk4
  have hk20 : 0 ≤ k2 := by positivity
  have hk40 : 0 ≤ k4 := by positivity
  set Gd : Ω → Matrix ι ι ℂ := fun ω => -(G 0 ω * P * G 0 ω) with hGd
  have h0 : |(0 : ℝ)| ≤ δ := by simp [hδ.le]
  have hC4 : 0 ≤ C4 := (integral_nonneg fun ω => by positivity).trans (hmom 0 h0).2
  set Q : ℝ → Ω → ℝ := fun h ω => 1 + ‖G h ω‖ ^ 4 + ‖G 0 ω‖ ^ 4 with hQ
  set B := 1 + 2 * C4 with hB
  have hB0 : 0 ≤ B := by positivity
  have hQi : ∀ h, |h| ≤ δ → Integrable (Q h) μ := fun h hh =>
    ((integrable_const 1).add (hmom h hh).1).add (hmom 0 h0).1
  have hQB : ∀ h, |h| ≤ δ → ∫ ω, Q h ω ∂μ ≤ B := fun h hh => by
    simp only [hQ]
    have i1 : Integrable (fun ω => (1 : ℝ) + ‖G h ω‖ ^ 4) μ :=
      (integrable_const 1).add (hmom h hh).1
    rw [integral_add i1 (hmom 0 h0).1, integral_add (integrable_const 1) (hmom h hh).1,
      integral_const, probReal_univ, one_smul]
    linarith [(hmom h hh).2, (hmom 0 h0).2]
  have mono : ∀ h ω (i j : ℕ), i + j ≤ 4 → ‖G h ω‖ ^ i * ‖G 0 ω‖ ^ j ≤ Q h ω :=
    fun h ω i j hij => dcv_mono_le (norm_nonneg _) (norm_nonneg _) hij
  have hGQ : ∀ h ω, ‖G h ω‖ ≤ Q h ω := fun h ω => by simpa using mono h ω 1 0 (by norm_num)
  have hGG : ∀ h ω, ‖G h ω‖ * ‖G h ω‖ ≤ Q h ω := fun h ω => by
    simpa [sq] using mono h ω 2 0 (by norm_num)
  have hG02 : ∀ ω, ‖G 0 ω‖ ^ 2 ≤ Q 0 ω := fun ω => by simpa using mono 0 ω 0 2 (by norm_num)
  have hG03 : ∀ ω, ‖G 0 ω‖ ^ 3 ≤ Q 0 ω := fun ω => by simpa using mono 0 ω 0 3 (by norm_num)
  have m3 : ∀ A B C : Matrix ι ι ℂ, ‖A * B * C‖ ≤ ‖A‖ * ‖B‖ * ‖C‖ := fun A B C =>
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
  have hGdn : ∀ ω, ‖Gd ω‖ ≤ p * ‖G 0 ω‖ ^ 2 := fun ω => by
    simp only [hGd, norm_neg]; exact (m3 _ _ _).trans (le_of_eq (by ring))
  -- measurability
  have hτc : Continuous τ := τ.continuous
  have mG : ∀ h, AEStronglyMeasurable (G h) μ := fun h => (hGm h).aestronglyMeasurable
  have mg : ∀ h, AEStronglyMeasurable (fun ω => τ (G h ω)) μ := fun h =>
    (hτc.measurable.comp (hGm h)).aestronglyMeasurable
  have hGdm : Measurable Gd :=
    (((continuous_id.mul continuous_const).mul continuous_id).neg.measurable).comp (hGm 0)
  have mGd : AEStronglyMeasurable Gd μ := hGdm.aestronglyMeasurable
  have mgd : AEStronglyMeasurable (fun ω => τ (Gd ω)) μ :=
    (hτc.measurable.comp hGdm).aestronglyMeasurable
  -- integrability
  have iG : ∀ h, |h| ≤ δ → Integrable (G h) μ := fun h hh =>
    Integrable.mono' (hQi h hh) (mG h) (ae_of_all _ fun ω => hGQ h ω)
  have ig : ∀ h, |h| ≤ δ → Integrable (fun ω => τ (G h ω)) μ := fun h hh =>
    Integrable.mono' ((hQi h hh).const_mul cτ) (mg h) (ae_of_all _ fun ω =>
      (hτ _).trans (mul_le_mul_of_nonneg_left (hGQ h ω) hcτ))
  have igG : ∀ h, |h| ≤ δ → Integrable (fun ω => τ (G h ω) • G h ω) μ := fun h hh =>
    Integrable.mono' ((hQi h hh).const_mul cτ) ((mg h).smul (mG h)) (ae_of_all _ fun ω => by
      rw [norm_smul]
      calc ‖τ (G h ω)‖ * ‖G h ω‖ ≤ (cτ * ‖G h ω‖) * ‖G h ω‖ :=
            mul_le_mul_of_nonneg_right (hτ _) (norm_nonneg _)
        _ = cτ * (‖G h ω‖ * ‖G h ω‖) := by ring
        _ ≤ cτ * Q h ω := mul_le_mul_of_nonneg_left (hGG h ω) hcτ)
  have iGd : Integrable Gd μ :=
    Integrable.mono' ((hQi 0 h0).const_mul p) mGd (ae_of_all _ fun ω =>
      (hGdn ω).trans (mul_le_mul_of_nonneg_left (hG02 ω) hp0))
  have igd : Integrable (fun ω => τ (Gd ω)) μ :=
    Integrable.mono' ((hQi 0 h0).const_mul (cτ * p)) mgd (ae_of_all _ fun ω =>
      (hτ _).trans (by
        calc cτ * ‖Gd ω‖ ≤ cτ * (p * ‖G 0 ω‖ ^ 2) := mul_le_mul_of_nonneg_left (hGdn ω) hcτ
          _ ≤ cτ * (p * Q 0 ω) := by gcongr; exact hG02 ω
          _ = cτ * p * Q 0 ω := by ring))
  have igdG : Integrable (fun ω => τ (Gd ω) • G 0 ω) μ :=
    Integrable.mono' ((hQi 0 h0).const_mul (cτ * p)) (mgd.smul (mG 0)) (ae_of_all _ fun ω => by
      rw [norm_smul]
      calc ‖τ (Gd ω)‖ * ‖G 0 ω‖ ≤ (cτ * (p * ‖G 0 ω‖ ^ 2)) * ‖G 0 ω‖ :=
            mul_le_mul_of_nonneg_right ((hτ _).trans (mul_le_mul_of_nonneg_left (hGdn ω) hcτ))
              (norm_nonneg _)
        _ = cτ * p * ‖G 0 ω‖ ^ 3 := by ring
        _ ≤ cτ * p * Q 0 ω := mul_le_mul_of_nonneg_left (hG03 ω) (by positivity))
  have igGd : Integrable (fun ω => τ (G 0 ω) • Gd ω) μ :=
    Integrable.mono' ((hQi 0 h0).const_mul (cτ * p)) ((mg 0).smul mGd) (ae_of_all _ fun ω => by
      rw [norm_smul]
      calc ‖τ (G 0 ω)‖ * ‖Gd ω‖ ≤ (cτ * ‖G 0 ω‖) * (p * ‖G 0 ω‖ ^ 2) :=
            mul_le_mul (hτ _) (hGdn ω) (norm_nonneg _) (by positivity)
        _ = cτ * p * ‖G 0 ω‖ ^ 3 := by ring
        _ ≤ cτ * p * Q 0 ω := mul_le_mul_of_nonneg_left (hG03 ω) (by positivity))
  -- the Bochner form
  set φ : ℝ → Matrix ι ι ℂ := fun h =>
    (∫ ω, τ (G h ω) • G h ω ∂μ) - (∫ ω, τ (G h ω) ∂μ) • ∫ ω, G h ω ∂μ with hφ
  have hcov : ∀ h, |h| ≤ δ → dcvCov μ (fun ω => τ (G h ω)) (G h) = φ h := fun h hh => by
    simp only [dcvCov, hφ]
    rw [dcv_matrixExpect_eq_integral (igG h hh), dcv_matrixExpect_eq_integral (iG h hh)]
  have hder : dcvCov μ (fun ω => τ (Gd ω)) (G 0) + dcvCov μ (fun ω => τ (G 0 ω)) Gd =
      ((∫ ω, τ (Gd ω) • G 0 ω ∂μ) - (∫ ω, τ (Gd ω) ∂μ) • ∫ ω, G 0 ω ∂μ) +
        ((∫ ω, τ (G 0 ω) • Gd ω ∂μ) - (∫ ω, τ (G 0 ω) ∂μ) • ∫ ω, Gd ω ∂μ) := by
    simp only [dcvCov]
    rw [dcv_matrixExpect_eq_integral igdG, dcv_matrixExpect_eq_integral (iG 0 h0),
      dcv_matrixExpect_eq_integral igGd, dcv_matrixExpect_eq_integral iGd]
  rw [hder]
  have hev : (fun h : ℝ => dcvCov μ (fun ω => τ (G h ω)) (G h)) =ᶠ[𝓝 0] φ := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with t ht
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
    exact hcov t ht.le
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  set e : ℝ → ℝ := fun t => ‖Δ t - (t : ℂ) • P‖ with he_def
  have hδ₂ : 0 < min δ δ₁ := lt_min hδ hδ₁
  refine tgt_hasDerivAt_of_rem (r := e) (K := cτ * k4 * B + cτ * k2 * B * B + cτ * B * (k2 * B) +
    cτ * p * B * (c₁ * B)) hδ₂ (fun t => norm_nonneg _) he fun t ht => ?_
  have htδ : |t| ≤ δ := ht.trans (min_le_left _ _)
  have htδ₁ : |t| ≤ δ₁ := ht.trans (min_le_right _ _)
  set ρ := t ^ 2 + e t with hρ
  have hρ0 : t ^ 2 ≤ ρ := by rw [hρ]; linarith [norm_nonneg (Δ t - (t : ℂ) • P)]
  -- pointwise expansions
  have hexp : ∀ᵐ ω ∂μ, _ := (hres t htδ).mono fun ω hω =>
    tgt_expand_le τ hcτ hτ (Gh := G t ω) (G0 := G 0 ω) (P := P) (Δ := Δ t) hc₁0 hω (hsmall t htδ₁)
  have b1 : ‖(∫ ω, τ (G t ω) • G t ω ∂μ) - (∫ ω, τ (G 0 ω) • G 0 ω ∂μ) -
      (t : ℂ) • ((∫ ω, τ (Gd ω) • G 0 ω ∂μ) + ∫ ω, τ (G 0 ω) • Gd ω ∂μ)‖ ≤
      cτ * k4 * B * ρ := by
    have j1 : Integrable (fun ω => τ (G t ω) • G t ω - τ (G 0 ω) • G 0 ω) μ :=
      (igG t htδ).sub (igG 0 h0)
    have j2 : Integrable (fun ω => (t : ℂ) • (τ (Gd ω) • G 0 ω + τ (G 0 ω) • Gd ω)) μ :=
      (igdG.add igGd).smul (t : ℂ)
    rw [← integral_add igdG igGd, ← integral_smul, ← integral_sub (igG t htδ) (igG 0 h0),
      ← integral_sub j1 j2]
    refine (dcv_norm_integral_le (hQi t htδ) (k := ρ * (cτ * k4)) ?_).trans ?_
    · filter_upwards [hexp] with ω hω
      have := hω.2.2.2
      simp only [hGd] at this ⊢
      refine this.trans (le_of_eq ?_)
      simp only [hQ, hρ, he_def, hk4]; ring
    · have := mul_le_mul_of_nonneg_left (hQB t htδ)
        (by positivity : 0 ≤ ρ * (cτ * k4))
      linarith
  have b2 : ‖(∫ ω, τ (G t ω) ∂μ) - (∫ ω, τ (G 0 ω) ∂μ) - (t : ℂ) * ∫ ω, τ (Gd ω) ∂μ‖ ≤
      cτ * k2 * B * ρ := by
    have j1 : Integrable (fun ω => τ (G t ω) - τ (G 0 ω)) μ := (ig t htδ).sub (ig 0 h0)
    have j2 : Integrable (fun ω => (t : ℂ) * τ (Gd ω)) μ := igd.const_mul _
    rw [← integral_const_mul, ← integral_sub (ig t htδ) (ig 0 h0), ← integral_sub j1 j2]
    refine (dcv_norm_integral_le (hQi t htδ) (k := ρ * (cτ * k2)) ?_).trans ?_
    · filter_upwards [hexp] with ω hω
      have := hω.2.2.1
      simp only [hGd] at this ⊢
      refine this.trans (le_of_eq ?_)
      simp only [hQ, hρ, he_def, hk2]; ring
    · have := mul_le_mul_of_nonneg_left (hQB t htδ) (by positivity : 0 ≤ ρ * (cτ * k2))
      linarith
  have b3 : ‖∫ ω, G t ω ∂μ‖ ≤ B := by
    refine (dcv_norm_integral_le (hQi t htδ) (k := 1) (ae_of_all _ fun ω => ?_)).trans ?_
    · rw [one_mul]; exact hGQ t ω
    · rw [one_mul]; exact hQB t htδ
  have b4 : ‖∫ ω, τ (G 0 ω) ∂μ‖ ≤ cτ * B := by
    refine (dcv_norm_integral_le (hQi 0 h0) (k := cτ) (ae_of_all _ fun ω => ?_)).trans ?_
    · exact (hτ _).trans (mul_le_mul_of_nonneg_left (hGQ 0 ω) hcτ)
    · exact mul_le_mul_of_nonneg_left (hQB 0 h0) hcτ
  have b5 : ‖(∫ ω, G t ω ∂μ) - (∫ ω, G 0 ω ∂μ) - (t : ℂ) • ∫ ω, Gd ω ∂μ‖ ≤ k2 * B * ρ := by
    have j1 : Integrable (fun ω => G t ω - G 0 ω) μ := (iG t htδ).sub (iG 0 h0)
    have j2 : Integrable (fun ω => (t : ℂ) • Gd ω) μ := iGd.smul (t : ℂ)
    rw [← integral_smul, ← integral_sub (iG t htδ) (iG 0 h0), ← integral_sub j1 j2]
    refine (dcv_norm_integral_le (hQi t htδ) (k := ρ * k2) ?_).trans ?_
    · filter_upwards [hexp] with ω hω
      have := hω.2.1
      simp only [hGd] at this ⊢
      refine this.trans (le_of_eq ?_)
      simp only [hQ, hρ, he_def, hk2]; ring
    · have := mul_le_mul_of_nonneg_left (hQB t htδ) (by positivity : 0 ≤ ρ * k2)
      linarith
  have b6 : ‖∫ ω, τ (Gd ω) ∂μ‖ ≤ cτ * p * B := by
    refine (dcv_norm_integral_le (hQi 0 h0) (k := cτ * p) (ae_of_all _ fun ω => ?_)).trans ?_
    · calc ‖τ (Gd ω)‖ ≤ cτ * (p * ‖G 0 ω‖ ^ 2) :=
            (hτ _).trans (mul_le_mul_of_nonneg_left (hGdn ω) hcτ)
        _ ≤ cτ * (p * Q 0 ω) := by gcongr; exact hG02 ω
        _ = cτ * p * Q 0 ω := by ring
    · exact mul_le_mul_of_nonneg_left (hQB 0 h0) (by positivity)
  have b7 : ‖(∫ ω, G t ω ∂μ) - ∫ ω, G 0 ω ∂μ‖ ≤ c₁ * B * |t| := by
    rw [← integral_sub (iG t htδ) (iG 0 h0)]
    refine (dcv_norm_integral_le (hQi t htδ) (k := |t| * c₁) ?_).trans ?_
    · filter_upwards [hexp] with ω hω
      refine hω.1.trans (le_of_eq ?_)
      simp only [hQ]; ring
    · have := mul_le_mul_of_nonneg_left (hQB t htδ) (by positivity : 0 ≤ |t| * c₁)
      linarith
  have hfin := tgt_quad_alg t ρ _ _ _ _ _ _ _ _ _ _ (by positivity : (0 : ℝ) ≤ cτ * B)
    (by positivity : (0 : ℝ) ≤ c₁ * B) hρ0 b1 b2 b3 b4 b5 b6 b7
  refine hfin.trans (le_of_eq ?_)
  ring

end Abs

section Blocks

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The block-diagonal embedding `(A, B) ↦ diag(A, B)` as a real continuous linear map. -/
def tgtBlk : (Matrix n n ℂ × Matrix m m ℂ) →L[ℝ] Matrix (n ⊕ m) (n ⊕ m) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => fromBlocks x.1 0 0 x.2
      map_add' := fun x y => by simp [fromBlocks_add]
      map_smul' := fun r x => by simp [fromBlocks_smul] }

theorem tgtBlk_apply (A : Matrix n n ℂ) (B : Matrix m m ℂ) :
    tgtBlk (A, B) = fromBlocks A 0 0 B := rfl

/-- The energy insertion `D₀ = diag(-I, z₁ I)` (`∂_E 𝒢⁻¹ = -Ŝ + D₀`). -/
def tgtD0 (z₁ : ℂ) : Matrix (n ⊕ m) (n ⊕ m) ℂ := fromBlocks (-1) 0 0 (z₁ • 1)

theorem tgt_fromBlocks22_eq (B : Matrix m m ℂ) :
    (fromBlocks 0 0 0 B : Matrix (n ⊕ m) (n ⊕ m) ℂ) =
      (dcvIncl (Sum.inr : m → n ⊕ m))ᴴ * B * dcvIncl (Sum.inr : m → n ⊕ m) := by
  ext (x | x) (y | y) <;>
    simp [fromBlocks, dcvIncl, Matrix.mul_apply, conjTranspose_apply]

/-- `‖diag(-I, z₁ I)‖ ≤ 1 + |z₁|`. -/
theorem tgt_norm_tgtD0_le (z₁ : ℂ) : ‖(tgtD0 z₁ : Matrix (n ⊕ m) (n ⊕ m) ℂ)‖ ≤ 1 + ‖z₁‖ := by
  have e : (tgtD0 z₁ : Matrix (n ⊕ m) (n ⊕ m) ℂ) = dcvHat (-1) + fromBlocks 0 0 0 (z₁ • 1) := by
    rw [tgtD0, dcvHat, fromBlocks_add]; simp
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (dcv_norm_hat_le _).trans ?_
    rw [norm_neg]; exact dcv_norm_one_le
  · rw [tgt_fromBlocks22_eq]
    refine (dcv_norm_sandwich_le _ Sum.inr_injective Sum.inr_injective).trans ?_
    refine (norm_smul_le _ _).trans ?_
    have := dcv_norm_one_le (n := m)
    nlinarith [norm_nonneg z₁]

/-- `N⁻¹ - N₀⁻¹ = -N⁻¹ Δ N₀⁻¹` for `N = N₀ + Δ`, both invertible. -/
theorem tgt_inv_sub_of_add {ι : Type*} [Fintype ι] [DecidableEq ι] {N N0 Δ : Matrix ι ι ℂ}
    (hN : N = N0 + Δ) (h1 : IsUnit N.det) (h0 : IsUnit N0.det) :
    N⁻¹ - N0⁻¹ = -(N⁻¹ * Δ * N0⁻¹) := by
  have k1 : N⁻¹ * N = 1 := nonsing_inv_mul _ h1
  have k0 : N0 * N0⁻¹ = 1 := mul_nonsing_inv _ h0
  have hdiff : N0 - N = -Δ := by rw [hN]; abel
  calc N⁻¹ - N0⁻¹ = N⁻¹ * (N0 * N0⁻¹) - (N⁻¹ * N) * N0⁻¹ := by
        rw [k0, k1, Matrix.mul_one, Matrix.one_mul]
    _ = N⁻¹ * (N0 - N) * N0⁻¹ := by
        rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc]
    _ = -(N⁻¹ * Δ * N0⁻¹) := by rw [hdiff, Matrix.mul_neg, Matrix.neg_mul]

/-- `h ↦ (N₀ + Δ(h))⁻¹` has derivative `-N₀⁻¹ P N₀⁻¹` at `0` (`Δ(0) = 0`, `Δ'(0) = P`). -/
theorem tgt_hasDerivAt_inv_family {ι : Type*} [Fintype ι] [DecidableEq ι] {N0 P : Matrix ι ι ℂ}
    {Δ : ℝ → Matrix ι ι ℂ} (hN : IsUnit N0.det) (hΔ : HasDerivAt Δ P 0) (hΔ0 : Δ 0 = 0) :
    HasDerivAt (fun h : ℝ => (N0 + Δ h)⁻¹) (-(N0⁻¹ * P * N0⁻¹)) 0 := by
  have e : (fun h : ℝ => (N0 + Δ h)⁻¹) = fun h : ℝ => Ring.inverse (N0 + Δ h) := by
    funext h; rw [Matrix.nonsing_inv_eq_ringInverse]
  rw [e]
  have hU : IsUnit N0 := (Matrix.isUnit_iff_isUnit_det N0).mpr hN
  have hinv := hasFDerivAt_ringInverse (𝕜 := ℝ) hU.unit
  rw [IsUnit.unit_spec] at hinv
  have haff : HasDerivAt (fun h : ℝ => N0 + Δ h) P 0 := hΔ.const_add N0
  have hinv' : HasFDerivAt Ring.inverse
      (-(ContinuousLinearMap.mulLeftRight ℝ (Matrix ι ι ℂ) ↑hU.unit⁻¹ ↑hU.unit⁻¹))
      ((fun h : ℝ => N0 + Δ h) 0) := by
    simp only [hΔ0, add_zero]; exact hinv
  have h3 := hinv'.comp_hasDerivAt (0 : ℝ) haff
  have hinvN : (↑hU.unit⁻¹ : Matrix ι ι ℂ) = N0⁻¹ := by
    rw [← Ring.inverse_unit, IsUnit.unit_spec, Matrix.nonsing_inv_eq_ringInverse]
  convert h3 using 1
  · rfl
  rw [_root_.neg_apply, ContinuousLinearMap.mulLeftRight_apply, hinvN]

end Blocks

/-- **The layer family** (Steps 1, 3 and 6 for a general parameter family): if the layer
matrices of the family `h ↦ (E(h), z(h), X(h))` are `𝒢(0)⁻¹ + Δ(h)` with a deterministic
`Δ`, `Δ(0) = 0`, `Δ'(0) = P`, are a.s. invertible and have `E‖𝒢(h)‖⁴ ≤ C₄` for `|h| ≤ δ`, then
`h ↦ Cov(W⁻¹ Tr(D𝒢(h)), 𝒢(h))` has derivative `dcvCovDir μ D 𝒢(0) P` at `0`, and a.s.
`h ↦ W⁻¹ Tr(D𝒢(h))` has derivative `-W⁻¹ Tr(D 𝒢(0) P 𝒢(0))`. -/
theorem tgt_layer_family {W : ℕ} (hW : 0 < W) {b : ℝ} (σ : LayerShape) (Ef : ℝ → ℝ)
    (zf : ℝ → ℂ) (Xf : ℝ → Matrix (PhysSite W σ) (PhysSite W σ) ℂ)
    (D : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    (Δ : ℝ → Matrix (LayerSite W σ) (LayerSite W σ) ℂ) (P : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    (hΔ : HasDerivAt Δ P 0) (hΔ0 : Δ 0 = 0)
    (hshift : ∀ (h : ℝ) ω, layerMatrix σ (Ef h) (zf h) (Xf h) ω =
      layerMatrix σ (Ef 0) (zf 0) (Xf 0) ω + Δ h)
    {δ : ℝ} (hδ : 0 < δ)
    (hinv : ∀ h : ℝ, |h| ≤ δ → ∀ᵐ ω ∂layerLaw W b σ,
      IsUnit (layerMatrix σ (Ef h) (zf h) (Xf h) ω).det)
    {C4 : ℝ} (hmom : ∀ h : ℝ, |h| ≤ δ →
      Integrable (fun ω => ‖layerResolvent σ (Ef h) (zf h) (Xf h) ω‖ ^ 4) (layerLaw W b σ) ∧
        ∫ ω, ‖layerResolvent σ (Ef h) (zf h) (Xf h) ω‖ ^ 4 ∂layerLaw W b σ ≤ C4) :
    HasDerivAt (fun h : ℝ => dcvCov (layerLaw W b σ)
        (fun ω => (W : ℂ)⁻¹ * (D * layerResolvent σ (Ef h) (zf h) (Xf h) ω).trace)
        (fun ω => layerResolvent σ (Ef h) (zf h) (Xf h) ω))
      (dcvCovDir (layerLaw W b σ) D (fun ω => layerResolvent σ (Ef 0) (zf 0) (Xf 0) ω) P) 0 ∧
    ∀ᵐ ω ∂layerLaw W b σ, HasDerivAt
      (fun h : ℝ => (W : ℂ)⁻¹ * (D * layerResolvent σ (Ef h) (zf h) (Xf h) ω).trace)
      (-((W : ℂ)⁻¹ * (D * (layerResolvent σ (Ef 0) (zf 0) (Xf 0) ω * P *
        layerResolvent σ (Ef 0) (zf 0) (Xf 0) ω)).trace)) 0 := by
  have := bond_isProbabilityMeasure_layerLaw W b σ
  have h0 : |(0 : ℝ)| ≤ δ := by simp [hδ.le]
  constructor
  · have hres : ∀ h : ℝ, |h| ≤ δ → ∀ᵐ ω ∂layerLaw W b σ,
        layerResolvent σ (Ef h) (zf h) (Xf h) ω - layerResolvent σ (Ef 0) (zf 0) (Xf 0) ω =
          -(layerResolvent σ (Ef h) (zf h) (Xf h) ω * Δ h *
            layerResolvent σ (Ef 0) (zf 0) (Xf 0) ω) := fun h hh => by
      filter_upwards [hinv h hh, hinv 0 h0] with ω h1 h2
      exact tgt_inv_sub_of_add (hshift h ω) h1 h2
    have hd := tgt_hasDerivAt_cov_family (μ := layerLaw W b σ)
      (fun (h : ℝ) ω => layerResolvent σ (Ef h) (zf h) (Xf h) ω) Δ P hΔ hΔ0 (tflTraceCLM W σ D)
      (by positivity : (0 : ℝ) ≤ 4 * ‖D‖) (fun N => dcv_traceCLM_le σ hW D N)
      (fun h => measurable_layerResolvent σ _ _ _) hδ hres hmom
    convert hd using 1
    · rfl
    unfold dcvCovDir
    simp only [map_neg, tflTraceCLM_apply]
  · filter_upwards [hinv 0 h0] with ω hω
    have e : (fun h : ℝ => layerResolvent σ (Ef h) (zf h) (Xf h) ω) =
        fun h : ℝ => (layerMatrix σ (Ef 0) (zf 0) (Xf 0) ω + Δ h)⁻¹ := by
      funext h; rw [layerResolvent, hshift]
    have h1 := tgt_hasDerivAt_inv_family hω hΔ hΔ0
    rw [← e] at h1
    have h2 := (tflTraceCLM W σ D).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
    convert h2 using 1
    · rfl
    rw [tflTraceCLM_apply, layerResolvent, Matrix.mul_neg, trace_neg, mul_neg]

/-!
## 3. Linearity in the direction and the two families
-/

section Families

variable {W : ℕ} {σ : LayerShape}

/-- `Cov(-g, U) = -Cov(g, U)` (no integrability needed). -/
theorem tgt_dcvCov_neg_left {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (g : Ω → ℂ)
    (U : Ω → Matrix ι ι ℂ) : dcvCov μ (fun ω => -g ω) U = -dcvCov μ g U := by
  ext x y
  simp [dcvCov, matrixExpect, integral_neg]
  ring

/-- `Cov(g, -U) = -Cov(g, U)` (no integrability needed). -/
theorem tgt_dcvCov_neg_right {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (g : Ω → ℂ)
    (U : Ω → Matrix ι ι ℂ) : dcvCov μ g (fun ω => -U ω) = -dcvCov μ g U := by
  ext x y
  simp [dcvCov, matrixExpect, integral_neg]
  ring

/-- **Linearity**: `dcvCovDir μ D G (-P) = -dcvCovDir μ D G P`. -/
theorem tgt_dcvCovDir_neg (μ : Measure (LayerSample W σ))
    (D : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    (G : LayerSample W σ → Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    (P : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    dcvCovDir μ D G (-P) = -dcvCovDir μ D G P := by
  unfold dcvCovDir
  have e1 : (fun ω => -((W : ℂ)⁻¹ * (D * (G ω * -P * G ω)).trace)) =
      fun ω => -(-((W : ℂ)⁻¹ * (D * (G ω * P * G ω)).trace)) := by
    funext ω; rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_neg, trace_neg, mul_neg]
  have e2 : (fun ω => -(G ω * -P * G ω)) = fun ω => -(-(G ω * P * G ω)) := by
    funext ω; rw [Matrix.mul_neg, Matrix.neg_mul]
  rw [e1, e2, tgt_dcvCov_neg_left, tgt_dcvCov_neg_right, neg_add]

/-- The centered trace derivative changes sign with the direction:
`ġ_{-P} - E ġ_{-P} = -(ġ_P - E ġ_P)`. -/
theorem tgt_gdot_neg (μ : Measure (LayerSample W σ))
    (D : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    (G : LayerSample W σ → Matrix (LayerSite W σ) (LayerSite W σ) ℂ)
    (P : Matrix (LayerSite W σ) (LayerSite W σ) ℂ) :
    (fun ω => -((W : ℂ)⁻¹ * (D * (G ω * -P * G ω)).trace) -
        ∫ ω', -((W : ℂ)⁻¹ * (D * (G ω' * -P * G ω')).trace) ∂μ) =
      -(fun ω => -((W : ℂ)⁻¹ * (D * (G ω * P * G ω)).trace) -
        ∫ ω', -((W : ℂ)⁻¹ * (D * (G ω' * P * G ω')).trace) ∂μ) := by
  have e : ∀ ω, -((W : ℂ)⁻¹ * (D * (G ω * -P * G ω)).trace) =
      -(-((W : ℂ)⁻¹ * (D * (G ω * P * G ω)).trace)) := fun ω => by
    rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_neg, trace_neg, mul_neg]
  simp only [e, integral_neg]
  funext ω
  simp only [Pi.neg_apply]
  ring

/-- The curved layer matrix: `𝒢(X')⁻¹ = 𝒢(X)⁻¹ + diag(X - X', 0)`. -/
theorem tgt_layerMatrix_curved (E : ℝ) (z : ℂ) (X X' : Matrix (PhysSite W σ) (PhysSite W σ) ℂ)
    (ω : LayerSample W σ) :
    layerMatrix σ E z X' ω = layerMatrix σ E z X ω + tgtBlk (X - X', 0) := by
  rw [layerMatrix, layerMatrix, tgtBlk_apply, fromBlocks_add]
  congr 1 <;> abel

/-- The energy layer matrix: `𝒢(E₀ + t, z', X')⁻¹ = 𝒢(E₀, z, X)⁻¹ + diag(-t + X - X', z' - z)`. -/
theorem tgt_layerMatrix_energy (E₀ t : ℝ) (z z' : ℂ)
    (X X' : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) (ω : LayerSample W σ) :
    layerMatrix σ (E₀ + t) z' X' ω =
      layerMatrix σ E₀ z X ω + tgtBlk ((-t) • (1 : Matrix (PhysSite W σ) (PhysSite W σ) ℂ) +
        (X - X'), (z' - z) • (1 : Matrix (PortSite W σ) (PortSite W σ) ℂ)) := by
  rw [layerMatrix, layerMatrix, tgtBlk_apply, fromBlocks_add]
  congr 1
  · ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [Complex.ofReal_add, Complex.real_smul]
    push_cast; ring
  · simp
  · simp
  · ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring

end Families

/-- Shift of the base point: `HasDerivAt (t ↦ f(E₀ + t)) v 0 → HasDerivAt f v E₀`. -/
theorem tgt_hasDerivAt_shift {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ → F}
    {v : F} {E₀ : ℝ} (h : HasDerivAt (fun t => f (E₀ + t)) v 0) : HasDerivAt f v E₀ := by
  have h' : HasDerivAt (fun t => f (E₀ + t)) v (E₀ - E₀) := by rwa [sub_self]
  have := HasDerivAt.comp_sub_const E₀ E₀ h'
  simpa using this

/-!
## 4. The statement
-/

/-- **Curved source family** (clause 1 of `DiffCovarianceFamilyStatement`). After `b` and `κ`:
there are `C, W₀` such that for `W ≥ W₀`, Hermitian `X`, `S ⪰ 0`, `E ∈ bulkInterval κ`, `‖D‖ ≤ 1`
and **every** deterministic family `X(h)` with `X(0) = X`, `X'(0) = -S` (i.e.
`X(h) = X - hS + o(h)`, which contains `X - hS + O(h²)`) and `X(h)` Hermitian for `|h| ≤ δ`
(some `δ > 0`): `h ↦ Cov(g(h), 𝒢(h))` has derivative `dcvCovDir μ D 𝒢 Ŝ` at `0`, a.s.
`h ↦ g(h) = W⁻¹ Tr(D𝒢(h))` has derivative `ġ = -W⁻¹ Tr(D𝒢Ŝ𝒢)` at `0`, and
`‖dcvCovDir μ D 𝒢 Ŝ‖ ≤ C W⁻²‖Y‖ ≤ Cu/W` (the covariance derivative formula). The fresh
coordinates, `E` and `z = z_∂(E)` are fixed. -/
def tgtCurvedClause (b κ : ℝ) : Prop :=
  ∃ (C : ℝ) (W₀ : ℕ), ∀ (W : ℕ), 0 < W → W₀ ≤ W →
    ∀ X S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian → S.PosSemidef →
    ∀ E ∈ bulkInterval κ,
    ∀ D : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ, ‖D‖ ≤ 1 →
    ∀ (Xf : ℝ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (δ : ℝ), 0 < δ → Xf 0 = X →
      HasDerivAt Xf (-S) 0 → (∀ h : ℝ, |h| ≤ δ → (Xf h).IsHermitian) →
      let μ := layerLaw W b .separate
      let z := boundaryZ b E
      let K := z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X
      let Y := (K⁻¹)ᴴ * S * K⁻¹
      let u := (W : ℝ)⁻¹ * Y.trace.re
      let G := fun ω => layerResolvent .separate E z X ω
      let Gf := fun (h : ℝ) ω => layerResolvent .separate E z (Xf h) ω
      HasDerivAt (fun h : ℝ => dcvCov μ (fun ω => (W : ℂ)⁻¹ * (D * Gf h ω).trace) (Gf h))
        (dcvCovDir μ D G (dcvHat S)) 0 ∧
      (∀ᵐ ω ∂μ, HasDerivAt (fun h : ℝ => (W : ℂ)⁻¹ * (D * Gf h ω).trace)
        (-((W : ℂ)⁻¹ * (D * (G ω * dcvHat S * G ω)).trace)) 0) ∧
      ‖dcvCovDir μ D G (dcvHat S)‖ ≤ C / (W : ℝ) ^ 2 * ‖Y‖ ∧
      C / (W : ℝ) ^ 2 * ‖Y‖ ≤ C * u / W

/-- **Energy family** (clause 2 of `DiffCovarianceFamilyStatement`). After `b` and `κ`: there are
`C, W₀` such that for `W ≥ W₀`, every deterministic family `E ↦ X(E)` that is Hermitian for
`|E - E₀| ≤ δ` (some `δ > 0`) and differentiable at `E₀ ∈ bulkInterval κ` with `S = X'(E₀) ⪰ 0`
(in the application `X_r' = B*(H - E)⁻²B ⪰ 0`), and `‖D‖ ≤ 1`: the family
`E ↦ 𝒢(E) = layerResolvent .separate E (z_∂(E)) (X(E))` (energy, port parameter and old input
moving together) has `∂_E Cov(g(E), 𝒢(E)) = dcvCovDir μ D 𝒢(E₀) (-Ŝ + D₀)` at `E₀`, with
`-Ŝ + D₀ = ∂_E 𝒢⁻¹ = diag(-(I + X'), z_∂' I)` and `D₀ = tgtD0 (z_∂'(E₀)) = diag(-I, z_∂' I)`.
A.s. `E ↦ g(E)` has derivative `-W⁻¹ Tr(D𝒢(-Ŝ + D₀)𝒢)`, and
`‖dcvCovDir μ D 𝒢 (-Ŝ + D₀)‖ ≤ C(1+u)/W` with `u = W⁻¹ Re Tr K⁻*X'K⁻¹`, which is the clock `s_r`
of the tagged-trace lemma ("`1 + u` in place of `u`"). -/
def tgtEnergyClause (b κ : ℝ) : Prop :=
  ∃ (C : ℝ) (W₀ : ℕ), ∀ (W : ℕ), 0 < W → W₀ ≤ W →
    ∀ (Xf : ℝ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
      (S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (E₀ δ : ℝ),
      E₀ ∈ bulkInterval κ → 0 < δ → S.PosSemidef → HasDerivAt Xf S E₀ →
      (∀ E : ℝ, |E - E₀| ≤ δ → (Xf E).IsHermitian) →
    ∀ D : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ, ‖D‖ ≤ 1 →
      let μ := layerLaw W b .separate
      let X := Xf E₀
      let z := boundaryZ b E₀
      let K := z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X
      let Y := (K⁻¹)ᴴ * S * K⁻¹
      let u := (W : ℝ)⁻¹ * Y.trace.re
      let G := fun ω => layerResolvent .separate E₀ z X ω
      let P : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ :=
        -dcvHat S + tgtD0 (tgtZd b E₀)
      let Gf := fun (E : ℝ) ω => layerResolvent .separate E (boundaryZ b E) (Xf E) ω
      HasDerivAt (fun E : ℝ => dcvCov μ (fun ω => (W : ℂ)⁻¹ * (D * Gf E ω).trace) (Gf E))
        (dcvCovDir μ D G P) E₀ ∧
      (∀ᵐ ω ∂μ, HasDerivAt (fun E : ℝ => (W : ℂ)⁻¹ * (D * Gf E ω).trace)
        (-((W : ℂ)⁻¹ * (D * (G ω * P * G ω)).trace)) E₀) ∧
      ‖dcvCovDir μ D G P‖ ≤ C * (1 + u) / W

/-- **Noise of both derivatives** (clause 3 of `DiffCovarianceFamilyStatement`;
the derivative-noise bound). After `b, κ` and the fixed moment order `p ≥ 1`: there are `C_p, W₀`
such that for `W ≥ W₀`, Hermitian `X`, `S ⪰ 0`, `E ∈ bulkInterval κ` and `‖D‖ ≤ 1`, with
`ġ_P = -W⁻¹ Tr(D𝒢P𝒢)` (the a.s. derivative of clause 1 for `P = Ŝ` and of clause 2 for
`P = -Ŝ + D₀`, `S = X'(E₀)`, `X = X(E₀)`):
`‖ġ_Ŝ - Eġ_Ŝ‖_p ≤ C_p W^{-3/2}‖Y‖_HS ≤ C_p u/√W` and
`‖ġ_{-Ŝ+D₀} - Eġ_{-Ŝ+D₀}‖_p ≤ C_p(1+u)/√W`. -/
def tgtNoiseClause (b κ : ℝ) : Prop :=
  ∀ p : ℝ, 1 ≤ p → ∃ (Cp : ℝ) (W₀ : ℕ), ∀ (W : ℕ), 0 < W → W₀ ≤ W →
    ∀ X S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, X.IsHermitian → S.PosSemidef →
    ∀ E ∈ bulkInterval κ,
    ∀ D : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ, ‖D‖ ≤ 1 →
      let μ := layerLaw W b .separate
      let z := boundaryZ b E
      let K := z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X
      let Y := (K⁻¹)ᴴ * S * K⁻¹
      let u := (W : ℝ)⁻¹ * Y.trace.re
      let G := fun ω => layerResolvent .separate E z X ω
      let gdot := fun (P : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ) ω =>
        -((W : ℂ)⁻¹ * (D * (G ω * P * G ω)).trace)
      eLpNorm (fun ω => gdot (dcvHat S) ω - ∫ ω', gdot (dcvHat S) ω' ∂μ) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (Cp / (W * Real.sqrt W) * Real.sqrt (Y * Y).trace.re) ∧
      Cp / (W * Real.sqrt W) * Real.sqrt (Y * Y).trace.re ≤ Cp * u / Real.sqrt W ∧
      eLpNorm (fun ω => gdot (-dcvHat S + tgtD0 (tgtZd b E)) ω -
          ∫ ω', gdot (-dcvHat S + tgtD0 (tgtZd b E)) ω' ∂μ) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (Cp * (1 + u) / Real.sqrt W)

/-- **The differentiated-covariance lemma for curved and energy families.** It extends
`DiffCovarianceStatement` and does not replace its linear-family clauses.

*Setting and law.* As in `DiffCovarianceStatement`: the conditioning data (the old two-port
input `X` or the family `X(·)`, and the source `S`) are deterministic, and expectations,
covariances and `L^p` norms are over the fresh separate-port layer only,
`μ = layerLaw W b .separate` (`A_a ~ GUE_W(c/W)`, `c = 1 - 2b`, bonds `Gin(b/W)`), at
`z = z_∂(E)`, `E ∈ bulkInterval κ`. `K = z - X`, `Y = K⁻*SK⁻¹`, `u = W⁻¹ Re Tr Y`,
`Ŝ = dcvHat S`, `g = W⁻¹ Tr(D𝒢)` for every deterministic `‖D‖ ≤ 1` (covering each block
projection `P_i`). The source families are general: only `HasDerivAt` of the deterministic
family at the base point and Hermiticity near it are assumed (curved: `X(h) = X - hS + o(h)`;
energy: `E ↦ (E, z_∂(E), X(E))` with `X'(E₀) = S ⪰ 0`).

*Norms.* `‖·‖` is the `ℓ²` operator norm, `‖Y‖_HS = √(Re Tr Y²)`, covariances are entrywise
(`dcvCov`), and `L^p` norms are `eLpNorm` under `μ`.

*Quantifiers and uniformity.* `b ∈ (0, 1/2)` and `κ > 0` first; then (for the noise) `p ≥ 1`;
then `C` (`C_p`) and `W₀`; then uniformly in `W ≥ W₀`, the Hermitian old input and family, the
source, `E ∈ bulkInterval κ` and `D`. The constants do not depend on the family, on `δ`, or on
`‖S‖` ("uniform in the old Hermitian deformation and source").

*Clauses.* `tgtCurvedClause` (the covariance derivative formula along curved families, with the a.s.
trace derivative), `tgtEnergyClause` (the energy derivative identity
`∂_E Cov = dcvCovDir(-Ŝ + D₀)`, `D₀ = diag(-I, z_∂' I)`, and the `1 + u` bound) and
`tgtNoiseClause` (the derivative-noise bound for both directions). -/
def DiffCovarianceFamilyStatement : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
    tgtCurvedClause b κ ∧ tgtEnergyClause b κ ∧ tgtNoiseClause b κ

/-!
## 5. Proofs of the clauses
-/

/-- Clause 1 (`tgtCurvedClause`). -/
theorem tgt_curved_clause (hcount : ConditionalBlockGUECount) (hwl : WeightedLayerContract)
    {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) : tgtCurvedClause b κ := by
  obtain ⟨C, W₁, hcov⟩ := dcv_cov_clause hcount hwl b hb0 hb1 κ hκ 0
  obtain ⟨η₀, hη₀, hbulk⟩ := dcv_bulk hb0 hb1 hκ
  obtain ⟨ε₁, CA, hε₁, hCA, habs⟩ := gaussianAbsorption_holds hcount b hb0 hb1 η₀ 3 hη₀
  refine ⟨C, max W₁ ⌈4 / ε₁⌉₊, ?_⟩
  intro W hW hWW X S hX hS E hE D hD Xf δ hδ hXf0 hXd hXh μ z K Y u G Gf
  obtain ⟨-, hc1, hc2, -⟩ :=
    hcov W hW ((le_max_left _ _).trans hWW) X S hX hS E hE D hD 0 (by simp)
  obtain ⟨hzim, hzM, -⟩ := hbulk E hE
  have hW4 : ((4 : ℕ) : ℝ) ≤ ε₁ * W := by
    have h1 : 4 / ε₁ ≤ (W : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hWW)
    rw [div_le_iff₀ hε₁] at h1; push_cast; linarith
  set Δ : ℝ → Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ := fun h =>
    tgtBlk (Xf 0 - Xf h, (0 : Matrix (PortSite W .separate) (PortSite W .separate) ℂ)) with hΔdef
  have hΔ : HasDerivAt Δ (dcvHat S) 0 := by
    have h1 : HasDerivAt (fun h : ℝ => (Xf 0 - Xf h,
        (0 : Matrix (PortSite W .separate) (PortSite W .separate) ℂ))) (-(-S), 0) 0 :=
      (hXd.const_sub (Xf 0)).prodMk (hasDerivAt_const 0 0)
    have h2 := tgtBlk.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
    rw [neg_neg] at h2
    exact h2
  have hΔ0 : Δ 0 = 0 := by simp [hΔdef, tgtBlk_apply]
  have hfam := tgt_layer_family hW .separate (fun _ => E) (fun _ => z) Xf D Δ (dcvHat S) hΔ hΔ0
    (fun h ω => tgt_layerMatrix_curved E z (Xf 0) (Xf h) ω) hδ
    (fun h hh => (habs W hW .separate _ (hXh h hh) E z hzim hzM).1) (C4 := CA ^ 4)
    (fun h hh => tcv_moment (m := 4) (by norm_num) hCA.le
      ((habs W hW .separate _ (hXh h hh) E z hzim hzM).2 _ (by norm_num) hW4))
  rw [hXf0] at hfam
  exact ⟨hfam.1, hfam.2, hc1, hc2⟩

/-- The energy insertion bound `‖-D₀‖ ≤ 1 + (b+1)/√(2κ)` on `bulkInterval κ`. -/
theorem tgt_norm_neg_tgtD0_le {W : ℕ} {σ : LayerShape} {b κ E : ℝ} (hb : 0 ≤ b) (hκ : 0 < κ) (hE : E ∈ bulkInterval κ) :
    ‖-(tgtD0 (tgtZd b E) : Matrix (LayerSite W σ) (LayerSite W σ) ℂ)‖ ≤
      1 + (b + 1) / Real.sqrt (2 * κ) := by
  rw [norm_neg]
  exact (tgt_norm_tgtD0_le _).trans (by linarith [tgt_norm_tgtZd_le hb hκ hE])

/-- Clause 2 (`tgtEnergyClause`). -/
theorem tgt_energy_clause (hcount : ConditionalBlockGUECount) (hwl : WeightedLayerContract)
    {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) : tgtEnergyClause b κ := by
  obtain ⟨C, W₁, hcov⟩ := dcv_cov_clause hcount hwl b hb0 hb1 κ hκ
    (1 + (b + 1) / Real.sqrt (2 * κ))
  have hκ2 : 0 < κ / 2 := by positivity
  obtain ⟨η₀, hη₀, hbulk⟩ := dcv_bulk hb0 hb1 hκ2
  obtain ⟨ε₁, CA, hε₁, hCA, habs⟩ := gaussianAbsorption_holds hcount b hb0 hb1 η₀ 3 hη₀
  refine ⟨C, max W₁ ⌈4 / ε₁⌉₊, ?_⟩
  intro W hW hWW Xf S E₀ δ hE₀ hδ hS hXd hXh D hD μ X z K Y u G P Gf
  have hXH : X.IsHermitian := hXh E₀ (by simp [hδ.le])
  obtain ⟨-, -, -, hins⟩ := hcov W hW ((le_max_left _ _).trans hWW) X S hXH hS E₀ hE₀ D hD _
    (tgt_norm_neg_tgtD0_le hb0.le hκ hE₀)
  have hW4 : ((4 : ℕ) : ℝ) ≤ ε₁ * W := by
    have h1 : 4 / ε₁ ≤ (W : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hWW)
    rw [div_le_iff₀ hε₁] at h1; push_cast; linarith
  have hE₀' : E₀ ∈ Set.Ioo (-2 : ℝ) 2 := abs_lt.mp (abs_lt_two_of_mem_bulkInterval hκ hE₀)
  set z₁ := tgtZd b E₀ with hz₁
  -- the insertion family
  set Δ : ℝ → Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ := fun t =>
    tgtBlk ((-t) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) + (Xf E₀ - Xf (E₀ + t)),
      (boundaryZ b (E₀ + t) - boundaryZ b E₀) •
        (1 : Matrix (PortSite W .separate) (PortSite W .separate) ℂ)) with hΔdef
  have hX' : HasDerivAt (fun t => Xf (E₀ + t)) S 0 :=
    HasDerivAt.comp_const_add E₀ 0 (by rwa [add_zero])
  have hz' : HasDerivAt (fun t => boundaryZ b (E₀ + t)) z₁ 0 :=
    HasDerivAt.comp_const_add E₀ 0 (by rw [add_zero]; exact tgt_hasDerivAt_boundaryZ b hE₀')
  have ha : HasDerivAt (fun t : ℝ => (-t) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) +
      (Xf E₀ - Xf (E₀ + t))) ((-1 : ℝ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) + -S) 0 :=
    ((hasDerivAt_neg 0).smul_const _).add (hX'.const_sub _)
  have hb : HasDerivAt (fun t : ℝ => (boundaryZ b (E₀ + t) - boundaryZ b E₀) •
      (1 : Matrix (PortSite W .separate) (PortSite W .separate) ℂ)) (z₁ • 1) 0 :=
    (hz'.sub_const _).smul_const _
  have hΔ' := tgtBlk.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (ha.prodMk hb)
  have hPeq : tgtBlk ((-1 : ℝ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) + -S,
      z₁ • (1 : Matrix (PortSite W .separate) (PortSite W .separate) ℂ)) = P := by
    rw [tgtBlk_apply]
    change _ = -dcvHat S + tgtD0 z₁
    rw [dcvHat, tgtD0, fromBlocks_neg, fromBlocks_add]
    congr 1
    · rw [neg_one_smul]; abel
    · simp
    · simp
    · simp
  have hΔ : HasDerivAt Δ P 0 := by rw [← hPeq]; exact hΔ'
  have hΔ0 : Δ 0 = 0 := by simp [hΔdef, tgtBlk_apply]
  have hshift : ∀ (t : ℝ) ω, layerMatrix .separate (E₀ + t) (boundaryZ b (E₀ + t)) (Xf (E₀ + t)) ω =
      layerMatrix .separate (E₀ + 0) (boundaryZ b (E₀ + 0)) (Xf (E₀ + 0)) ω + Δ t := by
    intro t ω
    simp only [add_zero]
    exact tgt_layerMatrix_energy E₀ t _ _ _ _ ω
  have hδ' : 0 < min δ (κ / 2) := lt_min hδ hκ2
  have hmem : ∀ t : ℝ, |t| ≤ min δ (κ / 2) →
      E₀ + t ∈ bulkInterval (κ / 2) ∧ (Xf (E₀ + t)).IsHermitian := fun t ht => by
    have h1 := abs_le.mp (ht.trans (min_le_right _ _))
    refine ⟨⟨by linarith [hE₀.1], by linarith [hE₀.2]⟩, hXh _ ?_⟩
    rw [add_sub_cancel_left]; exact ht.trans (min_le_left _ _)
  have hinv : ∀ t : ℝ, |t| ≤ min δ (κ / 2) → ∀ᵐ ω ∂layerLaw W b .separate,
      IsUnit (layerMatrix .separate (E₀ + t) (boundaryZ b (E₀ + t)) (Xf (E₀ + t)) ω).det :=
    fun t ht => (habs W hW .separate _ (hmem t ht).2 _ _ (hbulk _ (hmem t ht).1).1
      (hbulk _ (hmem t ht).1).2.1).1
  have hmom : ∀ t : ℝ, |t| ≤ min δ (κ / 2) →
      Integrable (fun ω => ‖layerResolvent .separate (E₀ + t) (boundaryZ b (E₀ + t))
        (Xf (E₀ + t)) ω‖ ^ 4) (layerLaw W b .separate) ∧
      ∫ ω, ‖layerResolvent .separate (E₀ + t) (boundaryZ b (E₀ + t)) (Xf (E₀ + t)) ω‖ ^ 4
        ∂layerLaw W b .separate ≤ CA ^ 4 :=
    fun t ht => tcv_moment (m := 4) (by norm_num) hCA.le
      ((habs W hW .separate _ (hmem t ht).2 _ _ (hbulk _ (hmem t ht).1).1
        (hbulk _ (hmem t ht).1).2.1).2 _ (by norm_num) hW4)
  have hfam := tgt_layer_family hW .separate (fun t => E₀ + t) (fun t => boundaryZ b (E₀ + t))
    (fun t => Xf (E₀ + t)) D Δ P hΔ hΔ0 hshift hδ' hinv hmom
  simp only [add_zero] at hfam
  refine ⟨tgt_hasDerivAt_shift hfam.1, ?_, ?_⟩
  · filter_upwards [hfam.2] with ω hω
    exact tgt_hasDerivAt_shift hω
  · have e : (-dcvHat S + tgtD0 z₁ :
        Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ) =
          -(dcvHat S + -tgtD0 z₁) := by rw [neg_add, neg_neg]
    change ‖dcvCovDir μ D G (-dcvHat S + tgtD0 z₁)‖ ≤ C * (1 + u) / W
    rw [e, tgt_dcvCovDir_neg, norm_neg]
    exact hins

/-- Clause 3 (`tgtNoiseClause`). -/
theorem tgt_noise_clause (hcount : ConditionalBlockGUECount) (hgrad : GaussianLpGradient)
    (hwl : WeightedLayerContract) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) :
    tgtNoiseClause b κ := by
  intro p hp
  obtain ⟨Cp, W₀, hn⟩ := dcv_noise_clause hcount hgrad hwl b hb0 hb1 κ hκ
    (1 + (b + 1) / Real.sqrt (2 * κ)) p hp
  refine ⟨Cp, W₀, ?_⟩
  intro W hW hWW X S hX hS E hE D hD μ z K Y u G gdot
  have hK0 : ‖(0 : Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ)‖ ≤
      1 + (b + 1) / Real.sqrt (2 * κ) := by
    rw [norm_zero]; positivity
  obtain ⟨-, h1, h2, -⟩ := hn W hW hWW X S hX hS E hE D hD 0 hK0
  obtain ⟨-, -, -, h3⟩ := hn W hW hWW X S hX hS E hE D hD _
    (tgt_norm_neg_tgtD0_le hb0.le hκ hE)
  refine ⟨h1, h2, ?_⟩
  have e : (-dcvHat S + tgtD0 (tgtZd b E) :
      Matrix (LayerSite W .separate) (LayerSite W .separate) ℂ) =
        -(dcvHat S + -tgtD0 (tgtZd b E)) := by rw [neg_add, neg_neg]
  simp only [gdot]
  rw [e, tgt_gdot_neg, eLpNorm_neg]
  exact h3

/-!
## 6. The constructor
-/

/-- **The differentiated-covariance lemma for curved and energy families**
(`DiffCovarianceFamilyStatement`), from `ConditionalBlockGUECount` (through the Gaussian
absorption lemma), `GaussianLpGradient` and `WeightedLayerContract` (`moments` field only,
through `dcv_theta_eLpNorm`). Constants: those of `diffCovariance_holds` with `K₀ = 0` (curved)
and `K₀ = 1 + (b+1)/√(2κ)` (energy, noise); `W₀` additionally `≥ ⌈4/ε₁⌉`, with `ε₁` from the
Gaussian absorption lemma on `bulkInterval κ` (curved) or `bulkInterval (κ/2)` (energy). -/
theorem diffCovarianceFamily_holds (hcount : ConditionalBlockGUECount)
    (hgrad : GaussianLpGradient) (hwl : WeightedLayerContract) :
    DiffCovarianceFamilyStatement := fun _ hb0 hb1 _ hκ =>
  ⟨tgt_curved_clause hcount hwl hb0 hb1 hκ, tgt_energy_clause hcount hwl hb0 hb1 hκ,
    tgt_noise_clause hcount hgrad hwl hb0 hb1 hκ⟩

/-- `DiffCovarianceFamilyStatement` from `ConditionalBlockGUECount` and `GaussianLpGradient`
alone, with `WeightedLayerContract` supplied by `weightedLayer_holds`. -/
theorem diffCovarianceFamily_holds' (hcount : ConditionalBlockGUECount)
    (hgrad : GaussianLpGradient) : DiffCovarianceFamilyStatement :=
  diffCovarianceFamily_holds hcount hgrad (weightedLayer_holds hcount hgrad)

end BlockBand.Layers
