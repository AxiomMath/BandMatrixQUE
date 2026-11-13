module

public import BlockBand.Native.ErdosRiabov.LemmaK.PartA

/-!
# The kernel lemma, clauses (K1)–(K3), (K5)–(K7)

Bounds on the VS kernels `A_t` by the polynomial control `Υ` (clauses `lemmaK_K1`, `lemmaK_K2`,
`lemmaK_K3`, `lemmaK_K5`, `lemmaK_K6`, `lemmaK_K7` of the kernel lemma).

Setting: `0 < b < 1/2`, `δ₀, κ > 0`, `C₀ ≥ 1`, `D ≥ 6`,
`m ≥ 4`, `W ≥ 1`, `N = mW`, `S = shortRingProfile b m W`, `Υ_h = polynomialControl N W D h`.
Two terminal points `z, z' ∈ 𝒟 = BulkDomain N δ₀ κ C₀` (upper half-plane representatives; the
single-trajectory kernels are the case `z' = z`), `m = semicircleM z`, `m' = semicircleM z'`,
heights `η_t(z) = vsHeight z t`; pair heights `η_t = min (η_t z) (η_t z')`, `η₀^Ξ = min (η₀ z)
(η₀ z')`. Kernels (`vsKernel`): Θ-type `A_t(z, z̄') = vsKernel S m
(conj m') t` (for `z' = z` this is `T̂_t`), Ξ-type `A_t(z, z') = vsKernel S m m' t` (for `z' = z`
this is `X̂_t`); propagators `vsPropagator` (closed form `(1-sY)(1-tY)⁻¹`). Lower-half-plane
pairs have the entrywise conjugate kernel (`μ ↦ conj μ`) and the same heights; they are not
restated. Constants: `C_K = lemmaKConst b κ C₀ D`, `C₁'' = lemmaKC1 b κ C₀ D`,
`c_m = imLower κ C₀`, record `q = lemmaKParams …`.

Proof structure: for `t ≤ 1/4`, the Neumann bound `lemmaK_partA`; for `t ≥ 1/4`, the admissibility theorem
(`cf1_vs`) at `w_t = lemmaKPoint z t` through `theta_vsScale`, `xi_vsScale` and
`lemmaKPoint_domain`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.LemmaK

open BlockBand.External BlockBand.Internal.Contracts.Inputs BlockBand.Adapters.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.External.ErdosRiabov (semicircleM semicircleM_dyson norm_semicircleM_lt_one)
open scoped BigOperators ComplexConjugate

/-!
## Heights
-/

private theorem lemmaK_height_facts {N : ℕ} (hN : 0 < N) {δ₀ κ C₀ : ℝ} {z : ℂ}
    (hz : BulkDomain N δ₀ κ C₀ z) :
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      (N : ℝ) ^ (-1 + δ₀) ≤ vsHeight z t ∧ vsHeight z t ≤ C₀ + 1) ∧
    (∀ t : ℝ, t ≤ 1 / 4 → 3 * imLower κ C₀ / 4 ≤ vsHeight z t) ∧
    imLower κ C₀ ≤ vsHeight z 0 ∧
    (∀ s t : ℝ, s ≤ t → t ≤ 1 → (t - s) * imLower κ C₀ ≤ vsHeight z s) := by
  have hη := hz.im_pos hN
  have hC0 : 0 ≤ C₀ := (norm_nonneg z).trans hz.2.2
  have hy := semicircleM_im_pos hη
  have hcm := semicircleM_im_ge hC0 hz.1 hη hz.2.2
  have hm1 := norm_semicircleM_lt_one hη.ne'
  have him : z.im ≤ C₀ :=
    (le_abs_self _).trans ((Complex.abs_im_le_norm z).trans hz.2.2)
  have hmim : (semicircleM z).im ≤ 1 :=
    ((le_abs_self _).trans (Complex.abs_im_le_norm _)).trans hm1.le
  refine ⟨fun t ht0 ht1 => ⟨?_, ?_⟩, fun t ht => ?_, ?_, fun s t hst ht1 => ?_⟩
  · exact hz.2.1.trans (lemmaK_im_le_vsHeight hη ht1)
  · unfold vsHeight
    nlinarith
  · unfold vsHeight
    nlinarith
  · unfold vsHeight
    linarith
  · have hpos := lemmaK_vsHeight_pos hη ht1
    have he : vsHeight z s = vsHeight z t + (t - s) * (semicircleM z).im := by
      unfold vsHeight
      ring
    rw [he]
    nlinarith

/-!
## Lower-half-plane pairs
-/

/-- Lower-half-plane pairs: for a stochastic symmetric `S`
and `‖tμμ'‖ < 1`, `A_t(conj μ, conj μ') = conj A_t(μ, μ')` entrywise; so the bounds below for
`(z, z̄')` and `(z, z')` transfer, with the same heights, to `(z̄, z')` and `(z̄, z̄')`. -/
theorem lemmaK_vsKernel_conj {N : ℕ} {S : Matrix (Fin N) (Fin N) ℝ} (hS : StochasticSymm S)
    {μ μ' : ℂ} {t : ℝ} (ht : ‖(t : ℂ) * (μ * μ')‖ < 1) (x y : Fin N) :
    vsKernel S (conj μ) (conj μ') t x y = conj (vsKernel S μ μ' t x y) := by
  have hc : (t : ℂ) * (conj μ * conj μ') = conj ((t : ℂ) * (μ * μ')) := by
    simp only [map_mul, Complex.conj_ofReal]
  have ht' : ‖(t : ℂ) * (conj μ * conj μ')‖ < 1 := by rwa [hc, Complex.norm_conj]
  rw [vsKernel_apply hS ht' x y, vsKernel_apply hS ht x y]
  simp only [map_mul, map_pow, Complex.conj_ofReal, Complex.conj_tsum]

/-!
## Elementary helpers
-/

/-- For `0 < e ≤ 1`, `e ≤ h`, `u ≥ 0`: `e ≤ min (u + W) ℓ(h) / ℓ(h)`. -/
private theorem lemmaK_regFactor_lower {N W : ℕ} (hN : 0 < N) (hW : 0 < W) {e h u : ℝ}
    (he0 : 0 < e) (he1 : e ≤ 1) (heh : e ≤ h) (hu : 0 ≤ u) :
    e ≤ min (u + W) (ErdosRiabov.localizationLength N W h) /
      ErdosRiabov.localizationLength N W h := by
  have hh : 0 < h := he0.trans_le heh
  have hl := loc_pos hN hW hh
  have hsq : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh
  have hesq : e ≤ Real.sqrt h := by
    have h1 := Real.sqrt_le_sqrt (show e ^ 2 ≤ h by nlinarith)
    rwa [Real.sqrt_sq he0.le] at h1
  have hlW : ErdosRiabov.localizationLength N W h ≤ (W : ℝ) / Real.sqrt h := min_le_left _ _
  rw [le_div_iff₀ hl]
  refine le_min ?_ ?_
  · have h2 : Real.sqrt h * ((W : ℝ) / Real.sqrt h) = W := mul_div_cancel₀ _ hsq.ne'
    have h3 : e * ErdosRiabov.localizationLength N W h ≤
        Real.sqrt h * ((W : ℝ) / Real.sqrt h) := mul_le_mul hesq hlW hl.le hsq.le
    linarith
  · nlinarith

/-- `Υ_1 ≤ (C₀+1)^{1+D/2} Υ_h` for `0 < h ≤ C₀ + 1`. -/
private theorem lemmaK_ups_one_le {N W : ℕ} (hN : 0 < N) (hW : 0 < W) {D : ℝ} (hD : 0 ≤ D)
    {C₀ : ℝ} (hC₀ : 1 ≤ C₀) {h : ℝ} (hh : 0 < h) (hhC : h ≤ C₀ + 1) (x y : Fin N) :
    polynomialControl N W D 1 x y ≤ (C₀ + 1) ^ (1 + D / 2) * polynomialControl N W D h x y := by
  have hΥ := polynomialControl_pos hN hW D hh x y
  rcases le_total h 1 with h1 | h1
  · have hp : 1 ≤ (C₀ + 1) ^ (1 + D / 2) := Real.one_le_rpow (by linarith) (by linarith)
    have := polynomialControl_mono hN hW hD hh h1 x y
    nlinarith
  · have hr := polynomialControl_reverse hN hW hD one_pos h1 x y
    rw [div_one] at hr
    have hp : h ^ (1 + D / 2) ≤ (C₀ + 1) ^ (1 + D / 2) :=
      Real.rpow_le_rpow hh.le hhC (by linarith)
    exact hr.trans (mul_le_mul_of_nonneg_right hp hΥ.le)

/-!
## Part B: `t ≥ 1/4`
-/

/-- Part B of Lemma K: for `t ∈ [1/4, 1]`, polynomial-control clauses (i),
(vi), (vii) at `w_t, w'_t`, divided by `t`.
-/
private theorem lemmaK_partB {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {δ₀ κ C₀ D : ℝ}
    (hδ₀ : 0 < δ₀) (hκ : 0 < κ) (hC₀ : 1 ≤ C₀) (hD : 6 ≤ D) {m W : ℕ} (hm : 4 ≤ m)
    (hW : 0 < W) {z z' : ℂ} (hz : BulkDomain (m * W) δ₀ κ C₀ z)
    (hz' : BulkDomain (m * W) δ₀ κ C₀ z') {t : ℝ} (ht : 1 / 4 ≤ t) (ht1 : t ≤ 1) :
    (∀ x y, ‖vsKernel (shortRingProfile b m W) (semicircleM z) (conj (semicircleM z')) t x y‖ ≤
      4 * lemmaKC1 b hb0 hb κ C₀ D *
        polynomialControl (m * W) W D (min (vsHeight z t) (vsHeight z' t)) x y) ∧
    (∀ x y, ‖vsKernel (shortRingProfile b m W) (semicircleM z) (semicircleM z') t x y‖ ≤
      4 * lemmaKC1 b hb0 hb κ C₀ D * polynomialControl (m * W) W D 1 x y) ∧
    (((W : ℝ) / ((m * W : ℕ) : ℝ)) ^ 2 ≤ min (vsHeight z t) (vsHeight z' t) → ∀ a x y,
      ‖vsKernel (shortRingProfile b m W) (semicircleM z) (conj (semicircleM z')) t a x -
          vsKernel (shortRingProfile b m W) (semicircleM z) (conj (semicircleM z')) t a y‖ ≤
        8 * lemmaKC1 b hb0 hb κ C₀ D *
          (min ((ErdosRiabov.cyclicDistance (m * W) x y : ℝ) + W)
              (ErdosRiabov.localizationLength (m * W) W
                (min (vsHeight z t) (vsHeight z' t))) /
            ErdosRiabov.localizationLength (m * W) W (min (vsHeight z t) (vsHeight z' t))) *
          (polynomialControl (m * W) W D (min (vsHeight z t) (vsHeight z' t)) a x +
            polynomialControl (m * W) W D (min (vsHeight z t) (vsHeight z' t)) a y)) ∧
    (∀ a x,
      ‖vsKernel (shortRingProfile b m W) (semicircleM z) (conj (semicircleM z')) t a x -
          (1 / ((m * W : ℕ) : ℂ)) *
            ∑ c, vsKernel (shortRingProfile b m W) (semicircleM z) (conj (semicircleM z')) t a c‖
        ≤ 4 * lemmaKC1 b hb0 hb κ C₀ D * ((m * W : ℕ) : ℝ) / (W : ℝ) ^ 2) := by
  have hN : 0 < m * W := Nat.mul_pos (by omega) hW
  have ht0 : 0 < t := by linarith
  have hD0 : (0 : ℝ) ≤ D := by linarith
  have hzi := (hz.im_pos hN).ne'
  have hz'i := (hz'.im_pos hN).ne'
  set S := shortRingProfile b m W with hSdef
  set q := lemmaKParams b hb0 hb δ₀ κ C₀ D hδ₀ hκ hC₀ hD with hqdef
  have hqC1 : q.C1 = lemmaKC1 b hb0 hb κ C₀ D := rfl
  have hC1 := lemmaKC1_ge_one hb0 hb κ C₀ D
  have hadm : ErdosRiabov.AdmissibleControl q (m * W) W S (polynomialControl (m * W) W D) :=
    cf1_vs hb0 hb hδ₀ hκ hC₀ hD hm hW
  obtain ⟨hw, hw', hs, -, hlo, hhi⟩ :=
    lemmaKPoint_domain hN hκ hz hz' q rfl le_rfl le_rfl ht ht1
  have hpos : 0 < min (vsHeight z t) (vsHeight z' t) :=
    lt_min (lemmaK_vsHeight_pos (hz.im_pos hN) ht1) (lemmaK_vsHeight_pos (hz'.im_pos hN) ht1)
  have hposw := hpos.trans_le hlo
  have hns : ∀ (M : Matrix (Fin (m * W)) (Fin (m * W)) ℂ) (x y : Fin (m * W)),
      ‖((t : ℂ) • M) x y‖ = t * ‖M x y‖ := fun M x y => by
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht0]
  refine ⟨fun x y => ?_, fun x y => ?_, fun hthr a x y => ?_, fun a x => ?_⟩
  · have h1 := (hadm.clause1 _ _ hw hw' hs x y).1
    rw [theta_vsScale S hzi hz'i ht0 ht1, hns, hqC1] at h1
    have hmono := polynomialControl_mono hN hW hD0 hpos hlo x y
    have hA := norm_nonneg (vsKernel S (semicircleM z) (conj (semicircleM z')) t x y)
    have h2 := mul_le_mul_of_nonneg_left hmono (by linarith : (0 : ℝ) ≤ lemmaKC1 b hb0 hb κ C₀ D)
    nlinarith
  · have h1 := (hadm.clause1 _ _ hw hw' hs x y).2
    rw [xi_vsScale S hzi hz'i ht0 ht1, hns, hqC1] at h1
    have hA := norm_nonneg (vsKernel S (semicircleM z) (semicircleM z') t x y)
    nlinarith
  · have hthr' : q.c2 * ((W : ℝ) / ((m * W : ℕ) : ℝ)) ^ 2 ≤
        min |(lemmaKPoint z t).im| |(lemmaKPoint z' t).im| := by
      show (1 : ℝ) * _ ≤ _
      rw [one_mul]
      exact hthr.trans hlo
    have h6 := hadm.clause6 _ _ hw hw' hs hthr' a x y
    rw [theta_vsScale S hzi hz'i ht0 ht1, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul,
      smul_eq_mul, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0,
      hqC1] at h6
    set hm0 := min (vsHeight z t) (vsHeight z' t) with hm0def
    set hmw := min |(lemmaKPoint z t).im| |(lemmaKPoint z' t).im| with hmwdef
    set ℓ := ErdosRiabov.localizationLength (m * W) W hm0 with hℓdef
    set ℓw := ErdosRiabov.localizationLength (m * W) W hmw with hℓwdef
    have hl : 0 < ℓ := loc_pos hN hW hpos
    have hlw : 0 < ℓw := loc_pos hN hW hposw
    have hℓ1 : ℓw ≤ ℓ := loc_antitone (m * W) W hpos hlo
    have hℓ2 : ℓ ≤ 2 * ℓw := by
      have h1 := loc_le_sqrt_ratio_mul (m * W) W hpos hlo
      have hr : Real.sqrt (hmw / hm0) ≤ 2 := by
        have h2 : hmw / hm0 ≤ 2 ^ 2 := by
          rw [div_le_iff₀ hpos]
          nlinarith
        calc Real.sqrt (hmw / hm0) ≤ Real.sqrt (2 ^ 2) := Real.sqrt_le_sqrt h2
          _ = 2 := Real.sqrt_sq (by norm_num)
      have h3 := mul_le_mul_of_nonneg_right hr hlw.le
      linarith
    set u : ℝ := (ErdosRiabov.cyclicDistance (m * W) x y : ℝ) + W with hudef
    have hu : 0 ≤ u := by positivity
    have hF : min u ℓw / ℓw ≤ 2 * (min u ℓ / ℓ) := by
      rw [div_le_iff₀ hlw]
      have hM : 0 ≤ min u ℓ := le_min hu hl.le
      calc min u ℓw ≤ min u ℓ := min_le_min_left u hℓ1
        _ ≤ min u ℓ * (2 * ℓw / ℓ) :=
            le_mul_of_one_le_right hM (by rw [le_div_iff₀ hl]; linarith)
        _ = 2 * (min u ℓ / ℓ) * ℓw := by ring
    have hFw0 : 0 ≤ min u ℓw / ℓw := div_nonneg (le_min hu hlw.le) hlw.le
    have hF0 : 0 ≤ min u ℓ / ℓ := div_nonneg (le_min hu hl.le) hl.le
    have hU1 := polynomialControl_mono hN hW hD0 hpos hlo a x
    have hU2 := polynomialControl_mono hN hW hD0 hpos hlo a y
    have hUw1 := polynomialControl_pos hN hW D hposw a x
    have hUw2 := polynomialControl_pos hN hW D hposw a y
    have hstep : lemmaKC1 b hb0 hb κ C₀ D * (min u ℓw / ℓw) *
          (polynomialControl (m * W) W D hmw a x + polynomialControl (m * W) W D hmw a y) ≤
        lemmaKC1 b hb0 hb κ C₀ D * (2 * (min u ℓ / ℓ)) *
          (polynomialControl (m * W) W D hm0 a x + polynomialControl (m * W) W D hm0 a y) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hF (by linarith)) (add_le_add hU1 hU2)
        (by positivity) (by positivity)
    have hΔ := norm_nonneg (vsKernel S (semicircleM z) (conj (semicircleM z')) t a x -
      vsKernel S (semicircleM z) (conj (semicircleM z')) t a y)
    nlinarith
  · have h7 := hadm.clause7 _ _ hw hw' hs a x
    have hrw : ErdosRiabov.theta S (lemmaKPoint z t) (lemmaKPoint z' t) a x -
          (1 / ((m * W : ℕ) : ℂ)) *
            ∑ c, ErdosRiabov.theta S (lemmaKPoint z t) (lemmaKPoint z' t) a c =
        (t : ℂ) * (vsKernel S (semicircleM z) (conj (semicircleM z')) t a x -
          (1 / ((m * W : ℕ) : ℂ)) *
            ∑ c, vsKernel S (semicircleM z) (conj (semicircleM z')) t a c) := by
      rw [theta_vsScale S hzi hz'i ht0 ht1]
      simp only [Matrix.smul_apply, smul_eq_mul]
      rw [← Finset.mul_sum]
      ring
    rw [hrw, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0, hqC1] at h7
    have hΔ := norm_nonneg (vsKernel S (semicircleM z) (conj (semicircleM z')) t a x -
      (1 / ((m * W : ℕ) : ℂ)) * ∑ c, vsKernel S (semicircleM z) (conj (semicircleM z')) t a c)
    have h8 : 4 * lemmaKC1 b hb0 hb κ C₀ D * ((m * W : ℕ) : ℝ) / (W : ℝ) ^ 2 =
        4 * (lemmaKC1 b hb0 hb κ C₀ D * ((m * W : ℕ) : ℝ) / (W : ℝ) ^ 2) := by ring
    rw [h8]
    nlinarith

/-!
## (K1)
-/

/-- For `0 < b < 1/2`,
`δ₀, κ > 0`, `C₀ ≥ 1`, `D ≥ 6`, `m ≥ 4`, `W ≥ 1`, `z, z' ∈ 𝒟` and `t ∈ [0,1]`, all sites:
Θ-type `|A_t(z, z̄')(x,y)| ≤ C_K Υ_{η_t}(x,y)` (`η_t = min (η_t z) (η_t z')`); Ξ-type
`|A_t(z, z')(x,y)| ≤ C_K Υ_{η₀^Ξ}(x,y)` and `≤ C_K Υ_1(x,y)`; and `T̂_t = A_t(z, z̄) ≥ 0`
entrywise (real).
-/
theorem lemmaK_K1 {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {δ₀ κ C₀ D : ℝ} (hδ₀ : 0 < δ₀)
    (hκ : 0 < κ) (hC₀ : 1 ≤ C₀) (hD : 6 ≤ D) {m W : ℕ} (hm : 4 ≤ m) (hW : 0 < W) {z z' : ℂ}
    (hz : BulkDomain (m * W) δ₀ κ C₀ z) (hz' : BulkDomain (m * W) δ₀ κ C₀ z') {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∀ x y, ‖vsKernel (shortRingProfile b m W) (semicircleM z) (conj (semicircleM z')) t x y‖ ≤
      lemmaKConst b hb0 hb κ C₀ D *
        polynomialControl (m * W) W D (min (vsHeight z t) (vsHeight z' t)) x y) ∧
    (∀ x y, ‖vsKernel (shortRingProfile b m W) (semicircleM z) (semicircleM z') t x y‖ ≤
      lemmaKConst b hb0 hb κ C₀ D *
        polynomialControl (m * W) W D (min (vsHeight z 0) (vsHeight z' 0)) x y) ∧
    (∀ x y, ‖vsKernel (shortRingProfile b m W) (semicircleM z) (semicircleM z') t x y‖ ≤
      lemmaKConst b hb0 hb κ C₀ D * polynomialControl (m * W) W D 1 x y) ∧
    (∀ x y,
      (vsKernel (shortRingProfile b m W) (semicircleM z) (conj (semicircleM z)) t x y).im = 0 ∧
      0 ≤ (vsKernel (shortRingProfile b m W) (semicircleM z) (conj (semicircleM z)) t x y).re) := by
  have hN : 0 < m * W := Nat.mul_pos (by omega) hW
  have hD0 : (0 : ℝ) ≤ D := by linarith
  have hη := hz.im_pos hN
  have hη' := hz'.im_pos hN
  have hS := shortRingProfile_stochasticSymm hb0 hb (by omega : 3 ≤ m) hW
  have hm1 := norm_semicircleM_lt_one hη.ne'
  have hm1' := norm_semicircleM_lt_one hη'.ne'
  have hmc' : ‖conj (semicircleM z')‖ < 1 := by rwa [Complex.norm_conj]
  obtain ⟨hF1, -, hF3, -⟩ := lemmaK_height_facts hN hz
  obtain ⟨hF1', -, hF3', -⟩ := lemmaK_height_facts hN hz'
  obtain ⟨hKA, -, -, hK8, hK4, -, -⟩ := lemmaKConst_facts hb0 hb hκ hC₀ hD0
  have hC1 := lemmaKC1_ge_one hb0 hb κ C₀ D
  have hp : 1 ≤ (C₀ + 1) ^ (1 + D / 2) := Real.one_le_rpow (by linarith) (by linarith)
  have hcm := (lemmaK_imLower_bounds hκ hC₀).1
  have hht : 0 < min (vsHeight z t) (vsHeight z' t) :=
    lt_min (lemmaK_vsHeight_pos hη ht1) (lemmaK_vsHeight_pos hη' ht1)
  have hhtC : min (vsHeight z t) (vsHeight z' t) ≤ C₀ + 1 :=
    (min_le_left _ _).trans (hF1 t ht0 ht1).2
  have hh0 : 0 < min (vsHeight z 0) (vsHeight z' 0) := lt_min (by linarith) (by linarith)
  have hh0C : min (vsHeight z 0) (vsHeight z' 0) ≤ C₀ + 1 :=
    (min_le_left _ _).trans (hF1 0 le_rfl zero_le_one).2
  have h1C : (1 : ℝ) ≤ C₀ + 1 := by linarith
  refine ⟨fun x y => ?_, fun x y => ?_, fun x y => ?_, fun x y =>
    (vsKernel_theta_core hS hη ht0 ht1 ht0 ht1).2.1 x y⟩
  · have hΥ := polynomialControl_pos hN hW D hht x y
    rcases le_total t (1 / 4) with hA | hB
    · exact ((lemmaK_partA hb0 hb hm hW hC₀ hD0 hm1 hmc' ht0 hA x y).2 _ hht hhtC).trans
        (mul_le_mul_of_nonneg_right hKA hΥ.le)
    · refine ((lemmaK_partB hb0 hb hδ₀ hκ hC₀ hD hm hW hz hz' hB ht1).1 x y).trans ?_
      exact mul_le_mul_of_nonneg_right (by linarith) hΥ.le
  · have hΥ := polynomialControl_pos hN hW D hh0 x y
    rcases le_total t (1 / 4) with hA | hB
    · exact ((lemmaK_partA hb0 hb hm hW hC₀ hD0 hm1 hm1' ht0 hA x y).2 _ hh0 hh0C).trans
        (mul_le_mul_of_nonneg_right hKA hΥ.le)
    · refine ((lemmaK_partB hb0 hb hδ₀ hκ hC₀ hD hm hW hz hz' hB ht1).2.1 x y).trans ?_
      have hU := lemmaK_ups_one_le hN hW hD0 hC₀ hh0 hh0C x y
      calc 4 * lemmaKC1 b hb0 hb κ C₀ D * polynomialControl (m * W) W D 1 x y
          ≤ 4 * lemmaKC1 b hb0 hb κ C₀ D *
              ((C₀ + 1) ^ (1 + D / 2) *
                polynomialControl (m * W) W D (min (vsHeight z 0) (vsHeight z' 0)) x y) :=
            mul_le_mul_of_nonneg_left hU (by linarith)
        _ = 4 * lemmaKC1 b hb0 hb κ C₀ D * (C₀ + 1) ^ (1 + D / 2) *
              polynomialControl (m * W) W D (min (vsHeight z 0) (vsHeight z' 0)) x y := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hK4 hΥ.le
  · have hΥ := polynomialControl_pos hN hW D one_pos x y
    rcases le_total t (1 / 4) with hA | hB
    · exact ((lemmaK_partA hb0 hb hm hW hC₀ hD0 hm1 hm1' ht0 hA x y).2 _ one_pos h1C).trans
        (mul_le_mul_of_nonneg_right hKA hΥ.le)
    · refine ((lemmaK_partB hb0 hb hδ₀ hκ hC₀ hD hm hW hz hz' hB ht1).2.1 x y).trans ?_
      exact mul_le_mul_of_nonneg_right (by linarith) hΥ.le

/-!
## (K3)
-/

private theorem lemmaK_K3_core {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {δ₀ κ C₀ D : ℝ}
    (hδ₀ : 0 < δ₀) (hκ : 0 < κ) (hC₀ : 1 ≤ C₀) (hD : 6 ≤ D) {m W : ℕ} (hm : 4 ≤ m)
    (hW : 0 < W) {z z' : ℂ} (hz : BulkDomain (m * W) δ₀ κ C₀ z)
    (hz' : BulkDomain (m * W) δ₀ κ C₀ z') {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (a x : Fin (m * W)) :
    ‖vsKernel (shortRingProfile b m W) (semicircleM z) (conj (semicircleM z')) t a x -
        (1 / ((m * W : ℕ) : ℂ)) *
          ∑ c, vsKernel (shortRingProfile b m W) (semicircleM z) (conj (semicircleM z')) t a c‖
      ≤ lemmaKConst b hb0 hb κ C₀ D * ((m * W : ℕ) : ℝ) / (W : ℝ) ^ 2 := by
  have hN : 0 < m * W := Nat.mul_pos (by omega) hW
  have hD0 : (0 : ℝ) ≤ D := by linarith
  have hη := hz.im_pos hN
  have hη' := hz'.im_pos hN
  have hm1 := norm_semicircleM_lt_one hη.ne'
  have hmc' : ‖conj (semicircleM z')‖ < 1 := by
    rw [Complex.norm_conj]; exact norm_semicircleM_lt_one hη'.ne'
  obtain ⟨-, -, hK83, hK8, -, -, -⟩ := lemmaKConst_facts hb0 hb hκ hC₀ hD0
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hNr : (0 : ℝ) < ((m * W : ℕ) : ℝ) := by exact_mod_cast hN
  have hWN : (W : ℝ) ≤ ((m * W : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_mul_of_pos_left W (by omega : 0 < m)
  have hC1 := lemmaKC1_ge_one hb0 hb κ C₀ D
  have hNW : 0 ≤ ((m * W : ℕ) : ℝ) / (W : ℝ) ^ 2 := by positivity
  rcases le_total t (1 / 4) with hA | hB
  · set A := vsKernel (shortRingProfile b m W) (semicircleM z) (conj (semicircleM z')) t
    have hent : ∀ c, ‖A a c‖ ≤ 4 / (3 * W) := fun c =>
      (lemmaK_partA hb0 hb hm hW hC₀ hD0 hm1 hmc' ht0 hA a c).1
    have hmean : ‖(1 / ((m * W : ℕ) : ℂ)) * ∑ c, A a c‖ ≤ 4 / (3 * W) := by
      rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
      have hs : ‖∑ c, A a c‖ ≤ ((m * W : ℕ) : ℝ) * (4 / (3 * W)) := by
        refine (norm_sum_le _ _).trans ?_
        refine (Finset.sum_le_sum fun c _ => hent c).trans ?_
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      calc 1 / ((m * W : ℕ) : ℝ) * ‖∑ c, A a c‖
          ≤ 1 / ((m * W : ℕ) : ℝ) * (((m * W : ℕ) : ℝ) * (4 / (3 * W))) :=
            mul_le_mul_of_nonneg_left hs (by positivity)
        _ = 4 / (3 * W) := by field_simp
    have h83 : 8 / (3 * (W : ℝ)) ≤ 8 / 3 * (((m * W : ℕ) : ℝ) / (W : ℝ) ^ 2) := by
      rw [div_le_iff₀ (by positivity)]
      have : 8 / 3 * (((m * W : ℕ) : ℝ) / (W : ℝ) ^ 2) * (3 * W) =
          8 * (((m * W : ℕ) : ℝ) / W) := by field_simp
      rw [this]
      have : (1 : ℝ) ≤ ((m * W : ℕ) : ℝ) / W := by rw [le_div_iff₀ hWr]; linarith
      linarith
    calc ‖A a x - (1 / ((m * W : ℕ) : ℂ)) * ∑ c, A a c‖
        ≤ ‖A a x‖ + ‖(1 / ((m * W : ℕ) : ℂ)) * ∑ c, A a c‖ := norm_sub_le _ _
      _ ≤ 4 / (3 * W) + 4 / (3 * W) := add_le_add (hent x) hmean
      _ = 8 / (3 * (W : ℝ)) := by ring
      _ ≤ 8 / 3 * (((m * W : ℕ) : ℝ) / (W : ℝ) ^ 2) := h83
      _ ≤ lemmaKConst b hb0 hb κ C₀ D * (((m * W : ℕ) : ℝ) / (W : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hK83 hNW
      _ = _ := by ring
  · refine ((lemmaK_partB hb0 hb hδ₀ hκ hC₀ hD hm hW hz hz' hB ht1).2.2.2 a x).trans ?_
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (by linarith) hNW

/-- Under the hypotheses of `lemmaK_K1`,
for all sites:
`|A_t(z, z̄')(a,x) - N⁻¹ Σ_c A_t(z, z̄')(a,c)| ≤ C_K N/W²` (row mean exact, all
`t ∈ [0,1]`); the row sum is `Σ_c A_t(z, z̄')(a,c) = μμ'/(1 - tμμ')`, `μμ' = m conj(m')`; and for
the single trajectory (`T̂_t = A_t(z, z̄)`):
`|T̂_t(a,x) - Im m/(N η_t)| ≤ C_K N/W²`.
-/
theorem lemmaK_K3 {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {δ₀ κ C₀ D : ℝ} (hδ₀ : 0 < δ₀)
    (hκ : 0 < κ) (hC₀ : 1 ≤ C₀) (hD : 6 ≤ D) {m W : ℕ} (hm : 4 ≤ m) (hW : 0 < W) {z z' : ℂ}
    (hz : BulkDomain (m * W) δ₀ κ C₀ z) (hz' : BulkDomain (m * W) δ₀ κ C₀ z') {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (a x : Fin (m * W)) :
    ‖vsKernel (shortRingProfile b m W) (semicircleM z) (conj (semicircleM z')) t a x -
        (1 / ((m * W : ℕ) : ℂ)) *
          ∑ c, vsKernel (shortRingProfile b m W) (semicircleM z) (conj (semicircleM z')) t a c‖
      ≤ lemmaKConst b hb0 hb κ C₀ D * ((m * W : ℕ) : ℝ) / (W : ℝ) ^ 2 ∧
    ∑ c, vsKernel (shortRingProfile b m W) (semicircleM z) (conj (semicircleM z')) t a c =
      (semicircleM z * conj (semicircleM z')) /
        (1 - (t : ℂ) * (semicircleM z * conj (semicircleM z'))) ∧
    ‖vsKernel (shortRingProfile b m W) (semicircleM z) (conj (semicircleM z)) t a x -
        (((semicircleM z).im / (((m * W : ℕ) : ℝ) * vsHeight z t) : ℝ) : ℂ)‖
      ≤ lemmaKConst b hb0 hb κ C₀ D * ((m * W : ℕ) : ℝ) / (W : ℝ) ^ 2 := by
  have hN : 0 < m * W := Nat.mul_pos (by omega) hW
  have hη := hz.im_pos hN
  have hη' := hz'.im_pos hN
  have hS := shortRingProfile_stochasticSymm hb0 hb (by omega : 3 ≤ m) hW
  have hm1 := norm_semicircleM_lt_one hη.ne'
  have hmc' : ‖conj (semicircleM z')‖ < 1 := by
    rw [Complex.norm_conj]; exact norm_semicircleM_lt_one hη'.ne'
  refine ⟨lemmaK_K3_core hb0 hb hδ₀ hκ hC₀ hD hm hW hz hz' ht0 ht1 a x,
    vsKernel_rowSum hS (norm_smul_lt_one hm1 hmc' ht0 ht1) a, ?_⟩
  have h := lemmaK_K3_core hb0 hb hδ₀ hκ hC₀ hD hm hW hz hz ht0 ht1 a x
  rw [(vsKernel_theta_core hS hη ht0 ht1 ht0 ht1).2.2.1 a] at h
  have hNr : ((m * W : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hht := lemmaK_vsHeight_pos hη ht1
  have he : (1 / ((m * W : ℕ) : ℂ)) * (((semicircleM z).im / vsHeight z t : ℝ) : ℂ) =
      (((semicircleM z).im / (((m * W : ℕ) : ℝ) * vsHeight z t) : ℝ) : ℂ) := by
    rw [show (1 / ((m * W : ℕ) : ℂ)) = ((1 / ((m * W : ℕ) : ℝ) : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_mul]
    congr 1
    field_simp
  rwa [he] at h

/-!
## (K2)
-/

/-- Under the
hypotheses of `lemmaK_K1`, if `η_t ≥ (W/N)²` or `t ≤ 1/4` (`η_t = min (η_t z) (η_t z')`), then
for all sites `|A_t(z, z̄')(a,x) - A_t(z, z̄')(a,y)| ≤ C_K ((d(x,y)+W) ∧ ℓ_t)/ℓ_t ·
(Υ_{η_t}(a,x) + Υ_{η_t}(a,y))`, `ℓ_t = localizationLength N W η_t`.
-/
theorem lemmaK_K2 {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {δ₀ κ C₀ D : ℝ} (hδ₀ : 0 < δ₀)
    (hκ : 0 < κ) (hC₀ : 1 ≤ C₀) (hD : 6 ≤ D) {m W : ℕ} (hm : 4 ≤ m) (hW : 0 < W) {z z' : ℂ}
    (hz : BulkDomain (m * W) δ₀ κ C₀ z) (hz' : BulkDomain (m * W) δ₀ κ C₀ z') {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hthr : ((W : ℝ) / ((m * W : ℕ) : ℝ)) ^ 2 ≤ min (vsHeight z t) (vsHeight z' t) ∨ t ≤ 1 / 4)
    (a x y : Fin (m * W)) :
    ‖vsKernel (shortRingProfile b m W) (semicircleM z) (conj (semicircleM z')) t a x -
        vsKernel (shortRingProfile b m W) (semicircleM z) (conj (semicircleM z')) t a y‖ ≤
      lemmaKConst b hb0 hb κ C₀ D *
        (min ((ErdosRiabov.cyclicDistance (m * W) x y : ℝ) + W)
            (ErdosRiabov.localizationLength (m * W) W (min (vsHeight z t) (vsHeight z' t))) /
          ErdosRiabov.localizationLength (m * W) W (min (vsHeight z t) (vsHeight z' t))) *
        (polynomialControl (m * W) W D (min (vsHeight z t) (vsHeight z' t)) a x +
          polynomialControl (m * W) W D (min (vsHeight z t) (vsHeight z' t)) a y) := by
  have hN : 0 < m * W := Nat.mul_pos (by omega) hW
  have hD0 : (0 : ℝ) ≤ D := by linarith
  have hη := hz.im_pos hN
  have hη' := hz'.im_pos hN
  have hm1 := norm_semicircleM_lt_one hη.ne'
  have hmc' : ‖conj (semicircleM z')‖ < 1 := by
    rw [Complex.norm_conj]; exact norm_semicircleM_lt_one hη'.ne'
  obtain ⟨hF1, hF2, -, -⟩ := lemmaK_height_facts hN hz
  obtain ⟨hF1', hF2', -, -⟩ := lemmaK_height_facts hN hz'
  obtain ⟨-, hKA4, -, hK8, -, -, hK0⟩ := lemmaKConst_facts hb0 hb hκ hC₀ hD0
  obtain ⟨hcm0, hcm1⟩ := lemmaK_imLower_bounds hκ hC₀
  have hht : 0 < min (vsHeight z t) (vsHeight z' t) :=
    lt_min (lemmaK_vsHeight_pos hη ht1) (lemmaK_vsHeight_pos hη' ht1)
  have hhtC : min (vsHeight z t) (vsHeight z' t) ≤ C₀ + 1 :=
    (min_le_left _ _).trans (hF1 t ht0 ht1).2
  set h := min (vsHeight z t) (vsHeight z' t) with hhdef
  set F := min ((ErdosRiabov.cyclicDistance (m * W) x y : ℝ) + W)
      (ErdosRiabov.localizationLength (m * W) W h) /
    ErdosRiabov.localizationLength (m * W) W h with hFdef
  have hl := loc_pos hN hW hht
  have hF0 : 0 ≤ F := div_nonneg (le_min (by positivity) hl.le) hl.le
  have hU1 := polynomialControl_pos hN hW D hht a x
  have hU2 := polynomialControl_pos hN hW D hht a y
  by_cases hA : t ≤ 1 / 4
  · have he : 3 * imLower κ C₀ / 4 ≤ h := le_min (hF2 t hA) (hF2' t hA)
    have hFlo : 3 * imLower κ C₀ / 4 ≤ F :=
      lemmaK_regFactor_lower hN hW (by positivity) (by linarith) he (Nat.cast_nonneg _)
    have hpa := lemmaK_partA hb0 hb hm hW hC₀ hD0 hm1 hmc' ht0 hA
    have h1 := (hpa a x).2 h hht hhtC
    have h2 := (hpa a y).2 h hht hhtC
    have hCA : 0 ≤ lemmaKPartAConst C₀ D := (zero_le_one.trans (lemmaKPartAConst_ge_one hC₀ hD0))
    have hsplit : lemmaKPartAConst C₀ D =
        4 * lemmaKPartAConst C₀ D / (3 * imLower κ C₀) * (3 * imLower κ C₀ / 4) := by
      field_simp
    calc _ ≤ ‖vsKernel (shortRingProfile b m W) (semicircleM z) (conj (semicircleM z')) t a x‖ +
          ‖vsKernel (shortRingProfile b m W) (semicircleM z) (conj (semicircleM z')) t a y‖ :=
          norm_sub_le _ _
      _ ≤ lemmaKPartAConst C₀ D * polynomialControl (m * W) W D h a x +
          lemmaKPartAConst C₀ D * polynomialControl (m * W) W D h a y := add_le_add h1 h2
      _ = 4 * lemmaKPartAConst C₀ D / (3 * imLower κ C₀) * (3 * imLower κ C₀ / 4) *
          (polynomialControl (m * W) W D h a x + polynomialControl (m * W) W D h a y) := by
          rw [← hsplit]; ring
      _ ≤ lemmaKConst b hb0 hb κ C₀ D * F *
          (polynomialControl (m * W) W D h a x + polynomialControl (m * W) W D h a y) :=
          mul_le_mul (mul_le_mul hKA4 hFlo (by linarith) hK0.le) le_rfl
            (by linarith) (mul_nonneg hK0.le hF0)
  · have hB : 1 / 4 ≤ t := by linarith
    have hthr' : ((W : ℝ) / ((m * W : ℕ) : ℝ)) ^ 2 ≤ h := hthr.resolve_right hA
    refine ((lemmaK_partB hb0 hb hδ₀ hκ hC₀ hD hm hW hz hz' hB ht1).2.2.1 hthr' a x y).trans ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_right hK8 hF0) le_rfl (by linarith)
      (mul_nonneg hK0.le hF0)

/-!
## (K5)
-/

/-- Under the hypotheses of
`lemmaK_K1` (one point `z`), with `q = lemmaKParams …`, `N = mW`:
`Υ` is an
`AdmissibleControl q`; all VS heights satisfy `N^{-1+δ₀} ≤ η_t(z) ≤ C₀+1` (`t ∈ [0,1]`); every
height in `[N^{-1+δ₀}, C₀+1]` is a `ControlHeight q N` (ceiling `C₀'' = 2(C₀+1)`); exact
monotonicity `Υ_{h'} ≤ Υ_h` and reverse comparison `Υ_h ≤ (h'/h)^{1+D/2} Υ_{h'}` for
`0 < h ≤ h'`; and the polynomial-control clauses (ii)–(v) (constant `C₁''`, floor `N^{-2D''}`) at all heights
`N^{-1+δ₀} ≤ h₁ ≤ h₂ ≤ C₀+1`.
-/
theorem lemmaK_K5 {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {δ₀ κ C₀ D : ℝ} (hδ₀ : 0 < δ₀)
    (hκ : 0 < κ) (hC₀ : 1 ≤ C₀) (hD : 6 ≤ D) {m W : ℕ} (hm : 4 ≤ m) (hW : 0 < W) {z : ℂ}
    (hz : BulkDomain (m * W) δ₀ κ C₀ z) :
    ErdosRiabov.AdmissibleControl (lemmaKParams b hb0 hb δ₀ κ C₀ D hδ₀ hκ hC₀ hD) (m * W) W
      (shortRingProfile b m W) (polynomialControl (m * W) W D) ∧
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ((m * W : ℕ) : ℝ) ^ (-1 + δ₀) ≤ vsHeight z t ∧ vsHeight z t ≤ C₀ + 1) ∧
    (∀ h : ℝ, ((m * W : ℕ) : ℝ) ^ (-1 + δ₀) ≤ h → h ≤ C₀ + 1 →
      ErdosRiabov.ControlHeight (lemmaKParams b hb0 hb δ₀ κ C₀ D hδ₀ hκ hC₀ hD) (m * W) h) ∧
    (∀ h h' : ℝ, 0 < h → h ≤ h' → ∀ x y,
      polynomialControl (m * W) W D h' x y ≤ polynomialControl (m * W) W D h x y ∧
      polynomialControl (m * W) W D h x y ≤
        (h' / h) ^ (1 + D / 2) * polynomialControl (m * W) W D h' x y) ∧
    (∀ h : ℝ, ((m * W : ℕ) : ℝ) ^ (-1 + δ₀) ≤ h → h ≤ C₀ + 1 →
      (∀ x y, polynomialControl (m * W) W D h x y ≤
        lemmaKC1 b hb0 hb κ C₀ D / (ErdosRiabov.localizationLength (m * W) W h * h)) ∧
      (∀ x, ∑ a, polynomialControl (m * W) W D h x a ≤ lemmaKC1 b hb0 hb κ C₀ D / h) ∧
      (∀ x y, Real.rpow ((m * W : ℕ) : ℝ) (-2 * lemmaKDPrime C₀ D) ≤
        polynomialControl (m * W) W D h x y) ∧
      (h ≤ ((W : ℝ) / ((m * W : ℕ) : ℝ)) ^ 2 → ∀ x y,
        (1 / lemmaKC1 b hb0 hb κ C₀ D) * (1 / (((m * W : ℕ) : ℝ) * h)) ≤
          polynomialControl (m * W) W D h x y ∧
        polynomialControl (m * W) W D h x y ≤
          lemmaKC1 b hb0 hb κ C₀ D * (1 / (((m * W : ℕ) : ℝ) * h)))) ∧
    (∀ h₁ h₂ : ℝ, ((m * W : ℕ) : ℝ) ^ (-1 + δ₀) ≤ h₁ → h₁ ≤ h₂ → h₂ ≤ C₀ + 1 →
      (∀ x y, polynomialControl (m * W) W D h₂ x y ≤
        lemmaKC1 b hb0 hb κ C₀ D * polynomialControl (m * W) W D h₁ x y) ∧
      (∀ x y,
        (∀ a, polynomialControl (m * W) W D h₂ x a * polynomialControl (m * W) W D h₁ a y ≤
          lemmaKC1 b hb0 hb κ C₀ D / (ErdosRiabov.localizationLength (m * W) W h₂ * h₂) *
            polynomialControl (m * W) W D h₁ x y) ∧
        (∑ a, Real.sqrt (polynomialControl (m * W) W D h₂ x a *
            polynomialControl (m * W) W D h₁ a y)) ≤
          lemmaKC1 b hb0 hb κ C₀ D / h₂ *
            Real.sqrt (ErdosRiabov.localizationLength (m * W) W h₂ * h₂ *
              polynomialControl (m * W) W D h₁ x y)) ∧
      (∀ hi, (hi = h₁ ∨ hi = h₂) → ∀ x y,
        (∑ a,
          (min ((ErdosRiabov.cyclicDistance (m * W) a x : ℝ) + W)
              (ErdosRiabov.localizationLength (m * W) W h₁) /
            ErdosRiabov.localizationLength (m * W) W h₁) *
            Real.sqrt (polynomialControl (m * W) W D h₂ x a *
              polynomialControl (m * W) W D hi a y)) ≤
          lemmaKC1 b hb0 hb κ C₀ D / h₂ *
            (ErdosRiabov.localizationLength (m * W) W h₂ /
              ErdosRiabov.localizationLength (m * W) W h₁) *
            Real.sqrt
              ((ErdosRiabov.localizationLength (m * W) W h₂ * h₂) /
                (ErdosRiabov.localizationLength (m * W) W hi * hi)) *
            Real.sqrt
              (ErdosRiabov.localizationLength (m * W) W h₁ * h₁ *
                polynomialControl (m * W) W D h₁ x y))) := by
  have hN : 0 < m * W := Nat.mul_pos (by omega) hW
  have hD0 : (0 : ℝ) ≤ D := by linarith
  have hadm := cf1_vs hb0 hb hδ₀ hκ hC₀ hD hm hW
  have hctl : ∀ h : ℝ, ((m * W : ℕ) : ℝ) ^ (-1 + δ₀) ≤ h → h ≤ C₀ + 1 →
      ErdosRiabov.ControlHeight (lemmaKParams b hb0 hb δ₀ κ C₀ D hδ₀ hκ hC₀ hD) (m * W) h :=
    fun h h1 h2 => ⟨h1, show h ≤ lemmaKCeiling C₀ by unfold lemmaKCeiling; linarith⟩
  refine ⟨hadm, fun t ht0 ht1 => (lemmaK_height_facts hN hz).1 t ht0 ht1, hctl,
    fun h h' hh hle x y => ⟨polynomialControl_mono hN hW hD0 hh hle x y,
      polynomialControl_reverse hN hW hD0 hh hle x y⟩,
    fun h h1 h2 => hadm.clause2 h (hctl h h1 h2), fun h₁ h₂ h1 h12 h2 => ?_⟩
  have c1 := hctl h₁ h1 (h12.trans h2)
  have c2 := hctl h₂ (h1.trans h12) h2
  exact ⟨hadm.clause3 h₁ h₂ c1 c2 h12, hadm.clause4 h₁ h₂ c1 c2 h12,
    hadm.clause5 h₁ h₂ c1 c2 h12⟩

/-!
## (K6)
-/

private theorem lemmaK_one_add_smul_entry {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) {s t : ℝ}
    (hst : s ≤ t) (a x : Fin n) :
    ‖(1 + ((t : ℂ) - s) • A) a x‖ ≤ (if a = x then 1 else 0) + (t - s) * ‖A a x‖ := by
  have hts : (t : ℂ) - s = ((t - s : ℝ) : ℂ) := by push_cast; ring
  rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hts]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  refine add_le_add_left (le_of_eq ?_) _
  rw [Matrix.one_apply]
  split_ifs <;> simp

private theorem lemmaK_time_factor {c K η U d : ℝ} (hc : 0 < c) (hdη : d * c ≤ η) (hK : 0 ≤ K)
    (hU : 0 ≤ U) : d * (K * U) ≤ K / c * η * U := by
  have h1 : d * (K * U) = d * c * (K / c * U) := by field_simp
  have h2 : 0 ≤ K / c * U := mul_nonneg (div_nonneg hK hc.le) hU
  rw [h1]
  calc d * c * (K / c * U) ≤ η * (K / c * U) := mul_le_mul_of_nonneg_right hdη h2
    _ = K / c * η * U := by ring

/-- Under the
hypotheses of `lemmaK_K1`, for `0 ≤ s ≤ t ≤ 1`, with `P_{s,t} = vsPropagator` (closed form
`(1-sY)(1-tY)⁻¹`): for both the Θ-type pair `(z, z̄')` and the Ξ-type pair `(z, z')`,
`P_{s,t} = I + (t-s)A_t`, `A_t = P_{s,t}A_s` and `∂_t A_t = A_t²` (entrywise); entrywise
`|P_{s,t}(a,x)| ≤ δ_{ax} + (C_K/c_m) η_s Υ_{η_t}(a,x)` (Θ-type) and
`|P_{s,t}(a,x)| ≤ δ_{ax} + (C_K/c_m) η_s Υ_{η₀^Ξ}(a,x)` (Ξ-type), `η_s = min (η_s z) (η_s z')`;
and the saturated propagator `P̂_{s,t} = P_{s,t}(z, z̄)` is real and `≥ 0` entrywise.
-/
theorem lemmaK_K6 {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {δ₀ κ C₀ D : ℝ} (hδ₀ : 0 < δ₀)
    (hκ : 0 < κ) (hC₀ : 1 ≤ C₀) (hD : 6 ≤ D) {m W : ℕ} (hm : 4 ≤ m) (hW : 0 < W) {z z' : ℂ}
    (hz : BulkDomain (m * W) δ₀ κ C₀ z) (hz' : BulkDomain (m * W) δ₀ κ C₀ z') {s t : ℝ}
    (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t ≤ 1) :
    vsPropagator (shortRingProfile b m W) (semicircleM z) (conj (semicircleM z')) s t =
      1 + ((t : ℂ) - s) •
        vsKernel (shortRingProfile b m W) (semicircleM z) (conj (semicircleM z')) t ∧
    vsKernel (shortRingProfile b m W) (semicircleM z) (conj (semicircleM z')) t =
      vsPropagator (shortRingProfile b m W) (semicircleM z) (conj (semicircleM z')) s t *
        vsKernel (shortRingProfile b m W) (semicircleM z) (conj (semicircleM z')) s ∧
    (∀ x y, HasDerivAt
      (fun r : ℝ => vsKernel (shortRingProfile b m W) (semicircleM z) (conj (semicircleM z')) r x y)
      ((vsKernel (shortRingProfile b m W) (semicircleM z) (conj (semicircleM z')) t *
        vsKernel (shortRingProfile b m W) (semicircleM z) (conj (semicircleM z')) t) x y) t) ∧
    (∀ a x,
      ‖vsPropagator (shortRingProfile b m W) (semicircleM z) (conj (semicircleM z')) s t a x‖ ≤
        (if a = x then 1 else 0) +
          lemmaKConst b hb0 hb κ C₀ D / imLower κ C₀ * min (vsHeight z s) (vsHeight z' s) *
            polynomialControl (m * W) W D (min (vsHeight z t) (vsHeight z' t)) a x) ∧
    vsPropagator (shortRingProfile b m W) (semicircleM z) (semicircleM z') s t =
      1 + ((t : ℂ) - s) • vsKernel (shortRingProfile b m W) (semicircleM z) (semicircleM z') t ∧
    vsKernel (shortRingProfile b m W) (semicircleM z) (semicircleM z') t =
      vsPropagator (shortRingProfile b m W) (semicircleM z) (semicircleM z') s t *
        vsKernel (shortRingProfile b m W) (semicircleM z) (semicircleM z') s ∧
    (∀ x y, HasDerivAt
      (fun r : ℝ => vsKernel (shortRingProfile b m W) (semicircleM z) (semicircleM z') r x y)
      ((vsKernel (shortRingProfile b m W) (semicircleM z) (semicircleM z') t *
        vsKernel (shortRingProfile b m W) (semicircleM z) (semicircleM z') t) x y) t) ∧
    (∀ a x,
      ‖vsPropagator (shortRingProfile b m W) (semicircleM z) (semicircleM z') s t a x‖ ≤
        (if a = x then 1 else 0) +
          lemmaKConst b hb0 hb κ C₀ D / imLower κ C₀ * min (vsHeight z s) (vsHeight z' s) *
            polynomialControl (m * W) W D (min (vsHeight z 0) (vsHeight z' 0)) a x) ∧
    (∀ a x,
      (vsPropagator (shortRingProfile b m W) (semicircleM z) (conj (semicircleM z)) s t a x).im
        = 0 ∧
      0 ≤ (vsPropagator (shortRingProfile b m W) (semicircleM z) (conj (semicircleM z)) s t
        a x).re) := by
  have hN : 0 < m * W := Nat.mul_pos (by omega) hW
  have hD0 : (0 : ℝ) ≤ D := by linarith
  have ht0 : 0 ≤ t := hs0.trans hst
  have hs1 : s ≤ 1 := hst.trans ht1
  have hη := hz.im_pos hN
  have hη' := hz'.im_pos hN
  have hS := shortRingProfile_stochasticSymm hb0 hb (by omega : 3 ≤ m) hW
  have hm1 := norm_semicircleM_lt_one hη.ne'
  have hm1' := norm_semicircleM_lt_one hη'.ne'
  have hmc' : ‖conj (semicircleM z')‖ < 1 := by rwa [Complex.norm_conj]
  have hmc : ‖conj (semicircleM z)‖ < 1 := by rwa [Complex.norm_conj]
  obtain ⟨-, -, -, hF4⟩ := lemmaK_height_facts hN hz
  obtain ⟨-, -, -, hF4'⟩ := lemmaK_height_facts hN hz'
  obtain ⟨-, -, -, -, -, -, hK0⟩ := lemmaKConst_facts hb0 hb hκ hC₀ hD0
  have hcm := (lemmaK_imLower_bounds hκ hC₀).1
  have hdη : (t - s) * imLower κ C₀ ≤ min (vsHeight z s) (vsHeight z' s) :=
    le_min (hF4 s t hst ht1) (hF4' s t hst ht1)
  obtain ⟨hK1T, hK1X, -, -⟩ := lemmaK_K1 hb0 hb hδ₀ hκ hC₀ hD hm hW hz hz' ht0 ht1
  have algT := vsKernel_algebra hS hm1 hmc' hs0 hs1 ht0 ht1
  have algX := vsKernel_algebra hS hm1 hm1' hs0 hs1 ht0 ht1
  have algS := vsKernel_algebra hS hm1 hmc hs0 hs1 ht0 ht1
  have hht : 0 < min (vsHeight z t) (vsHeight z' t) :=
    lt_min (lemmaK_vsHeight_pos hη ht1) (lemmaK_vsHeight_pos hη' ht1)
  have hh0 : 0 < min (vsHeight z 0) (vsHeight z' 0) :=
    lt_min (lemmaK_vsHeight_pos hη zero_le_one) (lemmaK_vsHeight_pos hη' zero_le_one)
  refine ⟨algT.2.1, algT.2.2.2.1, algT.2.2.2.2.2.1, fun a x => ?_, algX.2.1, algX.2.2.2.1,
    algX.2.2.2.2.2.1, fun a x => ?_, fun a x => ?_⟩
  · rw [algT.2.1]
    refine (lemmaK_one_add_smul_entry _ hst a x).trans (add_le_add le_rfl ?_)
    exact (mul_le_mul_of_nonneg_left (hK1T a x) (by linarith)).trans
      (lemmaK_time_factor hcm hdη hK0.le (polynomialControl_pos hN hW D hht a x).le)
  · rw [algX.2.1]
    refine (lemmaK_one_add_smul_entry _ hst a x).trans (add_le_add le_rfl ?_)
    exact (mul_le_mul_of_nonneg_left (hK1X a x) (by linarith)).trans
      (lemmaK_time_factor hcm hdη hK0.le (polynomialControl_pos hN hW D hh0 a x).le)
  · obtain ⟨h1, h2⟩ := (vsKernel_theta_core hS hη hs0 hs1 ht0 ht1).2.1 a x
    have hts : (t : ℂ) - s = ((t - s : ℝ) : ℂ) := by push_cast; ring
    rw [algS.2.1, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hts, Complex.add_im,
      Complex.add_re, Complex.im_ofReal_mul, Complex.re_ofReal_mul, h1, mul_zero, add_zero,
      Matrix.one_apply]
    have h3 : 0 ≤ (t - s) *
        (vsKernel (shortRingProfile b m W) (semicircleM z) (conj (semicircleM z)) t a x).re :=
      mul_nonneg (by linarith) h2
    split_ifs
    · simp only [Complex.one_im, Complex.one_re, true_and]
      linarith
    · simp only [Complex.zero_im, Complex.zero_re, true_and]
      linarith

/-!
## (K7)
-/

private theorem lemmaK_rowSum_one_add {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) {c : ℂ}
    (hc : ‖c‖ ≤ 1) (a : Fin n) :
    ∑ x, ‖(1 + c • A) a x‖ ≤ 1 + ∑ x, ‖A a x‖ := by
  have hone : ∑ x, ‖(1 : Matrix (Fin n) (Fin n) ℂ) a x‖ = 1 := by
    have h : ∀ x, ‖(1 : Matrix (Fin n) (Fin n) ℂ) a x‖ = if a = x then 1 else 0 := fun x => by
      rw [Matrix.one_apply]
      split_ifs <;> simp
    simp_rw [h]
    rw [Finset.sum_ite_eq]
    simp
  calc ∑ x, ‖(1 + c • A) a x‖ ≤ ∑ x, (‖(1 : Matrix (Fin n) (Fin n) ℂ) a x‖ + ‖A a x‖) := by
        refine Finset.sum_le_sum fun x _ => ?_
        rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) hc
    _ = 1 + ∑ x, ‖A a x‖ := by rw [Finset.sum_add_distrib, hone]

/-- Under the hypotheses of
`lemmaK_K1`, for `0 ≤ s ≤ t ≤ 1` and every site `a`: Θ-type
`Σ_x |A_t(z, z̄')(a,x)| ≤ C_K C₁''/η_t`; Ξ-type `(1 - tY)⁻¹ = I + tA_t(z, z')`,
`Σ_x |(I + tA_t(z, z'))(a,x)| ≤ 1 + C_K C₁''/c_m` and `Σ_x |P_{s,t}(z, z')(a,x)| ≤
1 + C_K C₁''/c_m`.
-/
theorem lemmaK_K7 {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {δ₀ κ C₀ D : ℝ} (hδ₀ : 0 < δ₀)
    (hκ : 0 < κ) (hC₀ : 1 ≤ C₀) (hD : 6 ≤ D) {m W : ℕ} (hm : 4 ≤ m) (hW : 0 < W) {z z' : ℂ}
    (hz : BulkDomain (m * W) δ₀ κ C₀ z) (hz' : BulkDomain (m * W) δ₀ κ C₀ z') {s t : ℝ}
    (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t ≤ 1) (a : Fin (m * W)) :
    ∑ x, ‖vsKernel (shortRingProfile b m W) (semicircleM z) (conj (semicircleM z')) t a x‖ ≤
      lemmaKConst b hb0 hb κ C₀ D * lemmaKC1 b hb0 hb κ C₀ D /
        min (vsHeight z t) (vsHeight z' t) ∧
    (1 - (t : ℂ) • vsY (shortRingProfile b m W) (semicircleM z) (semicircleM z'))⁻¹ =
      1 + (t : ℂ) • vsKernel (shortRingProfile b m W) (semicircleM z) (semicircleM z') t ∧
    ∑ x, ‖(1 + (t : ℂ) •
        vsKernel (shortRingProfile b m W) (semicircleM z) (semicircleM z') t) a x‖ ≤
      1 + lemmaKConst b hb0 hb κ C₀ D * lemmaKC1 b hb0 hb κ C₀ D / imLower κ C₀ ∧
    ∑ x, ‖vsPropagator (shortRingProfile b m W) (semicircleM z) (semicircleM z') s t a x‖ ≤
      1 + lemmaKConst b hb0 hb κ C₀ D * lemmaKC1 b hb0 hb κ C₀ D / imLower κ C₀ := by
  have hN : 0 < m * W := Nat.mul_pos (by omega) hW
  have hD0 : (0 : ℝ) ≤ D := by linarith
  have ht0 : 0 ≤ t := hs0.trans hst
  have hη := hz.im_pos hN
  have hη' := hz'.im_pos hN
  have hS := shortRingProfile_stochasticSymm hb0 hb (by omega : 3 ≤ m) hW
  have hm1 := norm_semicircleM_lt_one hη.ne'
  have hm1' := norm_semicircleM_lt_one hη'.ne'
  have htn := norm_smul_lt_one hm1 hm1' ht0 ht1
  obtain ⟨hF1, -, hF3, -⟩ := lemmaK_height_facts hN hz
  obtain ⟨hF1', -, hF3', -⟩ := lemmaK_height_facts hN hz'
  obtain ⟨-, -, -, -, -, -, hK0⟩ := lemmaKConst_facts hb0 hb hκ hC₀ hD0
  have hC1 := lemmaKC1_ge_one hb0 hb κ C₀ D
  have hcm := (lemmaK_imLower_bounds hκ hC₀).1
  obtain ⟨hadm, -, hctl, -, hcl2, -⟩ := lemmaK_K5 hb0 hb hδ₀ hκ hC₀ hD hm hW hz
  obtain ⟨hK1T, hK1X, -, -⟩ := lemmaK_K1 hb0 hb hδ₀ hκ hC₀ hD hm hW hz hz' ht0 ht1
  have hht0 : ((m * W : ℕ) : ℝ) ^ (-1 + δ₀) ≤ min (vsHeight z t) (vsHeight z' t) :=
    le_min (hF1 t ht0 ht1).1 (hF1' t ht0 ht1).1
  have hhtC : min (vsHeight z t) (vsHeight z' t) ≤ C₀ + 1 :=
    (min_le_left _ _).trans (hF1 t ht0 ht1).2
  have hh00 : ((m * W : ℕ) : ℝ) ^ (-1 + δ₀) ≤ min (vsHeight z 0) (vsHeight z' 0) :=
    le_min (hF1 0 le_rfl zero_le_one).1 (hF1' 0 le_rfl zero_le_one).1
  have hh0C : min (vsHeight z 0) (vsHeight z' 0) ≤ C₀ + 1 :=
    (min_le_left _ _).trans (hF1 0 le_rfl zero_le_one).2
  have hh0c : imLower κ C₀ ≤ min (vsHeight z 0) (vsHeight z' 0) := le_min hF3 hF3'
  -- the Ξ row sum of `A_t`
  have hXi : ∑ x, ‖vsKernel (shortRingProfile b m W) (semicircleM z) (semicircleM z') t a x‖ ≤
      lemmaKConst b hb0 hb κ C₀ D * lemmaKC1 b hb0 hb κ C₀ D / imLower κ C₀ := by
    have hrow := (hcl2 _ hh00 hh0C).2.1 a
    calc ∑ x, ‖vsKernel (shortRingProfile b m W) (semicircleM z) (semicircleM z') t a x‖
        ≤ ∑ x, lemmaKConst b hb0 hb κ C₀ D *
            polynomialControl (m * W) W D (min (vsHeight z 0) (vsHeight z' 0)) a x :=
          Finset.sum_le_sum fun x _ => hK1X a x
      _ = lemmaKConst b hb0 hb κ C₀ D *
            ∑ x, polynomialControl (m * W) W D (min (vsHeight z 0) (vsHeight z' 0)) a x :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ lemmaKConst b hb0 hb κ C₀ D *
            (lemmaKC1 b hb0 hb κ C₀ D / min (vsHeight z 0) (vsHeight z' 0)) :=
          mul_le_mul_of_nonneg_left hrow hK0.le
      _ ≤ lemmaKConst b hb0 hb κ C₀ D * (lemmaKC1 b hb0 hb κ C₀ D / imLower κ C₀) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by linarith) hcm hh0c) hK0.le
      _ = _ := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hrow := (hcl2 _ hht0 hhtC).2.1 a
    calc ∑ x, ‖vsKernel (shortRingProfile b m W) (semicircleM z) (conj (semicircleM z')) t a x‖
        ≤ ∑ x, lemmaKConst b hb0 hb κ C₀ D *
            polynomialControl (m * W) W D (min (vsHeight z t) (vsHeight z' t)) a x :=
          Finset.sum_le_sum fun x _ => hK1T a x
      _ = lemmaKConst b hb0 hb κ C₀ D *
            ∑ x, polynomialControl (m * W) W D (min (vsHeight z t) (vsHeight z' t)) a x :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ lemmaKConst b hb0 hb κ C₀ D *
            (lemmaKC1 b hb0 hb κ C₀ D / min (vsHeight z t) (vsHeight z' t)) :=
          mul_le_mul_of_nonneg_left hrow hK0.le
      _ = _ := by ring
  · have h := vsPropagator_eq (s := 0) hS htn
    simp only [vsPropagator, Complex.ofReal_zero, zero_smul, sub_zero, Matrix.one_mul] at h
    exact h
  · refine (lemmaK_rowSum_one_add _ ?_ a).trans (by linarith)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    exact ht1
  · rw [vsPropagator_eq hS htn]
    refine (lemmaK_rowSum_one_add _ ?_ a).trans (by linarith)
    have hts : (t : ℂ) - s = ((t - s : ℝ) : ℂ) := by push_cast; ring
    rw [hts, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith

end BlockBand.Native.ErdosRiabov.LemmaK
