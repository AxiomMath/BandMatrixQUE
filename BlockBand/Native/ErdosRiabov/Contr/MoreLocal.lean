module

public import BlockBand.Native.ErdosRiabov.Contr.MoreSplit

/-!
# Local contractions: further isotropic contractions

Contractions of the same type as the averaged insertion bound, for products of isotropic and
averaged size functions. (U2)–(U7) denote the properties of the control `Υ` given by
`LemmaK.ups_U2_U8_vs`. All hold at a single time `t` for `Psi.PsiData.sIso`/`sAv` (`Υ = P.ups t`,
`ℓη = P.lEta t`,
`η = vsHeight P.z t`). Abstract forms (`*_of`) take the inputs as hypotheses; VS forms (`*_vs`)
take `hin : ContrVSInputs d P t` (built by `contrVSInputs_of`), so constants are explicit in
`VSData`. Site concatenations are hypotheses on the site vectors.
* the squared convolution (`isoQj_*`): `Σ_c s^iso_{i+1}(a,x,c)² s^iso_{j+1}(c,y,b)² ≤ C_wc/η ·
  s^iso_{i+j+1}(a,(x,y),b)²` (by (U5)).
* the isotropic insertion (`isoQuad_*`): `Σ_q s^iso_{p+1}(q,y,q) s^iso_{r+s+2}(a,u,q,v,b) ≤
  C_wc/η (ℓη)^{-1/2} s^iso_{r+p+s+1}(a,(u,y,v),b)` for `p ≥ 1` (by (U6)); pointwise in `q`:
  `≤ C₁''(ℓη)^{-3/2} s^iso` (`isoQuadConcat_*`, by (U4)).
* the sublinear bounds (`isoSublin_*`): the same sum with the factor `(ℓη)^{1/2}` of the
  `M`-bound, `≤ C_wc/η · s^iso_{r+p+s+1}(a,(u,y,v),b)` (`b = a` in the first one).
* the isotropic-averaged bound (`isoAv_*`): `Σ_q Υ(a,q) s^av_{p+1}(x',q) ≤ C_wc/η (ℓη)^{-1/2}
  s^iso_{p+1}(a,x',a)` for `p ≥ 1` (by (U6) and the symmetry of `Υ`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Contr

open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow

variable {N : ℕ}

/-!
## Abstract forms
-/

section Abstract

variable (P : PsiData N) (t : ℝ)

/-- **Isotropic square convolution (abstract form).** If `Υ = P.ups t ≥ 0`, `ℓη > 0` and
`Σ_c Υ(x,c)Υ(c,y) ≤ K Υ(x,y)` (U5), then for isotropic sites `x` (the first `i` entries of
`x : Fin (i+1)`), `y` (the first `j` entries of `y : Fin (j+1)`) and any `w` whose first `i`
entries are those of `x` and next `j` those of `y`:
`Σ_c s^iso_{i+1}(a,x,c)² s^iso_{j+1}(c,y,b)² ≤ K s^iso_{i+j+1}(a,w,b)²`. -/
theorem isoQj_of (hU : ∀ x y, 0 ≤ P.ups t x y) (hL : 0 < P.lEta t) {K : ℝ}
    (h5 : ∀ x y, ∑ c, P.ups t x c * P.ups t c y ≤ K * P.ups t x y)
    {i j : ℕ} (a b : Fin N) (x : Fin (i + 1) → Fin N) (y : Fin (j + 1) → Fin N)
    (w : Fin (i + j + 1) → Fin N)
    (hx : ∀ (n : ℕ) (hn : n < i), x ⟨n, by omega⟩ = w ⟨n, by omega⟩)
    (hy : ∀ (n : ℕ) (hn : n < j), y ⟨n, by omega⟩ = w ⟨i + n, by omega⟩) :
    ∑ c, P.sIso a c x t ^ 2 * P.sIso c b y t ^ 2 ≤ K * P.sIso a b w t ^ 2 := by
  obtain ⟨c, R, u, v, hc, hR, hq, hw⟩ := contrSplit_iso_shape P t hU hL a b x y w hx hy
  have hsq : ∀ q, P.sIso a q x t ^ 2 * P.sIso q b y t ^ 2 =
      c ^ 2 * R * (P.ups t u q * P.ups t q v) := by
    intro q
    rw [← mul_pow, hq, mul_pow, Real.sq_sqrt (mul_nonneg hR (mul_nonneg (hU _ _) (hU _ _)))]
    ring
  simp_rw [hsq]
  rw [hw, mul_pow, Real.sq_sqrt (mul_nonneg hR (hU _ _)), ← Finset.mul_sum]
  calc c ^ 2 * R * ∑ q, P.ups t u q * P.ups t q v ≤ c ^ 2 * R * (K * P.ups t u v) :=
        mul_le_mul_of_nonneg_left (h5 u v) (mul_nonneg (sq_nonneg c) hR)
    _ = K * (c ^ 2 * (R * P.ups t u v)) := by ring

/-- **Isotropic quadratic insertion (abstract form).** If `Υ = P.ups t ≥ 0`, `ℓη > 0` and the
Schwarz convolution (U6) holds with constant `K`, then for `p ≥ 1` inserted sites `y` (the first `p`
entries of `y : Fin (p+1)`), outer site vectors `zq q` (`r` sites, then `q`, then `s` sites;
last entry unused) and `w` (`r + p + s` sites: the `r` outer, the `p` inserted, the `s` outer):
`Σ_q s^iso_{p+1}(q,y,q) s^iso_{r+s+2}(a,zq q,b) ≤ K (ℓη)^{-1/2} s^iso_{r+p+s+1}(a,w,b)`. -/
theorem isoQuad_of (hU : ∀ x y, 0 ≤ P.ups t x y) (hL : 0 < P.lEta t) {K : ℝ}
    (h6 : ∀ x₁ x₂ y₁ y₂, ∑ q, Real.sqrt (P.ups t x₁ q * P.ups t x₂ q * P.ups t q y₁ *
      P.ups t q y₂) ≤ K * Real.sqrt (P.ups t x₁ y₁ * P.ups t x₂ y₂))
    {r p s : ℕ} (hp : 1 ≤ p) (a b : Fin N) (y : Fin (p + 1) → Fin N)
    (zq : Fin N → Fin (r + s + 2) → Fin N) (w : Fin (r + p + s + 1) → Fin N)
    (hzpre : ∀ (q : Fin N) (n : ℕ) (hn : n < r), zq q ⟨n, by omega⟩ = w ⟨n, by omega⟩)
    (hzmid : ∀ q, zq q ⟨r, by omega⟩ = q)
    (hzpost : ∀ (q : Fin N) (n : ℕ) (hn : n < s),
      zq q ⟨r + 1 + n, by omega⟩ = w ⟨r + p + n, by omega⟩)
    (hy : ∀ (n : ℕ) (hn : n < p), y ⟨n, by omega⟩ = w ⟨r + n, by omega⟩) :
    ∑ q, P.sIso q q y t * P.sIso a b (zq q) t ≤
      K * P.lEta t ^ (-(1 / 2 : ℝ)) * P.sIso a b w t := by
  obtain ⟨c, R, x₁, x₂, y₁, y₂, hc, hR, hq, hw⟩ :=
    contrSplit_isoIns_shape P t hU hL hp a b y zq w hzpre hzmid hzpost hy
  simp_rw [hq]
  rw [mul_assoc K, hw]
  exact localContraction_sum h6 hc hR x₁ x₂ y₁ y₂

/-- **Isotropic quadratic insertion, pointwise form (abstract form).** Under the hypotheses of
`isoQuad_of` with (U4) `Υ(x,a)Υ(a,y) ≤ K Υ(x,y)`, `K ≥ 0`, in place of (U6), for every `q`:
`s^iso_{p+1}(q,y,q) s^iso_{r+s+2}(a,zq q,b) ≤ K (ℓη)^{-1/2} s^iso_{r+p+s+1}(a,w,b)`. -/
theorem isoQuadConcat_of (hU : ∀ x y, 0 ≤ P.ups t x y) (hL : 0 < P.lEta t) {K : ℝ}
    (hK : 0 ≤ K) (h4 : ∀ x a y, P.ups t x a * P.ups t a y ≤ K * P.ups t x y)
    {r p s : ℕ} (hp : 1 ≤ p) (a b : Fin N) (y : Fin (p + 1) → Fin N)
    (zq : Fin N → Fin (r + s + 2) → Fin N) (w : Fin (r + p + s + 1) → Fin N)
    (hzpre : ∀ (q : Fin N) (n : ℕ) (hn : n < r), zq q ⟨n, by omega⟩ = w ⟨n, by omega⟩)
    (hzmid : ∀ q, zq q ⟨r, by omega⟩ = q)
    (hzpost : ∀ (q : Fin N) (n : ℕ) (hn : n < s),
      zq q ⟨r + 1 + n, by omega⟩ = w ⟨r + p + n, by omega⟩)
    (hy : ∀ (n : ℕ) (hn : n < p), y ⟨n, by omega⟩ = w ⟨r + n, by omega⟩) (q : Fin N) :
    P.sIso q q y t * P.sIso a b (zq q) t ≤ K * P.lEta t ^ (-(1 / 2 : ℝ)) * P.sIso a b w t := by
  obtain ⟨c, R, x₁, x₂, y₁, y₂, hc, hR, hq, hw⟩ :=
    contrSplit_isoIns_shape P t hU hL hp a b y zq w hzpre hzmid hzpost hy
  rw [hq, mul_assoc K, hw]
  exact localContraction_max hU hK h4 hc hR x₁ x₂ y₁ y₂ q

/-- **Isotropic sublinear insertion (abstract form).** Under the hypotheses of `isoQuad_of`,
with the factor `(ℓη)^{1/2}` of the `M`-bound on one of the two chains:
`Σ_q (ℓη)^{1/2} s^iso_{p+1}(q,y,q) s^iso_{r+s+2}(a,zq q,b) ≤ K s^iso_{r+p+s+1}(a,w,b)`
(in particular for `b = a`). -/
theorem isoSublin_of (hU : ∀ x y, 0 ≤ P.ups t x y) (hL : 0 < P.lEta t) {K : ℝ}
    (h6 : ∀ x₁ x₂ y₁ y₂, ∑ q, Real.sqrt (P.ups t x₁ q * P.ups t x₂ q * P.ups t q y₁ *
      P.ups t q y₂) ≤ K * Real.sqrt (P.ups t x₁ y₁ * P.ups t x₂ y₂))
    {r p s : ℕ} (hp : 1 ≤ p) (a b : Fin N) (y : Fin (p + 1) → Fin N)
    (zq : Fin N → Fin (r + s + 2) → Fin N) (w : Fin (r + p + s + 1) → Fin N)
    (hzpre : ∀ (q : Fin N) (n : ℕ) (hn : n < r), zq q ⟨n, by omega⟩ = w ⟨n, by omega⟩)
    (hzmid : ∀ q, zq q ⟨r, by omega⟩ = q)
    (hzpost : ∀ (q : Fin N) (n : ℕ) (hn : n < s),
      zq q ⟨r + 1 + n, by omega⟩ = w ⟨r + p + n, by omega⟩)
    (hy : ∀ (n : ℕ) (hn : n < p), y ⟨n, by omega⟩ = w ⟨r + n, by omega⟩) :
    ∑ q, P.lEta t ^ (1 / 2 : ℝ) * P.sIso q q y t * P.sIso a b (zq q) t ≤
      K * P.sIso a b w t := by
  have h := isoQuad_of P t hU hL h6 hp a b y zq w hzpre hzmid hzpost hy
  have e : ∑ q, P.lEta t ^ (1 / 2 : ℝ) * P.sIso q q y t * P.sIso a b (zq q) t =
      P.lEta t ^ (1 / 2 : ℝ) * ∑ q, P.sIso q q y t * P.sIso a b (zq q) t := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => mul_assoc _ _ _
  have hone : P.lEta t ^ (1 / 2 : ℝ) * P.lEta t ^ (-(1 / 2 : ℝ)) = 1 := by
    rw [← Real.rpow_add hL]
    norm_num
  rw [e]
  calc P.lEta t ^ (1 / 2 : ℝ) * ∑ q, P.sIso q q y t * P.sIso a b (zq q) t
      ≤ P.lEta t ^ (1 / 2 : ℝ) * (K * P.lEta t ^ (-(1 / 2 : ℝ)) * P.sIso a b w t) :=
        mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hL.le _)
    _ = K * P.sIso a b w t * (P.lEta t ^ (1 / 2 : ℝ) * P.lEta t ^ (-(1 / 2 : ℝ))) := by ring
    _ = K * P.sIso a b w t := by rw [hone, mul_one]

/-- **Isotropic-averaged insertion (abstract form).** If `Υ = P.ups t ≥ 0` is symmetric, `ℓη > 0`
and the Schwarz convolution (U6) holds with constant `K`, then for `p ≥ 1`, isotropic sites `x`
(the first `p` entries of `x : Fin (p+1)`) and averaged site vectors `xq q` (those `p` sites,
then `q`): `Σ_q Υ(a,q) s^av_{p+1}(xq q) ≤ K (ℓη)^{-1/2} s^iso_{p+1}(a,x,a)`. -/
theorem isoAv_of (hU : ∀ x y, 0 ≤ P.ups t x y) (hsym : ∀ x y, P.ups t x y = P.ups t y x)
    (hL : 0 < P.lEta t) {K : ℝ}
    (h6 : ∀ x₁ x₂ y₁ y₂, ∑ q, Real.sqrt (P.ups t x₁ q * P.ups t x₂ q * P.ups t q y₁ *
      P.ups t q y₂) ≤ K * Real.sqrt (P.ups t x₁ y₁ * P.ups t x₂ y₂))
    {p : ℕ} (hp : 1 ≤ p) (a : Fin N) (xq : Fin N → Fin (p + 1) → Fin N)
    (x : Fin (p + 1) → Fin N) (hlast : ∀ q, xq q ⟨p, by omega⟩ = q)
    (hxq : ∀ (q : Fin N) (n : ℕ) (hn : n < p), xq q ⟨n, by omega⟩ = x ⟨n, by omega⟩) :
    ∑ q, P.ups t a q * P.sAv (xq q) t ≤ K * P.lEta t ^ (-(1 / 2 : ℝ)) * P.sIso a a x t := by
  obtain ⟨c, R, x₁, x₂, y₁, y₂, hc, hR, hq, hw⟩ :=
    contrSplit_isoAv_shape P t hU hsym hL hp a xq x hlast hxq
  simp_rw [hq]
  rw [mul_assoc K, hw]
  exact localContraction_sum h6 hc hR x₁ x₂ y₁ y₂

end Abstract

/-!
## VS forms
-/

section VS

variable (d : VSData) (P : PsiData N) {t : ℝ}

/-- **Isotropic square convolution along the VS flow.** With the inputs `hin : ContrVSInputs d P t`
and sites as in `isoQj_of`:
`Σ_c s^iso_{i+1}(a,x,c)² s^iso_{j+1}(c,y,b)² ≤ C_wc/η · s^iso_{i+j+1}(a,w,b)²`. -/
theorem isoQj_vs (hin : ContrVSInputs d P t) {i j : ℕ} (a b : Fin N)
    (x : Fin (i + 1) → Fin N) (y : Fin (j + 1) → Fin N) (w : Fin (i + j + 1) → Fin N)
    (hx : ∀ (n : ℕ) (hn : n < i), x ⟨n, by omega⟩ = w ⟨n, by omega⟩)
    (hy : ∀ (n : ℕ) (hn : n < j), y ⟨n, by omega⟩ = w ⟨i + n, by omega⟩) :
    ∑ c, P.sIso a c x t ^ 2 * P.sIso c b y t ^ 2 ≤
      d.Cwc / vsHeight P.z t * P.sIso a b w t ^ 2 :=
  isoQj_of P t hin.nonneg hin.lEta_pos hin.convol a b x y w hx hy

/-- **Isotropic quadratic insertion along the VS flow.** With `hin : ContrVSInputs d P t` and sites
as in `isoQuad_of` (`p ≥ 1`): `Σ_q s^iso_{p+1}(q,y,q) s^iso_{r+s+2}(a,zq q,b) ≤
C_wc/η · (ℓη)^{-1/2} · s^iso_{r+p+s+1}(a,w,b)`. -/
theorem isoQuad_vs (hin : ContrVSInputs d P t) {r p s : ℕ} (hp : 1 ≤ p) (a b : Fin N)
    (y : Fin (p + 1) → Fin N) (zq : Fin N → Fin (r + s + 2) → Fin N)
    (w : Fin (r + p + s + 1) → Fin N)
    (hzpre : ∀ (q : Fin N) (n : ℕ) (hn : n < r), zq q ⟨n, by omega⟩ = w ⟨n, by omega⟩)
    (hzmid : ∀ q, zq q ⟨r, by omega⟩ = q)
    (hzpost : ∀ (q : Fin N) (n : ℕ) (hn : n < s),
      zq q ⟨r + 1 + n, by omega⟩ = w ⟨r + p + n, by omega⟩)
    (hy : ∀ (n : ℕ) (hn : n < p), y ⟨n, by omega⟩ = w ⟨r + n, by omega⟩) :
    ∑ q, P.sIso q q y t * P.sIso a b (zq q) t ≤
      d.Cwc / vsHeight P.z t * P.lEta t ^ (-(1 / 2 : ℝ)) * P.sIso a b w t :=
  isoQuad_of P t hin.nonneg hin.lEta_pos hin.schwarz hp a b y zq w hzpre hzmid hzpost hy

/-- **Isotropic quadratic insertion, pointwise form, along the VS flow.** With
`hin : ContrVSInputs d P t` and sites as in `isoQuad_of`, for every `q`:
`s^iso_{p+1}(q,y,q) s^iso_{r+s+2}(a,zq q,b) ≤ C₁'' (ℓη)^{-3/2} s^iso_{r+p+s+1}(a,w,b)`. -/
theorem isoQuadConcat_vs (hin : ContrVSInputs d P t) {r p s : ℕ} (hp : 1 ≤ p) (a b : Fin N)
    (y : Fin (p + 1) → Fin N) (zq : Fin N → Fin (r + s + 2) → Fin N)
    (w : Fin (r + p + s + 1) → Fin N)
    (hzpre : ∀ (q : Fin N) (n : ℕ) (hn : n < r), zq q ⟨n, by omega⟩ = w ⟨n, by omega⟩)
    (hzmid : ∀ q, zq q ⟨r, by omega⟩ = q)
    (hzpost : ∀ (q : Fin N) (n : ℕ) (hn : n < s),
      zq q ⟨r + 1 + n, by omega⟩ = w ⟨r + p + n, by omega⟩)
    (hy : ∀ (n : ℕ) (hn : n < p), y ⟨n, by omega⟩ = w ⟨r + n, by omega⟩) (q : Fin N) :
    P.sIso q q y t * P.sIso a b (zq q) t ≤
      d.C1pp * P.lEta t ^ (-(3 / 2 : ℝ)) * P.sIso a b w t := by
  have hL := hin.lEta_pos
  have hK : 0 ≤ d.C1pp / P.lEta t := div_nonneg (by linarith [d.one_le_C1pp]) hL.le
  have h := isoQuadConcat_of P t hin.nonneg hL hK hin.triangle hp a b y zq w hzpre hzmid
    hzpost hy q
  have e : d.C1pp / P.lEta t * P.lEta t ^ (-(1 / 2 : ℝ)) =
      d.C1pp * P.lEta t ^ (-(3 / 2 : ℝ)) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one, mul_assoc, ← Real.rpow_add hL]
    norm_num
  rwa [e] at h

/-- **Isotropic sublinear insertion along the VS flow.** With `hin : ContrVSInputs d P t` and sites
as in `isoQuad_of`: `Σ_q (ℓη)^{1/2} s^iso_{p+1}(q,y,q) s^iso_{r+s+2}(a,zq q,b) ≤
C_wc/η · s^iso_{r+p+s+1}(a,w,b)`. -/
theorem isoSublin_vs (hin : ContrVSInputs d P t) {r p s : ℕ} (hp : 1 ≤ p) (a b : Fin N)
    (y : Fin (p + 1) → Fin N) (zq : Fin N → Fin (r + s + 2) → Fin N)
    (w : Fin (r + p + s + 1) → Fin N)
    (hzpre : ∀ (q : Fin N) (n : ℕ) (hn : n < r), zq q ⟨n, by omega⟩ = w ⟨n, by omega⟩)
    (hzmid : ∀ q, zq q ⟨r, by omega⟩ = q)
    (hzpost : ∀ (q : Fin N) (n : ℕ) (hn : n < s),
      zq q ⟨r + 1 + n, by omega⟩ = w ⟨r + p + n, by omega⟩)
    (hy : ∀ (n : ℕ) (hn : n < p), y ⟨n, by omega⟩ = w ⟨r + n, by omega⟩) :
    ∑ q, P.lEta t ^ (1 / 2 : ℝ) * P.sIso q q y t * P.sIso a b (zq q) t ≤
      d.Cwc / vsHeight P.z t * P.sIso a b w t :=
  isoSublin_of P t hin.nonneg hin.lEta_pos hin.schwarz hp a b y zq w hzpre hzmid hzpost hy

/-- **Isotropic-averaged insertion along the VS flow.** With `hin : ContrVSInputs d P t` and sites
as in `isoAv_of` (`p ≥ 1`):
`Σ_q Υ(a,q) s^av_{p+1}(xq q) ≤ C_wc/η · (ℓη)^{-1/2} · s^iso_{p+1}(a,x,a)`. -/
theorem isoAv_vs (hin : ContrVSInputs d P t) {p : ℕ} (hp : 1 ≤ p) (a : Fin N)
    (xq : Fin N → Fin (p + 1) → Fin N) (x : Fin (p + 1) → Fin N)
    (hlast : ∀ q, xq q ⟨p, by omega⟩ = q)
    (hxq : ∀ (q : Fin N) (n : ℕ) (hn : n < p), xq q ⟨n, by omega⟩ = x ⟨n, by omega⟩) :
    ∑ q, P.ups t a q * P.sAv (xq q) t ≤
      d.Cwc / vsHeight P.z t * P.lEta t ^ (-(1 / 2 : ℝ)) * P.sIso a a x t :=
  isoAv_of P t hin.nonneg hin.symm hin.lEta_pos hin.schwarz hp a xq x hlast hxq

end VS

end BlockBand.Native.ErdosRiabov.Contr
