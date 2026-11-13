module

public import BlockBand.Native.ErdosRiabov.LemmaK.Ups
public import BlockBand.Native.ErdosRiabov.Flow.Traj

/-!
# The kernel lemma for the propagator estimates

Single-trajectory forms of the clauses of the kernel lemma and related facts, as used by the
propagator estimates.

* (a) single-trajectory (`z' = z`) forms of (K1), (K2), (K3), (K6), (K7), at height
  `vsHeight z t` (no `min_self` rewriting at the call site): `lemmaK_K1_single`, …;
* (b) `vsPropagator_conj`: `P̂_{s,t}(conj μ, conj μ') = conj P̂_{s,t}(μ, μ')` entrywise;
* (c) the pair-height facts `vsPair_height_facts`, from `vsFlow_b`, `vsFlow_K0`;
* `vsCK d`: the kernel constant `C_K` at VS data `d`, and `lemmaKPoint_eq_vsTraj` (`w_t = z_t/√t`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Propagator

open BlockBand.External BlockBand.Internal.Contracts.Inputs BlockBand.Adapters.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.LemmaK
open BlockBand.External.ErdosRiabov (semicircleM semicircleM_dyson norm_semicircleM_lt_one)
open scoped BigOperators ComplexConjugate

/-!
## Constants and points
-/

/-- The kernel constant `C_K = lemmaKConst b κ C₀ D` at VS data `d`. -/
def vsCK (d : VSData) : ℝ := lemmaKConst d.b d.b_pos d.b_lt_half d.kappa d.C0 d.D

theorem vsCK_pos (d : VSData) : 0 < vsCK d :=
  (lemmaKConst_facts d.b_pos d.b_lt_half d.kappa_pos d.C0_ge_one
    (by linarith [d.D_ge_six])).2.2.2.2.2.2

/-- `lemmaKPoint z t = vsTraj z t / √t` (definitional). -/
theorem lemmaKPoint_eq_vsTraj (z : ℂ) (t : ℝ) :
    lemmaKPoint z t = vsTraj z t / (Real.sqrt t : ℂ) := rfl

/-!
## (c) pair heights
-/

/-- **Pair-height (K0) facts** (item (K0) of Lemma K), for `N ≥ 1`, `κ > 0`, `C₀ ≥ 0`,
`z, z' ∈ 𝒟`, `η_r = min (vsHeight z r) (vsHeight z' r)`: for `t ∈ [0,1]`,
`N^{-1+δ₀} ≤ η_t ≤ C₀+1`;
`3c_m/4 ≤ η_t` for `t ≤ 1/4`;
`c_m ≤ η_0`;
`(t-s)c_m ≤ η_s` and
`η_t ≤ η_s` for `s ≤ t ≤ 1`.
-/
theorem vsPair_height_facts {N : ℕ} (hN : 0 < N) {δ₀ κ C₀ : ℝ} (hκ : 0 < κ) (hC₀ : 0 ≤ C₀)
    {z z' : ℂ} (hz : BulkDomain N δ₀ κ C₀ z) (hz' : BulkDomain N δ₀ κ C₀ z') :
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 → (N : ℝ) ^ (-1 + δ₀) ≤ min (vsHeight z t) (vsHeight z' t) ∧
      min (vsHeight z t) (vsHeight z' t) ≤ C₀ + 1) ∧
    (∀ t : ℝ, t ≤ 1 / 4 → 3 / 4 * imLower κ C₀ ≤ min (vsHeight z t) (vsHeight z' t)) ∧
    imLower κ C₀ ≤ min (vsHeight z 0) (vsHeight z' 0) ∧
    (∀ s t : ℝ, s ≤ t → t ≤ 1 →
      (t - s) * imLower κ C₀ ≤ min (vsHeight z s) (vsHeight z' s) ∧
      min (vsHeight z t) (vsHeight z' t) ≤ min (vsHeight z s) (vsHeight z' s)) := by
  obtain ⟨-, -, hc, -, hr, -, h0, hcs, hs0, hdiff, -⟩ := vsFlow_b hN hκ hC₀ hz
  obtain ⟨-, -, hc', -, hr', -, h0', -, hs0', hdiff', -⟩ := vsFlow_b hN hκ hC₀ hz'
  have hcm := imLower_pos hκ (kappa_le_two_of_bulk hz) hC₀
  refine ⟨fun t ht0 ht1 => ⟨le_min (hz.2.1.trans (hr t ht0 ht1).1)
      (hz'.2.1.trans (hr' t ht0 ht1).1), (min_le_left _ _).trans ((hr t ht0 ht1).2.trans h0)⟩,
    fun t ht => le_min (vsFlow_K0 hN hC₀ hz ht) (vsFlow_K0 hN hC₀ hz' ht),
    le_min (hcs.trans hs0) (hcs.trans hs0'), fun s t hst ht1 => ?_⟩
  have hp := vsHeight_pos (hz.im_pos hN) ht1
  have hp' := vsHeight_pos (hz'.im_pos hN) ht1
  have e1 := hdiff s t
  have e2 := hdiff' s t
  have h1 : (t - s) * imLower κ C₀ ≤ (t - s) * (semicircleM z).im :=
    mul_le_mul_of_nonneg_left hc (by linarith)
  have h2 : (t - s) * imLower κ C₀ ≤ (t - s) * (semicircleM z').im :=
    mul_le_mul_of_nonneg_left hc' (by linarith)
  have h3 : 0 ≤ (t - s) * imLower κ C₀ := mul_nonneg (by linarith) hcm.le
  exact ⟨le_min (by linarith) (by linarith), min_le_min (by linarith) (by linarith)⟩

/-!
## (b) conjugate propagator
-/

/-- **Conjugate propagator**: for a stochastic symmetric `S`, `‖tμμ'‖ < 1`:
`P̂_{s,t}(conj μ, conj μ')_{ax} = conj P̂_{s,t}(μ, μ')_{ax}`. -/
theorem vsPropagator_conj {N : ℕ} {S : Matrix (Fin N) (Fin N) ℝ} (hS : StochasticSymm S)
    {μ μ' : ℂ} {s t : ℝ} (ht : ‖(t : ℂ) * (μ * μ')‖ < 1) (a x : Fin N) :
    vsPropagator S (conj μ) (conj μ') s t a x = conj (vsPropagator S μ μ' s t a x) := by
  have hc : (t : ℂ) * (conj μ * conj μ') = conj ((t : ℂ) * (μ * μ')) := by
    simp only [map_mul, Complex.conj_ofReal]
  have ht' : ‖(t : ℂ) * (conj μ * conj μ')‖ < 1 := by rwa [hc, Complex.norm_conj]
  rw [vsPropagator_eq hS ht', vsPropagator_eq hS ht]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, map_sub,
    Complex.conj_ofReal, lemmaK_vsKernel_conj hS ht a x, Matrix.one_apply]
  split_ifs <;> simp

/-!
## (a) single-trajectory forms
-/

section Single

variable {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {δ₀ κ C₀ D : ℝ} (hδ₀ : 0 < δ₀) (hκ : 0 < κ)
  (hC₀ : 1 ≤ C₀) (hD : 6 ≤ D) {m W : ℕ} (hm : 4 ≤ m) (hW : 0 < W) {z : ℂ}
  (hz : BulkDomain (m * W) δ₀ κ C₀ z)
include hb0 hb hδ₀ hκ hC₀ hD hm hW hz

/-- (K1), single trajectory: `|T̂_t| ≤ C_K Υ_{η_t}`, `|X̂_t| ≤ C_K Υ_{η_0}`, `|X̂_t| ≤ C_K Υ_1`,
`T̂_t` real and `≥ 0`. -/
theorem lemmaK_K1_single {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∀ x y, ‖vsKernel (shortRingProfile b m W) (semicircleM z) (conj (semicircleM z)) t x y‖ ≤
      lemmaKConst b hb0 hb κ C₀ D * polynomialControl (m * W) W D (vsHeight z t) x y) ∧
    (∀ x y, ‖vsKernel (shortRingProfile b m W) (semicircleM z) (semicircleM z) t x y‖ ≤
      lemmaKConst b hb0 hb κ C₀ D * polynomialControl (m * W) W D (vsHeight z 0) x y) ∧
    (∀ x y, ‖vsKernel (shortRingProfile b m W) (semicircleM z) (semicircleM z) t x y‖ ≤
      lemmaKConst b hb0 hb κ C₀ D * polynomialControl (m * W) W D 1 x y) ∧
    (∀ x y,
      (vsKernel (shortRingProfile b m W) (semicircleM z) (conj (semicircleM z)) t x y).im = 0 ∧
      0 ≤ (vsKernel (shortRingProfile b m W) (semicircleM z) (conj (semicircleM z)) t x y).re) := by
  have h := lemmaK_K1 hb0 hb hδ₀ hκ hC₀ hD hm hW hz hz ht0 ht1
  simp only [min_self] at h
  exact h

/-- (K2), single trajectory, "threshold or `t ≤ 1/4`". -/
theorem lemmaK_K2_single {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hthr : ((W : ℝ) / ((m * W : ℕ) : ℝ)) ^ 2 ≤ vsHeight z t ∨ t ≤ 1 / 4) (a x y : Fin (m * W)) :
    ‖vsKernel (shortRingProfile b m W) (semicircleM z) (conj (semicircleM z)) t a x -
        vsKernel (shortRingProfile b m W) (semicircleM z) (conj (semicircleM z)) t a y‖ ≤
      lemmaKConst b hb0 hb κ C₀ D *
        (min ((ErdosRiabov.cyclicDistance (m * W) x y : ℝ) + W)
            (ErdosRiabov.localizationLength (m * W) W (vsHeight z t)) /
          ErdosRiabov.localizationLength (m * W) W (vsHeight z t)) *
        (polynomialControl (m * W) W D (vsHeight z t) a x +
          polynomialControl (m * W) W D (vsHeight z t) a y) := by
  have h := lemmaK_K2 hb0 hb hδ₀ hκ hC₀ hD hm hW hz hz ht0 ht1 (by rwa [min_self]) a x y
  simp only [min_self] at h
  exact h

/-- (K3), single trajectory: `|T̂_t(a,x) - Im m/(Nη_t)| ≤ C_K N/W²`. -/
theorem lemmaK_K3_single {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (a x : Fin (m * W)) :
    ‖vsKernel (shortRingProfile b m W) (semicircleM z) (conj (semicircleM z)) t a x -
        (((semicircleM z).im / (((m * W : ℕ) : ℝ) * vsHeight z t) : ℝ) : ℂ)‖
      ≤ lemmaKConst b hb0 hb κ C₀ D * ((m * W : ℕ) : ℝ) / (W : ℝ) ^ 2 :=
  (lemmaK_K3 hb0 hb hδ₀ hκ hC₀ hD hm hW hz hz ht0 ht1 a x).2.2

/-- (K6), single trajectory: entry bounds of `P̂_{s,t}` (Θ-type) and `Q̂_{s,t}` (Ξ-type), and
`P̂_{s,t}` real and `≥ 0`. -/
theorem lemmaK_K6_single {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t ≤ 1) :
    (∀ a x,
      ‖vsPropagator (shortRingProfile b m W) (semicircleM z) (conj (semicircleM z)) s t a x‖ ≤
        (if a = x then 1 else 0) +
          lemmaKConst b hb0 hb κ C₀ D / imLower κ C₀ * vsHeight z s *
            polynomialControl (m * W) W D (vsHeight z t) a x) ∧
    (∀ a x,
      ‖vsPropagator (shortRingProfile b m W) (semicircleM z) (semicircleM z) s t a x‖ ≤
        (if a = x then 1 else 0) +
          lemmaKConst b hb0 hb κ C₀ D / imLower κ C₀ * vsHeight z s *
            polynomialControl (m * W) W D (vsHeight z 0) a x) ∧
    (∀ a x,
      (vsPropagator (shortRingProfile b m W) (semicircleM z) (conj (semicircleM z)) s t a x).im
        = 0 ∧
      0 ≤ (vsPropagator (shortRingProfile b m W) (semicircleM z) (conj (semicircleM z)) s t
        a x).re) := by
  obtain ⟨-, -, -, h1, -, -, -, h2, h3⟩ := lemmaK_K6 hb0 hb hδ₀ hκ hC₀ hD hm hW hz hz hs0 hst ht1
  simp only [min_self] at h1 h2
  exact ⟨h1, h2, h3⟩

/-- (K7), single trajectory: `Σ_x |T̂_t(a,x)| ≤ C_K C₁''/η_t`,
`Σ_x |(I + tX̂_t)(a,x)| ≤ 1 + C_K C₁''/c_m`, `Σ_x |Q̂_{s,t}(a,x)| ≤ 1 + C_K C₁''/c_m`. -/
theorem lemmaK_K7_single {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t ≤ 1)
    (a : Fin (m * W)) :
    ∑ x, ‖vsKernel (shortRingProfile b m W) (semicircleM z) (conj (semicircleM z)) t a x‖ ≤
      lemmaKConst b hb0 hb κ C₀ D * lemmaKC1 b hb0 hb κ C₀ D / vsHeight z t ∧
    ∑ x, ‖(1 + (t : ℂ) •
        vsKernel (shortRingProfile b m W) (semicircleM z) (semicircleM z) t) a x‖ ≤
      1 + lemmaKConst b hb0 hb κ C₀ D * lemmaKC1 b hb0 hb κ C₀ D / imLower κ C₀ ∧
    ∑ x, ‖vsPropagator (shortRingProfile b m W) (semicircleM z) (semicircleM z) s t a x‖ ≤
      1 + lemmaKConst b hb0 hb κ C₀ D * lemmaKC1 b hb0 hb κ C₀ D / imLower κ C₀ := by
  obtain ⟨h1, -, h3, h4⟩ := lemmaK_K7 hb0 hb hδ₀ hκ hC₀ hD hm hW hz hz hs0 hst ht1 a
  simp only [min_self] at h1
  exact ⟨h1, h3, h4⟩

end Single

end BlockBand.Native.ErdosRiabov.Propagator
