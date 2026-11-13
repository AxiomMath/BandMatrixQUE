module

public import BlockBand.Layers.TaggedDecay
public import BlockBand.Layers.FullEnergyPath
public import BlockBand.Layers.TaggedDecayMeanHolds

/-!
# `TdcPairStep` from the final residual-pair energy bound, by homogeneity

The final residual pair in the proof of the tagged decay bound: "The final residual pair has a
fixed stability gap, as in the matched-traces theorem; it needs a bounded coefficient, not a
further contraction".

## Proof

The quantity of `TdcPairStep` is the `S`-insertion `W⁻¹ Tr P_a R⁰ S R⁰`, `S = K*YK`, with
`R⁰ = (V - E - X - s ā)⁻¹ = G*`, `G = (V - E - X - sa)⁻¹ = rpResolvent E s X` (a.s., `V`
Hermitian; `tdp_pairRes_eq`), so its modulus is `|W⁻¹ Tr P_a G S G|`. The energy derivative of the
residual pair (`FetResidualBound`) bounds
`ρ'_a = W⁻¹ Tr P_a G(1 + S' + sa')G - a'` for **every** source `S' ⪰ 0`, with constants uniform in
`S'`. Since `ρ'_a` is affine in `S'`, applying it to `S' = tS` and letting `t → ∞`
(`tdp_le_of_scale`) gives the homogeneous bound
`‖W⁻¹ Tr P_a G S G‖_q ≤ C (d̂ + (δ + W^{-1/2}) u)` on `δ = d(X) ≤ d_*` (with
`d̂ = max_i |D_i(X, Y)|`, since `fetFd(tS) = t D - W⁻¹Tr R z_∂' R`, and `fetClock(tS) = t u`
because `K⁻*SK⁻¹ = Y`) and `≤ C u` for every `X` (crude clause), hence `≤ (C/d_*) δ u` for
`δ > d_*`. No operator-norm moment of `V` is used.

## Main results

* `tdcPairStep_of_fet : FetResidualBound → TdcPairStep`;
* `tgtDecayBound_of_fet (hcount) (hgrad) (FetResidualBound) : TgtDecayBound` — the assembly with
  `TdcLayerMean` proved (`tdcLayerMean_holds`);
  the corresponding tagged-trace statement is `taggedTrace_of_fet`.

`FetResidualBound` is a hypothesis here; it is proved by `fetResidualBound_holds`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

namespace BlockBand.Layers

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Inputs (GaussianLpGradient ConditionalBlockGUECount)
open scoped ENNReal NNReal ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

/-!
## 1. Deterministic identities
-/

section Det

variable {W : ℕ}

theorem tdp_blockTrace_conjTranspose (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i : Fin 2) :
    blockTrace Mᴴ i = star (blockTrace M i) := by
  unfold blockTrace
  simp [conjTranspose_apply, star_sum]

/-- `R⁰ = G*` for Hermitian residual-pair blocks (`s = min(c, b)`, `μ = ā`). -/
theorem tdp_pairRes_eq {b E : ℝ} {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hX : X.IsHermitian) (v : RpSample W) (hv : ∀ j, (v.1 j).IsHermitian) :
    tdcPairRes b E X v = (rpResolvent E (min (1 - 2 * b) b) X v)ᴴ := by
  unfold tdcPairRes rpResolvent
  rw [conjTranspose_nonsing_inv]
  congr 1
  rw [conjTranspose_sub, conjTranspose_sub, conjTranspose_sub, (rp_rpMatrix_isHermitian v hv).eq,
    hX.eq, conjTranspose_smul, conjTranspose_smul, conjTranspose_one]
  congr 2
  · simp
  · simp [tgtMu]

/-- `G(1 + tS + c)G = G(1 + c)G + t GSG`. -/
theorem tdp_GYG_eq (G S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (c t : ℂ) :
    G * (1 + t • S + c • 1) * G = G * (1 + c • 1) * G + t • (G * S * G) := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  abel

theorem tdp_clkTrace_smul (t : ℝ) (Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    clkTrace ((t : ℂ) • Y) = t * clkTrace Y := by
  unfold clkTrace
  rw [trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  ring

theorem tdp_le_maxD {b E : ℝ} (X Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i : Fin 2) :
    ‖tdcD b E X Y i‖ ≤ tdcMaxD b E X Y := by
  unfold tdcMaxD
  fin_cases i
  · exact le_max_left _ _
  · exact le_max_right _ _

/-- The clock of the scaled source: `fetClock(tS) = t u` for `S = K*YK`. -/
theorem tdp_fetClock_eq {b E : ℝ} (hz : 0 < (boundaryZ b E).im)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian)
    (Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (t : ℝ) :
    fetClock b E X ((t : ℂ) • ((tdcK b E X)ᴴ * Y * tdcK b E X)) = t * clkTrace Y := by
  unfold fetClock fetR
  rw [Matrix.mul_smul, Matrix.smul_mul, tdmH_Y_eq hz hX Y, tdp_clkTrace_smul]

/-- The distance of the scaled source: `fetDist(tS) ≤ t max_i|D_i| + N₀` (`t ≥ 0`). -/
theorem tdp_fetDist_le {b E : ℝ} (X Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) {t : ℝ}
    (ht : 0 ≤ t) :
    fetDist b E X ((t : ℂ) • ((tdcK b E X)ᴴ * Y * tdcK b E X)) ≤
      t * tdcMaxD b E X Y + (‖fetR b E X * (tgtZd b E • (1 : Matrix (Fin 2 × Fin W)
        (Fin 2 × Fin W) ℂ)) * fetR b E X‖ + ‖tgtAd E‖) := by
  have key : ∀ i, ‖fetFd b E X ((t : ℂ) • ((tdcK b E X)ᴴ * Y * tdcK b E X)) i - tgtAd E‖ ≤
      t * tdcMaxD b E X Y + (‖fetR b E X * (tgtZd b E • (1 : Matrix (Fin 2 × Fin W)
        (Fin 2 × Fin W) ℂ)) * fetR b E X‖ + ‖tgtAd E‖) := by
    intro i
    have e : fetFd b E X ((t : ℂ) • ((tdcK b E X)ᴴ * Y * tdcK b E X)) i =
        (t : ℂ) * tdcD b E X Y i - blockTrace (fetR b E X * (tgtZd b E • (1 : Matrix
          (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) * fetR b E X) i := by
      unfold fetFd tdcD
      rw [Matrix.mul_sub, Matrix.sub_mul, tdm_blockTrace_sub, Matrix.mul_smul, Matrix.smul_mul,
        tdm_blockTrace_smul]
      rfl
    rw [e]
    have h1 := lct_norm_blockTrace_le (fetR b E X * (tgtZd b E • (1 : Matrix (Fin 2 × Fin W)
      (Fin 2 × Fin W) ℂ)) * fetR b E X) i
    have h2 : ‖(t : ℂ) * tdcD b E X Y i‖ ≤ t * tdcMaxD b E X Y := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht]
      exact mul_le_mul_of_nonneg_left (tdp_le_maxD X Y i) ht
    calc ‖(t : ℂ) * tdcD b E X Y i - blockTrace (fetR b E X * (tgtZd b E • (1 : Matrix
          (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) * fetR b E X) i - tgtAd E‖
        ≤ ‖(t : ℂ) * tdcD b E X Y i‖ + ‖blockTrace (fetR b E X * (tgtZd b E • (1 : Matrix
          (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) * fetR b E X) i‖ + ‖tgtAd E‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact norm_sub_le _ _
      _ ≤ _ := by linarith
  exact max_le (key 0) (key 1)

end Det

/-!
## 2. The limit `t → ∞`
-/

/-- If `‖φ‖_p ≤ A + B/t` for every `t ≥ 1`, then `‖φ‖_p ≤ A`. -/
theorem tdp_le_of_scale {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} {φ : Ω → ℂ} {p A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ t : ℝ, 1 ≤ t → eLpNorm φ (ENNReal.ofReal p) ν ≤ ENNReal.ofReal (A + B / t)) :
    eLpNorm φ (ENNReal.ofReal p) ν ≤ ENNReal.ofReal A := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε' : (0 : ℝ) < ε := hε
  set t := max 1 (B / ε) with ht
  have ht1 : 1 ≤ t := le_max_left _ _
  have ht0 : 0 < t := by linarith
  refine (h t ht1).trans ?_
  rw [ENNReal.ofReal_add hA (by positivity)]
  gcongr
  rw [← ENNReal.ofReal_coe_nnreal]
  refine ENNReal.ofReal_le_ofReal (div_le_of_le_mul₀ ht0.le hε'.le ?_)
  have : B / ε ≤ t := le_max_right _ _
  rw [div_le_iff₀ hε'] at this
  linarith

/-!
## 3. `TdcPairStep`
-/

theorem tdp_measurable_GMG {W : ℕ} (E s : ℝ) (X M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (k : Fin 2) :
    Measurable (fun v : RpSample W => blockTrace (rpResolvent E s X v * M * rpResolvent E s X v) k) := by
  have hm : Measurable (fun v : RpSample W => rpResolvent E s X v) :=
    rp_measurable_resolvent E s (Xf := fun _ : RpSample W => X) (ωf := id) measurable_const
      measurable_id
  exact (tdc_continuous_blockTrace k).measurable.comp (srec_measurable_mul
    (srec_measurable_mul hm measurable_const) hm)

theorem tdp_measurable_rhoMax {W : ℕ} (E s : ℝ) (X S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Measurable (fetRhoMax E s X S) := by
  unfold fetRhoMax fetRho
  exact ((tdp_measurable_GMG E s X _ 0).sub measurable_const).norm.max
    ((tdp_measurable_GMG E s X _ 1).sub measurable_const).norm

theorem tdp_ae_herm (W : ℕ) (b s : ℝ) : ∀ᵐ v ∂rpLaw W b s, ∀ j, (v.1 j).IsHermitian := by
  have := fun t => isProbabilityMeasure_gueMeasure W t
  unfold rpLaw
  exact (Measure.quasiMeasurePreserving_fst).ae
    (ae_blocks_isHermitian 2 W (Real.toNNReal ((1 - 2 * b - s / 2) / W)))

/-- **One scale `t`** (deterministic data): `t ‖W⁻¹Tr P_a G S G‖_q ≤ M₀ + F` whenever
`‖max_k|ρ'_k(tS)|‖_q ≤ F`, `M₀ = y⁻² ‖1 + sa'‖ + |a'|`. -/
theorem tdp_one_scale {W : ℕ} {b E s y q : ℝ} (hq : 1 ≤ q) (hy : 0 < y)
    (hya : y ≤ -(s * (matchedA E).im)) {X S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hX : X.IsHermitian) {t F : ℝ} (ht : 0 < t) (hF0 : 0 ≤ F)
    (hF : eLpNorm (fetRhoMax E s X ((t : ℂ) • S)) (ENNReal.ofReal q) (rpLaw W b s) ≤
      ENNReal.ofReal F) (a : Fin 2) :
    eLpNorm (fun v => blockTrace (rpResolvent E s X v * S * rpResolvent E s X v) a)
        (ENNReal.ofReal q) (rpLaw W b s) ≤
      ENNReal.ofReal ((y⁻¹ ^ 2 * ‖(1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) +
        ((s : ℂ) * tgtAd E) • 1‖ + ‖tgtAd E‖ + F) / t) := by
  set M₀ := y⁻¹ ^ 2 * ‖(1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) +
    ((s : ℂ) * tgtAd E) • 1‖ + ‖tgtAd E‖ with hM₀
  have hM₀0 : 0 ≤ M₀ := by positivity
  set β := fun v => blockTrace (rpResolvent E s X v * S * rpResolvent E s X v) a with hβ
  have hβm : Measurable β := tdp_measurable_GMG E s X S a
  have hpt : ∀ᵐ v ∂rpLaw W b s, ‖t * ‖β v‖‖ ≤ M₀ + ‖fetRhoMax E s X ((t : ℂ) • S) v‖ := by
    filter_upwards [tdp_ae_herm W b s] with v hv
    set G := rpResolvent E s X v with hG
    have hGn : ‖G‖ ≤ y⁻¹ := rp_norm_resolvent_le E s hX v hv hy hya
    set c := blockTrace (G * (1 + ((s : ℂ) * tgtAd E) • 1) * G) a - tgtAd E with hc
    have hcn : ‖c‖ ≤ M₀ := by
      refine (norm_sub_le _ _).trans ?_
      have h1 := lct_norm_blockTrace_le (G * (1 + ((s : ℂ) * tgtAd E) • 1) * G) a
      have h2 := tdm_norm_mul3_le G (1 + ((s : ℂ) * tgtAd E) • 1) G
      have hG0 := norm_nonneg G
      have h3 : ‖G‖ * ‖(1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) +
          ((s : ℂ) * tgtAd E) • 1‖ * ‖G‖ ≤ y⁻¹ ^ 2 * ‖(1 : Matrix (Fin 2 × Fin W)
            (Fin 2 × Fin W) ℂ) + ((s : ℂ) * tgtAd E) • 1‖ := by
        have := mul_le_mul hGn hGn hG0 (by positivity)
        nlinarith [norm_nonneg ((1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) +
          ((s : ℂ) * tgtAd E) • 1)]
      linarith
    have hrho : fetRho E s X ((t : ℂ) • S) v a = c + (t : ℂ) * β v := by
      unfold fetRho
      rw [← hG, tdp_GYG_eq, tdm_blockTrace_add, tdm_blockTrace_smul, hc]
      ring
    have hmax : ‖fetRho E s X ((t : ℂ) • S) v a‖ ≤ fetRhoMax E s X ((t : ℂ) • S) v := by
      unfold fetRhoMax
      fin_cases a
      · exact le_max_left _ _
      · exact le_max_right _ _
    have e1 : ‖t * ‖β v‖‖ = ‖(t : ℂ) * β v‖ := by
      rw [Real.norm_of_nonneg (by positivity), norm_mul, Complex.norm_real,
        Real.norm_of_nonneg ht.le]
    rw [e1]
    have e2 : (t : ℂ) * β v = fetRho E s X ((t : ℂ) • S) v a - c := by rw [hrho]; ring
    rw [e2]
    refine (norm_sub_le _ _).trans ?_
    have := Real.le_norm_self (fetRhoMax E s X ((t : ℂ) • S) v)
    linarith
  have hfm : AEStronglyMeasurable (fun v => t * ‖β v‖) (rpLaw W b s) :=
    (measurable_const.mul hβm.norm).aestronglyMeasurable
  have hb := tdc_eLpNorm_le_const_add hfm (tdp_measurable_rhoMax E s X _).aestronglyMeasurable hq
    hM₀0 hF0 hpt hF
  have e3 : (fun v => t * ‖β v‖) = t • fun v => ‖β v‖ := rfl
  rw [e3, eLpNorm_const_smul, eLpNorm_norm _ hβm.aestronglyMeasurable,
    Real.enorm_eq_ofReal ht.le] at hb
  rw [ENNReal.ofReal_div_of_pos ht, ENNReal.le_div_iff_mul_le (Or.inl (by simpa using ht))
    (Or.inl ENNReal.ofReal_ne_top), mul_comm]
  exact hb

set_option maxHeartbeats 400000 in
/-- **`TdcPairStep` from `FetResidualBound`** (the final residual pair in the proof of the tagged
decay bound).

*Law.* The residual pair layer `rpLaw W b s`, `s = min(1 - 2b, b)` (`A_j ~ GUE_W((c - s/2)/W)`,
bond `Gin((b - s/2)/W)`), conditional on the deterministic Hermitian exterior Schur matrix `X`
and clock `Y ⪰ 0`; `S = K*YK`, `K = z_∂ - X`, `R⁰ = (V - E - X - sā)⁻¹` (`tdcPairRes`).

*Norms.* `L^q(rpLaw)` of the complex scalar `W⁻¹ Tr P_a R⁰ S R⁰` (modulus).

*Quantifiers and uniformity.* As in `TdcPairStep`: `b, κ, q ≥ 1` first, then `C ≥ 0, W₀` (those
of `FetResidualBound` at `s`, `C ↦ C(1 + 1/d_*)`), uniformly in `W ≥ W₀`, Hermitian `X` (no
restriction on `d(X)`), `Y ⪰ 0`, `E ∈ bulkInterval κ`, `a`.

*Proof.* Homogeneity in the source (`tdp_one_scale`, `tdp_le_of_scale`, `t → ∞` inside the
estimate, no limit in the statement): the fine clause of `FetResidualBound` at `tS` gives
`C(d̂ + (δ + W^{-1/2}) u)` on `δ ≤ d_*`, its crude clause `C u ≤ (C/d_*) δ u` on `δ > d_*`.

*Inputs.* `FetResidualBound`. -/
theorem tdcPairStep_of_fet (hfet : FetResidualBound) : TdcPairStep := by
  intro b hb0 hb1 κ hκ q hq
  set s := min (1 - 2 * b) b with hs
  have hs0 : 0 < s := lt_min (by linarith) hb0
  have hs2 : s < 2 * min (1 - 2 * b) b := by linarith
  obtain ⟨dstar, C, W₀, hdstar, hC, hF⟩ := hfet b hb0 hb1 κ s hκ hs0 hs2 q hq
  obtain ⟨y, hy, hyE⟩ := tdc_im_smu_lower hb0 hb1 hκ
  obtain ⟨η₀, hη₀, hbulk⟩ := dcv_bulk hb0 hb1 hκ
  refine ⟨C * (1 + dstar⁻¹), W₀, by positivity, ?_⟩
  intro W hW hWW X Y hX hY E hE a
  have hz : 0 < (boundaryZ b E).im := lt_of_lt_of_le hη₀ (hbulk E hE).1
  have hya : y ≤ -(s * (matchedA E).im) := by
    have := hyE E hE
    rw [Complex.im_ofReal_mul] at this
    simpa [tgtMu] using this
  set K := tdcK b E X with hK
  set S₀ := Kᴴ * Y * K with hS₀def
  have hS₀ : S₀.PosSemidef := hY.conjTranspose_mul_mul_same K
  set u := clkTrace Y with hu
  set δ := matchedDistance b E X with hδ
  set w := (W : ℝ) ^ (-(1 / 2 : ℝ)) with hw
  set Dm := tdcMaxD b E X Y with hDm
  have hu0 : 0 ≤ u := clkTrace_nonneg hY
  have hδ0 : 0 ≤ δ := clk_matchedDistance_nonneg b E X
  have hw0 : 0 ≤ w := tdc_rpow_half_nonneg W
  have hDm0 : 0 ≤ Dm := tdcMaxD_nonneg b E X Y
  have hwe : 1 / Real.sqrt W = w := by rw [hw, tdc_rpow_half, one_div]
  set N₀ := ‖fetR b E X * (tgtZd b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)) *
    fetR b E X‖ + ‖tgtAd E‖ with hN₀
  have hN₀0 : 0 ≤ N₀ := by positivity
  set M₀ := y⁻¹ ^ 2 * ‖(1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) +
    ((s : ℂ) * tgtAd E) • 1‖ + ‖tgtAd E‖ with hM₀
  have hM₀0 : 0 ≤ M₀ := by positivity
  have hSt : ∀ t : ℝ, 0 ≤ t → ((t : ℂ) • S₀).PosSemidef := fun t ht =>
    hS₀.smul (by exact_mod_cast ht)
  -- step 1: the target is `‖W⁻¹ Tr P_a G S G‖`
  have h1 : eLpNorm (fun v : RpSample W => blockTrace (tdcPairRes b E X v * S₀ *
      tdcPairRes b E X v) a) (ENNReal.ofReal q) (rpLaw W b s) =
      eLpNorm (fun v => blockTrace (rpResolvent E s X v * S₀ * rpResolvent E s X v) a)
        (ENNReal.ofReal q) (rpLaw W b s) := by
    have hRm : Measurable (fun v : RpSample W => tdcPairRes b E X v) :=
      tdc_measurable_pairRes b E measurable_const measurable_id
    refine eLpNorm_congr_norm_ae ((tdc_continuous_blockTrace a).measurable.comp
      (srec_measurable_mul (srec_measurable_mul hRm measurable_const) hRm)).aestronglyMeasurable
      (tdp_measurable_GMG E s X S₀ a).aestronglyMeasurable ?_
    filter_upwards [tdp_ae_herm W b s] with v hv
    rw [tdp_pairRes_eq hX v hv]
    have e : (rpResolvent E s X v)ᴴ * S₀ * (rpResolvent E s X v)ᴴ =
        (rpResolvent E s X v * S₀ * rpResolvent E s X v)ᴴ := by
      rw [conjTranspose_mul, conjTranspose_mul, hS₀.isHermitian.eq, Matrix.mul_assoc]
    rw [e, tdp_blockTrace_conjTranspose, norm_star]
  rw [h1]
  -- step 2: the two scaled bounds
  have hT : 0 ≤ Dm + (δ + w) * u := by positivity
  by_cases hd : δ ≤ dstar
  · have hA : 0 ≤ C * (Dm + u * (δ + w)) := by positivity
    refine (tdp_le_of_scale (B := M₀ + C * N₀ + C * (δ + w)) hA (by positivity) fun t ht => ?_).trans
      (ENNReal.ofReal_le_ofReal ?_)
    · have ht0 : 0 < t := by linarith
      have hFt := (hF W hW hWW X ((t : ℂ) • S₀) hX (hSt t ht0.le) E hE).2 hd
      rw [tdp_fetClock_eq hz hX Y t, hwe] at hFt
      have hdist := tdp_fetDist_le (b := b) (E := E) X Y ht0.le
      set Ft := C * (fetDist b E X ((t : ℂ) • S₀) + (1 + t * u) * (δ + w)) with hFtdef
      have hFt0 : 0 ≤ Ft := by
        have : 0 ≤ fetDist b E X ((t : ℂ) • S₀) :=
          (norm_nonneg _).trans (le_max_left _ _)
        positivity
      refine (tdp_one_scale hq hy hya hX ht0 hFt0 hFt a).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [div_le_iff₀ ht0]
      have hC1 : C * fetDist b E X ((t : ℂ) • S₀) ≤ C * (t * Dm + N₀) :=
        mul_le_mul_of_nonneg_left hdist hC
      have e : (C * (Dm + u * (δ + w)) + (M₀ + C * N₀ + C * (δ + w)) / t) * t =
          t * (C * (Dm + u * (δ + w))) + (M₀ + C * N₀ + C * (δ + w)) := by
        field_simp
      rw [e, hFtdef]
      nlinarith
    · have : C * (Dm + u * (δ + w)) ≤ C * (Dm + (δ + w) * u) + C * dstar⁻¹ * (Dm + (δ + w) * u) := by
        have : 0 ≤ C * dstar⁻¹ * (Dm + (δ + w) * u) := by positivity
        nlinarith
      nlinarith
  · replace hd : dstar < δ := not_le.mp hd
    have hA : 0 ≤ C * u := by positivity
    refine (tdp_le_of_scale (B := M₀ + C) hA (by positivity) fun t ht => ?_).trans
      (ENNReal.ofReal_le_ofReal ?_)
    · have ht0 : 0 < t := by linarith
      have hFt := (hF W hW hWW X ((t : ℂ) • S₀) hX (hSt t ht0.le) E hE).1
      rw [tdp_fetClock_eq hz hX Y t] at hFt
      refine (tdp_one_scale hq hy hya hX ht0 (by positivity) hFt a).trans
        (ENNReal.ofReal_le_ofReal ?_)
      rw [div_le_iff₀ ht0]
      have e : (C * u + (M₀ + C) / t) * t = t * (C * u) + (M₀ + C) := by field_simp
      rw [e]
      nlinarith
    · have h1 : 1 ≤ dstar⁻¹ * δ := by
        rw [inv_mul_eq_div, le_div_iff₀ hdstar]; linarith
      have h2 : C * u ≤ C * dstar⁻¹ * (δ * u) := by
        have := mul_le_mul_of_nonneg_left h1 (mul_nonneg hC hu0)
        nlinarith
      have h3 : C * dstar⁻¹ * (δ * u) ≤ C * dstar⁻¹ * (Dm + (δ + w) * u) := by
        have : δ * u ≤ Dm + (δ + w) * u := by nlinarith
        exact mul_le_mul_of_nonneg_left this (by positivity)
      have h4 : 0 ≤ C * (Dm + (δ + w) * u) := by positivity
      nlinarith

/-!
## 4. Assemblies
-/

/-- **The tagged decay bound from `FetResidualBound`** (`TgtDecayBound`). Law, domain, norms and
quantifiers as in `TgtDecayBound`. Inputs: `ConditionalBlockGUECount`, `GaussianLpGradient` and
`FetResidualBound`; `TdcLayerMean` is proved (`tdcLayerMean_holds`) and `TdcPairStep` follows
(`tdcPairStep_of_fet`). -/
theorem tgtDecayBound_of_fet (hcount : ConditionalBlockGUECount) (hgrad : GaussianLpGradient)
    (hfet : FetResidualBound) : TgtDecayBound :=
  tgtDecayBound_of_steps hcount hgrad (tdcLayerMean_holds hcount hgrad) (tdcPairStep_of_fet hfet)

end BlockBand.Layers
