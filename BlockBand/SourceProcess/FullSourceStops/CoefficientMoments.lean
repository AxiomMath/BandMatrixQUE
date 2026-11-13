module

public import BlockBand.SourceProcess.FullSourceStops.PolyEval
public import BlockBand.SourceProcess.FullSourceStops.LoadMoments
public import BlockBand.SourceProcess.FullSourceStops.Interface

/-!
# Second moments of the compensator coefficients

`compensatorCoefficientMoments_holds`: the coefficients `𝒜_tΦ` and `Γ(Φ)` of the compensator,
evaluated along the path, have bounded second moments uniformly on the bulk. Hypotheses:
`MatchedTracesContract`, `GaussianAbsorptionContract`, `ScalarRecursionContract` and
`GaussianLpGradient`.

Proof. `𝒜_tΦ = D₀ · genCore Φ + Σ_w inj_w(t) ∂_wΦ` and `Γ(Φ) = D₀ · carreCore Φ`
(`PolyAlgebra`), where `genCore Φ`, `carreCore Φ`, `∂_wΦ` are fixed polynomials in ordinary words.
On the bulk, `0 ≤ D₀ ≤ 2/(bκI²)`, and `|inj_w(t)| ≤ d_*Q` with `0 ≤ q_a ≤ Q`. Almost surely every
such polynomial is at most `polyConst · L_j^{polyExp}` (`PolyEval`), so both coefficients are at
most `K · L_j^N` with `K, N` independent of `W, E, k, j`. Then `E|·|² ≤ K² E L_j^{2N} ≤ K²C`
(`LoadMoments`). Only `L^{1+δ}` is needed later; the statement gives second moments.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceStops

open MeasureTheory MvPolynomial
open BlockBand.Internal.Contracts.Inputs BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal

variable {nT nI : ℕ}

theorem transportD0_bulk {b κ E : ℝ} (hb : 0 < b) (hκ : 0 < κ) (hE : E ∈ bulkInterval κ) :
    0 ≤ transportD0 b E ∧ transportD0 b E ≤ 2 / (b * κ ^ 2) := by
  obtain ⟨h1, h2⟩ := hE
  have hk : κ ^ 2 ≤ 4 - E ^ 2 := by nlinarith
  have hpos : 0 < b * κ ^ 2 := by positivity
  refine ⟨div_nonneg (by norm_num) (by nlinarith), ?_⟩
  rw [transportD0]
  exact div_le_div_of_nonneg_left (by norm_num) hpos (mul_le_mul_of_nonneg_left hk hb.le)

theorem intervalTests_bounded {q : Fin nI → ℝ → ℝ} (hq : IsIntervalTests q) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ a x, 0 ≤ q a x ∧ q a x ≤ Q := by
  choose Qa hQa using fun a => (hq a).elim fun s h => h.elim fun T h => intervalTest_bounded h
  refine ⟨∑ a, Qa a, Finset.sum_nonneg fun a _ => (hQa a).1, fun a x => ⟨((hQa a).2 x).1, ?_⟩⟩
  exact ((hQa a).2 x).2.trans (Finset.single_le_sum (fun a _ => (hQa a).1) (Finset.mem_univ a))

theorem dStar_pos {b : ℝ} (hb : b < 1) : 0 < dStar b := by
  rw [dStar]; exact one_div_pos.mpr (by linarith)

theorem norm_wordInjection_le {b : ℝ} (hb : b < 1) {q : Fin nI → ℝ → ℝ} {Q : ℝ} (hQ0 : 0 ≤ Q)
    (hQ : ∀ a x, 0 ≤ q a x ∧ q a x ≤ Q) (t : ℝ) (w : TraceWord nT nI) :
    ‖wordInjection b q t w‖ ≤ dStar b * Q := by
  have hd := dStar_pos hb
  have h0 : 0 ≤ dStar b * Q := mul_nonneg hd.le hQ0
  unfold wordInjection
  split
  · split_ifs
    · rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hd.le (hQ _ t).1)]
      exact mul_le_mul_of_nonneg_left (hQ _ t).2 hd.le
    · simpa using h0
  · simpa using h0

/-- The exponent `N` of the coefficient bound. -/
def coefN (Φ : TracePoly nT nI) : ℕ :=
  polyExp (genCore Φ) + polyExp (carreCore Φ) + ∑ w ∈ Φ.vars, polyExp (pderiv w Φ) + 1

/-- The constant `K` of the coefficient bound (`D₀ ≤ 2/(bκI²)`, `|inj| ≤ d_*Q`). -/
def coefK (b κI Q : ℝ) (Φ : TracePoly nT nI) : ℝ :=
  2 / (b * κI ^ 2) * polyConst (genCore Φ) +
    dStar b * Q * ∑ w ∈ Φ.vars, polyConst (pderiv w Φ) + 2 / (b * κI ^ 2) * polyConst (carreCore Φ)

theorem coefK_nonneg {b κI Q : ℝ} (hb0 : 0 < b) (hb : b < 1) (hκ : 0 < κI) (hQ0 : 0 ≤ Q)
    (Φ : TracePoly nT nI) : 0 ≤ coefK b κI Q Φ := by
  have hD : 0 ≤ 2 / (b * κI ^ 2) := by positivity
  have hd := (dStar_pos hb).le
  unfold coefK
  have := polyConst_nonneg (genCore Φ)
  have := polyConst_nonneg (carreCore Φ)
  have : 0 ≤ ∑ w ∈ Φ.vars, polyConst (pderiv w Φ) :=
    Finset.sum_nonneg fun w _ => polyConst_nonneg _
  positivity

variable {W : ℕ}

/-- **Almost-sure coefficient bounds**: `|𝒜_tΦ(Z_j)|, |Γ(Φ)(Z_j)| ≤ K L_j^N`, for every `j`, `k`,
`t`. -/
theorem ae_coefficients_le {b E κI : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κI)
    (hE : E ∈ bulkInterval κI) (hW : 1 ≤ W) (q : Fin nI → ℝ → ℝ) (hq : IsIntervalTests q)
    {Q : ℝ} (hQ0 : 0 ≤ Q) (hQ : ∀ a x, 0 ≤ q a x ∧ q a x ≤ Q)
    (Φ : TracePoly nT nI) (hΦ : IsOrdinaryPoly Φ) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ (j : ℕ) (k : Fin nT → ℕ) (t : ℝ),
      1 ≤ wordLoad b E k q W j ω ∧
      ‖polyValue b E k q W j ω (wordGenerator b E q t Φ)‖ ≤
        coefK b κI Q Φ * wordLoad b E k q W j ω ^ coefN Φ ∧
      ‖polyValue b E k q W j ω (wordCarre b E Φ)‖ ≤
        coefK b κI Q Φ * wordLoad b E k q W j ω ^ coefN Φ := by
  have hE1 : -2 < E := by have := hE.1; linarith
  have hE2 : E < 2 := by have := hE.2; linarith
  filter_upwards [ae_norm_polyValue_ord_le hb hE1 hE2 hW q hq,
    one_le_wordLoad_ae (nT := nT) hb hE1 hE2 hW q hq] with ω hP hL j k t
  set L := wordLoad b E k q W j ω
  set N := coefN Φ
  set D := 2 / (b * κI ^ 2)
  have hL1 : 1 ≤ L := hL j k
  have hLN : 0 ≤ L ^ N := by positivity
  obtain ⟨hD0, hD1⟩ := transportD0_bulk hb0 hκ hE
  have hd := (dStar_pos (b := b) (by linarith)).le
  have hm := mem_ordPoly_of_isOrdinaryPoly hΦ
  have hG := (hP j k _ (genCore_mem hΦ)).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hL1 (show polyExp (genCore Φ) ≤ N by simp only [N, coefN]; omega))
    (polyConst_nonneg _))
  have hC := (hP j k _ (carreCore_mem hΦ)).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hL1 (show polyExp (carreCore Φ) ≤ N by simp only [N, coefN]; omega))
    (polyConst_nonneg _))
  have hpd : ∀ w ∈ Φ.vars, ‖polyValue b E k q W j ω (pderiv w Φ)‖ ≤
      polyConst (pderiv w Φ) * L ^ N := fun w hw => by
    refine (hP j k _ (pderiv_mem_supported hm w)).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hL1 ?_) (polyConst_nonneg _))
    have := Finset.single_le_sum (f := fun w => polyExp (pderiv w Φ)) (fun _ _ => Nat.zero_le _) hw
    simp only [N, coefN]; omega
  have hDC : ‖((transportD0 b E : ℝ) : ℂ)‖ ≤ D := by
    rw [Complex.norm_real, Real.norm_of_nonneg hD0]; exact hD1
  have hpcG := polyConst_nonneg (genCore Φ)
  have hpcC := polyConst_nonneg (carreCore Φ)
  have hsum : 0 ≤ ∑ w ∈ Φ.vars, polyConst (pderiv w Φ) :=
    Finset.sum_nonneg fun w _ => polyConst_nonneg _
  have expand : coefK b κI Q Φ * L ^ N = D * (polyConst (genCore Φ) * L ^ N) +
      dStar b * Q * (∑ w ∈ Φ.vars, polyConst (pderiv w Φ)) * L ^ N +
      D * (polyConst (carreCore Φ) * L ^ N) := by
    simp only [coefK, D]; ring
  have h3 : 0 ≤ D * (polyConst (carreCore Φ) * L ^ N) := by positivity
  have h1 : 0 ≤ D * (polyConst (genCore Φ) * L ^ N) := by positivity
  have h2 : 0 ≤ dStar b * Q * (∑ w ∈ Φ.vars, polyConst (pderiv w Φ)) * L ^ N := by positivity
  refine ⟨hL1, ?_, ?_⟩
  · have e : polyValue b E k q W j ω (wordGenerator b E q t Φ) =
        ((transportD0 b E : ℝ) : ℂ) * polyValue b E k q W j ω (genCore Φ) +
          ∑ w ∈ Φ.vars, wordInjection b q t w * polyValue b E k q W j ω (pderiv w Φ) := by
      simp only [polyValue, wordGenerator_eq, map_add, map_mul, eval_C, map_sum]
    have hI : ‖∑ w ∈ Φ.vars, wordInjection b q t w * polyValue b E k q W j ω (pderiv w Φ)‖ ≤
        dStar b * Q * (∑ w ∈ Φ.vars, polyConst (pderiv w Φ)) * L ^ N := by
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_le_sum fun w hw => ?_
      rw [norm_mul, mul_assoc]
      exact mul_le_mul (norm_wordInjection_le (by linarith) hQ0 hQ t w) (hpd w hw) (norm_nonneg _)
        (mul_nonneg hd hQ0)
    rw [e, expand]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    have := mul_le_mul hDC hG (norm_nonneg _) (by positivity)
    linarith
  · have e : polyValue b E k q W j ω (wordCarre b E Φ) =
        ((transportD0 b E : ℝ) : ℂ) * polyValue b E k q W j ω (carreCore Φ) := by
      simp only [polyValue, wordCarre_eq, map_mul, eval_C]
    rw [e, expand, norm_mul]
    have := mul_le_mul hDC hC (norm_nonneg _) (by positivity)
    linarith

/-- **`CompensatorCoefficientMoments`** from the input hypotheses `MatchedTracesContract`,
`GaussianAbsorptionContract`, `GaussianLpGradient` and `ScalarRecursionContract`. -/
theorem compensatorCoefficientMoments_holds (hMT : MatchedTracesContract)
    (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hSR : ScalarRecursionContract) : CompensatorCoefficientMoments := by
  intro b hb0 hb κI hκ nT nI q hq Φ hΦ ε T hε hεT
  obtain ⟨Q, hQ0, hQ⟩ := intervalTests_bounded hq
  set N := coefN Φ
  set K := coefK b κI Q Φ
  have hK0 : 0 ≤ K := coefK_nonneg hb0 (by linarith) hκ hQ0 Φ
  obtain ⟨CL, WL, hCL, hL⟩ := lintegral_wordLoad_pow_le hMT hGA hLp hSR b hb0 hb κI hκ nT nI q hq
    ε T hε hεT (2 * N) (by simp only [N, coefN]; omega)
  refine ⟨(ENNReal.ofReal (K ^ 2) * CL).toReal, max WL 1, fun W hW E hE k j hj1 hj2 => ?_⟩
  have hae := ae_coefficients_le hb0 hb hκ hE (le_of_max_le_right hW) q hq hQ0 hQ Φ hΦ
  have key : ∀ f : GrowthPath W → ℂ, (∀ᵐ ω ∂growthPathLaw W b, 1 ≤ wordLoad b E k q W j ω ∧
      ‖f ω‖ ≤ K * wordLoad b E k q W j ω ^ N) →
      ∫⁻ ω, ‖f ω‖ₑ ^ 2 ∂growthPathLaw W b ≤
        ENNReal.ofReal (ENNReal.ofReal (K ^ 2) * CL).toReal := by
    intro f hf
    rw [ENNReal.ofReal_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hCL)]
    calc ∫⁻ ω, ‖f ω‖ₑ ^ 2 ∂growthPathLaw W b
        ≤ ∫⁻ ω, ENNReal.ofReal (K ^ 2) * ENNReal.ofReal (wordLoad b E k q W j ω) ^ (2 * N)
            ∂growthPathLaw W b := by
          refine lintegral_mono_ae (hf.mono fun ω h => ?_)
          have hL0 : 0 ≤ wordLoad b E k q W j ω := zero_le_one.trans h.1
          rw [← ofReal_norm]
          calc ENNReal.ofReal ‖f ω‖ ^ 2 ≤ ENNReal.ofReal (K * wordLoad b E k q W j ω ^ N) ^ 2 :=
                pow_le_pow_left₀ zero_le (ENNReal.ofReal_le_ofReal h.2) 2
            _ = _ := by
                rw [ENNReal.ofReal_mul hK0, ENNReal.ofReal_pow hL0, ENNReal.ofReal_pow hK0]; ring
      _ = ENNReal.ofReal (K ^ 2) * ∫⁻ ω, ENNReal.ofReal (wordLoad b E k q W j ω) ^ (2 * N)
            ∂growthPathLaw W b := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (K ^ 2) * CL :=
          mul_le_mul_right (hL W (le_of_max_le_left hW) E hE k j hj1 hj2) _
  refine ⟨measurable_polyValue b E k q j _, measurable_polyValue b E k q j _,
    key _ (hae.mono fun ω h => ⟨(h j k 0).1, (h j k _).2.1⟩),
    key _ (hae.mono fun ω h => ⟨(h j k 0).1, (h j k 0).2.2⟩)⟩

end BlockBand.SourceProcess.FullSourceStops
