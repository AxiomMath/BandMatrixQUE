module

public import BlockBand.Transmission.FractionalBulk.LayerIntegral
public import BlockBand.Transmission.LawClauses.EntryVarianceHolds
public import BlockBand.Transmission.PassiveLayer.TMMain

/-!
# The one-layer fractional step, uniformly on the bulk

Law `freshLaw W b` of one fresh layer, deterministic passive `X`, `T = T(X)`, `P = Tr T^p`,
`e = δ₀ + W⁻²`, `0 < p < 1`.

**`layerStep_bulk hGA hLp hP`**: `b, κ, p` first; then `C₀, C, c, d, γ, W₀` (no dependence on `E`);
for `W ≥ W₀`, `E ∈ bulkInterval κ`, every stationary jet `s` and passive `X`:
* `E stepFrac ≤ (1 + C₀) P` (always);
* if `δ₀ ≤ d`, `δ₁ ≤ d`, `g ≤ γW`:
  `E stepFrac ≤ (1 + C e) P - (c/W)(Σ_{t_i ≤ 1/2} t_i^p)²`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.FractionalBulk

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveCovariance
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.Generator
open scoped ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

theorem integral_re_bilinear {T : Matrix (Fin W) (Fin W) ℂ} (hT : T.PosSemidef) {b E : ℝ}
    {X : Matrix (Fin W) (Fin W) ℂ}
    (hU : ∀ x y, Integrable (fun ω => freshU b E X ω x y) (freshLaw W b)) (i : Fin W) :
    ∫ y, (bilinear (ts_vec hT i) (freshU b E X y) (ts_vec hT i)).re ∂freshLaw W b =
      (bilinear (ts_vec hT i) (matrixExpect (freshLaw W b) (freshU b E X)) (ts_vec hT i)).re := by
  have h := integral_re (𝕜 := ℂ) (integrable_bilinear_of hU (ts_vec hT i) (ts_vec hT i))
  refine h.trans ?_
  rw [SourceProcess.FullSource.integral_bilinear _ hU]
  rfl

/-- **The one-layer step.** -/
theorem layerStep_bulk (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C₀ C c d γ : ℝ) (W₀ : ℕ), 0 ≤ C₀ ∧ 0 ≤ C ∧ 0 < c ∧ 0 < d ∧ 0 < γ ∧
      ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ s : ℂ, IsStationaryJet b E s →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
        (∫ y, stepFrac p b E X y ∂freshLaw W b ≤
          (1 + C₀) * fracTrace p (passiveTransmission b E X)) ∧
        (jetDistance0 b E X ≤ d → jetDistance1 b E s X ≤ d →
          conductanceOf (passiveTransmission b E X) ≤ γ * W →
          ∫ y, stepFrac p b E X y ∂freshLaw W b ≤
            (1 + C * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2)) *
              fracTrace p (passiveTransmission b E X) -
            c / W * lowFrac p (passiveTransmission b E X) ^ 2) := by
  have hA := PassiveLayer.passiveBounds_holds hGA hLp
  obtain ⟨CL, WL, hCL, hL⟩ := layerMoments_bulk hA hb0 hb hκ
  obtain ⟨CB, WB, hCB, hB⟩ := layerBil4_bulk hA hb0 hb hκ
  obtain ⟨Cm, dm, Wm, hCm, hdm, hM⟩ := meanForm_bulk hA hb0 hb hκ
  obtain ⟨de, γ, ce, hde, hγ, hce, We, hEV⟩ := LawClauses.entryVariance_holds hGA hLp hP b hb0 hb κ hκ
  obtain ⟨WI, hI⟩ := LengthUniform.ml_integrable_U_bulk hA hb0 hb hκ
  have hcP := cP_pos hp0 hp1
  have hjP := jP_nonneg p
  set κ₀ := ce / (4 * max 1 (CB ^ 4 / ce ^ 2) + (1 + CL ^ 4) / 2) with hκ₀
  have hκ₀0 : 0 < κ₀ := by
    have : 0 < 4 * max 1 (CB ^ 4 / ce ^ 2) + (1 + CL ^ 4) / 2 := by
      have := le_max_left 1 (CB ^ 4 / ce ^ 2); positivity
    positivity
  refine ⟨cP p * jP p * CL ^ 4, cP p * jP p * Cm, cP p * κ₀ / 54, min de dm, γ,
    max (max (max WL WB) (max Wm We)) (max WI 1), by positivity, by positivity, by positivity,
    lt_min hde hdm, hγ, fun W hW E hE s hs X hX => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hWL, hWB⟩, hWm, hWe⟩, hWI, hW1⟩ := hW
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  have hT := passiveTransmission_posSemidef (by linarith : b < 1) h1 h2 hX
  have hU := hI W hWI E hE X hX
  obtain ⟨hL4i, hL4⟩ := hL W hWL E hE X hX
  obtain ⟨hAi, hint⟩ := layer_integral hp0 hp1 hb0 hb hW1 h1 h2 hX hT hU hL4i
  set t := ts_lam hT
  have hPeq : fracTrace p (passiveTransmission b E X) = ∑ i, t i ^ p := fracTrace_eq_sum_ts hT p
  have htp : ∀ i, 0 ≤ t i ^ p := fun i => Real.rpow_nonneg (ts_lam_nonneg hT i) p
  have hG0 : 0 ≤ ∑ i, ∑ j, ∫ y, gapG p hT b E X i j y ∂freshLaw W b :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      integral_nonneg fun y => gapG_nonneg p hT b E X i j y
  constructor
  · -- the global bound
    have hAle : ∀ i, (∫ y, (bilinear (ts_vec hT i) (freshU b E X y) (ts_vec hT i)).re
        ∂freshLaw W b) - 1 ≤ CL ^ 4 := by
      intro i
      have hpt : ∀ y, (bilinear (ts_vec hT i) (freshU b E X y) (ts_vec hT i)).re ≤
          1 + ‖freshL b E X y‖ ^ 4 := fun y => by
        have := (Complex.re_le_norm _).trans (norm_bilinear_freshU_le hT b E X i i y)
        nlinarith [sq_nonneg (‖freshL b E X y‖ ^ 2 - 1)]
      have := integral_mono (hAi i) (g := fun y => 1 + ‖freshL b E X y‖ ^ 4)
        ((integrable_const _).add hL4i) hpt
      rw [integral_add (integrable_const _) hL4i, integral_const] at this
      simp only [probReal_univ, smul_eq_mul, one_mul] at this
      linarith
    have hsum : ∑ i, t i ^ p * ((∫ y, (bilinear (ts_vec hT i) (freshU b E X y) (ts_vec hT i)).re
        ∂freshLaw W b) - 1) ≤ CL ^ 4 * ∑ i, t i ^ p := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => by
        rw [mul_comm (CL ^ 4)]; exact mul_le_mul_of_nonneg_left (hAle i) (htp i)
    rw [hPeq]
    have : 0 ≤ cP p * jP p := by positivity
    have := mul_le_mul_of_nonneg_left hsum this
    nlinarith
  · -- on the domain
    intro hd0 hd1 hg
    have hd0e : jetDistance0 b E X ≤ de := hd0.trans (min_le_left _ _)
    have hd1e : jetDistance1 b E s X ≤ de := hd1.trans (min_le_left _ _)
    have hd0m : jetDistance0 b E X ≤ dm := hd0.trans (min_le_right _ _)
    set e := jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2
    have hWpos : 0 < W := by omega
    have hWr : (0 : ℝ) < W := by exact_mod_cast hWpos
    -- the linear term
    have hAle : ∀ i, (∫ y, (bilinear (ts_vec hT i) (freshU b E X y) (ts_vec hT i)).re
        ∂freshLaw W b) - 1 ≤ Cm * e := by
      intro i
      rw [integral_re_bilinear hT hU i]
      have := hM W hWm E hE X hX hd0m (ts_vec hT i) (ts_vecNorm hT i)
      linarith
    have hsum : ∑ i, t i ^ p * ((∫ y, (bilinear (ts_vec hT i) (freshU b E X y) (ts_vec hT i)).re
        ∂freshLaw W b) - 1) ≤ Cm * e * ∑ i, t i ^ p := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => by
        rw [mul_comm (Cm * e)]; exact mul_le_mul_of_nonneg_left (hAle i) (htp i)
    -- the gap
    set a : Fin W → ℝ := fun i => if t i ≤ 1 / 2 then t i ^ p else 0 with ha
    have ha0 : ∀ i, 0 ≤ a i := fun i => by simp only [ha]; split_ifs; exacts [htp i, le_rfl]
    have hu := isOrthonormalEigenbasis_ts hT
    have hGij : ∀ i j, κ₀ / W * (if t i ≤ t j then a i * a j else 0) ≤
        ∫ y, gapG p hT b E X i j y ∂freshLaw W b := by
      intro i j
      have hGi0 : 0 ≤ ∫ y, gapG p hT b E X i j y ∂freshLaw W b :=
        integral_nonneg fun y => gapG_nonneg p hT b E X i j y
      by_cases hij : t i ≤ t j
      swap
      · rw [ite_eq_right hij, mul_zero]; exact hGi0
      by_cases htj : t j ≤ 1 / 2
      swap
      · have : a j = 0 := by simp only [ha]; rw [ite_eq_right htj]
        rw [ite_eq_left hij, this, mul_zero, mul_zero]; exact hGi0
      have hti : t i ≤ 1 / 2 := hij.trans htj
      have hai : a i = t i ^ p := by simp only [ha]; rw [ite_eq_left hti]
      have haj : a j = t j ^ p := by simp only [ha]; rw [ite_eq_left htj]
      rw [ite_eq_left hij, hai, haj]
      have hY2 := hEV W hWe E hE s hs X hX hd0e hd1e hg (ts_vec hT) (ts_lam hT) hu j i htj hti
      obtain ⟨hY4i, hY4⟩ := hB W hWB E hE X hX (ts_vec hT j) (ts_vec hT i) (ts_vecNorm hT j)
        (ts_vecNorm hT i)
      have hlow := entryGap_lower (u := ts_vec hT j) (v := ts_vec hT i)
        ((1 : Matrix (Fin W) (Fin W) ℂ) j i) hce hWpos hU hY2 hY4i hY4 hL4i hL4
      have heq : ∫ y, gapG p hT b E X i j y ∂freshLaw W b = t i ^ p * t j ^ p *
          ∫ y, ‖bilinear (ts_vec hT j) (freshU b E X y) (ts_vec hT i) -
            (1 : Matrix (Fin W) (Fin W) ℂ) j i‖ ^ 2 / weightN b E X y ∂freshLaw W b := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        rw [gapG, ite_eq_left hij]
      rw [heq]
      have hκeq : κ₀ / W = ce / W / (4 * max 1 (CB ^ 4 / ce ^ 2) + (1 + CL ^ 4) / 2) := by
        rw [hκ₀]; ring
      rw [hκeq]
      have := mul_le_mul_of_nonneg_left hlow (mul_nonneg (htp i) (htp j))
      linarith
    have hgap : κ₀ / W * ((∑ i, a i) ^ 2 / 2) ≤
        ∑ i, ∑ j, ∫ y, gapG p hT b E X i j y ∂freshLaw W b := by
      have h := half_sq_le a t ha0
      calc κ₀ / W * ((∑ i, a i) ^ 2 / 2) ≤
            κ₀ / W * ∑ i, ∑ j, (if t i ≤ t j then a i * a j else 0) :=
            mul_le_mul_of_nonneg_left h (by positivity)
        _ = ∑ i, ∑ j, κ₀ / W * (if t i ≤ t j then a i * a j else 0) := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => Finset.mul_sum _ _ _
        _ ≤ _ := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hGij i j
    have hlow : lowFrac p (passiveTransmission b E X) = ∑ i, a i := lowFrac_eq_sum hT p
    rw [hPeq, hlow]
    have hc1 : 0 ≤ cP p * jP p := by positivity
    have h3 := mul_le_mul_of_nonneg_left hsum hc1
    have h4 := mul_le_mul_of_nonneg_left hgap (show 0 ≤ cP p / 27 by positivity)
    have e5 : cP p * κ₀ / 54 / W * (∑ i, a i) ^ 2 = cP p / 27 * (κ₀ / W * ((∑ i, a i) ^ 2 / 2)) := by
      ring
    rw [e5]
    nlinarith

end BlockBand.Transmission.FractionalBulk
