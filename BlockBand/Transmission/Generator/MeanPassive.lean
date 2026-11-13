module

public import BlockBand.Transmission.Generator.MeanBulk

/-!
# `ubarMean_bulk`: the one-layer mean `Ū`, every passive input, bulk-uniform

* `ubarMean_strict_bulk`: strictly passive inputs (`ub_on`/`ub_off`);
* **`ubarMean_bulk`**: every passive input (`regX` limit, `G` fixed);
* `weightedMean_bulk`: the real part of the weighted refined mean, the form used by the `k ≥ 2`
  drift.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PathScalar
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.LengthUniform
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- **Strictly passive inputs, bulk-uniform.** -/
theorem ubarMean_strict_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef →
        ‖matrixExpect (freshLaw W b) (freshU b E X) - ((meanC b E X : ℝ) : ℂ) • 1‖ ≤
            C * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2 + passiveMass b E X / W) ∧
          ∀ G : Matrix (Fin W) (Fin W) ℂ, G.PosSemidef →
            ‖(G * matrixExpect (freshLaw W b) (freshU b E X)).trace -
              ((meanC b E X : ℝ) : ℂ) * G.trace‖ ≤ C * wmErr b E X G := by
  obtain ⟨Cf, Wf, hCf, hF⟩ := freshU_mean_bulk hA hb0 hb hκ
  obtain ⟨C2, W2, hC2, hS1⟩ := scalarS1_bulk hA hb0 hb hκ
  obtain ⟨CD, WD, hCD, hD⟩ := dressedBlocks_bulk hA hb0 hb hκ
  obtain ⟨d₀, Cm, Wm, hd₀, hCm, hm0⟩ := mm_matched0_bulk hA hb0 hb hκ
  have hηL : 0 < etaLow b κ := etaLow_pos (by linarith) hκ
  set Li := (etaLow b κ)⁻¹
  have hLi0 : 0 ≤ Li := (inv_pos.mpr hηL).le
  set d₁ := min d₀ (min (1 / (4 * (Cm + 1) * (Li + 1))) (1 / 2))
  have hd₁ : 0 < d₁ := lt_min hd₀ (lt_min (by positivity) (by norm_num))
  have hd₁0 : d₁ ≤ d₀ := min_le_left _ _
  have hd₁m : d₁ ≤ 1 / (4 * (Cm + 1) * (Li + 1)) := (min_le_right _ _).trans (min_le_left _ _)
  set K := ubK Cf C2 CD Cm Li b d₁
  have hK0 : 0 ≤ K := by unfold K ubK; positivity
  have hK1 : (Cf * Cf * Cf + Cf + 1) / d₁ ≤ K := by
    have : 0 ≤ (Cf + (3 * C2 + Cf * (2 * CD)) * (9 / 2 * Li / b)) + 4 * Cm +
      (Cm ^ 2 * Li ^ 2 + 2 * Cm * (Cm * (2 * Li * CD + CD ^ 2))) +
      (4 * Li / b * (4 * Cm * Li + Cm * (2 * Li * CD + CD ^ 2)) + 2 * Cm * Li / b) +
      (Cf * Cf * Cf + Cf + 1) / d₁ ^ 2 := by positivity
    have : 0 ≤ (Cf + (3 * C2 + Cf * (2 * CD)) * (2 * Li / b)) + (Cf * (5 / 2 * Cm) + Cm * Li) +
      10 * Li / b := by positivity
    unfold K ubK; linarith
  have hK2 : (Cf * Cf * Cf + Cf + 1) / d₁ ^ 2 ≤ K := by
    have : 0 ≤ (Cf + (3 * C2 + Cf * (2 * CD)) * (9 / 2 * Li / b)) + 4 * Cm +
      (Cm ^ 2 * Li ^ 2 + 2 * Cm * (Cm * (2 * Li * CD + CD ^ 2))) +
      (4 * Li / b * (4 * Cm * Li + Cm * (2 * Li * CD + CD ^ 2)) + 2 * Cm * Li / b) := by
      positivity
    have : 0 ≤ (Cf + (3 * C2 + Cf * (2 * CD)) * (2 * Li / b)) + (Cf * (5 / 2 * Cm) + Cm * Li) +
      10 * Li / b + (Cf * Cf * Cf + Cf + 1) / d₁ := by positivity
    unfold K ubK; linarith
  refine ⟨K, max (max (max Wf W2) (max WD Wm)) ⌈d₁⁻¹⌉₊, hK0, fun W hW E hE X hX => ?_⟩
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hLi : (etaZ b E)⁻¹ ≤ Li := inv_anti₀ hηL (etaLow_le (by linarith) hκ hE)
  have hz2 : ‖boundaryZ b E‖ ≤ 2 := bulk_norm_z hb0 hb hκ hE
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hWf, hW2⟩, hWD, hWm⟩, hWd⟩ := hW
  have hY := hX.posSemidef
  obtain ⟨hKMn, hsn, hU⟩ := hF W hWf E hE X hX
  obtain ⟨hW1, -, hM, -, -, -, hB0, hB1, hG, hzM, -⟩ := hD W hWD E hE X hX
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW1
  have hW1r : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hq : 0 ≤ passiveMass b E X := passiveMass_nonneg b E hY
  have hδ : 0 ≤ jetDistance0 b E X := norm_nonneg _
  set e := jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2
  have he0 : 0 ≤ e := by positivity
  have hWe : (W : ℝ)⁻¹ ^ 2 ≤ e := le_add_of_nonneg_left hδ
  obtain ⟨hc0, hc1⟩ := meanC_pos_le hb0 hb h1 h2 hY
  have hErr : ∀ G : Matrix (Fin W) (Fin W) ℂ, wmErr b E X G = e * ‖(G * passiveF b E X).trace‖ +
      e ^ 2 * G.trace.re + e * passiveMass b E X * G.trace.re / W + (W : ℝ)⁻¹ ^ 2 * G.trace.re :=
    fun G => rfl
  by_cases hdom : jetDistance0 b E X ≤ d₁
  swap
  · push Not at hdom
    have hUn : ‖matrixExpect (freshLaw W b) (freshU b E X)‖ ≤ Cf * Cf * Cf + Cf := by
      have h := norm_add_le (matrixExpect (freshLaw W b) (freshU b E X) -
        sOne b E X • (kmOf b E X * (kmOf b E X)ᴴ)) (sOne b E X • (kmOf b E X * (kmOf b E X)ᴴ))
      rw [sub_add_cancel] at h
      have h2' : ‖sOne b E X • (kmOf b E X * (kmOf b E X)ᴴ)‖ ≤ Cf * (Cf * Cf) := by
        refine (norm_smul_le _ _).trans (mul_le_mul hsn ?_ (norm_nonneg _) hCf)
        refine (Matrix.l2_opNorm_mul _ _).trans ?_
        rw [Matrix.l2_opNorm_conjTranspose]; exact mul_le_mul hKMn hKMn (norm_nonneg _) hCf
      have h3 : Cf / (W : ℝ) ^ 2 ≤ Cf := div_le_self hCf (one_le_pow₀ hW1r)
      linarith
    have hde : d₁ ≤ e := le_add_of_le_of_nonneg hdom.le (by positivity)
    obtain ⟨ha, hb'⟩ := ub_off hUn hc0 hc1 hd₁ hde hK1 hK2 (div_nonneg hq hWpos.le)
    refine ⟨ha, fun G hGp => ?_⟩
    have hg0 := (mm_trace_posSemidef hGp).1
    rw [hErr]
    have := hb' G hGp (e * ‖(G * passiveF b E X).trace‖ + e * passiveMass b E X * G.trace.re / W +
      (W : ℝ)⁻¹ ^ 2 * G.trace.re) (by positivity)
    refine this.trans (le_of_eq ?_); ring
  have hWinv : (W : ℝ)⁻¹ ≤ d₁ := by
    rw [inv_le_comm₀ hWpos hd₁]; exact (Nat.le_ceil _).trans (by exact_mod_cast hWd)
  have hWsq : (W : ℝ)⁻¹ ^ 2 ≤ d₁ := rf_Wsq hW1r hWinv
  have he2 : e ≤ 2 * (1 / (4 * (Cm + 1) * (Li + 1))) := by simp only [e]; linarith
  have hCmLi := rf_CmLi hCm hLi0
  have hCme : Cm * e ≤ 1 / 2 := (mul_le_mul_of_nonneg_left he2 hCm).trans hCmLi.1
  have hCmeLi : Cm * e * Li ≤ 1 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he2 hCm) hLi0).trans hCmLi.2
  obtain ⟨hzζ, hKM1, hh1⟩ := hm0 W hWm E hE X hX (hdom.trans hd₁0)
  have hheq : hOf b E X - 1 = ((Complex.normSq (vOf b E X) - 1 : ℝ) : ℂ) := by
    simp only [hOf, Complex.mul_conj]; push_cast; ring
  have hh1' : |Complex.normSq (vOf b E X) - 1| ≤ Cm * e := by
    rw [hheq, Complex.norm_real, Real.norm_eq_abs] at hh1; exact hh1
  obtain ⟨ha, hb'⟩ := ub_on hb0 hb h1 h2 hW1 hX hC2 hd₁.le hCm hCD he0 hWe hLi hCme hCmeLi hzζ
    hKM1 hh1' hz2 hU hsn hM hG hB0 hB1 hzM (hS1 W hW2 E hE X hX).2.2
  exact ⟨ha, fun G hGp => by rw [hErr]; exact hb' G hGp⟩

theorem tendsto_meanC_regX {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    {X : Matrix (Fin W) (Fin W) ℂ} (hX : (passiveY X).PosSemidef) :
    Tendsto (fun n => meanC b E (PassiveCovariance.regX X n)) atTop (𝓝 (meanC b E X)) := by
  have tq := tendsto_mass_regX hb0 hb h1 h2 hX
  have hden : Tendsto (fun n => 1 + alphaCoef b E * passiveMass b E (PassiveCovariance.regX X n) / W)
      atTop (𝓝 (1 + alphaCoef b E * passiveMass b E X / W)) :=
    tendsto_const_nhds.add ((tq.const_mul _).div_const _)
  have hne : 1 + alphaCoef b E * passiveMass b E X / W ≠ 0 := by
    have := (meanC_pos_le hb0 hb h1 h2 hX).1
    rw [meanC] at this; exact (inv_pos.mp this).ne'
  exact hden.inv₀ hne

/-- **`Ū` bounds, every passive input, bulk-uniform** (`regX` limit of the strict case). -/
theorem ubarMean_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
        ‖matrixExpect (freshLaw W b) (freshU b E X) - ((meanC b E X : ℝ) : ℂ) • 1‖ ≤
            C * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2 + passiveMass b E X / W) ∧
          ∀ G : Matrix (Fin W) (Fin W) ℂ, G.PosSemidef →
            ‖(G * matrixExpect (freshLaw W b) (freshU b E X)).trace -
              ((meanC b E X : ℝ) : ℂ) * G.trace‖ ≤ C * wmErr b E X G := by
  obtain ⟨C, W₀, hC, hS⟩ := ubarMean_strict_bulk hA hb0 hb hκ
  obtain ⟨W₁, hT⟩ := mm_tendsto_EU_bulk hA hb0 hb hκ
  refine ⟨C, max W₀ W₁, hC, fun W hW E hE X hX => ?_⟩
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  set Xn := PassiveCovariance.regX X
  have tq := tendsto_mass_regX hb0 hb h1 h2 hX
  have tQ := tendsto_Q_regX hb0 hb h1 h2 hX
  have tR := tendsto_res_regX hb0 hb h1 h2 hX
  have tδ := tendsto_jet0_regX hb0 hb h1 h2 hX
  have tU := hT W (le_trans (le_max_right _ _) hW) E hE X hX
  have tc := tendsto_meanC_regX hb0 hb h1 h2 hX
  have tcC : Tendsto (fun n => ((meanC b E (Xn n) : ℝ) : ℂ)) atTop (𝓝 ((meanC b E X : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp tc
  have tF : Tendsto (fun n => passiveF b E (Xn n)) atTop (𝓝 (passiveF b E X)) := tR.sub_const _
  have hS' := fun n => hS W (le_trans (le_max_left _ _) hW) E hE (Xn n) (passiveY_regX_posDef hX n)
  refine ⟨?_, fun G hGp => ?_⟩
  · have hL : Tendsto (fun n => ‖matrixExpect (freshLaw W b) (freshU b E (Xn n)) -
        ((meanC b E (Xn n) : ℝ) : ℂ) • 1‖) atTop
        (𝓝 ‖matrixExpect (freshLaw W b) (freshU b E X) - ((meanC b E X : ℝ) : ℂ) • 1‖) :=
      (tU.sub (tcC.smul_const _)).norm
    have hR : Tendsto (fun n => C * (jetDistance0 b E (Xn n) + (W : ℝ)⁻¹ ^ 2 +
        passiveMass b E (Xn n) / W)) atTop
        (𝓝 (C * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2 + passiveMass b E X / W))) :=
      (((tδ.add_const _).add (tq.div_const _))).const_mul _
    exact le_of_tendsto_of_tendsto' hL hR fun n => (hS' n).1
  · have hL : Tendsto (fun n => ‖(G * matrixExpect (freshLaw W b) (freshU b E (Xn n))).trace -
        ((meanC b E (Xn n) : ℝ) : ℂ) * G.trace‖) atTop
        (𝓝 ‖(G * matrixExpect (freshLaw W b) (freshU b E X)).trace -
          ((meanC b E X : ℝ) : ℂ) * G.trace‖) :=
      (((continuous_id.matrix_trace.tendsto _).comp (tendsto_const_nhds.mul tU)).sub
        (tcC.mul_const _)).norm
    have te : Tendsto (fun n => jetDistance0 b E (Xn n) + (W : ℝ)⁻¹ ^ 2) atTop
        (𝓝 (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2)) := tδ.add_const _
    have tτ : Tendsto (fun n => ‖(G * passiveF b E (Xn n)).trace‖) atTop
        (𝓝 ‖(G * passiveF b E X).trace‖) :=
      ((continuous_id.matrix_trace.tendsto _).comp (tendsto_const_nhds.mul tF)).norm
    have tErr : Tendsto (fun n => wmErr b E (Xn n) G) atTop (𝓝 (wmErr b E X G)) := by
      unfold wmErr
      exact (((te.mul tτ).add ((te.pow 2).mul_const _)).add
        (((te.mul tq).mul_const _).div_const _)).add tendsto_const_nhds
    exact le_of_tendsto_of_tendsto' hL (tErr.const_mul C) fun n => (hS' n).2 G hGp

/-- **The weighted refined mean**, real part:
`|Re Tr(GŪ) - c·Re Tr G| ≤ C·wmErr` for every `G ⪰ 0`. -/
theorem weightedMean_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ∀ G : Matrix (Fin W) (Fin W) ℂ, G.PosSemidef →
        |(G * matrixExpect (freshLaw W b) (freshU b E X)).trace.re -
          meanC b E X * G.trace.re| ≤ C * wmErr b E X G := by
  obtain ⟨C, W₀, hC, h⟩ := ubarMean_bulk hA hb0 hb hκ
  refine ⟨C, W₀, hC, fun W hW E hE X hX G hG => ?_⟩
  refine le_trans (le_of_eq ?_) ((Complex.abs_re_le_norm _).trans ((h W hW E hE X hX).2 G hG))
  simp [Complex.sub_re, Complex.mul_re]

end BlockBand.Transmission.Generator
