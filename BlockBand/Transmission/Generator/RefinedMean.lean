module

public import BlockBand.Transmission.Generator.RefinedStrict
public import BlockBand.Transmission.LengthUniform.BulkMassMean

/-!
# The refined (`Ω`-linear) mass mean, every passive input, bulk-uniform

Hypothesis `PassiveBoundsStatement`; law `freshLaw W b` of one fresh layer.

**`massMeanRefined_bulk`**: `b ∈ (0,1/2)`, `κ > 0` first; then `C, W₀`; for `W ≥ W₀`,
`E ∈ bulkInterval κ` and every deterministic passive `X` (`Y ⪰ 0`), one fresh layer:
`|Re Tr(Q E[LL*]) - q/(1+αq/W)| ≤ C·refinedErr`, with
`refinedErr = e|Tr(Qf)| + e²q + eq²/W + W⁻²q`, `e = δ₀ + W⁻²`.
`massMeanRefined_strict_bulk` is the strictly passive case; the passive case is its `regX` limit
(as `LengthUniform.massMean_holds_bulk`).
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

theorem rf_Wsq {W : ℕ} {d : ℝ} (hW1 : (1 : ℝ) ≤ W) (h : (W : ℝ)⁻¹ ≤ d) : (W : ℝ)⁻¹ ^ 2 ≤ d :=
  (pow_le_of_le_one (inv_nonneg.mpr (by linarith)) (inv_le_one_of_one_le₀ hW1)
    two_ne_zero).trans h

theorem rf_CmLi {Cm Li : ℝ} (hCm : 0 ≤ Cm) (hLi : 0 ≤ Li) :
    Cm * (2 * (1 / (4 * (Cm + 1) * (Li + 1)))) ≤ 1 / 2 ∧
      Cm * (2 * (1 / (4 * (Cm + 1) * (Li + 1)))) * Li ≤ 1 := by
  have hp : 0 < 4 * (Cm + 1) * (Li + 1) := by positivity
  constructor
  · rw [mul_one_div, ← mul_div_assoc, div_le_iff₀ hp]; nlinarith
  · rw [mul_one_div, ← mul_div_assoc, div_mul_eq_mul_div, div_le_iff₀ hp]; nlinarith

/-- **Refined mass mean, strictly passive inputs, bulk-uniform.** -/
theorem massMeanRefined_strict_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosDef →
        |(passiveQ b E X * matrixExpect (freshLaw W b) (freshU b E X)).trace.re -
            passiveMass b E X / (1 + alphaCoef b E * passiveMass b E X / W)| ≤
          C * refinedErr b E X := by
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
  set C₁ := Cf * Cf * Cf + Cf
  set KR := Cm * (2 * Li * CD + CD ^ 2)
  set K₀ := Cf + (3 * C2 + Cf * (2 * CD)) * (9 / 2 * Li / b)
  set K₂ := Cm ^ 2 * Li ^ 2 + 2 * Cm * KR
  set K₃ := 4 * Li / b * (4 * Cm * Li + KR) + 2 * Cm * Li / b
  set K₄ := (C₁ + 1) / d₁ ^ 2
  refine ⟨K₀ + 4 * Cm + K₂ + K₃ + K₄, max (max (max Wf W2) (max WD Wm)) ⌈d₁⁻¹⌉₊,
    by positivity, fun W hW E hE X hX => ?_⟩
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
  set Q := passiveQ b E X
  set q := passiveMass b E X
  set U := matrixExpect (freshLaw W b) (freshU b E X)
  set δ := jetDistance0 b E X
  set e := δ + (W : ℝ)⁻¹ ^ 2
  set τ := ‖(Q * passiveF b E X).trace‖
  have hQ : Q.PosSemidef := hY.conjTranspose_mul_mul_same _
  have hq : 0 ≤ q := passiveMass_nonneg b E hY
  have hδ : 0 ≤ δ := norm_nonneg _
  have he0 : 0 ≤ e := by positivity
  have hτ0 : 0 ≤ τ := norm_nonneg _
  have hErr : refinedErr b E X = e * τ + e ^ 2 * q + e * q ^ 2 / W + (W : ℝ)⁻¹ ^ 2 * q := rfl
  rw [hErr]
  have hEa : 0 ≤ e * τ := by positivity
  have hEb : 0 ≤ e ^ 2 * q := by positivity
  have hEc : 0 ≤ e * q ^ 2 / W := by positivity
  have hEd : 0 ≤ (W : ℝ)⁻¹ ^ 2 * q := by positivity
  have hK0 : 0 ≤ K₀ := by positivity
  have hK2 : 0 ≤ K₂ := by positivity
  have hK3 : 0 ≤ K₃ := by positivity
  have hK4 : 0 ≤ K₄ := by positivity
  have hsplit : (K₀ + 4 * Cm + K₂ + K₃ + K₄) * (e * τ + e ^ 2 * q + e * q ^ 2 / W +
      (W : ℝ)⁻¹ ^ 2 * q) = K₀ * ((W : ℝ)⁻¹ ^ 2 * q) + 4 * Cm * (e * τ) + K₂ * (e ^ 2 * q) +
      K₃ * (e * q ^ 2 / W) + (K₄ * (e ^ 2 * q) + (K₀ * (e * τ + e ^ 2 * q + e * q ^ 2 / W) +
      4 * Cm * (e ^ 2 * q + e * q ^ 2 / W + (W : ℝ)⁻¹ ^ 2 * q) +
      K₂ * (e * τ + e * q ^ 2 / W + (W : ℝ)⁻¹ ^ 2 * q) +
      K₃ * (e * τ + e ^ 2 * q + (W : ℝ)⁻¹ ^ 2 * q) +
      K₄ * (e * τ + e * q ^ 2 / W + (W : ℝ)⁻¹ ^ 2 * q))) := by ring
  rw [hsplit]
  have hrest : 0 ≤ K₀ * (e * τ + e ^ 2 * q + e * q ^ 2 / W) +
      4 * Cm * (e ^ 2 * q + e * q ^ 2 / W + (W : ℝ)⁻¹ ^ 2 * q) +
      K₂ * (e * τ + e * q ^ 2 / W + (W : ℝ)⁻¹ ^ 2 * q) +
      K₃ * (e * τ + e ^ 2 * q + (W : ℝ)⁻¹ ^ 2 * q) +
      K₄ * (e * τ + e * q ^ 2 / W + (W : ℝ)⁻¹ ^ 2 * q) := by positivity
  have hK4E : 0 ≤ K₄ * (e ^ 2 * q) := by positivity
  by_cases hdom : δ ≤ d₁
  swap
  · -- off the domain
    push Not at hdom
    have hUn : ‖U‖ ≤ C₁ := by
      have h := norm_add_le (U - sOne b E X • (kmOf b E X * (kmOf b E X)ᴴ))
        (sOne b E X • (kmOf b E X * (kmOf b E X)ᴴ))
      rw [sub_add_cancel] at h
      have h2' : ‖sOne b E X • (kmOf b E X * (kmOf b E X)ᴴ)‖ ≤ Cf * (Cf * Cf) := by
        refine (norm_smul_le _ _).trans (mul_le_mul hsn ?_ (norm_nonneg _) hCf)
        refine (Matrix.l2_opNorm_mul _ _).trans ?_
        rw [Matrix.l2_opNorm_conjTranspose]; exact mul_le_mul hKMn hKMn (norm_nonneg _) hCf
      have h3 : Cf / (W : ℝ) ^ 2 ≤ Cf := div_le_self hCf (one_le_pow₀ hW1r)
      simp only [C₁]; linarith
    have hcr : |(Q * U).trace.re| ≤ C₁ * q := by
      rw [trace_mul_comm]
      exact (Complex.abs_re_le_norm _).trans ((norm_trace_mul_posSemidef_le hQ U).trans
        (mul_le_mul_of_nonneg_right hUn hq))
    have hα : 0 ≤ alphaCoef b E := by
      rw [alphaCoef]; have : 0 < b * etaZ b E := mul_pos hb0 hη; positivity
    have hB : |q / (1 + alphaCoef b E * q / W)| ≤ q := by
      rw [abs_of_nonneg (by positivity)]
      exact div_le_self hq (by have : 0 ≤ alphaCoef b E * q / W := by positivity
                               linarith)
    have hde1 : d₁ ≤ e := le_add_of_le_of_nonneg hdom.le (by positivity)
    have hde : d₁ ^ 2 ≤ e ^ 2 := pow_le_pow_left₀ hd₁.le hde1 2
    have hK4q : (C₁ + 1) * q ≤ K₄ * (e ^ 2 * q) := by
      simp only [K₄]
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      have : 0 ≤ (C₁ + 1) * q := by positivity
      have h5 : (C₁ + 1) * q * d₁ ^ 2 ≤ (C₁ + 1) * q * e ^ 2 := mul_le_mul_of_nonneg_left hde this
      linarith
    have := abs_sub ((Q * U).trace.re) (q / (1 + alphaCoef b E * q / W))
    have hon : 0 ≤ K₀ * ((W : ℝ)⁻¹ ^ 2 * q) + 4 * Cm * (e * τ) + K₂ * (e ^ 2 * q) +
      K₃ * (e * q ^ 2 / W) := by positivity
    linarith
  -- on the domain
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
  have hon : |(Q * U).trace.re - q / (1 + alphaCoef b E * q / W)| ≤
      K₀ * ((W : ℝ)⁻¹ ^ 2 * q) + 4 * Cm * (e * τ) + K₂ * (e ^ 2 * q) + K₃ * (e * q ^ 2 / W) :=
    rf_onDomain hb0 hb h1 h2 hW1 hX hCm hCD he0 hLi hCme hCmeLi hzζ hKM1 hh1' hz2 hU
    hsn hM hG hB0 hB1 hzM (hS1 W hW2 E hE X hX).2.2
  linarith only [hon, hrest, hK4E]

/-- **Refined mass mean, every passive input, bulk-uniform** (`regX` limit of the strict case). -/
theorem massMeanRefined_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
        |(passiveQ b E X * matrixExpect (freshLaw W b) (freshU b E X)).trace.re -
            passiveMass b E X / (1 + alphaCoef b E * passiveMass b E X / W)| ≤
          C * refinedErr b E X := by
  obtain ⟨C, W₀, hC, hS⟩ := massMeanRefined_strict_bulk hA hb0 hb hκ
  obtain ⟨W₁, hT⟩ := mm_tendsto_EU_bulk hA hb0 hb hκ
  refine ⟨C, max W₀ W₁, hC, fun W hW E hE X hX => ?_⟩
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  set Xn := PassiveCovariance.regX X
  have hη := etaZ_pos b E (by linarith) h1 h2
  have tq := tendsto_mass_regX hb0 hb h1 h2 hX
  have tQ := tendsto_Q_regX hb0 hb h1 h2 hX
  have tR := tendsto_res_regX hb0 hb h1 h2 hX
  have tδ := tendsto_jet0_regX hb0 hb h1 h2 hX
  have tU := hT W (le_trans (le_max_right _ _) hW) E hE X hX
  have hL : Tendsto (fun n => (passiveQ b E (Xn n) *
      matrixExpect (freshLaw W b) (freshU b E (Xn n))).trace.re) atTop
      (𝓝 ((passiveQ b E X * matrixExpect (freshLaw W b) (freshU b E X)).trace.re)) :=
    (Complex.continuous_re.tendsto _).comp ((continuous_id.matrix_trace.tendsto _).comp
      (tQ.mul tU))
  have hden : Tendsto (fun n => 1 + alphaCoef b E * passiveMass b E (Xn n) / W) atTop
      (𝓝 (1 + alphaCoef b E * passiveMass b E X / W)) :=
    tendsto_const_nhds.add ((tq.const_mul _).div_const _)
  have hne : 1 + alphaCoef b E * passiveMass b E X / W ≠ 0 := by
    have hα : 0 ≤ alphaCoef b E := by
      rw [alphaCoef]; have : 0 < b * etaZ b E := mul_pos hb0 hη; positivity
    have := passiveMass_nonneg b E hX; positivity
  have tF : Tendsto (fun n => passiveF b E (Xn n)) atTop (𝓝 (passiveF b E X)) :=
    tR.sub_const _
  have tτ : Tendsto (fun n => ‖(passiveQ b E (Xn n) * passiveF b E (Xn n)).trace‖) atTop
      (𝓝 ‖(passiveQ b E X * passiveF b E X).trace‖) :=
    ((continuous_id.matrix_trace.tendsto _).comp (tQ.mul tF)).norm
  have te : Tendsto (fun n => jetDistance0 b E (Xn n) + (W : ℝ)⁻¹ ^ 2) atTop
      (𝓝 (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2)) := tδ.add_const _
  have tErr : Tendsto (fun n => refinedErr b E (Xn n)) atTop (𝓝 (refinedErr b E X)) := by
    unfold refinedErr
    exact (((te.mul tτ).add ((te.pow 2).mul tq)).add ((te.mul (tq.pow 2)).div_const _)).add
      (tq.const_mul _)
  have hLR : Tendsto (fun n => |(passiveQ b E (Xn n) *
      matrixExpect (freshLaw W b) (freshU b E (Xn n))).trace.re -
        passiveMass b E (Xn n) / (1 + alphaCoef b E * passiveMass b E (Xn n) / W)|) atTop
      (𝓝 |(passiveQ b E X * matrixExpect (freshLaw W b) (freshU b E X)).trace.re -
        passiveMass b E X / (1 + alphaCoef b E * passiveMass b E X / W)|) :=
    (hL.sub (tq.div hden hne)).abs
  exact le_of_tendsto_of_tendsto' hLR (tErr.const_mul C) fun n =>
    hS W (le_trans (le_max_left _ _) hW) E hE (Xn n) (passiveY_regX_posDef hX n)

end BlockBand.Transmission.Generator
