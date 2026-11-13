module

public import BlockBand.Transmission.SourceMixing.MassMeanStrict
public import BlockBand.Transmission.PathScalar.MeanBulk
public import BlockBand.Transmission.LengthUniform.BulkScalarS1

/-!
# Bulk-uniform `q/W`-exact mass mean for strictly passive inputs

The mass mean bound `massMean_strict` for strictly passive inputs, uniformly in
`E ∈ bulkInterval κ`: the constants and `W₀` depend only on `b` and the bulk margin `κ`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LengthUniform

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PathScalar
open BlockBand.Transmission.SourceMixing
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- **Mass mean, strictly passive inputs.** Bulk-uniform copy of `massMean_strict`: the
`E`-dependent numbers `η = etaZ b E` and `I_z = ‖boundaryZ b E‖ + 1` of the original constant are
replaced by `etaLow b κ ≤ η` (`etaLow_le`) and `3` (`bulk_norm_z`). -/
theorem massMean_strict_bulk (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef →
        (passiveQ b E X * matrixExpect (freshLaw W b) (freshU b E X)).trace.re ≤
          passiveMass b E X / (1 + alphaCoef b E * passiveMass b E X / W) +
            C * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2) * passiveMass b E X := by
  obtain ⟨Cf, Wf, hCf, hF⟩ := freshU_mean_bulk hA hb0 hb hκ
  obtain ⟨C2, W2, hC2, hS1⟩ := scalarS1_bulk hA hb0 hb hκ
  obtain ⟨CD, WD, hCD, hD⟩ := dressedBlocks_bulk hA hb0 hb hκ
  obtain ⟨d₀, Cm, Wm, hd₀, hCm, hm0⟩ := mm_matched0_bulk hA hb0 hb hκ
  set c := 1 - 2 * b
  have hc : 0 ≤ c := by simp only [c]; linarith
  set d₁ := min d₀ (min (1 / (4 * Cm + 4)) (1 / 2))
  have hd₁ : 0 < d₁ := lt_min hd₀ (lt_min (by positivity) (by norm_num))
  have hd₁0 : d₁ ≤ d₀ := min_le_left _ _
  have hd₁m : d₁ ≤ 1 / (4 * Cm + 4) := (min_le_right _ _).trans (min_le_left _ _)
  have hd₁h : d₁ ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  set C₁ := Cf * Cf * Cf + Cf
  -- uniform constants: `η = etaZ b E ≥ ηL = etaLow b κ`, `‖boundaryZ b E‖ + 1 ≤ 3`
  set ηL := etaLow b κ with hηLdef
  have hηL : 0 < ηL := etaLow_pos (by linarith) hκ
  set KhL := c / b * 2 * Cm / (4 * ηL ^ 2) with hKhL
  set CmainL := Cm / ηL + 2 * Cm + Cm ^ 2 + Cm / ηL * (2 * Cm + Cm ^ 2) +
    (1 + Cm / ηL) * (1 + Cm) ^ 2 * KhL with hCmainL
  set CerrL := (1 + Cm) ^ 2 * (3 * C2 + Cf * (2 * CD)) * (2 / (b * ηL)) + Cf with hCerrL
  refine ⟨CmainL + CerrL + C₁ / d₁, max (max (max Wf W2) (max WD Wm)) ⌈d₁⁻¹⌉₊,
    by positivity, fun W hW E hE X hX => ?_⟩
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hηLη : ηL ≤ etaZ b E := etaLow_le (by linarith) hκ hE
  have hz2 : ‖boundaryZ b E‖ ≤ 2 := bulk_norm_z hb0 hb hκ hE
  set η := etaZ b E
  set Iz := ‖boundaryZ b E‖ + 1 with hIz
  set Kh := c / b * 2 * Cm / (4 * η ^ 2) with hKh
  set Cmain := Cm / η + 2 * Cm + Cm ^ 2 + Cm / η * (2 * Cm + Cm ^ 2) +
    (1 + Cm / η) * (1 + Cm) ^ 2 * Kh with hCmain
  set Cerr := (1 + Cm) ^ 2 * (Iz * C2 + Cf * (2 * CD)) * (2 / (b * η)) + Cf with hCerr
  have hKhle : Kh ≤ KhL := by rw [hKh, hKhL]; gcongr
  have hCmainle : Cmain ≤ CmainL := by rw [hCmain, hCmainL]; gcongr
  have hCerrle : Cerr ≤ CerrL := by
    rw [hCerr, hCerrL]; gcongr; rw [hIz]; linarith
  have hq0 : 0 ≤ passiveMass b E X := passiveMass_nonneg b E hX.posSemidef
  have he0' : 0 ≤ jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2 := by
    have : 0 ≤ jetDistance0 b E X := norm_nonneg _
    positivity
  suffices H : (passiveQ b E X * matrixExpect (freshLaw W b) (freshU b E X)).trace.re ≤
      passiveMass b E X / (1 + alphaCoef b E * passiveMass b E X / W) +
        (Cmain + Cerr + C₁ / d₁) * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2) * passiveMass b E X by
    refine H.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right ?_ he0') hq0))
    linarith
  clear hKhle hCmainle hCerrle hηLη hz2 hq0 he0' hKhL hCmainL hCerrL hIz hKh hCmain hCerr
  clear CerrL CmainL KhL hηL hηLdef ηL
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hWf, hW2⟩, hWD, hWm⟩, hWd⟩ := hW
  have hY := hX.posSemidef
  obtain ⟨hKMn, hsn, hU⟩ := hF W hWf E hE X hX
  obtain ⟨hW1, -, hM, hv, -, -, hB0, hB1, hG, hzM, -⟩ := hD W hWD E hE X hX
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW1
  have hW1r : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  set Q := passiveQ b E X
  set q := passiveMass b E X
  set U := matrixExpect (freshLaw W b) (freshU b E X)
  set δ := jetDistance0 b E X
  set e := δ + (W : ℝ)⁻¹ ^ 2
  have hQ : Q.PosSemidef := hY.conjTranspose_mul_mul_same _
  have hq : 0 ≤ q := passiveMass_nonneg b E hY
  have hδ : 0 ≤ δ := norm_nonneg _
  have hWe : (W : ℝ)⁻¹ ^ 2 ≤ e := by simp only [e]; linarith
  have hW2le : (W : ℝ)⁻¹ ^ 2 = 1 / (W : ℝ) ^ 2 := by rw [inv_pow, one_div]
  set α := alphaCoef b E
  have hα : 0 ≤ α := by simp only [α, alphaCoef]; positivity
  set G0 := q / (1 + α * q / W)
  have hG0 : 0 ≤ G0 := by positivity
  have hG0q : G0 ≤ q := div_le_self hq (by
    have : 0 ≤ α * q / W := by positivity
    linarith)
  -- crude bound
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
  have hcrude : (Q * U).trace.re ≤ C₁ * q :=
    (mm_re_trace_le hQ).trans (mul_le_mul_of_nonneg_right hUn hq)
  by_cases hdom : δ ≤ d₁
  swap
  · push Not at hdom
    have : C₁ * q ≤ C₁ / d₁ * (δ * q) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hd₁]
      have : 0 ≤ C₁ := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hdom.le (mul_nonneg this hq)]
    have h4 : 0 ≤ (Cmain + Cerr) * (e * q) := by positivity
    have h5 : C₁ / d₁ * (δ * q) ≤ C₁ / d₁ * (e * q) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (by simp only [e]; linarith [sq_nonneg ((W : ℝ)⁻¹)]) hq) (by positivity)
    have e6 : G0 + (Cmain + Cerr + C₁ / d₁) * e * q =
        G0 + (Cmain + Cerr) * (e * q) + C₁ / d₁ * (e * q) := by ring
    rw [e6]
    calc (Q * U).trace.re ≤ C₁ / d₁ * (δ * q) := hcrude.trans this
      _ ≤ _ := by linarith
  -- on the domain
  have hWinv : (W : ℝ)⁻¹ ≤ d₁ := by
    rw [inv_le_comm₀ hWpos hd₁]; exact (Nat.le_ceil _).trans (by exact_mod_cast hWd)
  have hWsq : (W : ℝ)⁻¹ ^ 2 ≤ d₁ := by
    have : (W : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hW1r
    nlinarith [inv_nonneg.mpr hWpos.le]
  have he1 : e ≤ 1 := by simp only [e]; linarith
  have hCme : Cm * e ≤ 1 / 2 := by
    have : e ≤ 2 / (4 * Cm + 4) := by
      simp only [e]; have := hd₁m; rw [show (2 : ℝ) / (4 * Cm + 4) = 2 * (1 / (4 * Cm + 4)) by ring]
      linarith
    calc Cm * e ≤ Cm * (2 / (4 * Cm + 4)) := mul_le_mul_of_nonneg_left this hCm
      _ ≤ 1 / 2 := by rw [mul_div_assoc', div_le_iff₀ (by positivity)]; linarith
  obtain ⟨hzζ, hKM1, hh1⟩ := hm0 W hWm E hE X hX (hdom.trans hd₁0)
  have he0 : 0 ≤ e := by simp only [e]; positivity
  have hheq : hOf b E X - 1 = ((Complex.normSq (vOf b E X) - 1 : ℝ) : ℂ) := by
    simp only [hOf, Complex.mul_conj]; push_cast; ring
  have hh1' : |Complex.normSq (vOf b E X) - 1| ≤ Cm * e := by
    rw [hheq, Complex.norm_real, Real.norm_eq_abs] at hh1; exact hh1
  have hW2e : 1 / (W : ℝ) ^ 2 ≤ e := by rw [← hW2le]; exact hWe
  have hιb : |(zetaX b E X).im| ≤ Iz := by
    have h' : |(zetaX b E X).im| ≤ ‖zetaX b E X‖ := Complex.abs_im_le_norm _
    have h'' : ‖zetaX b E X‖ ≤ ‖boundaryZ b E‖ + ‖boundaryZ b E - zetaX b E X‖ := by
      have := norm_sub_le (boundaryZ b E) (boundaryZ b E - zetaX b E X)
      rwa [sub_sub_cancel] at this
    simp only [Iz]; linarith
  have hsre := mm_sre hW1 hb0 hb h1 h2 hX hC2 hCf hCD hG hB0 hB1 hzM (hS1 W hW2 E hE X hX).2.2 hsn
    (hh1'.trans hCme) hιb hW2e
  have hε : 0 ≤ (Iz * C2 + Cf * (2 * CD)) * e := by positivity
  have hon := mm_onDomain hb0 hb h1 h2 hW1 hX hCm hCf he0 he1 hW2e hε hzζ hKM1 hh1' hCme hU hsre
  have key : (Q * U).trace.re ≤ G0 + Cmain * e * q +
      (1 + Cm) ^ 2 * q * ((Iz * C2 + Cf * (2 * CD)) * e) * (2 / (b * η)) + Cf * e * q := hon
  have e7 : G0 + (Cmain + Cerr + C₁ / d₁) * e * q = G0 + Cmain * e * q +
      ((1 + Cm) ^ 2 * q * ((Iz * C2 + Cf * (2 * CD)) * e) * (2 / (b * η)) + Cf * e * q) +
      C₁ / d₁ * e * q := by simp only [Cerr]; ring
  have h8 : 0 ≤ C₁ / d₁ * e * q := by positivity
  rw [e7]
  linarith only [key, h8]

end BlockBand.Transmission.LengthUniform
