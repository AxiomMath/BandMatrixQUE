module

public import BlockBand.Transmission.SourceMixing.MassMeanAlg

/-!
# Matched values with `δ₀`-only errors

Hypothesis `PassiveBoundsStatement`. Law `layerLaw W b .oneBlockOnePort`, deterministic strictly
passive `X` (`Y ≻ 0`) with `δ₀ ≤ d₀`, fixed `b ∈ (0, 1/2)`, `E ∈ (-2, 2)`; constants depend on `b, E`
only, uniform in `W ≥ W₀`, `X`.

Matched-value estimates and the on-domain bound used for the mass mean.

`mm_matched0`: with `e₀ = δ₀ + W⁻²`, `|z - ζ|, ‖KM - 1‖, |h - 1| ≤ Ce₀`. These are the first
three items of `matchedBasic` (same proof), which there are stated with the larger
`epsOf = δ₀ + δ₁ + q/W + W⁻²`; the mass mean needs the `δ₁`- and `q/W`-free form.

`mm_scalar_final` (pure scalars) and `mm_trace_decomp` (`W y_M = Tr(Q·KM KMᴴ)` exactly, from
`M = R·KM`) are the two halves of the on-domain bound.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.SourceMixing

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PathScalar
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- Matched values with `δ₀ + W⁻²` errors. -/
theorem mm_matched0 (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) :
    ∃ (d₀ C : ℝ) (W₀ : ℕ), 0 < d₀ ∧ 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → jetDistance0 b E X ≤ d₀ →
        ‖boundaryZ b E - zetaX b E X‖ ≤ C * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2) ∧
        ‖kmOf b E X - 1‖ ≤ C * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2) ∧
        ‖hOf b E X - 1‖ ≤ C * (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2) := by
  obtain ⟨d₀, Cm, Wm, hd₀, hCm, hmi⟩ := mean_identify hA hb0 hb h1 h2
  obtain ⟨CD, WD, hCD, hD⟩ := dressedBlocks hA hb0 hb h1 h2
  obtain ⟨CR, WR, -, hres⟩ := mean_residuals hA hb0 hb h1 h2
  set Cv := CD * b * Cm
  refine ⟨d₀, Cm + Cm * CD + (CD + 1) * Cv, max (max Wm WD) WR, hd₀, by positivity,
    fun W hW X hX hd => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWm, hWD⟩, hWR⟩ := hW
  obtain ⟨hm1, hm2, -⟩ := hmi W hWm X hX hd
  obtain ⟨-, -, hM, hv, -, -, -, -, -, hzM, -⟩ := hD W hWD X hX
  obtain ⟨-, -, -, -, hβ, -⟩ := hres W hWR X hX
  set e := jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2
  have he : 0 ≤ e := by have : 0 ≤ jetDistance0 b E X := norm_nonneg _; positivity
  set M := mOf b E X
  set a := matchedA E
  set z := boundaryZ b E
  set ζ := zetaX b E X
  have hz : ‖z - ζ‖ ≤ Cm * e := by
    have h := PathJet.zeta_sub_z b E h1 h2 (meanTr b E X 0) (meanTr b E X 3)
    change ‖boundaryZ b E - zetaOf b E (meanTr b E X 0) (meanTr b E X 3)‖ ≤ _
    rw [← norm_neg, neg_sub, h, norm_neg]
    have nc : ‖((1 - 2 * b : ℝ) : ℂ)‖ = 1 - 2 * b := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    have nb : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, nc, nb]
    have hc : 0 ≤ 1 - 2 * b := by linarith
    have : 0 ≤ Cm * e := by positivity
    calc (1 - 2 * b) * ‖meanTr b E X 0 - a‖ + b * ‖meanTr b E X 3 - a‖
        ≤ (1 - 2 * b) * (Cm * e) + b * (Cm * e) := by gcongr
      _ ≤ Cm * e := by nlinarith
  have hKM : kmOf b E X - 1 = (z - ζ) • M := by
    have e' : kmOf b E X = (z • 1 - X) * M := (blkAt_kHat_mul_zero b E X _).1
    rw [e', show z • (1 : Matrix (Fin W) (Fin W) ℂ) - X = (z - ζ) • 1 + (ζ • 1 - X) by
      rw [sub_smul]; abel, Matrix.add_mul, hzM, Matrix.smul_mul, Matrix.one_mul]
    abel
  have hKM' : ‖kmOf b E X - 1‖ ≤ Cm * CD * e := by
    rw [hKM]
    calc ‖(z - ζ) • M‖ ≤ ‖z - ζ‖ * ‖M‖ := norm_smul_le _ _
      _ ≤ Cm * e * CD := mul_le_mul hz hM (norm_nonneg _) (by positivity)
      _ = Cm * CD * e := by ring
  have ha0 : a ≠ 0 := matchedA_ne_zero E h1 h2
  have hna : ‖a‖ = 1 := norm_matchedA E h1 h2
  have hva : vOf b E X - a = vOf b E X * a * (b : ℂ) * (meanTr b E X 0 - a) := by
    have hβ' : (a⁻¹ + (b : ℂ) * a) - (b : ℂ) * meanTr b E X 0 ≠ 0 := hβ
    show ((a⁻¹ + (b : ℂ) * a) - (b : ℂ) * meanTr b E X 0)⁻¹ - a =
      ((a⁻¹ + (b : ℂ) * a) - (b : ℂ) * meanTr b E X 0)⁻¹ * a * (b : ℂ) * (meanTr b E X 0 - a)
    have hD2 : 1 - a * (b : ℂ) * meanTr b E X 0 + a ^ 2 * (b : ℂ) ≠ 0 := by
      have e' : 1 - a * (b : ℂ) * meanTr b E X 0 + a ^ 2 * (b : ℂ) =
          a * ((a⁻¹ + (b : ℂ) * a) - (b : ℂ) * meanTr b E X 0) := by field_simp; ring
      rw [e']; exact mul_ne_zero ha0 hβ'
    have hinv := mul_inv_cancel₀ hD2
    field_simp
    linear_combination hinv
  have hva' : ‖vOf b E X - a‖ ≤ Cv * e := by
    rw [hva, norm_mul, norm_mul, norm_mul, hna, Complex.norm_real, Real.norm_of_nonneg hb0.le,
      mul_one]
    calc ‖vOf b E X‖ * b * ‖meanTr b E X 0 - a‖ ≤ CD * b * (Cm * e) := by gcongr
      _ = Cv * e := by ring
  have hh' : ‖hOf b E X - 1‖ ≤ (CD + 1) * Cv * e := by
    have e' : hOf b E X - 1 = (vOf b E X - a) * conj (vOf b E X) + a * conj (vOf b E X - a) := by
      unfold hOf
      rw [map_sub]
      have : a * conj a = 1 := matchedA_mul_conj E h1 h2
      linear_combination this
    rw [e']
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj, hna]
    calc ‖vOf b E X - a‖ * ‖vOf b E X‖ + 1 * ‖vOf b E X - a‖ = (‖vOf b E X‖ + 1) *
          ‖vOf b E X - a‖ := by ring
      _ ≤ (CD + 1) * (Cv * e) := mul_le_mul (by linarith) hva' (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hCv : 0 ≤ Cv := by positivity
  have p1 : 0 ≤ Cm * CD := by positivity
  have p2 : 0 ≤ (CD + 1) * Cv := by positivity
  have hle : ∀ K : ℝ, 0 ≤ K → K ≤ Cm + Cm * CD + (CD + 1) * Cv →
      K * e ≤ (Cm + Cm * CD + (CD + 1) * Cv) * e := fun K _ hK => mul_le_mul_of_nonneg_right hK he
  exact ⟨hz.trans (hle _ hCm (by linarith)), hKM'.trans (hle _ p1 (by linarith)),
    hh'.trans (hle _ p2 (by linarith))⟩

/-- The scalar assembly of the on-domain bound. -/
theorem mm_scalar_final {η b h u q W ι sr ε₁ Λ e Cm : ℝ} (hη : 0 < η) (hb0 : 0 < b)
    (hb : b < 1 / 2) (hhlo : 1 / 2 ≤ h) (hh1 : |h - 1| ≤ Cm * e) (hu : 0 ≤ u) (huΛ : u ≤ Λ * q)
    (hΛ1 : 1 ≤ Λ) (hΛ : Λ ≤ (1 + Cm * e) ^ 2) (hq : 0 ≤ q) (hqW : q ≤ W / (4 * η)) (hW : 0 < W)
    (hιη : |ι - η| ≤ Cm * e) (he : 0 ≤ e) (he1 : e ≤ 1) (hCm : 0 ≤ Cm) (hε₁ : 0 ≤ ε₁)
    (hs : sr ≤ (b * h * ι + ε₁) / (b * h * η + ((1 - 2 * b) + b ^ 2 * h) * (u / W))) :
    sr * u ≤ q / (1 + (1 - b) ^ 2 / (b * η) * q / W) +
      (Cm / η + 2 * Cm + Cm ^ 2 + Cm / η * (2 * Cm + Cm ^ 2) +
        (1 + Cm / η) * (1 + Cm) ^ 2 * ((1 - 2 * b) / b * 2 * Cm / (4 * η ^ 2))) * e * q +
      Λ * q * ε₁ * (2 / (b * η)) := by
  have hc : 0 ≤ 1 - 2 * b := by linarith
  set D := b * h * η + ((1 - 2 * b) + b ^ 2 * h) * (u / W)
  have hD : b * η / 2 ≤ D := by
    have : 0 ≤ ((1 - 2 * b) + b ^ 2 * h) * (u / W) := by
      have : 0 ≤ b ^ 2 * h := by have : 0 ≤ h := by linarith
                                 positivity
      positivity
    have : b * η / 2 ≤ b * h * η := by nlinarith [mul_pos hb0 hη]
    simp only [D]; linarith
  have hDp : 0 < D := lt_of_lt_of_le (by positivity) hD
  set F := u * (b * h) / D
  have hF0 : 0 ≤ F := by have : 0 ≤ h := by linarith
                         positivity
  have hsplit : sr * u ≤ ι * F + ε₁ * u / D := by
    have := mul_le_mul_of_nonneg_right hs hu
    calc sr * u ≤ (b * h * ι + ε₁) / D * u := this
      _ = ι * F + ε₁ * u / D := by simp only [F]; ring
  have hFle := mm_F_le hη hb0 hb hhlo hu hq hW hqW hΛ1 huΛ
  have hιF : ι * F ≤ (η + |ι - η|) * F :=
    mul_le_mul_of_nonneg_right (by have := le_abs_self (ι - η); linarith) hF0
  set G0 := q / (1 + (1 - b) ^ 2 / (b * η) * q / W)
  have hden : 1 ≤ 1 + (1 - b) ^ 2 / (b * η) * q / W := by
    have : 0 ≤ (1 - b) ^ 2 / (b * η) * q / W := by positivity
    linarith
  have hG0 : 0 ≤ G0 := by positivity
  have hG0q : G0 ≤ q := div_le_self hq hden
  set kk := (1 - 2 * b) / b * 2 * |h - 1| / (4 * η ^ 2)
  have hrw : (η + |ι - η|) * (Λ * (q / (η * (1 + (1 - b) ^ 2 / (b * η) * q / W)) +
      q * ((1 - 2 * b) / b * 2 * |h - 1|) / (4 * η ^ 3))) =
      (1 + |ι - η| / η) * Λ * (G0 + kk * q) := by
    simp only [G0, kk]; field_simp
  have hmain : ι * F ≤ G0 + (Cm / η + 2 * Cm + Cm ^ 2 + Cm / η * (2 * Cm + Cm ^ 2) +
      (1 + Cm / η) * (1 + Cm) ^ 2 * ((1 - 2 * b) / b * 2 * Cm / (4 * η ^ 2))) * e * q := by
    refine hιF.trans ?_
    refine (mul_le_mul_of_nonneg_left hFle (by positivity)).trans ?_
    rw [hrw]
    refine mm_final hq hG0 hG0q he he1 (by positivity) ?_ hΛ1 hΛ (by positivity) ?_
      (by positivity) hCm
    · rw [div_le_iff₀ hη]; calc |ι - η| ≤ Cm * e := hιη
        _ = Cm / η * e * η := by field_simp
    · simp only [kk]
      rw [div_le_iff₀ (by positivity)]
      have : (1 - 2 * b) / b * 2 * |h - 1| ≤ (1 - 2 * b) / b * 2 * (Cm * e) :=
        mul_le_mul_of_nonneg_left hh1 (by positivity)
      calc (1 - 2 * b) / b * 2 * |h - 1| ≤ (1 - 2 * b) / b * 2 * (Cm * e) := this
        _ = (1 - 2 * b) / b * 2 * Cm / (4 * η ^ 2) * e * (4 * η ^ 2) := by field_simp
  have herr : ε₁ * u / D ≤ Λ * q * ε₁ * (2 / (b * η)) := by
    rw [div_le_iff₀ hDp]
    have h1 : ε₁ * u ≤ ε₁ * (Λ * q) := mul_le_mul_of_nonneg_left huΛ hε₁
    have h2 : Λ * q * ε₁ * (2 / (b * η)) * D ≥ Λ * q * ε₁ * (2 / (b * η)) * (b * η / 2) :=
      mul_le_mul_of_nonneg_left hD (by positivity)
    have h3 : Λ * q * ε₁ * (2 / (b * η)) * (b * η / 2) = ε₁ * (Λ * q) := by field_simp
    linarith
  linarith

/-- The matrix part of the on-domain bound: with `M = R·KM`, `Q = RᴴYR`:
`u = Tr(MᴴYM) = Tr(Q KM KMᴴ) ≥ 0` is real, `u ≤ ‖KM‖²q`, and `Re Tr(QU) ≤ Re(s)u + ‖U - s KM KMᴴ‖q`.
-/
theorem mm_trace_decomp {Q U KM M R Y : Matrix (Fin W) (Fin W) ℂ} (s : ℂ) (hY : Y.PosSemidef)
    (hQ : Q = Rᴴ * Y * R) (hRKM : R * KM = M) :
    0 ≤ (Mᴴ * Y * M).trace.re ∧ (Mᴴ * Y * M).trace = ((Mᴴ * Y * M).trace.re : ℂ) ∧
      (Mᴴ * Y * M).trace.re ≤ ‖KM‖ ^ 2 * Q.trace.re ∧
      (Q * U).trace.re ≤ s.re * (Mᴴ * Y * M).trace.re + ‖U - s • (KM * KMᴴ)‖ * Q.trace.re := by
  have hQp : Q.PosSemidef := by rw [hQ]; exact hY.conjTranspose_mul_mul_same _
  have hMYM : Mᴴ * Y * M = KMᴴ * Q * KM := by
    rw [← hRKM, conjTranspose_mul, hQ]; simp only [Matrix.mul_assoc]
  rw [hMYM]
  obtain ⟨hu0, hureal⟩ := mm_trace_posSemidef (hQp.conjTranspose_mul_mul_same KM)
  have htQ : (Q * (KM * KMᴴ)).trace = ((KMᴴ * Q * KM).trace.re : ℂ) := by
    rw [← hureal, ← Matrix.mul_assoc, trace_mul_comm, ← Matrix.mul_assoc]
  refine ⟨hu0, hureal, ?_, ?_⟩
  · have h := norm_trace_mul_posSemidef_le hQp (KM * KMᴴ)
    rw [trace_mul_comm, htQ, Complex.norm_real, Real.norm_of_nonneg hu0] at h
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (mm_trace_posSemidef hQp).1)
    refine (Matrix.l2_opNorm_mul _ _).trans (le_of_eq ?_)
    rw [Matrix.l2_opNorm_conjTranspose, sq]
  · have hdec : (Q * U).trace.re = s.re * (KMᴴ * Q * KM).trace.re +
        (Q * (U - s • (KM * KMᴴ))).trace.re := by
      have : U = s • (KM * KMᴴ) + (U - s • (KM * KMᴴ)) := by abel
      conv_lhs => rw [this]
      rw [Matrix.mul_add, trace_add, Matrix.mul_smul, trace_smul, htQ, smul_eq_mul,
        Complex.add_re]
      simp [Complex.mul_re]
    rw [hdec]
    exact add_le_add le_rfl (mm_re_trace_le hQp)

end BlockBand.Transmission.SourceMixing
