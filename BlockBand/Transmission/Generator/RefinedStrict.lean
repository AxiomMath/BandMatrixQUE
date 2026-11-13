module

public import BlockBand.Transmission.Generator.RefinedSre

/-!
# The refined (`Ω`-linear) mass mean, strictly passive inputs, bulk-uniform

Law `freshLaw W b`, deterministic strictly passive `X` (`Y ≻ 0`), `b ∈ (0, 1/2)`,
`E ∈ bulkInterval κ`; constants depend on `b, κ` only, uniformly in `W ≥ W₀`, `E` and `X`.

Two-sided: with `e = δ₀ + W⁻²`, `τ = |Tr(Qf)|`,
`|Re Tr(Q E[LL*]) - q/(1+αq/W)| ≤ C(eτ + e²q + eq²/W + W⁻²q)` (`refinedErr`).
Compared with `massMean_holds_bulk` (`≤ q/(1+αq/W) + C(δ₀+W⁻²)q`), the first-order `δ₀q` term is
replaced by `δ₀|Tr Qf|` (summable by the passive source mixing bound) and `δ₀²q, δ₀q²/W`.
Proof: `rf_decomp` (`E q₊ = Re(s₁)u + O(qW⁻²)`), `rf_sre` (`Re s₁ = bhι/D + O(W⁻²)`),
`rf_u_expand` (`u = q + 2Re(ωTr Qf) + qIm ω/η + O(|ω|²q)`, `ω = z - ζ`, `KM = 1 + ωM`) and
`rf_scalar` (the `Im ω/η` terms cancel: `ι = η - Im ω`). Off the domain `δ₀ ≤ d₁`:
`|E q₊| + q ≤ (C₁+1)q ≤ (C₁+1)d₁⁻²δ₀²q`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PathScalar
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.LengthUniform
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- The error of the refined mass mean: with `e = δ₀ + W⁻²`,
`e|Tr(Qf)| + e²q + eq²/W + W⁻²q`. -/
def refinedErr (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2) * ‖(passiveQ b E X * passiveF b E X).trace‖ +
    (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2) ^ 2 * passiveMass b E X +
    (jetDistance0 b E X + (W : ℝ)⁻¹ ^ 2) * passiveMass b E X ^ 2 / W +
    (W : ℝ)⁻¹ ^ 2 * passiveMass b E X

theorem refinedErr_nonneg (b E : ℝ) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) : 0 ≤ refinedErr b E X := by
  have hq := passiveMass_nonneg b E hY
  have hδ : 0 ≤ jetDistance0 b E X := norm_nonneg _
  unfold refinedErr; positivity

/-- **The on-domain bound** of the refined mean (all inputs explicit). -/
theorem rf_onDomain {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    (hW1 : 1 ≤ W) {X : Matrix (Fin W) (Fin W) ℂ} (hX : (passiveY X).PosDef)
    {Cf C2 CD Cm Li e : ℝ} (hCm : 0 ≤ Cm) (hCD : 0 ≤ CD) (he0 : 0 ≤ e)
    (hLi : (etaZ b E)⁻¹ ≤ Li) (hCme : Cm * e ≤ 1 / 2) (hCmeLi : Cm * e * Li ≤ 1)
    (hzζ : ‖boundaryZ b E - zetaX b E X‖ ≤ Cm * e) (hKM1 : ‖kmOf b E X - 1‖ ≤ Cm * e)
    (hh1 : |Complex.normSq (vOf b E X) - 1| ≤ Cm * e) (hz2 : ‖boundaryZ b E‖ ≤ 2)
    (hU : ‖matrixExpect (freshLaw W b) (freshU b E X) -
      sOne b E X • (kmOf b E X * (kmOf b E X)ᴴ)‖ ≤ Cf / (W : ℝ) ^ 2)
    (hsn : ‖sOne b E X‖ ≤ Cf) (hM : ‖mOf b E X‖ ≤ CD)
    (hG : ∀ α β, Integrable (fun ω => gRes b E X ω α β) (layerLaw W b .oneBlockOnePort))
    (hB0 : ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 0 0 - mOf b E X‖ ≤
      CD / (W : ℝ) ^ 2)
    (hB1 : ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 1 1 -
      vOf b E X • 1‖ ≤ CD / (W : ℝ) ^ 2)
    (hzM : (zetaX b E X • 1 - X) * mOf b E X = 1)
    (hS : ‖sOne b E X * (1 - khOf b E X * aOf b E X) - (b : ℂ) * hOf b E X‖ ≤
      C2 / (W : ℝ) ^ 2) :
    |(passiveQ b E X * matrixExpect (freshLaw W b) (freshU b E X)).trace.re -
        passiveMass b E X / (1 + alphaCoef b E * passiveMass b E X / W)| ≤
      (Cf + (3 * C2 + Cf * (2 * CD)) * (9 / 2 * Li / b)) * ((W : ℝ)⁻¹ ^ 2 * passiveMass b E X) +
      4 * Cm * (e * ‖(passiveQ b E X * passiveF b E X).trace‖) +
      (Cm ^ 2 * Li ^ 2 + 2 * Cm * (Cm * (2 * Li * CD + CD ^ 2))) * (e ^ 2 * passiveMass b E X) +
      (4 * Li / b * (4 * Cm * Li + Cm * (2 * Li * CD + CD ^ 2)) + 2 * Cm * Li / b) *
        (e * passiveMass b E X ^ 2 / W) := by
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW1
  have hYs := hX.posSemidef
  have hLi0 : 0 ≤ Li := (inv_pos.mpr hη).le.trans hLi
  set Q := passiveQ b E X with hQdef
  set q := passiveMass b E X
  set U := matrixExpect (freshLaw W b) (freshU b E X)
  set R := passiveResolvent b E X
  set M := mOf b E X
  set KM := kmOf b E X
  set s := sOne b E X
  set ζ := zetaX b E X
  set z := boundaryZ b E
  set ω := z - ζ with hωdef
  set τ := ‖(Q * passiveF b E X).trace‖
  have hq : 0 ≤ q := passiveMass_nonneg b E hYs
  obtain ⟨-, hRz⟩ := nearPencil_inverse hb0 hb h1 h2 hYs
  have hKMeq : KM = (z • 1 - X) * M := (blkAt_kHat_mul_zero b E X _).1
  have hRKM : R * KM = M := by rw [hKMeq, ← Matrix.mul_assoc, hRz, Matrix.one_mul]
  have hKMω : KM = 1 + ω • M := by
    rw [hKMeq, show z • (1 : Matrix (Fin W) (Fin W) ℂ) - X = ω • 1 + (ζ • 1 - X) by
      rw [hωdef, sub_smul]; abel, Matrix.add_mul, hzM, Matrix.smul_mul, Matrix.one_mul]
    abel
  set u := (Mᴴ * passiveY X * M).trace.re
  obtain ⟨hu0, -, huq, -⟩ := mm_trace_decomp (Q := Q) (U := U) s hYs rfl hRKM
  have hexp := rf_u_expand hη hYs (show Q = Rᴴ * passiveY X * R from rfl) hRKM hKMω
  change |u - q - 2 * (ω * (Q * passiveF b E X).trace).re - q * ω.im / etaZ b E| ≤ _ at hexp
  have hω : ‖ω‖ ≤ Cm * e := hzζ
  have hR : ‖R‖ ≤ Li := (norm_passiveResolvent_le hb0 hb h1 h2 hYs).trans hLi
  set KR := Cm * (2 * Li * CD + CD ^ 2)
  have hKR : 0 ≤ KR := by positivity
  have hρ : ‖ω‖ ^ 2 * q * (2 * ‖R‖ * ‖M‖ + ‖M‖ ^ 2) ≤ Cm * e * (KR * (e * q)) := by
    have a1 : ‖ω‖ ^ 2 ≤ (Cm * e) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hω 2
    have a2 : 2 * ‖R‖ * ‖M‖ + ‖M‖ ^ 2 ≤ 2 * Li * CD + CD ^ 2 := by
      have := mul_le_mul hR hM (norm_nonneg _) hLi0
      have := pow_le_pow_left₀ (norm_nonneg _) hM 2
      nlinarith
    calc ‖ω‖ ^ 2 * q * (2 * ‖R‖ * ‖M‖ + ‖M‖ ^ 2) ≤ (Cm * e) ^ 2 * q * (2 * Li * CD + CD ^ 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_right a1 hq) a2 (by positivity) (by positivity)
      _ = _ := by simp only [KR]; ring
  have ht : |2 * (ω * (Q * passiveF b E X).trace).re| ≤ 2 * Cm * e * τ := by
    rw [abs_mul, abs_two]
    have := (Complex.abs_re_le_norm (ω * (Q * passiveF b E X).trace)).trans
      (le_of_eq (norm_mul _ _))
    have h3 : ‖ω‖ * τ ≤ Cm * e * τ := mul_le_mul_of_nonneg_right hω (norm_nonneg _)
    linarith
  have hτ : τ ≤ 3 / 2 * Li * q := by
    have hf := norm_passiveF_le hb0 hb h1 h2 hYs
    have h3 : τ ≤ ‖passiveF b E X‖ * q := by
      simp only [τ]; rw [trace_mul_comm]
      exact norm_trace_mul_posSemidef_le (hYs.conjTranspose_mul_mul_same _) _
    have h4 : 3 / (2 * etaZ b E) ≤ 3 / 2 * Li := by
      rw [div_mul_eq_div_div, div_eq_mul_inv]
      have := mul_le_mul_of_nonneg_left hLi (by norm_num : (0 : ℝ) ≤ 3 / 2)
      linarith
    exact h3.trans (mul_le_mul_of_nonneg_right (hf.trans h4) hq)
  have hωi : |ω.im| ≤ Cm * e := (Complex.abs_im_le_norm _).trans hω
  have hsc := rf_scalar hη hLi hb0 hb hCm he0 hCmeLi hCme hh1 hq hu0 hWpos hωi hexp hρ hKR ht hτ
  -- `Re s₁`
  have hιb : |ζ.im| ≤ 3 := by
    have h' : ‖ζ‖ ≤ ‖z‖ + ‖z - ζ‖ := by
      have := norm_sub_le z (z - ζ); rwa [sub_sub_cancel] at this
    have := Complex.abs_im_le_norm ζ
    linarith
  have hsre := rf_sre hW1 hb0 hb hG hB0 hB1 hzM hS hsn (hh1.trans hCme) hιb
  have hι : ζ.im = etaZ b E - ω.im := by simp only [ω, etaZ, Complex.sub_im]; ring
  rw [hι] at hsre
  set h := Complex.normSq (vOf b E X)
  set D := b * h * etaZ b E + ((1 - 2 * b) + b ^ 2 * h) * (u / W)
  have hhlo : 1 / 2 ≤ h := by have := neg_abs_le (h - 1); linarith
  have hD : b * (1 / 2) * etaZ b E ≤ D := by
    have : 0 ≤ ((1 - 2 * b) + b ^ 2 * h) * (u / W) := by
      have : 0 ≤ 1 - 2 * b := by linarith
      positivity
    have : b * (1 / 2) * etaZ b E ≤ b * h * etaZ b E :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhlo hb0.le) hη.le
    linarith
  have hD0 : 0 < D := lt_of_lt_of_le (by positivity) hD
  have hKMn : ‖KM‖ ≤ 3 / 2 := by
    have := norm_add_le (KM - 1) 1
    rw [sub_add_cancel] at this
    have h1' : ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ 1 := PassiveLayer.norm_one_le'
    linarith
  have huq' : u ≤ 9 / 4 * q := by
    refine huq.trans (mul_le_mul_of_nonneg_right ?_ hq)
    have := pow_le_pow_left₀ (norm_nonneg _) hKMn 2
    linarith
  have huD : u / D ≤ 9 / 2 * Li / b * q := by
    rw [div_le_iff₀ hD0]
    have a1 : 9 / 2 * Li / b * q * (b * (1 / 2) * etaZ b E) = 9 / 4 * q * (Li * etaZ b E) := by
      field_simp; ring
    have a2 : 1 ≤ Li * etaZ b E := by
      have := mul_le_mul_of_nonneg_right hLi hη.le
      rwa [inv_mul_cancel₀ hη.ne'] at this
    have a3 : 9 / 4 * q ≤ 9 / 4 * q * (Li * etaZ b E) := le_mul_of_one_le_right (by positivity) a2
    have a4 : 9 / 2 * Li / b * q * (b * (1 / 2) * etaZ b E) ≤ 9 / 2 * Li / b * q * D :=
      mul_le_mul_of_nonneg_left hD (by positivity)
    linarith
  set ε₀ := 3 * C2 + Cf * (2 * CD)
  have hs2 : |s.re * u - b * h * (etaZ b E - ω.im) * u / D| ≤ ε₀ * (9 / 2 * Li / b) *
      ((W : ℝ)⁻¹ ^ 2 * q) := by
    have e1 : s.re * u - b * h * (etaZ b E - ω.im) * u / D =
        (s.re * D - b * h * (etaZ b E - ω.im)) * (u / D) := by field_simp
    rw [e1, abs_mul, abs_of_nonneg (div_nonneg hu0 hD0.le)]
    have hε0 : 0 ≤ ε₀ / (W : ℝ) ^ 2 := (abs_nonneg _).trans hsre
    calc |s.re * D - b * h * (etaZ b E - ω.im)| * (u / D) ≤ ε₀ / (W : ℝ) ^ 2 *
          (9 / 2 * Li / b * q) := mul_le_mul hsre huD (by positivity) hε0
      _ = _ := by rw [inv_pow, div_eq_mul_inv]; ring
  have hdec := rf_decomp (U := U) s hYs (show Q = Rᴴ * passiveY X * R from rfl) hRKM
  change |(Q * U).trace.re - s.re * u| ≤ ‖U - s • (KM * KMᴴ)‖ * Q.trace.re at hdec
  have hdec' : |(Q * U).trace.re - s.re * u| ≤ Cf * ((W : ℝ)⁻¹ ^ 2 * q) := by
    refine hdec.trans ?_
    calc ‖U - s • (KM * KMᴴ)‖ * Q.trace.re ≤ Cf / (W : ℝ) ^ 2 * q :=
          mul_le_mul_of_nonneg_right hU hq
      _ = _ := by rw [inv_pow, div_eq_mul_inv]; ring
  have hαeq : alphaCoef b E = (1 - b) ^ 2 / (b * etaZ b E) := rfl
  rw [hαeq]
  have hfin : |(Q * U).trace.re - q / (1 + (1 - b) ^ 2 / (b * etaZ b E) * q / W)| ≤
      |(Q * U).trace.re - s.re * u| + |s.re * u - b * h * (etaZ b E - ω.im) * u / D| +
        |b * h * (etaZ b E - ω.im) * u / D - q / (1 + (1 - b) ^ 2 / (b * etaZ b E) * q / W)| := by
    have := abs_sub_le ((Q * U).trace.re) (s.re * u) (q / (1 + (1 - b) ^ 2 / (b * etaZ b E) * q / W))
    have := abs_sub_le (s.re * u) (b * h * (etaZ b E - ω.im) * u / D)
      (q / (1 + (1 - b) ^ 2 / (b * etaZ b E) * q / W))
    linarith
  have e2 : (Cf + ε₀ * (9 / 2 * Li / b)) * ((W : ℝ)⁻¹ ^ 2 * q) =
      Cf * ((W : ℝ)⁻¹ ^ 2 * q) + ε₀ * (9 / 2 * Li / b) * ((W : ℝ)⁻¹ ^ 2 * q) := by ring
  rw [e2]
  linarith only [hfin, hdec', hs2, hsc]

end BlockBand.Transmission.Generator
