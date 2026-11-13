module

public import BlockBand.Transmission.Generator.RefinedAlg
public import BlockBand.Transmission.LengthUniform.BulkMassMeanStrict

/-!
# Two-sided `Re s₁` and trace decomposition for the refined mass mean

* `rf_sre`: the two-sided form of `SourceMixing.mm_sre` (same proof): with `D = bhη + k_h u/W`,
  `|Re(s₁)D - bhι| ≤ (I_zC₂ + 2C_fC_D)/W²` (the imaginary parts of the scalar equations).
* `rf_decomp`: `|Re Tr(QU) - Re(s)u| ≤ ‖U - s KM KMᴴ‖q` with `u = Tr(MᴴYM)`, `M = R·KM`.
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
open BlockBand.Transmission.SourceMixing
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- **Two-sided `Re s₁`** (copy of `mm_sre` with the two-sided conclusion). -/
theorem rf_sre (hW1 : 1 ≤ W) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    {X : Matrix (Fin W) (Fin W) ℂ} {C2 Cf CD Iz : ℝ}
    (hG : ∀ α β, Integrable (fun ω => gRes b E X ω α β) (layerLaw W b .oneBlockOnePort))
    (hB0 : ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 0 0 - mOf b E X‖ ≤
      CD / (W : ℝ) ^ 2)
    (hB1 : ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 1 1 -
      vOf b E X • 1‖ ≤ CD / (W : ℝ) ^ 2)
    (hzM : (zetaX b E X • 1 - X) * mOf b E X = 1)
    (hS : ‖sOne b E X * (1 - khOf b E X * aOf b E X) - (b : ℂ) * hOf b E X‖ ≤ C2 / (W : ℝ) ^ 2)
    (hsn : ‖sOne b E X‖ ≤ Cf) (hh : |Complex.normSq (vOf b E X) - 1| ≤ 1 / 2)
    (hιb : |(zetaX b E X).im| ≤ Iz) :
    |(sOne b E X).re * (b * Complex.normSq (vOf b E X) * etaZ b E +
        ((1 - 2 * b) + b ^ 2 * Complex.normSq (vOf b E X)) *
        (((mOf b E X)ᴴ * passiveY X * mOf b E X).trace.re / W)) -
      b * Complex.normSq (vOf b E X) * (zetaX b E X).im| ≤
      (Iz * C2 + Cf * (2 * CD)) / (W : ℝ) ^ 2 := by
  set M := mOf b E X
  set v := vOf b E X
  set h := Complex.normSq v
  set u := (Mᴴ * passiveY X * M).trace.re
  have hhhi : h ≤ 3 / 2 := by have := le_abs_self (h - 1); linarith
  have hAP := mm_trace_posSemidef (Matrix.posSemidef_self_mul_conjTranspose M)
  set A := (aOf b E X).re
  have hAeq : aOf b E X = (A : ℂ) := by
    refine Complex.ext (by simp [A]) ?_
    simp only [aOf, Complex.ofReal_im]
    rw [hAP.2]; simp [Complex.mul_im]
  have hheq : hOf b E X = (h : ℂ) := by simp only [hOf, h, Complex.mul_conj]; rfl
  have hward := mm_ward X M (zetaX b E X) hzM
  have hy : ((W : ℂ)⁻¹ * (Mᴴ * passiveY X * M).trace).re = u / W := by
    rw [show ((W : ℂ)⁻¹) = (((W : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul,
      div_eq_inv_mul]
  rw [hy] at hward
  obtain ⟨hm1, hm2⟩ := meanTr_eq_blk b E X hG
  have hd1 : ‖meanTr b E X 0 - (W : ℂ)⁻¹ * M.trace‖ ≤ CD / (W : ℝ) ^ 2 := by
    rw [hm1]; exact (norm_normTrace_sub_le _ _).trans hB0
  have hd2 : ‖meanTr b E X 3 - v‖ ≤ CD / (W : ℝ) ^ 2 := by
    have e1 := normTrace_smul_one hW1 v
    rw [hm2]
    calc _ = ‖(W : ℂ)⁻¹ * (blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 1 1).trace -
          (W : ℂ)⁻¹ * (v • (1 : Matrix (Fin W) (Fin W) ℂ)).trace‖ := by rw [e1]
      _ ≤ _ := (norm_normTrace_sub_le _ _).trans hB1
  have hι : (zetaX b E X).im = (1 - 2 * b) * (-(meanTr b E X 0).im) +
      b * (-(meanTr b E X 3).im) := im_zetaOf b E _ _
  have hvim : v.im = -h * (etaZ b E - b * (meanTr b E X 0).im) := by
    have := mm_inv_im (boundaryZ b E - (b : ℂ) * meanTr b E X 0)
    rw [show (boundaryZ b E - (b : ℂ) * meanTr b E X 0)⁻¹ = v from rfl] at this
    rw [this, Complex.mul_conj, Complex.ofReal_re, Complex.sub_im, Complex.im_ofReal_mul]; rfl
  have hE₁ := mm_im_algebra hb0 hb (Complex.normSq_nonneg _) hhhi hward hι hvim hd1 hd2
  set ι := (zetaX b E X).im
  set k := (1 - 2 * b) + b ^ 2 * h
  set L := 1 - k * A
  set D := b * h * etaZ b E + k * (u / W)
  have hsL : ‖sOne b E X * (L : ℂ) - ((b * h : ℝ) : ℂ)‖ ≤ C2 / (W : ℝ) ^ 2 := by
    rw [hAeq, hheq] at hS
    convert hS using 2; simp only [L, k, khOf, hheq]; push_cast; ring
  have hres := rf_re_s_two hsL (show ι * L = D + (ι * L - D) by ring) hsn
  have hCf : 0 ≤ Cf := (norm_nonneg _).trans hsn
  have hε : |ι| * (C2 / (W : ℝ) ^ 2) + Cf * |ι * L - D| ≤ (Iz * C2 + Cf * (2 * CD)) / (W : ℝ) ^ 2 := by
    have hC2 : 0 ≤ C2 / (W : ℝ) ^ 2 := (norm_nonneg _).trans hsL
    have a1 : |ι| * (C2 / (W : ℝ) ^ 2) ≤ Iz * (C2 / (W : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hιb hC2
    have a2 : Cf * |ι * L - D| ≤ Cf * (2 * (CD / (W : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hE₁ hCf
    have e : (Iz * C2 + Cf * (2 * CD)) / (W : ℝ) ^ 2 =
        Iz * (C2 / (W : ℝ) ^ 2) + Cf * (2 * (CD / (W : ℝ) ^ 2)) := by ring
    rw [e]; linarith
  have : b * h * ι = (b * h : ℝ) * ι := rfl
  rw [this]
  exact hres.trans hε

/-- **Two-sided trace decomposition**: `|Re Tr(QU) - Re(s)u| ≤ ‖U - s KM KMᴴ‖q`. -/
theorem rf_decomp {Q U KM M R Y : Matrix (Fin W) (Fin W) ℂ} (s : ℂ) (hY : Y.PosSemidef)
    (hQ : Q = Rᴴ * Y * R) (hRKM : R * KM = M) :
    |(Q * U).trace.re - s.re * (Mᴴ * Y * M).trace.re| ≤ ‖U - s • (KM * KMᴴ)‖ * Q.trace.re := by
  have hQp : Q.PosSemidef := by rw [hQ]; exact hY.conjTranspose_mul_mul_same _
  have hMYM : Mᴴ * Y * M = KMᴴ * Q * KM := by
    rw [← hRKM, conjTranspose_mul, hQ]; simp only [Matrix.mul_assoc]
  rw [hMYM]
  obtain ⟨-, hureal⟩ := mm_trace_posSemidef (hQp.conjTranspose_mul_mul_same KM)
  have htQ : (Q * (KM * KMᴴ)).trace = ((KMᴴ * Q * KM).trace.re : ℂ) := by
    rw [← hureal, ← Matrix.mul_assoc, trace_mul_comm, ← Matrix.mul_assoc]
  have hdec : (Q * U).trace.re = s.re * (KMᴴ * Q * KM).trace.re +
      (Q * (U - s • (KM * KMᴴ))).trace.re := by
    have : U = s • (KM * KMᴴ) + (U - s • (KM * KMᴴ)) := by abel
    conv_lhs => rw [this]
    rw [Matrix.mul_add, trace_add, Matrix.mul_smul, trace_smul, htQ, smul_eq_mul,
      Complex.add_re]
    simp [Complex.mul_re]
  rw [hdec, add_sub_cancel_left, trace_mul_comm]
  exact (Complex.abs_re_le_norm _).trans (norm_trace_mul_posSemidef_le hQp _)

end BlockBand.Transmission.Generator
