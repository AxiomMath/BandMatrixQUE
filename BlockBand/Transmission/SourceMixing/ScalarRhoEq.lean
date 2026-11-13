module

public import BlockBand.Transmission.SourceMixing.ScalarRho

/-!
# The scalar equation for `ρ₁`

Hypothesis `PassiveBoundsStatement`. Law `layerLaw W b .oneBlockOnePort`, deterministic strictly
passive `X` (`Y ≻ 0`), fixed `b ∈ (0, 1/2)`, `E ∈ (-2, 2)`; constants depend on `b, E` only,
uniformly in `W ≥ W₀` and `X`.

For strictly passive `X`, up to `C/W²`: `u₁ = θs₁B + ρ₁A` and
`ρ₁(1 - k_hA) = k_hθs₁B + bv(1 + bτ₁)t₂`.
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

/-- The scalar equation for `ρ₁`, together with the trace equation for `u₁`. -/
theorem scalarRho (hA : PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (h1 : -2 < E) (h2 : E < 2) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef →
        ‖uTwo b E X 0 - (thetaOf b E X * sOne b E X * bOf b E X + rhoOf b E X * aOf b E X)‖ ≤
          C / (W : ℝ) ^ 2 ∧
        ‖rhoOf b E X * (1 - khOf b E X * aOf b E X) -
          (khOf b E X * (thetaOf b E X * sOne b E X * bOf b E X) +
            (b : ℂ) * vOf b E X * (1 + (b : ℂ) * tauTwo b E X 0) * tTwo b E X 1)‖ ≤
          C / (W : ℝ) ^ 2 := by
  obtain ⟨C₁, W₁, hC₁, hB⟩ := scalarRho_blocks hA hb0 hb h1 h2
  obtain ⟨CD, WD, hCD, hD⟩ := dressedBlocks hA hb0 hb h1 h2
  set K := (1 - 2 * b) + b + b ^ 2 * (CD * CD)
  have hK : 0 ≤ K := by have : 0 ≤ 1 - 2 * b := by linarith
                        positivity
  refine ⟨(K + 1) * C₁, max W₁ WD, by positivity, fun W hW X hX => ?_⟩
  obtain ⟨hW1, -, -, hv, -⟩ := hD W (le_trans (le_max_right _ _) hW) X hX
  obtain ⟨-, -, hent, hb00, hb11⟩ := hB W (le_trans (le_max_left _ _) hW) X hX
  have hu : ∀ r, uTwo b E X r = blkTr (matrixExpect (layerLaw W b .oneBlockOnePort)
      (fun ω => gRes b E X ω * (pTwo * (gRes b E X ω * (pTwo * (gRes b E X ω)ᴴ))))) r :=
    fun r => integral_blkTr _ hent r
  have d1 : ‖uTwo b E X 0 - (thetaOf b E X * sOne b E X * bOf b E X + rhoOf b E X * aOf b E X)‖ ≤
      C₁ / (W : ℝ) ^ 2 := by
    have h := (norm_blkTr_sub_le _ 0 _).trans hb00
    rw [trace_add, trace_smul, trace_smul, smul_eq_mul, smul_eq_mul, mul_add, mul_left_comm,
      mul_left_comm (W : ℂ)⁻¹ (rhoOf b E X), ← hu] at h
    exact h
  have d2 : ‖uTwo b E X 1 - (vOf b E X * (1 + (b : ℂ) * tauTwo b E X 0) * tTwo b E X 1 +
      vOf b E X * ((b : ℂ) * uTwo b E X 0) * conj (vOf b E X))‖ ≤ C₁ / (W : ℝ) ^ 2 := by
    have h := (norm_blkTr_sub_le _ 1 _).trans hb11
    rw [normTrace_smul_one hW1, ← hu] at h
    exact h
  have hW2' : (0 : ℝ) < (W : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ W := by exact_mod_cast hW1
    positivity
  have hup : C₁ / (W : ℝ) ^ 2 ≤ (K + 1) * C₁ / (W : ℝ) ^ 2 :=
    div_le_div_of_nonneg_right (le_mul_of_one_le_left hC₁ (by linarith)) hW2'.le
  refine ⟨d1.trans hup, ?_⟩
  have hh : ‖hOf b E X‖ ≤ CD * CD := by
    unfold hOf; rw [norm_mul, Complex.norm_conj]; exact mul_le_mul hv hv (norm_nonneg _) hCD
  have e : rhoOf b E X * (1 - khOf b E X * aOf b E X) -
      (khOf b E X * (thetaOf b E X * sOne b E X * bOf b E X) +
        (b : ℂ) * vOf b E X * (1 + (b : ℂ) * tauTwo b E X 0) * tTwo b E X 1) =
      ((1 - 2 * b : ℝ) : ℂ) * (uTwo b E X 0 - (thetaOf b E X * sOne b E X * bOf b E X +
          rhoOf b E X * aOf b E X)) +
        (b : ℂ) * (uTwo b E X 1 - (vOf b E X * (1 + (b : ℂ) * tauTwo b E X 0) * tTwo b E X 1 +
          vOf b E X * ((b : ℂ) * uTwo b E X 0) * conj (vOf b E X))) +
        (b : ℂ) ^ 2 * hOf b E X * (uTwo b E X 0 - (thetaOf b E X * sOne b E X * bOf b E X +
          rhoOf b E X * aOf b E X)) := by
    unfold khOf hOf
    rw [show rhoOf b E X = ((1 - 2 * b : ℝ) : ℂ) * uTwo b E X 0 + (b : ℂ) * uTwo b E X 1 from rfl]
    ring
  rw [e]
  have nc : ‖((1 - 2 * b : ℝ) : ℂ)‖ = 1 - 2 * b := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have nb : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
  have hW2 : (0 : ℝ) ≤ C₁ / (W : ℝ) ^ 2 := by positivity
  refine (norm_add₃_le).trans ?_
  calc _ ≤ (1 - 2 * b) * (C₁ / (W : ℝ) ^ 2) + b * (C₁ / (W : ℝ) ^ 2) +
        b ^ 2 * (CD * CD) * (C₁ / (W : ℝ) ^ 2) := by
        rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, nc, nb]
        have : 0 ≤ 1 - 2 * b := by linarith
        gcongr
    _ ≤ _ := by
        rw [show (1 - 2 * b) * (C₁ / (W : ℝ) ^ 2) + b * (C₁ / (W : ℝ) ^ 2) +
          b ^ 2 * (CD * CD) * (C₁ / (W : ℝ) ^ 2) = K * C₁ / (W : ℝ) ^ 2 by ring]
        exact div_le_div_of_nonneg_right (by nlinarith) hW2'.le

end BlockBand.Transmission.SourceMixing
