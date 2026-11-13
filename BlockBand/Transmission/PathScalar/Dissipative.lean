module

public import BlockBand.Transmission.PassiveCovariance.ResolventBound

/-!
# Deterministic dissipative bounds for the near-end scalar

For a passive input `X` (`Y = -Im X ⪰ 0`), `η = Im z_∂ > 0`, Euclidean operator norm:
* `norm_normTrace_le`: `|W⁻¹ Tr M| ≤ ‖M‖`;
* `passiveY_absorb`: `-Im(X - iε) = Y + ε ⪰ 0` for `ε ≥ 0` (the absorption of a fresh block
  moves into the passive input, `Bridge.pathNearSchur_succ_eq_freshSchur`);
* `jetDistance0_absorb_le`: `δ₀(X - iε) ≤ δ₀(X) + ε/η²` (resolvent identity, `‖R‖ ≤ η⁻¹`);
* `jetDistance0_le_bound`: `δ₀(X) ≤ η⁻¹ + 1` (the deterministic port bound that removes stops).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PathScalar

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.Transmission.PassiveCovariance
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

theorem vecNorm_single (i : Fin W) : vecNorm (Pi.single i (1 : ℂ)) = 1 := by
  rw [vecNorm]
  have : ∑ j, ‖(Pi.single i (1 : ℂ) : Fin W → ℂ) j‖ ^ 2 = 1 := by
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
    simp
  rw [this, Real.sqrt_one]

theorem norm_entry_diag_le (M : Matrix (Fin W) (Fin W) ℂ) (i : Fin W) : ‖M i i‖ ≤ ‖M‖ := by
  have h := norm_bilinear_le (Pi.single i (1 : ℂ)) M (Pi.single i 1)
  rw [vecNorm_single, mul_one, one_mul] at h
  have he : bilinear (Pi.single i (1 : ℂ)) M (Pi.single i 1) = M i i := by
    simp [bilinear, Matrix.col_apply]
  rwa [he] at h

/-- `|W⁻¹ Tr M| ≤ ‖M‖` (operator norm). -/
theorem norm_normTrace_le (M : Matrix (Fin W) (Fin W) ℂ) : ‖(W : ℂ)⁻¹ * M.trace‖ ≤ ‖M‖ := by
  rcases Nat.eq_zero_or_pos W with rfl | hW
  · simp
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have h1 : ‖M.trace‖ ≤ W * ‖M‖ := by
    calc ‖M.trace‖ = ‖∑ i, M i i‖ := rfl
      _ ≤ ∑ i, ‖M i i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin W, ‖M‖ := Finset.sum_le_sum fun i _ => norm_entry_diag_le M i
      _ = W * ‖M‖ := by simp
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (W : ℝ)⁻¹ * ‖M.trace‖ ≤ (W : ℝ)⁻¹ * (W * ‖M‖) := by gcongr
    _ = ‖M‖ := by field_simp

/-- `-Im(X - iε) = -Im X + ε`. -/
theorem passiveY_absorb_eq (X : Matrix (Fin W) (Fin W) ℂ) (ε : ℝ) :
    passiveY (X - (((ε : ℂ) * Complex.I)) • (1 : Matrix (Fin W) (Fin W) ℂ)) =
      passiveY X + (ε : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) := by
  rw [passiveY, passiveY, matrixImaginaryPart_sub,
    matrixImaginaryPart_smul_hermitian _ _ (Matrix.isHermitian_one)]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im,
    Complex.I_re, mul_zero, add_zero]
  abel

/-- The absorbed input stays passive. -/
theorem passiveY_absorb {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef) {ε : ℝ}
    (hε : 0 ≤ ε) :
    (passiveY (X - (((ε : ℂ) * Complex.I)) • (1 : Matrix (Fin W) (Fin W) ℂ))).PosSemidef := by
  rw [passiveY_absorb_eq]
  exact hY.add (Matrix.PosSemidef.one.smul (by exact_mod_cast hε))

section Bounds

variable {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
  {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef)
include hb0 hb h1 h2 hY

/-- **The deterministic port bound**: `δ₀(X) ≤ η⁻¹ + 1` for passive `X`. -/
theorem jetDistance0_le_bound : jetDistance0 b E X ≤ (etaZ b E)⁻¹ + 1 := by
  rw [jetDistance0]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_matchedA E h1 h2]
  have := (norm_normTrace_le (passiveResolvent b E X)).trans
    (norm_passiveResolvent_le hb0 hb h1 h2 hY)
  linarith

/-- **Absorption in the input costs `ε/η²`**: `δ₀(X - iε) ≤ δ₀(X) + ε/η²`, `ε ≥ 0`. -/
theorem jetDistance0_absorb_le {ε : ℝ} (hε : 0 ≤ ε) :
    jetDistance0 b E (X - (((ε : ℂ) * Complex.I)) • (1 : Matrix (Fin W) (Fin W) ℂ)) ≤
      jetDistance0 b E X + ε / etaZ b E ^ 2 := by
  have hη := etaZ_pos b E (by linarith) h1 h2
  set X' := X - (((ε : ℂ) * Complex.I)) • (1 : Matrix (Fin W) (Fin W) ℂ)
  have hY' := passiveY_absorb hY hε
  set K := boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X
  set K' := boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X'
  have hK := passive_inverse_constructed K _ hη hY (matrixImaginaryPart_nearPencil b E X)
  have hK' := passive_inverse_constructed K' _ hη hY' (matrixImaginaryPart_nearPencil b E X')
  have hdiff : passiveResolvent b E X' - passiveResolvent b E X =
      K'⁻¹ * (-(((ε : ℂ) * Complex.I)) • (1 : Matrix (Fin W) (Fin W) ℂ)) * K⁻¹ := by
    have hKK : K - K' = -(((ε : ℂ) * Complex.I)) • (1 : Matrix (Fin W) (Fin W) ℂ) := by
      simp only [K, K', X', neg_smul]; abel
    rw [← hKK, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hK.2.1, Matrix.mul_one,
      hK'.2.2, Matrix.one_mul]
    rfl
  have hR := norm_passiveResolvent_le hb0 hb h1 h2 hY
  have hR' := norm_passiveResolvent_le hb0 hb h1 h2 hY'
  have hnorm : ‖passiveResolvent b E X' - passiveResolvent b E X‖ ≤ ε / etaZ b E ^ 2 := by
    rw [hdiff]
    have hs : ‖-(((ε : ℂ) * Complex.I)) • (1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ ε := by
      refine (norm_smul_le _ _).trans ?_
      have : ‖-((ε : ℂ) * Complex.I)‖ = ε := by
        rw [norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hε]
      rw [this]
      exact mul_le_of_le_one_right hε norm_one_matrix_le
    calc ‖K'⁻¹ * (-(((ε : ℂ) * Complex.I)) • (1 : Matrix (Fin W) (Fin W) ℂ)) * K⁻¹‖
        ≤ ‖K'⁻¹‖ * ‖-(((ε : ℂ) * Complex.I)) • (1 : Matrix (Fin W) (Fin W) ℂ)‖ * ‖K⁻¹‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (etaZ b E)⁻¹ * ε * (etaZ b E)⁻¹ := by
          gcongr
          · exact hR'
          · exact hR
      _ = ε / etaZ b E ^ 2 := by field_simp
  rw [jetDistance0, jetDistance0]
  calc ‖(W : ℂ)⁻¹ * (passiveResolvent b E X').trace - matchedA E‖
      ≤ ‖(W : ℂ)⁻¹ * (passiveResolvent b E X' - passiveResolvent b E X).trace‖ +
          ‖(W : ℂ)⁻¹ * (passiveResolvent b E X).trace - matchedA E‖ := by
        rw [Matrix.trace_sub, mul_sub]
        exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans_eq (by rw [add_comm]) |>.trans
          (by rw [add_comm])
    _ ≤ ε / etaZ b E ^ 2 + ‖(W : ℂ)⁻¹ * (passiveResolvent b E X).trace - matchedA E‖ := by
        gcongr; exact (norm_normTrace_le _).trans hnorm
    _ = _ := add_comm _ _

end Bounds

end BlockBand.Transmission.PathScalar
