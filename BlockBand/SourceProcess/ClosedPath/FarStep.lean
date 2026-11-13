module

public import BlockBand.Transmission.Bridge.TransportFull
public import BlockBand.SourceProcess.ClosedPath.TimeSMain

/-!
# Near-end growth keeps the far port: the closed path is transported

The path grows at the near end, so the far lead is the same at every length:

* `one_sub_nearPortProj_mul_transportN` (every `ω`): the one-step transport keeps the far input,
  `(1-P)N_j = 1-P` (`N = [[L, Δℝ₁₂], [0, I]]`).
* **`ae_farOut_succ`** (a.s., `0 < b < 1/2`, `-2 < E < 2`, `W ≥ 1`, all `j ≥ 1`): it keeps the far
  output, `(1-P)𝕊_jN_j = (1-P)𝕊_{j+1}`. From the port row `Cᴴ𝒰_j + zℝ_j = 1` and the bridge
  formula for `ℝ_{j+1}`: the far rows of `ℝ_{j+1}` are those of `ℝ_jN_j`.
* **`ae_closedCol_transport`**: hence, a.s., for every `j ≥ 1` and every phase `z` at which
  `1 - zN` is invertible at `j` and `j+1` (true when `‖r‖ < 1`), the closed columns
  obey `C_{j+1}(z)ᴴ N_jᴴ = (N^cl_j)ᴴ C_j(z)ᴴ` with the closed transport `N^cl_j = (1-A)N_jC_{j+1}`:
  the path closed at time `s` and grown, and the path closed at the final time, produce the
  same closed probe and current columns.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedPath

open MeasureTheory Matrix BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedLimit
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers BlockBand.Transmission.Bridge

variable {W : ℕ} {b E : ℝ}

theorem one_sub_nearPortProj_mul_nearSel_conj :
    (1 - nearPortProj W) * (nearSel W)ᴴ = 0 := by
  ext x a
  simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, nearPortProj, diagonal_mul,
    conjTranspose_apply, nearSel, Matrix.zero_apply]
  by_cases hx : x = (0, a)
  · simp [hx]
  · simp [hx]

/-- **The transport keeps the far input**: `(1-P)N_j = 1-P`. -/
theorem one_sub_nearPortProj_mul_transportN (j : ℕ) (ω : GrowthPath W) :
    (1 - nearPortProj W) * transportN b E W j ω = 1 - nearPortProj W := by
  ext ⟨i, a⟩ ⟨k, c⟩
  simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, nearPortProj, diagonal_mul,
    diagonal_apply]
  fin_cases i <;> fin_cases k <;> simp [freshTransport, one_apply]

/-- **The transport keeps the far output**, almost surely: `(1-P)𝕊_jN_j = (1-P)𝕊_{j+1}`. -/
theorem ae_farOut_succ (hb : 0 < b) (hb2 : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hW : 1 ≤ W) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ j, 1 ≤ j →
      (1 - nearPortProj W) * scatteringMatrix b E W j ω * transportN b E W j ω =
        (1 - nearPortProj W) * scatteringMatrix b E W (j + 1) ω := by
  filter_upwards [ae_boundaryToInterior_succ_full hb hb2 hE1 hE2 hW, ae_growth_isHermitian W b,
    ae_isUnit_pathPencil_growth hb2 hW E] with ω hU hA hF j hj
  have hη := boundaryZ_im_pos (b := b) (by linarith) hE1 hE2
  have hz : boundaryZ b E ≠ 0 := fun h0 => by rw [h0] at hη; simp at hη
  obtain ⟨-, hR⟩ := hU j hj
  have hsol := (full_solution b E j ω (isUnit_fullPathMatrix b E j ω hA hη (hF j))).2
  rw [coupling_split, conjTranspose_add, conjTranspose_mul] at hsol
  set Pc := 1 - nearPortProj W
  set N := transportN b E W j ω
  set U := boundaryToInterior b E W j ω
  set R := boundaryResolvent b E W j ω
  set Cf := farCoupling W j ω
  have hPS := one_sub_nearPortProj_mul_nearSel_conj (W := W)
  have hPN : Pc * N = Pc := one_sub_nearPortProj_mul_transportN j ω
  have h1 : Pc * (boundaryZ b E • R) = Pc - Pc * (Cfᴴ * U) := by
    have := congrArg (Pc * ·) hsol
    simp only [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul] at this
    rw [Matrix.mul_assoc (nearSel W)ᴴ, ← Matrix.mul_assoc Pc (nearSel W)ᴴ, hPS, Matrix.zero_mul,
      zero_add] at this
    rw [eq_sub_iff_add_eq, add_comm]; exact this
  have hR' : Pc * R = (boundaryZ b E)⁻¹ • (Pc - Pc * (Cfᴴ * U)) := by
    rw [← h1, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hz, one_smul]
  have h2 : Pc * boundaryResolvent b E W (j + 1) ω =
      (boundaryZ b E)⁻¹ • (Pc - Pc * (Cfᴴ * (U * N))) := by
    rw [hR, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, conjTranspose_mul,
      Matrix.mul_assoc, ← Matrix.mul_assoc Pc, hPS, Matrix.zero_mul, sub_zero]
  have h3 : Pc * R * N = Pc * boundaryResolvent b E W (j + 1) ω := by
    rw [hR', h2, Matrix.smul_mul, Matrix.sub_mul, hPN, Matrix.mul_assoc Pc, Matrix.mul_assoc Cfᴴ]
  simp only [scatteringMatrix, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul]
  rw [hPN]
  change Pc - ((2 * etaZ b E : ℝ) * Complex.I) • (Pc * R * N) = _
  rw [h3]

/-- **Closing at time `s` and growing = closing at the final time**, one step, almost surely. -/
theorem ae_closedCol_transport {s h : ℝ} (hb : 0 < b) (hb2 : b < 1 / 2) (hE1 : -2 < E)
    (hE2 : E < 2) (hW : 1 ≤ W) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ j, 1 ≤ j → ∀ z : ℂ,
      IsUnit (1 - z • closingN (scatteringMatrix b E W j ω)
        (farEmbed (omittedProj b E h W (closeLen s W) ω))
        (farEmbed (closingPairing b E h W (closeLen s W) ω))).det →
      IsUnit (1 - z • closingN (scatteringMatrix b E W (j + 1) ω)
        (farEmbed (omittedProj b E h W (closeLen s W) ω))
        (farEmbed (closingPairing b E h W (closeLen s W) ω))).det →
      (physClosingMapAt b E s h W (j + 1) ω z)ᴴ * (transportN b E W j ω)ᴴ =
        ((1 - farEmbed (omittedProj b E h W (closeLen s W) ω)) *
          (transportN b E W j ω * physClosingMapAt b E s h W (j + 1) ω z))ᴴ *
          (physClosingMapAt b E s h W j ω z)ᴴ := by
  filter_upwards [ae_farOut_succ hb hb2 hE1 hE2 hW] with ω hS j hj z hU₀ hU₁
  have hAA : farEmbed (omittedProj b E h W (closeLen s W) ω) *
      farEmbed (omittedProj b E h W (closeLen s W) ω) =
        farEmbed (omittedProj b E h W (closeLen s W) ω) := by
    rw [farEmbed_mul, omittedProj_mul_self]
  have hAPi : farEmbed (omittedProj b E h W (closeLen s W) ω) *
      farEmbed (closingPairing b E h W (closeLen s W) ω) =
        farEmbed (closingPairing b E h W (closeLen s W) ω) := by
    rw [farEmbed_mul, omittedProj_mul_closingPairing]
  have hcomp : ∀ X : Matrix (Fin W) (Fin W) ℂ, farEmbed X * (1 - nearPortProj W) = farEmbed X :=
    fun X => by rw [Matrix.mul_sub, Matrix.mul_one, farEmbed_mul_nearPortProj, sub_zero]
  exact closingMap_conj_transport hAA hAPi (hcomp _) (hcomp _)
    (one_sub_nearPortProj_mul_transportN j ω) (hS j hj) hU₀ hU₁

end BlockBand.SourceProcess.ClosedPath
