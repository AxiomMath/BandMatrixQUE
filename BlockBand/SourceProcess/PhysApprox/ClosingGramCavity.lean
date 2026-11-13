module

public import BlockBand.SourceProcess.PhysApprox.ClosingAnalyticAlg
public import BlockBand.SourceProcess.PhysApprox.ClosingGramAlg
public import BlockBand.SourceProcess.Closing.HardyMain

/-!
# The output leakage bounds the closed current correction

For `N = Π𝕊A` with `N^n → 0`, `A` an orthogonal projection, `ΠΠᴴ = A`, `𝕊ᴴ𝕊 = 1`, and an
orthogonal projection `P` with `PΠᴴ = 0`, every `v` satisfies
`∫⁻ ‖P𝕊 Z(z) v‖² dz ≤ ‖Π𝕊 v‖²` (`lintegral_cavity_le`), `Z(z) = z(1 - zN)⁻¹Π𝕊`.

Proof (no series): `K = Z(z)v` solves `K = z(w + NK)`, `w = Π𝕊v`, and `AK = K`; so
`‖P𝕊K‖² + ‖NK‖² = ‖P𝕊K‖² + ‖Π𝕊K‖² ≤ ‖K‖² = ‖w + NK‖²`, i.e.
`‖P𝕊K‖² ≤ ‖w‖² + 2 Re⟨w, NK⟩` pointwise; and `E_z Z(z) = 0` (`phaseAvg_closingZ`: `Z` is
`closingX` for `(𝕊, A, Π)` plus `closingX` for `(2N, ½, 1)`, both of phase average `0` by
`phaseAvg_closingX`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox

open MeasureTheory Matrix Filter Topology
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosingAux
open BlockBand.SourceProcess.ClosingLeak

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem closingN_half (N : Matrix ι ι ℂ) :
    closingN ((2 : ℂ) • N) ((1 / 2 : ℂ) • 1) 1 = N := by
  rw [closingN, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul]
  norm_num

theorem closingT_half (N : Matrix ι ι ℂ) :
    closingT ((2 : ℂ) • N) ((1 / 2 : ℂ) • 1) 1 = N := by
  rw [closingT, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_one,
    smul_smul, ← sub_smul]
  norm_num

/-- `Z(z) = closingX(𝕊, A, Π) + closingX(2N, ½, 1)`. -/
theorem closingZ_phase_eq (S A Pi : Matrix ι ι ℂ) (θ : ℝ) :
    closingZ S A Pi (phase θ) =
      closingX S A Pi θ + closingX ((2 : ℂ) • closingN S A Pi) ((1 / 2 : ℂ) • 1) 1 θ := by
  rw [closingX, closingX, closingN_half, closingT_half, closingZ, ← Matrix.mul_add, ← smul_add,
    closingT, closingN, ← Matrix.mul_add, sub_add_cancel, Matrix.mul_smul, Matrix.mul_one]

theorem continuous_closingZ {S A Pi : Matrix ι ι ℂ}
    (hU : ∀ θ, IsUnit (1 - phase θ • closingN S A Pi).det) :
    Continuous fun θ => closingZ S A Pi (phase θ) := by
  have hU' : ∀ θ, IsUnit (1 - phase θ •
      closingN ((2 : ℂ) • closingN S A Pi) ((1 / 2 : ℂ) • 1) 1).det := by
    intro θ; rw [closingN_half]; exact hU θ
  simp_rw [closingZ_phase_eq]
  exact (continuous_closingX hU).add (continuous_closingX hU')

/-- **`E_z Z(z) = 0`**. -/
theorem phaseAvg_closingZ {S A Pi : Matrix ι ι ℂ}
    (hN : Tendsto (fun n => closingN S A Pi ^ n) atTop (𝓝 0)) :
    phaseAvg (fun θ => closingZ S A Pi (phase θ)) = 0 := by
  have hU : ∀ θ, IsUnit (1 - phase θ • closingN S A Pi).det :=
    fun θ => isUnit_det_of_tendsto hN (norm_phase θ)
  have hU' : ∀ θ, IsUnit (1 - phase θ •
      closingN ((2 : ℂ) • closingN S A Pi) ((1 / 2 : ℂ) • 1) 1).det := by
    intro θ; rw [closingN_half]; exact hU θ
  have hN' : Tendsto (fun n =>
      closingN ((2 : ℂ) • closingN S A Pi) ((1 / 2 : ℂ) • 1) 1 ^ n) atTop (𝓝 0) := by
    simpa only [closingN_half] using hN
  simp_rw [closingZ_phase_eq]
  rw [phaseAvg_add (continuous_closingX hU) (continuous_closingX hU'), phaseAvg_closingX hN,
    phaseAvg_closingX hN', add_zero]

/-- The fixed point `Z(z)v = z(Π𝕊v + N Z(z)v)`. -/
theorem closingZ_mulVec_fixed {S A Pi : Matrix ι ι ℂ} {z : ℂ}
    (hU : IsUnit (1 - z • closingN S A Pi).det) (v : ι → ℂ) :
    closingZ S A Pi z *ᵥ v =
      z • (Pi *ᵥ (S *ᵥ v) + closingN S A Pi *ᵥ (closingZ S A Pi z *ᵥ v)) := by
  have hLQ := mul_nonsing_inv (1 - z • closingN S A Pi) hU
  have hQ1 : (1 - z • closingN S A Pi)⁻¹ =
      1 + z • (closingN S A Pi * (1 - z • closingN S A Pi)⁻¹) := by
    have h := hLQ
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul] at h
    conv_lhs => rw [← sub_add_cancel (1 - z • closingN S A Pi)⁻¹
      (z • (closingN S A Pi * (1 - z • closingN S A Pi)⁻¹)), h]
  have hmat : closingZ S A Pi z = z • (Pi * S + closingN S A Pi * closingZ S A Pi z) := by
    have h1 : (1 - z • closingN S A Pi)⁻¹ * (Pi * S) =
        Pi * S + closingN S A Pi * (z • ((1 - z • closingN S A Pi)⁻¹ * (Pi * S))) := by
      conv_lhs => rw [hQ1]
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
    change z • ((1 - z • closingN S A Pi)⁻¹ * (Pi * S)) =
      z • (Pi * S + closingN S A Pi * (z • ((1 - z • closingN S A Pi)⁻¹ * (Pi * S))))
    rw [← h1]
  conv_lhs => rw [hmat]
  rw [Matrix.smul_mulVec, add_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]

omit [DecidableEq ι] in
theorem l2_smul_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) (u : ι → ℂ) : l2 (z • u) = l2 u := by
  simp only [l2, Pi.smul_apply, smul_eq_mul, norm_mul, hz, one_mul]

/-- `‖Py‖² + ‖Πy‖² ≤ ‖y‖²` for orthogonal projections `P`, `ΠᴴΠ` with `PΠᴴ = 0`. -/
theorem l2_proj_add_le {P Pi : Matrix ι ι ℂ} (hP2 : P * P = P) (hPH : Pᴴ = P)
    (hPiP : Pi * Piᴴ * Pi = Pi) (hPPi : P * Piᴴ = 0) (y : ι → ℂ) :
    l2 (P *ᵥ y) ^ 2 + l2 (Pi *ᵥ y) ^ 2 ≤ l2 y ^ 2 := by
  set B := P + Piᴴ * Pi with hB
  have hPB : P * (Piᴴ * Pi) = 0 := by rw [← Matrix.mul_assoc, hPPi, Matrix.zero_mul]
  have hBP : Piᴴ * Pi * P = 0 := by
    have h := congrArg conjTranspose hPB
    rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hPH,
      conjTranspose_zero] at h
  have hQQ : Piᴴ * Pi * (Piᴴ * Pi) = Piᴴ * Pi := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Pi, hPiP]
  have hB2 : B * B = B := by
    rw [hB, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hP2, hPB, hBP, hQQ, add_zero,
      zero_add]
  have hBH : Bᴴ = B := by
    rw [hB, conjTranspose_add, hPH, conjTranspose_mul, conjTranspose_conjTranspose]
  have h := l2_mulVec_le_of_proj hB2 hBH y
  have e : l2 (B *ᵥ y) ^ 2 = l2 (P *ᵥ y) ^ 2 + l2 (Pi *ᵥ y) ^ 2 := by
    rw [l2_sq, l2_sq, l2_sq, star_mulVec_dotProduct, star_mulVec_dotProduct,
      star_mulVec_dotProduct, hBH, hB2, hB, add_mulVec, dotProduct_add, Complex.add_re,
      hPH, hP2]
  rw [← e]
  exact pow_le_pow_left₀ (l2_nonneg _) h 2

omit [DecidableEq ι] in
/-- `‖u + v‖² = ‖u‖² + 2 Re⟨u, v⟩ + ‖v‖²`. -/
theorem l2_add_sq (u v : ι → ℂ) :
    l2 (u + v) ^ 2 = l2 u ^ 2 + 2 * (star u ⬝ᵥ v).re + l2 v ^ 2 := by
  rw [l2_sq, l2_sq, l2_sq, star_add, add_dotProduct, dotProduct_add, dotProduct_add,
    Complex.add_re, Complex.add_re, Complex.add_re]
  have : (star v ⬝ᵥ u).re = (star u ⬝ᵥ v).re := by
    simp only [dotProduct, Pi.star_apply, Complex.re_sum, Complex.mul_re, Complex.star_def,
      Complex.conj_re, Complex.conj_im]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this]
  ring

/-- The pointwise energy inequality `‖P𝕊K‖² ≤ ‖w‖² + 2 Re⟨w, NK⟩`, `K = Z(z)v`, `w = Π𝕊v`. -/
theorem cavity_pointwise {S A Pi P : Matrix ι ι ℂ} (hA2 : A * A = A) (hAH : Aᴴ = A)
    (hPi : Pi * Piᴴ = A) (hS : Sᴴ * S = 1) (hP2 : P * P = P) (hPH : Pᴴ = P)
    (hPPi : P * Piᴴ = 0) {z : ℂ} (hz : ‖z‖ = 1) (hUz : IsUnit (1 - z • closingN S A Pi).det)
    (v : ι → ℂ) :
    l2 (P *ᵥ (S *ᵥ (closingZ S A Pi z *ᵥ v))) ^ 2 ≤ l2 (Pi *ᵥ (S *ᵥ v)) ^ 2 +
      2 * (star (Pi *ᵥ (S *ᵥ v)) ⬝ᵥ ((closingN S A Pi * closingZ S A Pi z) *ᵥ v)).re := by
  have hAPi : A * Pi = Pi := proj_mul_partialIso hA2 hAH hPi
  have hPiP : Pi * Piᴴ * Pi = Pi := by rw [hPi, hAPi]
  have hAN : A * closingN S A Pi = closingN S A Pi := by
    rw [closingN]
    simp only [← Matrix.mul_assoc, hAPi]
  have hAw : A *ᵥ (Pi *ᵥ (S *ᵥ v)) = Pi *ᵥ (S *ᵥ v) := by rw [mulVec_mulVec, hAPi]
  rw [← mulVec_mulVec]
  have hfix := closingZ_mulVec_fixed hUz v
  generalize closingZ S A Pi z *ᵥ v = K at hfix ⊢
  generalize Pi *ᵥ (S *ᵥ v) = w at hfix hAw ⊢
  have hAK : A *ᵥ K = K := by
    rw [hfix, mulVec_smul, mulVec_add, hAw, mulVec_mulVec, hAN]
  have hNK : closingN S A Pi *ᵥ K = Pi *ᵥ (S *ᵥ K) := by
    rw [closingN, ← mulVec_mulVec, hAK, ← mulVec_mulVec]
  have hE := l2_proj_add_le hP2 hPH hPiP hPPi (S *ᵥ K)
  rw [l2_mulVec_of_unitary hS, ← hNK] at hE
  have hKn : l2 K ^ 2 = l2 (w + closingN S A Pi *ᵥ K) ^ 2 := by
    conv_lhs => rw [hfix]
    rw [l2_smul_of_norm_one hz]
  rw [hKn, l2_add_sq] at hE
  linarith

omit [DecidableEq ι] in
/-- `∫ u ⬝ (f(θ) v) = u ⬝ (E_z f v)` for continuous `f`. -/
theorem integral_dotProduct_mulVec {f : ℝ → Matrix ι ι ℂ} (hf : Continuous f) (u v : ι → ℂ) :
    ∫ θ, u ⬝ᵥ (f θ *ᵥ v) ∂phaseLaw = u ⬝ᵥ (phaseAvg f *ᵥ v) := by
  simp only [dotProduct, mulVec, phaseAvg, Matrix.of_apply]
  rw [integral_finsetSum _ fun i _ => (integrable_finsetSum _ fun l _ =>
    (integrable_entry hf i l).mul_const (v l)).const_mul (u i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, integral_finsetSum _ fun l _ => (integrable_entry hf i l).mul_const (v l)]
  simp_rw [integral_mul_const]

/-- **The cavity bound**: `∫⁻ ‖P𝕊Z(z)v‖² dz ≤ ‖Π𝕊v‖²`. -/
theorem lintegral_cavity_le {S A Pi P : Matrix ι ι ℂ} (hA2 : A * A = A) (hAH : Aᴴ = A)
    (hPi : Pi * Piᴴ = A) (hS : Sᴴ * S = 1)
    (hN : Tendsto (fun n => closingN S A Pi ^ n) atTop (𝓝 0)) (hP2 : P * P = P) (hPH : Pᴴ = P)
    (hPPi : P * Piᴴ = 0) (v : ι → ℂ) :
    ∫⁻ θ, ENNReal.ofReal (l2 (P *ᵥ (S *ᵥ (closingZ S A Pi (phase θ) *ᵥ v))) ^ 2) ∂phaseLaw ≤
      ENNReal.ofReal (l2 (Pi *ᵥ (S *ᵥ v)) ^ 2) := by
  have hU : ∀ θ, IsUnit (1 - phase θ • closingN S A Pi).det :=
    fun θ => isUnit_det_of_tendsto hN (norm_phase θ)
  set N := closingN S A Pi
  set w := Pi *ᵥ (S *ᵥ v)
  have hpt : ∀ θ, l2 (P *ᵥ (S *ᵥ (closingZ S A Pi (phase θ) *ᵥ v))) ^ 2 ≤
      l2 w ^ 2 + 2 * (star w ⬝ᵥ ((N * closingZ S A Pi (phase θ)) *ᵥ v)).re :=
    fun θ => cavity_pointwise hA2 hAH hPi hS hP2 hPH hPPi (norm_phase θ) (hU θ) v
  -- the phase average of the cross term vanishes
  have hZc := continuous_closingZ hU
  have hNZc : Continuous fun θ => N * closingZ S A Pi (phase θ) := continuous_const.matrix_mul hZc
  have hcont : Continuous fun θ => star w ⬝ᵥ ((N * closingZ S A Pi (phase θ)) *ᵥ v) :=
    continuous_const.dotProduct (hNZc.matrix_mulVec continuous_const)
  have hint' : Integrable (fun θ => star w ⬝ᵥ ((N * closingZ S A Pi (phase θ)) *ᵥ v))
      phaseLaw := integrable_of_continuous hcont
  have hre : Integrable (fun θ => (star w ⬝ᵥ ((N * closingZ S A Pi (phase θ)) *ᵥ v)).re)
      phaseLaw := hint'.re
  have hcross : ∫ θ, (star w ⬝ᵥ ((N * closingZ S A Pi (phase θ)) *ᵥ v)).re ∂phaseLaw = 0 := by
    have e : ∫ θ, star w ⬝ᵥ ((N * closingZ S A Pi (phase θ)) *ᵥ v) ∂phaseLaw = 0 := by
      rw [integral_dotProduct_mulVec hNZc, phaseAvg_mul_left _ hZc, phaseAvg_closingZ hN,
        Matrix.mul_zero, zero_mulVec, dotProduct_zero]
    rw [show ∫ θ, (star w ⬝ᵥ ((N * closingZ S A Pi (phase θ)) *ᵥ v)).re ∂phaseLaw =
      (∫ θ, star w ⬝ᵥ ((N * closingZ S A Pi (phase θ)) *ᵥ v) ∂phaseLaw).re from integral_re hint',
      e, Complex.zero_re]
  have hg : Integrable (fun θ => l2 w ^ 2 +
      2 * (star w ⬝ᵥ ((N * closingZ S A Pi (phase θ)) *ᵥ v)).re) phaseLaw :=
    (integrable_const _).add (hre.const_mul _)
  have hg0 : 0 ≤ᵐ[phaseLaw] fun θ => l2 w ^ 2 +
      2 * (star w ⬝ᵥ ((N * closingZ S A Pi (phase θ)) *ᵥ v)).re :=
    ae_of_all _ fun θ => (sq_nonneg _).trans (hpt θ)
  calc ∫⁻ θ, ENNReal.ofReal (l2 (P *ᵥ (S *ᵥ (closingZ S A Pi (phase θ) *ᵥ v))) ^ 2) ∂phaseLaw
      ≤ ∫⁻ θ, ENNReal.ofReal (l2 w ^ 2 +
          2 * (star w ⬝ᵥ ((N * closingZ S A Pi (phase θ)) *ᵥ v)).re) ∂phaseLaw :=
        lintegral_mono fun θ => ENNReal.ofReal_le_ofReal (hpt θ)
    _ = ENNReal.ofReal (∫ θ, (l2 w ^ 2 +
          2 * (star w ⬝ᵥ ((N * closingZ S A Pi (phase θ)) *ᵥ v)).re) ∂phaseLaw) :=
        (ofReal_integral_eq_lintegral_ofReal hg hg0).symm
    _ = ENNReal.ofReal (l2 w ^ 2) := by
        rw [integral_add (integrable_const _) (hre.const_mul _), integral_const_mul, hcross,
          integral_const, probReal_univ, one_smul, mul_zero, add_zero]

end BlockBand.SourceProcess.PhysApprox
