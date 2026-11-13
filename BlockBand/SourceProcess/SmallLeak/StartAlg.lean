module

public import BlockBand.SourceProcess.SmallLeak.FluxMean
public import BlockBand.SourceProcess.FullSourceStops.CurrentPast
public import BlockBand.Transmission.FractionalBulk.Spectral

/-!
# The omitted flux at the closing time: `g ≤ h Tr T^{1/2}`

At a Hermitian two-port `𝕏` (unitary `𝕊`), with `T_far = 1 - 𝕊₁₁ᴴ𝕊₁₁` and
`A = 1_{[0,h²]}(T_far)`:
* `Re Tr FP'F = Re Tr(A T_far A)` (`P'_ff = 𝕊₀₁ᴴ𝕊₀₁ = T_far`);
* `Re Tr(A T_far A) = Σ_{t_i ≤ h²} t_i ≤ h Σ_i t_i^{1/2} = h Tr T_far^{1/2}` (`trace_cfc_re`);
* `Tr T_far^{1/2} = Tr T^{1/2}` for the near transmission `T = T(nearSchur z 𝕏)` (the far and
  near transmission eigenvalues coincide; `nuclearNorm_current_eq`, applied to `𝕊` and to
  the port-swapped scattering matrix through the charpoly identities).
Result: `start_flux_le`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SmallLeak

open Matrix
open BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.Bridge BlockBand.SourceProcess.Closing
open BlockBand.SourceProcess.FullSourceStops BlockBand.Transmission.FractionalBulk
open scoped Matrix ComplexOrder

variable {W : ℕ}

section Spectral

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `Re Tr f(T) = Σ_i f(λ_i)` for Hermitian `T`. -/
theorem trace_cfc_re {T : Matrix n n ℂ} (hT : T.IsHermitian) (f : ℝ → ℝ) :
    (cfc f T).trace.re = ∑ i, f (hT.eigenvalues i) := by
  rw [hT.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Matrix.star_eq_conjTranspose, unitary_star_mul, Matrix.one_mul, trace_diagonal, Complex.re_sum]
  simp

/-- **`Re Tr(A T A) ≤ h Tr T^{1/2}`**, `A = 1_{[0,h²]}(T)`, for `T ⪰ 0`, `h ≥ 0`. -/
theorem trace_omitted_le {T : Matrix n n ℂ} (hT : T.PosSemidef) {h : ℝ} (hh : 0 ≤ h) :
    (cfc (omitIndicator h) T * T * cfc (omitIndicator h) T).trace.re ≤
      h * fracTrace (1 / 2) T := by
  have hc := fun f : ℝ → ℝ => T.finite_real_spectrum.continuousOn f
  have e : cfc (omitIndicator h) T * T * cfc (omitIndicator h) T =
      cfc (fun t => omitIndicator h t * t * omitIndicator h t) T := by
    have hsa : IsSelfAdjoint T := hT.1
    rw [cfc_mul _ _ T (hc _) (hc _), cfc_mul _ _ T (hc _) (hc _), cfc_id' ℝ T hsa]
  rw [e, trace_cfc_re hT.1, fracTrace_eq_sum_eigenvalues_psd hT, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hl := hT.eigenvalues_nonneg i
  set t := hT.1.eigenvalues i
  unfold omitIndicator
  split_ifs with ht
  · rw [mul_one, one_mul, ← Real.sqrt_eq_rpow]
    have hs : Real.sqrt t ≤ h := by
      rw [show h = Real.sqrt (h ^ 2) from (Real.sqrt_sq hh).symm]; exact Real.sqrt_le_sqrt ht
    calc t = Real.sqrt t * Real.sqrt t := (Real.mul_self_sqrt hl).symm
      _ ≤ h * Real.sqrt t := mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg _)
  · simp only [mul_zero, zero_mul]; positivity

end Spectral

theorem trace_farEmbed (X : Matrix (Fin W) (Fin W) ℂ) : (farEmbed X).trace = X.trace := by
  simp [farEmbed, Matrix.trace, Fintype.sum_prod_type]

theorem farEmbed_sandwich (A : Matrix (Fin W) (Fin W) ℂ) (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    farEmbed A * M * farEmbed A = farEmbed (A * portBlock M 1 1 * A) := by
  ext ⟨i, x⟩ ⟨j, y⟩
  simp only [farEmbed, portBlock, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp

/-- **The omitted flux at the closing two-port**: `Re Tr FP'F ≤ h Tr T^{1/2}`, `T` the near
transmission, `F = farEmbed 1_{[0,h²]}(1 - 𝕊₁₁ᴴ𝕊₁₁)`. -/
theorem start_flux_le {b E : ℝ} (hη : 0 < etaZ b E) {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hXX : XX.IsHermitian) {h : ℝ} (hh : 0 ≤ h) :
    let S := twoPortScattering b E XX
    let A := cfc (omitIndicator h) (1 - (portBlock S 1 1)ᴴ * portBlock S 1 1)
    (farEmbed A * (Sᴴ * nearProjection W * S) * farEmbed A).trace.re ≤
      h * fracTrace (1 / 2) (passiveTransmission b E (nearSchur (boundaryZ b E) XX)) := by
  intro S A
  have hS := twoPortScattering_unitary b E XX hXX (by simpa [etaZ] using hη)
  set c := portBlock S 0 1
  set d := portBlock S 1 1
  set a := portBlock S 0 0
  set Tf := 1 - dᴴ * d
  have hcc : cᴴ * c = Tf := by
    have h1 := congrArg (fun M => portBlock M 1 1) hS.1
    simp only [portBlock_mul, portBlock_conjTranspose, portBlock_one, ite_true] at h1
    simp only [Tf, c, d, ← h1]; abel
  have hTf : Tf.PosSemidef := by rw [← hcc]; exact Matrix.posSemidef_conjTranspose_mul_self c
  -- the flux is `Re Tr(A T_far A)`
  have e1 : (farEmbed A * (Sᴴ * nearProjection W * S) * farEmbed A).trace.re =
      (A * Tf * A).trace.re := by
    rw [farEmbed_sandwich, trace_farEmbed, portBlock_sandwich_far, hcc]
  rw [e1]
  refine (trace_omitted_le hTf hh).trans (le_of_eq ?_)
  congr 1
  -- far and near transmission spectra agree
  have hnear := nuclearNorm_twoPortCurrent_eq b E XX hXX (by simpa [etaZ] using hη)
  rw [nuclearNorm_current_eq S hS.2] at hnear
  have hfa : fracTrace (1 / 2) Tf = fracTrace (1 / 2) (1 - aᴴ * a) := by
    refine fracTrace_congr ?_
    have hcc' : c * cᴴ = 1 - a * aᴴ := by
      have h2 := congrArg (fun M => portBlock M 0 0) hS.2
      simp only [portBlock_mul, portBlock_conjTranspose, portBlock_one, ite_true] at h2
      simp only [a, c, ← h2]; abel
    rw [← hcc, Matrix.charpoly_mul_comm, hcc', charpoly_one_sub_mul_comm]
  rw [hfa]
  linarith

end BlockBand.SourceProcess.SmallLeak
