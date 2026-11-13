module

public import BlockBand.Palm.MomentFlow.LocalSpectral
public import BlockBand.Palm.MomentFlow.MaxShell

/-!
# The two-sided trace spectral identity

For Hermitian `H` with increasing eigenvalues `λ_k = freshEigenvalue H k` and `Im z ≠ 0`:

* `trace_resolvent_eigenbasis`: `Tr (H - z)⁻¹ = Σ_k (μ_k - z)⁻¹` over Mathlib's eigenvalues `μ_k`;
* `trace_resolvent_spectral`: the same over the increasing labels `λ_k`;
* **`normalizedTrace_resolvent_im`**: `Im ⟨(H - x - iη)⁻¹⟩ = (1/N) Σ_k η/((λ_k - x)² + η²)`
  (`η ≠ 0`), the two-sided form used for the averaged local law, in the kernel form of the
  averaged identity;
* `normalizedTrace_resolvent_im_kerAt`: at `x = λ_i`, `Im ⟨(H - λ_i - iη)⁻¹⟩ = Σ_j kerAt λ η i j`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Foundations.Spectral BlockBand.Model.Construction BlockBand.Palm
open BlockBand.Palm.CoarseRelative

variable {N : ℕ}

/-- `Tr (H - z)⁻¹ = Σ_k (μ_k - z)⁻¹` over Mathlib's eigenvalues. -/
theorem trace_resolvent_eigenbasis {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) :
    ((H - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹).trace =
      ∑ k, (((hH.eigenvalues k : ℝ) : ℂ) - z)⁻¹ := by
  have hR := certificateMatrixResolvent_eq_spectral H hH hz
  unfold certificateMatrixResolvent profileSpectralAut at hR
  rw [hR, Unitary.conjStarAlgAut_apply]
  set U : Matrix (Fin N) (Fin N) ℂ := ↑(hH.eigenvectorUnitary)
  have hU : star U * U = 1 := Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul, Matrix.trace_diagonal]
  rfl

/-- `Tr (H - z)⁻¹ = Σ_k (λ_k - z)⁻¹` over the increasing labels. -/
theorem trace_resolvent_spectral {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) {z : ℂ}
    (hz : z.im ≠ 0) :
    ((H - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹).trace =
      ∑ k, (((freshEigenvalue H k : ℝ) : ℂ) - z)⁻¹ := by
  rw [trace_resolvent_eigenbasis hH hz]
  set e : Fin N ≃ Fin N := (finCongr (Fintype.card_fin N).symm).trans increasingIndex
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hev : hH.eigenvalues (e j) = freshEigenvalue H j := by
    simp only [e, Equiv.trans_apply, finCongr_apply, eigenvalue_increasingIndex,
      freshEigenvalue, rawIncreasingEigenvalue_eq _ H hH]
  rw [hev]

/-- **Two-sided trace spectral identity.**
`Im ⟨(H - x - iη)⁻¹⟩ = (1/N) Σ_k η/((λ_k - x)² + η²)` for Hermitian `H`, `η ≠ 0`. -/
theorem normalizedTrace_resolvent_im {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    (x : ℝ) {η : ℝ} (hη : η ≠ 0) :
    (BlockBand.External.CEH.normalizedTrace
      ((H - (⟨x, η⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹)).im =
      (N : ℝ)⁻¹ * ∑ k, η / ((freshEigenvalue H k - x) ^ 2 + η ^ 2) := by
  unfold BlockBand.External.CEH.normalizedTrace
  rw [trace_resolvent_spectral hH (z := ⟨x, η⟩) hη]
  have hN : ((N : ℂ)⁻¹) = (((N : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [hN, Complex.im_ofReal_mul, Complex.im_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  set y := freshEigenvalue H k
  have hd : ((y : ℂ) - ⟨x, η⟩) = ⟨y - x, -η⟩ := by apply Complex.ext <;> simp
  rw [hd, Complex.inv_im]
  simp only [Complex.normSq_mk]
  have : (y - x) * (y - x) + -η * -η = (y - x) ^ 2 + η ^ 2 := by ring
  rw [this, neg_neg]

/-- At `x = λ_i`: `Im ⟨(H - λ_i - iη)⁻¹⟩ = Σ_j kerAt λ η i j`. -/
theorem normalizedTrace_resolvent_im_kerAt {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    (i : Fin N) {η : ℝ} (hη : η ≠ 0) :
    (BlockBand.External.CEH.normalizedTrace
      ((H - (⟨freshEigenvalue H i, η⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹)).im =
      ∑ j, kerAt (fun k => freshEigenvalue H k) η i j := by
  rw [normalizedTrace_resolvent_im hH _ hη, Finset.mul_sum]
  rfl

end BlockBand.Palm.MomentFlow
