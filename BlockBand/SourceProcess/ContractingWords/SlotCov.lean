module

public import BlockBand.SourceProcess.ContractingWords.SlotCovZ

/-!
# The covariance of two ordinary slots at one fresh layer

Measure `freshLaw W b`; deterministic Hermitian `𝕏`; separators `σ, σ' ∈ {I, P}`, `B_σ = sepOf 𝕏 σ`,
unit vectors. `slot_cov hGA hLp hP hΓ`: `C, W₀` from `b, κ`;

`|E[(u*(Nσ N* - B_σ)v)(u'*(Nσ'N* - B_σ')v')] - (u*m_σ v)(u'*m_σ' v') - Σ_k κ_k ct(u,v,u',v',
B_σ G_k B_σ', B_σ' H_k B_σ)| ≤ C(1+g)²(W^{-3/2} + e²)`,
`(κ_k, G_k, H_k)` the four tensors of the full-source covariance. Proof:
`NPN*⁰ = P(NN*)⁰P - projGamma⁰` (`centered_proj`),
`fullSourceCovarianceEnergyUniform_holds` for `(B_σu, B_σv, B_σ'u', B_σ'v')`, and the
`projGamma⁰` terms by `E|fg| ≤ (aE|f|² + a⁻¹E|g|²)/2` with `a = √W^{±1}` and the `L²` bound of
`projGamma`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.CompleteSourceGap
open BlockBand.Internal.Contracts.Inputs BlockBand.Internal.Contracts.TransmissionUniform2
open BlockBand.Transmission.PassiveCovariance
open scoped ENNReal Matrix.Norms.L2Operator

variable {W : ℕ}

/-- The non-ward part `zc σ u v - zc I (B_σu) (B_σv)` of a slot. -/
def zr (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (σ : Separator)
    (u v : Fin 2 × Fin W → ℂ) (y : LayerSample W .oneBlockOnePort) : ℂ :=
  zc b E XX σ u v y - zc b E XX .id (sepOf b E XX σ *ᵥ u) (sepOf b E XX σ *ᵥ v) y

theorem zr_cases {b E : ℝ} {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hI : ∀ i j, Integrable (fun y => transportedSep b E XX .id y i j) (freshLaw W b))
    (hP : ∀ i j, Integrable (fun y => transportedSep b E XX .proj y i j) (freshLaw W b))
    {σ : Separator} (hσ : σ.unconj + σ.conj = 0) (u v : Fin 2 × Fin W → ℂ) :
    (∀ y, zr b E XX σ u v y = 0) ∨ (∀ y, zr b E XX σ u v y = -bilinear u (projGamma b E XX y -
      matrixExpect (freshLaw W b) (projGamma b E XX)) v) := by
  cases σ <;> simp [Separator.unconj, Separator.conj] at hσ
  · left; intro y; simp [zr, sepOf]
  · right; intro y
    have h := centered_proj (matrixExpect_projGamma hI hP) u v y
    simp only [zr, zc, sepOf]
    rw [h]; ring

theorem sepOf_ord_herm {b E : ℝ} {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {σ : Separator}
    (hσ : σ.unconj + σ.conj = 0) : (sepOf b E XX σ)ᴴ = sepOf b E XX σ ∧ ‖sepOf b E XX σ‖ ≤ 1 := by
  cases σ <;> simp [Separator.unconj, Separator.conj] at hσ
  · exact ⟨by simp [sepOf], by simpa [sepOf] using norm_one_matrix_le⟩
  · exact ⟨BlockBand.Transmission.Bridge.nearProjection_conjTranspose, norm_nearProjection_le⟩

end BlockBand.SourceProcess.ContractingWords
