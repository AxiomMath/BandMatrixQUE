module

public import BlockBand.SourceProcess.ContractingWords.WordExpArith

/-!
# The slot covariance in increment form

`slot_cov_delta`: for ordinary separators `σ, σ'` (`I` or `P`) at a Hermitian old two-port, the
covariance of the bilinears `u*(T_σ - sepOf σ)v` and `u'*(T_{σ'} - sepOf σ')v'` of the transported
separators, minus the product of their means, equals the sum of the four full-source covariance
tensors up to `C(1 + g)²(W^{-3/2} + e²)`, uniformly on the bulk.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.CompleteSourceGap
open BlockBand.Internal.Contracts.Inputs BlockBand.Transmission.PassiveCovariance
open scoped ENNReal Matrix.Norms.L2Operator

variable {W : ℕ}

theorem slot_cov_delta (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) (hΓ : ProjGammaFluct) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {κ : ℝ}
    (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ s : ℂ,
      IsStationaryJet b E s → ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
      ∀ σ σ' : Separator, σ.unconj + σ.conj = 0 → σ'.unconj + σ'.conj = 0 →
      ∀ u v u' v' : Fin 2 × Fin W → ℂ, vecNorm u ≤ 1 → vecNorm v ≤ 1 → vecNorm u' ≤ 1 →
        vecNorm v' ≤ 1 →
        ‖∫ y, bilinear u (transportedSep b E XX σ y - sepOf b E XX σ) v *
              bilinear u' (transportedSep b E XX σ' y - sepOf b E XX σ') v' ∂freshLaw W b -
            bilinear u (matrixExpect (freshLaw W b) (transportedSep b E XX σ) - sepOf b E XX σ) v *
              bilinear u' (matrixExpect (freshLaw W b) (transportedSep b E XX σ') -
                sepOf b E XX σ') v' -
            ∑ k, fscK b E s W k * crossedTensor u v u' v'
              (sepOf b E XX σ * fscG b E XX k * sepOf b E XX σ')
              (sepOf b E XX σ' * fscH b E XX k * sepOf b E XX σ)‖ ≤
          C * (1 + conductanceOf (passiveTransmission b E (nearSchur (boundaryZ b E) XX))) ^ 2 *
            ((W : ℝ)⁻¹ / Real.sqrt W + layerErr b E s XX ^ 2) := by
  obtain ⟨C, W₁, hC, hcov⟩ := slot_cov hGA hLp hP hΓ hb0 hb hκ
  obtain ⟨C₂, W₂, hC₂, hf⟩ := sepFluctIdProj_holds hGA hLp b hb0 hb κ hκ 2 (by norm_num)
  obtain ⟨μb, W₃, -, hfb⟩ := fresh_basic hGA hb0 hb hκ
  refine ⟨C, max (max W₁ W₂) W₃, hC, ?_⟩
  intro W hW E hE s hs XX hXX σ σ' hσ hσ' u v u' v' hu hv hu' hv'
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW1, hW2⟩, hW3⟩ := hW
  have hT := fun τ => (hfb W hW3 E hE XX hXX τ).1
  have hfac : ∀ τ : Separator, τ.unconj + τ.conj = 0 → ∀ x z : Fin 2 × Fin W → ℂ,
      Integrable (zc b E XX τ x z) (freshLaw W b) ∧ ∫ y, zc b E XX τ x z y ∂freshLaw W b = 0 ∧
        AEStronglyMeasurable (zc b E XX τ x z) (freshLaw W b) ∧
        Integrable (fun y => ‖zc b E XX τ x z y‖ ^ 2) (freshLaw W b) := fun τ hτ x z => by
    have hβ : 0 ≤ C₂ * (1 / Real.sqrt W + min 1 (jetDistance0 b E (nearSchur (boundaryZ b E) XX))) *
        vecNorm x * vecNorm z := by
      have := vecNorm_nonneg x; have := vecNorm_nonneg z
      have : 0 ≤ min 1 (jetDistance0 b E (nearSchur (boundaryZ b E) XX)) :=
        le_min zero_le_one (norm_nonneg _)
      positivity
    obtain ⟨m, i, h0, i2, -⟩ := zc_facts (hT τ) x z hβ (hf W hW2 E hE XX hXX τ hτ x z)
    exact ⟨i, h0, m, i2⟩
  obtain ⟨i1, z1, m1, s1⟩ := hfac σ hσ u v
  obtain ⟨i2, z2, m2, s2⟩ := hfac σ' hσ' u' v'
  have hsplit : ∀ (τ : Separator) (x z : Fin 2 × Fin W → ℂ) y,
      bilinear x (transportedSep b E XX τ y - sepOf b E XX τ) z =
        bilinear x (matrixExpect (freshLaw W b) (transportedSep b E XX τ) - sepOf b E XX τ) z +
          zc b E XX τ x z y := fun τ x z y => by
    rw [zc, ← bilinear_add_mat]; congr 1; abel
  simp only [hsplit σ u v, hsplit σ' u' v']
  rw [int_center_mul i1 i2 (integrable_mul_of_sq m1 m2 s1 s2) z1 z2]
  exact hcov W hW1 E hE s hs XX hXX σ σ' hσ hσ' u v u' v' hu hv hu' hv'

end BlockBand.SourceProcess.ContractingWords
