module

public import BlockBand.Native.CEH.ETH.DeterministicLemma56

/-!
# CEH ETH: Lemma 5.6 bounds 1–4 for the MDE solutions of a Hermitian `F`

The bounds of CEH Lemma 5.6 in the diagonal model (`lemma56_window_bound`) transferred to the MDE
solutions of a Hermitian deformation `F`, by diagonalizing `F`, in the hybrid form and in CEH's
normalization.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.ETH

open Matrix
open CEHNative.BlockBand CEHNative.BlockBand.External.CEH
open scoped ComplexConjugate

variable {N : ℕ}

section Conj

variable (φ : Matrix (Fin N) (Fin N) ℂ ≃⋆ₐ[ℂ] Matrix (Fin N) (Fin N) ℂ)
  (hφ : ∀ X, NTrace (φ X) = NTrace X)
include hφ

theorem conj_twoResApprox (σ : ℝ) (X A Y : Matrix (Fin N) (Fin N) ℂ) :
    twoResApprox σ (φ X) (φ A) (φ Y) = φ (twoResApprox σ X A Y) := by
  unfold twoResApprox hybridDen
  simp only [← map_mul, hφ, map_add, map_smul]

theorem conj_hatApprox (σ : ℝ) (X A Y : Matrix (Fin N) (Fin N) ℂ) :
    hatApprox σ (φ X) (φ A) (φ Y) = φ (hatApprox σ X A Y) := by
  unfold hatApprox
  simp only [spectralConj_conjTranspose' φ, conj_twoResApprox φ hφ, map_add, map_sub, map_smul]

theorem conj_wardMass (X : Matrix (Fin N) (Fin N) ℂ) : wardMass (φ X) = wardMass X := by
  rw [wardMass, wardMass, spectralConj_conjTranspose' φ, ← map_mul, hφ]

theorem conj_chain (X A Y : Matrix (Fin N) (Fin N) ℂ) :
    NTrace (matrixImaginaryPart (φ X) * φ A * matrixImaginaryPart (φ Y) * (φ A)ᴴ) =
      NTrace (matrixImaginaryPart X * A * matrixImaginaryPart Y * Aᴴ) := by
  rw [spectralConj_matrixImaginaryPart φ, spectralConj_matrixImaginaryPart φ,
    spectralConj_conjTranspose' φ, ← map_mul, ← map_mul, ← map_mul, hφ]

end Conj

/-- **CEH Lemma 5.6 bounds 1–4, hybrid form, regular-window regime, Hermitian `F`.** -/
theorem lemma56_window_bound_hermitian (hN : 0 < N) {F : LocalETHMatrix N}
    (hF : F.IsHermitian) {s σ K κ B : ℝ} (hs : 0 < s) (hκ : 0 < κ) (hσ0 : 0 ≤ σ) (hσs : σ ≤ s)
    {z₁ z₂ : ℂ} (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im) {M₁ M₂ : LocalETHMatrix N}
    (h₁ : IsLocalETHMDESolution s F z₁ M₁) (h₂ : IsLocalETHMDESolution s F z₂ M₂)
    (A : LocalETHMatrix N) (hreg : NTrace (M₁ * A * M₂ᴴ) = 0)
    (hκ₁ : κ ≤ (NTrace M₁).im) (hκ₂ : κ ≤ (NTrace M₂).im)
    (hK₁ : (NTrace M₁).im ≤ K) (hK₂ : (NTrace M₂).im ≤ K)
    (hB : ‖(z₁ + (s : ℂ) * NTrace M₁) - conj (z₂ + (s : ℂ) * NTrace M₂)‖ ≤ B) :
    ‖NTrace (twoResApprox σ M₁ A M₂)‖ ≤ lemma56Const s K κ B *
        Real.sqrt (NTrace (matrixImaginaryPart M₁ * A * matrixImaginaryPart M₂ * Aᴴ)).re ∧
      ‖NTrace (twoResApprox σ M₁ᴴ A M₂ᴴ)‖ ≤ lemma56Const s K κ B *
        Real.sqrt (NTrace (matrixImaginaryPart M₁ * A * matrixImaginaryPart M₂ * Aᴴ)).re ∧
      NTrace (twoResApprox σ M₁ A M₂ᴴ) = 0 ∧
      ‖NTrace (twoResApprox σ M₁ᴴ A M₂)‖ ≤ lemma56Const s K κ B *
        Real.sqrt (NTrace (matrixImaginaryPart M₁ * A * matrixImaginaryPart M₂ * Aᴴ)).re ∧
      ‖NTrace (hatApprox σ M₁ A M₂)‖ ≤ lemma56Const s K κ B *
        Real.sqrt (NTrace (matrixImaginaryPart M₁ * A * matrixImaginaryPart M₂ * Aᴴ)).re := by
  set φ := Unitary.conjStarAlgAut ℂ (Matrix (Fin N) (Fin N) ℂ) hF.eigenvectorUnitary with hφdef
  have hφ : ∀ X, NTrace (φ X) = NTrace X := spectralConj_NTrace _
  set f := CEHNative.BlockBand.CEH.hermitianSpectrum hF
  set ζ₁ := z₁ + (s : ℂ) * NTrace M₁ with hζ₁
  set ζ₂ := z₂ + (s : ℂ) * NTrace M₂ with hζ₂
  have hM₁ : M₁ = φ (dg f ζ₁) := by
    have := CEHNative.BlockBand.CEH.eq_spectralLift_entry_of_isSolution hF hN hs hz₁.ne' h₁
    rw [entry_eq_resEntry] at this
    exact this
  have hM₂ : M₂ = φ (dg f ζ₂) := by
    have := CEHNative.BlockBand.CEH.eq_spectralLift_entry_of_isSolution hF hN hs hz₂.ne' h₂
    rw [entry_eq_resEntry] at this
    exact this
  have ht₁ : NTrace (dg f ζ₁) = NTrace M₁ := by rw [hM₁, hφ]
  have ht₂ : NTrace (dg f ζ₂) = NTrace M₂ := by rw [hM₂, hφ]
  have hΘ₁ : 0 < ζ₁.im := by
    rw [hζ₁, Complex.add_im, Complex.im_ofReal_mul]; nlinarith
  have hΘ₂ : 0 < ζ₂.im := by
    rw [hζ₂, Complex.add_im, Complex.im_ofReal_mul]; nlinarith
  
  have hm₁ : BlockBand.Internal.Contracts.Inputs.IsManuscriptMDE s ⟨F, hF⟩ z₁ M₁ :=
    ⟨h₁.inv, h₁.pos⟩
  have hm₂ : BlockBand.Internal.Contracts.Inputs.IsManuscriptMDE s ⟨F, hF⟩ z₂ M₂ :=
    ⟨h₂.inv, h₂.pos⟩
  have ha₁ : s * wardMass (dg f ζ₁) < 1 := by
    have := mul_wardMass_mde_lt_one hm₁ hz₁.ne' hs.le
    rwa [hM₁, conj_wardMass φ hφ] at this
  have ha₂ : s * wardMass (dg f ζ₂) < 1 := by
    have := mul_wardMass_mde_lt_one hm₂ hz₂.ne' hs.le
    rwa [hM₂, conj_wardMass φ hφ] at this
  set A' := φ.symm A with hA'
  have hA : A = φ A' := (φ.apply_symm_apply A).symm
  have hreg' : NTrace (dg f ζ₁ * A' * (dg f ζ₂)ᴴ) = 0 := by
    rw [hM₁, hM₂, hA, spectralConj_conjTranspose' φ, ← map_mul, ← map_mul, hφ] at hreg
    exact hreg
  have hκ₁' : κ ≤ (NTrace (dg f ζ₁)).im := by rw [ht₁]; exact hκ₁
  have hκ₂' : κ ≤ (NTrace (dg f ζ₂)).im := by rw [ht₂]; exact hκ₂
  have hK₁' : (NTrace (dg f ζ₁)).im ≤ K := by rw [ht₁]; exact hK₁
  have hK₂' : (NTrace (dg f ζ₂)).im ≤ K := by rw [ht₂]; exact hK₂
  have key := lemma56_window_bound (K := K) (B := B) f A' hN hs hκ hΘ₁ hΘ₂ hreg' hσ0 hσs
    ha₁ ha₂ hκ₁' hκ₂' hK₁' hK₂' hB
  have hP : (NTrace (matrixImaginaryPart M₁ * A * matrixImaginaryPart M₂ * Aᴴ)).re =
      chainP f ζ₁ ζ₂ A' := by
    rw [hM₁, hM₂, hA, conj_chain φ hφ]
  rw [hP]
  obtain ⟨k1, k2, k3, k4, k5⟩ := key
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hM₁, hM₂, hA, conj_twoResApprox φ hφ, hφ]; exact k1
  · rw [hM₁, hM₂, hA, spectralConj_conjTranspose' φ, spectralConj_conjTranspose' φ,
      conj_twoResApprox φ hφ, hφ]; exact k2
  · rw [hM₁, hM₂, hA, spectralConj_conjTranspose' φ, conj_twoResApprox φ hφ, hφ]; exact k3
  · rw [hM₁, hM₂, hA, spectralConj_conjTranspose' φ, conj_twoResApprox φ hφ, hφ]; exact k4
  · rw [hM₁, hM₂, hA, conj_hatApprox φ hφ, hφ]; exact k5

/-- **Corollary in CEH's normalization**: under the hypotheses of
`lemma56_window_bound_hermitian`, for every `σ ∈ [0, s]` and with `ρᵢ = cehDensityOf Mᵢ`,
`|⟨M^A_σ(z₁⁺,z₂⁺)⟩| ≤ π C √(ρ₁ρ₂) s₂(σ)` (and likewise in the other constellations and for
`M̂_σ`, by the same composition with `sqrt_chain_le`). -/
theorem lemma56_pp_le_sTwoAt (hN : 0 < N) {F : LocalETHMatrix N}
    (hF : F.IsHermitian) {s σ K κ B : ℝ} (hs : 0 < s) (hκ : 0 < κ) (hσ0 : 0 ≤ σ) (hσs : σ ≤ s)
    {z₁ z₂ : ℂ} (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im) {M₁ M₂ : LocalETHMatrix N}
    (h₁ : IsLocalETHMDESolution s F z₁ M₁) (h₂ : IsLocalETHMDESolution s F z₂ M₂)
    (A : LocalETHMatrix N) (hreg : NTrace (M₁ * A * M₂ᴴ) = 0)
    (hκ₁ : κ ≤ (NTrace M₁).im) (hκ₂ : κ ≤ (NTrace M₂).im)
    (hK₁ : (NTrace M₁).im ≤ K) (hK₂ : (NTrace M₂).im ≤ K)
    (hB : ‖(z₁ + (s : ℂ) * NTrace M₁) - conj (z₂ + (s : ℂ) * NTrace M₂)‖ ≤ B) :
    ‖NTrace (twoResApprox σ M₁ A M₂)‖ ≤ lemma56Const s K κ B *
        (Real.pi * Real.sqrt (cehDensityOf M₁ * cehDensityOf M₂) * sTwoAt σ M₁ M₂ A) := by
  have h := (lemma56_window_bound_hermitian hN hF hs hκ hσ0 hσs hz₁ hz₂ h₁ h₂ A hreg hκ₁ hκ₂
    hK₁ hK₂ hB).1
  have hC : 0 ≤ lemma56Const s K κ B := by
    rw [lemma56Const]
    have hB0 : 0 ≤ B := (norm_nonneg _).trans hB
    have : 0 ≤ s * κ ^ 2 := by positivity
    positivity
  exact h.trans (mul_le_mul_of_nonneg_left
    (sqrt_chain_le M₁ M₂ A (hκ.trans_le hκ₁) (hκ.trans_le hκ₂) hσ0) hC)

/-- **The `θ = 1` bound on `|ζ₁ - ζ̄₂|`** (input `B` of `lemma56_window_bound_hermitian`):
`(ζ₁ - ζ̄₂)⟨M₁M₂ᴴ⟩ = m₁ - m̄₂` and `θ = 1` (`s Re⟨M₁M₂ᴴ⟩ ≥ ½`) give
`|ζ₁ - ζ̄₂| ≤ 2s |m₁ - m̄₂|` (`≤ 4sK` when `|mᵢ| ≤ K`). -/
theorem norm_zeta_sub_conj_le_of_theta (hN : 0 < N) {F : LocalETHMatrix N}
    (hF : F.IsHermitian) {s : ℝ} (hs : 0 < s) {z₁ z₂ : ℂ} (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im)
    {M₁ M₂ : LocalETHMatrix N}
    (h₁ : IsLocalETHMDESolution s F z₁ M₁) (h₂ : IsLocalETHMDESolution s F z₂ M₂)
    (hθ : regularizationCoefficient (Real.sqrt s : ℂ) M₁ M₂ᴴ = 1) :
    ‖(z₁ + (s : ℂ) * NTrace M₁) - conj (z₂ + (s : ℂ) * NTrace M₂)‖ ≤
      2 * s * ‖NTrace M₁ - conj (NTrace M₂)‖ := by
  set φ := Unitary.conjStarAlgAut ℂ (Matrix (Fin N) (Fin N) ℂ) hF.eigenvectorUnitary with hφdef
  have hφ : ∀ X, NTrace (φ X) = NTrace X := spectralConj_NTrace _
  set f := CEHNative.BlockBand.CEH.hermitianSpectrum hF
  set ζ₁ := z₁ + (s : ℂ) * NTrace M₁ with hζ₁
  set ζ₂ := z₂ + (s : ℂ) * NTrace M₂ with hζ₂
  have hM₁ : M₁ = φ (dg f ζ₁) := by
    have := CEHNative.BlockBand.CEH.eq_spectralLift_entry_of_isSolution hF hN hs hz₁.ne' h₁
    rw [entry_eq_resEntry] at this
    exact this
  have hM₂ : M₂ = φ (dg f ζ₂) := by
    have := CEHNative.BlockBand.CEH.eq_spectralLift_entry_of_isSolution hF hN hs hz₂.ne' h₂
    rw [entry_eq_resEntry] at this
    exact this
  -- `θ = 1` gives `|⟨M₁M₂ᴴ⟩| ≥ 1/(2s)`
  have harg : 0 ≤ ((Real.sqrt s : ℂ) ^ 2 * NTrace (M₁ * M₂ᴴ)).re - 1 / 2 := by
    by_contra hneg
    unfold regularizationCoefficient at hθ
    rw [cehTheta_of_neg (not_le.mp hneg)] at hθ
    norm_num at hθ
  rw [← Complex.ofReal_pow, Real.sq_sqrt hs.le, Complex.re_ofReal_mul] at harg
  have hden : 1 / (2 * s) ≤ ‖NTrace (M₁ * M₂ᴴ)‖ := by
    have := Complex.re_le_norm (NTrace (M₁ * M₂ᴴ))
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hcpos : 0 < ‖NTrace (M₁ * M₂ᴴ)‖ := lt_of_lt_of_le (by positivity) hden
  -- the pair identity
  have hΘ₁ : ζ₁.im ≠ 0 := by
    have := Phase1.mde_im_mul_im_spectral_pos (s := s) (F := ⟨F, hF⟩) ⟨h₁.inv, h₁.pos⟩
      hz₁.ne' hs.le
    change 0 < z₁.im * ζ₁.im at this
    intro h0; rw [h0, mul_zero] at this; exact lt_irrefl _ this
  have hΘ₂ : (conj ζ₂).im ≠ 0 := by
    have := Phase1.mde_im_mul_im_spectral_pos (s := s) (F := ⟨F, hF⟩) ⟨h₂.inv, h₂.pos⟩
      hz₂.ne' hs.le
    change 0 < z₂.im * ζ₂.im at this
    rw [Complex.conj_im]
    intro h0; rw [neg_eq_zero.1 h0, mul_zero] at this
    exact lt_irrefl _ this
  have hpair := pair_identity f hΘ₁ hΘ₂
  rw [NTrace_dg_conj, ← dg_conjTranspose] at hpair
  have hc : NTrace (dg f ζ₁ * (dg f ζ₂)ᴴ) = NTrace (M₁ * M₂ᴴ) := by
    rw [hM₁, hM₂, spectralConj_conjTranspose' φ, ← map_mul, hφ]
  have hm₁ : NTrace (dg f ζ₁) = NTrace M₁ := by rw [hM₁, hφ]
  have hm₂ : NTrace (dg f ζ₂) = NTrace M₂ := by rw [hM₂, hφ]
  rw [hc, hm₁, hm₂] at hpair
  have hn := congrArg norm hpair
  rw [norm_mul] at hn
  rw [← hn]
  calc ‖ζ₁ - conj ζ₂‖ = ‖ζ₁ - conj ζ₂‖ * 1 := (mul_one _).symm
    _ ≤ ‖ζ₁ - conj ζ₂‖ * (2 * s * ‖NTrace (M₁ * M₂ᴴ)‖) := by
        gcongr
        rw [div_le_iff₀ (by positivity)] at hden
        linarith
    _ = 2 * s * (‖ζ₁ - conj ζ₂‖ * ‖NTrace (M₁ * M₂ᴴ)‖) := by ring

end BlockBand.Native.CEH.ETH
