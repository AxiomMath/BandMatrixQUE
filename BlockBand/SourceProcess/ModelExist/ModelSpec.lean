module

public import BlockBand.SourceProcess.ModelExist.ModelInit
public import BlockBand.SourceProcess.ModelExist.AmbientRank

/-!
# The selection specification holds at every sorted birth, almost surely

For the Gram process `𝒢_t = gramPair P X_t` of an ambient frame: `M ⪰ 0`, `M − B ⪰ 0`, both
Hermitian (`psd_gramPair`, `herm_gramPair`). Where `rank(P X_t) ≥ rank P` at every time and
`R > 2K + n`, `SelExists` holds at every time for every earlier family (`selExists_of_rank`), so
a selection meeting `SelSpec` wherever `SelExists` holds meets it at every sorted birth
(`allSpec_of_rank`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ModelExist
open MeasureTheory Set Matrix Finset
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.Internal.Contracts.TransmissionLaws
open scoped NNReal ComplexOrder

variable {ι c : Type*} [Fintype ι] [Fintype c]

omit [Fintype c] in
theorem herm_gramPair {P : Matrix ι ι ℂ} (hPh : Pᴴ = P) (V : Matrix ι c ℂ) :
    (gramPair P V).1ᴴ = (gramPair P V).1 ∧ (gramPair P V).2ᴴ = (gramPair P V).2 := by
  simp only [gramPair, sourceGram, nearGram, conjTranspose_mul, conjTranspose_conjTranspose, hPh,
    Matrix.mul_assoc, and_self]

theorem psd_gramPair [DecidableEq ι] {P : Matrix ι ι ℂ} (hPh : Pᴴ = P) (hPP : P * P = P)
    (V : Matrix ι c ℂ) :
    (gramPair P V).1.PosSemidef ∧ ((gramPair P V).1 - (gramPair P V).2).PosSemidef := by
  refine ⟨posSemidef_conjTranspose_mul_self V, ?_⟩
  have e : (gramPair P V).1 - (gramPair P V).2 = ((1 - P) * V)ᴴ * ((1 - P) * V) := by
    simp only [gramPair, sourceGram, nearGram, conjTranspose_mul, conjTranspose_sub,
      conjTranspose_one, hPh]
    have hq : (1 - P) * (1 - P) = 1 - P := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
        Matrix.one_mul, hPP, sub_self, sub_zero]
    rw [show Vᴴ * (1 - P) * ((1 - P) * V) = Vᴴ * ((1 - P) * (1 - P)) * V by
      simp only [Matrix.mul_assoc], hq, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.mul_assoc]
  rw [e]
  exact posSemidef_conjTranspose_mul_self _

theorem card_isCur (K R : ℕ) : (univ.filter (isCur K R)).card = 2 * K := by
  rw [Finset.card_filter, Fintype.sum_sum_type]
  simp [isCur, mul_comm]

variable {K R : ℕ} {π : Type*} [Fintype π] [DecidableEq π] {n : ℕ} {eπ : π ≃ Fin n} {Ω : Type*}

omit [Fintype π] [DecidableEq π] in
/-- **The specification at every sorted birth.** -/
theorem allSpec_of_rank
    {sel : (Matrix (ExtCol K R) (ExtCol K R) ℂ × Matrix (ExtCol K R) (ExtCol K R) ℂ) ×
      (Fin n → ExtCol K R → ℂ) × ℝ → ExtCol K R → ℂ}
    (hsel : ∀ (H : Matrix (ExtCol K R) (ExtCol K R) ℂ × Matrix (ExtCol K R) (ExtCol K R) ℂ)
      (prev : Fin n → ExtCol K R → ℂ) (v : ℝ), 0 ≤ v → H.1.PosSemidef →
        (H.1 - H.2).PosSemidef → SelExists (isCur K R) H prev →
          SelSpec (isCur K R) H prev v (sel (H, prev, v)))
    {X : ℝ≥0 → Ω → Matrix (Amb K R) (ExtCol K R) ℂ} {σ : π → Ω → ℝ} {v : π → ℝ}
    (hv : ∀ i, 0 ≤ v i) (hRn : 2 * K + n < R) {ω : Ω}
    (hrank : ∀ t, (ambP K R).rank ≤ (ambP K R * X t ω).rank) :
    AllSpec K R eπ sel (fun t ω => gramPair (ambP K R) (X t ω)) σ v ω := by
  intro l
  have hPh := (isNearProjection_ambP K R).1
  have hPP := (isNearProjection_ambP K R).2.1
  obtain ⟨h1, h2⟩ := psd_gramPair hPh hPP (X (sT (mθf eπ σ) l ω) ω)
  rw [bV_eq]
  refine hsel _ _ _ (hv _) h1 h2 (selExists_of_rank hPP _ (isCur K R) _ ?_ (hrank _))
  rw [card_isCur, rank_ambP]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  omega

end BlockBand.SourceProcess.ModelExist
