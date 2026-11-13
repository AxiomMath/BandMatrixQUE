module

public import BlockBand.SourceProcess.ModelExist.Rank

/-!
# A common perpendicular near direction of two frames

`exists_common_perp`: for frames `Y₁, Y₂` (rows `ι`) with `rank(P Y_j) ≥ rank P`, a projection
`P`, and finitely many vectors `u_f` with `#F + 2|ι| < 3 rank P`, there is `w ≠ 0` in
`range Y₁ ∩ range Y₂ ∩ range P` perpendicular to every `u_f`:
`dim(range Y₁ ∩ range Y₂ ∩ range P) ≥ 3 rank P − 2|ι| > #F`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CoupledFrames
open Matrix Finset Module

variable {ι c' F : Type*} [Fintype ι] [Fintype c'] [Fintype F]

theorem exists_common_perp {P : Matrix ι ι ℂ} (hPP : P * P = P) (Y₁ Y₂ : Matrix ι c' ℂ)
    (h₁ : P.rank ≤ (P * Y₁).rank) (h₂ : P.rank ≤ (P * Y₂).rank) (u : F → ι → ℂ)
    (hdim : Fintype.card F + 2 * Fintype.card ι < 3 * P.rank) :
    ∃ w : ι → ℂ, w ≠ 0 ∧ (∃ a₁, Y₁ *ᵥ a₁ = w) ∧ (∃ a₂, Y₂ *ᵥ a₂ = w) ∧ P *ᵥ w = w ∧
      ∀ f, star (u f) ⬝ᵥ w = 0 := by
  set U₁ := LinearMap.range Y₁.mulVecLin
  set U₂ := LinearMap.range Y₂.mulVecLin
  set N := LinearMap.range P.mulVecLin
  have hU₁ : P.rank ≤ finrank ℂ U₁ := h₁.trans (rank_mul_le_right P Y₁)
  have hU₂ : P.rank ≤ finrank ℂ U₂ := h₂.trans (rank_mul_le_right P Y₂)
  have hN : finrank ℂ N = P.rank := rfl
  have hle : ∀ V : Submodule ℂ (ι → ℂ), finrank ℂ V ≤ Fintype.card ι := fun V =>
    (Submodule.finrank_le _).trans (Module.finrank_fintype_fun_eq_card ℂ).le
  have hs1 := Submodule.finrank_sup_add_finrank_inf_eq U₁ U₂
  have hs2 := Submodule.finrank_sup_add_finrank_inf_eq (U₁ ⊓ U₂) N
  have hW : 3 * P.rank ≤ finrank ℂ ↥(U₁ ⊓ U₂ ⊓ N) + 2 * Fintype.card ι := by
    have := hle (U₁ ⊔ U₂)
    have := hle (U₁ ⊓ U₂ ⊔ N)
    omega
  let A : Matrix F ι ℂ := fun f => star (u f)
  let ψ := A.mulVecLin.domRestrict (U₁ ⊓ U₂ ⊓ N)
  have hrn := LinearMap.finrank_range_add_finrank_ker ψ
  have hrange : finrank ℂ (LinearMap.range ψ) ≤ Fintype.card F :=
    (Submodule.finrank_le _).trans (Module.finrank_fintype_fun_eq_card ℂ).le
  have hker : 0 < finrank ℂ (LinearMap.ker ψ) := by omega
  have hbot : LinearMap.ker ψ ≠ ⊥ := fun h => by
    rw [h, finrank_bot] at hker; exact lt_irrefl _ hker
  obtain ⟨⟨w, hw⟩, hψ, hne⟩ := (Submodule.ne_bot_iff _).1 hbot
  have hw0 : w ≠ 0 := fun h => hne (by ext; simp [h])
  obtain ⟨⟨⟨a₁, ha₁⟩, ⟨a₂, ha₂⟩⟩, ⟨z, hz⟩⟩ := hw
  have hAw : A *ᵥ w = 0 := LinearMap.mem_ker.1 hψ
  simp only [mulVecLin_apply] at ha₁ ha₂ hz
  refine ⟨w, hw0, ⟨a₁, ha₁⟩, ⟨a₂, ha₂⟩, ?_, fun f => ?_⟩
  · rw [← hz, mulVec_mulVec, hPP]
  · have := congrFun hAw f
    simpa [A, mulVec, dotProduct] using this

end BlockBand.SourceProcess.CoupledFrames
