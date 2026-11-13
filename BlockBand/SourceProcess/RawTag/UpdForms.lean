module

public import BlockBand.SourceProcess.RawTag.UpdGrown

/-!
# The raw forms of the grown path

Dot-product identities for reindexed and block vectors, and the embedding of a unit tag of the
path of length `l` into the grown path of length `l + 1` (`unitTag_comp_old` for old tags,
`unitTag_comp_new` for the newborn one).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.RawTag

open Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.Bridge BlockBand.Transmission.PassiveLayer
open scoped Matrix ComplexOrder

variable {W : ℕ}

theorem dot_reindex {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) (u v : β → ℂ)
    (M : Matrix β β ℂ) :
    star u ⬝ᵥ (M *ᵥ v) = star (u ∘ e) ⬝ᵥ (M.submatrix e e *ᵥ (v ∘ e)) := by
  simp only [dotProduct, mulVec, Pi.star_apply, Function.comp, submatrix_apply]
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  rw [← e.sum_comp]

theorem star_sumElim {α β : Type*} (a : α → ℂ) (c : β → ℂ) :
    star (Sum.elim a c) = Sum.elim (star a) (star c) := by
  funext x; cases x <;> rfl

theorem dot_fromBlocks {α β : Type*} [Fintype α] [Fintype β] (a : α → ℂ) (c : β → ℂ)
    (a' : α → ℂ) (c' : β → ℂ) (A : Matrix α α ℂ) (B : Matrix α β ℂ) (C : Matrix β α ℂ)
    (D : Matrix β β ℂ) :
    star (Sum.elim a c) ⬝ᵥ (fromBlocks A B C D *ᵥ Sum.elim a' c') =
      star a ⬝ᵥ (A *ᵥ a' + B *ᵥ c') + star c ⬝ᵥ (C *ᵥ a' + D *ᵥ c') := by
  rw [fromBlocks_mulVec, star_sumElim, sumElim_dotProduct_sumElim]
  rfl

theorem dot_sandwich {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (u : α → ℂ) (A : Matrix α β ℂ) (M : Matrix β γ ℂ) (B : Matrix γ δ ℂ) (v : δ → ℂ) :
    star u ⬝ᵥ ((A * M * B) *ᵥ v) = star (Aᴴ *ᵥ u) ⬝ᵥ (M *ᵥ (B *ᵥ v)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec, conjTranspose_conjTranspose]

theorem unitTag_comp_old {l β : ℕ} (hβ : β < l) (g : Fin W → ℂ) :
    unitTag W (l + 1) β g ∘ headEquiv l W = Sum.elim (0 : Fin W → ℂ) (unitTag W l β g) := by
  funext x
  rcases x with x | ⟨i, x⟩
  · simp only [Function.comp_apply, Sum.elim_inl, Pi.zero_apply]
    simp [unitTag, headEquiv_inl]
    omega
  · simp only [Function.comp, headEquiv_inr, unitTag, Sum.elim_inr, Fin.val_succ]
    have : (i.val + 1 = l + 1 - 1 - β ∧ β < l + 1) ↔ (i.val = l - 1 - β ∧ β < l) := by omega
    simp only [this]

theorem unitTag_comp_new {l : ℕ} (g : Fin W → ℂ) :
    unitTag W (l + 1) l g ∘ headEquiv l W = Sum.elim (unitVec W g) (0 : Fin l × Fin W → ℂ) := by
  funext x
  rcases x with x | ⟨i, x⟩
  · simp [Function.comp, headEquiv_inl, unitTag, unitVec]
  · simp only [Function.comp_apply, Sum.elim_inr, Pi.zero_apply]
    simp [unitTag, headEquiv_inr]

end BlockBand.SourceProcess.RawTag
