module

public import BlockBand.SourceProcess.ModelExist.ModelCases

/-!
# The birth values of the finite source model: the case analysis

If the selection meets its specification at every sorted birth (`AllSpec`), each probe vector
satisfies the selection specification (`probe_spec`) and is orthogonal, in the Gram form at the
later birth, to every probe born before it (`probe_perp`); the entries of the birth jumps are then
computed case by case.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ModelExist
open MeasureTheory Set Matrix Finset
open BlockBand.SourceProcess.Stochastic BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.BornUnique
open scoped NNReal ComplexConjugate

variable (K R : ℕ) {π : Type*} [Fintype π] [DecidableEq π] {n : ℕ} (eπ : π ≃ Fin n) {Ω : Type*}
  (sel : (Matrix (ExtCol K R) (ExtCol K R) ℂ × Matrix (ExtCol K R) (ExtCol K R) ℂ) ×
    (Fin n → ExtCol K R → ℂ) × ℝ → ExtCol K R → ℂ)
  (𝒢 : ℝ≥0 → Ω → Matrix (ExtCol K R) (ExtCol K R) ℂ × Matrix (ExtCol K R) (ExtCol K R) ℂ)
  (σ : π → Ω → ℝ) (v : π → ℝ) (ω : Ω)

/-- The specification at every sorted birth. -/
def AllSpec : Prop :=
  ∀ l : Fin n, SelSpec (isCur K R) (𝒢 (sT (mθf eπ σ) l ω) ω)
    (stateV sel 𝒢 (mθf eπ σ) (mvf eπ v) l.val ω) (mvf eπ v (srt (mθf eπ σ) ω l))
    (bV sel 𝒢 (mθf eπ σ) (mvf eπ v) l ω)

variable {K R eπ sel 𝒢 σ v ω}

omit [Fintype π] [DecidableEq π] in
theorem probe_spec (h : AllSpec K R eπ sel 𝒢 σ v ω) (i : π) :
    SelSpec (isCur K R) (𝒢 (σ i ω).toNNReal ω)
      (stateV sel 𝒢 (mθf eπ σ) (mvf eπ v) ((srt (mθf eπ σ) ω).symm (eπ i)).val ω) (v i)
      (mlam K R eπ sel 𝒢 σ v (Sum.inr i) ω) := by
  have := h ((srt (mθf eπ σ) ω).symm (eπ i))
  rwa [mθf_sT, mvf_srt] at this

omit [Fintype π] [DecidableEq π] in
theorem probe_perp (h : AllSpec K R eπ sel 𝒢 σ v ω) {i j : π}
    (hlt : (srt (mθf eπ σ) ω).symm (eπ i) < (srt (mθf eπ σ) ω).symm (eπ j)) :
    (σ i ω).toNNReal ≤ (σ j ω).toNNReal ∧
      star (mlam K R eπ sel 𝒢 σ v (Sum.inr i) ω) ⬝ᵥ
        ((𝒢 (σ j ω).toNNReal ω).1 *ᵥ mlam K R eπ sel 𝒢 σ v (Sum.inr j) ω) = 0 := by
  refine ⟨?_, ?_⟩
  · have := sT_mono (mθf eπ σ) ω hlt.le
    simp only at this
    rwa [mθf_sT, mθf_sT] at this
  · have := (probe_spec h j).1.2.2 ((srt (mθf eπ σ) ω).symm (eπ i))
    rwa [stateV_apply_lt _ _ _ _ _ _ _ hlt] at this

theorem entry_bJ_probe (t : ℝ≥0) (r : Fin 2) (y y' : SrcCol K π) :
    gramEntry (r, y, y') (bJ (probeJump (K := K) v) σ t ω) =
      match y, y' with
      | Sum.inr i, Sum.inr i' => if i = i' then (if σ i ω ≤ t then (v i : ℂ) else 0) else 0
      | _, _ => 0 := by
  rw [bJ, gramEntry_birthSum]
  simp only [gramEntry_probeJump]
  rcases y with k | i <;> rcases y' with k' | i'
  · simp
  · simp
  · simp
  · by_cases hii : i = i'
    · subst hii
      rw [Finset.sum_eq_single i (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
      simp
    · simp only [hii, ↓reduceIte]
      refine Finset.sum_eq_zero fun x _ => ?_
      have : ¬ (i = x ∧ i' = x) := fun h => hii (h.1.trans h.2.symm)
      simp [this]

end BlockBand.SourceProcess.ModelExist
