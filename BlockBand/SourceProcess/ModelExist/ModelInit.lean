module

public import BlockBand.SourceProcess.ModelExist.ModelCases3

/-!
# The born Gram process starts at the canonical Gram state

`bornG_zero`: if `𝒢₀ = gramPair P (extFrame t h)`, the selection specification holds and every
probe born at time `0` has `v_i = 0`, then `G₀ = initialGram K π t h`: the current block of the
extended frame is the canonical frame, and a probe column born at `0` with `v_i = 0` has
`M a = 0`, so it contributes nothing.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ModelExist
open MeasureTheory Set Matrix Finset
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.SourceProcess.BornUnique
open scoped NNReal ComplexConjugate

theorem ext_of_entries {c : Type*} {A B : Matrix c c ℂ × Matrix c c ℂ}
    (h : ∀ e : Fin 2 × c × c, gramEntry e A = gramEntry e B) : A = B := by
  ext i j
  · simpa [gramEntry] using h (0, i, j)
  · simpa [gramEntry] using h (1, i, j)

variable {K R : ℕ} {π : Type*} [Fintype π] [DecidableEq π]

omit [Fintype π] [DecidableEq π] in
theorem extFrame_cur_entry (t : ℕ → ℝ) (h : ℝ) (r : Fin 2) (k k' : Fin K × Fin 2) :
    gr r (gramPair (ambP K R) (extFrame K R t h)) (Sum.inl k) (Sum.inl k') =
      gramEntry (r, Sum.inl k, Sum.inl k') (initialGram K π t h) := by
  have hamb : ∀ x x' : Fin K × Fin 2, ambP K R (Sum.inl x) (Sum.inl x') = modeProjection K x x' := by
    intro x x'
    simp only [ambP, modeProjection, diagonal_apply, Sum.inl.injEq]
  simp only [gr, gramEntry, initialGram, gramPair, sourceGram, nearGram]
  split_ifs
  · simp only [Matrix.mul_apply, conjTranspose_apply, Fintype.sum_sum_type, extFrame,
      star_zero, zero_mul, Finset.sum_const_zero, add_zero]
    rfl
  · simp only [Matrix.mul_apply, conjTranspose_apply, Fintype.sum_sum_type, extFrame,
      star_zero, zero_mul, mul_zero, Finset.sum_const_zero, add_zero, hamb]
    rfl

variable {n : ℕ} {eπ : π ≃ Fin n} {Ω : Type*}
  {sel : (Matrix (ExtCol K R) (ExtCol K R) ℂ × Matrix (ExtCol K R) (ExtCol K R) ℂ) ×
    (Fin n → ExtCol K R → ℂ) × ℝ → ExtCol K R → ℂ}
  {𝒢 : ℝ≥0 → Ω → Matrix (ExtCol K R) (ExtCol K R) ℂ × Matrix (ExtCol K R) (ExtCol K R) ℂ}
  {σ : π → Ω → ℝ} {v : π → ℝ} {ω : Ω}

theorem bornG_zero {t : ℕ → ℝ} {h : ℝ} (h0 : 𝒢 0 ω = gramPair (ambP K R) (extFrame K R t h))
    (hs : AllSpec K R eπ sel 𝒢 σ v ω)
    (hherm : ∀ t, (𝒢 t ω).1ᴴ = (𝒢 t ω).1 ∧ (𝒢 t ω).2ᴴ = (𝒢 t ω).2)
    (hv0 : ∀ i, (σ i ω).toNNReal = 0 → v i = 0) :
    bornG 𝒢 (mθ K σ) (mlam K R eπ sel 𝒢 σ v) 0 ω = initialGram K π t h := by
  refine ext_of_entries fun e => ?_
  have h1 := entry_sub_rep (𝒢 := 𝒢) (θ := mθ K σ) (lam := mlam K R eπ sel 𝒢 σ v) e 0 ω
  have hz : ∀ r : WithTop ℝ≥0, stopTime r 0 = 0 := fun r => le_antisymm (stopTime_le _ 0) zero_le
  simp only [hz, sub_self, mul_zero, Finset.sum_const_zero, sub_zero] at h1
  rw [h1]
  obtain ⟨r, y, y'⟩ := e
  rcases y with k | i <;> rcases y' with k' | j
  · have hb : bTime (mθ K σ) (r, Sum.inl k, Sum.inl k') ω ≤ ((0 : ℝ≥0) : WithTop ℝ≥0) := by
      simp [bTime, mθ]
    rw [ite_eq_left hb, bVal_eq]
    simp only [mθ, max_self, mlam_inl, single_dot, h0]
    simp only [mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    exact extFrame_cur_entry t h r k k'
  · rw [bVal_probe_cur hs]
    simp [initialGram, gramPair, gramEntry, sourceGram, nearGram, Matrix.mul_apply, initialFrame]
  · rw [bVal_cur_probe hs hherm]
    simp [initialGram, gramPair, gramEntry, sourceGram, nearGram, Matrix.mul_apply, initialFrame]
  · by_cases hij : i = j
    · subst hij
      rw [bVal_probe_self hs]
      split_ifs with hb
      · simp only [bTime, mθ, max_self] at hb
        rw [WithTop.coe_le_coe] at hb
        have : (σ i ω).toNNReal = 0 := le_antisymm hb zero_le
        simp [hv0 i this, initialGram, gramPair, gramEntry, sourceGram, nearGram,
          Matrix.mul_apply, initialFrame]
      · simp [initialGram, gramPair, gramEntry, sourceGram, nearGram, Matrix.mul_apply,
          initialFrame]
    · rw [bVal_probe_probe hs hherm r hij]
      simp [initialGram, gramPair, gramEntry, sourceGram, nearGram, Matrix.mul_apply, initialFrame]

end BlockBand.SourceProcess.ModelExist
