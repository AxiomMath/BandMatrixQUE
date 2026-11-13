module

public import BlockBand.SourceProcess.CoupledFrames.ProbeModel

/-!
# The born Gram process from probe vectors: initial value and signature

* `bornG_zero_probe`: if `𝒢₀ = gramPair P (extFrame t h)`, `ProbeSpec` holds and every probe
  born at `0` has `v_i = 0`, then `G₀ = initialGram K π t h`.
* `bornL_sig_probe`: `L_t 𝖣 L_tᴴ = 𝖣'` (probe columns have zero signature).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CoupledFrames
open MeasureTheory Set Matrix Finset
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.SourceProcess.BornUnique
open BlockBand.SourceProcess.ModelExist
open scoped NNReal ComplexConjugate

variable {K R : ℕ} {π : Type*} [Fintype π] [DecidableEq π] {Ω : Type*}
  {𝒢 : ℝ≥0 → Ω → Matrix (ExtCol K R) (ExtCol K R) ℂ × Matrix (ExtCol K R) (ExtCol K R) ℂ}
  {σ : π → Ω → ℝ} {v : π → ℝ} {pv : π → Ω → ExtCol K R → ℂ} {ω : Ω}

theorem bornG_zero_probe {t : ℕ → ℝ} {h : ℝ}
    (h0 : 𝒢 0 ω = gramPair (ambP K R) (extFrame K R t h)) (hs : ProbeSpec 𝒢 σ v pv ω)
    (hherm : ∀ t, (𝒢 t ω).1ᴴ = (𝒢 t ω).1 ∧ (𝒢 t ω).2ᴴ = (𝒢 t ω).2)
    (hv0 : ∀ i, (σ i ω).toNNReal = 0 → v i = 0) :
    bornG 𝒢 (mθ K σ) (glam K R pv) 0 ω = initialGram K π t h := by
  refine ext_of_entries fun e => ?_
  have h1 := entry_sub_rep (𝒢 := 𝒢) (θ := mθ K σ) (lam := glam K R pv) e 0 ω
  have hz : ∀ r : WithTop ℝ≥0, stopTime r 0 = 0 := fun r => le_antisymm (stopTime_le _ 0) zero_le
  simp only [hz, sub_self, mul_zero, Finset.sum_const_zero, sub_zero] at h1
  rw [h1]
  obtain ⟨r, y, y'⟩ := e
  rcases y with k | i <;> rcases y' with k' | j
  · have hb : bTime (mθ K σ) (r, Sum.inl k, Sum.inl k') ω ≤ ((0 : ℝ≥0) : WithTop ℝ≥0) := by
      simp [bTime, mθ]
    rw [ite_eq_left hb, bVal_eq]
    simp only [mθ, max_self, glam, single_dot, h0]
    simp only [mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    exact extFrame_cur_entry t h r k k'
  · rw [bVal_probe_cur' hs]
    simp [initialGram, gramPair, gramEntry, sourceGram, nearGram, Matrix.mul_apply, initialFrame]
  · rw [bVal_cur_probe' hs hherm]
    simp [initialGram, gramPair, gramEntry, sourceGram, nearGram, Matrix.mul_apply, initialFrame]
  · by_cases hij : i = j
    · subst hij
      rw [bVal_probe_self' hs]
      split_ifs with hb
      · simp only [bTime, mθ, max_self] at hb
        rw [WithTop.coe_le_coe] at hb
        have : (σ i ω).toNNReal = 0 := le_antisymm hb zero_le
        simp [hv0 i this, initialGram, gramPair, gramEntry, sourceGram, nearGram,
          Matrix.mul_apply, initialFrame]
      · simp [initialGram, gramPair, gramEntry, sourceGram, nearGram, Matrix.mul_apply,
          initialFrame]
    · rw [bVal_probe_probe' hs hherm r hij]
      simp [initialGram, gramPair, gramEntry, sourceGram, nearGram, Matrix.mul_apply, initialFrame]

/-- **The born columns do not change the signature:** `L_t 𝖣 L_tᴴ = 𝖣'`. -/
theorem bornL_sig_probe (t : ℝ≥0) (ω : Ω) :
    bornL (mθ K σ) (glam K R pv) t ω * srcSignature K π * (bornL (mθ K σ) (glam K R pv) t ω)ᴴ =
      extSig K R := by
  ext x x'
  have hD : ∀ (A : Matrix (ExtCol K R) (SrcCol K π) ℂ) r y, (A * srcSignature K π) r y =
      A r y * (match y with | Sum.inl (_, σ) => if σ = 0 then (1 : ℂ) else -1 | Sum.inr _ => 0) :=
    fun A r y => by rw [srcSignature, Matrix.mul_diagonal]; rfl
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [hD]
  simp only [conjTranspose_apply, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, bornL, mθ,
    glam, zero_le, ↓reduceIte]
  rcases x with y | r <;> rcases x' with y' | r'
  · rw [Finset.sum_eq_single y (fun b _ hb => by simp [Pi.single_apply, Ne.symm hb]) (by simp)]
    by_cases hy : y = y' <;> simp [extSig, hy]
  · simp [extSig]
  · simp [extSig]
  · simp [extSig, diagonal_apply]

end BlockBand.SourceProcess.CoupledFrames
