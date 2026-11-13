module

public import BlockBand.SourceProcess.ModelExist.ModelCases2

/-!
# The birth values of the finite source model: conclusion

`bornRepresents_model`: if the selection meets its specification at every sorted birth and the
Gram process is Hermitian, the born Gram process represents the model (`BornRepresents`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ModelExist
open MeasureTheory Set Matrix Finset
open BlockBand.SourceProcess.Stochastic BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.BornUnique
open scoped NNReal ComplexConjugate

variable {K R : ℕ} {π : Type*} [Fintype π] [DecidableEq π] {n : ℕ} {eπ : π ≃ Fin n} {Ω : Type*}
  {sel : (Matrix (ExtCol K R) (ExtCol K R) ℂ × Matrix (ExtCol K R) (ExtCol K R) ℂ) ×
    (Fin n → ExtCol K R → ℂ) × ℝ → ExtCol K R → ℂ}
  {𝒢 : ℝ≥0 → Ω → Matrix (ExtCol K R) (ExtCol K R) ℂ × Matrix (ExtCol K R) (ExtCol K R) ℂ}
  {σ : π → Ω → ℝ} {v : π → ℝ} {ω : Ω}

omit [Fintype π] [DecidableEq π] in
theorem mlam_inl (k : Fin K × Fin 2) :
    mlam K R eπ sel 𝒢 σ v (Sum.inl k) ω = Pi.single (Sum.inl k) 1 := rfl

omit [Fintype π] [DecidableEq π] in
theorem gr_herm (hherm : ∀ t, (𝒢 t ω).1ᴴ = (𝒢 t ω).1 ∧ (𝒢 t ω).2ᴴ = (𝒢 t ω).2) (r : Fin 2)
    (t : ℝ≥0) : (gr r (𝒢 t ω))ᴴ = gr r (𝒢 t ω) := by
  unfold gr; split_ifs
  · exact (hherm t).1
  · exact (hherm t).2

omit [DecidableEq π] in
theorem bVal_probe_cur (h : AllSpec K R eπ sel 𝒢 σ v ω) (r : Fin 2) (i : π) (k : Fin K × Fin 2) :
    bVal 𝒢 (mθ K σ) (mlam K R eπ sel 𝒢 σ v) (r, Sum.inl k, Sum.inr i) ω = 0 := by
  have hs := probe_spec h i
  rw [bVal_eq]
  simp only [mθ, zero_max]
  rw [mlam_inl, single_dot, gr_mulVec hs.1.1]
  exact hs.1.2.1 (Sum.inl k) trivial

omit [DecidableEq π] in
theorem bVal_cur_probe (h : AllSpec K R eπ sel 𝒢 σ v ω)
    (hherm : ∀ t, (𝒢 t ω).1ᴴ = (𝒢 t ω).1 ∧ (𝒢 t ω).2ᴴ = (𝒢 t ω).2) (r : Fin 2) (i : π)
    (k : Fin K × Fin 2) :
    bVal 𝒢 (mθ K σ) (mlam K R eπ sel 𝒢 σ v) (r, Sum.inr i, Sum.inl k) ω = 0 := by
  have hs := probe_spec h i
  rw [bVal_eq]
  simp only [mθ, _root_.max_zero]
  rw [mlam_inl, herm_dot (gr_herm hherm r _), single_dot, gr_mulVec hs.1.1, hs.1.2.1 (Sum.inl k) trivial,
    star_zero]

omit [DecidableEq π] in
theorem bVal_probe_probe (h : AllSpec K R eπ sel 𝒢 σ v ω)
    (hherm : ∀ t, (𝒢 t ω).1ᴴ = (𝒢 t ω).1 ∧ (𝒢 t ω).2ᴴ = (𝒢 t ω).2) (r : Fin 2) {i j : π}
    (hij : i ≠ j) :
    bVal 𝒢 (mθ K σ) (mlam K R eπ sel 𝒢 σ v) (r, Sum.inr i, Sum.inr j) ω = 0 := by
  rw [bVal_eq]
  simp only [mθ]
  have hne : (srt (mθf eπ σ) ω).symm (eπ i) ≠ (srt (mθf eπ σ) ω).symm (eπ j) :=
    fun e => hij (eπ.injective ((srt (mθf eπ σ) ω).symm.injective e))
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨hle, hp⟩ := probe_perp h hlt
    rw [max_eq_right hle, gr_mulVec (probe_spec h j).1.1]
    exact hp
  · obtain ⟨hle, hp⟩ := probe_perp h hlt
    rw [max_eq_left hle, herm_dot (gr_herm hherm r _), gr_mulVec (probe_spec h i).1.1, hp,
      star_zero]

omit [DecidableEq π] in
theorem bVal_probe_self (h : AllSpec K R eπ sel 𝒢 σ v ω) (r : Fin 2) (i : π) :
    bVal 𝒢 (mθ K σ) (mlam K R eπ sel 𝒢 σ v) (r, Sum.inr i, Sum.inr i) ω = v i := by
  have hs := probe_spec h i
  rw [bVal_eq]
  simp only [mθ, max_self]
  rw [gr_mulVec hs.1.1]
  exact hs.2

theorem hcase_model (h : AllSpec K R eπ sel 𝒢 σ v ω)
    (hherm : ∀ t, (𝒢 t ω).1ᴴ = (𝒢 t ω).1 ∧ (𝒢 t ω).2ᴴ = (𝒢 t ω).2)
    (e : Fin 2 × SrcCol K π × SrcCol K π) (t : ℝ≥0) :
    (if bTime (mθ K σ) e ω ≤ t then bVal 𝒢 (mθ K σ) (mlam K R eπ sel 𝒢 σ v) e ω else 0) -
        gramEntry e (bJ (probeJump (K := K) v) σ t ω) =
      (if bTime (mθ K σ) e ω ≤ 0 then bVal 𝒢 (mθ K σ) (mlam K R eπ sel 𝒢 σ v) e ω else 0) -
        gramEntry e (bJ (probeJump (K := K) v) σ 0 ω) := by
  obtain ⟨r, y, y'⟩ := e
  rw [entry_bJ_probe, entry_bJ_probe]
  rcases y with k | i <;> rcases y' with k' | j
  · have h0 : ∀ u : ℝ≥0, bTime (mθ K σ) (r, Sum.inl k, Sum.inl k') ω ≤ u := fun u => by
      simp only [bTime, mθ, max_self]; exact WithTop.coe_le_coe.2 zero_le
    have h00 : bTime (mθ K σ) (r, Sum.inl k, Sum.inl k') ω ≤ 0 := by
      simp [bTime, mθ]
    simp only [h0, h00, ↓reduceIte, sub_zero]
  · rw [bVal_probe_cur h]
    split_ifs <;> simp
  · rw [bVal_cur_probe h hherm]
    split_ifs <;> simp
  · by_cases hij : i = j
    · subst hij
      have hle : ∀ u : ℝ≥0, (bTime (mθ K σ) (r, Sum.inr i, Sum.inr i) ω ≤ u ↔ σ i ω ≤ u) :=
        fun u => by
          simp only [bTime, mθ, max_self, WithTop.coe_le_coe, Real.toNNReal_le_iff_le_coe]
      rw [bVal_probe_self h]
      have h1 := hle t
      have h2 := hle 0
      rw [WithTop.coe_zero] at h2
      simp only [h1, h2, ite_true, sub_self]
    · rw [bVal_probe_probe h hherm r hij]
      simp only [hij, ↓reduceIte]
      split_ifs <;> simp

theorem bornRepresents_model (h : AllSpec K R eπ sel 𝒢 σ v ω)
    (hherm : ∀ t, (𝒢 t ω).1ᴴ = (𝒢 t ω).1 ∧ (𝒢 t ω).2ᴴ = (𝒢 t ω).2) :
    BornRepresents 𝒢 (mθ K σ) (mlam K R eπ sel 𝒢 σ v) (probeJump (K := K) v) σ ω :=
  bornRepresents_of fun e t => hcase_model h hherm e t

end BlockBand.SourceProcess.ModelExist
