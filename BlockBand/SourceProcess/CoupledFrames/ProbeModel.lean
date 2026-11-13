module

public import BlockBand.SourceProcess.ModelExist.ModelInit

/-!
# Born Gram processes from probe vectors with a specification

For a Gram process `𝒢` on the extended columns, probe birth times `θ_i = (σ_i)⁺` and probe vectors
`pv_i`, the target columns are `glam pv` (current column `(k, σ)` = extended column `inl (k, σ)`,
probe `i` = `pv_i`). `ProbeSpec`: at `θ_i`, `pv_i` is near (`(M − B) pv_i = 0`), perpendicular to
the current columns (`(M pv_i)_k = 0`), of squared norm `v_i`, and `pv_iᴴ M(θ_j) pv_j = 0` for
`i ≠ j` with `θ_i ≤ θ_j`. Then `BornRepresents` holds (`bornRepresents_probe`), and
`G_0 = initialGram` (`bornG_zero_probe`). `bornL_sig_probe`: `L 𝖣 Lᴴ = 𝖣'`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CoupledFrames
open MeasureTheory Set Matrix Finset
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.SourceProcess.BornUnique
open BlockBand.SourceProcess.ModelExist
open scoped NNReal ComplexConjugate

variable {K R : ℕ} {π : Type*} [Fintype π] [DecidableEq π] {Ω : Type*}

/-- The target-column vectors: current columns are extended unit vectors, probes are `pv`. -/
def glam (K R : ℕ) (pv : π → Ω → ExtCol K R → ℂ) : SrcCol K π → Ω → ExtCol K R → ℂ
  | Sum.inl k => fun _ => Pi.single (Sum.inl k) 1
  | Sum.inr i => pv i

/-- **The probe specification** at a sample point. -/
def ProbeSpec (𝒢 : ℝ≥0 → Ω → Matrix (ExtCol K R) (ExtCol K R) ℂ × Matrix (ExtCol K R) (ExtCol K R) ℂ)
    (σ : π → Ω → ℝ) (v : π → ℝ) (pv : π → Ω → ExtCol K R → ℂ) (ω : Ω) : Prop :=
  (∀ i, ((𝒢 (σ i ω).toNNReal ω).1 - (𝒢 (σ i ω).toNNReal ω).2) *ᵥ pv i ω = 0 ∧
      (∀ k, ((𝒢 (σ i ω).toNNReal ω).1 *ᵥ pv i ω) (Sum.inl k) = 0) ∧
      star (pv i ω) ⬝ᵥ ((𝒢 (σ i ω).toNNReal ω).1 *ᵥ pv i ω) = (v i : ℂ)) ∧
    ∀ i j, i ≠ j → (σ i ω).toNNReal ≤ (σ j ω).toNNReal →
      star (pv i ω) ⬝ᵥ ((𝒢 (σ j ω).toNNReal ω).1 *ᵥ pv j ω) = 0

variable {𝒢 : ℝ≥0 → Ω → Matrix (ExtCol K R) (ExtCol K R) ℂ × Matrix (ExtCol K R) (ExtCol K R) ℂ}
  {σ : π → Ω → ℝ} {v : π → ℝ} {pv : π → Ω → ExtCol K R → ℂ} {ω : Ω}

omit [DecidableEq π] in
theorem bVal_probe_cur' (h : ProbeSpec 𝒢 σ v pv ω) (r : Fin 2) (i : π) (k : Fin K × Fin 2) :
    bVal 𝒢 (mθ K σ) (glam K R pv) (r, Sum.inl k, Sum.inr i) ω = 0 := by
  rw [bVal_eq]
  simp only [mθ, zero_max, glam]
  rw [single_dot, gr_mulVec (h.1 i).1]
  exact (h.1 i).2.1 k

omit [DecidableEq π] in
theorem bVal_cur_probe' (h : ProbeSpec 𝒢 σ v pv ω)
    (hherm : ∀ t, (𝒢 t ω).1ᴴ = (𝒢 t ω).1 ∧ (𝒢 t ω).2ᴴ = (𝒢 t ω).2) (r : Fin 2) (i : π)
    (k : Fin K × Fin 2) :
    bVal 𝒢 (mθ K σ) (glam K R pv) (r, Sum.inr i, Sum.inl k) ω = 0 := by
  rw [bVal_eq]
  simp only [mθ, _root_.max_zero, glam]
  rw [herm_dot (gr_herm hherm r _), single_dot, gr_mulVec (h.1 i).1, (h.1 i).2.1 k, star_zero]

omit [DecidableEq π] in
theorem bVal_probe_probe' (h : ProbeSpec 𝒢 σ v pv ω)
    (hherm : ∀ t, (𝒢 t ω).1ᴴ = (𝒢 t ω).1 ∧ (𝒢 t ω).2ᴴ = (𝒢 t ω).2) (r : Fin 2) {i j : π}
    (hij : i ≠ j) :
    bVal 𝒢 (mθ K σ) (glam K R pv) (r, Sum.inr i, Sum.inr j) ω = 0 := by
  rw [bVal_eq]
  simp only [mθ, glam]
  rcases le_total (σ i ω).toNNReal (σ j ω).toNNReal with hle | hle
  · rw [max_eq_right hle, gr_mulVec (h.1 j).1]
    exact h.2 i j hij hle
  · rw [max_eq_left hle, herm_dot (gr_herm hherm r _), gr_mulVec (h.1 i).1,
      h.2 j i (Ne.symm hij) hle, star_zero]

omit [DecidableEq π] in
theorem bVal_probe_self' (h : ProbeSpec 𝒢 σ v pv ω) (r : Fin 2) (i : π) :
    bVal 𝒢 (mθ K σ) (glam K R pv) (r, Sum.inr i, Sum.inr i) ω = v i := by
  rw [bVal_eq]
  simp only [mθ, max_self, glam]
  rw [gr_mulVec (h.1 i).1]
  exact (h.1 i).2.2

theorem hcase_probe (h : ProbeSpec 𝒢 σ v pv ω)
    (hherm : ∀ t, (𝒢 t ω).1ᴴ = (𝒢 t ω).1 ∧ (𝒢 t ω).2ᴴ = (𝒢 t ω).2)
    (e : Fin 2 × SrcCol K π × SrcCol K π) (t : ℝ≥0) :
    (if bTime (mθ K σ) e ω ≤ t then bVal 𝒢 (mθ K σ) (glam K R pv) e ω else 0) -
        gramEntry e (bJ (probeJump (K := K) v) σ t ω) =
      (if bTime (mθ K σ) e ω ≤ 0 then bVal 𝒢 (mθ K σ) (glam K R pv) e ω else 0) -
        gramEntry e (bJ (probeJump (K := K) v) σ 0 ω) := by
  obtain ⟨r, y, y'⟩ := e
  rw [entry_bJ_probe, entry_bJ_probe]
  rcases y with k | i <;> rcases y' with k' | j
  · have h0 : ∀ u : ℝ≥0, bTime (mθ K σ) (r, Sum.inl k, Sum.inl k') ω ≤ u := fun u => by
      simp only [bTime, mθ, max_self]; exact WithTop.coe_le_coe.2 zero_le
    have h00 : bTime (mθ K σ) (r, Sum.inl k, Sum.inl k') ω ≤ 0 := by
      simp [bTime, mθ]
    simp only [h0, h00, ↓reduceIte, sub_zero]
  · rw [bVal_probe_cur' h]
    split_ifs <;> simp
  · rw [bVal_cur_probe' h hherm]
    split_ifs <;> simp
  · by_cases hij : i = j
    · subst hij
      have hle : ∀ u : ℝ≥0, (bTime (mθ K σ) (r, Sum.inr i, Sum.inr i) ω ≤ u ↔ σ i ω ≤ u) :=
        fun u => by
          simp only [bTime, mθ, max_self, WithTop.coe_le_coe, Real.toNNReal_le_iff_le_coe]
      rw [bVal_probe_self' h]
      have h1 := hle t
      have h2 := hle 0
      rw [WithTop.coe_zero] at h2
      simp only [h1, h2, ite_true, sub_self]
    · rw [bVal_probe_probe' h hherm r hij]
      simp only [hij, ↓reduceIte]
      split_ifs <;> simp

/-- **`BornRepresents` from the probe specification.** -/
theorem bornRepresents_probe (h : ProbeSpec 𝒢 σ v pv ω)
    (hherm : ∀ t, (𝒢 t ω).1ᴴ = (𝒢 t ω).1 ∧ (𝒢 t ω).2ᴴ = (𝒢 t ω).2) :
    BornRepresents 𝒢 (mθ K σ) (glam K R pv) (probeJump (K := K) v) σ ω :=
  bornRepresents_of fun e t => hcase_probe h hherm e t

end BlockBand.SourceProcess.CoupledFrames
