module
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.Isometry
public import BlockBand.SourceProcess.Stochastic.FiniteSource
public import Mathlib.LinearAlgebra.Trace
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Every constrained frame has a realization of dimension `≤ 2|c|`

Given `IsNearProjection P Naux` and `TwoProjection P 𝖣 V` in an arbitrary ambient space, the
subspace `S = span(V, PV)` (columns) has dimension `≤ 2|c|`, is invariant under `P` and under
`P' = P + V𝖣Vᴴ` (`P' x = P x + V𝖣Vᴴ x`). Compressing by an isometry `J` onto `S`
(`P̃ = JᴴPJ`, `Ṽ = JᴴV`) gives a constrained frame in `ℂ^m`, `m ≤ 2|c|`, with a near projection
of some rank `Ñ ≤ m` and the **same Gram pair** (`exists_small_realization`). This is the
reduction to `span(V, PV)`, of dimension `≤ 2|c|`, used for the uniform rank barrier.
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness
open Matrix BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic

variable {ι c : Type*} [Fintype ι] [DecidableEq ι] [Fintype c] [DecidableEq c]

/-- The trace of an idempotent `m × m` matrix is a natural number `≤ m`. -/
theorem exists_nat_trace_of_idem {m : ℕ} (Q : Matrix (Fin m) (Fin m) ℂ) (hQ : Q * Q = Q) :
    ∃ N : ℕ, N ≤ m ∧ Q.trace = N := by
  have hf : Matrix.toLin' Q * Matrix.toLin' Q = Matrix.toLin' Q := by
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hQ]
  refine ⟨Module.finrank ℂ (LinearMap.range (Matrix.toLin' Q)), ?_, ?_⟩
  · have := Submodule.finrank_le (LinearMap.range (Matrix.toLin' Q))
    simpa using this
  · rw [← Matrix.trace_toLin'_eq, (LinearMap.IsIdempotentElem.isProj_range _ hf).trace]

omit [DecidableEq ι] [Fintype c] [DecidableEq c] in
/-- Compression by an isometry `J` whose range contains `V`, `PV` and is `P`-invariant. -/
theorem compress_props {κ : Type*} [Fintype κ] {P : Matrix ι ι ℂ} (hPH : Pᴴ = P)
    (hPP : P * P = P) {D : Matrix c c ℂ} [Fintype c] {V : Matrix ι c ℂ} (hV : TwoProjection P D V)
    (J : Matrix ι κ ℂ) (hJV : J * (Jᴴ * V) = V) (hJPV : J * (Jᴴ * (P * V)) = P * V)
    (hJPJ : J * (Jᴴ * (P * J)) = P * J) :
    (Jᴴ * P * J)ᴴ = Jᴴ * P * J ∧ (Jᴴ * P * J) * (Jᴴ * P * J) = Jᴴ * P * J ∧
      TwoProjection (Jᴴ * P * J) D (Jᴴ * V) ∧ gramPair (Jᴴ * P * J) (Jᴴ * V) = gramPair P V := by
  set P' := gramProjection P V D with hP'
  have hcomp : gramProjection (Jᴴ * P * J) (Jᴴ * V) D = Jᴴ * P' * J := by
    simp only [hP', gramProjection, conjTranspose_mul, conjTranspose_conjTranspose,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  have hJP'J : J * (Jᴴ * (P' * J)) = P' * J := by
    simp only [hP', gramProjection, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hJPJ]
    rw [← Matrix.mul_assoc Jᴴ V, ← Matrix.mul_assoc J, hJV]
  have hP'H : P'ᴴ = P' := hV.1
  have hP'P' : P' * P' = P' := hV.2.1
  refine ⟨?_, ?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · simp only [conjTranspose_mul, conjTranspose_conjTranspose, hPH, Matrix.mul_assoc]
  · simp only [Matrix.mul_assoc]
    rw [hJPJ, ← Matrix.mul_assoc P P, hPP]
  · rw [hcomp]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hP'H, Matrix.mul_assoc]
  · rw [hcomp]
    simp only [Matrix.mul_assoc]
    rw [hJP'J, ← Matrix.mul_assoc P' P', hP'P']
  · have h0 : (V * D * Vᴴ).trace = 0 := by
      have h := hV.2.2
      rw [gramProjection, trace_add] at h
      exact add_eq_left.mp h
    rw [gramProjection, trace_add]
    have : (Jᴴ * V * D * (Jᴴ * V)ᴴ).trace = 0 := by
      rw [conjTranspose_mul, conjTranspose_conjTranspose, trace_mul_comm (Jᴴ * V * D) (Vᴴ * J),
        show Vᴴ * J * (Jᴴ * V * D) = Vᴴ * (J * (Jᴴ * V)) * D by simp only [Matrix.mul_assoc],
        hJV, Matrix.mul_assoc Vᴴ V D, trace_mul_comm Vᴴ (V * D), h0]
    rw [this, add_zero]
  · simp only [gramPair, sourceGram, nearGram, conjTranspose_mul, conjTranspose_conjTranspose,
      Matrix.mul_assoc]
    rw [hJV, hJPV]

omit [DecidableEq ι] [DecidableEq c] in
/-- **Small realization.** Every constrained frame has a constrained realization of the same
Gram pair in `ℂ^m`, `m ≤ 2|c|`, with a near projection of rank `Ñ ≤ m`. -/
theorem exists_small_realization {Naux : ℕ} {P : Matrix ι ι ℂ} {D : Matrix c c ℂ}
    {V : Matrix ι c ℂ} (hP : IsNearProjection P Naux) (hV : TwoProjection P D V) :
    ∃ (m N : ℕ) (Pt : Matrix (Fin m) (Fin m) ℂ) (Vt : Matrix (Fin m) c ℂ),
      m ≤ 2 * Fintype.card c ∧ N ≤ m ∧ IsNearProjection Pt N ∧ TwoProjection Pt D Vt ∧
        gramPair Pt Vt = gramPair P V := by
  obtain ⟨hPH, hPP, -⟩ := hP
  set gens : c ⊕ c → EuclideanSpace ℂ ι := Sum.elim (colVec V) (colVec (P * V)) with hgens
  set S := Submodule.span ℂ (Set.range gens)
  have hVS : ColsIn S V := fun j => Submodule.subset_span ⟨Sum.inl j, rfl⟩
  have hPVS : ColsIn S (P * V) := fun j => Submodule.subset_span ⟨Sum.inr j, rfl⟩
  have hinv : MatInvariant S P := by
    refine matInvariant_span ?_
    rintro x ⟨s, rfl⟩
    have e : ∀ A : Matrix ι c ℂ, ∀ j,
        WithLp.toLp 2 (P *ᵥ WithLp.ofLp (colVec A j)) = colVec (P * A) j := fun A j => by
      ext i; simp [colVec, mul_apply, mulVec, dotProduct]
    rcases s with j | j
    · simp only [hgens, Sum.elim_inl, e]
      exact hPVS j
    · simp only [hgens, Sum.elim_inr, e, ← Matrix.mul_assoc, hPP]
      exact hPVS j
  set J := basisMatrix S
  have hJ := colsIn_basisMatrix S
  obtain ⟨hPt, hPPt, hTw, hG⟩ := compress_props hPH hPP hV J
    (basisMatrix_mul_conjTranspose_mul S hVS) (basisMatrix_mul_conjTranspose_mul S hPVS)
    (basisMatrix_mul_conjTranspose_mul S (hJ.left_mul hinv))
  obtain ⟨N, hNm, hN⟩ := exists_nat_trace_of_idem _ hPPt
  refine ⟨Module.finrank ℂ S, N, Jᴴ * P * J, Jᴴ * V, ?_, hNm, ⟨hPt, hPPt, hN⟩, hTw, hG⟩
  have : Module.finrank ℂ S ≤ Fintype.card (c ⊕ c) := finrank_range_le_card gens
  rw [Fintype.card_sum] at this
  omega

end BlockBand.SourceProcess.Stochastic.GramUniqueness
