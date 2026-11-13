module

public import BlockBand.SourceProcess.ClosedSummedProof.LayerInt

/-!
# The polarized Gram letters satisfy the hypotheses of `LayerDrift`/`LayerCov`

The letters `gramLetters` are Hermitian (`gramLetters_herm`) with bounded nuclear norms
(`gramLetters_nuc`), the one-letter tag words are ordinary (`ordinary_tag`), and the contracting
drift sum of a tag is at most `4·contrGram` (`contrDrift_gram_le`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedSummedProof

open Matrix MeasureTheory
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.ContractingWords
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.CompleteSourceGap
open scoped Matrix.Norms.L2Operator

variable {W : ℕ} {c : Type} [Fintype c] [DecidableEq c]

/-- The diagonal signature matrix `diag(d)`. -/
abbrev sigD (d : c → ℝ) : Matrix c c ℂ := diagonal fun x => (d x : ℂ)

omit [DecidableEq c] in
theorem sum_col_sq_le {ι : Type} [Fintype ι] (V : Matrix ι c ℂ) (a : c) :
    ∑ x, ‖V x a‖ ^ 2 ≤ (Vᴴ * V).trace.re := by
  have e : (Vᴴ * V).trace.re = ∑ a', ∑ x, ‖V x a'‖ ^ 2 := by
    simp only [Matrix.trace, diag_apply, mul_apply, conjTranspose_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun x _ => ?_
    rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    exact_mod_cast rfl
  rw [e]
  exact Finset.single_le_sum (f := fun a' => ∑ x, ‖V x a'‖ ^ 2) (fun _ _ => by positivity)
    (Finset.mem_univ a)

omit [DecidableEq c] in
theorem nuclearNorm_entryLetter_le {ι : Type} [Fintype ι] [DecidableEq ι] (V : Matrix ι c ℂ)
    (e : Fin 2 × c × c) (k : Fin 4) :
    nuclearNorm (entryLetter V e k) ≤ 2 * (2 * (Vᴴ * V).trace.re) := by
  rw [entryLetter, nuclearNorm_rk1]
  have h1 := sum_col_sq_le V e.2.2
  have h2 := sum_col_sq_le V e.2.1
  calc ∑ x, ‖polVec (colOf V e.2.2) (colOf V e.2.1) k x‖ ^ 2
      ≤ ∑ x, 2 * (‖V x e.2.2‖ ^ 2 + ‖V x e.2.1‖ ^ 2) :=
        Finset.sum_le_sum fun x _ => norm_polVec_sq_le _ _ k x
    _ = 2 * (∑ x, ‖V x e.2.2‖ ^ 2 + ∑ x, ‖V x e.2.1‖ ^ 2) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 2 * (2 * (Vᴴ * V).trace.re) := by linarith

theorem tag_cases (t : Fin 8) : (∃ k : Fin 4, TraceLetter.tag (nT := 8) (nI := 0) t = tagL k) ∨
    (∃ k : Fin 4, TraceLetter.tag (nT := 8) (nI := 0) t = tagR k) := by
  rcases t with ⟨n, hn⟩
  by_cases h : n < 4
  · exact Or.inl ⟨⟨n, h⟩, rfl⟩
  · refine Or.inr ⟨⟨n - 4, by omega⟩, ?_⟩
    simp only [tagR, TraceLetter.tag.injEq]
    ext; simp; omega

theorem gramLetters_herm (V : Matrix (Fin 2 × Fin W) c ℂ) (d : c → ℝ) (e e' : Fin 2 × c × c) :
    ∀ ℓ, (gramLetters (V * sigD d * Vᴴ) V e e' ℓ).IsHermitian := by
  have hD : (sigD d).IsHermitian := isHermitian_diagonal_of_self_adjoint _ (by ext x; simp)
  intro ℓ
  cases ℓ with
  | current => exact isHermitian_mul_mul_conjTranspose V hD
  | tag t =>
    rcases tag_cases t with ⟨k, hk⟩ | ⟨k, hk⟩
    · rw [hk, gramLetters_tagL]; exact isHermitian_rk1 _
    · rw [hk, gramLetters_tagR]; exact isHermitian_rk1 _
  | interval a => exact a.elim0

theorem gramLetters_nuc (V : Matrix (Fin 2 × Fin W) c ℂ) (d : c → ℝ) (hd : ∀ x, |d x| ≤ 1)
    (R : ℝ) (hR : (Vᴴ * V).trace.re ≤ R) (e e' : Fin 2 × c × c) :
    ∀ ℓ, nuclearNorm (gramLetters (V * sigD d * Vᴴ) V e e' ℓ) ≤ 2 * (2 * max R 0) := by
  have hR' : (Vᴴ * V).trace.re ≤ max R 0 := hR.trans (le_max_left _ _)
  have h0 := le_max_right R 0
  intro ℓ
  cases ℓ with
  | current =>
    exact (nuclearNorm_frameCurrent_le V d hd).trans (by linarith)
  | tag t =>
    rcases tag_cases t with ⟨k, hk⟩ | ⟨k, hk⟩
    · rw [hk, gramLetters_tagL]; exact (nuclearNorm_entryLetter_le V e k).trans (by linarith)
    · rw [hk, gramLetters_tagR]; exact (nuclearNorm_entryLetter_le V e' k).trans (by linarith)
  | interval a => exact a.elim0

theorem ordinary_tag (t : TraceLetter 8 0) (σ : Fin 2) : IsOrdinaryWord [(t, gramSep σ)] := by
  refine ⟨List.cons_ne_nil _ _, fun x hx => ?_⟩
  rw [List.mem_singleton] at hx
  subst hx
  unfold gramSep; split_ifs <;> simp

theorem wordInjection_tag (b : ℝ) (q : Fin 0 → ℝ → ℝ) (t : ℝ) (u : TraceLetter 8 0)
    (σ : Separator) : wordInjection b q t [(u, σ)] = 0 := by
  cases u with
  | current => rfl
  | tag _ => rfl
  | interval a => exact a.elim0

omit [DecidableEq c] in
/-- `‖Tr(L_k τ)‖ ≤ 4 Σ‖(VᴴτV)_{xy}‖`, summed over the contracting `τ`: at most `4·contrGram`. -/
theorem contrDrift_gram_le (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (V : Matrix (Fin 2 × Fin W) c ℂ) (J : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (e e' : Fin 2 × c × c) (t : TraceLetter 8 0) (k : Fin 4) (ht : gramLetters J V e e' t = entryLetter V e k)
    (σ : Separator) :
    ((contrDrift [(t, σ)]).map fun Zs => ‖coreProd (gramLetters J V e e') (sepOf b E XX) Zs‖).sum ≤
      4 * contrGram b E XX V := by
  rw [contrDrift_one, ht]
  have hb := fun τ => norm_trace_rk1_le V (sepOf b E XX τ) e.2.1 e.2.2 k
  simp only [entryLetter, contrGram, contrSepSet]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  linarith [hb .projS, hb .sStarProj, hb .projSProj, hb .projSStarProj]

end BlockBand.SourceProcess.ClosedSummedProof
