module

public import BlockBand.SourceProcess.ClosedSummedProof.GramMatch

/-!
# The covariance match: polarized `wordCov` = `gramCovEntry` (deterministic)

The cross contraction of the word covariance rule for two polarized one-letter words, with
`J = V𝖣Vᴴ`, is the `gramCovEntry` of the finite Gram law, for all four pairs
of coordinate types (`M`/`B`). Hermitian `𝖣` is used for the conjugate `C₁ᴴ = B + B𝖣M`.

* `cov_sum`: `Σ_{k,l}(iᵏ/4)(iˡ/4) cov = (D₀/2)[2B_{ad}B_{cb} + B_{ad}(G'𝖣G)_{cb} + (G𝖣G')_{ad}B_{cb}]`
  with `G = VᴴT_σV`, `G' = VᴴT_σ'V`;
* **`cov_match`**: the same sum is `gramCovEntry D₀ 𝖣 e e' (gramPair P V)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedSummedProof

open Matrix
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.ContractingWords
open BlockBand.SourceProcess.Stochastic BlockBand.Internal.Contracts.TransmissionPath

variable {W : ℕ} {c : Type} [Fintype c]

theorem frame_sandwich {ι : Type} [Fintype ι] (V : Matrix ι c ℂ) (D : Matrix c c ℂ)
    (X Y : Matrix ι ι ℂ) : Vᴴ * (X * (V * D * Vᴴ * Y)) * V = (Vᴴ * X * V) * D * (Vᴴ * Y * V) := by
  simp only [Matrix.mul_assoc]

theorem frame_sandwich' {ι : Type} [Fintype ι] (V : Matrix ι c ℂ) (D : Matrix c c ℂ)
    (X Y : Matrix ι ι ℂ) : Vᴴ * (X * (V * D * Vᴴ) * Y) * V = (Vᴴ * X * V) * D * (Vᴴ * Y * V) := by
  simp only [Matrix.mul_assoc]

/-- The polarized covariance sum, in Gram form. -/
theorem cov_sum [DecidableEq c] (D0 : ℝ) (V : Matrix (Fin 2 × Fin W) c ℂ) (D : Matrix c c ℂ)
    (T : Separator → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (e e' : Fin 2 × c × c) :
    ∑ k, ∑ l, polCoef k * polCoef l *
        MvPolynomial.eval (fun v => coreProd (gramLetters (V * D * Vᴴ) V e e') T [v])
          (wordCov D0 [(tagL k, gramSep e.1)] [(tagR l, gramSep e'.1)]) =
      ((D0 / 2 : ℝ) : ℂ) * (2 * ((Vᴴ * T .proj * V) e.2.1 e'.2.2 * (Vᴴ * T .proj * V) e'.2.1 e.2.2) +
        (Vᴴ * T .proj * V) e.2.1 e'.2.2 *
          ((Vᴴ * T (gramSep e'.1) * V) * D * (Vᴴ * T (gramSep e.1) * V)) e'.2.1 e.2.2 +
        ((Vᴴ * T (gramSep e.1) * V) * D * (Vᴴ * T (gramSep e'.1) * V)) e.2.1 e'.2.2 *
          (Vᴴ * T .proj * V) e'.2.1 e.2.2) := by
  simp only [eval_wordCov_one, gramLetters_tagL, gramLetters_tagR]
  have hJ : gramLetters (V * D * Vᴴ) V e e' .current = V * D * Vᴴ := rfl
  rw [hJ]
  set s := gramSep e.1
  set s' := gramSep e'.1
  have pt : ∀ k l : Fin 4, polCoef k * polCoef l * (((D0 / 2 : ℝ) : ℂ) *
      ((entryLetter V e k * T .proj * (entryLetter V e' l * T .proj)).trace +
        (entryLetter V e k * T .proj * (entryLetter V e' l * T s' * (V * D * Vᴴ * T s))).trace +
        ((entryLetter V e k * T .proj * (entryLetter V e' l * T .proj)).trace +
          (entryLetter V e k * T s * (V * D * Vᴴ * T s' * (entryLetter V e' l * T .proj))).trace))) =
      ((D0 / 2 : ℝ) : ℂ) * (2 * (polCoef k * polCoef l *
          (entryLetter V e k * T .proj * (entryLetter V e' l * T .proj)).trace) +
        polCoef k * polCoef l *
          (entryLetter V e k * T .proj * (entryLetter V e' l * (T s' * (V * D * Vᴴ * T s)))).trace +
        polCoef k * polCoef l *
          (entryLetter V e k * (T s * (V * D * Vᴴ) * T s') * (entryLetter V e' l * T .proj)).trace) := by
    intro k l
    have a1 : entryLetter V e' l * T s' * (V * D * Vᴴ * T s) =
        entryLetter V e' l * (T s' * (V * D * Vᴴ * T s)) := by simp only [Matrix.mul_assoc]
    have a2 : entryLetter V e k * T s * (V * D * Vᴴ * T s' * (entryLetter V e' l * T .proj)) =
        entryLetter V e k * (T s * (V * D * Vᴴ) * T s') * (entryLetter V e' l * T .proj) := by
      simp only [Matrix.mul_assoc]
    rw [a1, a2]; ring
  simp only [pt, ← Finset.mul_sum, Finset.sum_add_distrib, sum_entry_two]
  rw [frame_sandwich, frame_sandwich']

/-- `C₁ᴴ = B + B𝖣M` for Hermitian `M, B, 𝖣`. -/
theorem gramC1_conjTranspose {M B D : Matrix c c ℂ} (hM : Mᴴ = M) (hB : Bᴴ = B) (hD : Dᴴ = D) :
    (BlockBand.SourceProcess.gramC1 M B D)ᴴ = B + B * D * M := by
  simp only [BlockBand.SourceProcess.gramC1, conjTranspose_add, conjTranspose_mul, hM, hB, hD,
    Matrix.mul_assoc]

/-- **The covariance match.** -/
theorem cov_match [DecidableEq c] (D0 : ℝ) (V : Matrix (Fin 2 × Fin W) c ℂ) (D : Matrix c c ℂ) (hD : Dᴴ = D)
    (T : Separator → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (h1 : T .id = 1)
    (hP : T .proj = nearProjection W) (e e' : Fin 2 × c × c) :
    ∑ k, ∑ l, polCoef k * polCoef l *
        MvPolynomial.eval (fun v => coreProd (gramLetters (V * D * Vᴴ) V e e') T [v])
          (wordCov D0 [(tagL k, gramSep e.1)] [(tagR l, gramSep e'.1)]) =
      gramCovEntry D0 D e e' (gramPair (nearProjection W) V) := by
  rw [cov_sum]
  have hM : (Vᴴ * V)ᴴ = Vᴴ * V := by rw [conjTranspose_mul, conjTranspose_conjTranspose]
  have hB : (Vᴴ * nearProjection W * V)ᴴ = Vᴴ * nearProjection W * V := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
      BlockBand.Transmission.Bridge.nearProjection_conjTranspose, Matrix.mul_assoc]
  have hC := gramC1_conjTranspose hM hB hD
  obtain ⟨σ, a, b⟩ := e
  obtain ⟨σ', c', d⟩ := e'
  fin_cases σ <;> fin_cases σ' <;>
    simp only [gramCovEntry, gramSep, gramPair, sourceGram, nearGram, h1, hP, hC, Fin.zero_eta,
      Fin.mk_one, Fin.isValue, Matrix.mul_one, ite_true, one_ne_zero, ite_false] <;>
    simp only [crossedBracket, BlockBand.SourceProcess.gramC0, BlockBand.SourceProcess.gramC1,
      BlockBand.SourceProcess.gramC2, Matrix.add_apply] <;> ring

end BlockBand.SourceProcess.ClosedSummedProof
