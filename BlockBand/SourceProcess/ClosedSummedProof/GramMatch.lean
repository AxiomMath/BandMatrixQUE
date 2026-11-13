module

public import BlockBand.SourceProcess.ClosedSummedProof.GramWords
public import BlockBand.SourceProcess.Stochastic.FiniteSource

/-!
# Polarized one-letter words reproduce the Gram drift (deterministic matching)

Letters (`gramLetters`): `J` and, for two Gram entries `e = (σ,a,b)`, `e' = (σ',c,d)`, the tags
`k < 4` (resp. `4 + k`) carry `rk1 (v_b + iᵏ v_a)` (resp. `rk1 (v_d + iᵏ v_c)`).

* `sum_entry`: `Σ_k (iᵏ/4) Tr(L_k X) = (VᴴXV)_{ab}`; `sum_entry_two`: the bilinear analogue;
* **`drift_match`**: `Σ_k (iᵏ/4)·drift[(tag k, σ)] = gramDriftEntry D₀ 𝖣 e (gramPair P V)`.

The covariance analogue `cov_match`,
`Σ_{k,l} (iᵏ/4)(iˡ/4)·cov([(tag k,σ)],[(tag 4+l,σ')]) = gramCovEntry D₀ 𝖣 e e' (gramPair P V)`,
is proved separately.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedSummedProof

open Matrix
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.ContractingWords
open BlockBand.SourceProcess.Stochastic BlockBand.Internal.Contracts.TransmissionPath

variable {W : ℕ} {c : Type}

/-- Column `a` of a frame. -/
def colOf {ι : Type} (V : Matrix ι c ℂ) (a : c) : ι → ℂ := fun x => V x a

/-- The Gram separator: `I` for `M` (`σ = 0`), `P` for `B` (`σ = 1`). -/
def gramSep (σ : Fin 2) : Separator := if σ = 0 then .id else .proj

/-- The polarized letters `rk1 (v_b + iᵏ v_a)` of the entry `e = (σ, a, b)`. -/
def entryLetter {ι : Type} [Fintype ι] (V : Matrix ι c ℂ) (e : Fin 2 × c × c) (k : Fin 4) :
    Matrix ι ι ℂ :=
  rk1 (polVec (colOf V e.2.2) (colOf V e.2.1) k)

/-- The letter matrices: the current `J`, then the polarized letters of `e` and `e'`. -/
def gramLetters (J : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (V : Matrix (Fin 2 × Fin W) c ℂ)
    (e e' : Fin 2 × c × c) : TraceLetter 8 0 → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ
  | .current => J
  | .tag t => Fin.addCases (m := 4) (n := 4) (entryLetter V e) (entryLetter V e') t
  | .interval a => a.elim0

/-- The tag of polarization `k` of `e`. -/
def tagL (k : Fin 4) : TraceLetter 8 0 := .tag (Fin.castAdd 4 k)

/-- The tag of polarization `k` of `e'`. -/
def tagR (k : Fin 4) : TraceLetter 8 0 := .tag (Fin.natAdd 4 k)

theorem gramLetters_tagL (J : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (V : Matrix (Fin 2 × Fin W) c ℂ) (e e' : Fin 2 × c × c) (k : Fin 4) :
    gramLetters J V e e' (tagL k) = entryLetter V e k := by
  simp [gramLetters, tagL]

theorem gramLetters_tagR (J : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (V : Matrix (Fin 2 × Fin W) c ℂ) (e e' : Fin 2 × c × c) (k : Fin 4) :
    gramLetters J V e e' (tagR k) = entryLetter V e' k := by
  exact Fin.addCases_right (motive := fun _ => Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) k

section Sums

variable {ι : Type} [Fintype ι] (V : Matrix ι c ℂ)

theorem sum_letters (e : Fin 2 × c × c) :
    ∑ k, polCoef k • entryLetter V e k = vecMulVec (colOf V e.2.2) (star (colOf V e.2.1)) :=
  pol_sum _ _

/-- `Σ_k (iᵏ/4) Tr(L_k X) = (VᴴXV)_{ab}`. -/
theorem sum_entry [Fintype c] (e : Fin 2 × c × c) (X : Matrix ι ι ℂ) :
    ∑ k, polCoef k * (entryLetter V e k * X).trace = (Vᴴ * X * V) e.2.1 e.2.2 := by
  have h : ∑ k, polCoef k * (entryLetter V e k * X).trace =
      ((∑ k, polCoef k • entryLetter V e k) * X).trace := by
    rw [Finset.sum_mul, Matrix.trace_sum]
    simp [Matrix.trace_smul]
  rw [h, sum_letters]
  exact trace_col V X _ _

/-- `Σ_{k,l} (iᵏ/4)(iˡ/4) Tr(L_k X L'_l Y) = (VᴴXV)_{ad}(VᴴYV)_{cb}`. -/
theorem sum_entry_two [Fintype c] (e e' : Fin 2 × c × c) (X Y : Matrix ι ι ℂ) :
    ∑ k, ∑ l, polCoef k * polCoef l * (entryLetter V e k * X * (entryLetter V e' l * Y)).trace =
      (Vᴴ * X * V) e.2.1 e'.2.2 * (Vᴴ * Y * V) e'.2.1 e.2.2 := by
  have h : ∑ k, ∑ l, polCoef k * polCoef l *
      (entryLetter V e k * X * (entryLetter V e' l * Y)).trace =
      ((∑ k, polCoef k • entryLetter V e k) * X * ((∑ l, polCoef l • entryLetter V e' l) * Y)).trace := by
    simp only [Finset.sum_mul, Finset.mul_sum, Matrix.trace_sum, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [h, sum_letters, sum_letters]
  exact trace_col_two V X Y _ _ _ _

end Sums

/-- Gram coordinates read through the separators `T .id = 1`, `T .proj = P`. -/
theorem gramEntry_sep [Fintype c] (V : Matrix (Fin 2 × Fin W) c ℂ)
    (T : Separator → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (h1 : T .id = 1)
    (hP : T .proj = nearProjection W) (e : Fin 2 × c × c) :
    gramEntry e (gramPair (nearProjection W) V) = (Vᴴ * T (gramSep e.1) * V) e.2.1 e.2.2 := by
  obtain ⟨σ, a, b⟩ := e
  fin_cases σ <;> simp [gramEntry, gramPair, sourceGram, nearGram, gramSep, h1, hP]

/-- `Tr(JJ) = Tr(𝖣M𝖣M)` for `J = V𝖣Vᴴ`, `M = VᴴV`. -/
theorem trace_frameCurrent_sq {ι : Type} [Fintype ι] [Fintype c] (V : Matrix ι c ℂ)
    (D : Matrix c c ℂ) :
    (V * D * Vᴴ * (V * D * Vᴴ)).trace = (D * (Vᴴ * V) * D * (Vᴴ * V)).trace := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem sum_neg_mul (f : Fin 4 → ℂ) (K : ℂ) :
    ∑ k, polCoef k * -(K * f k) = -K * ∑ k, polCoef k * f k := by
  rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring

/-- **The drift match**: the word generator on polarized one-letter words gives the Gram
drift. -/
theorem drift_match [Fintype c] [DecidableEq c] (D0 : ℝ) (V : Matrix (Fin 2 × Fin W) c ℂ)
    (D : Matrix c c ℂ) (T : Separator → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (h1 : T .id = 1) (hP : T .proj = nearProjection W) (e e' : Fin 2 × c × c) :
    ∑ k, polCoef k * MvPolynomial.eval (fun v => coreProd (gramLetters (V * D * Vᴴ) V e e') T [v])
        (wordDrift D0 [(tagL k, gramSep e.1)]) =
      gramDriftEntry D0 D e (gramPair (nearProjection W) V) := by
  simp only [eval_wordDrift_one, gramLetters_tagL]
  have hJ : gramLetters (V * D * Vᴴ) V e e' .current = V * D * Vᴴ := rfl
  rw [hJ, h1, Matrix.mul_one, sum_neg_mul, sum_entry, trace_frameCurrent_sq]
  obtain ⟨σ, a, b⟩ := e
  fin_cases σ
  · simp [gramDriftEntry, gramSep]
  · simp [gramDriftEntry, gramSep, gramPair, nearGram, sourceGram, gramScalar, hP]

end BlockBand.SourceProcess.ClosedSummedProof
