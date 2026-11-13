module
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.GramReal
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.MartingaleTools
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Pathwise identities for the real Gram coordinates

Deterministic facts used by `isMPSolutionOn_gramReal`:
* continuity of the Gram coordinates, drift and covariance entries (`continuous_gramEntry`,
  `continuous_gramDriftEntry`, `continuous_gramCovEntry`, `continuous_toGramReal`);
* Hermitian symmetry at feasible states: `star (gramEntry e G) = gramEntry (gramSwap e) G` and the
  same for the drift (`gramScalar` is real);
* the real-coordinate algebra `reIm r z * reIm r' w = L(zw) + L'(z w̄)` (`realCovL`, `realCovL'`).
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness
open Matrix MeasureTheory BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {c : Type*} [Fintype c] [DecidableEq c]

/-- `reIm r` as a continuous real-linear map. -/
def reImCLM (r : Fin 2) : ℂ →L[ℝ] ℝ := if r = 0 then Complex.reCLM else Complex.imCLM

theorem reImCLM_apply (r : Fin 2) (z : ℂ) : reImCLM r z = reIm r z := by
  unfold reImCLM reIm; split_ifs <;> rfl

/-- First half of `realCovEntry` (acts on the bilinear bracket). -/
def realCovL (r r' : Fin 2) : ℂ →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • (if r = 0 then (if r' = 0 then Complex.reCLM else Complex.imCLM)
    else (if r' = 0 then Complex.imCLM else -Complex.reCLM))

/-- Second half of `realCovEntry` (acts on the sesquilinear bracket). -/
def realCovL' (r r' : Fin 2) : ℂ →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • (if r = 0 then (if r' = 0 then Complex.reCLM else -Complex.imCLM)
    else (if r' = 0 then Complex.imCLM else Complex.reCLM))

theorem realCovEntry_eq (r r' : Fin 2) (p q : ℂ) :
    realCovEntry r r' p q = realCovL r r' p + realCovL' r r' q := by
  fin_cases r <;> fin_cases r' <;>
    simp [realCovEntry, realCovL, realCovL'] <;> ring

theorem reIm_mul_reIm (r r' : Fin 2) (z w : ℂ) :
    reIm r z * reIm r' w = realCovL r r' (z * w) + realCovL' r r' (z * star w) := by
  rw [← realCovEntry_eq]
  fin_cases r <;> fin_cases r' <;>
    simp [realCovEntry, reIm, Complex.mul_re, Complex.mul_im]
  ring

omit [Fintype c] [DecidableEq c] in
theorem continuous_gramEntry (e : Fin 2 × c × c) :
    Continuous (gramEntry (c := c) e) := by
  unfold gramEntry
  split_ifs
  · exact continuous_fst.matrix_elem _ _
  · exact continuous_snd.matrix_elem _ _

omit [DecidableEq c] in
theorem continuous_gramScalar (D : Matrix c c ℂ) :
    Continuous fun G : Matrix c c ℂ × Matrix c c ℂ => gramScalar D G.1 := by
  unfold gramScalar
  exact continuous_const.mul ((((continuous_const.matrix_mul continuous_fst).matrix_mul
    continuous_const).matrix_mul continuous_fst).matrix_trace)

omit [DecidableEq c] in
theorem continuous_gramDriftEntry (D0 : ℝ) (D : Matrix c c ℂ) (e : Fin 2 × c × c) :
    Continuous (gramDriftEntry (c := c) D0 D e) := by
  unfold gramDriftEntry
  split_ifs
  · exact continuous_const
  · exact (continuous_const.mul (continuous_gramScalar D)).neg.mul
      (continuous_snd.matrix_elem _ _)

omit [DecidableEq c] in
theorem continuous_gramCovEntry (D0 : ℝ) (D : Matrix c c ℂ) (e e' : Fin 2 × c × c) :
    Continuous (gramCovEntry (c := c) D0 D e e') := by
  have hM : Continuous fun G : Matrix c c ℂ × Matrix c c ℂ => G.1 := continuous_fst
  have hB : Continuous fun G : Matrix c c ℂ × Matrix c c ℂ => G.2 := continuous_snd
  have h0 : Continuous fun G : Matrix c c ℂ × Matrix c c ℂ => gramC0 G.1 G.2 D :=
    hB.add ((hM.matrix_mul continuous_const).matrix_mul hM)
  have h1 : Continuous fun G : Matrix c c ℂ × Matrix c c ℂ => gramC1 G.1 G.2 D :=
    hB.add ((hM.matrix_mul continuous_const).matrix_mul hB)
  have h2 : Continuous fun G : Matrix c c ℂ × Matrix c c ℂ => gramC2 G.2 D :=
    hB.add ((hB.matrix_mul continuous_const).matrix_mul hB)
  have hcb : ∀ {Cl Cr : Matrix c c ℂ × Matrix c c ℂ → Matrix c c ℂ}, Continuous Cl →
      Continuous Cr → ∀ i j k l, Continuous fun G =>
        crossedBracket D0 G.2 (Cl G) (Cr G) i j k l := fun hl hr i j k l =>
    continuous_const.mul (((hB.matrix_elem _ _).mul (hl.matrix_elem _ _)).add
      ((hr.matrix_elem _ _).mul (hB.matrix_elem _ _)))
  obtain ⟨r, i, j⟩ := e
  obtain ⟨r', k, l⟩ := e'
  fin_cases r <;> fin_cases r'
  · exact hcb h0 h0 i j k l
  · exact hcb h1.matrix_conjTranspose h1 i j k l
  · exact hcb h1.matrix_conjTranspose h1 k l i j
  · exact hcb h2 h2 i j k l

omit [DecidableEq c] in
theorem continuous_toGramReal : Continuous (toGramReal (c := c)) :=
  continuous_pi fun i => by
    unfold toGramReal reIm
    split_ifs
    · exact Complex.continuous_re.comp (continuous_gramEntry _)
    · exact Complex.continuous_im.comp (continuous_gramEntry _)

omit [DecidableEq c] in
theorem gramEntry_gramDriftG (D0 : ℝ) (D : Matrix c c ℂ) (e : Fin 2 × c × c)
    (G : Matrix c c ℂ × Matrix c c ℂ) :
    gramEntry e (gramDriftG D0 D G) = gramDriftEntry D0 D e G := by
  unfold gramEntry gramDriftEntry gramDriftG
  split_ifs <;> simp

omit [DecidableEq c] in
theorem herm_of_feasible {D : Matrix c c ℂ} {G : Matrix c c ℂ × Matrix c c ℂ}
    (hG : GramFeasible D G) : G.1ᴴ = G.1 ∧ G.2ᴴ = G.2 := by
  obtain ⟨n, P, V, hPH, -, -, rfl⟩ := hG
  refine ⟨?_, ?_⟩
  · simp [gramPair, sourceGram]
  · simp [gramPair, nearGram, hPH, Matrix.mul_assoc]

omit [DecidableEq c] in
theorem star_gramScalar {D M : Matrix c c ℂ} (hD : Dᴴ = D) (hM : Mᴴ = M) :
    star (gramScalar D M) = gramScalar D M := by
  unfold gramScalar
  rw [star_mul', ← trace_conjTranspose]
  simp only [conjTranspose_mul, hD, hM, Matrix.mul_assoc, star_div₀, star_one, star_ofNat]
  congr 1
  rw [trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc]

omit [DecidableEq c] in
theorem star_gramDriftEntry {D0 : ℝ} {D : Matrix c c ℂ} (hD : Dᴴ = D)
    {G : Matrix c c ℂ × Matrix c c ℂ} (h1 : G.1ᴴ = G.1) (h2 : G.2ᴴ = G.2) (e : Fin 2 × c × c) :
    star (gramDriftEntry D0 D e G) = gramDriftEntry D0 D (gramSwap e) G := by
  obtain ⟨r, i, j⟩ := e
  unfold gramDriftEntry gramSwap
  split_ifs
  · simp
  · rw [star_mul', star_neg, star_mul', star_gramScalar hD h1, Complex.star_def,
      Complex.conj_ofReal]
    congr 1
    conv_rhs => rw [← h2]
    rw [conjTranspose_apply]
    rfl

end BlockBand.SourceProcess.Stochastic.GramUniqueness
