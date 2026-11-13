module

public import BlockBand.SourceProcess.ClosedSummedProof.GramCov
public import BlockBand.SourceProcess.ContractingWords.WordsHolds

/-!
# Tools for the one-layer Gram estimates

* `layerGram b E 𝕏 V y = gramPair P (N(y)ᴴ V)`: the Gram pair after one fresh layer at the old
  two-port `𝕏` (`N = freshTransport`; frames transport as `V ↦ NᴴV`);
* `contrGram b E 𝕏 V = Σ_{σ ∈ {P𝕊, 𝕊*P, P𝕊P, P𝕊*P}} Σ_{x,y} ‖(VᴴσV)_{xy}‖`: the contracting Gram
  coordinates, which carry the summable part of the one-layer errors;
* `norm_trace_mul_le`, `norm_trace_rk1_le`: `‖Tr(LY)‖ ≤ (Σ|L_{ij}|)‖Y‖`, and
  `‖Tr(uu*T)‖ ≤ 4 Σ_{x,y}‖(VᴴTV)_{xy}‖` for `u = v_b + iᵏv_a`;
* `layerNew_tag`, `trace_conj_cycle`, `sum_new`: the new values of the polarized words.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedSummedProof

open Matrix Complex MeasureTheory
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.ContractingWords
open BlockBand.SourceProcess.Stochastic BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.SourceProcess.CompleteSourceGap BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionLaws
open scoped Matrix.Norms.L2Operator

variable {W : ℕ} {c : Type} [Fintype c]

/-- The Gram pair after one fresh layer: `gramPair P (NᴴV)`. -/
def layerGram (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (V : Matrix (Fin 2 × Fin W) c ℂ) (y : LayerSample W .oneBlockOnePort) : GramState c :=
  gramPair (nearProjection W) ((freshTransport b E XX y)ᴴ * V)

/-- The four contracting separators, as a finset. -/
def contrSepSet : Finset Separator := {.projS, .sStarProj, .projSProj, .projSStarProj}

/-- **The contracting Gram coordinates** `Σ_σ Σ_{x,y} ‖(VᴴσV)_{xy}‖`. -/
def contrGram (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (V : Matrix (Fin 2 × Fin W) c ℂ) : ℝ :=
  ∑ σ ∈ contrSepSet, ∑ x, ∑ y, ‖(Vᴴ * sepOf b E XX σ * V) x y‖

theorem contrGram_nonneg (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (V : Matrix (Fin 2 × Fin W) c ℂ) : 0 ≤ contrGram b E XX V := by
  unfold contrGram; positivity

/-- `‖Tr(LY)‖ ≤ (Σ_{ij}‖L_{ij}‖)‖Y‖`. -/
theorem norm_trace_mul_le {ι : Type} [Fintype ι] [DecidableEq ι] (L Y : Matrix ι ι ℂ) :
    ‖(L * Y).trace‖ ≤ (∑ i, ∑ j, ‖L i j‖) * ‖Y‖ := by
  simp only [Matrix.trace, diag_apply, mul_apply, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun j _ => ?_))
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (FullSource.norm_entry_le_op Y j i) (norm_nonneg _)

theorem I_pow_mul_star (k : ℕ) : I ^ k * star (I ^ k) = 1 := by
  rw [star_pow, ← mul_pow, Complex.star_def, Complex.conj_I]; simp

theorem rk1_polVec {ι : Type} [Fintype ι] (v w : ι → ℂ) (k : Fin 4) :
    rk1 (polVec v w k) = vecMulVec v (star v) + star (I ^ (k : ℕ)) • vecMulVec v (star w) +
      (I ^ (k : ℕ)) • vecMulVec w (star v) + vecMulVec w (star w) := by
  have h := I_pow_mul_star (k : ℕ)
  ext x y
  simp only [rk1, polVec, vecMulVec_apply, Pi.add_apply, Pi.smul_apply, Pi.star_apply, star_add,
    smul_eq_mul, star_mul', Matrix.add_apply, Matrix.smul_apply]
  linear_combination (star (w y) * w x) * h

/-- `‖Tr(uu*T)‖ ≤ 4 Σ_{x,y}‖(VᴴTV)_{xy}‖` for `u = v_b + iᵏ v_a`. -/
theorem norm_trace_rk1_le {ι : Type} [Fintype ι] (V : Matrix ι c ℂ) (T : Matrix ι ι ℂ) (a b : c)
    (k : Fin 4) :
    ‖(rk1 (polVec (colOf V b) (colOf V a) k) * T).trace‖ ≤
      4 * ∑ x, ∑ y, ‖(Vᴴ * T * V) x y‖ := by
  have hS : ∀ x y, ‖(Vᴴ * T * V) x y‖ ≤ ∑ x, ∑ y, ‖(Vᴴ * T * V) x y‖ := fun x y =>
    (Finset.single_le_sum (f := fun y => ‖(Vᴴ * T * V) x y‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ y)).trans (Finset.single_le_sum (f := fun x => ∑ y, ‖(Vᴴ * T * V) x y‖)
        (fun _ _ => by positivity) (Finset.mem_univ x))
  have hn : ‖I ^ (k : ℕ)‖ = 1 := by simp [norm_pow]
  have hn' : ‖star (I ^ (k : ℕ))‖ = 1 := by rw [norm_star, hn]
  rw [rk1_polVec, Matrix.add_mul, Matrix.add_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul,
    trace_add, trace_add, trace_add, trace_smul, trace_smul]
  have tc : ∀ x y : c, (vecMulVec (colOf V y) (star (colOf V x)) * T).trace = (Vᴴ * T * V) x y :=
    fun x y => trace_col V T x y
  simp only [tc, smul_eq_mul]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add_left ((norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)) _).trans ?_
  rw [norm_mul, norm_mul, hn, hn', one_mul, one_mul]
  linarith [hS b b, hS a b, hS b a, hS a a]

/-- The new value of a polarized one-letter tag word (no injection). -/
theorem layerNew_tag (b E : ℝ) {nT nI : ℕ}
    (A : TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (q : Fin nI → ℝ → ℝ) (j : ℕ)
    (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (t : Fin nT) (σ : Fin 2)
    (y : LayerSample W .oneBlockOnePort) :
    layerNew b E A (injCoef q W j) XX [(.tag t, gramSep σ)] y =
      ((freshTransport b E XX y)ᴴ * A (.tag t) * freshTransport b E XX y *
        sepOf b E XX (gramSep σ)).trace := by
  have hs : sepOf b E (freshTwoPortSchur E XX y) (gramSep σ) = sepOf b E XX (gramSep σ) := by
    unfold gramSep; split_ifs <;> rfl
  simp [layerNew, newWord, injCoef, hs]

theorem trace_conj_cycle {ι : Type} [Fintype ι] (N L T : Matrix ι ι ℂ) :
    (Nᴴ * L * N * T).trace = (L * (N * T * Nᴴ)).trace := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- The new Gram coordinate is the polarized sum of the new word values. -/
theorem sum_new [DecidableEq c] (V : Matrix (Fin 2 × Fin W) c ℂ) (b E : ℝ)
    (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (y : LayerSample W .oneBlockOnePort)
    (e : Fin 2 × c × c) :
    ∑ k, polCoef k * ((freshTransport b E XX y)ᴴ * entryLetter V e k * freshTransport b E XX y *
        sepOf b E XX (gramSep e.1)).trace = gramEntry e (layerGram b E XX V y) := by
  simp only [trace_conj_cycle, sum_entry]
  rw [layerGram, gramEntry_sep _ (sepOf b E XX) rfl rfl e]
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]

/-- The old Gram coordinate is the polarized sum of the old word values. -/
theorem sum_old [DecidableEq c] (V : Matrix (Fin 2 × Fin W) c ℂ) (b E : ℝ)
    (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (J : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (e e' : Fin 2 × c × c) :
    ∑ k, polCoef k * coreProd (gramLetters J V e e') (sepOf b E XX) [[(tagL k, gramSep e.1)]] =
      gramEntry e (gramPair (nearProjection W) V) := by
  simp only [coreProd_one, gramLetters_tagL, sum_entry]
  rw [gramEntry_sep _ (sepOf b E XX) rfl rfl e]

end BlockBand.SourceProcess.ClosedSummedProof
