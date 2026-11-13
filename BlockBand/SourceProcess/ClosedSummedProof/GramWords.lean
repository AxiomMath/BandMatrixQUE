module

public import BlockBand.SourceProcess.ClosedSummedProof.Polar
public import BlockBand.SourceProcess.ContractingWords.LayerPins

/-!
# One-letter trace words: their drift, covariance and contracting products

For one-letter words `[(ℓ, σ)]` the word generator and covariance rules (`wordDrift`, `wordCov`)
and the contracting products of `ContractingWords.LayerPins` (`contrDrift`, `contrCov`) evaluate to
explicit traces (any letter matrices `A`, separators `T`):

* `eval_wordDrift_one`: `drift[(ℓ,σ)] = -(D₀/2)·(½Tr(JJ))·1_{σ=P}·Tr(A_ℓ T_σ)`;
* `eval_wordCov_one`: `cov([(ℓ,σ)],[(ℓ',σ')]) = (D₀/2)[2Tr(A_ℓPA_ℓ'P) + Tr(A_ℓPA_ℓ'T_σ'JT_σ) +
  Tr(A_ℓT_σJT_σ'A_ℓ'P)]`;
* `contrDrift_one`, `contrCov_one`: the error sums of `LayerDrift`/`LayerCov`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedSummedProof

open Matrix
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.ContractingWords

variable {W nT nI : ℕ} (A : TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
  (T : Separator → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)

theorem coreProd_one (ℓ : TraceLetter nT nI) (σ : Separator) :
    coreProd A T [[(ℓ, σ)]] = (A ℓ * T σ).trace := by
  simp [coreProd, matWord, letWord]

theorem eval_wordDrift_one (D0 : ℝ) (ℓ : TraceLetter nT nI) (σ : Separator) :
    MvPolynomial.eval (fun v => coreProd A T [v]) (wordDrift D0 [(ℓ, σ)]) =
      -(((D0 / 2 : ℝ) : ℂ) * ((1 / 2 : ℂ) * (A .current * T .id * (A .current * T .id)).trace) *
        (if σ = .proj then 1 else 0) * (A ℓ * T σ).trace) := by
  have h : Finset.Ioo 0 1 = (∅ : Finset ℕ) := by decide
  simp only [wordDrift, gPoly, List.length_singleton, Finset.range_one, Finset.sum_singleton, h,
    Finset.sum_empty, add_zero, map_neg, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, wv]
  simp only [coreProd, matWord, letWord, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, Matrix.mul_one, List.countP_cons, List.countP_nil]
  by_cases hσ : σ = .proj <;> simp [hσ]

theorem setLastSep_one (ℓ : TraceLetter nT nI) (σ τ : Separator) :
    setLastSep [(ℓ, σ)] τ = [(ℓ, τ)] := rfl

theorem eval_wordCov_one (D0 : ℝ) (ℓ ℓ' : TraceLetter nT nI) (σ σ' : Separator) :
    MvPolynomial.eval (fun v => coreProd A T [v]) (wordCov D0 [(ℓ, σ)] [(ℓ', σ')]) =
      ((D0 / 2 : ℝ) : ℂ) * ((A ℓ * T .proj * (A ℓ' * T .proj)).trace +
          (A ℓ * T .proj * (A ℓ' * T σ' * (A .current * T σ))).trace +
        ((A ℓ * T .proj * (A ℓ' * T .proj)).trace +
          (A ℓ * T σ * (A .current * T σ' * (A ℓ' * T .proj))).trace)) := by
  simp only [wordCov, crossTerm, List.length_singleton, Finset.range_one, Finset.sum_singleton,
    List.rotate_singleton, setLastSep_one, sepAt, List.getD_cons_zero,
    List.cons_append, List.nil_append, map_mul, map_add, MvPolynomial.eval_C,
    MvPolynomial.eval_X, wv]
  simp only [coreProd, matWord, letWord, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]

/-- The contracting error sum of `LayerDrift` for a one-letter word. -/
theorem contrDrift_one (ℓ : TraceLetter nT nI) (σ : Separator) :
    ((contrDrift [(ℓ, σ)]).map fun Zs => ‖coreProd A T Zs‖).sum =
      ‖(A ℓ * T .projS).trace‖ + (‖(A ℓ * T .sStarProj).trace‖ +
        (‖(A ℓ * T .projSProj).trace‖ + ‖(A ℓ * T .projSStarProj).trace‖)) := by
  simp [contrDrift, contrOne, contrTwo, contrSeps, setSepAt, coreProd, matWord, letWord]

/-- The contracting error sum of `LayerCov` for two one-letter words. -/
theorem contrCov_one (ℓ ℓ' : TraceLetter nT nI) (σ σ' : Separator) :
    ((contrCov [(ℓ, σ)] [(ℓ', σ')]).map fun Zs => ‖coreProd A T Zs‖).sum =
      ∑ τ ∈ ({.projS, .sStarProj, .projSProj, .projSStarProj} : Finset Separator),
        ∑ τ' ∈ ({.projS, .sStarProj, .projSProj, .projSStarProj} : Finset Separator),
          ‖(A ℓ * T τ * (A ℓ' * T τ')).trace‖ := by
  simp [contrCov, contrSeps, setLastSep_one, coreProd, matWord, letWord]
  ring

end BlockBand.SourceProcess.ClosedSummedProof

