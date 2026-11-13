module
public import BlockBand.SourceProcess.Stochastic.GramUniqueness.GramGeneratorCoord
public import BlockBand.SourceProcess.Stochastic.MartingaleProblem
public import BlockBand.SourceProcess.Stochastic.SourceSDE.MatrixForms
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Real coordinates of the Gram martingale problem

The Gram pair `(M, B)` has the real coordinates `(Re, Im)` of its complex entries, indexed by
`gramRealIdx c = (Fin 2 × c × c) × Fin 2` and transported to `Fin (gramDim c)` (the coordinate
space of `IsMPSolutionOn`). `toGramReal`/`fromGramReal` are inverse
(`fromGramReal_toGramReal`). The real drift `gramRealDrift` and covariance `gramRealCov` are
read off from the Gram drift and from the bilinear/sesquilinear Gram brackets
(`gramCovEntry D0 𝖣 e e'`, `gramCovEntry D0 𝖣 e (gramSwap e')`), using
`Re z Re w = ½Re(zw + z w̄)`, `Re z Im w = ½Im(zw − z w̄)`, `Im z Re w = ½Im(zw + z w̄)`,
`Im z Im w = ½Re(z w̄ − zw)`.

`mpGenerator_gramReal`: the martingale-problem generator `mpGenerator` of `(gramRealDrift,
gramRealCov)` applied to `f ∘ fromGramReal` at `toGramReal G` is `gramGenerator D0 𝖣 f G`. With
`gramGenerator_rankBarrier` this is the rank barrier in the form used by the
Itô formula for martingale-problem solutions (`martingaleProblemIto_holds`).
-/

namespace BlockBand.SourceProcess.Stochastic.GramUniqueness
open Matrix Finset BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {c : Type*} [Fintype c] [DecidableEq c]

/-- Real Gram coordinates: complex coordinate `e` and `0 = Re`, `1 = Im`. -/
abbrev gramRealIdx (c : Type*) := (Fin 2 × c × c) × Fin 2

/-- Number of real Gram coordinates (`4 |c|²`). -/
abbrev gramDim (c : Type*) [Fintype c] : ℕ := Fintype.card (gramRealIdx c)

/-- Enumeration of the real Gram coordinates. -/
def gramRealEquiv (c : Type*) [Fintype c] : gramRealIdx c ≃ Fin (gramDim c) := Fintype.equivFin _

/-- Real part (`r = 0`) or imaginary part (`r = 1`). -/
def reIm (r : Fin 2) (z : ℂ) : ℝ := if r = 0 then z.re else z.im

/-- Real frame vector of the real coordinate `(e, r)`. -/
def gramFrame (q : gramRealIdx c) : Matrix c c ℂ × Matrix c c ℂ :=
  if q.2 = 0 then gramUnit q.1 else Complex.I • gramUnit q.1

/-- Real coordinates of a Gram pair. -/
def toGramReal (G : Matrix c c ℂ × Matrix c c ℂ) : Fin (gramDim c) → ℝ :=
  fun i => reIm ((gramRealEquiv c).symm i).2 (gramEntry ((gramRealEquiv c).symm i).1 G)

/-- Gram pair with given real coordinates, as a continuous linear map. -/
def fromGramReal :=
  SourceSDE.toCLM (F₁ := Fin (gramDim c) → ℝ) (F₂ := Matrix c c ℂ × Matrix c c ℂ)
    (∑ i, (LinearMap.proj i).smulRight (gramFrame ((gramRealEquiv c).symm i)))

theorem fromGramReal_apply (y : Fin (gramDim c) → ℝ) :
    fromGramReal y = ∑ i, y i • gramFrame ((gramRealEquiv c).symm i) := by
  simp [fromGramReal, SourceSDE.toCLM]

theorem fromGramReal_single (i : Fin (gramDim c)) :
    fromGramReal (Pi.single i 1) = gramFrame ((gramRealEquiv c).symm i) := by
  rw [fromGramReal_apply]
  simp [Pi.single_apply]

omit [DecidableEq c] in
/-- Sums over `Fin (gramDim c)` as sums over `(e, r)`. -/
theorem sum_gramReal {M : Type*} [AddCommMonoid M] (g : gramRealIdx c → M) :
    ∑ i, g ((gramRealEquiv c).symm i) = ∑ e, ∑ r : Fin 2, g (e, r) := by
  rw [Equiv.sum_comp (gramRealEquiv c).symm g, Fintype.sum_prod_type]

theorem fromGramReal_toGramReal (G : Matrix c c ℂ × Matrix c c ℂ) :
    fromGramReal (toGramReal G) = G := by
  rw [fromGramReal_apply]
  simp only [toGramReal]
  rw [sum_gramReal (fun q => reIm q.2 (gramEntry q.1 G) • gramFrame q)]
  conv_rhs => rw [gram_decomp G]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp [Fin.sum_univ_two, reIm, gramFrame]

/-- Real drift of the Gram martingale problem. -/
def gramRealDrift (D0 : ℝ) (D : Matrix c c ℂ) (y : Fin (gramDim c) → ℝ) : Fin (gramDim c) → ℝ :=
  toGramReal (gramDriftG D0 D (fromGramReal y))

/-- Real covariance between `(e, r)` and `(e', r')` from the brackets `Γ = dG_e dG_e'` and
`Γ' = dG_e conj(dG_e')`. -/
def realCovEntry (r r' : Fin 2) (Γ Γ' : ℂ) : ℝ :=
  if r = 0 then (if r' = 0 then (Γ + Γ').re / 2 else (Γ - Γ').im / 2)
  else (if r' = 0 then (Γ + Γ').im / 2 else (Γ' - Γ).re / 2)

/-- Real covariance of the Gram martingale problem. -/
def gramRealCov (D0 : ℝ) (D : Matrix c c ℂ) (y : Fin (gramDim c) → ℝ) :
    Matrix (Fin (gramDim c)) (Fin (gramDim c)) ℝ := fun i j =>
  realCovEntry ((gramRealEquiv c).symm i).2 ((gramRealEquiv c).symm j).2
    (gramCovEntry D0 D ((gramRealEquiv c).symm i).1 ((gramRealEquiv c).symm j).1 (fromGramReal y))
    (gramCovEntry D0 D ((gramRealEquiv c).symm i).1 (gramSwap ((gramRealEquiv c).symm j).1)
      (fromGramReal y))

section Generic
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- First derivative `Df(G)[v]` (elaborated with the normed structure of `F`). -/
def d1 (f : F → ℝ) (G v : F) : ℝ := fderiv ℝ f G v

/-- Second derivative `D²f(G)[v, w]`. -/
def d2 (f : F → ℝ) (G v w : F) : ℝ := fderiv ℝ (fderiv ℝ f) G v w

theorem fderiv_fderiv_clm_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] F) : fderiv ℝ (fderiv ℝ L) = 0 := by
  have h : fderiv ℝ L = fun _ => L := funext fun _ => ContinuousLinearMap.fderiv L
  rw [h]
  funext x
  exact fderiv_const_apply L

end Generic

/-- **The martingale-problem generator in real Gram coordinates is the Gram generator.** -/
theorem mpGenerator_gramReal (D0 : ℝ) (D : Matrix c c ℂ) {f : Matrix c c ℂ × Matrix c c ℂ → ℝ}
    (hf : ContDiff ℝ 2 f) (G : Matrix c c ℂ × Matrix c c ℂ) :
    mpGenerator (gramRealDrift D0 D) (gramRealCov D0 D) (fun y => f (fromGramReal y))
        (toGramReal G) = gramGenerator D0 D f G := by
  have hL : ContDiff ℝ 2 (fromGramReal (c := c)) := fromGramReal.contDiff
  have h1 : ∀ v, fderiv ℝ (fun y => f (fromGramReal y)) (toGramReal G) v =
      d1 f G (fromGramReal v) := fun v => by
    rw [fderiv_comp_apply' (hf.differentiable (by norm_num) _) fromGramReal.differentiableAt,
      ContinuousLinearMap.fderiv, fromGramReal_toGramReal]
    rfl
  have h2 : ∀ v w, fderiv ℝ (fderiv ℝ (fun y => f (fromGramReal y))) (toGramReal G) v w =
      d2 f G (fromGramReal v) (fromGramReal w) := fun v w => by
    rw [fderiv_fderiv_comp_apply hf hL, ContinuousLinearMap.fderiv, fderiv_fderiv_clm_eq,
      fromGramReal_toGramReal]
    simp only [Pi.zero_apply, _root_.zero_apply, map_zero, add_zero]
    rfl
  unfold mpGenerator gramGenerator genCoord
  simp only [h1, h2, fromGramReal_single]
  congr 1
  · have e1 : ∑ i, gramRealDrift D0 D (toGramReal G) i *
          d1 f G (gramFrame ((gramRealEquiv c).symm i)) =
        d1 f G (fromGramReal (gramRealDrift D0 D (toGramReal G))) := by
      rw [fromGramReal_apply]
      simp only [d1, map_sum, map_smul, smul_eq_mul]
    rw [e1, gramRealDrift, fromGramReal_toGramReal, fromGramReal_toGramReal]
    rfl
  · congr 1
    simp only [gramRealCov, fromGramReal_toGramReal]
    have hin : ∀ i, ∑ j, realCovEntry ((gramRealEquiv c).symm i).2 ((gramRealEquiv c).symm j).2
        (gramCovEntry D0 D ((gramRealEquiv c).symm i).1 ((gramRealEquiv c).symm j).1 G)
        (gramCovEntry D0 D ((gramRealEquiv c).symm i).1 (gramSwap ((gramRealEquiv c).symm j).1) G) *
          d2 f G (gramFrame ((gramRealEquiv c).symm i)) (gramFrame ((gramRealEquiv c).symm j)) =
        ∑ e', ∑ r' : Fin 2, realCovEntry ((gramRealEquiv c).symm i).2 r'
          (gramCovEntry D0 D ((gramRealEquiv c).symm i).1 e' G)
          (gramCovEntry D0 D ((gramRealEquiv c).symm i).1 (gramSwap e') G) *
          d2 f G (gramFrame ((gramRealEquiv c).symm i)) (gramFrame (e', r')) := fun i =>
      sum_gramReal (fun q' => realCovEntry ((gramRealEquiv c).symm i).2 q'.2
        (gramCovEntry D0 D ((gramRealEquiv c).symm i).1 q'.1 G)
        (gramCovEntry D0 D ((gramRealEquiv c).symm i).1 (gramSwap q'.1) G) *
          d2 f G (gramFrame ((gramRealEquiv c).symm i)) (gramFrame q'))
    rw [Finset.sum_congr rfl fun i _ => hin i]
    rw [sum_gramReal (fun q => ∑ e', ∑ r' : Fin 2, realCovEntry q.2 r'
      (gramCovEntry D0 D q.1 e' G) (gramCovEntry D0 D q.1 (gramSwap e') G) *
        d2 f G (gramFrame q) (gramFrame (e', r')))]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e' _ => ?_
    simp only [Fin.sum_univ_two, realCovEntry, bracketForm, gramFrame, Fin.isValue, ↓reduceIte,
      one_ne_zero, Complex.add_re, Complex.sub_re, Complex.add_im, Complex.sub_im, d2]
    ring

end BlockBand.SourceProcess.Stochastic.GramUniqueness
