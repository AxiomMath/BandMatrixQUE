module
public import BlockBand.SourceProcess.Stochastic.SourceAlgebra.GramBrackets
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Gram characteristics in the coordinates of the Gram martingale problem

Restates the Gram drift and brackets in the coordinates `gramEntry`/`gramDriftEntry`/
`gramCovEntry`: at every frame satisfying the two-projection constraint, the product-rule drift
and the complex-bilinear brackets of the Gram noise `gramNoise` are exactly the target Gram
coefficients. Pure algebra:
no stochastic process is constructed here.
-/

namespace BlockBand.SourceProcess.Stochastic.SourceAlgebra
open Matrix BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic

variable {ι c : Type*} [Fintype ι] [DecidableEq ι] [Fintype c]

/-- The product-rule Gram drift `(drift M, drift B)`. -/
def gramDrift (D0 : ℝ) (Naux : ℕ) (P : Matrix ι ι ℂ) (D : Matrix c c ℂ) (V : Matrix ι c ℂ) :
    Matrix c c ℂ × Matrix c c ℂ :=
  (quadDrift D0 Naux P 1 D V, quadDrift D0 Naux P P D V)

/-- **The Gram drift** under the constraint: `gramDrift = (0, -(D₀/2) g B)`. -/
theorem gramDrift_eq {D0 : ℝ} (hD0 : 0 ≤ D0) {Naux : ℕ} {P : Matrix ι ι ℂ}
    {D : Matrix c c ℂ} {V : Matrix ι c ℂ} (hP : IsNearProjection P Naux)
    (hV : TwoProjection P D V) :
    gramDrift D0 Naux P D V =
      (0, (-(((D0 / 2 : ℝ) : ℂ) * gramScalar D (sourceGram V))) • nearGram P V) := by
  rw [gramDrift, gram_drift_M hD0 hP hV, gram_drift_B hD0 hP hV]

/-- Drift coordinates match `gramDriftEntry`. -/
theorem gramDrift_entry {D0 : ℝ} (hD0 : 0 ≤ D0) {Naux : ℕ} {P : Matrix ι ι ℂ}
    {D : Matrix c c ℂ} {V : Matrix ι c ℂ} (hP : IsNearProjection P Naux)
    (hV : TwoProjection P D V) (e : Fin 2 × c × c) :
    gramEntry e (gramDrift D0 Naux P D V) = gramDriftEntry D0 D e (gramPair P V) := by
  rw [gramDrift_eq hD0 hP hV]
  obtain ⟨r, i, j⟩ := e
  fin_cases r <;> simp [gramEntry, gramDriftEntry, gramPair]

/-- **The Gram covariance** in martingale-problem coordinates: for all `e, e'`,
`∑_a dG_e dG_e' = gramCovEntry D0 D e e' (M, B)` under the constraint. -/
theorem gramNoise_cov_entry {D0 : ℝ} (hD0 : 0 ≤ D0) {Naux : ℕ} {P : Matrix ι ι ℂ}
    {D : Matrix c c ℂ} {V : Matrix ι c ℂ} (hP : IsNearProjection P Naux) (hD : IsSignature D)
    (hV : TwoProjection P D V) (e e' : Fin 2 × c × c) :
    ∑ a, gramEntry e (gramNoise D0 P D a V) * gramEntry e' (gramNoise D0 P D a V) =
      gramCovEntry D0 D e e' (gramPair P V) := by
  obtain ⟨r, i, j⟩ := e
  obtain ⟨r', k, l⟩ := e'
  fin_cases r <;> fin_cases r' <;> simp only [gramEntry, gramCovEntry, gramPair] <;>
    simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte, Fin.mk_one, one_ne_zero]
  · exact gram_bracket_MM hD0 hP hV i j k l
  · exact gram_bracket_MB hD0 hP hD hV i j k l
  · simp_rw [mul_comm ((gramNoise D0 P D _ V).2 i j)]
    exact gram_bracket_MB hD0 hP hD hV k l i j
  · exact gram_bracket_BB hD0 hP hV i j k l

end BlockBand.SourceProcess.Stochastic.SourceAlgebra
