module
public import BlockBand.SourceProcess.Stochastic.FiniteSource
public import BlockBand.SourceProcess.Stochastic.SourceAlgebra.GramCharacteristics
public import BlockBand.SourceProcess.Stochastic.SourceSDE.MatrixForms
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# The Gram pair as a real-bilinear image of the frame

Matrices carry the Frobenius norm (local instance), with the Borel/metrizability bridges
`frobBorelSpace`, `matrixPseudoMetrizable`.

* `gramPairBil P : Matrix ι c ℂ →L[ℝ] Matrix ι c ℂ →L[ℝ] Matrix c c ℂ × Matrix c c ℂ`,
  `(V, W) ↦ (Vᴴ W, Vᴴ P W)`; on the diagonal it is `gramPair P` (`gramPairBil_self`).
* `gramPairBil_variation`: `β(H, V) + β(V, H) = (gramVariation V H, nearVariation P V H)`,
  so the product-rule diffusion along `sourceDiffusion` is `gramNoise` (`SourceAlgebra`).
* `gramPairBil_drift`: `β(b, V) + β(V, b) + ∑_a β(σ_a, σ_a) = gramDrift` for the source
  coefficients `b = sourceDrift`, `σ = sourceDiffusion` (every `V`, no constraint).
* `gramTargetDrift`: the target drift `(0, -(D₀/2) g(M) B)`; `continuous_gramTargetDrift`.
-/

namespace BlockBand.SourceProcess.Stochastic.GramChar
open Matrix BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.SourceAlgebra BlockBand.SourceProcess.Stochastic.SourceSDE

variable {ι c : Type*} [Fintype ι] [DecidableEq ι] [Fintype c]

/-- The target Gram drift `(0, -(D₀/2) g(M) B)` as a function of the frame. -/
def gramTargetDrift (D0 : ℝ) (P : Matrix ι ι ℂ) (D : Matrix c c ℂ) (V : Matrix ι c ℂ) :
    Matrix c c ℂ × Matrix c c ℂ :=
  (0, (-(((D0 / 2 : ℝ) : ℂ) * gramScalar D (sourceGram V))) • nearGram P V)

omit [DecidableEq ι] in
/-- Continuity of the target drift (product topology on matrices). -/
theorem continuous_gramTargetDrift (D0 : ℝ) (P : Matrix ι ι ℂ) (D : Matrix c c ℂ) :
    Continuous (gramTargetDrift D0 P D) := by
  have hM : Continuous fun V : Matrix ι c ℂ => sourceGram V :=
    continuous_id.matrix_conjTranspose.matrix_mul continuous_id
  have hB : Continuous fun V : Matrix ι c ℂ => nearGram P V :=
    (continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id
  have hg : Continuous fun V : Matrix ι c ℂ => gramScalar D (sourceGram V) :=
    continuous_const.mul ((((continuous_const.matrix_mul hM).matrix_mul
      continuous_const).matrix_mul hM).matrix_trace)
  exact continuous_const.prodMk ((continuous_const.mul hg).neg.smul hB)

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  frobBorelSpace matrixPseudoMetrizable

/-- `(V, W) ↦ (Vᴴ W, Vᴴ P W)` as a continuous real-bilinear map (Frobenius norms). -/
def gramPairBil (P : Matrix ι ι ℂ) :
    Matrix ι c ℂ →L[ℝ] Matrix ι c ℂ →L[ℝ] Matrix c c ℂ × Matrix c c ℂ :=
  toCLM₂ (F₁ := Matrix ι c ℂ) (F₂ := Matrix ι c ℂ) (F₃ := Matrix c c ℂ × Matrix c c ℂ)
    (LinearMap.mk₂ ℝ (fun V W => (Vᴴ * W, Vᴴ * P * W))
    (fun _ _ _ => by simp only [conjTranspose_add, Matrix.add_mul, Prod.mk_add_mk])
    (fun _ _ _ => by
      simp only [conjTranspose_smul, star_trivial, Matrix.smul_mul, Prod.smul_mk])
    (fun _ _ _ => by simp only [Matrix.mul_add, Prod.mk_add_mk])
    (fun _ _ _ => by simp only [Matrix.mul_smul, Prod.smul_mk]))

omit [DecidableEq ι] in
theorem gramPairBil_apply (P : Matrix ι ι ℂ) (V W : Matrix ι c ℂ) :
    gramPairBil P V W = (Vᴴ * W, Vᴴ * P * W) := rfl

omit [DecidableEq ι] in
theorem gramPairBil_self (P : Matrix ι ι ℂ) (V : Matrix ι c ℂ) :
    gramPairBil P V V = gramPair P V := rfl

omit [DecidableEq ι] in
/-- The first-order variation of the Gram pair. -/
theorem gramPairBil_variation (P : Matrix ι ι ℂ) (V H : Matrix ι c ℂ) :
    gramPairBil P H V + gramPairBil P V H = (gramVariation V H, nearVariation P V H) := rfl

/-- The product-rule diffusion along the source noise is `gramNoise`. -/
theorem gramPairBil_noise (D0 : ℝ) (P : Matrix ι ι ℂ) (D : Matrix c c ℂ) (a : SourceNoise ι)
    (V : Matrix ι c ℂ) :
    gramPairBil P (sourceDiffusion D0 P D a V) V + gramPairBil P V (sourceDiffusion D0 P D a V) =
      gramNoise D0 P D a V := rfl

/-- The product-rule drift of the Gram pair is `gramDrift` (every frame). -/
theorem gramPairBil_drift (D0 : ℝ) (Naux : ℕ) (P : Matrix ι ι ℂ) (D : Matrix c c ℂ)
    (V : Matrix ι c ℂ) :
    gramPairBil P (sourceDrift D0 Naux P V) V + gramPairBil P V (sourceDrift D0 Naux P V) +
        ∑ a, gramPairBil P (sourceDiffusion D0 P D a V) (sourceDiffusion D0 P D a V) =
      gramDrift D0 Naux P D V := by
  ext : 1
  · simp only [Prod.fst_add, Prod.fst_sum, gramPairBil_apply, gramDrift, quadDrift,
      quadVariation, Matrix.mul_one]
  · simp only [Prod.snd_add, Prod.snd_sum, gramPairBil_apply, gramDrift, quadDrift,
      quadVariation]

end BlockBand.SourceProcess.Stochastic.GramChar
