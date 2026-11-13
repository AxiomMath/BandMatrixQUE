module

public import BlockBand.SourceProcess.ClosedIdent.Defs
public import BlockBand.SourceProcess.Sampling.Mix

/-!
# The closed physical frame and Gram coordinates at a fixed cap

At the final length `n = ⌊WT⌋`, with the closing map `C(z) = physClosingMap` (omitted channels
`t_i ≤ h²` chosen at `⌊Ws⌋`, closed by the phase `z = e^{iθ}`), the sampled probe `(a, l)` (tag
index `k_{a,l}`, Gaussian `g_{a,l}`) has the closed column
`u_{a,l} = √(m_a/(MW)) · C(z)ᴴ 𝒰_nᴴ ι_{k_{a,l}} g_{a,l}` (`closedProbeCol`, `m_a = gridMass`): its
rank-one matrix `u u*` is the closed form `C(z)ᴴ (m_a/(MW)) v v* C(z)` of the sampled injection
`sampledSource`. The closed frame (`closedFrame`) has these probe columns and
current columns `Vcur` on `Fin K × Fin 2`; the closed Gram coordinates are
`closedGram = gramPair P V` with the near-port projection `P` (`Fin 2` port `0` = near).

**Proved** (`closedIntegrand_eq_sampledTransformValue`, `cappedClosedTransform_eq_gram`): for every
current frame `Vcur`, the closed integrand is `sampledTransformValue a` of the closed Gram
state (Sylvester `det(1 + AB) = det(1 + BA)`), so
`cappedClosedTransform = E[1_{cap} · sampledTransformValue a (closedGram)]`: the capped closed
transform is the expectation of the model observable of `IsFiniteSourceModel` evaluated on the
closed physical Gram coordinates. The transform sees only the probe block, so the identity holds
whatever current columns are used; their definition (the canonical two-projection basis of the
retained far modes, transported along the path) matters only for the generator estimates.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosedLimit

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionLaws BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess BlockBand.SourceProcess.SourceProcessLaw BlockBand.SourceProcess.Closing
open BlockBand.SourceProcess.ClosingAux BlockBand.SourceProcess.ClosedIdent
open scoped ComplexConjugate

/-!
## Pure algebra
-/

section Algebra

variable {ι π : Type*} [Fintype π] [DecidableEq π]

/-- `Σ_i d_i u_i u_i* = U diag(d) Uᴴ` for the matrix `U` with columns `u_i`. -/
theorem sum_smul_vecMulVec_eq (w : π → ι → ℂ) (d : π → ℂ) :
    ∑ i, d i • vecMulVec (w i) (star (w i)) =
      (Matrix.of fun z i => w i z) * (diagonal d * (Matrix.of fun z i => w i z)ᴴ) := by
  ext z z'
  rw [Matrix.sum_apply, mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.smul_apply, vecMulVec_apply, diagonal_mul, conjTranspose_apply, of_apply, of_apply,
    Pi.star_apply, smul_eq_mul]
  ring

omit [Fintype π] [DecidableEq π] in
/-- `r u u* = (√r u)(√r u)*` for `r ≥ 0`. -/
theorem smul_vecMulVec_sqrt {r : ℝ} (hr : 0 ≤ r) (u : ι → ℂ) :
    ((r : ℝ) : ℂ) • vecMulVec u (star u) =
      vecMulVec (((Real.sqrt r : ℝ) : ℂ) • u) (star (((Real.sqrt r : ℝ) : ℂ) • u)) := by
  ext z z'
  simp only [vecMulVec_apply, Pi.star_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply,
    star_mul', Complex.star_def, Complex.conj_ofReal]
  rw [show (r : ℂ) = ((Real.sqrt r : ℝ) : ℂ) * ((Real.sqrt r : ℝ) : ℂ) by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hr]]
  ring

omit [Fintype π] [DecidableEq π] in
/-- Conjugating a rank-one matrix. -/
theorem conj_vecMulVec [Fintype ι] {κ : Type*} [Fintype κ] (C : Matrix κ ι ℂ) (v : κ → ℂ) :
    Cᴴ * vecMulVec v (star v) * C = vecMulVec (Cᴴ *ᵥ v) (star (Cᴴ *ᵥ v)) := by
  rw [mul_vecMulVec, vecMulVec_mul, star_mulVec, conjTranspose_conjTranspose]

end Algebra

/-!
## The closed frame
-/

variable {W : ℕ}

/-- The near-port projection on the two-port boundary space (`Fin 2` port `0` = near). -/
def nearPortProj (W : ℕ) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  diagonal fun z => if z.1 = 0 then 1 else 0

/-- The weight `m_a/(MW)` of one sampled probe of test `a` at the final length. -/
def probeWeight (T : ℝ) {p : ℕ} (q : Fin p → ℝ → ℝ) (M W : ℕ) (i : Fin p) : ℝ :=
  gridMass W ⌊(W : ℝ) * T⌋₊ (q i) / (M * W)

/-- The physical (unclosed) sampled vector `v = 𝒰_nᴴ ι_k g` of probe `(a, l)`. -/
def probeVec (b E T : ℝ) {p M : ℕ} (W : ℕ) (x : SampledPath W p M) (il : Fin p × Fin M) :
    Fin 2 × Fin W → ℂ :=
  (boundaryToInterior b E W ⌊(W : ℝ) * T⌋₊ x.1)ᴴ *ᵥ
    tagVector W ⌊(W : ℝ) * T⌋₊ (x.2.1 il) (x.2.2 il)

/-- **The closed probe column** `√(m_a/(MW)) C(z)ᴴ v_{a,l}`. -/
def closedProbeCol (b E s T h : ℝ) {p M : ℕ} (q : Fin p → ℝ → ℝ) (W : ℕ)
    (y : SampledPath W p M × ℝ) (il : Fin p × Fin M) : Fin 2 × Fin W → ℂ :=
  ((Real.sqrt (probeWeight T q M W il.1) : ℝ) : ℂ) •
    ((physClosingMap b E s T h W y.1.1 (phase y.2))ᴴ *ᵥ probeVec b E T W y.1 il)

/-- The closed probe frame (columns `closedProbeCol`). -/
def closedProbeFrame (b E s T h : ℝ) {p M : ℕ} (q : Fin p → ℝ → ℝ) (W : ℕ)
    (y : SampledPath W p M × ℝ) : Matrix (Fin 2 × Fin W) (Fin p × Fin M) ℂ :=
  Matrix.of fun z il => closedProbeCol b E s T h q W y il z

/-- **The closed frame**: current columns `Vcur`, closed probe columns. -/
def closedFrame (b E s T h : ℝ) {p K M : ℕ} (q : Fin p → ℝ → ℝ) (W : ℕ)
    (Vcur : Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (y : SampledPath W p M × ℝ) :
    Matrix (Fin 2 × Fin W) (SrcCol K (Fin p × Fin M)) ℂ :=
  Matrix.of fun z col => Sum.elim (fun k => Vcur z k) (fun il => closedProbeFrame b E s T h q W y z il)
    col

/-- **The closed Gram coordinates** `(VᴴV, VᴴPV)` of the closed frame. -/
def closedGram (b E s T h : ℝ) {p K M : ℕ} (q : Fin p → ℝ → ℝ) (W : ℕ)
    (Vcur : Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (y : SampledPath W p M × ℝ) :
    GramState (SrcCol K (Fin p × Fin M)) :=
  gramPair (nearPortProj W) (closedFrame b E s T h q W Vcur y)

theorem probeBlock_closedGram (b E s T h : ℝ) {p K M : ℕ} (q : Fin p → ℝ → ℝ) (W : ℕ)
    (Vcur : Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (y : SampledPath W p M × ℝ) :
    probeBlock (closedGram b E s T h q W Vcur y).1 =
      (closedProbeFrame b E s T h q W y)ᴴ * closedProbeFrame b E s T h q W y := by
  ext i j
  simp [probeBlock, closedGram, gramPair, sourceGram, mul_apply, closedFrame, conjTranspose_apply]

/-- The closed sampled source `C(z)ᴴ (Σ_a a_{j,a} \widehat Q_{M,a}) C(z)` is
`U diag(a_j) Uᴴ` for the closed probe frame `U` (`q ≥ 0`). -/
theorem closedSource_eq (b E s T h : ℝ) {p J M : ℕ} {q : Fin p → ℝ → ℝ} (hq : ∀ i x, 0 ≤ q i x)
    (a : Fin J → Fin p → ℝ) (W : ℕ) (y : SampledPath W p M × ℝ) (j : Fin J) :
    (physClosingMap b E s T h W y.1.1 (phase y.2))ᴴ *
        (∑ i, (a j i : ℂ) • sampledSource b E W ⌊(W : ℝ) * T⌋₊ (q i) M
          (fun l => y.1.2.1 (i, l)) (fun l => y.1.2.2 (i, l)) y.1.1) *
        physClosingMap b E s T h W y.1.1 (phase y.2) =
      closedProbeFrame b E s T h q W y *
        (diagonal (fun il : Fin p × Fin M => (a j il.1 : ℂ)) *
          (closedProbeFrame b E s T h q W y)ᴴ) := by
  rw [closedProbeFrame, ← sum_smul_vecMulVec_eq, Finset.mul_sum, Finset.sum_mul,
    ← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, sampledSource, Finset.mul_sum, Finset.sum_mul,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, conj_vecMulVec]
  have hw : 0 ≤ probeWeight T q M W i :=
    div_nonneg (Sampling.gridMass_nonneg W _ (hq i)) (by positivity)
  exact congrArg _ (smul_vecMulVec_sqrt hw _)

/-- **The closed integrand is the model observable of the closed Gram coordinates**
(every current frame `Vcur`, `q ≥ 0`). -/
theorem closedIntegrand_eq_sampledTransformValue (b E s T h : ℝ) {p J K M : ℕ}
    {q : Fin p → ℝ → ℝ} (hq : ∀ i x, 0 ≤ q i x) (a : Fin J → Fin p → ℝ) (W : ℕ)
    (Vcur : Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (y : SampledPath W p M × ℝ) :
    closedIntegrand b E s T h q a M W y =
      sampledTransformValue a (closedGram b E s T h q W Vcur y) := by
  unfold closedIntegrand sampledTransformValue
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [closedSource_eq b E s T h hq a W y j, det_one_add_mul_comm, Matrix.mul_assoc,
    probeBlock_closedGram]

/-- **The capped closed transform as an expectation over the closed Gram coordinates.** -/
theorem cappedClosedTransform_eq_gram (b E s T h : ℝ) {p J K M : ℕ} {q : Fin p → ℝ → ℝ}
    (hq : ∀ i x, 0 ≤ q i x) (a : Fin J → Fin p → ℝ) (W : ℕ)
    (Vcur : SampledPath W p M × ℝ → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) :
    cappedClosedTransform b E s T h q a K M W =
      ∫ y, (physCapEvent b E s h K W).indicator (fun _ => (1 : ℝ)) y.1.1 *
          sampledTransformValue a (closedGram b E s T h q W (Vcur y) y)
        ∂((sampledPathLaw b W ⌊(W : ℝ) * T⌋₊ q M).prod phaseLaw) := by
  unfold cappedClosedTransform
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  rw [closedIntegrand_eq_sampledTransformValue b E s T h hq a W (Vcur y) y]

end BlockBand.SourceProcess.ClosedLimit
