module

public import BlockBand.Internal.Contracts.TransmissionLaws

/-!
# The physical sampled source transform

The paper writes an interval source as `Q(q) = Σ_j (q_j/W) Q_j`, `Q_j = Y_{n;j}/W`, `m = Σ_j q_j/W`
(in Lean `intervalSource`: the block of birth index `k` carries `q((k+1)/W)`), samples `M`
independent tag locations with probabilities `q_j/(Wm)` and injects at each an independent
Gaussian vector with that tag covariance and weight `m/M`; `\widehat Q_M` is the sum of their final
rank-one matrices. Here the Gaussian vector with covariance `Q_k` is
`W^{-1/2} 𝒰_n* ι_k g`, `g ~ CN(0, I_W)` on block `k` (`E gg* = I`), so the rank-one matrix has
mean `(m/M) Q_k` and `E \widehat Q_M = Q(q)` given the path. A zero-mass test gives zero matrices.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SourceProcessLaw

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.TransmissionPath
open scoped ENNReal NNReal Matrix

/-- `ι_k g`: the vector `g ∈ ℂ^W` placed on the block of birth index `k` of the path of length `n`
(position `n-1-k`, as in `tagProjection`). -/
def tagVector (W n k : ℕ) (g : Fin W → ℂ) : Fin n × Fin W → ℂ :=
  fun x => if k < n ∧ x.1.val = n - 1 - k then g x.2 else 0

/-- The tag mass `m = Σ_j q_j/W` of a test on the path of length `n`. -/
def gridMass (W n : ℕ) (q : ℝ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, q (((k + 1 : ℕ) : ℝ) / W) / W

/-- Law of one sampled tag location: birth index `k < n` with probability `q_k/(Wm)`; a
zero-mass test samples the index `0` (its injection has weight `0`). -/
def tagSampleLaw (W n : ℕ) (q : ℝ → ℝ) : Measure ℕ :=
  if 0 < gridMass W n q then
    ∑ k ∈ Finset.range n,
      ENNReal.ofReal (q (((k + 1 : ℕ) : ℝ) / W) / (W * gridMass W n q)) • Measure.dirac k
  else Measure.dirac 0

/-- The sampled source `\widehat Q_M = Σ_{l<M} (m/(MW)) v_l v_l*`, `v_l = 𝒰_n* ι_{k_l} g_l`. -/
def sampledSource (b E : ℝ) (W n : ℕ) (q : ℝ → ℝ) (M : ℕ) (k : Fin M → ℕ)
    (g : Fin M → Fin W → ℂ) (ω : GrowthPath W) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  ∑ l, ((gridMass W n q / (M * W) : ℝ) : ℂ) •
    Matrix.vecMulVec ((boundaryToInterior b E W n ω)ᴴ *ᵥ tagVector W n (k l) (g l))
      (star ((boundaryToInterior b E W n ω)ᴴ *ᵥ tagVector W n (k l) (g l)))

/-- Joint sample of the path, the sampled tag indices `k_{a,l}` and the injected Gaussians
`g_{a,l}`, `(a, l) ∈ Fin p × Fin M`. -/
abbrev SampledPath (W p M : ℕ) :=
  GrowthPath W × ((Fin p × Fin M → ℕ) × (Fin p × Fin M → Fin W → ℂ))

/-- Its law: the path, independent i.i.d. tag indices (law `tagSampleLaw` of test `a`) and
independent `g_{a,l} ~ CN(0, I_W)`. -/
def sampledPathLaw (b : ℝ) (W n : ℕ) {p : ℕ} (q : Fin p → ℝ → ℝ) (M : ℕ) :
    Measure (SampledPath W p M) :=
  (growthPathLaw W b).prod ((Measure.pi fun i : Fin p × Fin M => tagSampleLaw W n (q i.1)).prod
    (Measure.pi fun _ : Fin p × Fin M => circularVectorLaw (Fin W)))

/-- **The physical sampled transform** `E Π_j det(I + Σ_a a_{j,a} \widehat Q_{M,a})⁻¹` of the
physical path of length `⌊WT⌋` (the left side of the positive source sampling bound; common
samples for all factors `j`). -/
def sampledPhysTransform (b E T : ℝ) {p J : ℕ} (q : Fin p → ℝ → ℝ) (a : Fin J → Fin p → ℝ)
    (M W : ℕ) : ℝ :=
  ∫ x, ∏ j, (((1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) +
      ∑ i, (a j i : ℂ) • sampledSource b E W ⌊(W : ℝ) * T⌋₊ (q i) M (fun l => x.2.1 (i, l))
        (fun l => x.2.2 (i, l)) x.1).det⁻¹).re
    ∂sampledPathLaw b W ⌊(W : ℝ) * T⌋₊ q M

end BlockBand.SourceProcess.SourceProcessLaw
