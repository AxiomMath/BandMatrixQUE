module

public import BlockBand.SourceProcess.CoupledFrames.CoupledModel2

/-!
# The canonical cutoff frame

The canonical frame `cutFrame` is the extended frame times `Lcur` (`cutFrame_eq`), and its probe
columns vanish (`cutFrame_col`); the source signature has zero probe rows and columns
(`srcSignature_col`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CoupledFrames
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix Finset
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.ModelExist
open BlockBand.SourceProcess.BornUnique BlockBand.SourceProcess.SourceProcessLaw
open BlockBand.SourceProcess.Stochastic.GramUniqueness BlockBand.SourceProcess.CutoffLimit

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

/-- The canonical frame is the extended frame times `Lcur`. -/
theorem cutFrame_eq {K R : ℕ} {Ω π : Type*} [DecidableEq π] (tseq : Ω → ℕ → ℝ) (h : ℝ) :
    cutFrame π (embK K R) tseq h = fun x => extFrame K R (tseq x) h * lcur K R π :=
  funext fun x => (extFrame_mul_lcur K R π (tseq x) h).symm

theorem srcSignature_col {K : ℕ} {π : Type*} [DecidableEq π] (i : π) (j : SrcCol K π) :
    srcSignature K π (Sum.inr i) j = 0 ∧ srcSignature K π j (Sum.inr i) = 0 := by
  constructor <;> simp only [srcSignature, diagonal_apply] <;> split_ifs <;> simp_all

theorem cutFrame_col {K R : ℕ} {Ω π : Type*} [Fintype π] [DecidableEq π] (tseq : Ω → ℕ → ℝ)
    (h : ℝ) (x : Ω) (r : Amb K R) (i : π) : cutFrame π (embK K R) tseq h x r (Sum.inr i) = 0 := by
  simp [cutFrame, Matrix.mul_apply, initialFrame]

end BlockBand.SourceProcess.CoupledFrames
