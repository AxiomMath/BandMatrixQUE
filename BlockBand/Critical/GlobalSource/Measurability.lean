module

public import BlockBand.Critical.GlobalSource.Statement
public import BlockBand.Coarea.GUELaw
public import BlockBand.Coarea.ProjectiveHaar
public import BlockBand.Layers.GinibreTails

/-!
# Global Gaussian source: measurability of the finite-width matrices

The finite-width matrices `𝒦_W = (ζ_a^* G ζ_c)` (`G = leadInverse b E W n`) and
`B_W = -η⁻¹ Im 𝒦_W` are Borel functions of the path and the Gaussian probes. Their laws are
therefore the push-forwards `(globalProbeLaw W n J b).map (globalProbeMatrix b E W n Q)`, and the
integrals in `IsGlobalProbeCriticalLimit` are integrals against these laws.

* `measurable_matrix_inv` — the totalized matrix inverse is Borel (`M⁻¹ = (det M)⁻¹ • adj M`);
* `measurable_pathMatrix`, `measurable_pathPortCoupling`, `measurable_pathAt`,
  `measurable_fullPathMatrix`, `measurable_leadInverse` — the path objects;
* `measurable_globalProbeMatrix`, `measurable_globalProbeGram`;
* `isProbabilityMeasure_globalProbeLaw`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.GlobalSource

open MeasureTheory
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.CriticalEntire
open scoped Matrix

/-- The totalized inverse of square complex matrices is Borel measurable. -/
theorem measurable_matrix_inv {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Measurable (fun M : Matrix ι ι ℂ => M⁻¹) := by
  have h : (fun M : Matrix ι ι ℂ => M⁻¹) = fun M => (M.det)⁻¹ • M.adjugate := by
    funext M
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  exact (continuous_id.matrix_det.measurable.inv).smul continuous_id.matrix_adjugate.measurable

/-- Conjugate transpose is Borel measurable. -/
theorem measurable_conjTranspose {ι κ : Type*} [Fintype ι] [Fintype κ] :
    Measurable (fun M : Matrix ι κ ℂ => Mᴴ) :=
  continuous_id.matrix_conjTranspose.measurable

/-- The path matrix is a Borel function of the path sample. -/
theorem measurable_pathMatrix {W r : ℕ} : Measurable (fun ω : PathSample W r => pathMatrix ω) := by
  refine Measurable.of_eval fun x => Measurable.of_eval fun y => ?_
  simp only [pathMatrix]
  split_ifs
  · exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp
      ((measurable_pi_apply _).comp measurable_fst))
  · exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp
      ((measurable_pi_apply _).comp (measurable_fst.comp measurable_snd)))
  · exact (continuous_star : Continuous (star : ℂ → ℂ)).measurable.comp
      ((measurable_pi_apply _).comp ((measurable_pi_apply _).comp
      ((measurable_pi_apply _).comp (measurable_fst.comp measurable_snd))))
  · exact measurable_const

/-- The port coupling is a Borel function of the path sample. -/
theorem measurable_pathPortCoupling {W r : ℕ} :
    Measurable (fun ω : PathSample W r => pathPortCoupling ω) := by
  refine Measurable.of_eval fun x => Measurable.of_eval fun y => ?_
  simp only [pathPortCoupling]
  split_ifs
  · exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp
      ((measurable_pi_apply _).comp (measurable_snd.comp measurable_snd)))
  · exact measurable_const

/-- The path of length `r` read from the grown sample is a Borel function of it. -/
theorem measurable_pathAt (W r : ℕ) : Measurable (pathAt W r) := by
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
  · exact Measurable.of_eval fun i => (measurable_pi_apply _).comp measurable_fst
  · exact Measurable.of_eval fun i =>
      measurable_conjTranspose.comp ((measurable_pi_apply _).comp measurable_snd)
  · refine Measurable.of_eval fun i => ?_
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Matrix.cons_val_zero]
      exact (measurable_pi_apply _).comp measurable_snd
    · refine Fin.cases ?_ (fun i => i.elim0) i
      simp only [Matrix.cons_val_succ, Matrix.cons_val_zero]
      exact (measurable_pi_apply _).comp measurable_snd

/-- The full path matrix with two matched leads is a Borel function of the grown sample. -/
theorem measurable_fullPathMatrix (b E : ℝ) (W n : ℕ) :
    Measurable (fullPathMatrix b E W n) := by
  have h1 := measurable_pathMatrix.comp (measurable_pathAt W n)
  have h2 := measurable_pathPortCoupling.comp (measurable_pathAt W n)
  refine Measurable.of_eval fun x => Measurable.of_eval fun y => ?_
  rcases x with x | x <;> rcases y with y | y
  · simp only [fullPathMatrix, Matrix.fromBlocks_apply₁₁]
    exact (((measurable_pi_apply y).comp ((measurable_pi_apply x).comp h1)).sub
      measurable_const)
  · simp only [fullPathMatrix, Matrix.fromBlocks_apply₁₂]
    exact (measurable_pi_apply y).comp ((measurable_pi_apply x).comp h2)
  · simp only [fullPathMatrix, Matrix.fromBlocks_apply₂₁]
    exact (measurable_pi_apply y).comp ((measurable_pi_apply x).comp
      (measurable_conjTranspose.comp h2))
  · simp only [fullPathMatrix, Matrix.fromBlocks_apply₂₂]
    exact measurable_const

/-- `leadInverse b E W n` is a Borel function of the grown sample. -/
theorem measurable_leadInverse (b E : ℝ) (W n : ℕ) : Measurable (leadInverse b E W n) := by
  have h := measurable_matrix_inv.comp (measurable_fullPathMatrix b E W (probePathLength n))
  refine Measurable.of_eval fun x => Measurable.of_eval fun y => ?_
  exact (measurable_pi_apply (Sum.inl y)).comp ((measurable_pi_apply (Sum.inl x)).comp h)

/-- `𝒦_W` is a Borel function of the path and the probes. -/
theorem measurable_globalProbeMatrix (b E : ℝ) (W n : ℕ) {J : ℕ} (Q : Fin J → C(Torus, ℝ)) :
    Measurable (globalProbeMatrix b E W n Q) := by
  have hG := measurable_leadInverse b E W n
  refine Measurable.of_eval fun a => Measurable.of_eval fun c => ?_
  simp only [globalProbeMatrix, dotProduct, Matrix.mulVec, globalProbeVector, Pi.star_apply]
  refine Finset.measurable_sum _ fun x _ => ?_
  refine Measurable.mul ?_ ?_
  · exact (continuous_star : Continuous (star : ℂ → ℂ)).measurable.comp (measurable_const.mul
      ((measurable_pi_apply x).comp ((measurable_pi_apply a).comp measurable_snd)))
  · refine Finset.measurable_sum _ fun y _ => ?_
    exact ((measurable_pi_apply y).comp ((measurable_pi_apply x).comp (hG.comp measurable_fst))).mul
      (measurable_const.mul
        ((measurable_pi_apply y).comp ((measurable_pi_apply c).comp measurable_snd)))

/-- `B_W` is a Borel function of the path and the probes. -/
theorem measurable_globalProbeGram (b E : ℝ) (W n : ℕ) {J : ℕ} (Q : Fin J → C(Torus, ℝ)) :
    Measurable (globalProbeGram b E W n Q) := by
  have hcont : Continuous (fun K : Matrix (Fin J) (Fin J) ℂ => probeGram b E K) := by
    have h : Continuous fun K : Matrix (Fin J) (Fin J) ℂ => K - Kᴴ :=
      continuous_id.sub continuous_id.matrix_conjTranspose
    unfold probeGram BlockBand.Internal.Contracts.Critical.imPart
    exact (h.const_smul ((2 * Complex.I)⁻¹)).const_smul (-(((etaZ b E)⁻¹ : ℝ) : ℂ))
  exact hcont.measurable.comp (measurable_globalProbeMatrix b E W n Q)

/-- The joint law of the path and the probes is a probability measure (for every `b`: the Gaussian
laws are probability measures for every variance). -/
instance isProbabilityMeasure_globalProbeLaw (W n J : ℕ) (b : ℝ) :
    IsProbabilityMeasure (globalProbeLaw W n J b) := by
  unfold globalProbeLaw growthPathLaw
  infer_instance

end BlockBand.Critical.GlobalSource
