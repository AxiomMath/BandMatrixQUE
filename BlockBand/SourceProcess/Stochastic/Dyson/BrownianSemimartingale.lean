module

public import BlockBand.SourceProcess.Stochastic.Dyson.BrownianMartingale

/-!
# Dyson Brownian motion: `F + G_{s+·}` as a continuous semimartingale in `ℝ^{N·N}`

This is the input of the Itô formula `SemimartingaleItoFormula` for the non-collision and
semimartingale clauses of `DysonBrownianMotion`: in the orthonormal real coordinates
`hermVec N H k = hermCoord N H (finProdFinEquiv.symm k)` the process
`u ↦ hermVec N (F + G_{s+u})` is an `IsContinuousSemimartingale` for `u ↦ 𝓖_{s+u}` with drift `0`
and constant covariance `gueCovVec N = (1/N) · I` (the GUE normalization `E|dG_ij|² = dt/N`).
The localizing sequence is constant `⊤`; the compensated coordinates and products are true
martingales (`martingale_coordIncr`, `martingale_coordIncr_mul`).

`vecHerm_hermVec`: the coordinates determine Hermitian matrices, so every function of `F + G_{s+u}`
is a function of this semimartingale.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.Dyson
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal Matrix
open BlockBand.Internal.Contracts.Transmission

attribute [local instance] secondCountableTopology_matrix

variable {N : ℕ}

/-- Orthonormal real coordinates of a matrix, indexed by `Fin (N * N)`. -/
def hermVec (N : ℕ) (H : Matrix (Fin N) (Fin N) ℂ) : Fin (N * N) → ℝ :=
  fun k => hermCoord N H (finProdFinEquiv.symm k)

/-- Hermitian matrix with given coordinates. -/
def vecHerm (N : ℕ) (y : Fin (N * N) → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  hermOfCoord N fun x => y (finProdFinEquiv x)

theorem vecHerm_hermVec {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian) :
    vecHerm N (hermVec N H) = H := by
  unfold vecHerm hermVec
  simp only [Equiv.symm_apply_apply]
  exact hermOfCoord_hermCoord hH

theorem hermVec_vecHerm (y : Fin (N * N) → ℝ) : hermVec N (vecHerm N y) = y := by
  funext k
  unfold vecHerm hermVec
  rw [hermCoord_hermOfCoord, Equiv.apply_symm_apply]

theorem vecHerm_isHermitian (y : Fin (N * N) → ℝ) : (vecHerm N y).IsHermitian :=
  hermOfCoord_isHermitian _

theorem continuous_hermVec : Continuous (hermVec N) :=
  continuous_pi fun _ => continuous_hermCoord _

theorem continuous_vecHerm : Continuous (vecHerm N) := by
  unfold vecHerm hermOfCoord
  refine continuous_finsetSum _ fun x _ => ?_
  exact (Complex.continuous_ofReal.comp (continuous_apply _)).smul continuous_const

/-- The GUE covariance `(1/N) · I` in the coordinates `hermVec`. -/
def gueCovVec (N : ℕ) : Matrix (Fin (N * N)) (Fin (N * N)) ℝ :=
  Matrix.of fun k l => coordCov N (finProdFinEquiv.symm k) (finProdFinEquiv.symm l)

theorem gueCovVec_apply (k l : Fin (N * N)) :
    gueCovVec N k l = if k = l then 1 / (N : ℝ) else 0 := by
  simp only [gueCovVec, coordCov, Matrix.of_apply, finProdFinEquiv.symm.injective.eq_iff]

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} {F : Ω → Matrix (Fin N) (Fin N) ℂ}

theorem isStoppingTime_top {ι : Type*} [Preorder ι] {Ω' : Type*} {m : MeasurableSpace Ω'}
    (f : Filtration ι m) : IsStoppingTime f (fun _ => (⊤ : WithTop ι)) := fun i => by
  simp

theorem stoppedProcess_top {ι β : Type*} [Nonempty ι] [LinearOrder ι] {Ω' : Type*}
    (u : ι → Ω' → β) : stoppedProcess u (fun _ => (⊤ : WithTop ι)) = u := by
  funext i ω; exact stoppedProcess_eq_of_le le_top

omit [MeasurableSpace Ω] in
theorem smCompensated_hermVec (s : ℝ≥0) (k : Fin (N * N)) (t : ℝ≥0) (ω : Ω) :
    smCompensated (fun u ω => hermVec N (F ω + G (s + u) ω)) (fun _ _ => 0) k t ω =
      coordIncr G s (finProdFinEquiv.symm k) t ω := by
  simp only [smCompensated, hermVec, Pi.zero_apply, integral_zero, sub_zero, add_zero, coordIncr]
  rw [show F ω + G (s + t) ω = (F ω + G s ω) + (G (s + t) ω - G s ω) by abel, hermCoord_add]
  ring

theorem integral_Ioc_const (t : ℝ≥0) (c : ℝ) : ∫ _ in Ioc (0 : ℝ) t, c = (t : ℝ) * c := by
  rw [setIntegral_const, Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by simp),
    sub_zero, smul_eq_mul]

/-- **`F + G_{s+·}` is a continuous semimartingale** in the coordinates `hermVec`, with drift `0`
and covariance `gueCovVec N`, for the shifted filtration (any `s`, any `𝓖_0`-measurable `F`). -/
theorem isContinuousSemimartingale_hermVec [IsProbabilityMeasure Q]
    (hG : IsHermitianBrownian Q 𝓖 N G) (hF : Measurable[𝓖 0] F) (s : ℝ≥0) :
    IsContinuousSemimartingale Q (shiftFiltration 𝓖 s)
      (fun u ω => hermVec N (F ω + G (s + u) ω)) (fun _ _ => 0) (fun _ _ => gueCovVec N) := by
  have hadapt : ∀ t, StronglyMeasurable[shiftFiltration 𝓖 s t]
      (fun ω => hermVec N (F ω + G (s + t) ω)) := fun t =>
    (continuous_hermVec.measurable.comp (measurable_hermBM_add hG hF (s + t))).stronglyMeasurable
  have hcont : ∀ ω, Continuous fun t => hermVec N (F ω + G (s + t) ω) := fun ω =>
    continuous_hermVec.comp ((continuous_hermBM_add hG F ω).comp
      (continuous_const.add continuous_id))
  refine
    { adapted := hadapt
      progressive := StronglyAdapted.isStronglyProgressive_of_continuous hadapt hcont
      continuous := Eventually.of_forall hcont
      drift_progressive := isStronglyProgressive_const _ _
      cov_progressive := isStronglyProgressive_const _ _
      integrable := Eventually.of_forall fun ω t =>
        ⟨fun _ => integrableOn_const (by simp), fun _ _ => integrableOn_const (by simp)⟩
      localizing := ⟨fun _ _ => ⊤, fun _ => isStoppingTime_top _,
        Eventually.of_forall fun _ => tendsto_const_nhds, fun n => ⟨fun k => ?_, fun k l => ?_⟩⟩ }
  · rw [stoppedProcess_top]
    refine ⟨coordIncr G s (finProdFinEquiv.symm k), martingale_coordIncr hG s _,
      fun t => Eventually.of_forall fun ω => (smCompensated_hermVec s k t ω).symm⟩
  · rw [stoppedProcess_top]
    refine ⟨_, martingale_coordIncr_mul hG s (finProdFinEquiv.symm k) (finProdFinEquiv.symm l),
      fun t => Eventually.of_forall fun ω => ?_⟩
    simp only [smCompensated_hermVec, integral_Ioc_const, gueCovVec, Matrix.of_apply]

end BlockBand.SourceProcess.Stochastic.Dyson
