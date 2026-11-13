module

public import BlockBand.Window.Transfer.BulkWindowRankSum
public import BlockBand.Model.Construction.GaussianTranslationPhysical
public import BlockBand.Internal.Contracts.WindowAngular

/-!
# Exact scalar decomposition of the physical law for the window transfer

Law: `model.law` of every `GaussianRingModel` (every `n ≥ 4`, `W ≥ 1`, `0 < b < 1/2`), raw `H`,
`t = Parameters.scalarTrace`, `H_0 = Parameters.tracelessGaussianMatrix H = H - tI`.
Nothing is assumed: the Gaussian marginal of `t` (`GaussianRingModel.scalarTrace_hasLaw`) and
the independence `t ⊥ H_0` (`GaussianRingModel.scalarTrace_independent_tracelessMatrix`) are
adopted proved theorems of `BlockBand.Counting.{ScalarTrace,TraceDecomposition}`; the rank shift
is `physicalOrderedEigenvalue_gaussianSpectralTranslate`. This file identifies them with the
primitive chart `(Ω, μ, Y, t)` of `BulkWindowRankSum` and proves the moment transfer
`‖λ^0_α - e‖_q ≤ ‖λ_α - e‖_q + K_q σ` (Gaussian scaling `‖t‖_q = K_q σ`,
`K_q = ‖Z‖_{L^q}`, `Z ~ N(0,1)`). New file (no draft source).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Window.Transfer

open MeasureTheory ProbabilityTheory
open BlockBand.Model.Construction BlockBand.Internal.Contracts.WindowAngular
open scoped NNReal ENNReal

variable {p : Parameters}

/-- The draft's scalar variance `σ² = c/(NW)` is the adopted `scalarTraceVariance`. -/
theorem scalarVariance_originalScalarSigma (p : Parameters) :
    scalarVariance (originalScalarSigma p) = p.scalarTraceVariance := by
  apply NNReal.eq
  change originalScalarSigma p ^ 2 = p.c / ((p.N : ℝ) * (p.W : ℝ))
  exact originalScalarSigma_sq p

/-- `t = N⁻¹ Tr H ~ N(0, c/(NW))` under the physical law, in the draft's normalization. -/
theorem scalarTrace_hasLaw_original (model : p.GaussianRingModel) :
    HasLaw p.scalarTrace (gaussianReal 0 (scalarVariance (originalScalarSigma p)))
      (model.law : Measure p.SiteMatrix) := by
  rw [scalarVariance_originalScalarSigma]
  exact model.scalarTrace_hasLaw

/-- `H_0 ⊥ t` under the physical law. -/
theorem traceless_indep_scalarTrace (model : p.GaussianRingModel) :
    IndepFun p.tracelessGaussianMatrix p.scalarTrace (model.law : Measure p.SiteMatrix) :=
  model.scalarTrace_independent_tracelessMatrix.symm

theorem tracelessGaussianMatrix_add_scalar (H : p.SiteMatrix) :
    p.tracelessGaussianMatrix H + (p.scalarTrace H : ℂ) • (1 : p.SiteMatrix) = H := by
  simp [Parameters.tracelessGaussianMatrix]

theorem isHermitian_tracelessGaussianMatrix (H : p.SiteMatrix) (hH : H.IsHermitian) :
    (p.tracelessGaussianMatrix H).IsHermitian := by
  have h := isHermitian_gaussianSpectralTranslate (-p.scalarTrace H) H hH
  have he : gaussianSpectralTranslate (-p.scalarTrace H) H = p.tracelessGaussianMatrix H := by
    simp [gaussianSpectralTranslate, Parameters.tracelessGaussianMatrix, sub_eq_add_neg]
  rwa [he] at h

/-- `λ_α(H) = λ_α(H_0) + t` for Hermitian `H`. -/
theorem physicalOrderedEigenvalue_eq_traceless_add (H : p.SiteMatrix) (hH : H.IsHermitian)
    (α : Fin p.N) :
    physicalOrderedEigenvalue p H α =
      physicalOrderedEigenvalue p (p.tracelessGaussianMatrix H) α + p.scalarTrace H := by
  have h := physicalOrderedEigenvalue_gaussianSpectralTranslate p (p.scalarTrace H)
    (p.tracelessGaussianMatrix H) (isHermitian_tracelessGaussianMatrix H hH) α
  rwa [gaussianSpectralTranslate, tracelessGaussianMatrix_add_scalar] at h

/-- A scalar-shift invariant observable is a function of `H_0` alone (every `H`). -/
theorem scalarShiftInvariant_traceless {A : p.SiteMatrix → ℝ} (hA : IsScalarShiftInvariant A)
    (H : p.SiteMatrix) : A (p.tracelessGaussianMatrix H) = A H := by
  have h := hA (p.tracelessGaussianMatrix H) (p.scalarTrace H)
  rw [tracelessGaussianMatrix_add_scalar] at h
  exact h.symm

/-- Increasing order of `physicalOrderedEigenvalue` holds for every raw matrix (the
non-Hermitian default is the constant `0`). -/
theorem physicalOrderedEigenvalue_monotone (p : Parameters) (H : p.SiteMatrix) :
    Monotone (fun α => physicalOrderedEigenvalue p H α) := by
  intro α β hab
  by_cases hH : H.IsHermitian
  · change physicalOrderedEigenvalue p H α ≤ physicalOrderedEigenvalue p H β
    unfold physicalOrderedEigenvalue
    rw [rawIncreasingEigenvalue_eq _ H hH, rawIncreasingEigenvalue_eq _ H hH]
    exact BlockBand.Foundations.Spectral.increasingEigenvalue_monotone hH hab
  · simp [physicalOrderedEigenvalue, rawIncreasingEigenvalue, hH]

/-- The physical window expectation in the primitive chart `Y = H_0`, `t = N⁻¹ Tr H`,
`X_α = λ_α(·)` (equality of the Bochner integrals, a.e. equality of integrands). -/
theorem windowExpectation_eq_split (model : p.GaussianRingModel) (E ρ : ℝ) (w : ℝ → ℝ)
    (A : Fin p.N → p.SiteMatrix → ℝ) (hA : ∀ α, IsScalarShiftInvariant (A α)) :
    windowExpectation p model E ρ w A =
      ∫ H, ∑ i : Fin p.N, A i (p.tracelessGaussianMatrix H) *
        w ((p.N : ℝ) * ρ * (physicalOrderedEigenvalue p (p.tracelessGaussianMatrix H) i +
          p.scalarTrace H - E)) ∂(model.law : Measure p.SiteMatrix) := by
  unfold windowExpectation
  apply integral_congr_ae
  filter_upwards [model.isPhysical.1] with H hH
  apply Finset.sum_congr rfl
  intro i _
  rw [scalarShiftInvariant_traceless (hA i), physicalOrderedEigenvalue_eq_traceless_add H hH,
    mul_comm]

/-- `K_q = ‖Z‖_{L^q}`, `Z ~ N(0,1)`. -/
def gaussianMomentConstant (q : ℝ) : ℝ :=
  (eLpNorm id (ENNReal.ofReal q) (gaussianReal 0 1)).toReal

theorem gaussianMomentConstant_nonneg (q : ℝ) : 0 ≤ gaussianMomentConstant q :=
  ENNReal.toReal_nonneg

/-- Gaussian scaling: `‖t‖_{L^q} = K_q σ` (bound form), every real `q`. -/
theorem eLpNorm_scalarTrace_le (model : p.GaussianRingModel) (q : ℝ) :
    eLpNorm p.scalarTrace (ENNReal.ofReal q) (model.law : Measure p.SiteMatrix) ≤
      ENNReal.ofReal (gaussianMomentConstant q * originalScalarSigma p) := by
  have hlaw := scalarTrace_hasLaw_original model
  have hσ := originalScalarSigma_pos p
  have hmap : eLpNorm p.scalarTrace (ENNReal.ofReal q) (model.law : Measure p.SiteMatrix) =
      eLpNorm id (ENNReal.ofReal q) (gaussianReal 0 (scalarVariance (originalScalarSigma p))) := by
    rw [← hlaw.map_eq, eLpNorm_map_measure (by fun_prop) hlaw.aemeasurable]
    rfl
  have hscale : gaussianReal 0 (scalarVariance (originalScalarSigma p)) =
      (gaussianReal 0 1).map (fun x => originalScalarSigma p * x) := by
    rw [gaussianReal_map_const_mul, mul_zero, mul_one]
    congr 1
  have hfin : eLpNorm id (ENNReal.ofReal q) (gaussianReal 0 1) ≠ ⊤ :=
    (memLp_id_gaussianReal' (μ := 0) (v := 1) (ENNReal.ofReal q) ENNReal.ofReal_ne_top).eLpNorm_ne_top
  rw [hmap, hscale, eLpNorm_map_measure (by fun_prop) (by fun_prop)]
  have hfun : (id ∘ fun x : ℝ => originalScalarSigma p * x) = originalScalarSigma p • id := by
    funext x; simp
  rw [hfun, eLpNorm_const_smul, Real.enorm_eq_ofReal hσ.le, mul_comm,
    ENNReal.ofReal_mul (gaussianMomentConstant_nonneg q), gaussianMomentConstant,
    ENNReal.ofReal_toReal hfin]

/-- Moment transfer to the traceless state: if `‖λ_α - e‖_{L^q(law)} ≤ L` (`q ≥ 1`), then
`‖λ_α(·) - e‖_{L^q(Law(H_0))} ≤ L + K_q σ`. -/
theorem traceless_rank_eLpNorm_le (model : p.GaussianRingModel) (α : Fin p.N) (e q L : ℝ)
    (hq : 1 ≤ q) (hL : 0 ≤ L)
    (hLp : eLpNorm (fun H => physicalOrderedEigenvalue p H α - e) (ENNReal.ofReal q)
      (model.law : Measure p.SiteMatrix) ≤ ENNReal.ofReal L) :
    eLpNorm (fun y => physicalOrderedEigenvalue p y α - e) (ENNReal.ofReal q)
        ((model.law : Measure p.SiteMatrix).map p.tracelessGaussianMatrix) ≤
      ENNReal.ofReal (L + gaussianMomentConstant q * originalScalarSigma p) := by
  have hlam := measurable_physicalOrderedEigenvalue p α
  rw [eLpNorm_map_measure (by fun_prop) p.measurable_tracelessGaussianMatrix.aemeasurable]
  have hae : ((fun y => physicalOrderedEigenvalue p y α - e) ∘ p.tracelessGaussianMatrix) =ᵐ[
      (model.law : Measure p.SiteMatrix)]
      (fun H => physicalOrderedEigenvalue p H α - e) - p.scalarTrace := by
    filter_upwards [model.isPhysical.1] with H hH
    simp only [Function.comp_apply, Pi.sub_apply]
    rw [physicalOrderedEigenvalue_eq_traceless_add H hH]
    ring
  rw [eLpNorm_congr_ae hae]
  have hp : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by simpa using ENNReal.ofReal_le_ofReal hq
  calc _ ≤ eLpNorm (fun H => physicalOrderedEigenvalue p H α - e) (ENNReal.ofReal q)
          (model.law : Measure p.SiteMatrix) +
        eLpNorm p.scalarTrace (ENNReal.ofReal q) (model.law : Measure p.SiteMatrix) :=
        eLpNorm_sub_le hp
    _ ≤ ENNReal.ofReal L + ENNReal.ofReal (gaussianMomentConstant q * originalScalarSigma p) :=
        add_le_add hLp (eLpNorm_scalarTrace_le model q)
    _ = _ := (ENNReal.ofReal_add hL (mul_nonneg (gaussianMomentConstant_nonneg q)
        (originalScalarSigma_pos p).le)).symm

/-- `σ ≤ a_{n,W}/N`: indeed `Nσ = √(cn) ≤ √n ≤ a_{n,W}`. -/
theorem originalScalarSigma_le_scale (p : Parameters) (a : ℝ) (ha : Real.sqrt (p.n : ℝ) ≤ a) :
    originalScalarSigma p ≤ a / (p.N : ℝ) := by
  have hN : (0 : ℝ) < p.N := by exact_mod_cast p.N_pos
  rw [le_div_iff₀ hN, mul_comm, dimension_mul_originalScalarSigma]
  refine le_trans (Real.sqrt_le_sqrt ?_) ha
  have hc1 : p.c ≤ 1 := by unfold Parameters.c; linarith [p.b_pos]
  have hn : (0 : ℝ) ≤ p.n := Nat.cast_nonneg _
  nlinarith

end BlockBand.Window.Transfer
