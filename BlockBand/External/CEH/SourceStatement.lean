module

public import BlockBand.External.CEH.SourceMDE

/-!
# The local laws and eigenstate thermalization of CEH, as hypotheses

This file states Theorems 2.3 and 2.5 of Cipolloni–Erdős–Henheik (arXiv:2607.02446v2):
the averaged and isotropic local laws (2.8)–(2.9) and eigenstate thermalization (2.12)–(2.15)
for the deformed Wigner matrix `H_λ = H₀ + λW`. They are collected in the structure
`SourceContract`, used as a hypothesis (these are cited results of the paper).

The measure is `WignerFamily.law N` on Hermitian matrices. The entry laws and moment constants
are fixed first, then `κ, C`, then the exponents; the threshold `N₀` depends only on these, and the
bounds are uniform in `λ > 0`, in every `H₀` with `‖H₀‖ ≤ C N^κ λ`, in the spectral parameter
`z`, in the deterministic observable and in the deterministic vectors or index pairs. Each
probability bound holds for each fixed choice of these parameters, not for a supremum over them.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.External.CEH

open Matrix MeasureTheory
open scoped ENNReal NNReal Matrix.Norms.L2Operator

/-- The normalized Hilbert–Schmidt norm `⟨BB*⟩^{1/2}`, with `⟨·⟩ = N⁻¹ tr`. -/
def normalizedHilbertSchmidt {N : ℕ} (B : SourceMatrix N) : ℝ :=
  Real.sqrt (normalizedTrace (B * Bᴴ)).re

/-- The right side of CEH (2.8):
`‖B‖_hs / (N|Im z|) · (⟨Γ(M) BB*⟩ / ⟨BB*⟩)^{1/2}`. It is `0` at `B = 0` (Lean's `x / 0 = 0`). -/
def averagedControl {N : ℕ} (M B : SourceMatrix N) (z : ℂ) : ℝ :=
  normalizedHilbertSchmidt B / ((N : ℝ) * |z.im|) *
    Real.sqrt ((normalizedTrace (gammaMatrix M * B * Bᴴ)).re /
      (normalizedTrace (B * Bᴴ)).re)

/-- The right side of CEH (2.9):
`(ρ / (N|Im z|))^{1/2} ‖x‖ ‖y‖ (⟨x, Γ(M)x⟩⟨y, Γ(M)y⟩ / (‖x‖²‖y‖²))^{1/2}`, with unnormalized
Euclidean norms. It is `0` if `x = 0` or `y = 0`. -/
def isotropicControl {N : ℕ} (M : SourceMatrix N) (z : ℂ)
    (x y : Fin N → ℂ) : ℝ :=
  Real.sqrt (sourceDensity M / ((N : ℝ) * |z.im|)) *
    sourceVectorNorm x * sourceVectorNorm y *
    Real.sqrt ((sourceMatrixElement (gammaMatrix M) x x).re *
      (sourceMatrixElement (gammaMatrix M) y y).re /
      (sourceVectorNorm x ^ 2 * sourceVectorNorm y ^ 2))

/-- The averaged control vanishes at `B = 0`. -/
@[simp] theorem averagedControl_zero {N : ℕ} (M : SourceMatrix N) (z : ℂ) :
    averagedControl M 0 z = 0 := by
  simp [averagedControl, normalizedHilbertSchmidt, normalizedTrace]

/-- The isotropic control vanishes at `x = 0`. -/
@[simp] theorem isotropicControl_zero_left {N : ℕ} (M : SourceMatrix N) (z : ℂ)
    (y : Fin N → ℂ) : isotropicControl M z 0 y = 0 := by
  simp [isotropicControl, sourceVectorNorm]

/-- The isotropic control vanishes at `y = 0`. -/
@[simp] theorem isotropicControl_zero_right {N : ℕ} (M : SourceMatrix N) (z : ℂ)
    (x : Fin N → ℂ) : isotropicControl M z x 0 = 0 := by
  simp [isotropicControl, sourceVectorNorm]

/-- The event `|⟨(G - M)B⟩| > N^δ · averagedControl`, `G` the resolvent of `H_λ`. -/
def averagedBadEvent {N : ℕ} {lambda : ℝ} {H0 : SourceHermitian N}
    (M : MDEBranch lambda H0) (B : SourceMatrix N) (z : ℂ) (delta : ℝ) :
    Set (SourceHermitian N) :=
  {W | (N : ℝ) ^ delta * averagedControl (M.matrix z) B z <
    ‖normalizedTrace ((sourceResolvent lambda H0 W z - M.matrix z) * B)‖}

/-- The event `|⟨x, (G - M)y⟩| > N^δ · isotropicControl`, `G` the resolvent of `H_λ`. -/
def isotropicBadEvent {N : ℕ} {lambda : ℝ} {H0 : SourceHermitian N}
    (M : MDEBranch lambda H0) (x y : Fin N → ℂ) (z : ℂ) (delta : ℝ) :
    Set (SourceHermitian N) :=
  {W | (N : ℝ) ^ delta * isotropicControl (M.matrix z) z x y <
    ‖sourceMatrixElement (sourceResolvent lambda H0 W z - M.matrix z) x y‖}

/-- The coefficient `θ_ij` computed from `M_i` and `M_j*` (`regularizationCoefficient`). -/
def eigenpairTheta {N : ℕ} {lambda : ℝ} {H0 : SourceHermitian N}
    (M : MDEBranch lambda H0) (spacing : TypicalSpacing M)
    (selection : EigenpairSelection N) (xi : ℝ) (W : SourceHermitian N)
    (i j : Fin N) : ℝ :=
  regularizationCoefficient lambda (eigenvalueMDE M spacing selection xi W i)
    (eigenvalueMDE M spacing selection xi W j)ᴴ

/-- The regularized observable `A_ij` of CEH (2.13). -/
def eigenpairRegularized {N : ℕ} {lambda : ℝ} {H0 : SourceHermitian N}
    (M : MDEBranch lambda H0) (spacing : TypicalSpacing M)
    (selection : EigenpairSelection N) (xi : ℝ) (W : SourceHermitian N)
    (A : SourceMatrix N) (i j : Fin N) : SourceMatrix N :=
  regularizedObservable (eigenpairTheta M spacing selection xi W i j)
    (eigenvalueMDE M spacing selection xi W i)
    (eigenvalueMDE M spacing selection xi W j)ᴴ A

/-- The control `s₂(i, j; A)` of CEH (2.14), built from `M_i`, `M_j` and the regularized
observable `A_ij`. -/
def eigenpairControl {N : ℕ} {lambda : ℝ} {H0 : SourceHermitian N}
    (M : MDEBranch lambda H0) (spacing : TypicalSpacing M)
    (selection : EigenpairSelection N) (xi : ℝ) (W : SourceHermitian N)
    (A : SourceMatrix N) (i j : Fin N) : ℝ :=
  sTwo (eigenpairTheta M spacing selection xi W i j) lambda
    (eigenvalueMDE M spacing selection xi W i)
    (eigenvalueMDE M spacing selection xi W j)
    (eigenpairRegularized M spacing selection xi W A i j)

/-- The overlap error of CEH (2.15): `|⟨u_i, A u_j⟩ - δ_ij θ_ij ⟨Γ_i A⟩|`, with `u_i` the
selected eigenvectors of `H_λ`. -/
def eigenpairError {N : ℕ} {lambda : ℝ} {H0 : SourceHermitian N}
    (M : MDEBranch lambda H0) (spacing : TypicalSpacing M)
    (selection : EigenpairSelection N) (xi : ℝ) (W : SourceHermitian N)
    (A : SourceMatrix N) (i j : Fin N) : ℝ :=
  let H := deformedHermitian lambda H0 W
  let center := (eigenpairTheta M spacing selection xi W i j : ℂ) *
    normalizedTrace (gammaMatrix (eigenvalueMDE M spacing selection xi W i) * A)
  ‖sourceMatrixElement A (selection.eigenvector H i) (selection.eigenvector H j) -
    (if i = j then center else 0)‖

/-- The event `eigenpairError > N^δ s₂(i, j; A) / √N`, for a deterministic matrix `A` and an index
pair `(i, j)`; `s₂` is itself random. -/
def eigenpairBadEvent {N : ℕ} {lambda : ℝ} {H0 : SourceHermitian N}
    (M : MDEBranch lambda H0) (spacing : TypicalSpacing M)
    (selection : EigenpairSelection N) (xi delta : ℝ) (A : SourceMatrix N)
    (i j : Fin N) : Set (SourceHermitian N) :=
  {W | (N : ℝ) ^ delta * eigenpairControl M spacing selection xi W A i j /
      Real.sqrt (N : ℝ) < eigenpairError M spacing selection xi W A i j}

/-- The averaged local law (CEH Theorem 2.3): for all `κ, C, ε, δ, D` there is `N₀` such that for
`N ≥ N₀`, uniformly in `λ > 0`, admissible `H₀`, `z` in the local-law domain and `B`, the averaged
bad event is measurable with probability at most `N^{-D}`. -/
def AveragedLocalLaw (W : WignerFamily) : Prop :=
  ∀ kappa C : ℝ, 0 ≤ kappa → 0 < C →
  ∀ epsilon delta D : ℝ, 0 < epsilon → 0 < delta → 0 < D →
  ∃ N0 : ℕ, 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
    ∀ lambda : ℝ, 0 < lambda →
    ∀ H0 : SourceHermitian N, DeformationBound kappa C lambda H0 →
    ∀ M : MDEBranch lambda H0,
    ∀ z : ℂ, InLocalLawDomain M kappa epsilon z →
    ∀ B : SourceMatrix N,
      MeasurableSet (averagedBadEvent M B z delta) ∧
      (W.law N : Measure (SourceHermitian N)) (averagedBadEvent M B z delta) ≤
        ENNReal.ofReal ((N : ℝ) ^ (-D))

/-- The isotropic local law (CEH Theorem 2.3), uniformly in the deterministic vectors `x, y`. -/
def IsotropicLocalLaw (W : WignerFamily) : Prop :=
  ∀ kappa C : ℝ, 0 ≤ kappa → 0 < C →
  ∀ epsilon delta D : ℝ, 0 < epsilon → 0 < delta → 0 < D →
  ∃ N0 : ℕ, 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
    ∀ lambda : ℝ, 0 < lambda →
    ∀ H0 : SourceHermitian N, DeformationBound kappa C lambda H0 →
    ∀ M : MDEBranch lambda H0,
    ∀ z : ℂ, InLocalLawDomain M kappa epsilon z →
    ∀ x y : Fin N → ℂ,
      MeasurableSet (isotropicBadEvent M x y z delta) ∧
      (W.law N : Measure (SourceHermitian N)) (isotropicBadEvent M x y z delta) ≤
        ENNReal.ofReal ((N : ℝ) ^ (-D))

/-- Eigenstate thermalization (CEH Theorem 2.5): for all `κ, C` there is `ξ₀ > 0` such that for
`0 < ξ < ξ₀` and all `δ, D` there is `N₀ ≥ 4` with the eigenpair bad event of probability at most
`N^{-D}` for `N ≥ N₀`, uniformly in `λ`, admissible `H₀`, `A` and the indices `i, j`. -/
def EigenstateThermalization (W : WignerFamily) : Prop :=
  ∀ kappa C : ℝ, 0 ≤ kappa → 0 < C →
  ∃ xi0 : ℝ, 0 < xi0 ∧
    ∀ xi : ℝ, 0 < xi → xi < xi0 →
    ∀ delta D : ℝ, 0 < delta → 0 < D →
    ∃ N0 : ℕ, 4 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
      ∀ lambda : ℝ, 0 < lambda →
      ∀ H0 : SourceHermitian N, DeformationBound kappa C lambda H0 →
      ∀ M : MDEBranch lambda H0,
      ∀ spacing : TypicalSpacing M,
      ∀ selection : EigenpairSelection N,
      ∀ A : SourceMatrix N, ∀ i j : Fin N,
        MeasurableSet (eigenpairBadEvent M spacing selection xi delta A i j) ∧
        (W.law N : Measure (SourceHermitian N))
          (eigenpairBadEvent M spacing selection xi delta A i j) ≤
            ENNReal.ofReal ((N : ℝ) ^ (-D))

/-- The results of CEH used as hypotheses: the two local laws and eigenstate thermalization,
together with deterministic existence statements (MDE branches, their uniqueness off the real
axis, typical spacings and eigenpair selections) for the objects in CEH (2.4), (2.10) and (2.12).
Existence of the typical spacing is required only for `N ≥ 4`: in the normalization of CEH,
`N η ρ` tends to `N/π` as `η → ∞`, which is less than one for `N ≤ 3`. -/
structure SourceContract (W : WignerFamily) : Prop where
  mde_exists : ∀ (N : ℕ), 0 < N → ∀ lambda : ℝ, 0 < lambda →
    ∀ H0 : SourceHermitian N, Nonempty (MDEBranch lambda H0)
  mde_unique_off_real : ∀ {N : ℕ} {lambda : ℝ} {H0 : SourceHermitian N},
    0 < N → 0 < lambda → ∀ M M' : MDEBranch lambda H0,
      ∀ z : ℂ, z.im ≠ 0 → M.matrix z = M'.matrix z
  spacing_exists : ∀ {N : ℕ} {lambda : ℝ} {H0 : SourceHermitian N},
    4 ≤ N → 0 < lambda → ∀ M : MDEBranch lambda H0, Nonempty (TypicalSpacing M)
  eigenpairs_exist : ∀ (N : ℕ), 0 < N → Nonempty (EigenpairSelection N)
  averaged : AveragedLocalLaw W
  isotropic : IsotropicLocalLaw W
  eigenstate_thermalization : EigenstateThermalization W

/-- The averaged local law, from `SourceContract`. -/
theorem SourceContract.averagedLocalLaw {W : WignerFamily} (source : SourceContract W) :
    AveragedLocalLaw W := source.averaged

/-- The isotropic local law, from `SourceContract`. -/
theorem SourceContract.isotropicLocalLaw {W : WignerFamily} (source : SourceContract W) :
    IsotropicLocalLaw W := source.isotropic

/-- Eigenstate thermalization, from `SourceContract`. -/
theorem SourceContract.eigenstateThermalization {W : WignerFamily}
    (source : SourceContract W) : EigenstateThermalization W :=
  source.eigenstate_thermalization

end BlockBand.External.CEH
