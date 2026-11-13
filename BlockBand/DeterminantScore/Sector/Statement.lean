module

public import BlockBand.Internal.Contracts.Inputs
public import BlockBand.Internal.Contracts.CoareaPalm

/-!
# Sector integration by parts: statement

`SectorIBPStatement`: first derivatives of the sector-cut determinant functions across the
singular sector boundary, Gaussian integration by parts, and the first derivative of the complete
sector mass.

## Law and coordinates

`G_m(t)` is realized on the explicit real coordinate space
`HermCoord m → ℝ`, `HermCoord m = Fin m × Fin m`, with the linear coordinate map
`hermOfCoord : (HermCoord m → ℝ) → Matrix (Fin m) (Fin m) ℂ`:

* `x (a, a)` is the (real) diagonal entry `G_aa`;
* for `a < b`, `x (a, b) = Re G_ab` and `x (b, a) = Im G_ab`
  (so `G_ab = x (a,b) + i x (b,a)` and `G_ba = conj G_ab`).

The law is `Inputs.gaussianProduct (hermVariance m t)`: independent centered real Gaussians,
variance `t` on the diagonal coordinates and `t/2` on each real and imaginary off-diagonal
coordinate. Its push-forward under `hermOfCoord` is `CoareaPalm.gueMeasure (Fin m) t`
(proved in the module `BlockBand.DeterminantScore.Sector.GUELaw`).

## Quantifier order and scope

For every `m`, every Hermitian `K`, every sector `ℓ` and every coordinate `c` (and every
`t` for the integral clauses): weak derivatives in the standard distributional sense
(`Inputs.HasWeakCoordPartial`, locally integrable derivative, hence no singular boundary
measure), agreement with the ordinary derivative off `{P = 0}`, Gaussian integrability of the
functions, of their weak derivatives and of the coordinate products, both first Gaussian
integration-by-parts identities, the pole-removal identity `P² R_ab = P C_ab`, and the first
derivative of `Z_ℓ` in a parameter. The paper's hypotheses `t > 0`, attainability of `ℓ` and
smoothness/finite dimensionality of the parameter are not needed for these unnormalized
identities (attainability `Z_ℓ(K) > 0` only enters a later normalization, which is not
part of the conclusion); the Lean statement holds for every `t ≥ 0`, every `ℓ`, and a
parameter in any real normed space along which `K` is Hermitian and entrywise differentiable
at the base point. Each clause therefore implies the corresponding clause of the paper.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.Sector

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts
open scoped NNReal

/-- Real Gaussian coordinates of an `m × m` Hermitian matrix: `(a, a)` diagonal, `(a, b)` with
`a < b` the real part and `(b, a)` the imaginary part of the entry `(a, b)`. -/
abbrev HermCoord (m : ℕ) := Fin m × Fin m

/-- The explicit linear coordinate map onto Hermitian matrices. -/
def hermOfCoord {m : ℕ} (x : HermCoord m → ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun a b =>
    if a = b then (x (a, a) : ℂ)
    else if a < b then (x (a, b) : ℂ) + (x (b, a) : ℂ) * Complex.I
    else (x (b, a) : ℂ) - (x (a, b) : ℂ) * Complex.I

/-- Coordinate variances of `G_m(t)`: `t` on the diagonal, `t/2` on every real and imaginary
off-diagonal coordinate. -/
def hermVariance (m : ℕ) (t : ℝ≥0) : HermCoord m → ℝ≥0 :=
  fun c => if c.1 = c.2 then t else t / 2

/-- The coordinate law of `G_m(t)`: the product Gaussian `Inputs.gaussianProduct`. -/
def hermGaussian (m : ℕ) (t : ℝ≥0) : Measure (HermCoord m → ℝ) :=
  Inputs.gaussianProduct (hermVariance m t)

/-- The sector predicate `N_-(K + G(x)) = ℓ`. -/
def InSector {m : ℕ} (K : Matrix (Fin m) (Fin m) ℂ) (ℓ : ℕ) (x : HermCoord m → ℝ) : Prop :=
  CoareaPalm.negativeCount (K + hermOfCoord x) = ℓ

instance {m : ℕ} (K : Matrix (Fin m) (Fin m) ℂ) (ℓ : ℕ) (x : HermCoord m → ℝ) :
    Decidable (InSector K ℓ x) :=
  inferInstanceAs (Decidable (_ = _))

/-- `1{N_-(M)=ℓ} P²`, `M = K + G(x)`, `P = det M`. -/
def sectorDetSq {m : ℕ} (K : Matrix (Fin m) (Fin m) ℂ) (ℓ : ℕ) (x : HermCoord m → ℝ) : ℂ :=
  if InSector K ℓ x then (K + hermOfCoord x).det ^ 2 else 0

/-- `1{N_-(M)=ℓ} P C_ab`, `C = adj M`. -/
def sectorDetAdj {m : ℕ} (K : Matrix (Fin m) (Fin m) ℂ) (ℓ : ℕ) (a b : Fin m)
    (x : HermCoord m → ℝ) : ℂ :=
  if InSector K ℓ x then
    (K + hermOfCoord x).det * (K + hermOfCoord x).adjugate a b
  else 0

/-- The inverse insertion `1{N_-(M)=ℓ} P² R_ab`, `R = M⁻¹`. -/
def sectorDetSqInv {m : ℕ} (K : Matrix (Fin m) (Fin m) ℂ) (ℓ : ℕ) (a b : Fin m)
    (x : HermCoord m → ℝ) : ℂ :=
  if InSector K ℓ x then
    (K + hermOfCoord x).det ^ 2 * (K + hermOfCoord x)⁻¹ a b
  else 0

/-- Ordinary partial derivative of a complex function of the coordinates in coordinate `c`. -/
def coordDeriv {m : ℕ} (F : (HermCoord m → ℝ) → ℂ) (c : HermCoord m)
    (x : HermCoord m → ℝ) : ℂ :=
  deriv (fun s : ℝ => F (Function.update x c s)) (x c)

/-- Candidate weak derivative of `1{N_-=ℓ} P²`: the indicator times `∂_c (P²)`. -/
def sectorDetSqDeriv {m : ℕ} (K : Matrix (Fin m) (Fin m) ℂ) (ℓ : ℕ) (c : HermCoord m)
    (x : HermCoord m → ℝ) : ℂ :=
  if InSector K ℓ x then
    coordDeriv (fun y => (K + hermOfCoord y).det ^ 2) c x
  else 0

/-- Candidate weak derivative of `1{N_-=ℓ} P C_ab`: the indicator times `∂_c (P C_ab)`. -/
def sectorDetAdjDeriv {m : ℕ} (K : Matrix (Fin m) (Fin m) ℂ) (ℓ : ℕ) (a b : Fin m)
    (c : HermCoord m) (x : HermCoord m → ℝ) : ℂ :=
  if InSector K ℓ x then
    coordDeriv (fun y => (K + hermOfCoord y).det * (K + hermOfCoord y).adjugate a b) c x
  else 0

/-- The complete sector mass `Z_ℓ(K) = E[1{N_-(K + G_m(t)) = ℓ} det(K + G_m(t))²]`. -/
def sectorMass (m : ℕ) (t : ℝ≥0) (K : Matrix (Fin m) (Fin m) ℂ) (ℓ : ℕ) : ℂ :=
  ∫ x, sectorDetSq K ℓ x ∂hermGaussian m t

/-- Entrywise derivative `∂K = DK(θ)[h]` of a matrix-valued parameter family. -/
def paramDeriv {m : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : E → Matrix (Fin m) (Fin m) ℂ) (θ h : E) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun a b => fderiv ℝ (fun θ' => K θ' a b) θ h

/-- **Sector integration by parts**, as a Prop-valued structure of named clauses.

Law `hermGaussian m t = gaussianProduct (hermVariance m t)` on the real coordinates of
`G_m(t)` (see the module docstring); `M = K + hermOfCoord x`.

* `weak_detSq`, `weak_detAdj`: in every real Gaussian coordinate `c`, `1{N_-=ℓ}P²` and
  `1{N_-=ℓ}PC_ab` have the weak derivatives `1{N_-=ℓ}∂_c(P²)`, `1{N_-=ℓ}∂_c(PC_ab)`
  (distributional, locally integrable: no singular boundary measure);
* `ordinary_detSq`, `ordinary_detAdj`: these agree with the ordinary derivatives off `{P=0}`;
* `integrable_*`: the functions, their first derivatives and coordinate products are
  Gaussian integrable;
* `detSqInv_eq`: the pole removal `P² R_ab = P C_ab`, pointwise;
* `ibp_one`, `ibp_inverse`: first Gaussian integration by parts with insertion `1` and `R_ab`:
  `E[x_c 1{..}P²] = v_c E[∂_c(1{..}P²)]`, `E[x_c 1{..}P² R_ab] = v_c E[∂_c(1{..}P C_ab)]`;
* `mass_hasFDerivAt`: `∂Z_ℓ = 2 E[1{N_-=ℓ} P² Tr(R ∂K)]` for a Hermitian parameter family. -/
structure SectorIBPStatement : Prop where
  weak_detSq : ∀ (m : ℕ) (K : Matrix (Fin m) (Fin m) ℂ), K.IsHermitian →
    ∀ (ℓ : ℕ) (c : HermCoord m),
      Inputs.HasWeakCoordPartial c (sectorDetSq K ℓ) (sectorDetSqDeriv K ℓ c)
  weak_detAdj : ∀ (m : ℕ) (K : Matrix (Fin m) (Fin m) ℂ), K.IsHermitian →
    ∀ (ℓ : ℕ) (a b : Fin m) (c : HermCoord m),
      Inputs.HasWeakCoordPartial c (sectorDetAdj K ℓ a b) (sectorDetAdjDeriv K ℓ a b c)
  ordinary_detSq : ∀ (m : ℕ) (K : Matrix (Fin m) (Fin m) ℂ), K.IsHermitian →
    ∀ (ℓ : ℕ) (c : HermCoord m) (x : HermCoord m → ℝ), (K + hermOfCoord x).det ≠ 0 →
      HasDerivAt (fun s : ℝ => sectorDetSq K ℓ (Function.update x c s))
        (sectorDetSqDeriv K ℓ c x) (x c)
  ordinary_detAdj : ∀ (m : ℕ) (K : Matrix (Fin m) (Fin m) ℂ), K.IsHermitian →
    ∀ (ℓ : ℕ) (a b : Fin m) (c : HermCoord m) (x : HermCoord m → ℝ),
      (K + hermOfCoord x).det ≠ 0 →
      HasDerivAt (fun s : ℝ => sectorDetAdj K ℓ a b (Function.update x c s))
        (sectorDetAdjDeriv K ℓ a b c x) (x c)
  integrable_detSq : ∀ (m : ℕ) (t : ℝ≥0) (K : Matrix (Fin m) (Fin m) ℂ), K.IsHermitian →
    ∀ (ℓ : ℕ) (c : HermCoord m),
      Integrable (sectorDetSq K ℓ) (hermGaussian m t) ∧
      Integrable (sectorDetSqDeriv K ℓ c) (hermGaussian m t) ∧
      Integrable (fun x => x c • sectorDetSq K ℓ x) (hermGaussian m t)
  integrable_detAdj : ∀ (m : ℕ) (t : ℝ≥0) (K : Matrix (Fin m) (Fin m) ℂ), K.IsHermitian →
    ∀ (ℓ : ℕ) (a b : Fin m) (c : HermCoord m),
      Integrable (sectorDetAdj K ℓ a b) (hermGaussian m t) ∧
      Integrable (sectorDetAdjDeriv K ℓ a b c) (hermGaussian m t) ∧
      Integrable (fun x => x c • sectorDetAdj K ℓ a b x) (hermGaussian m t)
  detSqInv_eq : ∀ (m : ℕ) (K : Matrix (Fin m) (Fin m) ℂ) (ℓ : ℕ) (a b : Fin m),
    sectorDetSqInv K ℓ a b = sectorDetAdj K ℓ a b
  ibp_one : ∀ (m : ℕ) (t : ℝ≥0) (K : Matrix (Fin m) (Fin m) ℂ), K.IsHermitian →
    ∀ (ℓ : ℕ) (c : HermCoord m),
      (∫ x, x c • sectorDetSq K ℓ x ∂hermGaussian m t) =
        (hermVariance m t c : ℝ) • ∫ x, sectorDetSqDeriv K ℓ c x ∂hermGaussian m t
  ibp_inverse : ∀ (m : ℕ) (t : ℝ≥0) (K : Matrix (Fin m) (Fin m) ℂ), K.IsHermitian →
    ∀ (ℓ : ℕ) (a b : Fin m) (c : HermCoord m),
      (∫ x, x c • sectorDetSqInv K ℓ a b x ∂hermGaussian m t) =
        (hermVariance m t c : ℝ) • ∫ x, sectorDetAdjDeriv K ℓ a b c x ∂hermGaussian m t
  mass_hasFDerivAt : ∀ (m : ℕ) (t : ℝ≥0) (ℓ : ℕ) (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℝ E] (K : E → Matrix (Fin m) (Fin m) ℂ) (θ : E),
    (∀ θ', (K θ').IsHermitian) → (∀ a b, DifferentiableAt ℝ (fun θ' => K θ' a b) θ) →
      ∃ L : E →L[ℝ] ℂ, HasFDerivAt (fun θ' => sectorMass m t (K θ') ℓ) L θ ∧
        ∀ h : E, L h = 2 * ∫ x, (if InSector (K θ) ℓ x then
            (K θ + hermOfCoord x).det ^ 2 *
              ((K θ + hermOfCoord x)⁻¹ * paramDeriv K θ h).trace
          else 0) ∂hermGaussian m t

end BlockBand.DeterminantScore.Sector
