module

public import BlockBand.External.Johansson.SourceStatement
public import BlockBand.DeterminantScore.SpectralConvexity
public import BlockBand.DeterminantScore.Statements

/-!
# Johansson's formula (2.18): definitions and intermediate statements

The explicit objects of the proof of Johansson's correlation kernel formula (2.18) for a
GUE matrix with external source, and the statements of its intermediate steps.

* the explicit objects of the proof: `p_S` (`gaussKernel`), `E(λ, d/S)` (`expDet`), the ordered profile
  `Φ_N` (`orderedProfile`), the Lagrange basis, the inverse heat transform `T` (`heatInv`), the
  biorthogonal polynomials `q_j = T ℓ_j`, the real kernel `K(u,v) = Σ_j p_S(u - d_j) q_j(v)`
  (`sourceKernel`) and its determinants;
* the intermediate statements of the proof.

Every `…Statement` here is **proved** (by the corresponding `…_holds` theorem). None is a
hypothesis of `sourceContract_holds`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.Johansson

open MeasureTheory ProbabilityTheory Polynomial
open BlockBand.External.Johansson
open BlockBand.DeterminantScore.SpectralConvexity (vandermonde weylChamber)
open scoped ENNReal NNReal BigOperators

/-!
## Explicit objects
-/

/-- `p_S(x - a) = (2πS)^{-1/2} e^{-(x-a)²/(2S)}`, the `N(a, S)` density. -/
def gaussKernel (S : ℝ≥0) (a x : ℝ) : ℝ := gaussianPDFReal a S x

/-- `E(λ, d/S) = det[e^{λ_i d_j / S}]`. -/
def expDet {n : ℕ} (S : ℝ≥0) (d lam : Fin n → ℝ) : ℝ :=
  (Matrix.of fun i j => Real.exp (lam i * d j / (S : ℝ))).det

/-- The ordered profile `Φ_n(λ) = Δ(λ) E(λ, d/S) e^{-Σλ²/(2S)} / Δ(d)`. -/
def orderedProfile {n : ℕ} (S : ℝ≥0) (d lam : Fin n → ℝ) : ℝ :=
  vandermonde lam / vandermonde d * expDet S d lam *
    Real.exp (-(∑ i, lam i ^ 2) / (2 * (S : ℝ)))

/-- The Lagrange basis polynomial `ℓ_j` at the nodes `d`. -/
def lagrangeBasis {n : ℕ} (d : Fin n → ℝ) (j : Fin n) : ℝ[X] :=
  Lagrange.basis Finset.univ d j

/-- The `k`-th moment `∫ y^k dN(0,S)(y)`. -/
def gaussMoment (S : ℝ≥0) (k : ℕ) : ℝ := ∫ y, y ^ k ∂gaussianReal 0 S

/-- The inverse heat transform `T P = Σ_r (-1)^r m_{2r} D^{(2r)}_{Hasse} P`. Its value at `v` is
`∫ P(v + iy) dN(0,S)(y)`, because the odd moments vanish. -/
def heatInv (S : ℝ≥0) (P : ℝ[X]) : ℝ[X] :=
  ∑ r ∈ Finset.range (P.natDegree + 1),
    Polynomial.C ((-1) ^ r * gaussMoment S (2 * r)) * hasseDeriv (2 * r) P

/-- The biorthogonal polynomials `q_j = T ℓ_j`. -/
def biorthPoly {n : ℕ} (S : ℝ≥0) (d : Fin n → ℝ) (j : Fin n) : ℝ[X] :=
  heatInv S (lagrangeBasis d j)

/-- The real kernel `K(u, v) = Σ_j p_S(u - d_j) q_j(v)`. -/
def sourceKernel {n : ℕ} (S : ℝ≥0) (d : Fin n → ℝ) (u v : ℝ) : ℝ :=
  ∑ j, gaussKernel S (d j) u * (biorthPoly S d j).eval v

/-- `det[K(x_i, x_l)]_{k×k}`. -/
def kernelMatDet {n k : ℕ} (S : ℝ≥0) (d : Fin n → ℝ) (x : Fin k → ℝ) : ℝ :=
  (Matrix.of fun i l => sourceKernel S d (x i) (x l)).det

/-- `(x, y) ↦ (x_1, …, x_k, y_1, …, y_{N-k})` as a point of `Fin N → ℝ` (`k ≤ N`). -/
def appendCast {k N : ℕ} (hk : k ≤ N) (x : Fin k → ℝ) (y : Fin (N - k) → ℝ) : Fin N → ℝ :=
  fun i => Fin.append x y (Fin.cast (by omega) i)

/-!
## Intermediate statements
-/

/-- **The ordered law**: the increasing spectrum of the law `matrixMeasure S d` has
density `C Φ_N` on the open chamber, for some `C > 0`. -/
def OrderedLawStatement : Prop :=
  ∀ {N : ℕ} (S : ℝ≥0), 0 < S → ∀ d : Fin N → ℝ, StrictMono d →
    ∃ C : ℝ, 0 < C ∧ ∀ g : (Fin N → ℝ) → ℝ≥0∞, Measurable g →
      ∫⁻ A, g (spectralTuple (Equiv.refl (Fin N)).toEmbedding A) ∂matrixMeasure S d =
        ENNReal.ofReal C * ∫⁻ lam in weylChamber N, g lam * ENNReal.ofReal (orderedProfile S d lam)

/-- **Positivity of the profile**, pointwise on the open chamber. -/
def ProfileNonnegStatement : Prop :=
  ∀ {N : ℕ} (S : ℝ≥0), 0 < S → ∀ d : Fin N → ℝ, StrictMono d →
    ∀ lam ∈ weylChamber N, 0 ≤ orderedProfile S d lam

/-- **Biorthogonality**: `∫ p_S(u - d_k) q_j(u) du = δ_jk`, with the
integrability of every product `p_S(· - d_k) q_j`. -/
def BiorthogonalStatement : Prop :=
  ∀ {N : ℕ} (S : ℝ≥0), 0 < S → ∀ d : Fin N → ℝ, StrictMono d → ∀ j k : Fin N,
    Integrable (fun u => gaussKernel S (d k) u * (biorthPoly S d j).eval u) ∧
      ∫ u, gaussKernel S (d k) u * (biorthPoly S d j).eval u = if j = k then 1 else 0

/-- **Factorization**:
`det[K(x_i, x_l)]_{N×N} = Δ(x)/Δ(d) · det[p_S(x_i - d_j)]`, for every `x`. -/
def KernelFactorStatement : Prop :=
  ∀ {N : ℕ} (S : ℝ≥0), 0 < S → ∀ d : Fin N → ℝ, StrictMono d → ∀ x : Fin N → ℝ,
    kernelMatDet S d x =
      vandermonde x / vandermonde d * (Matrix.of fun i j => gaussKernel S (d j) (x i)).det

/-- **Gaudin marginals**: for `k ≤ N` and every `x : Fin k → ℝ`,
`∫_{ℝ^{N-k}} det K_N(x, y) dy = (N-k)! det K_k(x)`, with integrability. -/
def KernelMarginalStatement : Prop :=
  ∀ {N : ℕ} (S : ℝ≥0), 0 < S → ∀ d : Fin N → ℝ, StrictMono d → ∀ {k : ℕ} (hk : k ≤ N),
    ∀ x : Fin k → ℝ,
      Integrable (fun y : Fin (N - k) → ℝ => kernelMatDet S d (appendCast hk x y)) ∧
        ∫ y : Fin (N - k) → ℝ, kernelMatDet S d (appendCast hk x y) =
          ((N - k).factorial : ℝ) * kernelMatDet S d x

/-- **Factorial measures from the ordered law**. If the increasing
spectrum has density `f` on the open chamber, with `f` symmetric, then every factorial correlation
measure is the `1/(N-k)!`-normalized marginal of `f`. -/
def FactorialFromOrderedStatement : Prop :=
  ∀ {N : ℕ} (S : ℝ≥0) (d : Fin N → ℝ) (f : (Fin N → ℝ) → ℝ≥0∞), Measurable f →
    (∀ (σ : Equiv.Perm (Fin N)) (x : Fin N → ℝ), f (x ∘ σ) = f x) →
    (∀ g : (Fin N → ℝ) → ℝ≥0∞, Measurable g →
      ∫⁻ A, g (spectralTuple (Equiv.refl (Fin N)).toEmbedding A) ∂matrixMeasure S d =
        ∫⁻ lam in weylChamber N, g lam * f lam) →
    ∀ {k : ℕ} (hk : k ≤ N),
      factorialCorrelationMeasure S d k =
        (volume : Measure (Fin k → ℝ)).withDensity fun x =>
          ((N - k).factorial : ℝ≥0∞)⁻¹ * ∫⁻ y : Fin (N - k) → ℝ, f (appendCast hk x y)

/-- **The contour form**: the contour-integral kernel (2.18) is the real kernel
`K`, for every real `u, v` on admissible contours. -/
def ContourKernelStatement : Prop :=
  ∀ {N : ℕ}, 0 < N → ∀ (S : ℝ≥0), 0 < S → ∀ d : Fin N → ℝ, StrictMono d →
    ∀ R L : ℝ, AdmissibleContours d R L → ∀ u v : ℝ,
      kernel S d R L u v = (sourceKernel S d u v : ℂ)

/-- **The coordinate bridge**: the increasing spectrum of the law `matrixMeasure S d`
is the ordered spectrum `orderedEigs (diag d)` under the Gaussian `hermGaussian N S`. -/
def CoordinateBridgeStatement : Prop :=
  ∀ {N : ℕ} (S : ℝ≥0) (d : Fin N → ℝ) (g : (Fin N → ℝ) → ℝ≥0∞), Measurable g →
    ∫⁻ A, g (spectralTuple (Equiv.refl (Fin N)).toEmbedding A) ∂matrixMeasure S d =
      ∫⁻ x, g (BlockBand.DeterminantScore.orderedEigs
        (Matrix.diagonal fun i => (d i : ℂ)) x) ∂BlockBand.DeterminantScore.Sector.hermGaussian N S

/-- **Evaluation of the inverse heat transform** (used for biorthogonality and the contour form):
`T P (v) = ∫ P(v + iy) dN(0,S)(y)`. -/
def HeatInvEvalStatement : Prop :=
  ∀ (S : ℝ≥0) (P : ℝ[X]) (v : ℝ),
    (((heatInv S P).eval v : ℝ) : ℂ) =
      ∫ y, (P.map (algebraMap ℝ ℂ)).eval ((v : ℂ) + (y : ℂ) * Complex.I) ∂gaussianReal 0 S

/-- **Gaussian scaling of the determinant `det[p_S(x_i - d_j)]`**:
`det[p_S(x_i - d_j)] = (2πS)^{-N/2} e^{-(Σx² + Σd²)/(2S)} E(x, d/S)`. -/
def GaussDetScalingStatement : Prop :=
  ∀ {N : ℕ} (S : ℝ≥0), 0 < S → ∀ d x : Fin N → ℝ,
    (Matrix.of fun i j => gaussKernel S (d j) (x i)).det =
      (Real.sqrt (2 * Real.pi * S))⁻¹ ^ N *
        Real.exp (-(∑ i, x i ^ 2 + ∑ j, d j ^ 2) / (2 * (S : ℝ))) * expDet S d x

/-- **Line integrability**: the field `vertical_integrable` of the source statement. -/
def VerticalIntegrableStatement : Prop :=
  ∀ {N : ℕ}, 0 < N → ∀ (S : ℝ≥0), 0 < S →
    ∀ (d : Fin N → ℝ), StrictMono d → ∀ (R L : ℝ), AdmissibleContours d R L →
      ∀ (u v : ℝ) (z : ℂ), ‖z‖ = R →
        Integrable (fun y : ℝ => Complex.I *
          kernelIntegrand S d u v z ((L : ℂ)+(y : ℂ)*Complex.I))

/-- **Circle integrability**: the field `circle_integrable` of the source statement. -/
def CircleIntegrableStatement : Prop :=
  ∀ {N : ℕ}, 0 < N → ∀ (S : ℝ≥0), 0 < S →
    ∀ (d : Fin N → ℝ), StrictMono d → ∀ (R L : ℝ), AdmissibleContours d R L →
      ∀ (u v : ℝ), CircleIntegrable (verticalIntegral S d u v L) 0 R

/-!
## Defining lemmas
-/

theorem gaussKernel_nonneg (S : ℝ≥0) (a x : ℝ) : 0 ≤ gaussKernel S a x :=
  gaussianPDFReal_nonneg a S x

theorem sourceKernel_def {n : ℕ} (S : ℝ≥0) (d : Fin n → ℝ) (u v : ℝ) :
    sourceKernel S d u v = ∑ j, gaussKernel S (d j) u * (biorthPoly S d j).eval v := rfl

theorem kernelMatDet_zero {n : ℕ} (S : ℝ≥0) (d : Fin n → ℝ) (x : Fin 0 → ℝ) :
    kernelMatDet S d x = 1 := by
  simp [kernelMatDet]

theorem appendCast_apply_castLE {k N : ℕ} (hk : k ≤ N) (x : Fin k → ℝ) (y : Fin (N - k) → ℝ)
    (i : Fin k) : appendCast hk x y (Fin.castLE hk i) = x i := by
  simp only [appendCast]
  have : Fin.cast (by omega) (Fin.castLE hk i) = Fin.castAdd (N - k) i := by
    ext; simp
  rw [this, Fin.append_left]

end BlockBand.Native.Johansson
