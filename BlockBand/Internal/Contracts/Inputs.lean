module

public import BlockBand.External.NativeInputs
public import BlockBand.Statements
public import BlockBand.PointProcess.Specifications
public import BlockBand.Counting.FiniteSpectralIntensity
public import BlockBand.Counting.PSSSPhysicalCounting

/-!
# Statements of the analytic inputs

Definitions only: the statements of the Gaussian calculus lemmas, the projected Wegner and
singular-log lemmas, the inputs on the fresh GUE block from the CEH local law, the PSSS
conditional counts, the short-ring local law, mean density and stationarity, and the
external-source sine-kernel theorem.

Conventions. `GUE_d(t)` has diagonal entries of variance `t`,
off-diagonal `E|A_ij|^2 = t`, realized by the concrete Johansson coordinate law.
Spectral sums over `Spec A` use the complex roots of the characteristic polynomial with
multiplicity (all real for Hermitian `A`), so no eigenbasis choice enters a statement.
Matrix norms are the Euclidean operator norm (`Matrix.Norms.L2Operator`), as in the CEH
source files.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Internal.Contracts.Inputs

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.External
open scoped ENNReal NNReal ContDiff ComplexOrder Matrix.Norms.L2Operator

/-!
## 1. Gaussian calculus: multivariate Gaussian identities and the Poincaré inequality
-/

/-- The centered independent real Gaussian product law on `ι → ℝ`; coordinate `i` has
variance `v i` (zero allowed in the definition). Every real-coordinate Gaussian vector of the paper (matrix
entries split into real and imaginary parts) is of this form. -/
def gaussianProduct {ι : Type} [Fintype ι] (v : ι → ℝ≥0) : Measure (ι → ℝ) :=
  Measure.pi (fun i => gaussianReal 0 (v i))

/-- The `i`-th partial derivative of a real test function. -/
def coordPartial {ι : Type} [DecidableEq ι] (φ : (ι → ℝ) → ℝ) (i : ι) (x : ι → ℝ) : ℝ :=
  deriv (fun s => φ (Function.update x i s)) (x i)

/-- Standard distributional weak partial derivative in coordinate `i` on `ι → ℝ`:
`f` and `g` are locally Lebesgue integrable and `∫ ∂ᵢφ • f = -∫ φ • g` for every smooth
compactly supported real test `φ`. This is the multivariate form of
`Model.Construction.HasRealWeakDerivative`. -/
def HasWeakCoordPartial {ι : Type} [Fintype ι] [DecidableEq ι] {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (i : ι) (f g : (ι → ℝ) → E) : Prop :=
  LocallyIntegrable f volume ∧ LocallyIntegrable g volume ∧
    ∀ φ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, coordPartial φ i x • f x) = -(∫ x, φ x • g x)

/-- **Gaussian integration by parts**, real clause `E[X f] = t E[∂_X f]` for `f` a locally
weakly differentiable function of the whole Gaussian vector. Law: `gaussianProduct v` on
`ι → ℝ`, any finite `ι`. Hypotheses: a weak partial derivative in the coordinate used, and
Gaussian integrability of `f`, of that derivative and of the coordinate product.
Target: any complete real normed space.
Every coordinate other than the differentiated one
has positive variance: with another degenerate coordinate the law is singular and a
Lebesgue weak derivative carries no information on its support, so the identity would fail
(e.g.
`v = (1,0)`, `f = x₀`, `g = 1` off `{x₁ = 0}` and `0` on it).
The differentiated
coordinate may be degenerate (both sides vanish).
-/
def MultivariateGaussianIBP : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (v : ι → ℝ≥0) (E : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (i : ι) (f g : (ι → ℝ) → E),
    (∀ j, j ≠ i → 0 < v j) → HasWeakCoordPartial i f g →
    Integrable f (gaussianProduct v) → Integrable g (gaussianProduct v) →
    Integrable (fun x => x i • f x) (gaussianProduct v) →
    (∫ x, x i • f x ∂gaussianProduct v) = (v i : ℝ) • ∫ x, g x ∂gaussianProduct v

/-- **Gaussian integration by parts** for a circular coordinate `Z = X_a + i X_b`
of variance `t` inside the whole Gaussian vector:
`X_a, X_b` are two distinct coordinates of
variance `t/2` (all other coordinates of positive variance, as in the real clause), `f` is
complex valued, and `∂_{Z̄} = (∂_a + i∂_b)/2`, `∂_Z = (∂_a - i∂_b)/2`
are the Wirtinger derivatives built from the two real weak partial derivatives. Each
identity assumes integrability of `f`, both weak derivatives and its own coordinate product.
-/
def MultivariateCircularGaussianIBP : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (v : ι → ℝ≥0) (a b : ι) (t : ℝ≥0),
    (∀ j, j ≠ a → j ≠ b → 0 < v j) → a ≠ b → v a = t / 2 → v b = t / 2 →
    ∀ f ga gb : (ι → ℝ) → ℂ,
      HasWeakCoordPartial a f ga → HasWeakCoordPartial b f gb →
      Integrable f (gaussianProduct v) → Integrable ga (gaussianProduct v) →
      Integrable gb (gaussianProduct v) →
      (Integrable (fun x => ((x a : ℂ) + (x b : ℂ) * Complex.I) * f x) (gaussianProduct v) →
        (∫ x, ((x a : ℂ) + (x b : ℂ) * Complex.I) * f x ∂gaussianProduct v) =
          (t : ℂ) * ∫ x, (ga x + Complex.I * gb x) / 2 ∂gaussianProduct v) ∧
      (Integrable (fun x => ((x a : ℂ) - (x b : ℂ) * Complex.I) * f x) (gaussianProduct v) →
        (∫ x, ((x a : ℂ) - (x b : ℂ) * Complex.I) * f x ∂gaussianProduct v) =
          (t : ℂ) * ∫ x, (ga x - Complex.I * gb x) / 2 ∂gaussianProduct v)

/-- The multivariate clause of the Gaussian identities: both the real and the circular
integration-by-parts identities for functions of the whole Gaussian vector. -/
def GaussianIdentitiesMultivariate : Prop :=
  MultivariateGaussianIBP ∧ MultivariateCircularGaussianIBP

/-- The covariance-weighted gradient norm `(Σᵢ vᵢ |∂ᵢ f|²)^{1/2}` of a complex function on
`ι → ℝ`, with the Fréchet partial derivatives `∂ᵢ f(x) = Df(x) eᵢ`. -/
def weightedGradientNorm {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → ℝ≥0)
    (f : (ι → ℝ) → ℂ) (x : ι → ℝ) : ℝ :=
  Real.sqrt (∑ i, (v i : ℝ) * ‖fderiv ℝ f x (Pi.single i 1)‖ ^ 2)

/-- **The Gaussian Poincaré inequality** (a remark of the paper, stated here as a lemma), with the
covariance of the real coordinates:
`Var f ≤ Σᵢ vᵢ E|∂ᵢ f|²` under `gaussianProduct v`, for complex `C¹` functions with `f` and
all partial derivatives in `L²`.
The remark gives no regularity class;
`C¹` with these
integrability hypotheses is the class used at every cited occurrence (resolvent words,
after smooth cutoff).
-/
def GaussianPoincare : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (v : ι → ℝ≥0) (f : (ι → ℝ) → ℂ),
    ContDiff ℝ 1 f → MemLp f 2 (gaussianProduct v) →
    (∀ i, MemLp (fun x => fderiv ℝ f x (Pi.single i 1)) 2 (gaussianProduct v)) →
    (∫ x, ‖f x - ∫ y, f y ∂gaussianProduct v‖ ^ 2 ∂gaussianProduct v) ≤
      ∑ i, (v i : ℝ) * ∫ x, ‖fderiv ℝ f x (Pi.single i 1)‖ ^ 2 ∂gaussianProduct v

/-- **The dimension-free Gaussian `L^p` gradient inequality** "for a fixed
moment order `p`": one absolute `C` is chosen first, then for every `p ≥ 1`, every finite
coordinate set and covariance, and every complex `C¹` function in `L^p`,
`‖f - E f‖_p ≤ C √p ‖(Σᵢ vᵢ|∂ᵢ f|²)^{1/2}‖_p`.
The explicit `√p` is the form used in the paper (`C√p/W` with `p` up to a multiple of `W`); it
is the classical Pisier–Maurey bound.
-/
def GaussianLpGradient : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (p : ℝ), 1 ≤ p → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (v : ι → ℝ≥0)
      (f : (ι → ℝ) → ℂ), ContDiff ℝ 1 f → MemLp f (ENNReal.ofReal p) (gaussianProduct v) →
        eLpNorm (fun x => f x - ∫ y, f y ∂gaussianProduct v) (ENNReal.ofReal p)
            (gaussianProduct v) ≤
          ENNReal.ofReal (C * Real.sqrt p) *
            eLpNorm (weightedGradientNorm v f) (ENNReal.ofReal p) (gaussianProduct v)

/-- The Gaussian gradient inequalities: the Poincaré inequality and the `L^p` gradient bound. -/
def GaussianGradientInequalities : Prop :=
  GaussianPoincare ∧ GaussianLpGradient

/-!
## 2. Wegner and singular-log lemmas
-/

/-- `GUE_d(t)` as a law on all `d × d` complex matrices (supported on
Hermitian matrices): the concrete Johansson coordinate law with total entry variance `t`. -/
def gueMatrixLaw (d : ℕ) (t : ℝ≥0) : Measure (Matrix (Fin d) (Fin d) ℂ) :=
  (Johansson.coordinateMeasure d t).map (fun z => (Johansson.gaussianMatrix z).1)

/-- Model data of the projected Wegner lemma: random diagonal blocks `A_j` (`W × W`), a random
Hermitian deformation `D` and a random positive semidefinite absorber `Y` on `ℂ^{kW}`
(sites `(j, a) : Fin k × Fin W`). The law, independence and estimates are not fields. -/
structure BlockModel (k W : ℕ) where
  Ω : Type
  [mΩ : MeasurableSpace Ω]
  P : Measure Ω
  [prob : IsProbabilityMeasure P]
  A : Ω → Fin k → Matrix (Fin W) (Fin W) ℂ
  D : Ω → Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ
  Y : Ω → Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ
  measurable_A : Measurable A
  measurable_D : Measurable D
  measurable_Y : Measurable Y
  hermitian_A : ∀ w j, (A w j).IsHermitian
  hermitian_D : ∀ w, (D w).IsHermitian
  posSemidef_Y : ∀ w, (Y w).PosSemidef

attribute [instance] BlockModel.mΩ BlockModel.prob

/-- The direct sum `⊕_j A_j`. -/
def BlockModel.blockSum {k W : ℕ} (M : BlockModel k W) (w : M.Ω) :
    Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ :=
  fun x y => if x.1 = y.1 then M.A w x.1 x.2 y.2 else 0

/-- `H = D + ⊕_j A_j`. -/
def BlockModel.H {k W : ℕ} (M : BlockModel k W) (w : M.Ω) :
    Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ :=
  M.D w + M.blockSum w

/-- The hypotheses of the projected Wegner lemma on the law: the blocks are independent,
each `GUE_W(c/W)`, and `(D, Y)` is jointly independent of the block family. -/
def BlockModel.IsIndependent {k W : ℕ} (M : BlockModel k W) (c : ℝ) : Prop :=
  (∀ j, HasLaw (fun w => M.A w j) (gueMatrixLaw W (Real.toNNReal (c / W))) M.P) ∧
    iIndepFun (fun j w => M.A w j) M.P ∧
    IndepFun (fun w => (M.D w, M.Y w)) M.A M.P

/-- The single-block hypothesis of the projected Wegner lemma ("for a single block `j`, it
suffices that `D` and `Γ` are independent of `A_j`"): `A_j ~ GUE_W(c/W)` is independent of
`(D, Y)` together with the other blocks; nothing is assumed about the other blocks' laws. -/
def BlockModel.IsFreshBlock {k W : ℕ} (M : BlockModel k W) (c : ℝ) (j : Fin k) : Prop :=
  HasLaw (fun w => M.A w j) (gueMatrixLaw W (Real.toNNReal (c / W))) M.P ∧
    IndepFun (fun w => M.A w j)
      (fun w => (M.D w, M.Y w, fun i => if i = j then (0 : Matrix (Fin W) (Fin W) ℂ)
        else M.A w i)) M.P

/-- The spatial projection `P_B` onto a union `B` of blocks. -/
def blockProjector {k W : ℕ} (B : Finset (Fin k)) : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ :=
  Matrix.diagonal (fun x => if x.1 ∈ B then 1 else 0)

/-- `G = (H - e + iΓ + iη I)⁻¹` with absorber `Γ = Y`. -/
def BlockModel.absorbedResolvent {k W : ℕ} (M : BlockModel k W) (e η : ℝ) (w : M.Ω) :
    Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ :=
  (M.H w - (e : ℂ) • (1 : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ) + Complex.I • M.Y w +
    ((η : ℂ) * Complex.I) • (1 : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ))⁻¹

/-- `-Im Tr P_B G`. -/
def BlockModel.projectedDensity {k W : ℕ} (M : BlockModel k W) (B : Finset (Fin k))
    (e η : ℝ) (w : M.Ω) : ℝ :=
  -(Matrix.trace (blockProjector B * M.absorbedResolvent e η w)).im

/-- **The projected Wegner estimate.** One absolute
`C` (the PSSS constant;
`K_c = C/√c`) is chosen first.
For every `k`, `W ≥ 1`, `c > 0`,
every model with independent `GUE_W(c/W)` blocks and `(D, Γ)` independent of them (any
norm, possibly random), every real `e`, `η > 0` and union `B` of blocks:
`E[-Im Tr P_B G] ≤ π K_c W |B|` (with integrability).
Clause 2 is the single-block
version under `IsFreshBlock`.
Clause 3 is the boundary-value (Fatou) version
`E liminf_{η↓0} (-Im Tr P_B G_η) ≤ π K_c W |B|`; clause 4 is its single-block version.
-/
def ProjectedWegner : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (k W : ℕ), 0 < W → ∀ (c : ℝ), 0 < c → ∀ M : BlockModel k W,
      (M.IsIndependent c → ∀ (e η : ℝ), 0 < η → ∀ B : Finset (Fin k),
        Integrable (M.projectedDensity B e η) M.P ∧
          (∫ w, M.projectedDensity B e η w ∂M.P) ≤
            Real.pi * (C / Real.sqrt c) * (W : ℝ) * (B.card : ℝ)) ∧
      (∀ j : Fin k, M.IsFreshBlock c j → ∀ (e η : ℝ), 0 < η →
        Integrable (M.projectedDensity {j} e η) M.P ∧
          (∫ w, M.projectedDensity {j} e η w ∂M.P) ≤
            Real.pi * (C / Real.sqrt c) * (W : ℝ)) ∧
      (M.IsIndependent c → ∀ (e : ℝ) (B : Finset (Fin k)),
        (∫⁻ w, Filter.liminf (fun η => ENNReal.ofReal (M.projectedDensity B e η w))
            (𝓝[>] (0 : ℝ)) ∂M.P) ≤
          ENNReal.ofReal (Real.pi * (C / Real.sqrt c) * (W : ℝ) * (B.card : ℝ))) ∧
      (∀ j : Fin k, M.IsFreshBlock c j → ∀ e : ℝ,
        (∫⁻ w, Filter.liminf (fun η => ENNReal.ofReal (M.projectedDensity {j} e η w))
            (𝓝[>] (0 : ℝ)) ∂M.P) ≤
          ENNReal.ofReal (Real.pi * (C / Real.sqrt c) * (W : ℝ)))

/-- `Σ_{λ ∈ Spec A} f(λ)` with multiplicity, through the complex characteristic roots. -/
def spectralSum {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (f : ℝ → ℝ) : ℝ :=
  (A.charpoly.roots.map (fun z => f z.re)).sum

/-- The singular log statistic `½ Σ_λ log(1 + a²/(λ-e)²)`. (At an eigenvalue `λ = e` the
summand is `0` by Lean's convention; such configurations are null under the models used.) -/
def singularLogStatistic {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (a e : ℝ) : ℝ :=
  (1 / 2) * spectralSum A (fun l => Real.log (1 + a ^ 2 / (l - e) ^ 2))

/-- **Singular logarithmic moments.** For fixed `r > 0`, `K` and `c > 0`
there is `C_{r,K,c}` with `‖½ Σ_λ log(1 + a²/(λ-e)²)‖_{L^r} ≤ C` uniformly in real `e`, in the
(possibly random, independent) deformation `D`, in `W, k, N` with `d = kW ≤ N`, and in
`0 ≤ aN ≤ K`.
Deterministic `D` (the "conditional" form) is the special case of a constant
deformation.
-/
def SingularLogMoments : Prop :=
  ∀ (r : ℝ), 0 < r → ∀ (K c : ℝ), 0 < c → ∃ C : ℝ,
    ∀ (N k W : ℕ), 0 < W → k * W ≤ N → ∀ M : BlockModel k W, M.IsIndependent c →
      ∀ (e a : ℝ), 0 ≤ a → a * (N : ℝ) ≤ K →
        eLpNorm (fun w => singularLogStatistic (M.H w) a e) (ENNReal.ofReal r) M.P ≤
          ENNReal.ofReal C

/-- `B_a(X; Q) = log |det(X - e + iaQ) / det(X - e)|` (Lean conventions `x/0 = 0`,
`log 0 = 0` at singular configurations). -/
def passiveLog {ι : Type} [Fintype ι] [DecidableEq ι] (X Q : Matrix ι ι ℂ) (a e : ℝ) : ℝ :=
  Real.log ‖(X - (e : ℂ) • (1 : Matrix ι ι ℂ) + ((a : ℂ) * Complex.I) • Q).det /
    (X - (e : ℂ) • (1 : Matrix ι ι ℂ)).det‖

/-- **The passive logarithm lemma.** Clause 1 (the passive log formula): in the setting of
`SingularLogMoments` with `Y ⪰ 0` independent of the blocks jointly
with `D`, fixed `0 ⪯ Q ⪯ I`, fixed real `e` and `a ≥ 0`, almost surely the Cauchy integrand
is integrable and `B_a(H+iY;Q) = ∫ B_a(H+tY;Q) dt/(π(1+t²)) ≥ 0`.
Clause 2 (the partial log bound): for every Hermitian `A` with `A - e` invertible,
`0 ≤ B_a(A;Q) ≤ B_a(A;I) = ½ Σ_λ log(1+a²/(λ-e)²)`.
Clause 3:
`‖B_a(H+iY;Q)‖_r ≤ C_{r,K,c}`
when `aN ≤ K`, uniformly in `D, Y, Q` and `d = kW ≤ N`.
-/
def PassiveLog : Prop :=
  (∀ (k W : ℕ), 0 < W → ∀ (c : ℝ), 0 < c → ∀ M : BlockModel k W, M.IsIndependent c →
    ∀ Q : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ, Q.PosSemidef → (1 - Q).PosSemidef →
      ∀ (e a : ℝ), 0 ≤ a →
        ∀ᵐ w ∂M.P,
          Integrable (fun t : ℝ =>
            passiveLog (M.H w + (t : ℂ) • M.Y w) Q a e / (Real.pi * (1 + t ^ 2))) ∧
          passiveLog (M.H w + Complex.I • M.Y w) Q a e =
            (∫ t : ℝ, passiveLog (M.H w + (t : ℂ) • M.Y w) Q a e / (Real.pi * (1 + t ^ 2))) ∧
          0 ≤ passiveLog (M.H w + Complex.I • M.Y w) Q a e) ∧
  (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A Q : Matrix ι ι ℂ), A.IsHermitian →
    Q.PosSemidef → (1 - Q).PosSemidef → ∀ (e a : ℝ), 0 ≤ a →
      (A - (e : ℂ) • (1 : Matrix ι ι ℂ)).det ≠ 0 →
        0 ≤ passiveLog A Q a e ∧ passiveLog A Q a e ≤ passiveLog A 1 a e ∧
          passiveLog A 1 a e = singularLogStatistic A a e) ∧
  (∀ (r : ℝ), 0 < r → ∀ (K c : ℝ), 0 < c → ∃ C : ℝ,
    ∀ (N k W : ℕ), 0 < W → k * W ≤ N → ∀ M : BlockModel k W, M.IsIndependent c →
      ∀ Q : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ, Q.PosSemidef → (1 - Q).PosSemidef →
        ∀ (e a : ℝ), 0 ≤ a → a * (N : ℝ) ≤ K →
          eLpNorm (fun w => passiveLog (M.H w + Complex.I • M.Y w) Q a e)
            (ENNReal.ofReal r) M.P ≤ ENNReal.ofReal C)

/-!
## 3. Inputs from the CEH local law and PSSS
-/

/-!
### 3a. CEH for the fresh GUE block
-/

/-- The normalized GUE `GUE_N(1/N)` as a law on the CEH Hermitian sample space. -/
def gueSourceLaw (N : ℕ) : Measure (CEH.SourceHermitian N) :=
  (Johansson.coordinateMeasure N (1 / (N : ℝ≥0))).map
    (fun z => (⟨(Johansson.gaussianMatrix z).1, (Johansson.gaussianMatrix z).2⟩ :
      CEH.SourceHermitian N))

/-- **From GUE to `CEH.WignerFamily`**: some Wigner family has exactly the normalized GUE law in
every dimension. With `λ = √s`, `F + G` (`G ~ GUE_N(s/N)`) is the CEH matrix `F + λW`.
-/
def GUEWignerFamilyAdapter : Prop :=
  ∃ Wf : CEH.WignerFamily, ∀ N : ℕ, (Wf.law N : Measure (CEH.SourceHermitian N)) = gueSourceLaw N

/-- The matrix Dyson equation at a nonreal `z`:
`M = (F - z - s⟨M⟩)⁻¹` and `Im z · Im M ≻ 0`. -/
def IsManuscriptMDE {N : ℕ} (s : ℝ) (F : CEH.SourceHermitian N) (z : ℂ)
    (M : CEH.SourceMatrix N) : Prop :=
  (F.1 - (z + (s : ℂ) * CEH.normalizedTrace M) • (1 : CEH.SourceMatrix N)) * M = 1 ∧
    ((z.im : ℂ) • CEH.imaginaryPart M).PosDef

/-- **MDE-branch identification**: for `N > 0`, `s > 0` and Hermitian `F`, an `MDEBranch` with
`λ = √s` exists; every such branch solves the matrix Dyson equation at every nonreal `z`; and
the equation has at most one solution at each nonreal `z`, so "the solution `M(z)`" of the
paper is this branch.
-/
def MDEBranchIdentification : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ (s : ℝ), 0 < s → ∀ F : CEH.SourceHermitian N,
    Nonempty (CEH.MDEBranch (Real.sqrt s) F) ∧
    (∀ M : CEH.MDEBranch (Real.sqrt s) F, ∀ z : ℂ, z.im ≠ 0 →
      IsManuscriptMDE s F z (M.matrix z)) ∧
    (∀ z : ℂ, z.im ≠ 0 → ∀ M₁ M₂ : CEH.SourceMatrix N,
      IsManuscriptMDE s F z M₁ → IsManuscriptMDE s F z M₂ → M₁ = M₂)

/-- **The external local law** in the normalization of the paper: Theorem 2.3 of
Cipolloni–Erdős–Henheik (CEH) for `A = F + G`, `G ~ GUE_N(s/N)`, i.e. the CEH statements at the
GUE family with `λ = √s`, `κ = A`.
Fixed `A, C` (`s^{-1/2}‖F‖ ≤ C N^A`) and fixed `ε, δ, D` precede `N₀`;
`s > 0`, `F`, `z` in the domain `N|Im z|ρ_s ≥ N^ε`, `|z| ≤ √s N^{A+1/ε}`, vectors and `B` are
after `N₀`.
The bad events (loss `N^δ`, failure `N^{-D}`) are those of CEH and keep
`Γ(z)` on the right side. This is the CEH averaged law for the fresh GUE block.
-/
def ExternalLocalGUE : Prop :=
  ∀ (A C : ℝ) (ε δ D : ℝ), 0 < ε → 0 < δ → 0 < D →
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ (s : ℝ), 0 < s →
      ∀ F : CEH.SourceHermitian N, (Real.sqrt s)⁻¹ * ‖F.1‖ ≤ C * (N : ℝ) ^ A →
        ∀ (M : CEH.MDEBranch (Real.sqrt s) F) (z : ℂ), CEH.InLocalLawDomain M A ε z →
          (∀ x y : Fin N → ℂ,
            gueSourceLaw N (CEH.isotropicBadEvent M x y z δ) ≤ ENNReal.ofReal ((N : ℝ) ^ (-D))) ∧
          (∀ B : CEH.SourceMatrix N,
            gueSourceLaw N (CEH.averagedBadEvent M B z δ) ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)))

/-- The regularity hypotheses of the external-source ETH theorem on a window `(E₀ - r, E₀ + r)`: the
boundary values `M_s(E) = lim_{η↓0} M(E + iη)` exist there, are differentiable with
`‖M_s'‖ ≤ K` (hence `|m_s'| ≤ K`), `‖M_s‖ ≤ K`, `Im m_s ≥ 1/K` and `|1 - s⟨M_s²⟩| ≥ 1/K`. -/
def RegularWindow {N : ℕ} {s : ℝ} {F : CEH.SourceHermitian N}
    (M : CEH.MDEBranch (Real.sqrt s) F) (E₀ r K : ℝ) : Prop :=
  ∃ Mb : ℝ → CEH.SourceMatrix N,
    (∀ E ∈ Ioo (E₀ - r) (E₀ + r),
      Tendsto (fun η : ℝ => M.matrix ((E : ℂ) + (η : ℂ) * Complex.I)) (𝓝[>] 0) (𝓝 (Mb E))) ∧
    DifferentiableOn ℝ Mb (Ioo (E₀ - r) (E₀ + r)) ∧
    ∀ E ∈ Ioo (E₀ - r) (E₀ + r),
      ‖deriv Mb E‖ ≤ K ∧ ‖Mb E‖ ≤ K ∧ 1 / K ≤ (CEH.normalizedTrace (Mb E)).im ∧
        1 / K ≤ ‖1 - (s : ℂ) * CEH.normalizedTrace (Mb E * Mb E)‖

/-- The ETH bad event: some pair of eigenvalues in
`[E₀ - h, E₀ + h]`, `h = N^{-1+β}`, has overlap error above `N^ε · N^{-1/2}`. -/
def ethBadEvent {N : ℕ} {s : ℝ} {F : CEH.SourceHermitian N}
    (M : CEH.MDEBranch (Real.sqrt s) F) (spacing : CEH.TypicalSpacing M)
    (sel : CEH.EigenpairSelection N) (E₀ β ξ ε : ℝ) (J : CEH.SourceMatrix N) :
    Set (CEH.SourceHermitian N) :=
  {W | ∃ i j : Fin N,
    sel.eigenvalue (CEH.deformedHermitian (Real.sqrt s) F W) i ∈
        Icc (E₀ - (N : ℝ) ^ (-1 + β)) (E₀ + (N : ℝ) ^ (-1 + β)) ∧
    sel.eigenvalue (CEH.deformedHermitian (Real.sqrt s) F W) j ∈
        Icc (E₀ - (N : ℝ) ^ (-1 + β)) (E₀ + (N : ℝ) ^ (-1 + β)) ∧
    (N : ℝ) ^ ε * (N : ℝ) ^ (-(1 : ℝ) / 2) <
      ‖CEH.sourceMatrixElement J
          (sel.eigenvector (CEH.deformedHermitian (Real.sqrt s) F W) i)
          (sel.eigenvector (CEH.deformedHermitian (Real.sqrt s) F W) j) -
        (if i = j then
          CEH.normalizedTrace (CEH.gammaMatrix (M.matrix (CEH.inflatedSpectralPoint spacing ξ
            (sel.eigenvalue (CEH.deformedHermitian (Real.sqrt s) F W) i))) * J)
        else 0)‖}

/-- **External eigenstate thermalization (ETH)**, with `s` in a fixed compact subset of
`(0,∞)`. Fixed data first: `A, C` (`s^{-1/2}‖F‖ ≤ C N^A`),
`[sLo, sHi] ⊂ (0,∞)`, the window radius `r` and the regularity constant `K`.
Then a
sufficiently small `β₀ > 0`; then any `0 < ξ < β < β₀` and stochastic-domination exponents
`ε, D`; then `N₀`.
Uniformly in `N ≥ N₀`, `s ∈ [sLo,sHi]`, `F`, the branch `M`, `E₀` with
`RegularWindow M E₀ r K`, the typical spacing `η_f` (`N η_f ρ_s(x + iη_f) = 1`), the
measurable eigenpair selection and Hermitian `J` with `‖J‖ ≤ 1`: under `G ~ GUE_N(s/N)`,
`P(∃ i j, λ_i, λ_j ∈ [E₀ - h, E₀ + h], |u_i*Ju_j - δ_ij⟨Γ(λ_i + iN^ξ η_f(λ_i))J⟩| > N^{ε-1/2})
≤ N^{-D}`.
-/
def ExternalETH : Prop :=
  ∀ (A C sLo sHi r K : ℝ), 0 < sLo → sLo ≤ sHi → 0 < r → 0 < K →
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ (β ξ : ℝ), 0 < ξ → ξ < β → β < β₀ → ∀ (ε D : ℝ), 0 < ε → 0 < D →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ s ∈ Icc sLo sHi, ∀ F : CEH.SourceHermitian N,
        (Real.sqrt s)⁻¹ * ‖F.1‖ ≤ C * (N : ℝ) ^ A →
        ∀ (M : CEH.MDEBranch (Real.sqrt s) F) (E₀ : ℝ), RegularWindow M E₀ r K →
        ∀ (spacing : CEH.TypicalSpacing M) (sel : CEH.EigenpairSelection N)
          (J : CEH.SourceMatrix N), J.IsHermitian → ‖J‖ ≤ 1 →
            gueSourceLaw N (ethBadEvent M spacing sel E₀ β ξ ε J) ≤
              ENNReal.ofReal ((N : ℝ) ^ (-D))

/-!
### 3b. PSSS conditional on bonds
-/

/-- **Block-GUE count conditional on a deformation** (the PSSS bound for generic block-GUE
noise). One absolute `C > 0` first (the PSSS constant).
On any probability space, let `G` be
block-diagonal Gaussian noise with `t^{-1/2}G` exactly the normalized PSSS block-GUE law
(blocks `GUE_{d_j}(t/d_j)`, any number of blocks, any sizes), and `D` a random Hermitian
deformation independent of `G` (any norm).
Then for every closed `[a,b]` and `r ≥ 1` the
factorial moment of the eigenvalue count of `D + G` is integrable and at most
`(C/√t · Σ_j d_j · (b-a))^r`.
-/
def ConditionalBlockGUECount : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (k : ℕ) (d : Fin k → ℕ) (hd : ∀ j, 0 < d j) (t : ℝ), 0 < t →
      ∀ (G D : Ω → PSSS.HermitianMatrix (PSSS.BlockGUE.Index d)),
        Measurable G → Measurable D →
        HasLaw (fun w => ((Real.sqrt t)⁻¹ : ℂ) • (G w).1)
          ((PSSS.BlockGUE.canonicalMatrixMeasure d hd).map Subtype.val) P →
        IndepFun D G P →
        ∀ (a b : ℝ), a ≤ b → ∀ r : ℕ, 1 ≤ r →
          Integrable (PSSS.factorialCount
            (fun w => PSSS.eigenCount ⟨(D w).1 + (G w).1, (D w).2.add (G w).2⟩ (Icc a b)) r) P ∧
          (∫ w, PSSS.factorialCount
              (fun w => PSSS.eigenCount ⟨(D w).1 + (G w).1, (D w).2.add (G w).2⟩ (Icc a b)) r w
              ∂P) ≤
            (C / Real.sqrt t * ((∑ j, d j : ℕ) : ℝ) * (b - a)) ^ r

/-- Sites of the physical ring lying in a set `R` of blocks. -/
abbrev BlockSites (p : Parameters) (R : Finset (ZMod p.n)) := {x : p.Site // x.1 ∈ R}

/-- The ring matrix with the diagonal blocks of `R` removed: every bond and every other
block (the conditioning data). -/
def withoutFreshBlocks (p : Parameters) (R : Finset (ZMod p.n)) (H : p.SiteMatrix) :
    p.SiteMatrix :=
  fun x y => if x.1 = y.1 ∧ x.1 ∈ R then 0 else H x y

/-- The eigenvalue count of `H_RR + Φ(rest)` on a set `J`, for the Hermitian version of the
physical sample. -/
def subsystemCount (p : Parameters) (R : Finset (ZMod p.n))
    (Φ : p.SiteMatrix → PSSS.HermitianMatrix (BlockSites p R)) (J : Set ℝ)
    (H : p.SiteMatrix) : ℕ :=
  PSSS.eigenCount
    ⟨((p.physicalHermitianVersion H).1.submatrix Subtype.val Subtype.val) +
        (Φ (withoutFreshBlocks p R (p.physicalHermitianVersion H).1)).1,
      ((p.physicalHermitianVersion H).2.submatrix Subtype.val).add
        (Φ (withoutFreshBlocks p R (p.physicalHermitianVersion H).1)).2⟩ J

/-- **The PSSS bound conditional on the bonds, for the physical ring** (the conditioning of the
proof of the counting theorem). One absolute `C > 0` first.
For every admissible `p`, every realization of the physical
law, every set `R` of blocks, and every measurable Hermitian deformation `Φ` of the
conditioning data (bonds and blocks outside `R`): the count of `H_RR + Φ(rest)` on
`[a,b]` has integrable factorial moments of order `r ≥ 1`, at most
`(C/√c · |R|W · (b-a))^r`.
-/
def PhysicalBlockConditionalCount : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (p : Parameters) (model : p.GaussianRingModel) (R : Finset (ZMod p.n))
      (Φ : p.SiteMatrix → PSSS.HermitianMatrix (BlockSites p R)), Measurable Φ →
      ∀ (a b : ℝ), a ≤ b → ∀ r : ℕ, 1 ≤ r →
        Integrable (PSSS.factorialCount (subsystemCount p R Φ (Icc a b)) r)
            (model.law : Measure p.SiteMatrix) ∧
          (∫ H, PSSS.factorialCount (subsystemCount p R Φ (Icc a b)) r H
              ∂(model.law : Measure p.SiteMatrix)) ≤
            (C / Real.sqrt p.c * ((R.card * p.W : ℕ) : ℝ) * (b - a)) ^ r

/-!
## 4. Short ring, mean density and stationarity
-/

/-- The short-ring variance profile `S = C ⊗ J_W` on `Fin (mW)`, `C_kl = c δ_kl + b 1{l=k±1}`
(cyclic, `c = 1 - 2b`), in row-major block coordinates `x = kW + a`. -/
def shortRingProfile (b : ℝ) (m W : ℕ) : Matrix (Fin (m * W)) (Fin (m * W)) ℝ :=
  fun x y =>
    if x.val / W = y.val / W then (1 - 2 * b) / W
    else if y.val / W = (x.val / W + 1) % m ∨ x.val / W = (y.val / W + 1) % m then b / W
    else 0

/-- The polynomial control function of [ER, Example 2.6]:
`Υ_η(x,y) = (ℓη)⁻¹ (1 + d(x,y)/ℓ)^{-D}`, `ℓ = min(N, W/√η)`, `d` the cyclic distance. -/
def polynomialControl (N W : ℕ) (D : ℝ) : ℝ → Matrix (Fin N) (Fin N) ℝ :=
  fun η x y =>
    (ErdosRiabov.localizationLength N W η * η)⁻¹ *
      (1 + (ErdosRiabov.cyclicDistance N x y : ℝ) / ErdosRiabov.localizationLength N W η) ^ (-D)

/-- **Admissibility of the short-ring control** for the Erdős–Riabov (ER) local law, in the
corrected form. Fixed first: `b ∈ (0,1/2)`, the bulk-domain constants `δ₀, κ, C₀` of
[ER, Definition 2.4] and `D ≥ 6`.
Then constants `C₁, c₂, D'` (depending only on these)
such that for every parameter set with those domain constants and admissibility
constants at least `C₁, c₂, D'` (each clause is monotone in them), and every `m ≥ 4` of
either parity and `W ≥ 1`, `Υ` is an admissible control of `S = C ⊗ J_W`: all seven clauses
of [ER, Definition 2.4] with fixed constants, no logarithmic loss.
-/
def ShortRingAdmissibility : Prop :=
  ∀ (b : ℝ), 0 < b → b < 1 / 2 → ∀ (δ₀ κ C₀ : ℝ), 0 < δ₀ → 0 < κ → 1 ≤ C₀ →
    ∀ D : ℝ, 6 ≤ D →
      ∃ C₁ c₂ D' : ℝ, 1 ≤ C₁ ∧ 0 < c₂ ∧ 0 < D' ∧
        ∀ p : ErdosRiabov.ModelParameters, p.delta0 = δ₀ → p.kappa = κ → p.C0 = C₀ →
          C₁ ≤ p.C1 → c₂ ≤ p.c2 → D' ≤ p.DPrime →
          ∀ (m W : ℕ), 4 ≤ m → 0 < W →
            ErdosRiabov.AdmissibleControl p (m * W) W (shortRingProfile b m W)
              (polynomialControl (m * W) W D)

/-- Cyclic site distance `|x - y|_N` of the physical ring, through the row-major index. -/
def siteDistance (p : Parameters) (x y : p.Site) : ℕ :=
  let d := max (p.siteIndex x) (p.siteIndex y) - min (p.siteIndex x) (p.siteIndex y)
  min d (p.N - d)

/-- The polynomial control at sites of the physical ring (`N = nW`). -/
def siteControl (p : Parameters) (D η : ℝ) (x y : p.Site) : ℝ :=
  (ErdosRiabov.localizationLength p.N p.W η * η)⁻¹ *
    (1 + (siteDistance p x y : ℝ) / ErdosRiabov.localizationLength p.N p.W η) ^ (-D)

/-- **The short-ring local law** (the external band local law, in corrected form, with the domain
restriction `|z| ≤ C₀`, `δ₀ < ζ₀`, `m ≥ 4`): for a ring with the law of this
paper with `m = p.n ≥ 4` blocks (`N = mW`) and bond `b`, `W² ≥ N^{1+ζ₀}`, `0 < δ₀ < ζ₀`, bulk energies
`|e| ≤ 2 - κ`, `η ≥ N^{-1+δ₀}` and `|e + iη| ≤ C₀`, for every fixed `D ≥ 6`:
`|G_xy(e+iη) - m_sc(e+iη)δ_xy| ≺ {(ℓη)⁻¹(1 + |x-y|_N/ℓ)^{-D}}^{1/2}`, i.e. for all
`ε, D₁ > 0` there is `N₀` with failure probability `≤ N^{-D₁}` for `N ≥ N₀`, uniformly in
`m, W`, the realization, `e, η` and the sites.
`m_sc` is the semicircle Stieltjes transform
of the ER source (`semicircleM`).
-/
def ShortRingLocalLaw : Prop :=
  ∀ (b ζ₀ δ₀ κ C₀ : ℝ), 0 < b → b < 1 / 2 → 0 < δ₀ → δ₀ < ζ₀ → 0 < κ →
    1 ≤ C₀ → ∀ D : ℝ, 6 ≤ D → ∀ (ε D₁ : ℝ), 0 < ε → 0 < D₁ →
      ∃ N₀ : ℕ, ∀ p : Parameters, p.b = b → N₀ ≤ p.N →
        (p.N : ℝ) ^ (1 + ζ₀) ≤ (p.W : ℝ) ^ 2 →
        ∀ model : p.GaussianRingModel,
        ∀ (e η : ℝ), |e| ≤ 2 - κ → (p.N : ℝ) ^ (-1 + δ₀) ≤ η →
          ‖(e : ℂ) + (η : ℂ) * Complex.I‖ ≤ C₀ →
          ∀ x y : p.Site,
            (model.law : Measure p.SiteMatrix)
              {H | (p.N : ℝ) ^ ε * Real.sqrt (siteControl p D η x y) <
                ‖(H - ((e : ℂ) + (η : ℂ) * Complex.I) • (1 : p.SiteMatrix))⁻¹ x y -
                  (if x = y then ErdosRiabov.semicircleM ((e : ℂ) + (η : ℂ) * Complex.I)
                    else 0)‖} ≤
              ENNReal.ofReal ((p.N : ℝ) ^ (-D₁))

/-- The normalized expected empirical spectral measure `E N⁻¹ Σ_α δ_{λ_α}` of the physical
law (multiplicity counted, Hermitian version of the sample). -/
def meanEmpiricalMeasure (p : Parameters) (model : p.GaussianRingModel) : Measure ℝ :=
  (p.N : ℝ≥0∞)⁻¹ •
    Counting.finiteSpectralIntensity (model.law : Measure p.SiteMatrix)
      (fun H i => Foundations.Spectral.increasingEigenvalue (p.physicalHermitianVersion H).2 i)

/-- **The critical density theorem.** Clause 1: for every
admissible parameter set and realization the normalized expected empirical measure has a
smooth (C^∞) density `ρ_{n,W}`.
Clause 2: for fixed `b, κ, T` there is `C_{b,κ,T}` such that,
uniformly for `4⌈W^{15/16}⌉ ≤ n ≤ TW` (all `W ≥ 1`), every realization and every continuous
density `ρ_{n,W}` of that measure, `|ρ_{n,W}(e) - ρ(e)| ≤ C W^{-1/32}` for `|e| ≤ 2 - κ`,
`ρ = semicircleDensity`.
The proof uses the corrected short-ring law (`ShortRingLocalLaw`); the statement is unchanged
by the correction.
-/
def CriticalDensityEstimate : Prop :=
  (∀ (p : Parameters) (model : p.GaussianRingModel), ∃ ρ : ℝ → ℝ,
      ContDiff ℝ ∞ ρ ∧ (∀ e, 0 ≤ ρ e) ∧
        meanEmpiricalMeasure p model = volume.withDensity (fun e => ENNReal.ofReal (ρ e))) ∧
  ∀ (b κ T : ℝ) (hb : 0 < b) (hb' : b < 1 / 2), 0 < κ → 0 < T → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (n W : ℕ) (hn : 4 ≤ n) (hW : 0 < W),
      4 * ⌈(W : ℝ) ^ ((15 : ℝ) / 16)⌉₊ ≤ n → (n : ℝ) ≤ T * (W : ℝ) →
      let p : Parameters := ⟨n, W, b, hn, hW, hb, hb'⟩
      ∀ (model : p.GaussianRingModel) (ρ : ℝ → ℝ), Continuous ρ →
        meanEmpiricalMeasure p model = volume.withDensity (fun e => ENNReal.ofReal (ρ e)) →
        ∀ e : ℝ, |e| ≤ 2 - κ →
          |ρ e - Parameters.semicircleDensity e| ≤ C * (W : ℝ) ^ (-(1 : ℝ) / 32)

/-- The binder pattern of "every critical subsequential marked limit" (as in
`criticalSequence_marked_weakLimit_spectrallyStationary`): a critical sequence with ratio
`τ > 0`, bond `b`, bulk energy `E² < 4`, realizations, a strictly increasing subsequence and
a weak limit of the physical marked laws. -/
def ForEveryCriticalLimit (conclusion : ProbabilityMeasure MarkedPointMeasure → Prop) : Prop :=
  ∀ (τ : ℝ) (s : CriticalSequence τ), 0 < τ → ∀ (b E : ℝ) (hb : 0 < b) (hb' : b < 1 / 2),
    E ^ 2 < 4 → ∀ (R : ∀ j, FiniteRealization (s.parameters b hb hb' j)) (φ : ℕ → ℕ),
      StrictMono φ → ∀ ν : ProbabilityMeasure MarkedPointMeasure,
        Tendsto (fun j => (R (φ j)).markedLaw E) atTop (𝓝 ν) → conclusion ν

/-- **The critical density theorem**, the consequence "every critical subsequential marked limit
has unit spectral intensity" (used in the stationarity proposition and the critical joint-law
theorem).
-/
def CriticalUnitIntensity : Prop :=
  ForEveryCriticalLimit HasUnitSpectralIntensity

/-- The critical density theorem: both the estimate and its unit-intensity consequence. -/
def CriticalDensity : Prop :=
  CriticalDensityEstimate ∧ CriticalUnitIntensity

/-- The stationarity clause: the mean spatial intensity of
every critical subsequential marked law is `du dr` (`HasUniformSpatialIntensity`). -/
def CriticalMeanSpatialIntensity : Prop :=
  ForEveryCriticalLimit HasUniformSpatialIntensity

/-- **The stationarity proposition**, all three clauses: every critical subsequential
marked law is invariant under spectral translations and simultaneous rotations of its
circle marks, and has mean spatial intensity `du dr`.
-/
def CriticalStationarity : Prop :=
  ForEveryCriticalLimit fun ν =>
    IsSpectrallyStationary ν ∧ IsMarkRotationInvariant ν ∧ HasUniformSpatialIntensity ν

/-!
## 5. The external-source sine-kernel theorem
-/

/-- The law of `F + √t G_N`, `G_N` the normalized complex GUE, for Hermitian `F`:
the concrete Johansson coordinate law at `S = t/N`, shifted by `F`. -/
def deformedGUELaw (N : ℕ) (t : ℝ≥0) (F : Matrix (Fin N) (Fin N) ℂ) (hF : F.IsHermitian) :
    Measure (Johansson.HermitianMatrix N) :=
  (Johansson.coordinateMeasure N (Johansson.sourceTime N t)).map
    (fun z => (⟨F + (Johansson.gaussianMatrix z).1, hF.add (Johansson.gaussianMatrix z).2⟩ :
      Johansson.HermitianMatrix N))

/-- Factorial correlation measure of order `k` of `F + √t G_N` (sum over ordered injective
`k`-tuples of ranks, the Johansson `N!/(N-k)!` normalization). -/
def deformedFactorialCorrelation (N : ℕ) (t : ℝ≥0) (F : Matrix (Fin N) (Fin N) ℂ)
    (hF : F.IsHermitian) (k : ℕ) : Measure (Fin k → ℝ) :=
  ∑ e : Fin k ↪ Fin N, (deformedGUELaw N t F hF).map (Johansson.spectralTuple e)

/-- The boundary MDE `M = (F - E - t⟨M⟩)⁻¹` at real `E` with `Im M ≻ 0` (the solution of the
matrix Dyson equation at `E` with positive imaginary part); `m_{F,t}(E) = ⟨M⟩`. -/
def IsBoundaryMDE {N : ℕ} (t : ℝ) (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ)
    (M : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  (F - ((E : ℂ) + (t : ℂ) * CEH.normalizedTrace M) • (1 : Matrix (Fin N) (Fin N) ℂ)) * M = 1 ∧
    (CEH.imaginaryPart M).PosDef

/-- Laplace functional `E exp(-Σ_i f(Nρ(λ_i - E)))` of the unfolded spectrum of `F + √t G_N`. -/
def unfoldedLaplace (N : ℕ) (t : ℝ≥0) (F : Matrix (Fin N) (Fin N) ℂ) (hF : F.IsHermitian)
    (E ρ : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ A, Real.exp (-(∑ i, f ((N : ℝ) * ρ *
      (Model.Construction.orderedEigenvalue A i - E)))) ∂deformedGUELaw N t F hF

/-- **The external sine theorem.** Fixed first:
`A`, `0 < tLo ≤ tHi`, `v_* > 0`, a
compact energy interval `[ELo, EHi]` and a compact rescaled window `[-L, L]`.
Then `C, N₀`
depending only on these.
For `N ≥ N₀`, Hermitian `F` with `‖F‖ ≤ N^A`, `t ∈ [tLo,tHi]`,
`E ∈ [ELo,EHi]` and the boundary MDE solution with `Im m_{F,t}(E) ≥ v_*`, `ρ = Im m/π`:
(a) there are a continuous correlation kernel `K_N` (all factorial correlations of order `k ≤ N` are
`det[K_N(x_i,x_j)] dx`) and a real conjugation `h_N` with
`|e^{-h_N(ξ)} K_N(E+ξ/(Nρ), E+ζ/(Nρ)) e^{h_N(ζ)}/(Nρ) - sin π(ξ-ζ)/(π(ξ-ζ))| ≤ C N^{-1/2}`
for `ξ, ζ ∈ [-L, L]` (diagonal by continuity);
(b) the normalized mean density at `E` is
`ρ + O(N^{-1/2})`:
`|K_N(E,E)/N - ρ| ≤ C N^{-1/2}`.
Clause (c), the local point process: for
every nonnegative `f ∈ C_c(ℝ)` the Laplace functional of the unfolded spectrum converges to
the unit sine Laplace functional, uniformly over the same class.
No limiting empirical
measure of `F` and no `N`-independent norm bound is assumed.
-/
def ExternalSine : Prop :=
  ∀ (A tLo tHi v ELo EHi L : ℝ), 0 < tLo → tLo ≤ tHi → 0 < v →
    (∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ) (hF : F.IsHermitian), ‖F‖ ≤ (N : ℝ) ^ A →
      ∀ (t : ℝ≥0), (t : ℝ) ∈ Icc tLo tHi → ∀ E ∈ Icc ELo EHi,
      ∀ M : Matrix (Fin N) (Fin N) ℂ, IsBoundaryMDE (t : ℝ) F E M →
        v ≤ (CEH.normalizedTrace M).im →
        ∃ (Kern : ℝ → ℝ → ℂ) (h : ℝ → ℝ), Continuous (Function.uncurry Kern) ∧
          (∀ k : ℕ, k ≤ N → deformedFactorialCorrelation N t F hF k =
            volume.withDensity (fun x : Fin k → ℝ =>
              ENNReal.ofReal (Matrix.det (fun i j => Kern (x i) (x j))).re)) ∧
          (∀ ξ ∈ Icc (-L) L, ∀ ζ ∈ Icc (-L) L,
            ‖Complex.exp (-(h ξ : ℂ)) *
                Kern (E + ξ / ((N : ℝ) * ((CEH.normalizedTrace M).im / Real.pi)))
                  (E + ζ / ((N : ℝ) * ((CEH.normalizedTrace M).im / Real.pi))) *
                Complex.exp (h ζ : ℂ) / ((N : ℝ) * ((CEH.normalizedTrace M).im / Real.pi)) -
              (sineKernel ξ ζ : ℂ)‖ ≤ C * (N : ℝ) ^ (-(1 : ℝ) / 2)) ∧
          ‖Kern E E / (N : ℝ) - ((CEH.normalizedTrace M).im / Real.pi : ℝ)‖ ≤
            C * (N : ℝ) ^ (-(1 : ℝ) / 2)) ∧
    ∀ f : CompactlySupportedContinuousMap ℝ ℝ, (∀ x, 0 ≤ f x) → ∀ δ : ℝ, 0 < δ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ (F : Matrix (Fin N) (Fin N) ℂ) (hF : F.IsHermitian), ‖F‖ ≤ (N : ℝ) ^ A →
        ∀ (t : ℝ≥0), (t : ℝ) ∈ Icc tLo tHi → ∀ E ∈ Icc ELo EHi,
        ∀ M : Matrix (Fin N) (Fin N) ℂ, IsBoundaryMDE (t : ℝ) F E M →
          v ≤ (CEH.normalizedTrace M).im →
          |unfoldedLaplace N t F hF E ((CEH.normalizedTrace M).im / Real.pi) f -
            sineLaplaceFunctional f| ≤ δ

end BlockBand.Internal.Contracts.Inputs
