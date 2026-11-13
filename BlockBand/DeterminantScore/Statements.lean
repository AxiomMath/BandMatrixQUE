module

public import BlockBand.Angular.FiberAngular
public import BlockBand.DeterminantScore.Sector.Statement

/-!
# The determinant score and its inputs: statements

This file states the complete determinant score theorem and the intermediate statements it is
proved from:

* `PhysicalColumnStatement`: column and Hilbert–Schmidt moments of the inverse under the pair law;
* `PhysicalRealLoopStatement`: the real-loop error bound and the good event for the spread;
* `IndexedSpectralConvexityStatement`: the fixed-inertia eigenvalue density and the weighted
  spectral variance inequality;
* `NegativeSpreadStatement`: moments of `Tr M⁻²` under the fixed-inertia sector law;
* `SignedRowSpreadStatement`: the signed row integral at a fixed minor;
* `PhysicalMinorTailStatement`: the minor tail and the inverse-spread bound;
* `DeterminantScoreStatement`: the exact score formula and its moments.

## Representation choices

No hypothesis is added and no conclusion is weakened by the following choices.

* **Sector averages** `⟨f⟩_θ` are `sectorAvg` (real `f`) and
  `sectorAvgMat` (matrix `f`, entrywise), Bochner integrals against
  `det(M)² 1{sector} dGUE_{d-1}(t)` divided by `𝔷_ℓ(v)`. All averaged quantities used here
  (`R`, `Tr R²`, `(Tr R)²`) times `det(M)²` are polynomials in `G'`, hence integrable at every
  `θ`. `R̄ = ⟨R⟩_θ` is `condInverse` in frame coordinates; "embed `R` by zero on `v`" is
  `U_v R U_v*` (`embedFrame`); norms are frame-independent. `‖·‖` on matrices is the Euclidean
  operator norm (`Matrix.Norms.L2Operator`), `‖x‖` on vectors is `l2Norm`.
* **Score.** `𝔷_ℓ` is extended from the unit sphere by degree-zero homogeneity
  (`z ↦ 𝔷_ℓ(z/‖z‖)`, `FiberAngular.normalize`), as in the angular layer (`ProjectiveStein`);
  the horizontal real gradient with `Df[h] = Re(h*∇f)`, `h ⊥ v`, is the real Fréchet derivative
  of `log 𝔷_ℓ` at `v` restricted to `h ⊥ v` (`v*h = 0`). The formula `-4R̄QK₀v` is `score`.
  The Fréchet form is what the angular Stein identities consume.
* **"Every outer-measurable unit vector `w ∈ v^⊥`"** (physical column lemma): a measurable map
  `w : OuterData → ℂ^S` with `‖w(θ)‖ = 1`, `v*w(θ) = 0` for unit `v`; `‖Rw‖` is
  `‖R U_v*w‖` (R embedded by zero on `v`). It may depend on all of `θ` (e.g. an eigenvector of
  `K`, as in the proof of the determinant score theorem), but not on `G'`.
* **The deleted row** (physical minor tail): `w(θ)` is any measurable unit eigenvector of
  `K` (frame coordinates, required where `K` is Hermitian), `μ = w*Kw`, and the minor `B` is the
  compression of `M` to `w^⊥` through any measurable frame of `w^⊥` (`IsMinorFrame`); `V_B`,
  `δ_B`, `q_B` are frame independent.
* **Interval.** `I` is a fixed compact bulk interval, `bulkInterval κ = [-2+κ, 2-κ]`, `κ > 0`.
  The paper's `I` also contains the classical locations of the ranks considered; that restriction
  is not imposed (the statements are for every compact bulk interval and every `ϑ`-bulk rank),
  which is stronger and is what the proofs give, the physical local window being stated at
  every bulk rank.
* **Uniformity.** "Uniform for `4 ≤ n ≤ TW`, both parities, adjacent pairs and deterministic
  bulk ranks" is `∀ p : Parameters, p.b = b → n ≤ T W → ∀ model, ∀ ϑ-bulk α, ∀ i, ∀ Pω, ∀ U`
  after the constants (which depend on `b, T, ϑ, κ` and the stated exponents). The
  `Parameters` binder (rather than `let p := ⟨n, W, b, …⟩`) keeps the `NeZero p.n` instance.
  The physical column lemma and the first clause of the physical minor tail state constants `C_p`
  only: there the bound is required for every `n ≥ 4` and every rank, as their proofs give.
* The negative-spread and indexed spectral convexity statements are deterministic-`K` statements
  on the coordinate space of `G_m(t)` of `Sector.Statement` (`hermGaussian`, `hermOfCoord`,
  `sectorDetSq`, `sectorMass`); the normalized law is `sectorLaw`. The paper's proof of
  indexed spectral convexity cites the Hermitian Brownian motion transition density
  (Katori–Tanemura); here only the convexity statement itself is stated.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Angular.FiberAngular BlockBand.DeterminantScore.Sector
open scoped ENNReal NNReal ContDiff Matrix.Norms.L2Operator

/-!
## Outer data, sector averages and the pair law in coarea coordinates
-/

section Outer

variable (p : Parameters) (i : ZMod p.n)

/-- Outer data `θ = (ω, E, v)`, `ω = (H_R, C, V)`. -/
abbrev OuterData := SplitState p i × ℝ × (PairSite p i → ℂ)

/-- Matrices on the frame coordinates of `v^⊥` (dimension `d - 1`). -/
abbrev FrameMatrix := Matrix (FrameIndex p) (FrameIndex p) ℂ

/-- A frame map `v ↦ U_v`. -/
abbrev FrameMap := (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ

variable {p i}

/-- `K₀ = F(E) - E` at the outer data. -/
def outerK0 (θ : OuterData p i) : PairMatrix p i :=
  physicalCoareaF θ.1.1 θ.1.2.1 θ.1.2.2 θ.2.1 - (θ.2.1 : ℂ) • 1

/-- `K = U_v* K₀ U_v` (`= QK₀Q|_{v^⊥}` in frame coordinates). -/
def outerK (U : FrameMap p i) (θ : OuterData p i) : FrameMatrix p :=
  (U θ.2.2)ᴴ * outerK0 θ * U θ.2.2

/-- `M = K + G'` (the `frameM`). -/
def outerM (U : FrameMap p i) (θ : OuterData p i) (G' : FrameMatrix p) : FrameMatrix p :=
  frameM p i U θ.1 θ.2.1 θ.2.2 G'

/-- The sector weight `det(M)² 1{N_-(M) + N_-(H_R - E) = α}` (zero-based rank). -/
def sectorWeight (α : Fin p.N) (U : FrameMap p i) (θ : OuterData p i) (G' : FrameMatrix p) :
    ℝ :=
  Complex.normSq (outerM U θ G').det *
    (if negativeCount (outerM U θ G') + negativeCount (θ.1.1 - (θ.2.1 : ℂ) • 1) = α.val
      then 1 else 0)

/-- `𝔷_ℓ(v)` as a real number (`detFactor` is finite). -/
def sectorZ (α : Fin p.N) (s : ℝ) (U : FrameMap p i) (θ : OuterData p i) : ℝ :=
  (detFactor p i α s U θ.1 θ.2.1 θ.2.2).toReal

/-- The sector average `⟨f⟩_θ` of a real function of `G'`. -/
def sectorAvg (α : Fin p.N) (s : ℝ) (U : FrameMap p i) (f : FrameMatrix p → ℝ)
    (θ : OuterData p i) : ℝ :=
  (∫ G', sectorWeight α U θ G' * f G' ∂gueMeasure (FrameIndex p) (pairTime p s)) /
    sectorZ α s U θ

/-- `⟨F⟩_θ` for a matrix function of `G'`, entrywise. -/
def sectorAvgMat (α : Fin p.N) (s : ℝ) (U : FrameMap p i) (F : FrameMatrix p → FrameMatrix p)
    (θ : OuterData p i) : FrameMatrix p :=
  Matrix.of fun a c =>
    (∫ G', (sectorWeight α U θ G' : ℂ) * F G' a c ∂gueMeasure (FrameIndex p) (pairTime p s)) /
      (sectorZ α s U θ : ℂ)

/-- `R̄ = ⟨R⟩_θ`, `R = M⁻¹`, in frame coordinates. -/
def condInverse (α : Fin p.N) (s : ℝ) (U : FrameMap p i) (θ : OuterData p i) : FrameMatrix p :=
  sectorAvgMat α s U (fun G' => (outerM U θ G')⁻¹) θ

/-- A frame matrix embedded by zero on `v`: `U_v X U_v*`. -/
def embedFrame (U : FrameMap p i) (v : PairSite p i → ℂ) (X : FrameMatrix p) : PairMatrix p i :=
  U v * X * (U v)ᴴ

/-- `Q = I - vv*`. -/
def orthProj (v : PairSite p i → ℂ) : PairMatrix p i :=
  1 - vecMulVec v (star v)

/-- The score vector `-4 R̄ Q K₀ v` of the exact determinant score. -/
def score (α : Fin p.N) (s : ℝ) (U : FrameMap p i) (θ : OuterData p i) : PairSite p i → ℂ :=
  (-4 : ℂ) • (embedFrame U θ.2.2 (condInverse α s U θ) *ᵥ
    (orthProj θ.2.2 *ᵥ (outerK0 θ *ᵥ θ.2.2)))

/-- `E♯_{α,S}[Ψ(θ, G')]`: the pair-law form of the complete coarea formula (`v*𝒟v ↦ n/2`). -/
def pairExpect (α : Fin p.N) (s : ℝ) (U : FrameMap p i) (Pω : Measure (SplitState p i))
    (Ψ : OuterData p i → FrameMatrix p → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ om, ∫⁻ E, ∫⁻ v, ∫⁻ G',
    ENNReal.ofReal (angularWeight p i s om E v) * ENNReal.ofReal (sectorWeight α U (om, E, v) G') *
      Ψ (om, E, v) G'
    ∂gueMeasure (FrameIndex p) (pairTime p s) ∂projectiveHaar (PairSite p i) ∂volume ∂Pω

/-- `{0,1}`-valued indicator of an event. -/
def ind {X : Type*} (P : X → Prop) (x : X) : ℝ≥0∞ :=
  Set.indicator {y | P y} 1 x

/-- `U = Tr R²`. -/
def invSqTrace (U : FrameMap p i) (θ : OuterData p i) (G' : FrameMatrix p) : ℝ :=
  ((outerM U θ G')⁻¹ * (outerM U θ G')⁻¹).trace.re

/-- `Tr R`. -/
def invTrace (U : FrameMap p i) (θ : OuterData p i) (G' : FrameMatrix p) : ℝ :=
  (outerM U θ G')⁻¹.trace.re

/-- `‖R‖_HS`. -/
def invHS (U : FrameMap p i) (θ : OuterData p i) (G' : FrameMatrix p) : ℝ :=
  Real.sqrt (∑ a, ∑ c, ‖(outerM U θ G')⁻¹ a c‖ ^ 2)

/-- The real-loop error `e_θ`:
`e_θ = 2t⟨U⟩ - t⟨(Tr R + dE/2)²⟩ - (sd(1 - E²/4) - 1)`, `d = 2W`, `t = s/d`. -/
def realLoopError (α : Fin p.N) (s : ℝ) (U : FrameMap p i) (θ : OuterData p i) : ℝ :=
  let t : ℝ := pairTime p s
  let d : ℝ := 2 * p.W
  let E := θ.2.1
  2 * t * sectorAvg α s U (invSqTrace U θ) θ -
      t * sectorAvg α s U (fun G' => (invTrace U θ G' + d * E / 2) ^ 2) θ -
    (s * d * (1 - E ^ 2 / 4) - 1)

/-- The good event `𝒢_α = {E ∈ I, ⟨U⟩_θ ≥ c W²}` of the spread, `I = bulkInterval κ`. -/
def SpreadGood (α : Fin p.N) (s : ℝ) (U : FrameMap p i) (κ c : ℝ) (θ : OuterData p i) : Prop :=
  θ.2.1 ∈ bulkInterval κ ∧ c * (p.W : ℝ) ^ 2 ≤ sectorAvg α s U (invSqTrace U θ) θ

/-!
### The deleted row
-/

variable (p) in
/-- Index of the minor `B` (dimension `d - 2`). -/
abbrev MinorIndex := Fin (2 * p.W - 2)

/-- A measurable frame of `w^⊥` in the frame coordinates (for unit `w`). -/
def IsMinorFrame (Uw : (FrameIndex p → ℂ) → Matrix (FrameIndex p) (MinorIndex p) ℂ) : Prop :=
  Measurable Uw ∧ ∀ x : FrameIndex p → ℂ, l2Norm x = 1 →
    (Uw x)ᴴ * Uw x = 1 ∧ (Uw x)ᴴ *ᵥ x = 0

/-- A measurable unit eigenvector `w(θ)` of `K` (frame coordinates), wherever `K` is Hermitian. -/
def IsOuterEigenvector (U : FrameMap p i) (w : OuterData p i → (FrameIndex p → ℂ)) : Prop :=
  Measurable w ∧ ∀ θ : OuterData p i, l2Norm θ.2.2 = 1 → (outerK U θ).IsHermitian →
    l2Norm (w θ) = 1 ∧ ∃ μ : ℝ, outerK U θ *ᵥ w θ = (μ : ℂ) • w θ

/-- `μ = w*Kw`. -/
def rowMean (U : FrameMap p i) (w : OuterData p i → (FrameIndex p → ℂ)) (θ : OuterData p i) : ℝ :=
  (star (w θ) ⬝ᵥ (outerK U θ *ᵥ w θ)).re

/-- The minor `B`: the compression of `M` to `w^⊥`. -/
def minorB (U : FrameMap p i) (w : OuterData p i → (FrameIndex p → ℂ))
    (Uw : (FrameIndex p → ℂ) → Matrix (FrameIndex p) (MinorIndex p) ℂ) (θ : OuterData p i)
    (G' : FrameMatrix p) : Matrix (MinorIndex p) (MinorIndex p) ℂ :=
  (Uw (w θ))ᴴ * outerM U θ G' * Uw (w θ)

/-- `V_B = Tr C_B²`, `C_B = B⁻¹`. -/
def minorV (U : FrameMap p i) (w : OuterData p i → (FrameIndex p → ℂ))
    (Uw : (FrameIndex p → ℂ) → Matrix (FrameIndex p) (MinorIndex p) ℂ) (θ : OuterData p i)
    (G' : FrameMatrix p) : ℝ :=
  ((minorB U w Uw θ G')⁻¹ * (minorB U w Uw θ G')⁻¹).trace.re

/-- `q_B² = δ_B² + t + t²V_B`, `δ_B = μ - t Tr C_B`. -/
def minorQSq (s : ℝ) (U : FrameMap p i) (w : OuterData p i → (FrameIndex p → ℂ))
    (Uw : (FrameIndex p → ℂ) → Matrix (FrameIndex p) (MinorIndex p) ℂ) (θ : OuterData p i)
    (G' : FrameMatrix p) : ℝ :=
  let t : ℝ := pairTime p s
  let δ := rowMean U w θ - t * (minorB U w Uw θ G')⁻¹.trace.re
  δ ^ 2 + t + t ^ 2 * minorV U w Uw θ G'

end Outer

/-!
## The physical column bound
-/

/-- **The physical column bound.** For fixed `b` and `2 ≤ q < 3` there is `C`
such that for every `n ≥ 4`, `W`, model, rank `α` (every rank), pair, splitting law and frame, and
every outer-measurable unit `w(θ) ∈ v^⊥`, under the pair law (all energies):
`E♯‖Rw‖^q ≤ C W^{q/2}` and `E♯‖R‖_HS^q ≤ C W^q`. -/
def PhysicalColumnStatement : Prop :=
  ∀ b q : ℝ, 2 ≤ q → q < 3 → ∃ C : ℝ, ∀ p : Parameters, p.b = b →
    ∀ (model : p.GaussianRingModel) (α : Fin p.N) (i : ZMod p.n) (Pω : Measure (SplitState p i)),
      IsPairSplitting p i model (splitS p) Pω → ∀ U : FrameMap p i, IsPairFrame p i U →
      (∀ w : OuterData p i → (PairSite p i → ℂ), Measurable w →
        (∀ θ : OuterData p i, l2Norm θ.2.2 = 1 →
          l2Norm (w θ) = 1 ∧ star θ.2.2 ⬝ᵥ w θ = 0) →
        pairExpect α (splitS p) U Pω (fun θ G' =>
            ENNReal.ofReal (l2Norm ((outerM U θ G')⁻¹ *ᵥ ((U θ.2.2)ᴴ *ᵥ w θ)) ^ q)) ≤
          ENNReal.ofReal (C * (p.W : ℝ) ^ (q / 2))) ∧
      pairExpect α (splitS p) U Pω (fun θ G' => ENNReal.ofReal (invHS U θ G' ^ q)) ≤
        ENNReal.ofReal (C * (p.W : ℝ) ^ q)

/-!
## The physical real loop
-/

/-- **The physical real loop.** The error `e_θ` is the outer function
`realLoopError` (so the identity holds by definition; the
content is its size).
* `error`: `b, T, ϑ, κ` first, then `C`; for `4 ≤ n ≤ TW` and `ϑ`-bulk ranks,
  `E♯ 1{E ∈ I} |e_θ| ≤ C W^{49/50}`;
* `good`: `b, κ` first, then a fixed `c > 0`; then for `T, ϑ` a `C` with
  `P♯({E ∈ I} \ 𝒢_α) ≤ C W^{-1/50}`, `𝒢_α = {E ∈ I, ⟨U⟩_θ ≥ cW²}`. -/
structure PhysicalRealLoopStatement : Prop where
  error : ∀ b T ϑ κ : ℝ, 0 < ϑ → 0 < κ → ∃ C : ℝ, ∀ p : Parameters, p.b = b →
    (p.n : ℝ) ≤ T * (p.W : ℝ) →
    ∀ (model : p.GaussianRingModel) (α : Fin p.N), IsBulkRank p ϑ α →
    ∀ (i : ZMod p.n) (Pω : Measure (SplitState p i)), IsPairSplitting p i model (splitS p) Pω →
    ∀ U : FrameMap p i, IsPairFrame p i U →
      pairExpect α (splitS p) U Pω (fun θ _ =>
          (bulkInterval κ).indicator 1 θ.2.1 *
            ENNReal.ofReal |realLoopError α (splitS p) U θ|) ≤
        ENNReal.ofReal (C * (p.W : ℝ) ^ (49 / 50 : ℝ))
  good : ∀ b κ : ℝ, 0 < κ → ∃ c : ℝ, 0 < c ∧ ∀ T ϑ : ℝ, 0 < ϑ → ∃ C : ℝ,
    ∀ p : Parameters, p.b = b → (p.n : ℝ) ≤ T * (p.W : ℝ) →
    ∀ (model : p.GaussianRingModel) (α : Fin p.N), IsBulkRank p ϑ α →
    ∀ (i : ZMod p.n) (Pω : Measure (SplitState p i)), IsPairSplitting p i model (splitS p) Pω →
    ∀ U : FrameMap p i, IsPairFrame p i U →
      pairExpect α (splitS p) U Pω (fun θ _ =>
          ind (fun θ' => θ'.2.1 ∈ bulkInterval κ ∧ ¬ SpreadGood α (splitS p) U κ c θ') θ) ≤
        ENNReal.ofReal (C * (p.W : ℝ) ^ (-(1 / 50 : ℝ)))

/-!
## Fixed-inertia spectral law (indexed spectral convexity, negative spread)
-/

section Sector

variable {m : ℕ}

/-- The normalized law `Z_ℓ(K)⁻¹ det(M)² 1{N_-(M) = ℓ} dP(K + G_m(t))` on the coordinates of
`G_m(t)`. -/
def sectorLaw (m : ℕ) (t : ℝ≥0) (K : Matrix (Fin m) (Fin m) ℂ) (ℓ : ℕ) :
    Measure (HermCoord m → ℝ) :=
  (hermGaussian m t).withDensity fun x =>
    ENNReal.ofReal ((sectorDetSq K ℓ x).re / (sectorMass m t K ℓ).re)

/-- The ordered (increasing) eigenvalues of `M = K + G(x)`. -/
def orderedEigs (K : Matrix (Fin m) (Fin m) ℂ) (x : HermCoord m → ℝ) : Fin m → ℝ :=
  fun k => freshEigenvalue (K + hermOfCoord x) k

/-- The convex fixed-inertia chamber `{λ₁ < ⋯ < λ_m, λ_ℓ < 0 < λ_{ℓ+1}}` (zero-based). -/
def chamber (m ℓ : ℕ) : Set (Fin m → ℝ) :=
  {lam | StrictMono lam ∧ ∀ k : Fin m, (k.val < ℓ → lam k < 0) ∧ (ℓ ≤ k.val → 0 < lam k)}

/-- The curvature form `aᵀ[t⁻¹I + 2 diag(λ_j⁻²) + Σ_{i<j}(e_i-e_j)(e_i-e_j)ᵀ/(λ_i-λ_j)²]a`. -/
def curvatureForm (t : ℝ) (lam a : Fin m → ℝ) : ℝ :=
  t⁻¹ * ∑ j, a j ^ 2 + 2 * ∑ j, a j ^ 2 / lam j ^ 2 +
    ∑ k, ∑ j, if k < j then (a k - a j) ^ 2 / (lam k - lam j) ^ 2 else 0

/-- The weighted energy density `Σ_j |∂_j f|²/(t⁻¹ + 2λ_j⁻²)`. -/
def weightedEnergy (t : ℝ) (f : (Fin m → ℝ) → ℝ) (lam : Fin m → ℝ) : ℝ :=
  ∑ j, (fderiv ℝ f lam (Pi.single j 1)) ^ 2 / (t⁻¹ + 2 / lam j ^ 2)

/-- `U = Tr M⁻²` at `M = K + G(x)`. -/
def sectorInvSq (K : Matrix (Fin m) (Fin m) ℂ) (x : HermCoord m → ℝ) : ℝ :=
  ((K + hermOfCoord x)⁻¹ * (K + hermOfCoord x)⁻¹).trace.re

end Sector

/-- **Indexed spectral convexity.** For every `m`, `t > 0`, Hermitian
`K` and attainable sector `ℓ` (`Z_ℓ(K) > 0`):
* `density`: the ordered eigenvalues under the normalized law have the density `e^{-𝒰}` on the
  chamber, with `𝒰` of class `C²` there and `∇²𝒰 ⪰ t⁻¹I + 2diag(λ_j⁻²) +
  Σ_{i<j}(e_i-e_j)(e_i-e_j)ᵀ/(λ_i-λ_j)²` (spectral curvature); the density identity is
  stated unnormalized, for every measurable `g ≥ 0`;
* `variance`: for every measurable `f`, smooth on the chamber, of finite weighted energy,
  `Var f(λ) ≤ E Σ_j |∂_jf(λ)|²/(t⁻¹ + 2λ_j⁻²)` (the
  `evariance` form also asserts `f(λ) ∈ L²`). -/
structure IndexedSpectralConvexityStatement : Prop where
  density : ∀ (m : ℕ) (t : ℝ≥0) (K : Matrix (Fin m) (Fin m) ℂ) (ℓ : ℕ), 0 < t →
    K.IsHermitian → 0 < (sectorMass m t K ℓ).re →
    ∃ 𝒰 : (Fin m → ℝ) → ℝ, ContDiffOn ℝ 2 𝒰 (chamber m ℓ) ∧
      (∀ g : (Fin m → ℝ) → ℝ≥0∞, Measurable g →
        (∫⁻ x, ENNReal.ofReal (sectorDetSq K ℓ x).re * g (orderedEigs K x) ∂hermGaussian m t) =
          ENNReal.ofReal (sectorMass m t K ℓ).re *
            ∫⁻ lam in chamber m ℓ, ENNReal.ofReal (Real.exp (-𝒰 lam)) * g lam) ∧
      ∀ lam ∈ chamber m ℓ, ∀ a : Fin m → ℝ,
        curvatureForm (t : ℝ) lam a ≤ iteratedFDeriv ℝ 2 𝒰 lam (fun _ => a)
  variance : ∀ (m : ℕ) (t : ℝ≥0) (K : Matrix (Fin m) (Fin m) ℂ) (ℓ : ℕ), 0 < t →
    K.IsHermitian → 0 < (sectorMass m t K ℓ).re →
    ∀ f : (Fin m → ℝ) → ℝ, Measurable f → ContDiffOn ℝ ∞ f (chamber m ℓ) →
      (∫⁻ x, ENNReal.ofReal (weightedEnergy (t : ℝ) f (orderedEigs K x)) ∂sectorLaw m t K ℓ) ≠ ⊤ →
      evariance (fun x => f (orderedEigs K x)) (sectorLaw m t K ℓ) ≤
        ∫⁻ x, ENNReal.ofReal (weightedEnergy (t : ℝ) f (orderedEigs K x)) ∂sectorLaw m t K ℓ

/-- **Negative spread.** Under the normalized sector law, with
`U = Tr M⁻²`: `E U < ∞`, `E U · E U⁻¹ ≤ 64e⁸`, and for every `q > 0` a `C_q` with
`E U^{-q} ≤ C_q (E U)^{-q}`; all constants are independent of `K, m, t, ℓ`. -/
structure NegativeSpreadStatement : Prop where
  product : ∀ (m : ℕ) (t : ℝ≥0) (K : Matrix (Fin m) (Fin m) ℂ) (ℓ : ℕ), 0 < t →
    K.IsHermitian → 0 < (sectorMass m t K ℓ).re →
      (∫⁻ x, ENNReal.ofReal (sectorInvSq K x) ∂sectorLaw m t K ℓ) ≠ ⊤ ∧
      (∫⁻ x, ENNReal.ofReal (sectorInvSq K x) ∂sectorLaw m t K ℓ) *
          (∫⁻ x, ENNReal.ofReal (sectorInvSq K x)⁻¹ ∂sectorLaw m t K ℓ) ≤
        ENNReal.ofReal (64 * Real.exp 8)
  inverse_moment : ∀ q : ℝ, 0 < q → ∃ C : ℝ, ∀ (m : ℕ) (t : ℝ≥0)
    (K : Matrix (Fin m) (Fin m) ℂ) (ℓ : ℕ), 0 < t → K.IsHermitian →
    0 < (sectorMass m t K ℓ).re →
      (∫⁻ x, ENNReal.ofReal ((sectorInvSq K x)⁻¹ ^ q) ∂sectorLaw m t K ℓ) ≤
        ENNReal.ofReal C * ((∫⁻ x, ENNReal.ofReal (sectorInvSq K x) ∂sectorLaw m t K ℓ) ^ q)⁻¹

/-!
## The signed row spread
-/

section Row

variable {k : ℕ}

/-- `M = [[μ + x, y*], [y, B]]` on `Unit ⊕ Fin k`. -/
def rowMatrix (μ x : ℝ) (y : Fin k → ℂ) (B : Matrix (Fin k) (Fin k) ℂ) :
    Matrix (Unit ⊕ Fin k) (Unit ⊕ Fin k) ℂ :=
  Matrix.fromBlocks (Matrix.of fun _ _ => ((μ + x : ℝ) : ℂ)) (Matrix.of fun _ j => star (y j))
    (Matrix.of fun j _ => y j) B

/-- The row law: `x ~ N(0,t)` independent of `y ~ CN(0, tI)` (`E|y_j|² = t`). -/
def rowLaw (k : ℕ) (t : ℝ≥0) : Measure (ℝ × (Fin k → ℂ)) :=
  (gaussianReal 0 t).prod
    ((circularVectorLaw (Fin k)).map fun g => (Real.sqrt (t : ℝ) : ℂ) • g)

/-- The Schur complement `a = μ + x - y*C_B y`. -/
def rowSchur (μ : ℝ) (B : Matrix (Fin k) (Fin k) ℂ) (z : ℝ × (Fin k → ℂ)) : ℝ :=
  μ + z.1 - (star z.2 ⬝ᵥ (B⁻¹ *ᵥ z.2)).re

end Row

/-- **The signed row spread.** For every `k`, `t > 0`,
real `μ` and invertible Hermitian `B` (the minor), with `C_B = B⁻¹`, `V_B = Tr C_B²`,
`δ_B = μ - t Tr C_B`, `q_B² = δ_B² + t + t²V_B`, `a = μ + x - y*C_By` and `U = Tr M⁻²`:
`E a² = q_B²`; `a²U` is integrable and
`E a²U = V_Bq_B² + (1+tV_B)² + 2tδ_B Tr C_B³ - t² Tr C_B⁴
       = 2V_Bq_B² + 1 + tV_B - Tr[C_B²(δ_B I - tC_B)²] ≤ (2V_B + t⁻¹)q_B²`. -/
def SignedRowSpreadStatement : Prop :=
  ∀ (k : ℕ) (t : ℝ≥0) (μ : ℝ) (B : Matrix (Fin k) (Fin k) ℂ), 0 < t → B.IsHermitian →
    B.det ≠ 0 →
    let t' : ℝ := t
    let CB := B⁻¹
    let V := (CB * CB).trace.re
    let δ := μ - t' * CB.trace.re
    let q2 := δ ^ 2 + t' + t' ^ 2 * V
    let F := fun z : ℝ × (Fin k → ℂ) => rowSchur μ B z ^ 2 *
      ((rowMatrix μ z.1 z.2 B)⁻¹ * (rowMatrix μ z.1 z.2 B)⁻¹).trace.re
    let X := δ • (1 : Matrix (Fin k) (Fin k) ℂ) - t' • CB
    let first := V * q2 + (1 + t' * V) ^ 2 + 2 * t' * δ * (CB ^ 3).trace.re -
      t' ^ 2 * (CB ^ 4).trace.re
    let second := 2 * V * q2 + 1 + t' * V - (CB ^ 2 * X ^ 2).trace.re
    (∫ z, rowSchur μ B z ^ 2 ∂rowLaw k t) = q2 ∧
    Integrable F (rowLaw k t) ∧
    (∫ z, F z ∂rowLaw k t) = first ∧ first = second ∧ second ≤ (2 * V + t'⁻¹) * q2

/-!
## The physical minor tail
-/

/-- **The physical minor tail.** `w(θ)` a measurable unit eigenvector of `K`,
`B` the minor of `M` on `w^⊥` (any measurable frame), `V_B = Tr B⁻²`, `q_B² = δ_B² + t + t²V_B`.
* `tail`: for `b, κ`, every `c > 0` (the constant of `𝒢_α`) and
  `q > 0` there is `C` with `P♯(𝒢_α, V_B ≤ A) ≤ C((A + W)/W²)^{q/(q+1)}` for every `A ≥ 0`,
  every `n ≥ 4` and every rank;
* `inverse_spread`: for `b, T, ϑ, κ` and `0 < r < 2` there is `C`
  with `E♯ 1{E ∈ I} q_B^{-r} ≤ C` for `4 ≤ n ≤ TW` and `ϑ`-bulk ranks. ("Every `r < 2`" is read
  as `0 < r < 2`: the proof bounds positive powers of `Y = q_B⁻¹`, the use in
  the determinant score theorem is `0 < r < 2`, and `r = 0` is trivial.) -/
structure PhysicalMinorTailStatement : Prop where
  tail : ∀ b κ c q : ℝ, 0 < κ → 0 < c → 0 < q → ∃ C : ℝ, ∀ p : Parameters, p.b = b →
    ∀ (model : p.GaussianRingModel) (α : Fin p.N) (i : ZMod p.n)
      (Pω : Measure (SplitState p i)), IsPairSplitting p i model (splitS p) Pω →
    ∀ U : FrameMap p i, IsPairFrame p i U →
    ∀ w : OuterData p i → (FrameIndex p → ℂ), IsOuterEigenvector U w →
    ∀ Uw : (FrameIndex p → ℂ) → Matrix (FrameIndex p) (MinorIndex p) ℂ, IsMinorFrame Uw →
    ∀ A : ℝ, 0 ≤ A →
      pairExpect α (splitS p) U Pω (fun θ G' =>
          ind (fun x : OuterData p i × FrameMatrix p =>
            SpreadGood α (splitS p) U κ c x.1 ∧ minorV U w Uw x.1 x.2 ≤ A) (θ, G')) ≤
        ENNReal.ofReal (C * ((A + p.W) / (p.W : ℝ) ^ 2) ^ (q / (q + 1)))
  inverse_spread : ∀ b T ϑ κ r : ℝ, 0 < ϑ → 0 < κ → 0 < r → r < 2 → ∃ C : ℝ,
    ∀ p : Parameters, p.b = b → (p.n : ℝ) ≤ T * (p.W : ℝ) →
    ∀ (model : p.GaussianRingModel) (α : Fin p.N), IsBulkRank p ϑ α →
    ∀ (i : ZMod p.n) (Pω : Measure (SplitState p i)), IsPairSplitting p i model (splitS p) Pω →
    ∀ U : FrameMap p i, IsPairFrame p i U →
    ∀ w : OuterData p i → (FrameIndex p → ℂ), IsOuterEigenvector U w →
    ∀ Uw : (FrameIndex p → ℂ) → Matrix (FrameIndex p) (MinorIndex p) ℂ, IsMinorFrame Uw →
      pairExpect α (splitS p) U Pω (fun θ G' =>
          (bulkInterval κ).indicator 1 θ.2.1 *
            ENNReal.ofReal (minorQSq (splitS p) U w Uw θ G' ^ (-(r / 2)))) ≤
        ENNReal.ofReal C

/-!
## The determinant score
-/

/-- **The determinant score theorem.**
* `exact`: at every fixed exterior (`H_R`, `V` Hermitian, any
  `C`), every real nonpole energy `E`, every `s > 0`, every rank, frame and unit `v` with
  `𝔷_ℓ(v) ≠ 0` (attainable sector), `log 𝔷_ℓ` (degree-zero extension) is real Fréchet
  differentiable at `v` and its derivative on `h ⊥ v` is `Re(h*(-4R̄QK₀v))`;
* `moments`: for `b, T, ϑ, κ` and `0 < r < 2` there is `C`
  with `E♯ 1{E ∈ I}[‖R̄‖^r + ‖∇_v log 𝔷_ℓ(v)‖^r] ≤ C`, uniformly in `4 ≤ n ≤ TW`, both parities,
  adjacent pairs and `ϑ`-bulk ranks (the gradient is the vector `score`, by `exact`). -/
structure DeterminantScoreStatement : Prop where
  exact : ∀ (p : Parameters) (α : Fin p.N) (i : ZMod p.n) (s : ℝ), 0 < s →
    ∀ U : FrameMap p i, IsPairFrame p i U →
    ∀ om : SplitState p i, om.1.IsHermitian → om.2.2.IsHermitian →
    ∀ E : ℝ, (om.1 - (E : ℂ) • 1).det ≠ 0 →
    ∀ v : PairSite p i → ℂ, l2Norm v = 1 → detFactor p i α s U om E v ≠ 0 →
      ∃ L : (PairSite p i → ℂ) →L[ℝ] ℝ,
        HasFDerivAt (fun z => Real.log (detFactor p i α s U om E (normalize z)).toReal) L v ∧
        ∀ h : PairSite p i → ℂ, star h ⬝ᵥ v = 0 →
          L h = (star h ⬝ᵥ score α s U (om, E, v)).re
  moments : ∀ b T ϑ κ r : ℝ, 0 < ϑ → 0 < κ → 0 < r → r < 2 → ∃ C : ℝ,
    ∀ p : Parameters, p.b = b → (p.n : ℝ) ≤ T * (p.W : ℝ) →
    ∀ (model : p.GaussianRingModel) (α : Fin p.N), IsBulkRank p ϑ α →
    ∀ (i : ZMod p.n) (Pω : Measure (SplitState p i)), IsPairSplitting p i model (splitS p) Pω →
    ∀ U : FrameMap p i, IsPairFrame p i U →
      pairExpect α (splitS p) U Pω (fun θ _ =>
          (bulkInterval κ).indicator 1 θ.2.1 *
            ENNReal.ofReal (‖condInverse α (splitS p) U θ‖ ^ r +
              l2Norm (score α (splitS p) U θ) ^ r)) ≤
        ENNReal.ofReal C

end BlockBand.DeterminantScore
