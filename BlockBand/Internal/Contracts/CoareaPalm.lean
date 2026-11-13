module

public import BlockBand.QUE.Fourier.PhysicalPairTilt
public import BlockBand.Coarea.SchurDerivative
public import BlockBand.Palm.ScalarGaussianWeight
public import BlockBand.SourceProcess.CommonMatrixBrownian

/-!
# Exact coarea, fresh-block Palm and relative localization statements

This file states, as propositions, the exact coarea formula for the exposed pair of blocks,
pole exclusion, the Palm moments of a fresh Gaussian block, the coarse relative local law, the
relative localization of the matrix Brownian flow, and the fixed-deformation eigenpair density.

## Conventions

* `GUE_d(t)` is `gueMeasure`: the law of
  `√(t/2)(X + Xᴴ)` for a matrix `X` of i.i.d. standard circular entries
  (`E|X_ij|² = 1`). Diagonal entries are real with variance `t`, off-diagonal
  entries have `E|A_ij|² = t` with independent real/imaginary parts of variance `t/2`,
  distinct unordered pairs are independent: this is exactly the stated law; its
  Lebesgue density `Z_d(t)⁻¹ e^{-Tr A²/(2t)}` is a lemma, not a definition.
* Normalized projective Haar measure `ν_d` is represented by `projectiveHaar`, the law of
  `g/‖g‖` for a standard circular Gaussian vector `g`, i.e. the normalized uniform
  measure on the unit sphere of `ℂ^d`. Its image in `ℂP^{d-1}` is `ν_d`. Every
  integrand below is invariant under `v ↦ e^{iθ} v` after the `G_{d-1}` integration,
  so the two integrals coincide.
* The frame `U_v` of `v^⊥` is an arbitrary measurable choice (`IsPairFrame`); the
  formula is required for every such frame (the formula in the paper is frame-independent).
* The rank `α : Fin p.N` is zero-based: the paper's rank `α` is Lean `α.val + 1`, so the
  inertia indicator `N_-(M) = α - N_R(E) - 1` is `N_-(M) + N_R(E) = α.val`.
* The coarea theorem is stated for an arbitrary measurable nonnegative observable `Φ(ω,G)` of
  the split state. Observables of `(H, λ_α, ψ_α)` are the special case
  `Φ(ω,G) = Φ₀(assemble ω G, …)`, and `reconstructed_rank` identifies `λ_α` and the
  eigenline of the reconstructed matrix with `(E, L_E v)` on the support of the density.
  This is the form used for integrands depending on exterior data, `V`, `E` and `v`.
* The pair splitting is an existence clause plus a formula valid for
  every law `Pω` of `ω = (H_R, C, V)` such that `Pω ⊗ GUE_d(t)` reassembles to the
  physical law (such `Pω` is unique: the GUE characteristic function never vanishes).
  Extensions carrying extra randomness beyond `(ω, G)` use the fixed-`ω` clause
  `formula_fixed`.
* Probabilities `≤ N^{-D}` "for every fixed D" are stated as `∀ D, ∃ N₀, ∀ N ≥ N₀`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Internal.Contracts.CoareaPalm

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Model.Construction BlockBand.QUE.Fourier BlockBand.Coarea BlockBand.SourceProcess
open scoped ENNReal NNReal ComplexConjugate

/-!
## Finite Gaussian vocabulary
-/

/-- Euclidean (ℓ²) norm of a finite complex vector. -/
def l2Norm {ι : Type*} [Fintype ι] (x : ι → ℂ) : ℝ :=
  Real.sqrt (∑ k, ‖x k‖ ^ 2)

/-- `GUE` sample map: `√(t/2) (X + Xᴴ)` from a matrix of standard circular entries. -/
def gueSample {ι : Type*} (t : ℝ≥0) (X : ι × ι → ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun a b => (Real.sqrt ((t : ℝ) / 2) : ℂ) * (X (a, b) + conj (X (b, a)))

/-- `GUE_ι(t)`: diagonal variance `t`, `E|A_ab|² = t`. The
circular entries are `commonCircularIncrementLaw ι 1` (`E|X_ab|² = 1`). -/
def gueMeasure (ι : Type*) [Fintype ι] (t : ℝ≥0) : Measure (Matrix ι ι ℂ) :=
  (commonCircularIncrementLaw ι 1).map (gueSample t)

/-- Standard circular Gaussian vector (density `π^{-d} e^{-‖g‖²}`, `E gg* = I`). -/
def circularVectorLaw (ι : Type*) [Fintype ι] : Measure (ι → ℂ) :=
  (Measure.pi fun _ : ι × Fin 2 => gaussianReal 0 (1 / 2 : ℝ≥0)).map
    (fun r a => (r (a, 0) : ℂ) + (r (a, 1) : ℂ) * Complex.I)

/-- Normalized projective Haar measure `ν_d`, as the uniform law of `g/‖g‖`. -/
def projectiveHaar (ι : Type*) [Fintype ι] : Measure (ι → ℂ) :=
  (circularVectorLaw ι).map (fun g => ((l2Norm g)⁻¹ : ℂ) • g)

/-- `N_-`: the number of strictly negative eigenvalues (with multiplicity) of a
Hermitian matrix; zero by convention off the Hermitian set. -/
def negativeCount {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) : ℕ := by
  classical
  exact if h : M.IsHermitian then (Finset.univ.filter fun k => h.eigenvalues k < 0).card else 0

/-- Real quadratic form `Re(q* Γ q)`. -/
def quadForm {ι : Type*} [Fintype ι] (Γ : Matrix ι ι ℂ) (q : ι → ℂ) : ℝ :=
  (star q ⬝ᵥ (Γ *ᵥ q)).re

/-!
## The exposed pair and its Schur data
-/

section Pair

variable (p : Parameters) (i : ZMod p.n)

/-- Sites of the exposed pair `S = {i, i+1}` (dimension `d = 2W` since `n ≥ 4`). -/
abbrev PairSite := {x : p.Site // x.1 = i ∨ x.1 = i + 1}

/-- Sites of the exterior `R = Sᶜ`. -/
abbrev ExteriorSite := {x : p.Site // ¬ (x.1 = i ∨ x.1 = i + 1)}

/-- Pair matrices. -/
abbrev PairMatrix := Matrix (PairSite p i) (PairSite p i) ℂ

/-- The randomness `ω = (H_R, C, V)` other than the fresh pair Gaussian `G`;
`C = H_RS` is the exterior-to-pair coupling. -/
abbrev SplitState :=
  Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ ×
    Matrix (ExteriorSite p i) (PairSite p i) ℂ × PairMatrix p i

/-- Index type `Fin (d-1)` of a frame of `v^⊥`. -/
abbrev FrameIndex := Fin (2 * p.W - 1)

/-- The Gaussian part's entry variance `t = s/d`, `d = 2W`. -/
def pairTime (s : ℝ) : ℝ≥0 := Real.toNNReal (s / (2 * (p.W : ℝ)))

/-- Reassembly `H = [[V+G, C*],[C, H_R]]` in the decomposition `S ⊕ R`. -/
def assemble (ω : SplitState p i) (G : PairMatrix p i) : p.SiteMatrix :=
  fun x y =>
    if hx : x.1 = i ∨ x.1 = i + 1 then
      if hy : y.1 = i ∨ y.1 = i + 1 then ω.2.2 ⟨x, hx⟩ ⟨y, hy⟩ + G ⟨x, hx⟩ ⟨y, hy⟩
      else star (ω.2.1 ⟨y, hy⟩ ⟨x, hx⟩)
    else
      if hy : y.1 = i ∨ y.1 = i + 1 then ω.2.1 ⟨x, hx⟩ ⟨y, hy⟩
      else ω.1 ⟨x, hx⟩ ⟨y, hy⟩

/-- Exterior block `H_R`. -/
def exteriorBlock (H : p.SiteMatrix) : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ :=
  fun x y => H x.1 y.1

/-- Coupling block `C = H_RS`. -/
def couplingBlock (H : p.SiteMatrix) : Matrix (ExteriorSite p i) (PairSite p i) ℂ :=
  fun x y => H x.1 y.1

/-- Pair block `H_SS`. -/
def pairBlock (H : p.SiteMatrix) : PairMatrix p i :=
  fun x y => H x.1 y.1

/-- The pair splitting at parameter `s`: the law `Pω` of `ω` together with an
independent `G ~ GUE_d(s/d)` reassembles to the exact physical law. -/
def IsPairSplitting (model : p.GaussianRingModel) (s : ℝ) (Pω : Measure (SplitState p i)) :
    Prop :=
  (Pω.prod (gueMeasure (PairSite p i) (pairTime p s))).map
      (fun x => assemble p i x.1 x.2) = (model.law : Measure p.SiteMatrix)

/-- Reconstruction map `L_E v = (v, -T(E) v)` from the Schur data. -/
def schurLift (H_R : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ)
    (C : Matrix (ExteriorSite p i) (PairSite p i) ℂ) (E : ℝ) (v : PairSite p i → ℂ) :
    p.Site → ℂ :=
  fun x =>
    if hx : x.1 = i ∨ x.1 = i + 1 then v ⟨x, hx⟩
    else -((physicalCoareaT H_R C E *ᵥ v) ⟨x, hx⟩)

/-- Pair mass `m = p_{αi} + p_{α,i+1}` of the ordered rank-`α` eigenvector. -/
def pairMass (α : Fin p.N) (H : p.SiteMatrix) : ℝ :=
  physicalOrderedBlockMass p H α i + physicalOrderedBlockMass p H α (i + 1)

/-- Clock reconstruction at `E = λ_α`: with `ψ = ψ_α`, `m` the pair mass and
`v = P_Sψ/√m`, one has `A v = 0`, `v* 𝒟 v = m⁻¹`, `ψ = L_E v/‖L_E v‖`. -/
def ClockReconstruction (α : Fin p.N) (H : p.SiteMatrix) : Prop :=
  let E := physicalOrderedEigenvalue p H α
  let ψ := physicalOrderedEigenvector p H α
  let m := pairMass p i α H
  let v : PairSite p i → ℂ := fun x => ((Real.sqrt m)⁻¹ : ℂ) * ψ x.1
  let H_R := exteriorBlock p i H
  let C := couplingBlock p i H
  physicalCoareaA H_R C (pairBlock p i H) 0 E *ᵥ v = 0 ∧
    star v ⬝ᵥ (physicalCoareaD H_R C E *ᵥ v) = ((m⁻¹ : ℝ) : ℂ) ∧
    ∀ x, ψ x = ((l2Norm (schurLift p i H_R C E v))⁻¹ : ℂ) * schurLift p i H_R C E v x

/-- A measurable orthonormal frame `U_v` of `v^⊥` for unit vectors `v`. -/
def IsPairFrame (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ) : Prop :=
  Measurable U ∧ ∀ v : PairSite p i → ℂ, l2Norm v = 1 →
    (U v)ᴴ * U v = 1 ∧ (U v)ᴴ *ᵥ v = 0

/-- `B - E = M = F_v + G_{d-1} - E`, with `F_v = U_v* F(E) U_v`. -/
def frameM (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ)
    (ω : SplitState p i) (E : ℝ) (v : PairSite p i → ℂ)
    (G' : Matrix (FrameIndex p) (FrameIndex p) ℂ) : Matrix (FrameIndex p) (FrameIndex p) ℂ :=
  (U v)ᴴ * physicalCoareaF ω.1 ω.2.1 ω.2.2 E * U v + G' - (E : ℂ) • 1

/-- The fresh pair Gaussian reconstructed from eigenpair coordinates:
`G = E vv* + U_v (F_v + G_{d-1}) U_v* - F(E)`, so that `F(E) + G` has eigenpair `(E,v)`. -/
def reconstructedGaussian (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ)
    (ω : SplitState p i) (E : ℝ) (v : PairSite p i → ℂ)
    (G' : Matrix (FrameIndex p) (FrameIndex p) ℂ) : PairMatrix p i :=
  let F := physicalCoareaF ω.1 ω.2.1 ω.2.2 E
  (E : ℂ) • vecMulVec v (star v) + U v * ((U v)ᴴ * F * U v + G') * (U v)ᴴ - F

end Pair

/-- The Gaussian regression factor `𝓡(E,v,F)` of the coarea formula. -/
def regressionFactor {ι : Type*} [Fintype ι] (t E : ℝ) (v : ι → ℂ) (F : Matrix ι ι ℂ) : ℝ :=
  let a := star v ⬝ᵥ (F *ᵥ v)
  Real.exp (-((E - a.re) ^ 2 + 2 * l2Norm (F *ᵥ v - a • v) ^ 2) / (2 * t))

/-- The constant `c_{d,t} = 1/((d-1)! t^{d-1} √(2πt))` of the coarea formula. -/
def coareaConstant (d : ℕ) (t : ℝ) : ℝ :=
  1 / (((d - 1).factorial : ℝ) * t ^ (d - 1) * Real.sqrt (2 * Real.pi * t))

/-- Fixed-`ω` right side of the complete coarea formula for an observable `g` of the fresh pair
Gaussian, with crossing factor `speed ω E v` (`v* 𝒟(E) v` for the law of `H`, the
constant `n/2` for the pair law). -/
def coareaFiber (p : Parameters) (α : Fin p.N) (i : ZMod p.n) (s : ℝ)
    (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ)
    (speed : SplitState p i → ℝ → (PairSite p i → ℂ) → ℝ)
    (ω : SplitState p i) (g : PairMatrix p i → ℝ≥0∞) : ℝ≥0∞ := by
  classical
  exact ∫⁻ E : ℝ, ∫⁻ v, ∫⁻ G',
    ENNReal.ofReal (coareaConstant (2 * p.W) (pairTime p s) *
        regressionFactor (pairTime p s) E v (physicalCoareaF ω.1 ω.2.1 ω.2.2 E) *
        speed ω E v * Complex.normSq (frameM p i U ω E v G').det) *
      (if negativeCount (frameM p i U ω E v G') + negativeCount (ω.1 - (E : ℂ) • 1) = α.val
        then 1 else 0) *
      g (reconstructedGaussian p i U ω E v G')
    ∂(gueMeasure (FrameIndex p) (pairTime p s)) ∂(projectiveHaar (PairSite p i)) ∂volume

/-- Right side of the complete coarea formula: `∫ dP(ω)` of the fixed-`ω` fiber. -/
def coareaRHS (p : Parameters) (α : Fin p.N) (i : ZMod p.n) (s : ℝ)
    (Pω : Measure (SplitState p i))
    (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ)
    (speed : SplitState p i → ℝ → (PairSite p i → ℂ) → ℝ)
    (Φ : SplitState p i → PairMatrix p i → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ ω, coareaFiber p α i s U speed ω (Φ ω) ∂Pω

/-- Crossing speed `v* 𝒟(E) v`. -/
def clockSpeed (p : Parameters) (i : ZMod p.n) (ω : SplitState p i) (E : ℝ)
    (v : PairSite p i → ℂ) : ℝ :=
  (star v ⬝ᵥ (physicalCoareaD ω.1 ω.2.1 E *ᵥ v)).re

/-- The exact coarea formula for the exposed pair.
* `splitting_exists`: a pair splitting exists.
* `frame_exists`: a measurable frame of `v^⊥` exists.
* `clock`: the clock reconstruction on every Hermitian `H` with `λ_α ∉ Spec H_R`
  (pointwise), and `regular_ae`: almost surely `H` is Hermitian with simple spectrum
  and no eigenvalue of `H` lies in `Spec H_R` (so the clock identities hold a.s.).
* `formula`: the complete coarea formula for every splitting law, frame and measurable
  `Φ ≥ 0` of the split state; `formula_fixed`: its fixed-`ω` (conditional on `ω`) form,
  for `Pω`-almost every `ω` simultaneously for all measurable `g ≥ 0` of `G` (usable on
  extensions whose extra randomness is not a function of `ω`); `mass_one`: total mass one.
* `reconstructed_rank`: on the support of the density the reconstructed matrix has
  `λ_α = E` and rank-`α` eigenline spanned by `L_E v`.
* `pairLaw_probability`, `pairLaw_formula`, `pairLaw_measure`: the pair law has mass one
  and its formula is the complete coarea formula with `v*𝒟v` replaced by `n/2`, stated both on the
  split state and directly for `P♯_{α,S} = physicalPairMeasure p model α i`. -/
structure CoareaContract : Prop where
  splitting_exists : ∀ (p : Parameters) (model : p.GaussianRingModel) (i : ZMod p.n) (s : ℝ),
    0 < s → s ≤ min p.c p.b → ∃ Pω : Measure (SplitState p i), IsPairSplitting p i model s Pω
  frame_exists : ∀ (p : Parameters) (i : ZMod p.n),
    ∃ U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ, IsPairFrame p i U
  clock : ∀ (p : Parameters) (α : Fin p.N) (i : ZMod p.n) (H : p.SiteMatrix),
    H.IsHermitian →
    (exteriorBlock p i H - ((physicalOrderedEigenvalue p H α : ℝ) : ℂ) • 1).det ≠ 0 →
    ClockReconstruction p i α H
  regular_ae : ∀ (p : Parameters) (model : p.GaussianRingModel),
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix), H.IsHermitian ∧ H.charpoly.Separable ∧
      ∀ (α : Fin p.N) (i : ZMod p.n),
        (exteriorBlock p i H - ((physicalOrderedEigenvalue p H α : ℝ) : ℂ) • 1).det ≠ 0
  formula : ∀ (p : Parameters) (model : p.GaussianRingModel) (α : Fin p.N) (i : ZMod p.n)
    (s : ℝ), 0 < s → s ≤ min p.c p.b →
    ∀ Pω : Measure (SplitState p i), IsPairSplitting p i model s Pω →
    ∀ U, IsPairFrame p i U →
    ∀ Φ : SplitState p i → PairMatrix p i → ℝ≥0∞, Measurable (Function.uncurry Φ) →
      (∫⁻ x, Φ x.1 x.2 ∂(Pω.prod (gueMeasure (PairSite p i) (pairTime p s)))) =
        coareaRHS p α i s Pω U (clockSpeed p i) Φ
  formula_fixed : ∀ (p : Parameters) (model : p.GaussianRingModel) (α : Fin p.N)
    (i : ZMod p.n) (s : ℝ), 0 < s → s ≤ min p.c p.b →
    ∀ Pω : Measure (SplitState p i), IsPairSplitting p i model s Pω →
    ∀ U, IsPairFrame p i U →
    ∀ᵐ ω ∂Pω, ∀ g : PairMatrix p i → ℝ≥0∞, Measurable g →
      (∫⁻ G, g G ∂(gueMeasure (PairSite p i) (pairTime p s))) =
        coareaFiber p α i s U (clockSpeed p i) ω g
  mass_one : ∀ (p : Parameters) (model : p.GaussianRingModel) (α : Fin p.N) (i : ZMod p.n)
    (s : ℝ), 0 < s → s ≤ min p.c p.b →
    ∀ Pω : Measure (SplitState p i), IsPairSplitting p i model s Pω →
    ∀ U, IsPairFrame p i U → coareaRHS p α i s Pω U (clockSpeed p i) (fun _ _ => 1) = 1
  reconstructed_rank : ∀ (p : Parameters) (α : Fin p.N) (i : ZMod p.n)
    (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ),
    IsPairFrame p i U →
    ∀ (ω : SplitState p i) (E : ℝ) (v : PairSite p i → ℂ)
      (G' : Matrix (FrameIndex p) (FrameIndex p) ℂ),
      (assemble p i ω (reconstructedGaussian p i U ω E v G')).IsHermitian →
      l2Norm v = 1 → (ω.1 - (E : ℂ) • 1).det ≠ 0 → (frameM p i U ω E v G').det ≠ 0 →
      negativeCount (frameM p i U ω E v G') + negativeCount (ω.1 - (E : ℂ) • 1) = α.val →
      let H := assemble p i ω (reconstructedGaussian p i U ω E v G')
      let L := schurLift p i ω.1 ω.2.1 E v
      physicalOrderedEigenvalue p H α = E ∧
        ∀ x y, physicalOrderedEigenvector p H α x * conj (physicalOrderedEigenvector p H α y) =
          ((l2Norm L ^ 2)⁻¹ : ℂ) * (L x * conj (L y))
  pairLaw_probability : ∀ (p : Parameters) (model : p.GaussianRingModel) (α : Fin p.N)
    (i : ZMod p.n), IsProbabilityMeasure (physicalPairMeasure p model α i)
  pairLaw_formula : ∀ (p : Parameters) (model : p.GaussianRingModel) (α : Fin p.N)
    (i : ZMod p.n) (s : ℝ), 0 < s → s ≤ min p.c p.b →
    ∀ Pω : Measure (SplitState p i), IsPairSplitting p i model s Pω →
    ∀ U, IsPairFrame p i U →
    ∀ Φ : SplitState p i → PairMatrix p i → ℝ≥0∞, Measurable (Function.uncurry Φ) →
      (∫⁻ x, ENNReal.ofReal ((p.n : ℝ) / 2 * pairMass p i α (assemble p i x.1 x.2)) *
          Φ x.1 x.2 ∂(Pω.prod (gueMeasure (PairSite p i) (pairTime p s)))) =
        coareaRHS p α i s Pω U (fun _ _ _ => (p.n : ℝ) / 2) Φ
  pairLaw_measure : ∀ (p : Parameters) (model : p.GaussianRingModel) (α : Fin p.N)
    (i : ZMod p.n) (s : ℝ), 0 < s → s ≤ min p.c p.b →
    ∀ Pω : Measure (SplitState p i), IsPairSplitting p i model s Pω →
    ∀ U, IsPairFrame p i U →
    ∀ Φ₀ : p.SiteMatrix → ℝ≥0∞, Measurable Φ₀ →
      (∫⁻ H, Φ₀ H ∂physicalPairMeasure p model α i) =
        coareaRHS p α i s Pω U (fun _ _ _ => (p.n : ℝ) / 2) (fun ω G => Φ₀ (assemble p i ω G))

/-!
## Pole exclusion
-/

/-- Traceless part `G⁰ = G - (Tr G/d) I`. -/
def tracelessPart {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  G - (((Fintype.card ι : ℂ))⁻¹ * G.trace) • 1

/-- Pole exclusion for the exposed pair.
* `averaging` (weighted spectral averaging): for almost every `(ω, G⁰)` and
  every Borel `B` (in particular every exterior-measurable `B(ω)`), the `ζ`-integral of
  `m_S 1{λ_α ∈ B}` is at most `d/√(2πs) |B|`; every rank, no condition on the exterior.
* `pole_probability`: uniformly in all `n ≥ 4`, `W`, both
  parities, models, ranks and pairs, `P♯_{α,S}{dist(λ_α, Spec H_R) < ε} ≤ n d (d+1) ε/√(2πs)`.
No normalization by a rank-sector mass occurs. -/
structure PairPoleExclusionContract : Prop where
  averaging : ∀ (p : Parameters) (model : p.GaussianRingModel) (α : Fin p.N) (i : ZMod p.n)
    (s : ℝ), 0 < s → s ≤ min p.c p.b →
    ∀ Pω : Measure (SplitState p i), IsPairSplitting p i model s Pω →
    ∀ᵐ x ∂(Pω.prod ((gueMeasure (PairSite p i) (pairTime p s)).map tracelessPart)),
      ∀ B : Set ℝ, MeasurableSet B →
        (∫⁻ ζ : ℝ, ENNReal.ofReal (pairMass p i α (assemble p i x.1 (x.2 + (ζ : ℂ) • 1))) *
            B.indicator 1 (physicalOrderedEigenvalue p (assemble p i x.1 (x.2 + (ζ : ℂ) • 1)) α)
          ∂(gaussianReal 0 (Real.toNNReal (s / (2 * (p.W : ℝ)) ^ 2)))) ≤
          ENNReal.ofReal (2 * (p.W : ℝ) / Real.sqrt (2 * Real.pi * s)) * volume B
  pole_probability : ∀ (p : Parameters) (model : p.GaussianRingModel) (α : Fin p.N)
    (i : ZMod p.n) (s : ℝ), 0 < s → s ≤ min p.c p.b → ∀ ε : ℝ, 0 < ε →
    physicalPairMeasure p model α i
        {H | ∃ μ : ℝ, (exteriorBlock p i H - (μ : ℂ) • 1).det = 0 ∧
          |physicalOrderedEigenvalue p H α - μ| < ε} ≤
      ENNReal.ofReal ((p.n : ℝ) * (2 * p.W) * (2 * p.W + 1) * ε / Real.sqrt (2 * Real.pi * s))

/-!
## Fresh Gaussian block: regularity
-/

section Fresh

variable {N : ℕ}

/-- `‖F‖ ≤ N^A` in operator norm. -/
def NormBound (F : Matrix (Fin N) (Fin N) ℂ) (A : ℝ) : Prop :=
  ∀ x : Fin N → ℂ, l2Norm (F *ᵥ x) ≤ (N : ℝ) ^ A * l2Norm x

/-- `m_s(z)`: the solution with positive imaginary part of
`m = ⟨(F - z - s m)⁻¹⟩` (unique for `Im z ≥ 0`; zero if none exists). For real `z`
this is the boundary value used in the regularity condition and in `Γ`. -/
def freshDyson (F : Matrix (Fin N) (Fin N) ℂ) (s : ℝ) (z : ℂ) : ℂ := by
  classical
  exact if h : ∃ m : ℂ, 0 < m.im ∧ m = (N : ℂ)⁻¹ * (F - (z + (s : ℂ) * m) • 1)⁻¹.trace
    then Classical.choose h else 0

/-- `M_s(z) = (F - z - s m_s(z))⁻¹`. -/
def freshM (F : Matrix (Fin N) (Fin N) ℂ) (s : ℝ) (z : ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  (F - (z + (s : ℂ) * freshDyson F s z) • 1)⁻¹

/-- Fresh regularity: `v₀ ≤ Im m_s(x+iη) ≤ v₀⁻¹` for `s ∈ [c₀-s₀, c₀]`,
`|x-E| ≤ r₀`, `0 ≤ η ≤ 1`. -/
def FreshRegular (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E r₀ s₀ v₀ : ℝ) : Prop :=
  ∀ s ∈ Set.Icc (c₀ - s₀) c₀, ∀ x : ℝ, |x - E| ≤ r₀ → ∀ η ∈ Set.Icc (0 : ℝ) 1,
    v₀ ≤ (freshDyson F s ⟨x, η⟩).im ∧ (freshDyson F s ⟨x, η⟩).im ≤ v₀⁻¹

/-- The admissible fixed constants of the fresh regularity condition. -/
def FreshConstants (c₀ r₀ s₀ v₀ : ℝ) : Prop :=
  0 < c₀ ∧ c₀ < 1 ∧ 0 < r₀ ∧ 0 < s₀ ∧ s₀ < c₀ / 2 ∧ 0 < v₀

/-- The fresh deformation class: Hermitian `F` with `‖F‖ ≤ N^A`, regular at `(c₀, E)`. -/
def FreshClass (F : Matrix (Fin N) (Fin N) ℂ) (A c₀ E r₀ s₀ v₀ : ℝ) : Prop :=
  F.IsHermitian ∧ NormBound F A ∧ FreshRegular F c₀ E r₀ s₀ v₀

/-- `Γ = c₀ |F - E - c₀ m_{c₀}(E)|^{-2}` (so `Tr Γ = N` under regularity). -/
def freshGamma (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  let X := F - ((E : ℂ) + (c₀ : ℂ) * freshDyson F c₀ E) • 1
  (c₀ : ℂ) • (Xᴴ * X)⁻¹

/-- Increasing eigenvalue of rank `ℓ`. -/
def freshEigenvalue (K : Matrix (Fin N) (Fin N) ℂ) (ℓ : Fin N) : ℝ :=
  rawIncreasingEigenvalue (Fin.cast (Fintype.card_fin N).symm ℓ) K

/-- Selected unit eigenvector of rank `ℓ` (phase-free in every use below). -/
def freshEigenvector (K : Matrix (Fin N) (Fin N) ℂ) (ℓ : Fin N) : Fin N → ℂ :=
  rawOrderedColumnSelection (Fin.cast (Fintype.card_fin N).symm ℓ) K

/-- Law of the traceless part `A⁰_N` of `A_N ~ GUE_N(c₀/N)`. -/
def freshTracelessLaw (N : ℕ) (c₀ : ℝ) : Measure (Matrix (Fin N) (Fin N) ℂ) :=
  (gueMeasure (Fin N) (Real.toNNReal (c₀ / N))).map tracelessPart

/-- Scalar Palm weight `w_{ℓ,E} = φ_{√c₀/N}(E - ν⁰_ℓ)`. -/
def palmWeight (F : Matrix (Fin N) (Fin N) ℂ) (c₀ E : ℝ) (ℓ : Fin N)
    (A0 : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  BlockBand.Palm.scalarWeight (Real.toNNReal c₀) N E (freshEigenvalue (F + A0) ℓ)

/-- `|√N q* u_ℓ|²` for the eigenvector `u_ℓ` of `F + A⁰`. -/
def palmOverlap (F : Matrix (Fin N) (Fin N) ℂ) (q : Fin N → ℂ) (ℓ : Fin N)
    (A0 : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  (N : ℝ) * ‖star q ⬝ᵥ freshEigenvector (F + A0) ℓ‖ ^ 2

end Fresh

/-- **The fresh Palm theorem.** Fixed `0 < c₀ < 1`, `r₀, s₀, v₀ > 0`, `s₀ < c₀/2`, and the polynomial
norm exponent `A` come first; then each order `r ≥ 1` has `κ_r > 0` and `C_r`; then
every `K > 0` has `C_{r,K}`; uniformly in `N ≥ 1`, every Hermitian `F` with
`‖F‖ ≤ N^A` regular at `(c₀, E)`, every deterministic `q ∈ ℂ^N` and every ordered
rank `ℓ`:
`|E[w_{ℓ,E} |√N q*u_ℓ|^{2r}] - r!(q*Γq)^r Z_{ℓ,E}| ≤ C_r(N^{-κ_r} Z_{ℓ,E} + C_{r,K} N^{-K})(q*Γq)^r`.
The expectation is over the traceless part `A⁰` of `A_N ~ GUE_N(c₀/N)`;
`Z = E w`.
No lower bound on `Z` is assumed and the order `r` is fixed before `N`.
-/
def FreshPalmContract : Prop :=
  ∀ A c₀ r₀ s₀ v₀ : ℝ, FreshConstants c₀ r₀ s₀ v₀ →
  ∀ r : ℕ, 1 ≤ r → ∃ κ : ℝ, 0 < κ ∧ ∃ Cr : ℝ, ∀ K : ℝ, 0 < K → ∃ CrK : ℝ,
    ∀ (N : ℕ), 0 < N → ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c₀ E r₀ s₀ v₀ →
    ∀ (q : Fin N → ℂ) (ℓ : Fin N),
      let Z := ∫ A0, palmWeight F c₀ E ℓ A0 ∂freshTracelessLaw N c₀
      let γ := quadForm (freshGamma F c₀ E) q
      |(∫ A0, palmWeight F c₀ E ℓ A0 * palmOverlap F q ℓ A0 ^ r ∂freshTracelessLaw N c₀) -
          (r.factorial : ℝ) * γ ^ r * Z| ≤
        Cr * ((N : ℝ) ^ (-κ) * Z + CrK * (N : ℝ) ^ (-K)) * γ ^ r

/-- **The coarse relative local law.** Under the fresh regularity condition (fixed constants and
norm exponent `A` first), for every fixed
family-size exponent `a` and failure exponent `D` there is `N₀`; for `N ≥ N₀`, every `F`
in the class, every `s ∈ [c₀-s₀, c₀]` and every deterministic family `Q` of at most `N^a`
vectors, with `G_N ~ GUE_N(1/N)` and `G_s(z) = (F + √s G_N - z)⁻¹`, the event that for
some `z = x+iη`, `|x-E| ≤ r₀/2`, `N^{-1/100} ≤ η ≤ 1`, either
`|⟨G_s(z)⟩ - m_s(z)| > N^{-1/3}` or `|q*(G_s - M_s)q| > N^{-1/3} q* Im M_s q` for some
`q ∈ Q`, has (outer) probability at most `N^{-D}` (`q* Im M q = Im(q* M q)`).
-/
def CoarseRelativeContract : Prop :=
  ∀ A c₀ r₀ s₀ v₀ : ℝ, FreshConstants c₀ r₀ s₀ v₀ → ∀ a D : ℝ, ∃ N₀ : ℕ,
    ∀ N : ℕ, N₀ ≤ N → ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c₀ E r₀ s₀ v₀ →
    ∀ s ∈ Set.Icc (c₀ - s₀) c₀, ∀ Q : Finset (Fin N → ℂ), (Q.card : ℝ) ≤ (N : ℝ) ^ a →
      gueMeasure (Fin N) (Real.toNNReal (1 / N))
          {G | ∃ x η : ℝ, |x - E| ≤ r₀ / 2 ∧ (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤ η ∧ η ≤ 1 ∧
            let z : ℂ := ⟨x, η⟩
            let R := (F + (Real.sqrt s : ℂ) • G - z • 1)⁻¹
            (N : ℝ) ^ (-(1 / 3 : ℝ)) < ‖(N : ℂ)⁻¹ * R.trace - freshDyson F s z‖ ∨
              ∃ q ∈ Q, (N : ℝ) ^ (-(1 / 3 : ℝ)) * (star q ⬝ᵥ (freshM F s z *ᵥ q)).im <
                ‖star q ⬝ᵥ ((R - freshM F s z) *ᵥ q)‖} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-D))

/-!
## Matrix Brownian flow and one-particle mass equations
-/

section Flow

variable {N : ℕ}

/-- Independent real Wiener coordinates driving the Hermitian matrix Brownian motion. -/
abbrev FlowNoise (N : ℕ) := ((Fin N × Fin N) × Fin 2) → CanonicalWienerPath

/-- Sample space: the Gaussian matrix at the initial variance and the Brownian noise. -/
abbrev FlowSample (N : ℕ) := Matrix (Fin N) (Fin N) ℂ × FlowNoise N

/-- Law of `(G_a, Brownian noise)`: `G_a ~ GUE_N(a/N)` independent of the noise. -/
def flowLaw (N : ℕ) (a : ℝ) : Measure (FlowSample N) :=
  (gueMeasure (Fin N) (Real.toNNReal (a / N))).prod (commonWienerLaw ((Fin N × Fin N) × Fin 2))

/-- Hermitian matrix Brownian increment with `E|B_ij(t)|² = t/N` (GUE normalization). -/
def hermitianBrownian (B : FlowNoise N) (t : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  let X := circularBrownianCoordinates (fun q => B q (Real.toNNReal t))
  Matrix.of fun a b => ((Real.sqrt (2 * N))⁻¹ : ℂ) * (X (a, b) + conj (X (b, a)))

/-- `H_σ = F + G_σ`, `G_σ = G_a + B(σ - a) ~ GUE_N(σ/N)` for `σ ≥ a`. -/
def flowMatrix (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N) (σ : ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  F + ω.1 + hermitianBrownian ω.2 (σ - a)

/-- Ordered eigenvalue path `λ_k(σ)` of `H_σ`. -/
def flowEigenvalue (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N) (σ : ℝ)
    (k : Fin N) : ℝ :=
  freshEigenvalue (flowMatrix F a ω σ) k

/-- Coupling `c_ij(σ) = 1/(N (λ_i - λ_j)²)` of the moment generator. -/
def flowRate (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N) (σ : ℝ)
    (k l : Fin N) : ℝ :=
  ((N : ℝ) * (flowEigenvalue F a ω σ k - flowEigenvalue F a ω σ l) ^ 2)⁻¹

/-- Rank distance `|k - l|` between labels. -/
def labelDist (k l : Fin N) : ℕ := Int.natAbs ((k : ℤ) - (l : ℤ))

/-- Generator of the short one-particle flow (`0 < |k-l| < ℓ`), as a matrix acting
on the row index: `(S f)_k = Σ_{0<|k-l|<ℓ} c_kl (f_l - f_k)`. -/
def shortGenerator (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N) (ℓ : ℕ)
    (σ : ℝ) (k l : Fin N) : ℝ := by
  classical
  exact if k = l then
      -∑ m ∈ Finset.univ.filter (fun m => m ≠ k ∧ labelDist k m < ℓ), flowRate F a ω σ k m
    else if labelDist k l < ℓ then flowRate F a ω σ k l else 0

/-- Total long coupling `β_k = Σ_{|k-l| ≥ ℓ} c_kl`. -/
def longCoupling (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N) (ℓ : ℕ)
    (σ : ℝ) (k : Fin N) : ℝ := by
  classical
  exact ∑ m ∈ Finset.univ.filter (fun m => ℓ ≤ labelDist k m), flowRate F a ω σ k m

/-- Reference generator: short rotations kept, killing `β̂_k = max(β_k, b₀N/ℓ)`. -/
def referenceGenerator (F : Matrix (Fin N) (Fin N) ℂ) (a b₀ : ℝ) (ω : FlowSample N) (ℓ : ℕ)
    (σ : ℝ) (k l : Fin N) : ℝ :=
  shortGenerator F a ω ℓ σ k l -
    if k = l then max (longCoupling F a ω ℓ σ k) (b₀ * N / ℓ) else 0

/-- Forward mass equation `∂_u v = L(u) v` on `[s,u]` with `v(s) = v₀`. For the
generator of a propagator `𝓜_{s,u}`, `v_k(u) = E_aux Σ_j |(𝓜_{s,u})_{kj}|² (v₀)_j`. -/
def ForwardMassSolution (L : ℝ → Fin N → Fin N → ℝ) (s u : ℝ) (v₀ : Fin N → ℝ)
    (v : ℝ → Fin N → ℝ) : Prop :=
  v s = v₀ ∧ ContinuousOn v (Set.Icc s u) ∧
    ∀ x ∈ Set.Ioo s u, HasDerivAt v (fun k => ∑ l, L x k l * v x l) x

/-- Mean-square propagator `P(s)_{kj} = E_aux |(𝓜_{s,c})_{kj}|²` as a function of the
starting time: `∂_s P(s) = -P(s) L(s)` on `[a,c]`, `P(c) = I`. -/
def BackwardPropagator (L : ℝ → Fin N → Fin N → ℝ) (a c : ℝ) (P : ℝ → Fin N → Fin N → ℝ) :
    Prop :=
  P c = (fun k l => if k = l then 1 else 0) ∧ ContinuousOn P (Set.Icc a c) ∧
    ∀ x ∈ Set.Ioo a c, HasDerivAt P (fun k l => -∑ m, P x k m * L x m l) x

end Flow

/-- Relative localization of the matrix Brownian flow.
* `reference_finite_speed` (finite speed of the reference flow): the scales
  `θ = 1/500`, `t = N^{-θ}`, `a = c - t`, `κ = 13/5000`, `ε = 1/10000`,
  `ℓ = ⌊N^{1-κ}⌋`, `w = ⌈N√t N^{2ε}⌉`; `k₀` the first rank above `E` at time `a`,
  `J = {j : |j-k₀| ≤ w}`. For every fixed `b₀ > 0` (reference damping floor), every
  fixed terminal window constant `C` and every `D`, for `N ≥ N₀`, outside a set of
  eigenvalue paths of probability at most `N^{-D}`, every terminal label `k` with
  `|λ_k(c) - E| ≤ C/N` has `∫_a^c Σ_{j∉J} E_aux|(𝓜_{s,c})_{kj}|² ds ≤ N^{-D}`. -/
structure RelativeLocalizationContract : Prop where
  reference_finite_speed : ∀ A c r₀ s₀ v₀ : ℝ, FreshConstants c r₀ s₀ v₀ →
    ∀ b₀ : ℝ, 0 < b₀ → ∀ Cw D : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c E r₀ s₀ v₀ →
      let t : ℝ := (N : ℝ) ^ (-(1 / 500 : ℝ))
      let a : ℝ := c - t
      let ℓ : ℕ := ⌊(N : ℝ) ^ (1 - 13 / 5000 : ℝ)⌋₊
      let w : ℕ := ⌈(N : ℝ) * Real.sqrt t * (N : ℝ) ^ (2 * (1 / 10000 : ℝ))⌉₊
      flowLaw N a {ω | ∃ k : Fin N, |flowEigenvalue F a ω c k - E| ≤ Cw / N ∧
          ∃ P, BackwardPropagator (referenceGenerator F a b₀ ω ℓ) a c P ∧
            ENNReal.ofReal ((N : ℝ) ^ (-D)) <
              ∫⁻ s in Set.Icc a c, ENNReal.ofReal (∑ j : Fin N,
                (if Int.natAbs ((j : ℤ) -
                    ((Finset.univ.filter fun l : Fin N => flowEigenvalue F a ω a l ≤ E).card : ℤ)) ≤ w
                  then 0 else 1) * P s k j)} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-D))
  short_row : ∀ A c r₀ s₀ v₀ : ℝ, FreshConstants c r₀ s₀ v₀ →
    ∀ ε : ℝ, 0 < ε → ∃ c' : ℝ, 0 < c' ∧ ∀ D : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c E r₀ s₀ v₀ →
      let a : ℝ := c - (N : ℝ) ^ (-(1 / 100 : ℝ))
      let ℓ : ℕ := ⌊(N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊
      let R : ℝ := (N : ℝ) ^ ε * ℓ
      ∀ s u : ℝ, a ≤ s → s ≤ u → u ≤ c → ∀ k : Fin N,
        flowLaw N a {ω | |flowEigenvalue F a ω s k - E| ≤ r₀ / 16 ∧
            ∃ v, ForwardMassSolution (shortGenerator F a ω ℓ) s u
              (fun j => if R < (labelDist k j : ℝ) then 1 else 0) v ∧
              Real.exp (-(c' * (N : ℝ) ^ ε)) < v u k} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D))
  short_column : ∀ A c r₀ s₀ v₀ : ℝ, FreshConstants c r₀ s₀ v₀ →
    ∀ ε : ℝ, 0 < ε → ∃ c' : ℝ, 0 < c' ∧ ∀ D : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c E r₀ s₀ v₀ →
      let a : ℝ := c - (N : ℝ) ^ (-(1 / 100 : ℝ))
      let ℓ : ℕ := ⌊(N : ℝ) ^ (1 - (1 / 100 : ℝ) / 3)⌋₊
      let R : ℝ := (N : ℝ) ^ ε * ℓ
      ∀ s u : ℝ, a ≤ s → s ≤ u → u ≤ c → ∀ k : Fin N,
        flowLaw N a {ω | |flowEigenvalue F a ω s k - E| ≤ r₀ / 16 ∧
            ∃ v, ForwardMassSolution (shortGenerator F a ω ℓ) s u
              (fun j => if j = k then 1 else 0) v ∧
              Real.exp (-(c' * (N : ℝ) ^ ε)) <
                ∑ j : Fin N, (if R < (labelDist k j : ℝ) then 1 else 0) * v u j} ≤
          ENNReal.ofReal ((N : ℝ) ^ (-D))

/-!
## Fixed-deformation eigenpair density and the good spectral event
-/

section FreshDensity

variable {N : ℕ}

/-- A measurable orthonormal frame `U_v` of `v^⊥ ⊂ ℂ^N` for unit vectors `v`. -/
def IsFreshFrame (U : (Fin N → ℂ) → Matrix (Fin N) (Fin (N - 1)) ℂ) : Prop :=
  Measurable U ∧ ∀ v : Fin N → ℂ, l2Norm v = 1 → (U v)ᴴ * U v = 1 ∧ (U v)ᴴ *ᵥ v = 0

/-- `M = U_v* F U_v + G_{N-1} - E` for a deterministic deformation `F`. -/
def freshFrameM (U : (Fin N → ℂ) → Matrix (Fin N) (Fin (N - 1)) ℂ)
    (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ) (v : Fin N → ℂ)
    (G' : Matrix (Fin (N - 1)) (Fin (N - 1)) ℂ) : Matrix (Fin (N - 1)) (Fin (N - 1)) ℂ :=
  (U v)ᴴ * F * U v + G' - (E : ℂ) • 1

/-- `G = E vv* + U_v (U_v* F U_v + G_{N-1}) U_v* - F`, so `F + G` has eigenpair `(E, v)`. -/
def freshReconstructed (U : (Fin N → ℂ) → Matrix (Fin N) (Fin (N - 1)) ℂ)
    (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ) (v : Fin N → ℂ)
    (G' : Matrix (Fin (N - 1)) (Fin (N - 1)) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  (E : ℂ) • vecMulVec v (star v) + U v * ((U v)ᴴ * F * U v + G') * (U v)ᴴ - F

/-- Density at energy `E` of the rank-`ℓ` eigenpair of `F + GUE_N(t)`, tested against
`g(v, G)`: `∫dν_N(v) ∫dGUE_{N-1}(t)(G') c_{N,t} 𝓡(E,v,F) det(M)² 1{N_-(M) = ℓ} g(v, G_rec)`. -/
def freshEigenpairFiber (F : Matrix (Fin N) (Fin N) ℂ) (t : ℝ≥0) (ℓ : Fin N)
    (U : (Fin N → ℂ) → Matrix (Fin N) (Fin (N - 1)) ℂ) (E : ℝ)
    (g : (Fin N → ℂ) → Matrix (Fin N) (Fin N) ℂ → ℝ≥0∞) : ℝ≥0∞ := by
  classical
  exact ∫⁻ v, ∫⁻ G',
    ENNReal.ofReal (coareaConstant N t * regressionFactor t E v F *
        Complex.normSq (freshFrameM U F E v G').det) *
      (if negativeCount (freshFrameM U F E v G') = ℓ.val then 1 else 0) *
      g v (freshReconstructed U F E v G')
    ∂(gueMeasure (Fin (N - 1)) t) ∂(projectiveHaar (Fin N))

end FreshDensity

/-- The fixed-deformation eigenpair density.
* `frame_exists`: a measurable frame of `v^⊥` exists.
* `density`: for every `N ≥ 1`, Hermitian `F`, `t > 0`, rank `ℓ`, measurable frame and
  measurable `g ≥ 0`: `∫ g dGUE_N(t) = ∫dE ∫dν_N ∫dGUE_{N-1}(t) c_{N,t}𝓡|det M|²1{N_-(M)=ℓ} g(G_rec)`.
* `palm`: with `t = c₀/N` (`c₀ > 0`) and the traceless part `A⁰` of `GUE_N(c₀/N)`, for every
  measurable `f ≥ 0` of the eigenprojector and every `E`,
  `E_{A⁰}[w_{ℓ,E} f(u_ℓu_ℓ*)] = ∫dν_N ∫dGUE_{N-1} c_{N,t}𝓡|det M|²1{N_-(M)=ℓ} f(vv*)`. -/
structure FreshEigenpairDensityContract : Prop where
  frame_exists : ∀ (N : ℕ), 0 < N →
    ∃ U : (Fin N → ℂ) → Matrix (Fin N) (Fin (N - 1)) ℂ, IsFreshFrame U
  density : ∀ (N : ℕ), 0 < N → ∀ (F : Matrix (Fin N) (Fin N) ℂ), F.IsHermitian →
    ∀ (t : ℝ≥0), 0 < t → ∀ (ℓ : Fin N) (U : (Fin N → ℂ) → Matrix (Fin N) (Fin (N - 1)) ℂ),
    IsFreshFrame U → ∀ g : Matrix (Fin N) (Fin N) ℂ → ℝ≥0∞, Measurable g →
      (∫⁻ G, g G ∂gueMeasure (Fin N) t) =
        ∫⁻ E : ℝ, freshEigenpairFiber F t ℓ U E (fun _ G => g G)
  palm : ∀ (N : ℕ), 0 < N → ∀ (F : Matrix (Fin N) (Fin N) ℂ), F.IsHermitian →
    ∀ (c₀ : ℝ), 0 < c₀ → ∀ (ℓ : Fin N) (U : (Fin N → ℂ) → Matrix (Fin N) (Fin (N - 1)) ℂ),
    IsFreshFrame U → ∀ f : Matrix (Fin N) (Fin N) ℂ → ℝ≥0∞, Measurable f →
      ∀ E : ℝ, (∫⁻ A0, ENNReal.ofReal (palmWeight F c₀ E ℓ A0) *
            f (vecMulVec (freshEigenvector (F + A0) ℓ) (star (freshEigenvector (F + A0) ℓ)))
          ∂freshTracelessLaw N c₀) =
        freshEigenpairFiber F (Real.toNNReal (c₀ / N)) ℓ U E (fun v _ => f (vecMulVec v (star v)))

/-- **The good spectral event `𝓡`**: the long-gap bound together with the counts, long couplings
and displacement bound that define `𝓡`, at the scales `θ = 1/500`, `t = N^{-θ}`, `a = c - t`,
`κ = 13/5000`, `ℓ = ⌊N^{1-κ}⌋`, `h = N^{-1/100}`.
Fixed regularity constants and `A` first; then fixed `c₁, C₁, C, b₀ > 0`;
then every `D` has `N₀`; for `N ≥ N₀` and every `F` in the class, outside an outer
probability `N^{-D}`, simultaneously for all `s ∈ [a,c]`:
1. `|λ_i - λ_j| ≥ c₁|i-j|/N` for `|i-j| ≥ ℓ`;
2. `|λ_i - λ_j| ≤ C₁ℓ/N` for `|i-j| < ℓ` with `min(|λ_i-E|,|λ_j-E|) ≤ r₀/8`;
3. the coarse upper count `#{i: λ_i(s) ∈ [x,y]} ≤ C N((y-x) + h)` for all `x ≤ y` (the
 "coarse count event", defined here) and the bulk lower count
 `#{i: λ_i(s) ∈ [x,y]} ≥ c₁ N (y-x)` for `[x,y] ⊂ [E - r₀/8, E + r₀/8]`, `y - x ≥ ℓ/N`;
4. `β_i(s) ≤ C N/ℓ` for all `i`, and `β_i(s) ≥ b₀ N/ℓ` when `|λ_i(s) - E| ≤ r₀/8`
 (so `β̂ = β` there for the reference generator with this `b₀`);
5. `‖H_s - H_a‖ ≤ C√t` (operator norm).
The bad set is a set of eigenvalue paths except for clause 5 (a matrix-path condition).
-/
def SpectralGoodEventContract : Prop :=
  ∀ A c r₀ s₀ v₀ : ℝ, FreshConstants c r₀ s₀ v₀ →
  ∃ c₁ C₁ C b₀ : ℝ, 0 < c₁ ∧ 0 < C₁ ∧ 0 < C ∧ 0 < b₀ ∧
    ∀ D : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c E r₀ s₀ v₀ →
      let t : ℝ := (N : ℝ) ^ (-(1 / 500 : ℝ))
      let a : ℝ := c - t
      let ℓ : ℕ := ⌊(N : ℝ) ^ (1 - 13 / 5000 : ℝ)⌋₊
      let h : ℝ := (N : ℝ) ^ (-(1 / 100 : ℝ))
      flowLaw N a {ω | ¬ ∀ s ∈ Set.Icc a c,
        (∀ i j : Fin N, ℓ ≤ labelDist i j →
          c₁ * (labelDist i j : ℝ) / N ≤ |flowEigenvalue F a ω s i - flowEigenvalue F a ω s j|) ∧
        (∀ i j : Fin N, labelDist i j < ℓ →
          min |flowEigenvalue F a ω s i - E| |flowEigenvalue F a ω s j - E| ≤ r₀ / 8 →
          |flowEigenvalue F a ω s i - flowEigenvalue F a ω s j| ≤ C₁ * ℓ / N) ∧
        (∀ x y : ℝ, x ≤ y →
          ((Finset.univ.filter fun i : Fin N =>
              flowEigenvalue F a ω s i ∈ Set.Icc x y).card : ℝ) ≤ C * N * ((y - x) + h)) ∧
        (∀ x y : ℝ, E - r₀ / 8 ≤ x → y ≤ E + r₀ / 8 → (ℓ : ℝ) / N ≤ y - x →
          c₁ * N * (y - x) ≤
            ((Finset.univ.filter fun i : Fin N =>
              flowEigenvalue F a ω s i ∈ Set.Icc x y).card : ℝ)) ∧
        (∀ i : Fin N, longCoupling F a ω ℓ s i ≤ C * N / ℓ ∧
          (|flowEigenvalue F a ω s i - E| ≤ r₀ / 8 → b₀ * N / ℓ ≤ longCoupling F a ω ℓ s i)) ∧
        (∀ x : Fin N → ℂ, l2Norm ((flowMatrix F a ω s - flowMatrix F a ω a) *ᵥ x) ≤
          C * Real.sqrt t * l2Norm x)} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-D))

end BlockBand.Internal.Contracts.CoareaPalm
