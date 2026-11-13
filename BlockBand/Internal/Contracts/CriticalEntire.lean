module

public import BlockBand.Statements
public import BlockBand.Critical.Entire.RandomEntire
public import BlockBand.Critical.FiniteReadback
public import BlockBand.Critical.PhysicalProfiles
public import BlockBand.Internal.Contracts.TransmissionLaws
public import BlockBand.Internal.Contracts.Critical

/-!
# The entire-law and joint recovery statements

The finite determinant `D_W(z) = det(H - E + W⁻² Σ_a z_a Q_a)/det(H - E)` with profile sources,
its critical limit in law as a random entire function, the determining hierarchy of bounded
inverse moments on the positive imaginary cone built from the global Gaussian source law and the
canonical closing matrix, and the root/derivative rule recovering the marked critical process.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Internal.Contracts.CriticalEntire

open MeasureTheory Filter Topology
open BlockBand.Critical.Entire
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open scoped ComplexConjugate Matrix

/-!
## 1. Profile families and the finite determinant
-/

/-- The full source family `q_0 = 1, q_1, …, q_k`: coordinate `0` is the constant profile `1`
(so `Q_0 = I`), coordinates `1, …, k` are `q`. -/
def fullProfile {k : ℕ} (q : Fin k → C(Torus, ℝ)) : Fin (k + 1) → C(Torus, ℝ) :=
  Fin.cons (ContinuousMap.const Torus 1) q

/-- The spatial profiles are nonnegative (bounded nonnegative continuous functions on `𝕋`;
boundedness is automatic on the compact torus). -/
def IsProfileFamily {k : ℕ} (q : Fin k → C(Torus, ℝ)) : Prop :=
  ∀ a x, 0 ≤ q a x

/-- **The finite determinant** as a function of the physical matrix `H`:
`D_W(z) = det(H - E + W⁻² Σ_a z_a Q_a) / det(H - E)`, `Q_a = profileSourceMatrix (Q a)`
(block `j` multiplied by `Q a (j/n)`), physical row-variance-one `H`, physical scale `W⁻²`
(never `N⁻¹`), written `numerator * det(H - E)⁻¹`. Lean's `0⁻¹ = 0` makes this total: on the
null set `det(H - E) = 0` (`GaussianRingModel.ae_baseDeterminant_ne_zero`) it is the zero
function, which does not affect the law. Off that set it is `physicalFiniteDeterminant`. -/
def finiteEntireDeterminant (p : Parameters) (E : ℝ) {m : ℕ} (Q : Fin m → C(Torus, ℝ))
    (H : p.SiteMatrix) : EntireFunction m :=
  EntireFunction.ofDifferentiable
    (fun z => BlockBand.Critical.finiteCharacteristicDeterminant (H - (E : ℂ) • 1)
        (fun a => p.profileSourceMatrix (Q a)) (BlockBand.Critical.widthSourceScale p.W) z *
      ((H - (E : ℂ) • 1).det)⁻¹)
    ((BlockBand.Critical.differentiable_finiteCharacteristicDeterminant _ _ _).mul_const _)

/-- Law of `D_W` under the exact physical Gaussian ring law of a finite realization, as a
random element of the compact-open (locally uniform) Borel space `EntireFunction m`. -/
def finiteEntireLaw {p : Parameters} (R : FiniteRealization p) (E : ℝ) {m : ℕ}
    (Q : Fin m → C(Torus, ℝ)) : RandomEntire m :=
  R.model.law.map (finiteEntireDeterminant p E Q)

/-- `μ` is the critical limit in law of `D_W`: along **every** critical sequence
(`W → ∞`, `n/W → τ`, any parity, no rate) and every choice of finite realizations, the laws of
`D_W` for the family `1, q_1, …, q_k` converge weakly in the compact-open topology to `μ`.
Same binder pattern as the convergence clause of `IsCriticalFamily`. -/
def IsEntireLimit (b E : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (τ : PositiveRatio) {k : ℕ}
    (q : Fin k → C(Torus, ℝ)) (μ : RandomEntire (k + 1)) : Prop :=
  ∀ s : CriticalSequence τ.1, ∀ R : ∀ j, FiniteRealization (s.parameters b hb hb' j),
    Tendsto (fun j => finiteEntireLaw (R j) E (fullProfile q)) atTop (𝓝 μ)

/-!
## 2. Bounded inverse moments on the positive imaginary cone
-/

/-- The cone point `i y`, `y ∈ [0,∞)^m`. -/
def conePoint {m : ℕ} (y : Fin m → ℝ) : Fin m → ℂ :=
  fun a => (y a : ℂ) * Complex.I

/-- Factor of the bounded inverse moments: `w⁻¹` for sign `+1`, `conj(w⁻¹)` for `-1`. -/
def mixedInverseFactor (σ : ℤˣ) (w : ℂ) : ℂ :=
  if σ = 1 then w⁻¹ else conj w⁻¹

/-- The mixed inverse moment `E Π_{σ_j=1} D(iy^{(j)})⁻¹ Π_{σ_j=-1} conj(D(iy^{(j)})⁻¹)`. -/
def mixedInverseMoment {m J : ℕ} (μ : RandomEntire m) (y : Fin J → Fin m → ℝ)
    (σ : Fin J → ℤˣ) : ℂ :=
  ∫ F, ∏ j, mixedInverseFactor (σ j) (F (conePoint (y j))) ∂(μ : Measure (EntireFunction m))

/-- Every inverse value on the closed positive imaginary cone lies in the closed unit disk
(`|D(iy)| ≥ 1` on the positive imaginary cone). -/
def HasInverseConeBound {m : ℕ} (μ : RandomEntire m) : Prop :=
  ∀ y : Fin m → ℝ, (∀ a, 0 ≤ y a) →
    ∀ᵐ F ∂(μ : Measure (EntireFunction m)), 1 ≤ ‖F (conePoint y)‖

/-- One global probe per factor, with profile `Σ_a y_a^{(j)} q_a`. -/
def probeProfile {k J : ℕ} (q : Fin k → C(Torus, ℝ)) (y : Fin J → Fin (k + 1) → ℝ) :
    Fin J → C(Torus, ℝ) :=
  fun j => ∑ a, y j a • fullProfile q a

/-!
## 3. The global Gaussian source law
-/

/-- Probe mass `m_a = τ ∫_𝕋 q_a` (Haar probability measure on `𝕋 = ℝ/ℤ`). -/
def probeMass (τ : ℝ) (Q : C(Torus, ℝ)) : ℝ :=
  τ * ∫ r, Q r

/-- Birth density `q_a(t/τ)/m_a` on `[0,τ]`. For a zero-mass group (then `q_a ≡ 0`) the density
is undefined; the group is identically zero and is zeroed in `groupedSourceMatrix`, so any
admissible time law may be used: we take uniform. Orientation: a tag born at time `t` carries
the profile value `q(t/τ)`; the paper fixes neither the direction nor the origin of time along
the ring. The statement does not depend on this choice (all probes of one moment share the same
map, and the ring law is invariant under rotations and reflections), but a proof must establish
that invariance. -/
def birthDensity (τ : ℝ) (Q : C(Torus, ℝ)) (t : ℝ) : ℝ :=
  if 0 < probeMass τ Q then Q (QuotientAddGroup.mk (t / τ)) / probeMass τ Q else τ⁻¹

/-- Law of one sampled birth time of a probe with profile `Q`. -/
def probeBirthLaw (τ : ℝ) (Q : C(Torus, ℝ)) : Measure ℝ :=
  (volume.restrict (Set.Icc 0 τ)).withDensity fun t => ENNReal.ofReal (birthDensity τ Q t)

/-- Tag `i : Fin (J*M)` is the `(finProdFinEquiv.symm i).2`-th sampled tag of probe group
`(finProdFinEquiv.symm i).1`. -/
def tagGroup {J M : ℕ} (i : Fin (J * M)) : Fin J :=
  (finProdFinEquiv.symm i).1

/-- `M` independent birth times per group, all groups independent. -/
def sampledBirthLaw (τ : ℝ) {J : ℕ} (Q : Fin J → C(Torus, ℝ)) (M : ℕ) :
    Measure (Fin (J * M) → ℝ) :=
  Measure.pi fun i => probeBirthLaw τ (Q (tagGroup i))

/-- Mass `m_a` of every tag of group `a` ("a mass-`m_a` Gaussian tag at each sampled time"). -/
def tagMasses (τ : ℝ) {J : ℕ} (Q : Fin J → C(Torus, ℝ)) (M : ℕ) : Fin (J * M) → ℝ :=
  fun i => probeMass τ (Q (tagGroup i))

/-- Distinct, positive birth times before the terminal time `τ`.
-/
def IsAdmissibleBirthTimes (τ : ℝ) {n : ℕ} (t : Fin n → ℝ) : Prop :=
  Function.Injective t ∧ (∀ j, 0 < t j) ∧ ∀ j, t j < τ

/-- "At the terminal time sum its source matrix entries within the probe groups, with
coefficient `1/M`": `(1/M) Σ_{i,i'} 𝒦_{(a,i),(c,i')}`; zero-mass groups are identically zero. -/
def groupedSourceMatrix (τ : ℝ) {J : ℕ} (Q : Fin J → C(Torus, ℝ)) (M : ℕ)
    (K : Matrix (Fin (J * M)) (Fin (J * M)) ℂ) : Matrix (Fin J) (Fin J) ℂ :=
  fun a c =>
    if 0 < probeMass τ (Q a) ∧ 0 < probeMass τ (Q c) then
      (M : ℂ)⁻¹ * ∑ i : Fin M, ∑ i' : Fin M, K (finProdFinEquiv (a, i)) (finProdFinEquiv (c, i'))
    else 0

/-- For every admissible list `t`, `ν M t` is the complex source limit at time `τ` with
mass-`m_a` tags born at `t` (all groups use the same current noise: one model for all `J*M`
tags).
-/
def IsSampledSourceFamily (b E τ : ℝ) {J : ℕ} (Q : Fin J → C(Torus, ℝ))
    (ν : ∀ M : ℕ, (Fin (J * M) → ℝ) → Measure (SourceData (J * M))) : Prop :=
  ∀ (M : ℕ) (t : Fin (J * M) → ℝ), IsAdmissibleBirthTimes τ t →
    IsComplexSourceLimit b E τ t (tagMasses τ Q M) (ν M t)

/-- Value of a bounded continuous test `Φ` of the `M`-sampled grouped matrix: average over the
sampled times of the source law (component `0` of `SourceData` is `𝒦`). -/
def sampledProbeValue (τ : ℝ) {J : ℕ} (Q : Fin J → C(Torus, ℝ)) (M : ℕ)
    (ν : (Fin (J * M) → ℝ) → Measure (SourceData (J * M)))
    (Φ : BoundedContinuousFunction (Matrix (Fin J) (Fin J) ℂ) ℝ) : ℝ :=
  ∫ t, ∫ y, Φ (groupedSourceMatrix τ Q M (y 0)) ∂(ν t) ∂(sampledBirthLaw τ Q M)

/-- **`κ` is the law of the limiting global source matrix `𝒦`** for `J` probes with profiles
`Q` (the explicit construction of the global Gaussian source): the sampled finite-source family
exists, and for every such family the `M`-sampled grouped laws converge weakly to `κ` as
`M → ∞`. `B = -η⁻¹ Im 𝒦` is a function of `𝒦` (`probeGram`), so this determines the joint law
of `(𝒦, B)`. -/
def IsGlobalProbeLaw (b E τ : ℝ) {J : ℕ} (Q : Fin J → C(Torus, ℝ))
    (κ : Measure (Matrix (Fin J) (Fin J) ℂ)) : Prop :=
  IsProbabilityMeasure κ ∧ (∃ ν, IsSampledSourceFamily b E τ Q ν) ∧
    ∀ ν, IsSampledSourceFamily b E τ Q ν →
      ∀ Φ : BoundedContinuousFunction (Matrix (Fin J) (Fin J) ℂ) ℝ,
        Tendsto (fun M => sampledProbeValue τ Q M (ν M) Φ) atTop (𝓝 (∫ K, Φ K ∂κ))

/-!
## 4. The canonical closing matrix `𝖢_r(0)`
-/

/-- Laplace functional of the unit-intensity sine process on `ℝ` with independent standard
circular Gaussian decorations `g_j ∈ ℂ^r`: the sine Fredholm expansion of `IsSineLaw` with
`1 - e^{-f(x)}` replaced by `1 - E_g e^{-f(x,g)}` (independent marking). -/
def decoratedSineLaplace (r : ℕ)
    (f : CompactlySupportedContinuousMap (ℝ × (Fin r → ℂ)) ℝ) : ℝ :=
  ∑' k : ℕ, ((-1 : ℝ) ^ k / (Nat.factorial k : ℝ)) *
    ∫ x : Fin k → ℝ,
      Matrix.det (fun i j : Fin k => sineKernel (x i) (x j)) *
        ∏ i : Fin k, (1 - ∫ g, Real.exp (-f (x i, g)) ∂circularVectorLaw (Fin r))
      ∂Measure.pi (fun _ : Fin k => volume)

/-- `Ξ = Σ_j δ_{(x_j, g_j)}` is the decorated sine process on `(Ω, P)`: simple ground process and
the decorated sine Laplace functional for every nonnegative compactly supported continuous
test (this determines the law of the marked process). -/
structure IsDecoratedSineProcess (r : ℕ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Ξ : Ω → VaguePointMeasure (ℝ × (Fin r → ℂ))) : Prop where
  prob : IsProbabilityMeasure P
  measurable : Measurable Ξ
  simple : ∀ᵐ ω ∂P, ∀ x : ℝ, (Ξ ω).measure ({x} ×ˢ Set.univ) ≤ 1
  laplace : ∀ f : CompactlySupportedContinuousMap (ℝ × (Fin r → ℂ)) ℝ, (∀ z, 0 ≤ f z) →
    ∫ ω, Real.exp (-∫ z, f z ∂(Ξ ω).measure) ∂P = decoratedSineLaplace r f

/-- Entry `(i,j)` of the symmetric cutoff `π⁻¹ Σ_{|x_j| ≤ R} g_j g_j^* / x_j` at `z = 0`. -/
def truncatedCauchyEntry (r : ℕ) (ξ : VaguePointMeasure (ℝ × (Fin r → ℂ))) (R : ℝ)
    (i j : Fin r) : ℂ :=
  ∫ z in {z : ℝ × (Fin r → ℂ) | |z.1| ≤ R},
    (((Real.pi * z.1)⁻¹ : ℝ) : ℂ) * (z.2 i * conj (z.2 j)) ∂ξ.measure

/-- **`C = 𝖢_r(0)`**: the boundary value at `0` of the canonical Cauchy matrix, i.e. the limit in
probability of the symmetric cutoff at `z = 0` (at `z = 0` no pole occurs almost surely), built
from one decorated sine process. -/
structure IsCanonicalCauchyAtZero (r : ℕ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Ξ : Ω → VaguePointMeasure (ℝ × (Fin r → ℂ))) (C : Ω → Matrix (Fin r) (Fin r) ℂ) :
    Prop where
  decorated : IsDecoratedSineProcess r P Ξ
  measurable : ∀ i j, Measurable fun ω => C ω i j
  limit : ∀ i j, TendstoInMeasure P (fun R ω => truncatedCauchyEntry r (Ξ ω) R i j) atTop
    (fun ω => C ω i j)

/-!
## 5. The limiting closed source matrix `𝒯`
-/

/-- `Re K = (K + K^*)/2`. -/
def matrixRePart {ι : Type*} [Fintype ι] (K : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (2 : ℂ)⁻¹ • (K + Kᴴ)

/-- `B = -Im 𝒦/η` (`Im` is `Critical.imPart`), `η = Im z_∂(E)` (`etaZ`, the matched parameter). -/
def probeGram (b E : ℝ) {ι : Type*} [Fintype ι] (K : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  -(((etaZ b E)⁻¹ : ℝ) : ℂ) • Critical.imPart K

/-- `𝒯 = Re 𝒦 + η B^{1/2} 𝖢_p(0) B^{1/2}`; `B^{1/2}` by the Hermitian continuous functional
calculus (`B` is Hermitian for every `𝒦`, and `⪰ 0` on the support). -/
def closedSourceMatrix (b E : ℝ) {J : ℕ} (K C : Matrix (Fin J) (Fin J) ℂ) :
    Matrix (Fin J) (Fin J) ℂ :=
  matrixRePart K + ((etaZ b E : ℝ) : ℂ) •
    (cfc Real.sqrt (probeGram b E K) * C * cfc Real.sqrt (probeGram b E K))

/-- `exp{-i Σ_j σ_j 𝒯_jj}`. -/
def closedSourcePhase {J : ℕ} (σ : Fin J → ℤˣ) (T : Matrix (Fin J) (Fin J) ℂ) : ℂ :=
  Complex.exp (-(Complex.I * ∑ j, (((σ j : ℤ) : ℂ) * T j j)))

/-- `v = E exp{−iΣ_j σ_j 𝒯_jj}` for `J` probes with profiles `Q`: a global source law and a
closing matrix `𝖢_J(0)` exist, and every such realization gives `v`. `𝖢_J(0)` is independent of
`𝒦` (product integral), one common `𝖢_J(0)` for all probes.
-/
def ClosedSourceMomentValue (b E τ : ℝ) {J : ℕ} (Q : Fin J → C(Torus, ℝ))
    (σ : Fin J → ℤˣ) (v : ℂ) : Prop :=
  (∃ κ, IsGlobalProbeLaw b E τ Q κ) ∧
  (∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (Ξ : Ω → VaguePointMeasure (ℝ × (Fin J → ℂ))) (C : Ω → Matrix (Fin J) (Fin J) ℂ),
      IsCanonicalCauchyAtZero J P Ξ C) ∧
  ∀ κ, IsGlobalProbeLaw b E τ Q κ →
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (Ξ : Ω → VaguePointMeasure (ℝ × (Fin J → ℂ))) (C : Ω → Matrix (Fin J) (Fin J) ℂ),
      IsCanonicalCauchyAtZero J P Ξ C →
        ∫ K, ∫ ω, closedSourcePhase σ (closedSourceMatrix b E K (C ω)) ∂P ∂κ = v

/-- `μ` satisfies the determining hierarchy: inverse values on the cone are in the unit disk, and
every mixed inverse moment equals the value of the positive construction with one global probe
of profile `Σ_a y_a^{(j)} q_a` per factor. -/
def IsDeterminingHierarchyLaw (b E : ℝ) (τ : PositiveRatio) {k : ℕ}
    (q : Fin k → C(Torus, ℝ)) (μ : RandomEntire (k + 1)) : Prop :=
  HasInverseConeBound μ ∧
    ∀ (J : ℕ) (y : Fin J → Fin (k + 1) → ℝ) (σ : Fin J → ℤˣ), (∀ j a, 0 ≤ y j a) →
      ClosedSourceMomentValue b E τ.1 (probeProfile q y) σ (mixedInverseMoment μ y σ)

/-!
## 6. The entire-law theorem
-/

/-- The entire-law theorem.
* `convergence`: `D_W` converges in law, locally uniformly on `ℂ^{k+1}`, to one law, the same
  along every critical sequence and realization ("unique").
* `characterization`: every such limit satisfies the bounded inverse-moment identities with `𝒯`
  the limiting closed source matrix built from the global source law and `𝖢_J(0)`.
* `coneBound`, a fact from the proof, stated because `determination` is only meaningful on this
  class: `|D(iy)| ≥ 1` on the cone.
* `determination`: on laws whose inverse values on the cone lie in the unit disk, the mixed
  inverse moments determine the law (stated for every `m`). -/
structure EntireLawContract : Prop where
  convergence : ∀ (b E : ℝ) (hb : 0 < b) (hb' : b < 1 / 2), -2 < E ∧ E < 2 →
    ∀ (τ : PositiveRatio) (k : ℕ) (q : Fin k → C(Torus, ℝ)), IsProfileFamily q →
      ∃ μ : RandomEntire (k + 1), IsEntireLimit b E hb hb' τ q μ
  characterization : ∀ (b E : ℝ) (hb : 0 < b) (hb' : b < 1 / 2), -2 < E ∧ E < 2 →
    ∀ (τ : PositiveRatio) (k : ℕ) (q : Fin k → C(Torus, ℝ)), IsProfileFamily q →
    ∀ μ : RandomEntire (k + 1), IsEntireLimit b E hb hb' τ q μ →
    ∀ (J : ℕ) (y : Fin J → Fin (k + 1) → ℝ) (σ : Fin J → ℤˣ), (∀ j a, 0 ≤ y j a) →
      ClosedSourceMomentValue b E τ.1 (probeProfile q y) σ (mixedInverseMoment μ y σ)
  coneBound : ∀ (b E : ℝ) (hb : 0 < b) (hb' : b < 1 / 2), -2 < E ∧ E < 2 →
    ∀ (τ : PositiveRatio) (k : ℕ) (q : Fin k → C(Torus, ℝ)), IsProfileFamily q →
    ∀ μ : RandomEntire (k + 1), IsEntireLimit b E hb hb' τ q μ → HasInverseConeBound μ
  determination : ∀ (m : ℕ) (μ μ' : RandomEntire m),
    HasInverseConeBound μ → HasInverseConeBound μ' →
    (∀ (J : ℕ) (y : Fin J → Fin m → ℝ) (σ : Fin J → ℤˣ), (∀ j a, 0 ≤ y j a) →
      mixedInverseMoment μ y σ = mixedInverseMoment μ' y σ) → μ = μ'

/-!
## 7. The root/derivative rule and the joint recovery theorem
-/

/-- Readout of one marked point `(u, ν)` on the family `1, q_1, …, q_k`:
`(u, (ν(q_a))_{a ≤ k})`, values cast to `ℂ` so they can be compared with derivative ratios. -/
def profileReadout {k : ℕ} (q : Fin k → C(Torus, ℝ)) (z : MarkedSpectralSpace) :
    ℝ × (Fin (k + 1) → ℂ) :=
  (z.1, fun a => ((∫ r, fullProfile q a r ∂(z.2 : Measure Torus) : ℝ) : ℂ))

/-- Laplace functional of the readout process `Σ_α δ_{(u_α, (ν_α(q_a))_a)}` under `law`. -/
def readoutLaplace {k : ℕ} (q : Fin k → C(Torus, ℝ))
    (law : ProbabilityMeasure MarkedPointMeasure)
    (f : CompactlySupportedContinuousMap (ℝ × (Fin (k + 1) → ℂ)) ℝ) : ℝ :=
  ∫ ξ, Real.exp (-∫ z, f (profileReadout q z) ∂ξ.marked.measure)
    ∂(law : Measure MarkedPointMeasure)

/-- Real zeros of `x ↦ F(x, 0, …, 0)`. -/
abbrev EnergyZero {m : ℕ} (F : EntireFunction (m + 1)) : Type :=
  {x : ℝ // F (BlockBand.Critical.energySource (x : ℂ)) = 0}

/-- The root/derivative point at a real zero `x`:
`(u, (∂_{z_a}D/∂_{z_0}D)(x,0,…,0))_a` with `u = -τρ(E)x`, `ρ = semicircleDensity`. -/
def rootDerivativePoint (E τ : ℝ) {m : ℕ} (F : EntireFunction (m + 1)) (x : ℝ) :
    ℝ × (Fin (m + 1) → ℂ) :=
  (-(τ * Parameters.semicircleDensity E) * x, fun a =>
    EntireFunction.partialDerivValue a F (BlockBand.Critical.energySource (x : ℂ)) /
      EntireFunction.partialDerivValue 0 F (BlockBand.Critical.energySource (x : ℂ)))

/-- Laplace functional of the extracted process `Σ_{real zeros x} δ_{rootDerivativePoint x}`
under the entire law `μ` (each zero counted once; zeros are a.s. simple). -/
def extractorLaplace (E τ : ℝ) {m : ℕ} (μ : RandomEntire (m + 1))
    (f : CompactlySupportedContinuousMap (ℝ × (Fin (m + 1) → ℂ)) ℝ) : ℝ :=
  ∫ F, Real.exp (-∑' x : EnergyZero F, f (rootDerivativePoint E τ F x))
    ∂(μ : Measure (EntireFunction (m + 1)))

/-- "It is explicitly constructed by … the determining hierarchy … and the following
root/derivative rule", for one finite family `1, q_1, …, q_k`: a law satisfying the determining
hierarchy exists, and for every such law `μ` of `D` the readout of `law` on that family has the
law of the root/derivative extraction from `D ~ μ`. -/
def RootDerivativeRule (b E : ℝ) (τ : PositiveRatio) {k : ℕ} (q : Fin k → C(Torus, ℝ))
    (law : ProbabilityMeasure MarkedPointMeasure) : Prop :=
  (∃ μ : RandomEntire (k + 1), IsDeterminingHierarchyLaw b E τ q μ) ∧
    ∀ μ : RandomEntire (k + 1), IsDeterminingHierarchyLaw b E τ q μ →
      ∀ f : CompactlySupportedContinuousMap (ℝ × (Fin (k + 1) → ℂ)) ℝ, (∀ z, 0 ≤ f z) →
        readoutLaplace q law f = extractorLaplace E τ.1 μ f

/-- The clauses of the joint recovery theorem for an all-ratio family at fixed `(b, E)`.
* `convergence`: `Ξ_W ⇒ family τ` along every critical sequence (both parities, no rate) and
  every realization, in the marked vague topology (compact spectral tests, weak marks), in the
  binder form of the convergence clause of `IsCriticalFamily`;
* `simple`, `unitIntensity`: simple spectral locations, unit spectral intensity;
* `construction`: `RootDerivativeRule` for every finite nonnegative family. -/
structure IsJointRecoveryFamily (b E : ℝ) (hb : 0 < b) (hb' : b < 1 / 2)
    (family : PositiveRatio → ProbabilityMeasure MarkedPointMeasure) : Prop where
  convergence : ∀ (τ : PositiveRatio) (s : CriticalSequence τ.1)
    (R : ∀ j, FiniteRealization (s.parameters b hb hb' j)),
      Tendsto (fun j => (R j).markedLaw E) atTop (𝓝 (family τ))
  simple : ∀ τ, HasSimpleSpectralLocations (family τ)
  unitIntensity : ∀ τ, HasUnitSpectralIntensity (family τ)
  construction : ∀ (τ : PositiveRatio) (k : ℕ) (q : Fin k → C(Torus, ℝ)), IsProfileFamily q →
    RootDerivativeRule b E τ q (family τ)

/-- **The joint recovery theorem.** For `0<b<1/2`, `−2<E<2` there is a unique family of marked
laws, one for each ratio `τ > 0`, satisfying `IsJointRecoveryFamily`. Quantifier order: `b, E`
first; then one family for all `τ > 0`; then every critical sequence and realization.
-/
def JointRecoveryContract : Prop :=
  ∀ (b E : ℝ) (hb : 0 < b) (hb' : b < 1 / 2), -2 < E ∧ E < 2 →
    ∃! family : PositiveRatio → ProbabilityMeasure MarkedPointMeasure,
      IsJointRecoveryFamily b E hb hb' family

end BlockBand.Internal.Contracts.CriticalEntire
