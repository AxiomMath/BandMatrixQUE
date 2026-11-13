module

public import BlockBand.Internal.Contracts.TransmissionLaws
public import BlockBand.Internal.Contracts.TransmissionStatements

/-!
# Moving energies, length-uniform moments and dual boundary starts

Energy-uniform versions of the transmission statements along energies moving by `O(W⁻²)`,
conductance and jet moments uniform in the total path length, and the deletion law of the dual
diffusion started on the boundary of the chamber.

## Conventions

As in `TransmissionStatements` (`0 < b < 1/2`; "every fixed `p`" is `∀ p ≥ 1, ∃ C`; constants after
every fixed parameter and before `W`; "`W` sufficiently large" is `∃ W₀, ∀ W ≥ W₀`; `eLpNorm` at
`ENNReal.ofReal p`; nonnegative expectations are `lintegral`s of `‖·‖ₑ`), and in addition:
* **Compact bulk sets.** Finite-`W` bounds are uniform on `E ∈ bulkInterval κI` (base energy)
  and on every `E'` within `C_e W⁻²` of it, with `C, W₀` chosen before `E, E'`
  (as `PassiveInitialScalarContract`). Limit clauses fix the base `E ∈ (-2,2)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Internal.Contracts.TransmissionUniform

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped ENNReal NNReal Matrix

/-!
## 1. Moving energies
-/

/-- `E'` lies within `C W⁻²` of the base energy `E` at width `W`. -/
def IsNearEnergy (C : ℝ) (W : ℕ) (E E' : ℝ) : Prop :=
  |E' - E| ≤ C / (W : ℝ) ^ 2

/-- A deterministic moving energy `E_W = e W` with `|E_W - E| ≤ C W⁻²` for every `W ≥ 1` (as in
the unfolded window `E + u/(Nρ(E))`, `|u| ≤ U`, `N = nW`, `n ≥ cW`). -/
def IsMovingEnergy (E C : ℝ) (e : ℕ → ℝ) : Prop :=
  ∀ W : ℕ, 0 < W → IsNearEnergy C W E (e W)

/-- **`(P, μ)` is the critical limit of the transmission processes along the energies `e W`**:
`IsTransmissionLimit` with the width-`W` path evaluated at energy `e W` (and matched lead
`z_∂(e W)`). For `e = fun _ => E` this is exactly `IsTransmissionLimit b E κ P μ`. -/
structure IsTransmissionLimitAlong (b : ℝ) (e : ℕ → ℝ) (κ : ℝ → ℝ) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (μ : ℝ → Ω → FiniteMeasure unitInterval) : Prop where
  prob : IsProbabilityMeasure P
  measurable : ∀ t, 0 < t → Measurable (μ t)
  continuous : ∀ᵐ ω ∂P, ContinuousOn (fun t => μ t ω) (Set.Ioi 0)
  fdd : ∀ (k : ℕ) (τ : Fin k → ℝ), (∀ i, 0 < τ i) →
    ∀ Φ : BoundedContinuousFunction (Fin k → FiniteMeasure unitInterval) ℝ,
      Tendsto (fun W : ℕ => ∫ ω, Φ (fun i => transmissionProcess b (e W) κ W (τ i) ω)
          ∂growthPathLaw W b) atTop (𝓝 (∫ ω, Φ (fun i => μ (τ i) ω) ∂P))
  modulus : ∀ ε T : ℝ, 0 < ε → ∀ f : C(unitInterval, ℝ), ∀ η θ : ℝ, 0 < η → 0 < θ →
    ∃ δ : ℝ, 0 < δ ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      growthPathLaw W b {ω | ∃ t ∈ Set.Icc ε T, ∃ t' ∈ Set.Icc ε T, |t - t'| ≤ δ ∧
        η < |∫ x, f x ∂(transmissionProcess b (e W) κ W t ω : Measure unitInterval) -
          ∫ x, f x ∂(transmissionProcess b (e W) κ W t' ω : Measure unitInterval)|} ≤
        ENNReal.ofReal θ

/-!
## 2. The full clock moment bounds and the full tag-clock moment bounds along moving energies
-/

/-- The full clock and tag-clock moments along moving energies.
* `clock`: `‖W⁻¹Tr Y_j^1‖_p ≤ C(j+1)`;
* `clockSquare`: `E Tr(Y_j^1)² ≤ C W (j+1)³`;
* `tag`: `‖W⁻¹Tr Y_{j;k}‖_p ≤ C` for `k < j`.
With `C_e = 0` this is the compact-uniform fixed-energy form; with `E' = E` it implies
`FullSourceMomentsContract`. -/
structure FullSourceMomentsEnergyUniformContract : Prop where
  clock : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI Ce T p : ℝ, 0 < κI → 1 ≤ p →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI, ∀ E' : ℝ,
      IsNearEnergy Ce W E E' → ∀ j : ℕ, (j : ℝ) ≤ T * W →
        eLpNorm (fun ω => (W : ℂ)⁻¹ * ((boundaryToInterior b E' W j ω)ᴴ *
            boundaryToInterior b E' W j ω).trace) (ENNReal.ofReal p) (growthPathLaw W b) ≤
          ENNReal.ofReal (C * ((j : ℝ) + 1))
  clockSquare : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI Ce T : ℝ, 0 < κI →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI, ∀ E' : ℝ,
      IsNearEnergy Ce W E E' → ∀ j : ℕ, (j : ℝ) ≤ T * W →
        ∫⁻ ω, ‖(((boundaryToInterior b E' W j ω)ᴴ * boundaryToInterior b E' W j ω) ^ 2).trace‖ₑ
            ∂growthPathLaw W b ≤ ENNReal.ofReal (C * W * ((j : ℝ) + 1) ^ 3)
  tag : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI Ce T p : ℝ, 0 < κI → 1 ≤ p →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI, ∀ E' : ℝ,
      IsNearEnergy Ce W E E' → ∀ j : ℕ, (j : ℝ) ≤ T * W → ∀ k : ℕ, k < j →
        eLpNorm (fun ω => (W : ℂ)⁻¹ * (tagResponse b E' W j k ω).trace) (ENNReal.ofReal p)
            (growthPathLaw W b) ≤ ENNReal.ofReal C

/-!
## 3. The transmission-law theorem along moving energies
-/

/-- **The transmission law along moving energies** (as used in the pass-derivative lemma:
"uniform for deterministic energies in the bounded unfolded window"). Fixed `b`, base bulk `E`; moving energies `E_W` with
`|E_W - E| ≤ C_e W⁻²` (`IsMovingEnergy`), for every `C_e`.
* `law`: for every admissible profile `κ` there is one critical limit `(P, μ)` such that the
 processes at energies `E_W` converge to it for *every* moving energy (`IsTransmissionLimitAlong`;
 `E_W = E` included, so `(P, μ)` is the fixed-`E` limit), and its determining transforms
 are those of the transmission dual law at the base `E` (`D₀ = D₀(E)`, `h = 4πρ(E)κ`).
* `fractional`, `expDecay` (`κ ≡ 0`): the fixed-energy bounds with one constant `C_p` (`C_q, c_q`)
 chosen before the moving energy, for every moving energy.
* `moments`: `FullSourceMomentsEnergyUniformContract`.
The fixed-energy clauses `determining`, `noMassAtZero` (statements about the limit object,
which is the same), `fractionalHessian` (energy-free), `jetGap` (pointwise in `E`, applies at
each `E_W`) and `entryVariance` (already uniform on `bulkInterval κI`) are not restated.
-/
structure TransmissionLawEnergyUniformContract : Prop where
  law : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ κ : ℝ → ℝ, IsAbsorptionProfile κ →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
        (μ : ℝ → Ω → FiniteMeasure unitInterval),
        (∀ (Ce : ℝ) (e : ℕ → ℝ), IsMovingEnergy E Ce e → IsTransmissionLimitAlong b e κ P μ) ∧
        ∀ t : ℝ, 0 < t → ∀ (p : ℕ) (x y : Fin p → ℝ), IsRatioParameter x y →
          HasDualDeletionProcess (transportD0 b E) x y ∧
          DualLawValue E κ t (transportD0 b E) x y (∫ ω, transmissionRatio x y (μ t ω) ∂P)
  fractional : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ p : ℝ, 0 < p → p < 1 → ∃ C : ℝ, ∀ (Ce : ℝ) (e : ℕ → ℝ), IsMovingEnergy E Ce e →
      ∀ t : ℝ, 0 < t →
        limsup (fun W : ℕ => ∫⁻ ω, ENNReal.ofReal
            (fracTrace p (pathTransmission b (e W) (fun _ => 0) W ⌊(W : ℝ) * t⌋₊ ω))
            ∂growthPathLaw W b) atTop ≤ ENNReal.ofReal (C * (1 + t⁻¹))
  expDecay : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ q : ℝ, 0 < q → q < 1 → ∃ C c : ℝ, 0 < c ∧ ∀ (Ce : ℝ) (e : ℕ → ℝ), IsMovingEnergy E Ce e →
      ∀ t : ℝ, 2 ≤ t →
        limsup (fun W : ℕ => ∫⁻ ω, ENNReal.ofReal
            (fracTrace q (pathTransmission b (e W) (fun _ => 0) W ⌊(W : ℝ) * t⌋₊ ω))
            ∂growthPathLaw W b) atTop ≤ ENNReal.ofReal (C * Real.exp (-(c * t)))
  moments : FullSourceMomentsEnergyUniformContract

/-!
## 4. Conductance and scalar-jet moments uniform in the total length
-/

/-- Conductance and scalar-jet moments uniform in the total length.
* `conductance`: `E g_r^p ≤ C`;
* `jet`: `‖δ_{0,r}‖_p + ‖δ_{1,r}‖_p ≤ C/W` at every stationary jet `s`
  (`δ₁` with the far absorber fixed, as `PathJet.PassiveJetMoments`). -/
structure TransmissionLengthUniformContract : Prop where
  conductance : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI ε p : ℝ, 0 < κI → 0 < ε → 1 ≤ p →
    ∃ C : ℝ, ∀ T : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI, ∀ r : ℕ,
      ε * W ≤ r → (r : ℝ) ≤ T * W →
        ∫⁻ ω, ‖pathConductance b E W r ω‖ₑ ^ p ∂growthPathLaw W b ≤ ENNReal.ofReal C
  jet : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI ε p : ℝ, 0 < κI → 0 < ε → 1 ≤ p →
    ∃ C : ℝ, ∀ T : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI,
      ∀ s : ℂ, IsStationaryJet b E s → ∀ r : ℕ, ε * W ≤ r → (r : ℝ) ≤ T * W →
        eLpNorm (fun ω => jetDistance0 b E (pathX b E W r ω)) (ENNReal.ofReal p)
            (growthPathLaw W b) +
          eLpNorm (fun ω => jetDistance1 b E s (pathX b E W r ω)) (ENNReal.ofReal p)
            (growthPathLaw W b) ≤
          ENNReal.ofReal (C / W)

/-!
## 5. Boundary starts of the dual diffusion
-/

/-- **Boundary starts**: ordered points of the closed chamber with no same-species
coincidence and off the paired corner:
`0 ≤ x₁ < ⋯ < x_p`, `0 ≤ y₁ < ⋯ < y_p ≤ 1` and
`x_i + y_j > 0` for all `i, j` (so `H_p = det[(x_i+y_j)⁻¹] > 0` is finite).
For `p = 1`: every
`z = (x, y) ∈ [0,∞) × [0,1]`, `z ≠ (0,0)`.
Contains the
interior starts `IsRatioParameter`.
The paired corner `(0,0)` (`p = 1`) is excluded: there
`F_{0,0} ≡ 1` and consumers treat it separately (`J(0,0) = 0`).
-/
def IsDualStart {p : ℕ} (x y : Fin p → ℝ) : Prop :=
  StrictMono x ∧ StrictMono y ∧ (∀ i, 0 ≤ x i) ∧ (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧
    ∀ i j, 0 < x i + y j

/-- Pathwise structure of the deletion process from a boundary start: `IsDeletionPath` with the
open-chamber condition required at positive times only (the state may sit on the boundary of
the chamber at `t = 0` and enters the open chamber immediately). Right-continuity of the level
and continuity of the coordinates on `[0, t₂]` at constant level give continuity at `t = 0`. -/
structure IsBoundaryDeletionPath (n : ℝ≥0 → ℕ) (x y : ℝ≥0 → ℕ → ℝ) : Prop where
  antitone : Antitone n
  chamber : ∀ t, 0 < t → dualCoordOf (n t) (x t) (y t) ∈ dualChamber (n t)
  rightCont : ∀ t, ∀ᶠ u in 𝓝[>] t, n u = n t
  cont : ∀ t₁ t₂, t₁ ≤ t₂ → n t₂ = n t₁ → ∀ i, i < n t₁ →
    ContinuousOn (fun u => x u i) (Set.Icc t₁ t₂) ∧ ContinuousOn (fun u => y u i) (Set.Icc t₁ t₂)
  deletion : ∀ τ : ℝ≥0, 0 < τ → ∀ q : ℕ, (∀ᶠ u in 𝓝[<] τ, n u = q + 1) → n τ ≠ q + 1 →
    n τ = q ∧ Tendsto (fun u => x u 0) (𝓝[<] τ) (𝓝 0) ∧
      Tendsto (fun u => y u 0) (𝓝[<] τ) (𝓝 0) ∧
      ∀ i, i < q → Tendsto (fun u => x u (i + 1)) (𝓝[<] τ) (𝓝 (x τ i)) ∧
        Tendsto (fun u => y u (i + 1)) (𝓝[<] τ) (𝓝 (y τ i))

/-- **The conservative deletion law started at a (possibly boundary) point `(x, y)`**:
`IsDualDeletionProcess` with `IsBoundaryDeletionPath` in place of `IsDeletionPath` (same start,
adaptedness and level-`q` martingale problems for `C_c^∞(𝒞_q)` tests; at a boundary start the
top-level entrance value `f(Z₀)` is `0`).
Every `IsDualDeletionProcess` is one; at an interior
start the two classes coincide.
-/
structure IsBoundaryDualProcess {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) (D0 : ℝ) {p : ℕ}
    (x y : Fin p → ℝ) (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ) : Prop where
  prob : IsProbabilityMeasure P
  adapted : ∀ t, Measurable[𝓖 t] (N t) ∧ Measurable[𝓖 t] (X t) ∧ Measurable[𝓖 t] (Y t)
  start : ∀ᵐ ω ∂P, N 0 ω = p ∧ ∀ i : Fin p, X 0 ω i = x i ∧ Y 0 ω i = y i
  paths : ∀ᵐ ω ∂P, IsBoundaryDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω)
  martingale : ∀ q : ℕ, 1 ≤ q → q ≤ p → ∀ f : DualCoord q → ℝ, ContDiff ℝ (⊤ : ℕ∞) f →
    HasCompactSupport f → tsupport f ⊆ dualChamber q →
    Martingale (dualMartingale D0 q f N X Y) 𝓖 P

/-- The boundary-start deletion law exists (on some filtered probability space). -/
def HasBoundaryDualProcess (D0 : ℝ) {p : ℕ} (x y : Fin p → ℝ) : Prop :=
  ∃ (Ω : Type) (m : MeasurableSpace Ω) (𝓖 : Filtration ℝ≥0 m) (P : Measure Ω)
    (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ), IsBoundaryDualProcess P 𝓖 D0 x y N X Y

/-- Every boundary-start realization gives the value `v` to
`E_{x,y}[exp(-∫_0^t h(t-s)R_s ds) 1{ζ ≤ t}]` (the `dualTransform`).
-/
def BoundaryDualLawValue (E : ℝ) (κ : ℝ → ℝ) (t D0 : ℝ) {p : ℕ} (x y : Fin p → ℝ) (v : ℝ) :
    Prop :=
  ∀ (Ω : Type) (m : MeasurableSpace Ω) (𝓖 : Filtration ℝ≥0 m) (P : Measure Ω)
    (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ), IsBoundaryDualProcess P 𝓖 D0 x y N X Y →
      dualTransform E κ t P N X Y = v

/-- Truncation of a coordinate sequence at level `n` (entries of index `≥ n` set to `0`). -/
def truncDualCoord (n : ℕ) (x : ℕ → ℝ) : ℕ → ℝ := fun i => if i < n then x i else 0

/-- The truncated state path `t ↦ (N_t, X_t|_{<N_t}, Y_t|_{<N_t})` (the object whose law is
determined; definitionally `Transmission.Dual.dualState`). -/
def truncDualState {Ω : Type*} (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ) (ω : Ω) :
    ℝ≥0 → ℕ × (ℕ → ℝ) × (ℕ → ℝ) :=
  fun t => (N t ω, truncDualCoord (N t ω) (X t ω), truncDualCoord (N t ω) (Y t ω))

/-- The deletion law of the dual diffusion from a boundary start.
* `exists_`: the boundary-start deletion law exists (`HasBoundaryDualProcess`).
* `unique`: any two realizations have the same law of the truncated state path.
* `firstMoment`: `E∫_0^t R_s ds ≤ t(x + y)` for every realization (integrability of the signed
  response; the paper's equality `E R_s = R_0` is stronger and is not needed). -/
structure DualBoundaryStartContract : Prop where
  exists_ : ∀ D0 : ℝ, 0 < D0 → ∀ x y : ℝ, IsDualStart ![x] ![y] →
    HasBoundaryDualProcess D0 ![x] ![y]
  unique : ∀ D0 : ℝ, 0 < D0 → ∀ x y : ℝ, IsDualStart ![x] ![y] →
    ∀ (Ω₁ : Type) (m₁ : MeasurableSpace Ω₁) (𝓖₁ : Filtration ℝ≥0 m₁) (P₁ : Measure Ω₁)
      (N₁ : ℝ≥0 → Ω₁ → ℕ) (X₁ Y₁ : ℝ≥0 → Ω₁ → ℕ → ℝ)
      (Ω₂ : Type) (m₂ : MeasurableSpace Ω₂) (𝓖₂ : Filtration ℝ≥0 m₂) (P₂ : Measure Ω₂)
      (N₂ : ℝ≥0 → Ω₂ → ℕ) (X₂ Y₂ : ℝ≥0 → Ω₂ → ℕ → ℝ),
      IsBoundaryDualProcess P₁ 𝓖₁ D0 ![x] ![y] N₁ X₁ Y₁ →
      IsBoundaryDualProcess P₂ 𝓖₂ D0 ![x] ![y] N₂ X₂ Y₂ →
      P₁.map (truncDualState N₁ X₁ Y₁) = P₂.map (truncDualState N₂ X₂ Y₂)
  firstMoment : ∀ D0 : ℝ, 0 < D0 → ∀ x y : ℝ, IsDualStart ![x] ![y] →
    ∀ (Ω : Type) (m : MeasurableSpace Ω) (𝓖 : Filtration ℝ≥0 m) (P : Measure Ω)
      (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ), IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y →
      ∀ t : ℝ, 0 ≤ t →
        ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) t,
            ENNReal.ofReal (dualTotal (N s.toNNReal ω) (X s.toNNReal ω) (Y s.toNNReal ω))) ∂P ≤
          ENNReal.ofReal (t * (x + y))
  law : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ κ : ℝ → ℝ, IsAbsorptionProfile κ →
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (μ : ℝ → Ω → FiniteMeasure unitInterval), IsTransmissionLimit b E κ P μ →
    ∀ t : ℝ, 0 < t → ∀ x y : ℝ, IsDualStart ![x] ![y] → y < 1 →
      HasBoundaryDualProcess (transportD0 b E) ![x] ![y] ∧
      BoundaryDualLawValue E κ t (transportD0 b E) ![x] ![y]
        (∫ ω, transmissionRatio ![x] ![y] (μ t ω) ∂P)

end BlockBand.Internal.Contracts.TransmissionUniform
