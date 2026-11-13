module

public import BlockBand.Internal.Contracts.Layers
public import BlockBand.Transmission.PositiveResolvent
public import Mathlib.Probability.ProductMeasure
public import Mathlib.MeasureTheory.Measure.FiniteMeasure
public import Mathlib.Topology.UnitInterval
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# The near-end-grown physical path, its transmission and the dual

Vocabulary for the transmission statements.

## Contents

* §0 scalars: `η = Im z`, `D₀ = 2/(b(4-E²))`, `d_* = 1/(1-b)`, `k = c+b²`,
  `k₋ = c+b²a²`, `σ₊ = k/b`, `σ₋ = k₋/(1+k₋s_*)`, the stationary jet
  the stationary jet equation, `h(s) = 4πρ(E)κ(s)`.
* §1 the near-end-grown two-port Gaussian path on **one** probability space (with the passive update): an i.i.d. sequence of
  GUE blocks and Ginibre bonds; the path of length `r` is a function of the first `r` blocks
  and the first `r+1` bonds (`pathAt`), so `r ↦ T_r` is a process adapted to
  `growthSigma`. Physical absorption `κ(r/W)/W²` on the block added at step `r`.
* §2 passive coordinates `X, Y, K, R, Q, T, g`.
* §3 the transmission trace measure `μ_W(t) = Σ t_i δ_{t_i}` and the ratios `F_{x,y}`; fractional traces `Tr T^p`.
* §4 the dual generator `𝒟_p`, the ordered chamber,
  and the conservative deletion process of the dual boundary lemma, its total
  coordinate `R_s` and extinction time `ζ`.
* §5 the fresh one-port layer, `U = LL*` and the scalar jets `δ₀, δ₁`.
* §6 the two-input path: the full inverse `G` with two matched leads, `ℝ`, `𝕊`,
  `𝒰_n`, tags `Y_{n;k}`, `P`, `P' = 𝕊*P𝕊`, `J = P'-P`, interval sources `Q(q)`, the bounded Gaussian source transforms, and the complex source
  data `𝒦, V_pr, M_pr`.

## Conventions

* Port `0` is the **near** port (the growing end, where `R`, `T` and `P = diag(I_W, 0)` live);
  port `1` is the far port. Layers' `PathSample` puts port `0` at path position `0`; we place
  the newest block at position `0`, so the block of birth index `k` (the `(k+1)`-st block
  added; layer `r = k+1` of the paper) sits at position `r-1-k` in the path of length `r`.
* Bond orientation is chosen so that the coupling between birth blocks `k-1` and `k` at every
  length `≥ k+1` is exactly the coupling between block `k-1` and the near port at length `k`
  (`(older, newer)` entry `= B_k`); hence `X_{r+1} = B_{r+1}*(A_r - E - X_r)⁻¹ B_{r+1}`
  holds exactly along one sample (this identity is not stated here).
* Lean's `⁻¹` is the totalized inverse; every inverse below is almost surely of an invertible
  matrix (the ports carry `Im z > 0`; absorption is `≥ 0`).
* Spectra are read through `charpoly.roots` (as in `Inputs.spectralSum`); for the Hermitian
  `0 ⪯ T ⪯ I` the roots are the real eigenvalues in `[0,1]`, and `toUnit` (clamping to
  `[0,1]`) does not change them.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Internal.Contracts.TransmissionPath

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal ComplexConjugate Matrix

/-!
## 0. Scalars
-/

/-- `η = Im z_∂`. -/
def etaZ (b E : ℝ) : ℝ := (boundaryZ b E).im

/-- `D₀ = 2/(b(4-E²))`. -/
def transportD0 (b E : ℝ) : ℝ := 2 / (b * (4 - E ^ 2))

/-- `d_* = 1/(1-b)`. -/
def dStar (b : ℝ) : ℝ := 1 / (1 - b)

/-- `k = c + b²`, `c = 1-2b`. -/
def kPlus (b : ℝ) : ℝ := (1 - 2 * b) + b ^ 2

/-- `k₋ = c + b²a²`. -/
def kMinus (b E : ℝ) : ℂ := ((1 - 2 * b : ℝ) : ℂ) + (b : ℂ) ^ 2 * matchedA E ^ 2

/-- `σ₊ = k/b`. -/
def sigmaPlus (b : ℝ) : ℝ := kPlus b / b

/-- `s` is the stationary first jet of the stationary jet equation:
`k₋s² + (1+ca²)s + a² = 0` and `|s| ≤ d_*` (the paper states that this `s_*` is unique). -/
def IsStationaryJet (b E : ℝ) (s : ℂ) : Prop :=
  kMinus b E * s ^ 2 + (1 + ((1 - 2 * b : ℝ) : ℂ) * matchedA E ^ 2) * s + matchedA E ^ 2 = 0 ∧
    ‖s‖ ≤ dStar b

/-- `σ₋ = k₋/(1+k₋s)` evaluated at a stationary jet `s = s_*`. -/
def sigmaMinus (b E : ℝ) (s : ℂ) : ℂ := kMinus b E / (1 + kMinus b E * s)

/-- The limiting killing rate `h(s) = 4πρ(E)κ(s)` of the transmission-law theorem,
`ρ = semicircleDensity`. -/
def absorptionRate (E : ℝ) (κ : ℝ → ℝ) (s : ℝ) : ℝ :=
  4 * Real.pi * Parameters.semicircleDensity E * κ s

/-- A deterministic absorption profile: the block added at step `r` carries absorption
`κ(r/W)/W²`. Reading of the paper: `κ` nonnegative, bounded and
continuous; `κ ≡ 0` is the homogeneous case ("`h = 0` otherwise"). -/
def IsAbsorptionProfile (κ : ℝ → ℝ) : Prop :=
  Continuous κ ∧ (∀ s, 0 ≤ κ s) ∧ ∃ K : ℝ, ∀ s, κ s ≤ K

/-!
## 1. The near-end-grown coupled two-port Gaussian path
-/

/-- Gaussian coordinates of the whole near-end-grown path: GUE blocks `A_k` (`k = 0,1,…` in birth
order) and Ginibre bonds `B_k`. `B_0` couples block `0` to the far port; for `k ≥ 1`, `B_k`
couples block `k-1` to the near port at length `k`, and to block `k` at every length `≥ k+1`. -/
abbrev GrowthPath (W : ℕ) :=
  (ℕ → Matrix (Fin W) (Fin W) ℂ) × (ℕ → Matrix (Fin W) (Fin W) ℂ)

/-- Law of the near-end-grown path: all blocks `A_k ~ GUE_W(c/W)` (`c = 1-2b`) and all bonds
`B_k ~ Gin(b/W)` independent (countable product, `Measure.infinitePi`). Same Gaussian laws as
`Layers.pathLaw`; the `r`-marginal relation `(growthPathLaw W b).map (pathAt W r) = pathLaw W r b`
is not stated here. -/
def growthPathLaw (W : ℕ) (b : ℝ) : Measure (GrowthPath W) :=
  (Measure.infinitePi fun _ : ℕ => gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W))).prod
    (Measure.infinitePi fun _ : ℕ => ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W)))

/-- The growth σ-algebra at length `r`: generated by `A_0,…,A_{r-1}` and `B_0,…,B_r`
(the near-end filtration `r = 1, 2, …`). -/
abbrev growthSigma (W r : ℕ) : MeasurableSpace (GrowthPath W) :=
  MeasurableSpace.comap
    (fun ω : GrowthPath W => ((fun k : Fin r => ω.1 k), (fun k : Fin (r + 1) => ω.2 k)))
    inferInstance

/-- The path of length `r` read from the grown sample, as a Layers `PathSample`: position `i`
carries block `A_{r-1-i}`; internal bond `i` (positions `i, i+1`) is `B_{r-1-i}ᴴ`, so that the
`(older, newer)` coupling is `B_{r-1-i}`; port `0` (near, at position `0`) has bond `B_r` and
port `1` (far, at position `r-1`) has bond `B_0`. -/
def pathAt (W r : ℕ) (ω : GrowthPath W) : PathSample W r :=
  (fun i => ω.1 (r - 1 - i.val), fun i => (ω.2 (r - 1 - i.val))ᴴ, ![ω.2 r, ω.2 0])

/-- Absorption `ε` on the path positions: `i ↦ κ((r-i)/W)/W²`; position `i` holds the block
added at step `r-i` (in the paper: `A-E ↦ A-E+iε`, `ε = κ(r/W)/W²`). -/
def layerAbsorption (W : ℕ) (κ : ℝ → ℝ) (r : ℕ) : Fin r → ℝ :=
  fun i => κ (((r - i.val : ℕ) : ℝ) / W) / (W : ℝ) ^ 2

/-- Diagonal absorption `i diag(ε)` on the path sites. -/
def absorptionDiag {r : ℕ} (W : ℕ) (ε : Fin r → ℝ) :
    Matrix (Fin r × Fin W) (Fin r × Fin W) ℂ :=
  Matrix.diagonal fun x => ((ε x.1 : ℝ) : ℂ) * Complex.I

/-- The (absorbed) two-port Schur matrix `𝕏 = C*(H_path - E + i diag ε)⁻¹ C`; with `ε = 0` this
is `Layers.pathSchur`. -/
def absorbedPathSchur {W r : ℕ} (E : ℝ) (ε : Fin r → ℝ) (ω : PathSample W r) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (pathPortCoupling ω)ᴴ * (pathMatrix ω - (E : ℂ) • 1 + absorptionDiag W ε)⁻¹ *
    pathPortCoupling ω

/-!
## 2. Passive coordinates
-/

/-- The `(i,j)` port block of a two-port matrix. -/
def portBlock {W : ℕ} (M : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (i j : Fin 2) :
    Matrix (Fin W) (Fin W) ℂ :=
  Matrix.of fun x y => M (i, x) (j, y)

/-- Far port eliminated: `X = X₁₁ + X₁₂(z - X₂₂)⁻¹X₂₁` with the paper's index `1` = near = Lean port `0`. -/
def nearSchur {W : ℕ} (z : ℂ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Matrix (Fin W) (Fin W) ℂ :=
  portBlock XX 0 0 + portBlock XX 0 1 * (z • 1 - portBlock XX 1 1)⁻¹ * portBlock XX 1 0

/-- `R = K⁻¹ = (z - X)⁻¹`. -/
def passiveResolvent {W : ℕ} (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    Matrix (Fin W) (Fin W) ℂ :=
  (boundaryZ b E • 1 - X)⁻¹

/-- `Y = -Im X`, `Im M = (M - M*)/(2i)` (`BlockBand.Transmission.matrixImaginaryPart`). -/
def passiveY {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  -BlockBand.Transmission.matrixImaginaryPart X

/-- `Q = R*YR`. -/
def passiveQ {W : ℕ} (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  (passiveResolvent b E X)ᴴ * passiveY X * passiveResolvent b E X

/-- The transmission matrix `T = 4ηQ` (`= I - S*S`, `S = I - 2iηR`). -/
def passiveTransmission {W : ℕ} (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    Matrix (Fin W) (Fin W) ℂ :=
  ((4 * etaZ b E : ℝ) : ℂ) • passiveQ b E X

/-- `g = Tr T` (real part; `T` is Hermitian). -/
def conductanceOf {W : ℕ} (T : Matrix (Fin W) (Fin W) ℂ) : ℝ := T.trace.re

/-- `X_r` of the near-end-grown path at length `r`, absorption profile `κ`. -/
def pathNearSchur (b E : ℝ) (κ : ℝ → ℝ) (W r : ℕ) (ω : GrowthPath W) :
    Matrix (Fin W) (Fin W) ℂ :=
  nearSchur (boundaryZ b E) (absorbedPathSchur E (layerAbsorption W κ r) (pathAt W r ω))

/-- `T_r` of the path at length `r` (absorption profile `κ`; `κ = 0`: homogeneous). -/
def pathTransmission (b E : ℝ) (κ : ℝ → ℝ) (W r : ℕ) (ω : GrowthPath W) :
    Matrix (Fin W) (Fin W) ℂ :=
  passiveTransmission b E (pathNearSchur b E κ W r ω)

/-!
## 3. The transmission trace measure and the ratios `F_{x,y}`
-/

/-- Clamp a real number to `[0,1]`. -/
def toUnit (x : ℝ) : unitInterval := Set.projIcc 0 1 zero_le_one x

/-- Dirac mass on `[0,1]` as a finite measure. -/
def unitDirac (x : unitInterval) : FiniteMeasure unitInterval := ⟨Measure.dirac x, inferInstance⟩

/-- The trace measure `Σ_i t_i δ_{t_i}` of a matrix with eigenvalues `t_i ∈ [0,1]`. -/
def traceMeasure {n : Type*} [Fintype n] [DecidableEq n] (T : Matrix n n ℂ) :
    FiniteMeasure unitInterval :=
  (T.charpoly.roots.map fun z => Real.toNNReal z.re • unitDirac (toUnit z.re)).sum

/-- `Tr T^p = Σ_i t_i^p` for real `p > 0` (eigenvalues through `charpoly.roots`). -/
def fracTrace {n : Type*} [Fintype n] [DecidableEq n] (p : ℝ) (T : Matrix n n ℂ) : ℝ :=
  (T.charpoly.roots.map fun z => (max z.re 0) ^ p).sum

/-- The transmission trace-measure process `μ_W(t) = Σ_i t_i(t) δ_{t_i(t)}` of
`T_{⌊Wt⌋}` (critical time `t = r/W`). -/
def transmissionProcess (b E : ℝ) (κ : ℝ → ℝ) (W : ℕ) (t : ℝ) (ω : GrowthPath W) :
    FiniteMeasure unitInterval :=
  traceMeasure (pathTransmission b E κ W ⌊(W : ℝ) * t⌋₊ ω)

/-- Ordered ratio parameters `0 < x₁ < ⋯ < x_p`, `0 < y₁ < ⋯ < y_p < 1`. -/
def IsRatioParameter {p : ℕ} (x y : Fin p → ℝ) : Prop :=
  StrictMono x ∧ StrictMono y ∧ (∀ i, 0 < x i) ∧ ∀ i, 0 < y i ∧ y i < 1

/-- The integrand of the transmission ratios, with value `-Σ(x_i + y_i)` at `t = 0`. -/
def ratioIntegrand {p : ℕ} (x y : Fin p → ℝ) (t : ℝ) : ℝ :=
  if t = 0 then -∑ i, (x i + y i)
  else (∑ i, (Real.log (1 - y i * t) - Real.log (1 + x i * t))) / t

/-- `F_{x,y}(μ) = exp ∫_{[0,1]} Σ_i [log(1-y_i t) - log(1+x_i t)]/t dμ(t)`; for a finite matrix it is
`Π_i det(I - y_iT)/det(I + x_iT) ∈ [0,1]`. -/
def transmissionRatio {p : ℕ} (x y : Fin p → ℝ) (μ : FiniteMeasure unitInterval) : ℝ :=
  Real.exp (∫ t, ratioIntegrand x y (t : ℝ) ∂(μ : Measure unitInterval))

/-!
## 4. The dual diffusion and its conservative deletion law
-/

/-- Dual coordinates `(x, y)` with `q` pairs. -/
abbrev DualCoord (q : ℕ) := (Fin q → ℝ) × (Fin q → ℝ)

/-- The ordered interior chamber `𝒞_q`: `0 < x₁ < ⋯ < x_q`, `0 < y₁ < ⋯ < y_q < 1`. -/
def dualChamber (q : ℕ) : Set (DualCoord q) :=
  {z | IsRatioParameter z.1 z.2}

/-- Unit direction `∂_{x_i}`. -/
def dirX {q : ℕ} (i : Fin q) : DualCoord q := (Pi.single i 1, 0)

/-- Unit direction `∂_{y_j}`. -/
def dirY {q : ℕ} (j : Fin q) : DualCoord q := (0, Pi.single j 1)

/-- `β_i^x = 1 + 2x_i + 2x_i(1+x_i)[Σ_{k≠i} (x_i-x_k)⁻¹ - Σ_j (x_i+y_j)⁻¹]`. -/
def dualDriftX {q : ℕ} (z : DualCoord q) (i : Fin q) : ℝ :=
  1 + 2 * z.1 i + 2 * z.1 i * (1 + z.1 i) *
    ((∑ k ∈ Finset.univ.erase i, 1 / (z.1 i - z.1 k)) - ∑ j, 1 / (z.1 i + z.2 j))

/-- `β_j^y = 1 - 2y_j + 2y_j(1-y_j)[Σ_{ℓ≠j} (y_j-y_ℓ)⁻¹ - Σ_i (x_i+y_j)⁻¹]`. -/
def dualDriftY {q : ℕ} (z : DualCoord q) (j : Fin q) : ℝ :=
  1 - 2 * z.2 j + 2 * z.2 j * (1 - z.2 j) *
    ((∑ l ∈ Finset.univ.erase j, 1 / (z.2 j - z.2 l)) - ∑ i, 1 / (z.1 i + z.2 j))

/-- The dual generator `𝒟_q f = (D₀/2)[Σ_i (x_i(1+x_i)∂²_{x_i} + β_i^x ∂_{x_i})f
+ Σ_j (y_j(1-y_j)∂²_{y_j} + β_j^y ∂_{y_j})f]`. -/
def dualGenerator (D0 : ℝ) {q : ℕ} (f : DualCoord q → ℝ) (z : DualCoord q) : ℝ :=
  D0 / 2 *
    ((∑ i, (z.1 i * (1 + z.1 i) * fderiv ℝ (fun w => fderiv ℝ f w (dirX i)) z (dirX i) +
        dualDriftX z i * fderiv ℝ f z (dirX i))) +
      ∑ j, (z.2 j * (1 - z.2 j) * fderiv ℝ (fun w => fderiv ℝ f w (dirY j)) z (dirY j) +
        dualDriftY z j * fderiv ℝ f z (dirY j)))

/-- The first `q` coordinates of sequences `x, y : ℕ → ℝ` (a dual state with `q` pairs is a
level `q` and two sequences whose first `q` entries are the particle positions). -/
def dualCoordOf (q : ℕ) (x y : ℕ → ℝ) : DualCoord q := (fun i => x i, fun i => y i)

/-- A level-`q` test function lifted to the whole state space (zero on other levels). -/
def dualLift {q : ℕ} (f : DualCoord q → ℝ) (n : ℕ) (x y : ℕ → ℝ) : ℝ :=
  if n = q then f (dualCoordOf q x y) else 0

/-- The total coordinate `R = Σ_{i < n} (x_i + y_i)`. -/
def dualTotal (n : ℕ) (x y : ℕ → ℝ) : ℝ := ∑ i ∈ Finset.range n, (x i + y i)

/-- The extinction time `ζ = inf {t : N_t = 0}` (empty state; `⊤` if never). -/
def dualExtinction {Ω : Type*} (N : ℝ≥0 → Ω → ℕ) (ω : Ω) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : N t ω = 0), (t : ℝ≥0∞)

/-- Entrance time into the levels `≤ q`. -/
def dualEntrance {Ω : Type*} (N : ℝ≥0 → Ω → ℕ) (q : ℕ) (ω : Ω) : ℝ≥0 :=
  sInf {t | N t ω ≤ q}

open scoped Classical in
/-- The value of a level-`q` test at the entrance into level `q`, once entered by time `t`
(the restart value after a deletion; `f(Z₀)` when `q = p`). -/
def dualEntranceValue {Ω : Type*} {q : ℕ} (f : DualCoord q → ℝ) (N : ℝ≥0 → Ω → ℕ)
    (X Y : ℝ≥0 → Ω → ℕ → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if ∃ u ≤ t, N u ω ≤ q then
    dualLift f (N (dualEntrance N q ω) ω) (X (dualEntrance N q ω) ω) (Y (dualEntrance N q ω) ω)
  else 0

/-- `f(Z_t) - f(Z_{σ_q}) 1{σ_q ≤ t} - ∫_0^t 𝒟_q f(Z_u) du` for a level-`q` test `f`
(the level-`q` martingale problem started at the entrance time `σ_q`). -/
def dualMartingale {Ω : Type*} (D0 : ℝ) (q : ℕ) (f : DualCoord q → ℝ) (N : ℝ≥0 → Ω → ℕ)
    (X Y : ℝ≥0 → Ω → ℕ → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  dualLift f (N t ω) (X t ω) (Y t ω) - dualEntranceValue f N X Y t ω -
    ∫ u in Set.Ioc (0 : ℝ) t,
      dualLift (dualGenerator D0 f) (N u.toNNReal ω) (X u.toNNReal ω) (Y u.toNNReal ω)

/-- Pathwise structure of the deletion process: the level
`n` is nonincreasing and right-continuous; the state is always in the open ordered chamber of
its level (no same-species collision, no other boundary loss, no explosion); coordinates are
continuous on every closed interval of constant level; at every jump the level drops by
exactly one (no simultaneous multiple deletion), the left limit is the paired corner
`(0, x̃; 0, ỹ)` and the process restarts at the survivors `(x̃, ỹ)`. -/
structure IsDeletionPath (n : ℝ≥0 → ℕ) (x y : ℝ≥0 → ℕ → ℝ) : Prop where
  antitone : Antitone n
  chamber : ∀ t, dualCoordOf (n t) (x t) (y t) ∈ dualChamber (n t)
  rightCont : ∀ t, ∀ᶠ u in 𝓝[>] t, n u = n t
  cont : ∀ t₁ t₂, t₁ ≤ t₂ → n t₂ = n t₁ → ∀ i, i < n t₁ →
    ContinuousOn (fun u => x u i) (Set.Icc t₁ t₂) ∧ ContinuousOn (fun u => y u i) (Set.Icc t₁ t₂)
  deletion : ∀ τ : ℝ≥0, 0 < τ → ∀ q : ℕ, (∀ᶠ u in 𝓝[<] τ, n u = q + 1) → n τ ≠ q + 1 →
    n τ = q ∧ Tendsto (fun u => x u 0) (𝓝[<] τ) (𝓝 0) ∧
      Tendsto (fun u => y u 0) (𝓝[<] τ) (𝓝 0) ∧
      ∀ i, i < q → Tendsto (fun u => x u (i + 1)) (𝓝[<] τ) (𝓝 (x τ i)) ∧
        Tendsto (fun u => y u (i + 1)) (𝓝[<] τ) (𝓝 (y τ i))

/-- **The conservative deletion law of the dual boundary lemma**, started at the
interior ordered point `(x, y)` with `p` pairs, as a process `(N, X, Y)` adapted to a filtration
`𝓖`: it starts at `(p; x, y)`, has the pathwise structure `IsDeletionPath`, and for every level
`1 ≤ q ≤ p` and every smooth test `f` compactly supported in the open chamber `𝒞_q` the process
`dualMartingale D₀ q f` is a `𝓖`-martingale (generator `𝒟_q` in each interior chamber; strong
Markov restart at the survivors). The empty state is absorbing (`n` nonincreasing). By local
uniqueness of the martingale problem for the smooth nondegenerate `𝒟_q` on the open chamber and
induction over deletions this characterizes the law uniquely; its existence
and uniqueness is the content of the dual boundary lemma. -/
structure IsDualDeletionProcess {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) (D0 : ℝ) {p : ℕ}
    (x y : Fin p → ℝ) (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ) : Prop where
  prob : IsProbabilityMeasure P
  adapted : ∀ t, Measurable[𝓖 t] (N t) ∧ Measurable[𝓖 t] (X t) ∧ Measurable[𝓖 t] (Y t)
  start : ∀ᵐ ω ∂P, N 0 ω = p ∧ ∀ i : Fin p, X 0 ω i = x i ∧ Y 0 ω i = y i
  paths : ∀ᵐ ω ∂P, IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω)
  martingale : ∀ q : ℕ, 1 ≤ q → q ≤ p → ∀ f : DualCoord q → ℝ, ContDiff ℝ (⊤ : ℕ∞) f →
    HasCompactSupport f → tsupport f ⊆ dualChamber q →
    Martingale (dualMartingale D0 q f N X Y) 𝓖 P

/-- The right side of the dual transmission law:
`E_{x,y}[exp(-∫_0^t h(t-s) R_s ds) 1{ζ ≤ t}]`. -/
def dualTransform {Ω : Type*} [MeasurableSpace Ω] (E : ℝ) (κ : ℝ → ℝ) (t : ℝ) (P : Measure Ω)
    (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ) : ℝ :=
  ∫ ω, (if dualExtinction N ω ≤ ENNReal.ofReal t then
      Real.exp (-∫ s in (0 : ℝ)..t,
        absorptionRate E κ (t - s) * dualTotal (N s.toNNReal ω) (X s.toNNReal ω) (Y s.toNNReal ω))
    else 0) ∂P

/-!
## 5. The fresh one-port layer and the scalar jets
-/

/-- The fresh layer `𝒢 = [[A - E - X, B],[B*, zI]]⁻¹` (one block, one port; `A ~ GUE_W(c/W)`,
`B ~ Gin(b/W)`, `Layers.layerLaw W b .oneBlockOnePort`), for an old passive self-energy `X`. -/
def freshLayer {W : ℕ} (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ :=
  layerResolvent .oneBlockOnePort E (boundaryZ b E)
    (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) ω

/-- `L = K𝒢₁₂`, `K = z - X`. -/
def freshL {W : ℕ} (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) : Matrix (Fin W) (Fin W) ℂ :=
  (boundaryZ b E • 1 - X) *
    Matrix.of fun x y => freshLayer b E X ω (Sum.inl ((0 : Fin 1), x)) (Sum.inr ((0 : Fin 1), y))

/-- `U = LL*`. -/
def freshU {W : ℕ} (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) : Matrix (Fin W) (Fin W) ℂ :=
  freshL b E X ω * (freshL b E X ω)ᴴ

/-- `δ₀ = |W⁻¹ Tr R - a|`. -/
def jetDistance0 {W : ℕ} (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  ‖(W : ℂ)⁻¹ * (passiveResolvent b E X).trace - matchedA E‖

/-- `δ₁ = |∂_z(W⁻¹ Tr R) - s_*|`, derivative in the boundary parameter with `X` (hence the far
absorber) held fixed. -/
def jetDistance1 {W : ℕ} (b E : ℝ) (s : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  ‖deriv (fun w : ℂ => (W : ℂ)⁻¹ * ((w • (1 : Matrix (Fin W) (Fin W) ℂ) - X)⁻¹).trace)
      (boundaryZ b E) - s‖

/-- `u` is an orthonormal eigenbasis of `T` with eigenvalues `t`. -/
def IsOrthonormalEigenbasis {W : ℕ} (T : Matrix (Fin W) (Fin W) ℂ) (u : Fin W → Fin W → ℂ)
    (t : Fin W → ℝ) : Prop :=
  (∀ i j, star (u i) ⬝ᵥ u j = if i = j then 1 else 0) ∧ ∀ i, T *ᵥ u i = (t i : ℂ) • u i

/-!
## 6. The two-input path and its sources
-/

/-- Sites of the full path of length `n` with its two ports. -/
abbrev FullSite (W n : ℕ) := (Fin n × Fin W) ⊕ (Fin 2 × Fin W)

/-- `𝓜 = [[H_path - E, C],[C*, zI]]`: the unabsorbed path of length `n` with its two matched
leads (Schur complement on the ports `z - 𝕏`, so the port block of `𝓜⁻¹` is `ℝ = (z - 𝕏)⁻¹`). -/
def fullPathMatrix (b E : ℝ) (W n : ℕ) (ω : GrowthPath W) :
    Matrix (FullSite W n) (FullSite W n) ℂ :=
  Matrix.fromBlocks (pathMatrix (pathAt W n ω) - (E : ℂ) • 1) (pathPortCoupling (pathAt W n ω))
    (pathPortCoupling (pathAt W n ω))ᴴ (boundaryZ b E • 1)

/-- `G`, the inverse of the full path with its two matched leads. -/
def fullInverse (b E : ℝ) (W n : ℕ) (ω : GrowthPath W) : Matrix (FullSite W n) (FullSite W n) ℂ :=
  (fullPathMatrix b E W n ω)⁻¹

/-- `ℝ = (z - 𝕏)⁻¹`, the port block of `G`. -/
def boundaryResolvent (b E : ℝ) (W n : ℕ) (ω : GrowthPath W) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (fullInverse b E W n ω).toBlocks₂₂

/-- `𝒰_n = G_{int,ports}`: maps an incoming boundary vector `v ∈ ℂ^{2W}` to the interior part of
the solution of `𝓜ψ = (0, v)`, whose boundary part is `ℝv`. -/
def boundaryToInterior (b E : ℝ) (W n : ℕ) (ω : GrowthPath W) :
    Matrix (Fin n × Fin W) (Fin 2 × Fin W) ℂ :=
  (fullInverse b E W n ω).toBlocks₁₂

/-- `P = diag(I_W, 0)`: the near-port projection. -/
def nearProjection (W : ℕ) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  Matrix.diagonal fun x => if x.1 = 0 then 1 else 0

/-- `𝕊 = I - 2iηℝ` (unitary at real energy). -/
def scatteringMatrix (b E : ℝ) (W n : ℕ) (ω : GrowthPath W) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  1 - ((2 * etaZ b E : ℝ) * Complex.I) • boundaryResolvent b E W n ω

/-- The current `J = P' - P`, `P' = 𝕊*P𝕊`. -/
def pathCurrent (b E : ℝ) (W n : ℕ) (ω : GrowthPath W) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (scatteringMatrix b E W n ω)ᴴ * nearProjection W * scatteringMatrix b E W n ω - nearProjection W

/-- `P_k` on the path of length `n`: the block of birth index `k` (position `n-1-k`). -/
def tagProjection (W n k : ℕ) : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ :=
  Matrix.diagonal fun x => if k < n ∧ x.1.val = n - 1 - k then 1 else 0

/-- `Y_{n;k} = 𝒰_n* P_k 𝒰_n`. -/
def tagResponse (b E : ℝ) (W n k : ℕ) (ω : GrowthPath W) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (boundaryToInterior b E W n ω)ᴴ * tagProjection W n k * boundaryToInterior b E W n ω

/-- The interval source `Q(q) = Σ_j (q_j/W) Q_j`, `Q_j = Y_{n;j}/W`, `q_j = q(j/W)` for the
`j`-th block (Lean birth index `k = j - 1`). -/
def intervalSource (b E : ℝ) (W n : ℕ) (q : ℝ → ℝ) (ω : GrowthPath W) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  ∑ k ∈ Finset.range n, ((q (((k + 1 : ℕ) : ℝ) / W) / (W : ℝ) ^ 2 : ℝ) : ℂ) • tagResponse b E W n k ω

/-- A positive source test supported in `[s,T]`: `q ≥ 0`, `q = 0` off `[s,T]`, continuous on
`[s,T]` (truncations `q·1_{[s,T]}` of continuous tests are tests). -/
def IsSourceTest (s T : ℝ) (q : ℝ → ℝ) : Prop :=
  (∀ x, 0 ≤ q x) ∧ (∀ x, x ∉ Set.Icc s T → q x = 0) ∧ ContinuousOn q (Set.Icc s T)

/-- **Bounded Gaussian source transform** of the two-input path at width `W`:
`E Π_j det(I + Σ_a a_{j,a} Q_a)⁻¹` for the interval sources `Q_a = Q(q_a)` of the path of length
`⌊WT⌋` (final time `T`), coefficients `a_{j,a} ≥ 0`. Each factor equals `E_{h_j} exp(-h_j*(Σ_a
a_{j,a}Q_a)h_j)` for an independent final Gaussian probe `h_j ~ CN(0, I_{2W})`; the product
over `j` is the joint expectation with independent probes for distinct factors. -/
def sourceTransform (b E T : ℝ) {p J : ℕ} (q : Fin p → ℝ → ℝ) (a : Fin J → Fin p → ℝ)
    (W : ℕ) : ℝ :=
  ∫ ω, ∏ j, (((1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) +
      ∑ i, (a j i : ℂ) • intervalSource b E W ⌊(W : ℝ) * T⌋₊ (q i) ω).det⁻¹).re
    ∂growthPathLaw W b

/-- The probe frame `𝒥`: columns `ξ_j = √(m_j/W) ι_{k_j} g_j` on the block of birth index
`k_j = ⌊Wτ_j⌋` (birth time `τ_j`), `g_j ∈ ℂ^W`. -/
def probeColumns {np : ℕ} (W n : ℕ) (τ m : Fin np → ℝ) (g : Fin np → Fin W → ℂ) :
    Matrix (Fin n × Fin W) (Fin np) ℂ :=
  fun x j => if ⌊(W : ℝ) * τ j⌋₊ < n ∧ x.1.val = n - 1 - ⌊(W : ℝ) * τ j⌋₊ then
    ((Real.sqrt (m j / W) : ℝ) : ℂ) * g j x.2 else 0

/-- Joint sample of the path and the independent probe Gaussians. -/
abbrev ProbedPath (W np : ℕ) := GrowthPath W × (Fin np → Fin W → ℂ)

/-- Law of `ProbedPath`: the path law and independent `g_j ~ CN(0, I_W)`
(`CoareaPalm.circularVectorLaw`, `E gg* = I`). -/
def probedPathLaw (W np : ℕ) (b : ℝ) : Measure (ProbedPath W np) :=
  (growthPathLaw W b).prod (Measure.pi fun _ : Fin np => circularVectorLaw (Fin W))

/-- `𝒦 = 𝒥*G𝒥` (interior block of `G`), the complex source data. -/
def complexSourceK (b E : ℝ) {np : ℕ} (W n : ℕ) (τ m : Fin np → ℝ) (x : ProbedPath W np) :
    Matrix (Fin np) (Fin np) ℂ :=
  (probeColumns W n τ m x.2)ᴴ * (fullInverse b E W n x.1).toBlocks₁₁ * probeColumns W n τ m x.2

/-- The boundary response frame `V_pr = 𝒰_n*𝒥 = (G_{int,ports})*𝒥` (so that
`Im 𝒦 = -η V_pr*V_pr`). -/
def probeFrame (b E : ℝ) {np : ℕ} (W n : ℕ) (τ m : Fin np → ℝ) (x : ProbedPath W np) :
    Matrix (Fin 2 × Fin W) (Fin np) ℂ :=
  (boundaryToInterior b E W n x.1)ᴴ * probeColumns W n τ m x.2

/-- The joint source data `(𝒦, M_pr, B_pr, J_pr)` at final length `n`:
`M_pr = V_pr*V_pr`, `B_pr = V_pr*PV_pr` (source Gram matrices) and the current seen by the
sources `J_pr = V_pr*JV_pr`. -/
def complexSourceData (b E : ℝ) {np : ℕ} (W n : ℕ) (τ m : Fin np → ℝ) (x : ProbedPath W np) :
    Fin 4 → Matrix (Fin np) (Fin np) ℂ :=
  let V := probeFrame b E W n τ m x
  ![complexSourceK b E W n τ m x, Vᴴ * V, Vᴴ * nearProjection W * V,
    Vᴴ * pathCurrent b E W n x.1 * V]

end BlockBand.Internal.Contracts.TransmissionPath
