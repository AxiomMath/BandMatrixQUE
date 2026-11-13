module

public import BlockBand.Internal.Contracts.TransmissionStatements
public import BlockBand.Internal.Contracts.TransmissionUniform
public import BlockBand.Foundations.Spectral.OrderedEigenpairs

/-!
# The transmission law: statements of the finite-`W` entrance and forcing

Every probabilistic statement below is **bulk-uniform** (`C, W₀` before `E ∈ bulkInterval κI`)
and therefore holds along every moving energy `e W → E` (`IsMovingEnergy`): see
`entranceAlong_of_bulk` for the reduction. Conventions: `0 < b < 1/2`,
`q = Tr Q = passiveMass`, `g = Tr T = 4ηq`, the near-end-grown path `growthPathLaw W b`, the
block added at step `r` carries absorption `κ(r/W)/W²` (`pathNearSchur b E κ`).

Statements:
* `GinibreSmallSingularFraction`: `E #{i : s_i(B)² < a} ≤ C_b W / log(1/a)`;
* `FiniteCoreEntrance`: `q_r/W` bounded below in probability at each fixed length;
* `ReciprocalDrift`: the one-step bound on `E r_K(q₊)`;
* `TransmissionEntranceBulk`: the transmission entrance bound, with absorption;
* `AbsorbedWardIdentity`, `InjectionNorms`, `InjectionMean`: the microscopic forcing.

Norms: Euclidean operator norm (`Matrix.Norms.L2Operator`) for matrices, as in `PassiveLayer`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawFinite

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.TransmissionUniform
open scoped ENNReal NNReal ComplexOrder Matrix Matrix.Norms.L2Operator

variable {W : ℕ}

/-!
## Vocabulary
-/

/-- `#{i : s_i(B)² < a}`: the number of eigenvalues of `BᴴB` below `a`, with multiplicity
(read through the increasing spectrum `increasingEigenvalue`, which is Borel in the matrix:
`BlockBand.Model.Construction.measurable_increasingEigenvalue`). -/
def smallSingularCount (a : ℝ) (B : Matrix (Fin W) (Fin W) ℂ) : ℕ :=
  (Finset.univ.filter fun i : Fin (Fintype.card (Fin W)) =>
    BlockBand.Foundations.Spectral.increasingEigenvalue
      (isHermitian_conjTranspose_mul_self B) i < a).card

/-- The bounded reciprocal `r_K(q) = min(q⁻¹, K⁻¹)`. -/
def recipK (K q : ℝ) : ℝ := min q⁻¹ K⁻¹

/-- The absorbed input `X - iε` of one fresh layer (`A - E - X ↦ A - E + iε - X`;
`Bridge.pathNearSchur_succ_eq_freshSchur`). -/
def absorbedInput (X : Matrix (Fin W) (Fin W) ℂ) (ε : ℝ) : Matrix (Fin W) (Fin W) ℂ :=
  X - (((ε : ℝ) : ℂ) * Complex.I) • (1 : Matrix (Fin W) (Fin W) ℂ)

/-- `𝒢₁₂` (block × port) of the fresh one-port layer at input `X`. -/
def freshG12 (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) :
    Matrix (Fin W) (Fin W) ℂ :=
  Matrix.of fun x y => freshLayer b E X ω (Sum.inl ((0 : Fin 1), x)) (Sum.inr ((0 : Fin 1), y))

/-- The injection `C = 𝒢₁₂*𝒢₁₂` of the absorbed layer. -/
def injection (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ε : ℝ)
    (ω : LayerSample W .oneBlockOnePort) : Matrix (Fin W) (Fin W) ℂ :=
  (freshG12 b E (absorbedInput X ε) ω)ᴴ * freshG12 b E (absorbedInput X ε) ω

/-- `L = K𝒢₁₂` of the absorbed layer with the *old* `K = z - X`. -/
def absorbedL (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (ε : ℝ)
    (ω : LayerSample W .oneBlockOnePort) : Matrix (Fin W) (Fin W) ℂ :=
  (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X) * freshG12 b E (absorbedInput X ε) ω

/-- The entrance event `{min_{1 ≤ r ≤ tW} g_r ≤ K}` of the path with absorption profile `κ`. -/
def entranceEvent (b E : ℝ) (κ : ℝ → ℝ) (K t : ℝ) (W : ℕ) : Set (GrowthPath W) :=
  {ω | ∃ r : ℕ, 1 ≤ r ∧ (r : ℝ) ≤ t * W ∧
    conductanceOf (pathTransmission b E κ W r ω) ≤ K}

/-!
## The Ginibre small-singular-value fraction
-/

/-- **Ginibre small singular values** (the paper proves it by Gaussian QR /
Bartlett, `det(B*B) = (b/W)^W ∏ G_j`, `G_j ~ Gamma(j,1)`, hence
`W⁻¹ E Σ_i log⁻(s_i(B)²) ≤ C_b`, then Markov). For `B ~ Gin(b/W)` and `0 < a < 1`,
`E #{i : s_i(B)² < a} ≤ C_b W / log(1/a)`; `C_b` depends on `b` only. Markov then bounds
`P(#{i : s_i(B)² < a} > εW) ≤ C_b/(ε log(1/a))` (`smallFraction_prob_le`). -/
def GinibreSmallSingularFraction : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∃ C : ℝ, ∀ W : ℕ, 0 < W → ∀ a : ℝ, 0 < a → a < 1 →
    ∫⁻ B, (smallSingularCount a B : ℝ≥0∞)
        ∂ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W)) ≤
      ENNReal.ofReal (C * W / Real.log a⁻¹)

/-!
## The finite core
-/

/-- **The finite core has `q_r/W` bounded below in probability** (the
initial bond, one additional fixed layer, iteration; with absorption the argument persists with
`A - E` replaced by `A - E + iε`). `b, κI`, the profile `κ`, `δ > 0` and the fixed length
`r ≥ 1` first; then `a > 0` and `W₀`; for `W ≥ W₀` and `E ∈ bulkInterval κI`, `P(q_r < aW) ≤ δ`. -/
def FiniteCoreEntrance : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI → ∀ κ : ℝ → ℝ, IsAbsorptionProfile κ →
    ∀ δ : ℝ, 0 < δ → ∀ r : ℕ, 1 ≤ r → ∃ a : ℝ, 0 < a ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ E ∈ bulkInterval κI,
        growthPathLaw W b {ω | passiveMass b E (pathNearSchur b E κ W r ω) < a * W} ≤
          ENNReal.ofReal δ

/-!
## The reciprocal drift
-/

/-- **One-step reciprocal drift** (with a fresh absorption `ε ≤ Kε/W²`). For a deterministic
passive old input `X` (the old path conditioned on, as in `Layers`) in a fixed scalar domain
`δ₀(X) ≤ d` and with `q = q(X) ≥ K`, one fresh layer with
absorption `ε` gives `q₊ = q(X₊)`, `X₊ = B*(A - E + iε - X)⁻¹B`, and
`E r_K(q₊) ≤ q⁻¹ + C(W⁻¹ + δ₀/q + (Wq)⁻¹ + ε/q) + C_{A,K} W^{-A}`.
Order: `b, κI, Kε` first; then the domain radius `d > 0` and `C` (independent of `K`); then
`K > 0`, `A > 0`; then `C_{A,K}`, `W₀`. (`ε/q` is the paper's `Cε/q`; summed over `TW`
layers with `ε ≤ Kε/W²` it is `O(1/(KW))`.) -/
def ReciprocalDrift : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI Kε : ℝ, 0 < κI → 0 ≤ Kε →
    ∃ d C : ℝ, 0 < d ∧ ∀ K A : ℝ, 0 < K → 0 < A → ∃ (CA : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W →
      ∀ E ∈ bulkInterval κI, ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ Kε / (W : ℝ) ^ 2 →
        jetDistance0 b E X ≤ d → K ≤ passiveMass b E X →
          ∫ ω, recipK K (passiveMass b E (freshSchur E (absorbedInput X ε) ω)) ∂freshLaw W b ≤
            (passiveMass b E X)⁻¹ + C * ((W : ℝ)⁻¹ + jetDistance0 b E X / passiveMass b E X +
              ((W : ℝ) * passiveMass b E X)⁻¹ + ε / passiveMass b E X) +
              CA * (W : ℝ) ^ (-A)

/-!
## The entrance
-/

/-- **The transmission entrance bound** (with bounded microscopic absorption on the entire initial
interval), bulk-uniform: `b, κI` and
the profile `κ` first; then `C`; then `K > 0`, `0 < t ≤ 1` and a slack `θ > 0`; then `W₀`; for
`W ≥ W₀` and `E ∈ bulkInterval κI`, `P(min_{1 ≤ r ≤ tW} g_r ≤ K) ≤ C(1+K)t + θ`. This is the
paper's `limsup_W P(⋯) ≤ C(1+K)t` with `C` uniform on the bulk set;
`entranceAlong_of_bulk` gives the along-moving-energy `limsup` form. `κ ≡ 0` is the unabsorbed
entrance. -/
def TransmissionEntranceBulk : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI → ∀ κ : ℝ → ℝ, IsAbsorptionProfile κ →
    ∃ C : ℝ, ∀ K t θ : ℝ, 0 < K → 0 < t → t ≤ 1 → 0 < θ → ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ E ∈ bulkInterval κI,
        growthPathLaw W b (entranceEvent b E κ K t W) ≤ ENNReal.ofReal (C * (1 + K) * t + θ)

/-- **The transmission entrance bound along moving energies** (the form used by
`TransmissionLawEnergyUniformContract`): `b`, base `E ∈ (-2,2)`, `κ` first; then `C`; for all
`K > 0`, `0 < t ≤ 1` and every moving energy `e W → E`,
`limsup_W P(min_{1 ≤ r ≤ tW} g_r(e W) ≤ K) ≤ C(1+K)t`. -/
def TransmissionEntranceAlong : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ κ : ℝ → ℝ, IsAbsorptionProfile κ →
    ∃ C : ℝ, ∀ K t : ℝ, 0 < K → 0 < t → t ≤ 1 → ∀ (Ce : ℝ) (e : ℕ → ℝ), IsMovingEnergy E Ce e →
      limsup (fun W : ℕ => growthPathLaw W b (entranceEvent b (e W) κ K t W)) atTop ≤
        ENNReal.ofReal (C * (1 + K) * t)

/-!
## The microscopic forcing
-/

/-- **The absorbed update** `Q₊ = L*QL + εC`, `C = 𝒢₁₂*𝒢₁₂`, almost surely for one
fresh layer at a deterministic passive `X` and `ε ≥ 0`, with `L = K𝒢₁₂` of the absorbed layer
and the old `K = z - X`, `Q = Q(X)`, `Q₊ = Q(X₊)`, `X₊ = B*(A - E + iε - X)⁻¹B`. (An exact
resolvent/Ward identity, stated separately because the entrance and the forcing both use it.) -/
def AbsorbedWardIdentity : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ W : ℕ, 0 < W →
    ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef → ∀ ε : ℝ, 0 ≤ ε →
      ∀ᵐ ω ∂freshLaw W b,
        passiveQ b E (freshSchur E (absorbedInput X ε) ω) =
          (absorbedL b E X ε ω)ᴴ * passiveQ b E X * absorbedL b E X ε ω +
            ((ε : ℝ) : ℂ) • injection b E X ε ω

/-- **Injection norms**: for `ε ≤ Kε/W²` the injection `εC` has operator
`L^p` norm `O(W⁻²)` and trace norm (`Tr C ≥ 0`) `O_{L^p}(W⁻¹)`, uniformly in passive `X`. -/
def InjectionNorms : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI Kε p : ℝ, 0 < κI → 0 ≤ Kε → 1 ≤ p →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ Kε / (W : ℝ) ^ 2 →
        eLpNorm (fun ω => ε * ‖injection b E X ε ω‖) (ENNReal.ofReal p) (freshLaw W b) ≤
            ENNReal.ofReal (C / (W : ℝ) ^ 2) ∧
          eLpNorm (fun ω => ε * (injection b E X ε ω).trace.re) (ENNReal.ofReal p)
            (freshLaw W b) ≤ ENNReal.ofReal (C / W)

/-- **Injection mean**: `W⁻¹ E(Tr C ∣ X) = d_* + O(δ₀ + q/W + W⁻¹)`,
`d_* = 1/(1-b)`, uniformly in passive `X` and `ε ≤ Kε/W²`. With `Q₊ = L*QL + εC` and
`ε = κ(r/W)/W²` this is the source of `h(t) = 4πρ(E)κ(t)` in the drift of `P₁`. -/
def InjectionMean : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI Kε : ℝ, 0 < κI → 0 ≤ Kε →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI,
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ Kε / (W : ℝ) ^ 2 →
        |(W : ℝ)⁻¹ * ∫ ω, (injection b E X ε ω).trace.re ∂freshLaw W b - dStar b| ≤
          C * (jetDistance0 b E X + passiveMass b E X / W + (W : ℝ)⁻¹)

end BlockBand.Transmission.LawFinite
