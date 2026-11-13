module

public import BlockBand.Internal.Contracts.TransmissionPath
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# The transmission generator and the full-source statements

Statements on one fresh layer at a passive input, the conductance and power sums of the
homogeneous path and their limiting martingale problem, the passive one-layer lemmas, the full
two-input transport, and the trace words of the two-input path with their generator, moments
and stopping.

## Conventions

* Parameters `0 < b < 1/2`, `c = 1-2b`; "fixed bulk energy" is `-2 < E < 2` with
  constants depending on `E`; the passive initial scalar lemma is uniform on `bulkInterval κ`.
* "For every fixed `p`": `∀ p ≥ 1, ∃ C` (on probability spaces `L^p`-bounds for `p ≥ 1`
  imply those for `0 < p < 1`). Constants come after every fixed parameter and before `W`;
  "`W` sufficiently large" is `∃ W₀, ∀ W ≥ W₀`. `O_D(W^{-D})` for every `D` is
  `∀ D, ∃ W₀, ∀ W ≥ W₀, ≤ W^{-D}` (as in `CoareaPalm`).
* Conditioning on the old path before a fresh layer is integration over the fresh layer at a
  *deterministic* old self-energy (the `Layers` convention; Fubini gives the conditional form).
  "Four old vectors" are then deterministic vectors.
* Expectations of nonnegative quantities are `lintegral`s of `‖·‖ₑ` (no integrability
  loophole); `‖·‖` on matrices is the Euclidean operator norm; `vecNorm` is the Euclidean norm.
* The crossed tensor `A ⊗ B = (v₁*Av₄)(v₃*Bv₂)` of the bilinear covariance
  `E[(v₁*U⁰v₂)(v₃*U⁰v₄)]`, without conjugation.
* Sources of a two-input path: tags `Q = Y_{j;k}/W` (birth index `k`) and interval
  sources `Q = Σ_k q((k+1)/W) Y_{j;k}/W²` (`TransmissionPath.intervalSource`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Internal.Contracts.TransmissionStatements

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath
open scoped ENNReal NNReal ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

/-!
## 0. Scalars and bilinear vocabulary
-/

/-- `c₀ = (2iη)⁻¹`. -/
def cZero (b E : ℝ) : ℂ := (2 * Complex.I * (etaZ b E : ℂ))⁻¹

/-- `α = (1-b)²/(bη)`. -/
def alphaCoef (b E : ℝ) : ℝ := (1 - b) ^ 2 / (b * etaZ b E)

/-- `θ_* = b a²/(1 + k₋ s_*)`, at a stationary jet `s`. -/
def thetaStar (b E : ℝ) (s : ℂ) : ℂ := (b : ℂ) * matchedA E ^ 2 / (1 + kMinus b E * s)

/-- The bilinear form `u* M v`. -/
def bilinear {n : Type*} [Fintype n] (u : n → ℂ) (M : Matrix n n ℂ) (v : n → ℂ) : ℂ :=
  star u ⬝ᵥ (M *ᵥ v)

/-- Euclidean norm `‖v‖ = (Σ|v_i|²)^{1/2}` of a vector. -/
def vecNorm {n : Type*} [Fintype n] (v : n → ℂ) : ℝ := Real.sqrt (∑ i, ‖v i‖ ^ 2)

/-- `∏_j ‖v_j‖` for four vectors. -/
def fourNorm {n : Type*} [Fintype n] (v₁ v₂ v₃ v₄ : n → ℂ) : ℝ :=
  vecNorm v₁ * vecNorm v₂ * vecNorm v₃ * vecNorm v₄

/-- The crossed tensor `A ⊗ B = (v₁*Av₄)(v₃*Bv₂)` of four vectors. -/
def crossedTensor {n : Type*} [Fintype n] (v₁ v₂ v₃ v₄ : n → ℂ) (A B : Matrix n n ℂ) : ℂ :=
  bilinear v₁ A v₄ * bilinear v₃ B v₂

/-- The bilinear covariance `E[(v₁*U⁰v₂)(v₃*U⁰v₄)]`, `U⁰ = U - E U`, under `μ`. -/
def bilinearCovariance {Ω n : Type*} [MeasurableSpace Ω] [Fintype n] (μ : Measure Ω)
    (U : Ω → Matrix n n ℂ) (v₁ v₂ v₃ v₄ : n → ℂ) : ℂ :=
  ∫ ω, bilinear v₁ (U ω - matrixExpect μ U) v₂ * bilinear v₃ (U ω - matrixExpect μ U) v₄ ∂μ

/-!
## 1. One fresh layer at a deterministic passive input
-/

/-- `f = R - c₀I`. -/
def passiveF {W : ℕ} (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  passiveResolvent b E X - cZero b E • (1 : Matrix (Fin W) (Fin W) ℂ)

/-- `q = Tr Q`. -/
def passiveMass {W : ℕ} (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  (passiveQ b E X).trace.re

/-- The law of one fresh one-port layer (`A ~ GUE_W(c/W)`, `B ~ Gin(b/W)`). -/
abbrev freshLaw (W : ℕ) (b : ℝ) : Measure (LayerSample W .oneBlockOnePort) :=
  layerLaw W b .oneBlockOnePort

/-- `X₊ = B*(A - E - X)⁻¹B`. -/
def freshSchur {W : ℕ} (E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) : Matrix (Fin W) (Fin W) ℂ :=
  Matrix.of fun x y => layerSchur .oneBlockOnePort E
    (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) ω ((0 : Fin 1), x) ((0 : Fin 1), y)

/-- `L f₊ L*`, `f₊ = R₊ - c₀I`, `R₊ = (z - X₊)⁻¹` (the transported `f`; it enters `T₊`). -/
def freshTransportedF {W : ℕ} (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) : Matrix (Fin W) (Fin W) ℂ :=
  freshL b E X ω * passiveF b E (freshSchur E X ω) * (freshL b E X ω)ᴴ

/-- `‖Q^{1/2} f Q^{1/2}‖_HS = (Tr Q f Q f*)^{1/2}` for `Q ⪰ 0`; the square root of
`Q` is not needed. -/
def hsSandwich {W : ℕ} (Q f : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  Real.sqrt (Q * f * Q * fᴴ).trace.re

/-!
## 2. The homogeneous near-end-grown path: conductance and power sums
-/

/-- `X_r` of the unabsorbed near-end-grown path at length `r`. -/
abbrev pathX (b E : ℝ) (W r : ℕ) (ω : GrowthPath W) : Matrix (Fin W) (Fin W) ℂ :=
  pathNearSchur b E (fun _ => 0) W r ω

/-- `g_r = Tr T_r` of the unabsorbed path. -/
def pathConductance (b E : ℝ) (W r : ℕ) (ω : GrowthPath W) : ℝ :=
  conductanceOf (pathTransmission b E (fun _ => 0) W r ω)

/-- `P_k(t) = Tr T^k_{⌊Wt⌋}`. -/
def powerTrace (b E : ℝ) (W k : ℕ) (t : ℝ) (ω : GrowthPath W) : ℝ :=
  ((pathTransmission b E (fun _ => 0) W ⌊(W : ℝ) * t⌋₊ ω) ^ k).trace.re

/-- `A_k(P)`. -/
def transmissionDrift (D0 : ℝ) (k : ℕ) (P : ℕ → ℝ) : ℝ :=
  -(D0 * k / 2) * P 1 * P k +
    D0 * k / 2 * ∑ j ∈ Finset.Ico 1 k, (P j * P (k - j) - P (j + 1) * P (k - j))

/-- `B_{kℓ}(P) = D₀kℓ(P_{k+ℓ} - P_{k+ℓ+1})`. -/
def transmissionBracket (D0 : ℝ) (k l : ℕ) (P : ℕ → ℝ) : ℝ :=
  D0 * k * l * (P (k + l) - P (k + l + 1))

/-- **Martingale increments for the natural filtration.** For times `s ≤ t` in `D`, the
increment `inc s t` is integrable and orthogonal to every bounded continuous function of
finitely many observations `obs i u` with `u ∈ D`, `u ≤ s`. This is `E[inc s t ∣ 𝓕_s] = 0`
for `𝓕_s = σ(obs i u : u ∈ D, u ≤ s)` (bounded continuous cylinder tests generate `𝓕_s`). With
`inc s t = M(t) - M(s)` it is the martingale property of `M`; with
`inc s t = (M(t) - M(s))² - ∫_s^t b` (given that `M` is a martingale) it says that
`M² - ∫ b` is a martingale. -/
def IsMartingaleIncrements {Ω I V F : Type*} [MeasurableSpace Ω] [TopologicalSpace V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (P : Measure Ω) (obs : I → ℝ → Ω → V) (D : Set ℝ)
    (inc : ℝ → ℝ → Ω → F) : Prop :=
  ∀ s t : ℝ, s ∈ D → t ∈ D → s ≤ t → Integrable (inc s t) P ∧
    ∀ (m : ℕ) (i : Fin m → I) (u : Fin m → ℝ), (∀ l, u l ∈ D ∧ u l ≤ s) →
      ∀ φ : BoundedContinuousFunction (Fin m → V) ℝ,
        ∫ ω, φ (fun l => obs (i l) (u l) ω) • inc s t ω ∂P = 0

/-- **`(P, Π)` is a limit of the power-sum processes** `P_k(t) = Tr T^k_{⌊Wt⌋}`, `k ≥ 1`: a
probability space carrying processes `Π_k` (only `k ≥ 1` is constrained) with continuous paths
on `(0,∞)`, whose finite-dimensional laws at positive times are the limits along some
subsequence `W_n → ∞` of those of `P_k` under `growthPathLaw` (weak convergence: bounded
continuous tests). By the tightness clause of the transmission generator theorem such limits
exist. The fdd limits are the process limits. -/
structure IsPowerTraceLimit (b E : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Pk : ℕ → ℝ → Ω → ℝ) : Prop where
  prob : IsProbabilityMeasure P
  measurable : ∀ k, 1 ≤ k → ∀ t, 0 < t → Measurable (Pk k t)
  continuous : ∀ k, 1 ≤ k → ∀ᵐ ω ∂P, ContinuousOn (fun t => Pk k t ω) (Set.Ioi 0)
  fdd : ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ (m : ℕ) (ks : Fin m → ℕ) (ts : Fin m → ℝ),
    (∀ l, 1 ≤ ks l ∧ 0 < ts l) → ∀ Φ : BoundedContinuousFunction (Fin m → ℝ) ℝ,
      Tendsto (fun n => ∫ ω, Φ (fun l => powerTrace b E (φ n) (ks l) (ts l) ω)
          ∂growthPathLaw (φ n) b) atTop (𝓝 (∫ ω, Φ (fun l => Pk (ks l) (ts l) ω) ∂P))

/-- **The finite-`W` conductance moments** (the first display of the conductance moment bounds,
stated at finite `W` as in the passive source-mixing lemma).
`b`, bulk `E`, the time horizon `T` and `p ≥ 1` first; then
`C = C_{p,T}`; for every `W ≥ 1` and every length `0 ≤ r ≤ TW` of the unabsorbed
near-end-grown path:
`E g_r^p ≤ C(1 + W^p/(r+1)^p)`.
-/
def ConductanceMomentBound : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ T p : ℝ, 1 ≤ p →
    ∃ C : ℝ, ∀ W : ℕ, 0 < W → ∀ r : ℕ, (r : ℝ) ≤ T * W →
      ∫⁻ ω, ‖pathConductance b E W r ω‖ₑ ^ p ∂growthPathLaw W b ≤
        ENNReal.ofReal (C * (1 + (W : ℝ) ^ p / ((r : ℝ) + 1) ^ p))

/-- The transmission generator theorem.
* `tight` ("jointly tight on compact positive-time intervals, with continuous
  limits"): for each `k ≥ 1` and `0 < ε < T`, the one-time laws at `ε` are tight and the
  `[ε,T]` sup-modulus of continuity is asymptotically small in probability. For processes
  with paths in `D` this is `C`-tightness (Billingsley, Thm. 13.2 with the sup-modulus): tight,
  with every limit point continuous; joint tightness over `k` in the product topology follows.
* `martingale`: every limit (`IsPowerTraceLimit`) solves the martingale problem on
  positive times: for `k, ℓ ≥ 1`, `M_k = P_k - ∫ A_k(P)` is a martingale and
  `M_kM_ℓ - ∫ B_{kℓ}(P)` is a martingale (natural filtration of the limit).
* `conductanceMoments` (finite `W` and `r ≤ TW` explicit): `ConductanceMomentBound`.
* `meanConductance`: every limit has `E P_1(t) ≤ 2/(D₀t)`, `t > 0`
  (the proof takes limits on positive-time intervals). -/
structure TransmissionGeneratorContract : Prop where
  tight : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ k : ℕ, 1 ≤ k → ∀ ε T : ℝ, 0 < ε → ε < T →
      (∀ θ : ℝ, 0 < θ → ∃ (M : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W →
        growthPathLaw W b {ω | M < |powerTrace b E W k ε ω|} ≤ ENNReal.ofReal θ) ∧
      (∀ η θ : ℝ, 0 < η → 0 < θ → ∃ δ : ℝ, 0 < δ ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
        growthPathLaw W b {ω | ∃ t ∈ Set.Icc ε T, ∃ t' ∈ Set.Icc ε T, |t - t'| ≤ δ ∧
          η < |powerTrace b E W k t ω - powerTrace b E W k t' ω|} ≤ ENNReal.ofReal θ)
  martingale : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (Pk : ℕ → ℝ → Ω → ℝ),
      IsPowerTraceLimit b E P Pk →
      let obs : {k : ℕ // 1 ≤ k} → ℝ → Ω → ℝ := fun k => Pk k.1
      let M : ℕ → ℝ → ℝ → Ω → ℝ := fun k s t ω => Pk k t ω - Pk k s ω -
        ∫ u in s..t, transmissionDrift (transportD0 b E) k (fun i => Pk i u ω)
      (∀ k : ℕ, 1 ≤ k → IsMartingaleIncrements P obs (Set.Ioi 0) (M k)) ∧
      ∀ k l : ℕ, 1 ≤ k → 1 ≤ l → IsMartingaleIncrements P obs (Set.Ioi 0) fun s t ω =>
        M k s t ω * M l s t ω -
          ∫ u in s..t, transmissionBracket (transportD0 b E) k l (fun i => Pk i u ω)
  conductanceMoments : ConductanceMomentBound
  meanConductance : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (Pk : ℕ → ℝ → Ω → ℝ),
      IsPowerTraceLimit b E P Pk → ∀ t : ℝ, 0 < t →
        ∫⁻ ω, ‖Pk 1 t ω‖ₑ ∂P ≤ ENNReal.ofReal (2 / (transportD0 b E * t))

/-- The passive initial scalar lemma.
* `moment`: `sup_{1 ≤ r ≤ TW} ‖δ_{0,r}‖_p ≤ C_{p,T}/W`.
* `exit`: for fixed `d_* > 0` and every `D`, `P(∃ r ≤ TW, δ_{0,r} > d_*) ≤ W^{-D}`.
* `absorbedMoment` ("the same fixed-moment conclusions" with deterministic nonnegative
  absorptions `≤ K/W²`): every block of the length-`r` path carries its own deterministic
  absorption `ε_i ∈ [0, K/W²]` (`A - E ↦ A - E + iε_i`); the bound is uniform over them. -/
structure PassiveInitialScalarContract : Prop where
  moment : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T p : ℝ, 0 < κ → 1 ≤ p →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ r : ℕ, 1 ≤ r →
      (r : ℝ) ≤ T * W →
        eLpNorm (fun ω => jetDistance0 b E (pathX b E W r ω)) (ENNReal.ofReal p)
          (growthPathLaw W b) ≤ ENNReal.ofReal (C / W)
  exit : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T d D : ℝ, 0 < κ → 0 < d → 0 < D →
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ,
      growthPathLaw W b {ω | ∃ r : ℕ, 1 ≤ r ∧ (r : ℝ) ≤ T * W ∧
        d < jetDistance0 b E (pathX b E W r ω)} ≤ ENNReal.ofReal ((W : ℝ) ^ (-D))
  absorbedMoment : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T K p : ℝ, 0 < κ → 0 ≤ K → 1 ≤ p →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ, ∀ r : ℕ, 1 ≤ r →
      (r : ℝ) ≤ T * W → ∀ ε : Fin r → ℝ, (∀ i, 0 ≤ ε i ∧ ε i ≤ K / (W : ℝ) ^ 2) →
        eLpNorm (fun ω => jetDistance0 b E
            (nearSchur (boundaryZ b E) (absorbedPathSchur E ε (pathAt W r ω))))
          (ENNReal.ofReal p) (growthPathLaw W b) ≤ ENNReal.ofReal (C / W)

/-!
## 3. The two passive one-layer lemmas
-/

/-- **The passive covariance lemma.** Fixed `b`, bulk `E`; the
stationary jet `s_*` exists (it is unique; the clause holds at every solution); then `C, W₀`;
for `W ≥ W₀`, every deterministic passive old input `X` (`Y = -Im X ⪰ 0`, the old path
integrated out) and four deterministic old vectors, with `U = LL*` of one fresh one-port
layer and `U⁰ = U - E(U ∣ X)`:
`|E[(v₁*U⁰v₂)(v₃*U⁰v₄)] - {(D₀/2W)[I⊗(I-T) + (I-T)⊗I] + (σ₋/W) f⊗f + (σ̄₋/W) f*⊗f*}|
 ≤ C[W⁻² + W⁻¹(δ₀ + δ₁ + q/W)] ∏‖v_j‖`, `A⊗B = (v₁*Av₄)(v₃*Bv₂)`, `T, f, q, δ₀, δ₁` of `X`.
Uniform in `X` and the vectors (no scalar-domain restriction: off a fixed jet domain the bound
follows from the passive bounds lemma with a larger `C`).
-/
def PassiveCovarianceContract : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    (∃ s : ℂ, IsStationaryJet b E s) ∧ ∀ s : ℂ, IsStationaryJet b E s →
      ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
        (passiveY X).PosSemidef → ∀ v₁ v₂ v₃ v₄ : Fin W → ℂ,
        let T := passiveTransmission b E X
        let f := passiveF b E X
        let I : Matrix (Fin W) (Fin W) ℂ := 1
        ‖bilinearCovariance (freshLaw W b) (freshU b E X) v₁ v₂ v₃ v₄ -
            ((((transportD0 b E / (2 * W) : ℝ)) : ℂ) *
                (crossedTensor v₁ v₂ v₃ v₄ I (I - T) + crossedTensor v₁ v₂ v₃ v₄ (I - T) I) +
              sigmaMinus b E s / W * crossedTensor v₁ v₂ v₃ v₄ f f +
              conj (sigmaMinus b E s) / W * crossedTensor v₁ v₂ v₃ v₄ fᴴ fᴴ)‖ ≤
          C * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ *
            (jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W)) *
            fourNorm v₁ v₂ v₃ v₄

/-- The passive source-mixing lemma.
* `mixing`: `0 < ε < T`, `p ≥ 1` first; then `C = C_{p,ε,T}`,
  `W₀`; for `W ≥ W₀` and every length `εW ≤ r ≤ TW` of the unabsorbed near-end-grown path,
  `‖Tr(Q_r f_r)‖_p + ‖‖Q_r^{1/2} f_r Q_r^{1/2}‖_HS‖_p ≤ C W^{-1/2}`.
* `finiteConductance`: `ConductanceMomentBound` (at finite `W`). -/
structure PassiveSourceMixingContract : Prop where
  mixing : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ ε T p : ℝ, 0 < ε → ε < T → 1 ≤ p → ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W →
      ∀ r : ℕ, ε * W ≤ r → (r : ℝ) ≤ T * W →
        eLpNorm (fun ω => (passiveQ b E (pathX b E W r ω) *
            passiveF b E (pathX b E W r ω)).trace) (ENNReal.ofReal p) (growthPathLaw W b) +
          eLpNorm (fun ω => hsSandwich (passiveQ b E (pathX b E W r ω))
            (passiveF b E (pathX b E W r ω))) (ENNReal.ofReal p) (growthPathLaw W b) ≤
          ENNReal.ofReal (C / Real.sqrt W)
  finiteConductance : ConductanceMomentBound
  oneStepMean : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    (∃ s : ℂ, IsStationaryJet b E s) ∧ ∀ s : ℂ, IsStationaryJet b E s →
      ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
        (passiveY X).PosSemidef →
        ‖matrixExpect (freshLaw W b) (freshTransportedF b E X) -
            (thetaStar b E s / (1 + alphaCoef b E * passiveMass b E X / W)) • passiveF b E X‖ ≤
          C * (jetDistance0 b E X + jetDistance1 b E s X + passiveMass b E X / W +
            (W : ℝ)⁻¹ ^ 2)
  oneStepFluctuation : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ p : ℝ, 1 ≤ p → ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef → ∀ u v : Fin W → ℂ,
        eLpNorm (fun ω => bilinear u (freshU b E X ω -
            matrixExpect (freshLaw W b) (freshU b E X)) v) (ENNReal.ofReal p) (freshLaw W b) ≤
          ENNReal.ofReal (C / Real.sqrt W * vecNorm u * vecNorm v) ∧
        eLpNorm (fun ω => bilinear u (freshTransportedF b E X ω -
            matrixExpect (freshLaw W b) (freshTransportedF b E X)) v) (ENNReal.ofReal p)
            (freshLaw W b) ≤
          ENNReal.ofReal (C / Real.sqrt W * vecNorm u * vecNorm v)

/-!
## 4. The full two-input transport at a deterministic old two-port Schur matrix
-/

/-- `ℝ = (z - 𝕏)⁻¹` of an old two-port Schur matrix `𝕏`. -/
def twoPortResolvent {W : ℕ} (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - XX)⁻¹

/-- `𝕊 = I - 2iηℝ`. -/
def twoPortScattering {W : ℕ} (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  1 - ((2 * etaZ b E : ℝ) * Complex.I) • twoPortResolvent b E XX

/-- `Δ = K𝒢₁₁K - K`, `K = z - X`. -/
def freshDelta {W : ℕ} (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) : Matrix (Fin W) (Fin W) ℂ :=
  let K := boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X
  K * (Matrix.of fun x y =>
    freshLayer b E X ω (Sum.inl ((0 : Fin 1), x)) (Sum.inl ((0 : Fin 1), y))) * K - K

/-- `N = [[L, Δℝ₁₂],[0, I]]`, near block first; `X` is the far-eliminated `𝕏`. -/
def freshTransport {W : ℕ} (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  let X := nearSchur (boundaryZ b E) XX
  let L := freshL b E X ω
  let DR := freshDelta b E X ω * portBlock (twoPortResolvent b E XX) 0 1
  Matrix.of fun x y =>
    if x.1 = 0 ∧ y.1 = 0 then L x.2 y.2
    else if x.1 = 0 ∧ y.1 = 1 then DR x.2 y.2
    else if x.1 = 1 ∧ y.1 = 1 then (1 : Matrix (Fin W) (Fin W) ℂ) x.2 y.2
    else 0

/-- `𝓔 = NN* - I`. -/
def wardNoise {W : ℕ} (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  freshTransport b E XX ω * (freshTransport b E XX ω)ᴴ - 1

/-- **The full-source covariance lemma.** Fixed `b`, bulk `E`; the stationary jet exists and,
at every stationary jet `s`:
`C, W₀`; for `W ≥ W₀`, every deterministic Hermitian old two-port
Schur matrix `𝕏` (the unabsorbed path integrated out), its far-eliminated `X`,
`ℝ = (z - 𝕏)⁻¹`, `𝕊 = I - 2iηℝ`, `P = diag(I_W,0)`, `P' = 𝕊*P𝕊`, `g = Tr T(X)`, and four
deterministic old vectors in `ℂ^{2W}`: the centered covariance of `𝓔 = NN* - I` satisfies
`|E[(v₁*𝓔⁰v₂)(v₃*𝓔⁰v₄)] - {(D₀/2W)(P⊗P' + P'⊗P) - σ₋/(4η²W) P𝕊⊗P𝕊 - σ̄₋/(4η²W) 𝕊*P⊗𝕊*P}|
 ≤ C[W⁻² + W⁻¹(δ₀ + δ₁ + g/W)] ∏‖v_i‖`.
Uniform in `𝕏`.
-/
def FullSourceCovarianceContract : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    (∃ s : ℂ, IsStationaryJet b E s) ∧ ∀ s : ℂ, IsStationaryJet b E s →
      ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W →
        ∀ XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, XX.IsHermitian →
        ∀ v₁ v₂ v₃ v₄ : Fin 2 × Fin W → ℂ,
        let X := nearSchur (boundaryZ b E) XX
        let P := nearProjection W
        let S := twoPortScattering b E XX
        let P' := Sᴴ * P * S
        let η2 : ℂ := ((4 * etaZ b E ^ 2 * W : ℝ) : ℂ)
        ‖bilinearCovariance (freshLaw W b) (wardNoise b E XX) v₁ v₂ v₃ v₄ -
            ((((transportD0 b E / (2 * W) : ℝ)) : ℂ) *
                (crossedTensor v₁ v₂ v₃ v₄ P P' + crossedTensor v₁ v₂ v₃ v₄ P' P) -
              sigmaMinus b E s / η2 * crossedTensor v₁ v₂ v₃ v₄ (P * S) (P * S) -
              conj (sigmaMinus b E s) / η2 * crossedTensor v₁ v₂ v₃ v₄ (Sᴴ * P) (Sᴴ * P))‖ ≤
          C * ((W : ℝ)⁻¹ ^ 2 + (W : ℝ)⁻¹ * (jetDistance0 b E X + jetDistance1 b E s X +
            conductanceOf (passiveTransmission b E X) / W)) * fourNorm v₁ v₂ v₃ v₄

/-!
## 5. Trace words of the two-input path
-/

/-- Trace-class letters: the current `J`, tags `Q_a` and interval sources `Q_a`. -/
inductive TraceLetter (nT nI : ℕ)
  /-- `J = P' - P`. -/
  | current
  /-- tag `a`: `Q = Y_{j;k_a}/W`. -/
  | tag (a : Fin nT)
  /-- interval source `a`: `Q = Σ_k q_a((k+1)/W) Y_{j;k}/W²`. -/
  | interval (a : Fin nI)
  deriving DecidableEq

/-- Separators: ordinary `I`, `P`; contracting `P𝕊`, `𝕊*P`, `P𝕊P`, `P𝕊*P`. -/
inductive Separator
  | id
  | proj
  | projS
  | sStarProj
  | projSProj
  | projSStarProj
  deriving DecidableEq

/-- Unconjugated contracting separators (`P𝕊`, `P𝕊P`; mean factor `θ_*`). -/
def Separator.unconj : Separator → ℕ
  | .projS => 1
  | .projSProj => 1
  | _ => 0

/-- Conjugated contracting separators (`𝕊*P`, `P𝕊*P`; mean factor `θ̄_*`). -/
def Separator.conj : Separator → ℕ
  | .sStarProj => 1
  | .projSStarProj => 1
  | _ => 0

/-- A cyclic word in normal form `Tr(A₁B₁A₂B₂⋯A_rB_r)`, `A_i` trace-class letters and `B_i`
separators. Every cyclic word in these letters whose consecutive contracting letters
are separated by a trace-class letter reduces to this form (`P² = P`, `P·P𝕊 = P𝕊`, …). -/
abbrev TraceWord (nT nI : ℕ) := List (TraceLetter nT nI × Separator)

/-- Ordinary words: nonempty, separators `I` or `P` only. -/
def IsOrdinaryWord {nT nI : ℕ} (w : TraceWord nT nI) : Prop :=
  w ≠ [] ∧ ∀ x ∈ w, x.2 = .id ∨ x.2 = .proj

/-- An admitted product of words: every factor is a nonempty normal-form word
(no free trace of `I` or `P`). -/
def IsAdmittedProduct {nT nI : ℕ} (Zs : List (TraceWord nT nI)) : Prop := ∀ w ∈ Zs, w ≠ []

/-- Word degree of a product: total number of letters. -/
def productDegree {nT nI : ℕ} (Zs : List (TraceWord nT nI)) : ℕ := (Zs.map List.length).sum

/-- Number `r` of unconjugated contracting letters of a product. -/
def unconjCount {nT nI : ℕ} (Zs : List (TraceWord nT nI)) : ℕ :=
  (Zs.map fun w => (w.map fun x => x.2.unconj).sum).sum

/-- Number `r̄` of conjugated contracting letters of a product. -/
def conjCount {nT nI : ℕ} (Zs : List (TraceWord nT nI)) : ℕ :=
  (Zs.map fun w => (w.map fun x => x.2.conj).sum).sum

/-- The letter matrices at path length `j` (tags at birth indices `k`, interval tests `q`). -/
def letterMatrix (b E : ℝ) {nT nI : ℕ} (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (W j : ℕ)
    (ω : GrowthPath W) : TraceLetter nT nI → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ
  | .current => pathCurrent b E W j ω
  | .tag a => (W : ℂ)⁻¹ • tagResponse b E W j (k a) ω
  | .interval a => intervalSource b E W j (q a) ω

/-- The separator matrices at path length `j`. -/
def separatorMatrix (b E : ℝ) (W j : ℕ) (ω : GrowthPath W) :
    Separator → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ
  | .id => 1
  | .proj => nearProjection W
  | .projS => nearProjection W * scatteringMatrix b E W j ω
  | .sStarProj => (scatteringMatrix b E W j ω)ᴴ * nearProjection W
  | .projSProj => nearProjection W * scatteringMatrix b E W j ω * nearProjection W
  | .projSStarProj => nearProjection W * (scatteringMatrix b E W j ω)ᴴ * nearProjection W

/-- The value `Tr(A₁B₁⋯A_rB_r)` of a word at path length `j`. -/
def wordValue (b E : ℝ) {nT nI : ℕ} (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (W j : ℕ)
    (ω : GrowthPath W) (w : TraceWord nT nI) : ℂ :=
  (w.map fun x => letterMatrix b E k q W j ω x.1 * separatorMatrix b E W j ω x.2).prod.trace

/-- The value of a product of words. -/
def productValue (b E : ℝ) {nT nI : ℕ} (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (W j : ℕ)
    (ω : GrowthPath W) (Zs : List (TraceWord nT nI)) : ℂ :=
  (Zs.map (wordValue b E k q W j ω)).prod

/-- Nuclear norm `Tr|M| = Σ|λ_i|` of a (Hermitian) matrix, eigenvalues via `charpoly.roots`. -/
def nuclearNorm {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) : ℝ :=
  (M.charpoly.roots.map fun z => ‖z‖).sum

/-- The source letters `Fin nT ⊕ Fin nI → TraceLetter`. -/
def sourceLetter {nT nI : ℕ} : Fin nT ⊕ Fin nI → TraceLetter nT nI :=
  Sum.elim TraceLetter.tag TraceLetter.interval

/-- `Tr Q_{a,j}` of source `a`. -/
def sourceTrace (b E : ℝ) {nT nI : ℕ} (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (W j : ℕ)
    (ω : GrowthPath W) (a : Fin nT ⊕ Fin nI) : ℝ :=
  (letterMatrix b E k q W j ω (sourceLetter a)).trace.re

/-- `Σ_a Tr Q_{a,j} + Tr|J_j|`, the quantity controlled by the trace stop. -/
def traceLoad (b E : ℝ) {nT nI : ℕ} (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (W j : ℕ)
    (ω : GrowthPath W) : ℝ :=
  ∑ a, sourceTrace b E k q W j ω a + nuclearNorm (pathCurrent b E W j ω)

/-- The trace stop `σ_K`: the first length `j ≥ εW` with `Σ_a Tr Q_{a,j} + Tr|J_j| > K`
(`⊤` if none). -/
def traceStop (b E : ℝ) {nT nI : ℕ} (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (K ε : ℝ) (W : ℕ)
    (ω : GrowthPath W) : ℕ∞ :=
  ⨅ (i : ℕ) (_ : ε * W ≤ i ∧ K < traceLoad b E k q W i ω), (i : ℕ∞)

/-- The survival event `{j < σ_K}`. -/
def alive (b E : ℝ) {nT nI : ℕ} (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (K ε : ℝ) (W j : ℕ) :
    Set (GrowthPath W) :=
  {ω | (j : ℕ∞) < traceStop b E k q K ε W ω}

/-!
### The contraction rule: word generator and word covariance
-/

/-- Trace polynomials: polynomials in word values. -/
abbrev TracePoly (nT nI : ℕ) := MvPolynomial (TraceWord nT nI) ℂ

/-- Ordinary trace polynomials: every variable is an ordinary word. -/
def IsOrdinaryPoly {nT nI : ℕ} (Φ : TracePoly nT nI) : Prop := ∀ w ∈ Φ.vars, IsOrdinaryWord w

/-- Replace the last separator of a word. -/
def setLastSep {nT nI : ℕ} (w : TraceWord nT nI) (s : Separator) : TraceWord nT nI :=
  w.dropLast ++ (w.getLast?.map fun x => (x.1, s)).toList

/-- The separator after the `i`-th letter. -/
def sepAt {nT nI : ℕ} (w : TraceWord nT nI) (i : ℕ) : Separator :=
  (w.getD i (.current, .id)).2

/-- The word variable. -/
abbrev wv {nT nI : ℕ} (w : TraceWord nT nI) : TracePoly nT nI := MvPolynomial.X w

/-- `g = ½ Tr J²`. -/
def gPoly {nT nI : ℕ} : TracePoly nT nI :=
  MvPolynomial.C (1 / 2 : ℂ) * wv [(.current, .id), (.current, .id)]

/-- Pair `i < j` of separators of one word `w`: writing `Tr w = Tr(A dB B dB)` with `dB` at
`i, j`, the contraction `(D₀/2)[Tr(AP)Tr(BP') + Tr(AP')Tr(BP)]`, `P' = P + J`.
`S₁` runs from letter `j+1` to letter `i`, `S₂` from `i+1`
to `j` (cyclically); `A = P^{e_j}S₁P^{e_i}`, `B = P^{e_i}S₂P^{e_j}`. -/
def pairTerm (D0 : ℝ) {nT nI : ℕ} (w : TraceWord nT nI) (i j : ℕ) : TracePoly nT nI :=
  let S₁ := (w.rotate (j + 1)).take (w.length - (j - i))
  let S₂ := (w.rotate (i + 1)).take (j - i)
  let AP := wv (setLastSep S₁ .proj)
  let AP' := AP + wv (S₁ ++ [(.current, sepAt w j)])
  let BP := wv (setLastSep S₂ .proj)
  let BP' := BP + wv (S₂ ++ [(.current, sepAt w i)])
  MvPolynomial.C ((D0 / 2 : ℝ) : ℂ) * (AP * BP' + AP' * BP)

/-- Separator `i` of `w` and separator `j` of `v`: `Tr w = Tr(A dB)`, `Tr v = Tr(B dB)`,
contraction `(D₀/2)[Tr(APBP') + Tr(AP'BP)]`, with
`A = P^{e_i}S_wP^{e_i}`, `B = P^{e_j}S_vP^{e_j}`, `S_w` the rotation of `w` after separator `i`. -/
def crossTerm (D0 : ℝ) {nT nI : ℕ} (w v : TraceWord nT nI) (i j : ℕ) : TracePoly nT nI :=
  let Sw := w.rotate (i + 1)
  let Sv := v.rotate (j + 1)
  let base := wv (setLastSep Sw .proj ++ setLastSep Sv .proj)
  let APBP' := base + wv (setLastSep Sw .proj ++ Sv ++ [(.current, sepAt w i)])
  let AP'BP := base + wv (Sw ++ [(.current, sepAt v j)] ++ setLastSep Sv .proj)
  MvPolynomial.C ((D0 / 2 : ℝ) : ℂ) * (APBP' + AP'BP)

/-- Drift of a word: each separator `P` contributes `-(D₀g/2)` times the word, and each pair of
separators contributes `pairTerm`. -/
def wordDrift (D0 : ℝ) {nT nI : ℕ} (w : TraceWord nT nI) : TracePoly nT nI :=
  -(MvPolynomial.C ((D0 / 2 : ℝ) : ℂ) * gPoly *
      MvPolynomial.C ((w.countP fun x => decide (x.2 = Separator.proj) : ℕ) : ℂ) * wv w) +
    ∑ i ∈ Finset.range w.length, ∑ j ∈ Finset.Ioo i w.length, pairTerm D0 w i j

/-- Bracket rate `d⟨Tr w, Tr v⟩/dt`: sum over all separators of `w` and of `v`. -/
def wordCov (D0 : ℝ) {nT nI : ℕ} (w v : TraceWord nT nI) : TracePoly nT nI :=
  ∑ i ∈ Finset.range w.length, ∑ j ∈ Finset.range v.length, crossTerm D0 w v i j

/-- Continuous injection: `d_*q_a(t)` for `Tr Q_a` and `Tr(Q_aP)` of an interval
source, zero for every other word. -/
def wordInjection (b : ℝ) {nT nI : ℕ} (q : Fin nI → ℝ → ℝ) (t : ℝ) :
    TraceWord nT nI → ℂ
  | [(.interval a, s)] => if s = .id ∨ s = .proj then ((dStar b * q a t : ℝ) : ℂ) else 0
  | _ => 0

/-- The generator on trace polynomials ("apply the product rule"):
`𝒜_tΦ = Σ_w ∂_wΦ (drift_w + inj_w(t)) + ½ Σ_{w,v} ∂_v∂_wΦ cov_{w,v}`. -/
def wordGenerator (b E : ℝ) {nT nI : ℕ} (q : Fin nI → ℝ → ℝ) (t : ℝ) (Φ : TracePoly nT nI) :
    TracePoly nT nI :=
  ∑ w ∈ Φ.vars, MvPolynomial.pderiv w Φ *
      (wordDrift (transportD0 b E) w + MvPolynomial.C (wordInjection b q t w)) +
    MvPolynomial.C (1 / 2 : ℂ) * ∑ w ∈ Φ.vars, ∑ v ∈ Φ.vars,
      MvPolynomial.pderiv v (MvPolynomial.pderiv w Φ) * wordCov (transportD0 b E) w v

/-- The bracket rate of a trace polynomial: `Γ(Φ) = Σ_{w,v} ∂_wΦ ∂_vΦ cov_{w,v}`. -/
def wordCarre (b E : ℝ) {nT nI : ℕ} (Φ : TracePoly nT nI) : TracePoly nT nI :=
  ∑ w ∈ Φ.vars, ∑ v ∈ Φ.vars,
    MvPolynomial.pderiv w Φ * MvPolynomial.pderiv v Φ * wordCov (transportD0 b E) w v

/-- Evaluation of a trace polynomial on the words of the path at length `j`. -/
def polyValue (b E : ℝ) {nT nI : ℕ} (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (W j : ℕ)
    (ω : GrowthPath W) (Φ : TracePoly nT nI) : ℂ :=
  MvPolynomial.eval (wordValue b E k q W j ω) Φ

/-- Admissible interval tests (`IsSourceTest` on some interval). -/
def IsIntervalTests {nI : ℕ} (q : Fin nI → ℝ → ℝ) : Prop :=
  ∀ a, ∃ s T : ℝ, IsSourceTest s T (q a)

/-!
## 6. Statements on the two-input path
-/

/-- Moments of the full-source clocks and tags.
* `clock`: `T`, `p ≥ 1`, then `C_{p,T}`, `W₀`: `‖W⁻¹Tr Y_j^1‖_p ≤ C(j+1)` for `j ≤ TW`.
* `clockSquare`: `T`, then `C_T`, `W₀`: `E Tr(Y_j^1)² ≤ C W (j+1)³` for `j ≤ TW`.
* `tag`: `T`, `p ≥ 1`, then `C_{p,T}`, `W₀`: `‖W⁻¹Tr Y_{j;k}‖_p ≤ C` for `k < j ≤ TW`. -/
structure FullSourceMomentsContract : Prop where
  clock : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ T p : ℝ, 1 ≤ p →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ j : ℕ, (j : ℝ) ≤ T * W →
      eLpNorm (fun ω => (W : ℂ)⁻¹ * ((boundaryToInterior b E W j ω)ᴴ *
          boundaryToInterior b E W j ω).trace) (ENNReal.ofReal p) (growthPathLaw W b) ≤
        ENNReal.ofReal (C * ((j : ℝ) + 1))
  clockSquare : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ T : ℝ,
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ j : ℕ, (j : ℝ) ≤ T * W →
      ∫⁻ ω, ‖(((boundaryToInterior b E W j ω)ᴴ * boundaryToInterior b E W j ω) ^ 2).trace‖ₑ
          ∂growthPathLaw W b ≤ ENNReal.ofReal (C * W * ((j : ℝ) + 1) ^ 3)
  tag : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ T p : ℝ, 1 ≤ p →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ j : ℕ, (j : ℝ) ≤ T * W → ∀ k : ℕ, k < j →
      eLpNorm (fun ω => (W : ℂ)⁻¹ * (tagResponse b E W j k ω).trace) (ENNReal.ofReal p)
          (growthPathLaw W b) ≤ ENNReal.ofReal C

/-- The value of a tag at its birth.
* `trace`: for every `p ≥ 1`, `‖W⁻¹Tr Y_{k+1;k} - d_*‖_p → 0` as `W → ∞`, uniformly in
  `εW ≤ k`, `k + 1 ≤ TW` (`∀ θ > 0, ∃ W₀`);
* `square`: `E Tr(Y_{k+1;k}/W)² ≤ C/W` for `W ≥ W₀`, uniformly in the same `k`. -/
structure TagBirthValueContract : Prop where
  trace : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ ε T p : ℝ, 0 < ε → ε < T →
    1 ≤ p → ∀ θ : ℝ, 0 < θ → ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ k : ℕ, ε * W ≤ k →
      ((k + 1 : ℕ) : ℝ) ≤ T * W →
        eLpNorm (fun ω => (W : ℂ)⁻¹ * (tagResponse b E W (k + 1) k ω).trace - (dStar b : ℂ))
          (ENNReal.ofReal p) (growthPathLaw W b) ≤ ENNReal.ofReal θ
  square : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ ε T : ℝ, 0 < ε → ε < T →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ k : ℕ, ε * W ≤ k → ((k + 1 : ℕ) : ℝ) ≤ T * W →
      ∫⁻ ω, ‖(((W : ℂ)⁻¹ • tagResponse b E W (k + 1) k ω) ^ 2).trace‖ₑ ∂growthPathLaw W b ≤
        ENNReal.ofReal (C / W)

/-- **Edge-clock moments** (from the linearly weighted recursion proving the full clock moments,
begun with zero clock at the start of an injection interval), as used in the edge-clock moment
lemma. The constant does not depend on the preceding length. Fixed `b`, bulk `E`;
`R₀ > 0`, `p ≥ 1`, then
`C = C_{p,R₀}`; then the total length `T` and `W₀ = W₀(T)` (the exit bound removes the stops "on
each fixed total length"); for `W ≥ W₀`, every start `t₁ ≥ 0` of the injection (the preceding
path has `≈ t₁W` blocks), injection length `0 ≤ R ≤ R₀` and propagation by at most `R₀`
(`t₁ + R + R₀ ≤ T`): the interval clock with indicator test `q = 1_{[t₁, t₁+R]}` (normalized by
`W²`) satisfies `‖Tr Q_j‖_p ≤ C` at every length `j ≤ (t₁ + R + R₀)W`.
-/
def EdgeClockMomentsContract : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ R₀ p : ℝ, 0 < R₀ → 1 ≤ p →
    ∃ C : ℝ, ∀ T : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ t₁ R : ℝ, 0 ≤ t₁ → 0 ≤ R → R ≤ R₀ →
      t₁ + R + R₀ ≤ T → ∀ j : ℕ, (j : ℝ) ≤ (t₁ + R + R₀) * W →
        eLpNorm (fun ω => (intervalSource b E W j
            ((Set.Icc t₁ (t₁ + R)).indicator fun _ => (1 : ℝ)) ω).trace)
          (ENNReal.ofReal p) (growthPathLaw W b) ≤ ENNReal.ofReal C

/-- **A joint critical limit of the trace words** on `[t₀, ∞)` of a source family with tag
birth indices `k(W)` and interval tests `q`: a probability space carrying complex processes
`Z_w` (only ordinary words are constrained) with continuous paths on `[t₀,∞)`, whose
finite-dimensional laws are the limits, along some subsequence `W_n → ∞`, of those of the
ordinary word values `Tr w` of the path of length `⌊Wt⌋` (bounded continuous tests). -/
structure IsWordLimit (b E : ℝ) {nT nI : ℕ} (k : ℕ → Fin nT → ℕ) (q : Fin nI → ℝ → ℝ)
    (t₀ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : TraceWord nT nI → ℝ → Ω → ℂ) : Prop where
  prob : IsProbabilityMeasure P
  measurable : ∀ w, IsOrdinaryWord w → ∀ t, t₀ ≤ t → Measurable (Z w t)
  continuous : ∀ w, IsOrdinaryWord w → ∀ᵐ ω ∂P, ContinuousOn (fun t => Z w t ω) (Set.Ici t₀)
  fdd : ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ (m : ℕ) (ws : Fin m → TraceWord nT nI) (ts : Fin m → ℝ),
    (∀ l, IsOrdinaryWord (ws l) ∧ t₀ ≤ ts l) → ∀ Ψ : BoundedContinuousFunction (Fin m → ℂ) ℝ,
      Tendsto (fun n => ∫ ω, Ψ (fun l =>
          wordValue b E (k (φ n)) q (φ n) ⌊(φ n : ℝ) * ts l⌋₊ ω (ws l)) ∂growthPathLaw (φ n) b)
        atTop (𝓝 (∫ ω, Ψ (fun l => Z (ws l) (ts l) ω) ∂P))

/-- The full-source generator.
* `generator`: fixed `b`, bulk `E`, `t₀ > 0`; finitely many positive *homogeneous* sources on
  `[t₀,∞)` (transported after their last injection): tags born before `t₀`
  (`k_a(W) + 1 ≤ Wt₀` for all large `W`, normalized by `W`) and interval sources normalized by
  `W²` with tests supported in some `[s, t₀]`. Every joint critical limit (`IsWordLimit`) has
  the trace-word generator: for every ordinary trace polynomial `Φ`, `Φ(Z) - ∫𝒜Φ(Z)` is a martingale and
  `M_Φ² - ∫Γ(Φ)(Z)` is a martingale on `[t₀,∞)` (natural filtration of the ordinary words).
  The current `J` is a letter of every word, so the limit retains it.
* `tight`, a fact from the proof of the full-source stopping lemma, stated so that
  `generator` is not vacuous: for the same homogeneous families, every ordinary word and every
  `t₀ ≤ t₁ < T`, the word values `t ↦ Tr w(⌊Wt⌋)` are `C`-tight on `[t₁, T]` (tight at `t₁`,
  asymptotically small sup-modulus, as in `TransmissionGeneratorContract.tight`). Hence, by
  Prokhorov over the countably many ordinary words, joint critical limits `IsWordLimit` exist
  along subsequences.
* `moments`: `FullSourceMomentsContract`. -/
structure FullSourceGeneratorContract : Prop where
  generator : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ t₀ : ℝ, 0 < t₀ →
    ∀ (nT nI : ℕ) (q : Fin nI → ℝ → ℝ), (∀ a, ∃ s : ℝ, IsSourceTest s t₀ (q a)) →
    ∀ k : ℕ → Fin nT → ℕ, (∀ᶠ W in atTop, ∀ a, ((k W a + 1 : ℕ) : ℝ) ≤ W * t₀) →
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (Z : TraceWord nT nI → ℝ → Ω → ℂ),
      IsWordLimit b E k q t₀ P Z → ∀ Φ : TracePoly nT nI, IsOrdinaryPoly Φ →
      let obs : {w : TraceWord nT nI // IsOrdinaryWord w} → ℝ → Ω → ℂ := fun w => Z w.1
      let M : ℝ → ℝ → Ω → ℂ := fun s t ω =>
        MvPolynomial.eval (fun w => Z w t ω) Φ - MvPolynomial.eval (fun w => Z w s ω) Φ -
          ∫ u in s..t, MvPolynomial.eval (fun w => Z w u ω) (wordGenerator b E q u Φ)
      IsMartingaleIncrements P obs (Set.Ici t₀) M ∧
      IsMartingaleIncrements P obs (Set.Ici t₀) fun s t ω =>
        M s t ω ^ 2 - ∫ u in s..t, MvPolynomial.eval (fun w => Z w u ω) (wordCarre b E Φ)
  tight : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 → ∀ t₀ : ℝ, 0 < t₀ →
    ∀ (nT nI : ℕ) (q : Fin nI → ℝ → ℝ), (∀ a, ∃ s : ℝ, IsSourceTest s t₀ (q a)) →
    ∀ k : ℕ → Fin nT → ℕ, (∀ᶠ W in atTop, ∀ a, ((k W a + 1 : ℕ) : ℝ) ≤ W * t₀) →
    ∀ w : TraceWord nT nI, IsOrdinaryWord w → ∀ t₁ T : ℝ, t₀ ≤ t₁ → t₁ < T →
      (∀ θ : ℝ, 0 < θ → ∃ (M : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W →
        growthPathLaw W b {ω | M < ‖wordValue b E (k W) q W ⌊(W : ℝ) * t₁⌋₊ ω w‖} ≤
          ENNReal.ofReal θ) ∧
      (∀ η θ : ℝ, 0 < η → 0 < θ → ∃ δ : ℝ, 0 < δ ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
        growthPathLaw W b {ω | ∃ t ∈ Set.Icc t₁ T, ∃ t' ∈ Set.Icc t₁ T, |t - t'| ≤ δ ∧
          η < ‖wordValue b E (k W) q W ⌊(W : ℝ) * t⌋₊ ω w -
            wordValue b E (k W) q W ⌊(W : ℝ) * t'⌋₊ ω w‖} ≤ ENNReal.ofReal θ)
  moments : FullSourceMomentsContract

/-- The conditional increment formulas for trace polynomials, with summed errors.
* `summed`: every ordinary trace polynomial `Φ`, `0 < ε < T`, `K`
  first; then `C, W₀`; for `W ≥ W₀` and all tag birth indices `≥ εW`, the expected absolute
  errors of the first and second conditional increment formulas,
  `E|1{j<σ_K}(E_j[ΔΦ_j] - W⁻¹𝒜_{(j+1)/W}Φ)|` and `E|1{j<σ_K}(E_j[(ΔΦ_j)²] - W⁻¹Γ(Φ))|`,
  summed over the steps `εW ≤ j < TW` other than the tag births `j = k_a` (their increments are
  retained exactly), are at most `C(W^{-1/2} + W⁻¹)`. -/
structure ContractingWordsContract : Prop where
  recursion : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    (∃ s : ℂ, IsStationaryJet b E s) ∧ ∀ s : ℂ, IsStationaryJet b E s →
    ∀ (nT nI : ℕ) (q : Fin nI → ℝ → ℝ), IsIntervalTests q →
    ∀ (d : ℕ) (ε T K p : ℝ), 0 < ε → ε < T → 1 ≤ p →
    ∃ (C ρ : ℝ) (W₀ : ℕ), 0 ≤ ρ ∧ ρ < 1 ∧ ∀ W : ℕ, W₀ ≤ W →
      ∀ k : Fin nT → ℕ, (∀ a, ε * W ≤ k a) → ∀ j₀ : ℕ, ε * W ≤ j₀ → (∀ a, k a < j₀) →
      ∀ Zs : List (TraceWord nT nI), IsAdmittedProduct Zs → productDegree Zs ≤ d →
        1 ≤ unconjCount Zs + conjCount Zs →
      let μ := growthPathLaw W b
      let lam : ℂ := thetaStar b E s ^ unconjCount Zs * conj (thetaStar b E s) ^ conjCount Zs
      let Z : ℕ → GrowthPath W → ℂ := fun j ω => productValue b E k q W j ω Zs
      let A : ℕ → Set (GrowthPath W) := alive b E k q K ε W
      (∀ j : ℕ, j₀ ≤ j → ((j + 1 : ℕ) : ℝ) ≤ T * W → ∃ ξ : GrowthPath W → ℂ,
        Integrable ((A j).indicator ξ) μ ∧
        μ[(A j).indicator ξ | growthSigma W j] =ᵐ[μ] 0 ∧
        eLpNorm ((A j).indicator fun ω => Z (j + 1) ω - lam * Z j ω - ξ ω)
          (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (C / W) ∧
        eLpNorm ((A j).indicator ξ) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (C / Real.sqrt W)) ∧
      ∀ j : ℕ, j₀ ≤ j → (j : ℝ) ≤ T * W →
        eLpNorm ((A j).indicator (Z j)) (ENNReal.ofReal p) μ ≤
          ENNReal.ofReal (C * (ρ ^ (j - j₀) + 1 / Real.sqrt W))
  summed : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ (nT nI : ℕ) (q : Fin nI → ℝ → ℝ), IsIntervalTests q →
    ∀ Φ : TracePoly nT nI, IsOrdinaryPoly Φ → ∀ ε T K : ℝ, 0 < ε → ε < T →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ k : Fin nT → ℕ, (∀ a, ε * W ≤ k a) →
      let μ := growthPathLaw W b
      let A : ℕ → Set (GrowthPath W) := alive b E k q K ε W
      let F : ℕ → GrowthPath W → ℂ := fun j ω => polyValue b E k q W j ω Φ
      let steps := (Finset.range ⌊T * W⌋₊).filter fun j : ℕ => ε * W ≤ (j : ℝ) ∧ ∀ a, j ≠ k a
      (∑ j ∈ steps, ∫⁻ ω, ‖(A j).indicator (fun ω =>
          μ[(A j).indicator (fun ω => F (j + 1) ω - F j ω) | growthSigma W j] ω -
            (W : ℂ)⁻¹ * polyValue b E k q W j ω
              (wordGenerator b E q (((j + 1 : ℕ) : ℝ) / W) Φ)) ω‖ₑ ∂μ) ≤
          ENNReal.ofReal (C * (1 / Real.sqrt W + 1 / W)) ∧
      (∑ j ∈ steps, ∫⁻ ω, ‖(A j).indicator (fun ω =>
          μ[(A j).indicator (fun ω => (F (j + 1) ω - F j ω) ^ 2) | growthSigma W j] ω -
            (W : ℂ)⁻¹ * polyValue b E k q W j ω (wordCarre b E Φ)) ω‖ₑ ∂μ) ≤
          ENNReal.ofReal (C * (1 / Real.sqrt W + 1 / W))

/-- The full-source stopping lemma.
* `tail`: `∃ C_{ε,T}`, `∀ K > 0`:
  `limsup_W P{sup_{εW ≤ j ≤ TW}(Σ_a Tr Q_{a,j} + Tr|J_j|) > K} ≤ C/K`.
* `supMoments`: for every `p > 0`, `E[sup_{εW≤j≤TW} (Tr Q_{a,j})^p] ≤ C_p` for `W ≥ W₀`.
* `compensatorUI`: for every ordinary trace polynomial `Φ`, the total variations
  `Σ_{εW≤j<TW} W⁻¹|𝒜_{(j+1)/W}Φ(Z_j)|` and `Σ W⁻¹|Γ(Φ)(Z_j)|` of the finite-`W` drift and
  quadratic-variation compensators of the word generator and word covariance are uniformly
  integrable in `W ≥ W₀` (`∀ η > 0, ∃ M, sup_W E[X_W; X_W > M] ≤ η`).
* The fourth sentence ("the stops may be removed through increasing regular levels, retaining
  their exit values", a statement about the passage to the limit of stopped processes) is not
  stated here: it needs a process-level convergence vocabulary. -/
structure FullSourceStopsContract : Prop where
  tail : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ (nT nI : ℕ) (q : Fin nI → ℝ → ℝ), IsIntervalTests q → ∀ ε T : ℝ, 0 < ε → ε < T →
    ∃ C : ℝ, ∀ K : ℝ, 0 < K →
      limsup (fun W : ℕ => ⨆ k : Fin nT → ℕ, growthPathLaw W b {ω | ∃ j : ℕ, ε * W ≤ j ∧
          (j : ℝ) ≤ T * W ∧ K < traceLoad b E k q W j ω}) atTop ≤ ENNReal.ofReal (C / K)
  supMoments : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ (nT nI : ℕ) (q : Fin nI → ℝ → ℝ), IsIntervalTests q → ∀ ε T p : ℝ, 0 < ε → ε < T →
    0 < p → ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ (k : Fin nT → ℕ) (a : Fin nT ⊕ Fin nI),
      ∫⁻ ω, (⨆ (j : ℕ) (_ : ε * W ≤ j ∧ (j : ℝ) ≤ T * W), ‖sourceTrace b E k q W j ω a‖ₑ) ^ p
        ∂growthPathLaw W b ≤ ENNReal.ofReal C
  compensatorUI : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ (nT nI : ℕ) (q : Fin nI → ℝ → ℝ), IsIntervalTests q →
    ∀ Φ : TracePoly nT nI, IsOrdinaryPoly Φ → ∀ ε T η : ℝ, 0 < ε → ε < T → 0 < η →
    ∃ (M : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ k : Fin nT → ℕ,
      let steps := (Finset.range ⌊T * W⌋₊).filter fun j : ℕ => ε * W ≤ (j : ℝ)
      let drift : GrowthPath W → ℝ≥0∞ := fun ω => ∑ j ∈ steps, (W : ℝ≥0∞)⁻¹ *
        ‖polyValue b E k q W j ω (wordGenerator b E q (((j + 1 : ℕ) : ℝ) / W) Φ)‖ₑ
      let qv : GrowthPath W → ℝ≥0∞ := fun ω => ∑ j ∈ steps, (W : ℝ≥0∞)⁻¹ *
        ‖polyValue b E k q W j ω (wordCarre b E Φ)‖ₑ
      ∫⁻ ω, {ω | ENNReal.ofReal M < drift ω}.indicator drift ω ∂growthPathLaw W b ≤
          ENNReal.ofReal η ∧
        ∫⁻ ω, {ω | ENNReal.ofReal M < qv ω}.indicator qv ω ∂growthPathLaw W b ≤
          ENNReal.ofReal η

end BlockBand.Internal.Contracts.TransmissionStatements
