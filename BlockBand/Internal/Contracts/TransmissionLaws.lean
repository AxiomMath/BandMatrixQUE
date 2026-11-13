module

public import BlockBand.Internal.Contracts.TransmissionPath
public import BlockBand.SourceProcess.Stochastic.FiniteSource

/-!
# The transmission law, the source process and the complex source law

Statements of the critical limit of the transmission trace-measure processes and its dual
deletion transforms, of the limit of the positive Gaussian source transforms through finite
source models, of the rank-free coupling of source SDEs, and of the complex source law.

## Shape of the limit statements

* **Critical limit.** `W → ∞` along all widths, time `t ↔ ⌊Wt⌋` blocks. "Unique critical
  limit" = convergence of the whole sequence (so all subsequential limits agree).
* **Convergence of processes** (`IsTransmissionLimit`): convergence of all finite-dimensional
  distributions at positive times (bounded continuous tests on products of finite measures on
  `[0,1]` with the weak topology), a limit with continuous paths, and the asymptotic
  equicontinuity of `t ↦ ∫f dμ_W(t)` on each `[ε,T]`. Together these are equivalent to
  convergence in law in `D([ε,T], 𝓜_f[0,1])` to a process in `C([ε,T], 𝓜_f[0,1])`.
* **Explicit limit objects** are identified without constructing a solution operator: a value `v`
  is "the value of the construction" if (i) the construction exists and (ii) *every* realization
  gives `v` (`DualLawValue`, `FiniteSourceModelValue`, `ComplexModelValue`). Uniqueness in law of
  the constructions is part of the cited statements (the dual boundary lemma and the finite
  Gram law), so (ii) is not stronger than the paper; (i) prevents vacuity.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Internal.Contracts.TransmissionLaws

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.FiniteDriverIntegration
open scoped ENNReal NNReal ComplexConjugate ComplexOrder Matrix

/-!
## 1. The transmission limit
-/

/-- **`(P, μ)` is the critical limit of the transmission trace-measure processes** with
absorption profile `κ` at `(b, E)` (the first sentence of the transmission-law theorem):
* `measurable`, `continuous`: `μ(t)` is a random finite measure on `[0,1]` for `t > 0`, with
  continuous paths on `(0,∞)` (weak topology);
* `fdd`: for all positive times `τ_1,…,τ_k` the joint laws of `(μ_W(τ_i))_i` under the path law
  converge weakly to those of `(μ(τ_i))_i`;
* `modulus`: on every compact positive-time interval `[ε,T]`, for every continuous `f` on
  `[0,1]`, `lim_{δ↓0} limsup_W P(sup_{|t-t'| ≤ δ} |∫f dμ_W(t) - ∫f dμ_W(t')| > η) = 0`
  (written with explicit `θ, δ, W₀`). -/
structure IsTransmissionLimit (b E : ℝ) (κ : ℝ → ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (μ : ℝ → Ω → FiniteMeasure unitInterval) : Prop where
  prob : IsProbabilityMeasure P
  measurable : ∀ t, 0 < t → Measurable (μ t)
  continuous : ∀ᵐ ω ∂P, ContinuousOn (fun t => μ t ω) (Set.Ioi 0)
  fdd : ∀ (k : ℕ) (τ : Fin k → ℝ), (∀ i, 0 < τ i) →
    ∀ Φ : BoundedContinuousFunction (Fin k → FiniteMeasure unitInterval) ℝ,
      Tendsto (fun W : ℕ => ∫ ω, Φ (fun i => transmissionProcess b E κ W (τ i) ω)
          ∂growthPathLaw W b) atTop (𝓝 (∫ ω, Φ (fun i => μ (τ i) ω) ∂P))
  modulus : ∀ ε T : ℝ, 0 < ε → ∀ f : C(unitInterval, ℝ), ∀ η θ : ℝ, 0 < η → 0 < θ →
    ∃ δ : ℝ, 0 < δ ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      growthPathLaw W b {ω | ∃ t ∈ Set.Icc ε T, ∃ t' ∈ Set.Icc ε T, |t - t'| ≤ δ ∧
        η < |∫ x, f x ∂(transmissionProcess b E κ W t ω : Measure unitInterval) -
          ∫ x, f x ∂(transmissionProcess b E κ W t' ω : Measure unitInterval)|} ≤
        ENNReal.ofReal θ

/-- The dual deletion law started at `(x, y)` exists (on some filtered probability space). -/
def HasDualDeletionProcess (D0 : ℝ) {p : ℕ} (x y : Fin p → ℝ) : Prop :=
  ∃ (Ω : Type) (m : MeasurableSpace Ω) (𝓖 : Filtration ℝ≥0 m) (P : Measure Ω)
    (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ), IsDualDeletionProcess P 𝓖 D0 x y N X Y

/-- Every realization of the dual deletion law started at `(x, y)` gives the value `v` to
`E_{x,y}[exp(-∫_0^t h(t-s)R_s ds) 1{ζ ≤ t}]`. -/
def DualLawValue (E : ℝ) (κ : ℝ → ℝ) (t D0 : ℝ) {p : ℕ} (x y : Fin p → ℝ) (v : ℝ) : Prop :=
  ∀ (Ω : Type) (m : MeasurableSpace Ω) (𝓖 : Filtration ℝ≥0 m) (P : Measure Ω)
    (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ), IsDualDeletionProcess P 𝓖 D0 x y N X Y →
      dualTransform E κ t P N X Y = v

/-- The transmission-law theorem.
* `law`: for every admissible absorption profile `κ` (block added at step `r`
  carries `κ(r/W)/W²`; `κ ≡ 0`: homogeneous) the processes `μ_W` have a critical limit `μ`
  (`IsTransmissionLimit`: process convergence on compact positive-time intervals to a continuous
  process; uniqueness of its law follows from the convergence of the whole sequence), and its
  determining transforms are given by the dual law: for every `t > 0` and ordered
  parameters `(x, y)`, `E F_{x,y}(μ(t)) = E_{x,y}[exp(-∫_0^t h(t-s)R_s ds) 1{ζ ≤ t}]`, with
  `h = 4πρ(E)κ`, the dual being the conservative deletion law of the dual boundary lemma with
  generator `𝒟_p` (`D₀ = 2/(b(4-E²))`), which exists. Index convention: the block that makes
  the length `r` carries `κ(r/W)/W²`; the paper's `ε = κ(r/W)/W²` for the step `r → r+1`
  differs by one block, immaterial for continuous `κ`.
* `determining` ("its determining transforms"): every random finite
  measure on `[0,1]` whose transforms `E F_{x,y}` agree with those of `μ(t)` for all ordered
  `(x, y)` has the law of `μ(t)`.
* `fractional` (fractional transmission moments, `κ ≡ 0`): for `0 < p < 1` there is `C_p` with
  `limsup_W E Tr T_{⌊Wt⌋}^p ≤ C_p(1 + t⁻¹)` for all `t > 0`.
* `noMassAtZero` (`κ ≡ 0`): the limit has no trace mass at zero: `μ(t){0} = 0` a.s., `t > 0`.
* `expDecay` (`κ ≡ 0`): for `0 < q < 1` there are `C_q, c_q > 0` with
  `limsup_W E Tr T_{⌊Wt⌋}^q ≤ C_q e^{-c_q t}` for `t ≥ 2`. -/
structure TransmissionLawContract : Prop where
  law : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ κ : ℝ → ℝ, IsAbsorptionProfile κ →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
        (μ : ℝ → Ω → FiniteMeasure unitInterval),
        IsTransmissionLimit b E κ P μ ∧
        ∀ t : ℝ, 0 < t → ∀ (p : ℕ) (x y : Fin p → ℝ), IsRatioParameter x y →
          HasDualDeletionProcess (transportD0 b E) x y ∧
          DualLawValue E κ t (transportD0 b E) x y (∫ ω, transmissionRatio x y (μ t ω) ∂P)
  fractional : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ p : ℝ, 0 < p → p < 1 → ∃ C : ℝ, ∀ t : ℝ, 0 < t →
      limsup (fun W : ℕ => ∫⁻ ω, ENNReal.ofReal
          (fracTrace p (pathTransmission b E (fun _ => 0) W ⌊(W : ℝ) * t⌋₊ ω))
          ∂growthPathLaw W b) atTop ≤ ENNReal.ofReal (C * (1 + t⁻¹))
  noMassAtZero : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (μ : ℝ → Ω → FiniteMeasure unitInterval), IsTransmissionLimit b E (fun _ => 0) P μ →
      ∀ t : ℝ, 0 < t → ∀ᵐ ω ∂P, (μ t ω : Measure unitInterval) {0} = 0
  expDecay : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ q : ℝ, 0 < q → q < 1 → ∃ C c : ℝ, 0 < c ∧ ∀ t : ℝ, 2 ≤ t →
      limsup (fun W : ℕ => ∫⁻ ω, ENNReal.ofReal
          (fracTrace q (pathTransmission b E (fun _ => 0) W ⌊(W : ℝ) * t⌋₊ ω))
          ∂growthPathLaw W b) atTop ≤ ENNReal.ofReal (C * Real.exp (-(c * t)))
  determining : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ κ : ℝ → ℝ, IsAbsorptionProfile κ →
    ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (μ : ℝ → Ω → FiniteMeasure unitInterval), IsTransmissionLimit b E κ P μ →
    ∀ t : ℝ, 0 < t →
    ∀ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω')
      (ν : Ω' → FiniteMeasure unitInterval), IsProbabilityMeasure P' → Measurable ν →
      (∀ (p : ℕ) (x y : Fin p → ℝ), IsRatioParameter x y →
        ∫ ω, transmissionRatio x y (ν ω) ∂P' = ∫ ω, transmissionRatio x y (μ t ω) ∂P) →
      P'.map ν = P.map (μ t)
  fractionalHessian : ∀ p : ℝ, 0 < p → p < 1 → ∀ (n : ℕ) (A H : Matrix (Fin n) (Fin n) ℂ),
    A.PosDef → H.IsHermitian →
      deriv (deriv (fun τ : ℝ => fracTrace p (A + (τ : ℂ) • H))) 0 =
        -(p * Real.sin (Real.pi * p) / Real.pi) *
          ∫ s in Set.Ioi (0 : ℝ), s ^ (p - 1) *
            ((A + (s : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))⁻¹ * H *
              (A + (s : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))⁻¹ * H).trace.re
  jetGap : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    (∃ s : ℂ, IsStationaryJet b E s) ∧
      ∀ s : ℂ, IsStationaryJet b E s → ‖sigmaMinus b E s‖ < sigmaPlus b
  entryVariance : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI →
    ∃ d γ c : ℝ, 0 < d ∧ 0 < γ ∧ 0 < c ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ E ∈ bulkInterval κI, ∀ s : ℂ, IsStationaryJet b E s →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
        jetDistance0 b E X ≤ d → jetDistance1 b E s X ≤ d →
        conductanceOf (passiveTransmission b E X) ≤ γ * W →
        ∀ (u : Fin W → Fin W → ℂ) (t : Fin W → ℝ),
          IsOrthonormalEigenbasis (passiveTransmission b E X) u t →
          ∀ i j, t i ≤ 1 / 2 → t j ≤ 1 / 2 →
            c / W ≤ ∫ ω, ‖star (u i) ⬝ᵥ ((freshU b E X ω -
                matrixExpect (layerLaw W b .oneBlockOnePort) (freshU b E X)) *ᵥ u j)‖ ^ 2
              ∂layerLaw W b .oneBlockOnePort

/-!
## 2. Positive finite source models
-/

/-- The law of the random measure `μ(s)`: the transmission entrance at time `s`. -/
def entranceLaw {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : ℝ → Ω → FiniteMeasure unitInterval) (s : ℝ) : Measure (Measure unitInterval) :=
  P.map fun ω => (μ s ω : Measure unitInterval)

/-- A transmission sequence `t₁ ≥ t₂ ≥ ⋯` in `[0,1]` with `Σ t_i < ∞`. -/
def IsTransmissionSequence (t : ℕ → ℝ) : Prop :=
  Antitone t ∧ (∀ i, 0 ≤ t i ∧ t i ≤ 1) ∧ Summable t

/-- Its trace measure `Σ_i t_i δ_{t_i}`. -/
def seqTraceMeasure (t : ℕ → ℝ) : Measure unitInterval :=
  Measure.sum fun i => ENNReal.ofReal (t i) • Measure.dirac (toUnit (t i))

/-- Gram column indices: two current columns per retained mode (`Fin K × Fin 2`, cap `K`) and
the probe columns `π`. -/
abbrev SrcCol (K : ℕ) (π : Type*) := (Fin K × Fin 2) ⊕ π

/-- A Gram state `(M, B) = (V*V, V*PV)`. -/
abbrev GramState (c : Type*) := Matrix c c ℂ × Matrix c c ℂ

/-- The signature `𝖣`: `+1, -1` on the two current columns of each mode, `0` on probes. -/
def srcSignature (K : ℕ) (π : Type*) [DecidableEq π] : Matrix (SrcCol K π) (SrcCol K π) ℂ :=
  Matrix.diagonal fun c => match c with
    | Sum.inl (_, σ) => if σ = 0 then 1 else -1
    | Sum.inr _ => 0

/-- Unit eigenvectors `e_±` of `P_i' - P_i` (eigenvalues `±√t`) in the canonical two-dimensional
block `(near, far)` of mode `t`:
`e_+ = (√(1-√t), √(1+√t))/√2`, `e_- = (√(1+√t), -√(1-√t))/√2`. -/
def modeVector (t : ℝ) (σ : Fin 2) : Fin 2 → ℂ :=
  if σ = 0 then
    ![((Real.sqrt (1 - Real.sqrt t) / Real.sqrt 2 : ℝ) : ℂ),
      ((Real.sqrt (1 + Real.sqrt t) / Real.sqrt 2 : ℝ) : ℂ)]
  else
    ![((Real.sqrt (1 + Real.sqrt t) / Real.sqrt 2 : ℝ) : ℂ),
      ((-(Real.sqrt (1 - Real.sqrt t) / Real.sqrt 2) : ℝ) : ℂ)]

/-- The near projection `⊕_i P_i` of the canonical pairs (`P_i = diag(1, 0)`). -/
def modeProjection (K : ℕ) : Matrix (Fin K × Fin 2) (Fin K × Fin 2) ℂ :=
  Matrix.diagonal fun x => if x.2 = 0 then 1 else 0

/-- The initial frame at time `s`: retain the modes `t_k > h²` among the first `K` (the current
cutoff and count cap); current columns `t_k^{1/4} e_±(t_k)` (norm `t_k^{1/4}`, so that
`V𝖣V* = ⊕(P_i' - P_i)`); probe columns zero. -/
def initialFrame (K : ℕ) (π : Type*) (t : ℕ → ℝ) (h : ℝ) :
    Matrix (Fin K × Fin 2) (SrcCol K π) ℂ :=
  fun x c => match c with
    | Sum.inl (k, σ) => if x.1 = k ∧ h ^ 2 < t k.val then
        ((t k.val ^ (1 / 4 : ℝ) : ℝ) : ℂ) * modeVector (t k.val) σ x.2 else 0
    | Sum.inr _ => 0

/-- The initial Gram state `gramPair (⊕P_i) V₀`. -/
def initialGram (K : ℕ) (π : Type*) (t : ℕ → ℝ) (h : ℝ) : GramState (SrcCol K π) :=
  gramPair (modeProjection K) (initialFrame K π t h)

/-- Gram jumps of near probe births: probe `i` born at (model) time `τ_i` as a new perpendicular
near vector of squared norm `v_i`: `M_ii` and `B_ii` jump by `v_i`, zero cross entries. -/
def birthJump {K : ℕ} {π : Type*} [Fintype π] [DecidableEq π] (τ v : π → ℝ) (t : ℝ) :
    GramState (SrcCol K π) :=
  ∑ i, if τ i ≤ t then
    (((v i : ℝ) : ℂ) • Matrix.single (Sum.inr i) (Sum.inr i) 1,
      ((v i : ℝ) : ℂ) • Matrix.single (Sum.inr i) (Sum.inr i) 1) else 0

/-- Continuous part of a Gram coordinate: `(G - J)_e(t) - (G - J)_e(0) - ∫_0^t b_e(G_s) ds`. -/
def bornCompensated {Ω c : Type*} [Fintype c] [DecidableEq c] (D0 : ℝ) (D : Matrix c c ℂ)
    (G J : ℝ≥0 → Ω → GramState c) (e : Fin 2 × c × c) (t : ℝ≥0) (ω : Ω) : ℂ :=
  gramEntry e (G t ω - J t ω) - gramEntry e (G 0 ω - J 0 ω) -
    ∫ s in Set.Ioc (0 : ℝ) t, gramDriftEntry D0 D e (G s.toNNReal ω)

/-- **The Gram law of the finite source SDE with births** (the finite Gram law, completed by the
probe births): `G - J` is continuous, `J` is the `𝓖₀`-measurable birth
jump process, `G` is feasible, and for every trace level the compensated continuous coordinates
and their products compensated by the Gram covariance are martingales (as in
`IsGramMartingaleSolution`). -/
structure IsBornGramSolution {Ω c : Type*} [MeasurableSpace Ω] [Fintype c] [DecidableEq c]
    (Q : Measure Ω) (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) (D0 : ℝ)
    (D : Matrix c c ℂ) (J G : ℝ≥0 → Ω → GramState c) : Prop where
  adapted : ∀ t, StronglyMeasurable[𝓖 t] (G t)
  jump : ∀ t, StronglyMeasurable[𝓖 0] (J t)
  continuous : ∀ᵐ ω ∂Q, Continuous fun t => G t ω - J t ω
  feasible : ∀ᵐ ω ∂Q, ∀ t, GramFeasible D (G t ω)
  drift : ∀ (K : ℝ) (e : Fin 2 × c × c), ∃ N : ℝ≥0 → Ω → ℂ, Martingale N 𝓖 Q ∧ ∀ t,
    N t =ᵐ[Q] stoppedProcess (bornCompensated D0 D G J e) (gramTraceStop G K) t
  bracket : ∀ (K : ℝ) (e e' : Fin 2 × c × c), ∃ N : ℝ≥0 → Ω → ℂ, Martingale N 𝓖 Q ∧ ∀ t,
    N t =ᵐ[Q] stoppedProcess (fun t ω => bornCompensated D0 D G J e t ω *
        bornCompensated D0 D G J e' t ω -
        ∫ s in Set.Ioc (0 : ℝ) t, gramCovEntry D0 D e e' (G s.toNNReal ω))
      (gramTraceStop G K) t

/-- Total mass `m = ∫_s^T q` of a source test (continuum of `m = Σ_j q_j/W`). -/
def sourceMass (s T : ℝ) (q : ℝ → ℝ) : ℝ := ∫ x in Set.Icc s T, q x

/-- Law of one sampled source location: density `q/m` on `[s,T]` (continuum of the sampling
probabilities `q_j/(Wm)`); a zero-mass test has zero births (any location). -/
def birthTimeLaw (s T : ℝ) (q : ℝ → ℝ) : Measure ℝ :=
  if 0 < sourceMass s T q then
    (volume.restrict (Set.Icc s T)).withDensity fun x => ENNReal.ofReal (q x / sourceMass s T q)
  else Measure.dirac s

/-- **The positive finite source model** of the source-process theorem at current cutoff `h` (retain
`t_i > h²`), count cap `K` and `M` sampled locations per test, started at the source-free time
`s` (model time `u ↔` physical time `s + u`): on a filtered probability space,
* the entrance: a `𝓖₀`-measurable transmission sequence whose trace measure has the law of
  `μ(s)` (`entrance = entranceLaw P μ s`);
* independent `𝓖₀`-measurable sampled locations `τ_{a,k}`, `k < M`, i.i.d. with density
  `q_a/m_a` on `[s,T]`;
* the Gram law of the finite source SDE (`D₀ = 2/(b(4-E²))`, signature `srcSignature`) started
  from the canonical frame, with the near probe birth of squared norm `d_* m_a/M` at
  `τ_{a,k}`. -/
structure IsFiniteSourceModel (b E s T : ℝ) {p : ℕ} (q : Fin p → ℝ → ℝ) (h : ℝ) (K M : ℕ)
    (entrance : Measure (Measure unitInterval)) {Ω : Type*} [MeasurableSpace Ω]
    (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) (Q : Measure Ω)
    (tseq : Ω → ℕ → ℝ) (τ : Ω → Fin p × Fin M → ℝ)
    (G : ℝ≥0 → Ω → GramState (SrcCol K (Fin p × Fin M))) : Prop where
  prob : IsProbabilityMeasure Q
  entrance_measurable : Measurable[𝓖 0] tseq
  entrance_sequence : ∀ᵐ ω ∂Q, IsTransmissionSequence (tseq ω)
  entrance_law : Q.map (fun ω => seqTraceMeasure (tseq ω)) = entrance
  births_measurable : Measurable[𝓖 0] τ
  births_law : Q.map τ = Measure.pi fun i : Fin p × Fin M => birthTimeLaw s T (q i.1)
  independent : IndepFun tseq τ Q
  initial : ∀ᵐ ω ∂Q, G 0 ω = initialGram K (Fin p × Fin M) (tseq ω) h
  solution : IsBornGramSolution Q 𝓖 (transportD0 b E) (srcSignature K (Fin p × Fin M))
    (fun t ω => birthJump (fun i => τ ω i - s) (fun i => dStar b * sourceMass s T (q i.1) / M)
      (t : ℝ)) G

/-- The probe block of a Gram-indexed matrix. -/
def probeBlock {K : ℕ} {π : Type*} (A : Matrix (SrcCol K π) (SrcCol K π) ℂ) : Matrix π π ℂ :=
  fun i j => A (Sum.inr i) (Sum.inr j)

/-- The bounded Gaussian source transform of the sampled finite model:
`Π_j det(I + Σ_a a_{j,a} \widehat Q_a)⁻¹ = Π_j det(I + diag(a_j) M_pr)⁻¹` (Sylvester), where
`\widehat Q_a` is the sum of the final rank-one matrices of the probes of test `a`. -/
def sampledTransformValue {K p M J : ℕ} (a : Fin J → Fin p → ℝ)
    (G : GramState (SrcCol K (Fin p × Fin M))) : ℝ :=
  ∏ j, ((1 + Matrix.diagonal (fun i : Fin p × Fin M => (a j i.1 : ℂ)) * probeBlock G.1).det⁻¹).re

/-- `v` is the transform value of the finite model at `(h, K, M)`: a model exists and every
model gives `v` at the final time `T`. -/
def FiniteSourceModelValue (b E s T : ℝ) {p : ℕ} (q : Fin p → ℝ → ℝ) (h : ℝ) (K M : ℕ)
    (entrance : Measure (Measure unitInterval)) {J : ℕ} (a : Fin J → Fin p → ℝ) (v : ℝ) :
    Prop :=
  (∃ (Ω : Type) (m : MeasurableSpace Ω) (𝓖 : Filtration ℝ≥0 m) (Q : Measure Ω)
      (tseq : Ω → ℕ → ℝ) (τ : Ω → Fin p × Fin M → ℝ)
      (G : ℝ≥0 → Ω → GramState (SrcCol K (Fin p × Fin M))),
      IsFiniteSourceModel b E s T q h K M entrance 𝓖 Q tseq τ G) ∧
  ∀ (Ω : Type) (m : MeasurableSpace Ω) (𝓖 : Filtration ℝ≥0 m) (Q : Measure Ω)
    (tseq : Ω → ℕ → ℝ) (τ : Ω → Fin p × Fin M → ℝ)
    (G : ℝ≥0 → Ω → GramState (SrcCol K (Fin p × Fin M))),
    IsFiniteSourceModel b E s T q h K M entrance 𝓖 Q tseq τ G →
      ∫ ω, sampledTransformValue a (G (T - s).toNNReal ω) ∂Q = v

/-- The order of limits of the source-process theorem: first the count cap `K → ∞` and the current
cutoff `h ↓ 0` (along every sequence: "independent of the cutoff sequence"), then `M → ∞`;
the result is `L`. -/
def IteratedCutoffLimit (Φ : ℕ → ℝ → ℕ → ℝ) (L : ℝ) : Prop :=
  ∃ (Λ : ℝ → ℕ → ℝ) (Λ' : ℕ → ℝ),
    (∀ h M, 0 < h → 0 < M → Tendsto (fun K => Φ K h M) atTop (𝓝 (Λ h M))) ∧
    (∀ M, 0 < M → Tendsto (fun h => Λ h M) (𝓝[>] 0) (𝓝 (Λ' M))) ∧
    Tendsto Λ' atTop (𝓝 L)

section RankFree

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

/-- Squared Hilbert–Schmidt norm `Σ |V_ij|²`. -/
def hsSq {ι c : Type*} [Fintype ι] [Fintype c] (V : Matrix ι c ℂ) : ℝ :=
  ∑ i, ∑ j, ‖V i j‖ ^ 2

/-- The shared-birth jump of a frame: `J_b(t) = Σ_k 1{τ_k ≤ t} w_k e_{col_k}ᵀ` (birth `k` puts the
vector `w_k` into the previously zero column `col_k` at time `τ_k`). -/
def frameBirthJump {Ω ι c : Type*} [DecidableEq c] {nb : ℕ} (τ : Fin nb → Ω → ℝ≥0)
    (col : Fin nb → c) (w : Fin nb → Ω → ι → ℂ) (t : ℝ≥0) (x : Ω) : Matrix ι c ℂ :=
  ∑ k, if τ k x ≤ t then Matrix.of (fun i j => if j = col k then w k x i else 0) else 0

/-- A born solution of the finite source SDE: `X - J_b` is an Itô process whose drift and
diffusion are the source coefficients evaluated at `X` (births are jumps, the SDE runs between
them), and `X₀ = ξ`. With `J_b = 0` this is `IsSDESolution`. -/
def IsBornSDESolution {ι c S : Type*} [Fintype ι] [DecidableEq ι] [Fintype c] [DecidableEq c]
    [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ] (D0 : ℝ) (Naux : ℕ)
    (P : Matrix ι ι ℂ) (D : Matrix c c ℂ) (ξ : DriverSample S (SourceNoise ι) → Matrix ι c ℂ)
    (Jb X : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix ι c ℂ) : Prop :=
  IsNativeItoProcess μ (fun t x => X t x - Jb t x) (fun t x => sourceDrift D0 Naux P (X t x))
      (fun a t x => sourceDiffusion D0 P D a (X t x)) ∧
    ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, X 0 x = ξ x

/-- **Rank-free coupling**, with finitely many shared births. Two solutions of the finite source
SDE in a common padded space (same near projection
`P`, same signature `𝖣`, same driving noise `Z`), constrained `𝓖₀`-measurable initial frames
`ξ₁, ξ₂`, and `n_b` **shared births**: birth `k` happens at a stopping time `τ_k`;
its vector `w_k` is `𝓕_{τ_k}`-measurable, near (`Pw_k = w_k`, "in unused near dimensions"), of
deterministic squared norm `β_k`, and perpendicular to every other column of both frames at
`τ_k` ("perpendicular to both old frames"); it enters the same column `col_k` of both frames,
the columns `col_k` being distinct, of zero signature (probe columns) and zero in `ξ₁, ξ₂`.
Conclusion: for all `K, u > 0`, `T ≥ 0`, with `X = ‖V₁ - V₂‖²_HS`, `R = ‖V₁‖²_HS + ‖V₂‖²_HS`,
`B_birth = Σ_k β_k`,
`P{sup_{t ≤ T} X_t > u} ≤ (E R₀ + 2B_birth)/K + e^{D₀K²T/2} E X₀/u`.
No dependence on the dimension or the number of retained modes. -/
def RankFreeCoupling : Prop :=
  ∀ (ι c S : Type) [Fintype ι] [DecidableEq ι] [Fintype c] [DecidableEq c] [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (D0 : ℝ) (Naux : ℕ) (P : Matrix ι ι ℂ)
    (D : Matrix c c ℂ), 0 < D0 → IsNearProjection P Naux → IsSignature D →
  ∀ ξ₁ ξ₂ : DriverSample S (SourceNoise ι) → Matrix ι c ℂ,
    StronglyMeasurable[driverAugmented (κ := SourceNoise ι) μ 0] ξ₁ →
    StronglyMeasurable[driverAugmented (κ := SourceNoise ι) μ 0] ξ₂ →
    (∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, TwoProjection P D (ξ₁ x)) →
    (∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, TwoProjection P D (ξ₂ x)) →
  ∀ (nb : ℕ) (τ : Fin nb → DriverSample S (SourceNoise ι) → ℝ≥0) (col : Fin nb → c)
    (w : Fin nb → DriverSample S (SourceNoise ι) → ι → ℂ) (β : Fin nb → ℝ)
    (hτ : ∀ k, IsStoppingTime (driverAugmented (κ := SourceNoise ι) μ)
      (fun x => ((τ k x : ℝ≥0) : WithTop ℝ≥0))),
    (∀ k, StronglyMeasurable[(hτ k).measurableSpace] (w k)) →
    Function.Injective col → (∀ k j, D (col k) j = 0 ∧ D j (col k) = 0) →
    (∀ k, ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ i, ξ₁ x i (col k) = 0 ∧ ξ₂ x i (col k) = 0) →
    (∀ k, ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ,
      P *ᵥ w k x = w k x ∧ ∑ i, ‖w k x i‖ ^ 2 = β k) →
  ∀ X₁ X₂ : ℝ≥0 → DriverSample S (SourceNoise ι) → Matrix ι c ℂ,
    IsBornSDESolution μ D0 Naux P D ξ₁ (frameBirthJump τ col w) X₁ →
    IsBornSDESolution μ D0 Naux P D ξ₂ (frameBirthJump τ col w) X₂ →
    (∀ k, ∀ᵐ x ∂driverLaw (κ := SourceNoise ι) μ, ∀ j, j ≠ col k →
      (∑ i, conj (X₁ (τ k x) x i j) * w k x i = 0) ∧
        ∑ i, conj (X₂ (τ k x) x i j) * w k x i = 0) →
  ∀ K u T : ℝ, 0 < K → 0 < u → 0 ≤ T →
    driverLaw (κ := SourceNoise ι) μ
        {x | ∃ t : ℝ≥0, (t : ℝ) ≤ T ∧ u < hsSq (X₁ t x - X₂ t x)} ≤
      ((∫⁻ x, ENNReal.ofReal (hsSq (ξ₁ x) + hsSq (ξ₂ x)) ∂driverLaw (κ := SourceNoise ι) μ) +
            ENNReal.ofReal (2 * ∑ k, β k)) / ENNReal.ofReal K +
        ENNReal.ofReal (Real.exp (D0 * K ^ 2 * T / 2)) *
          (∫⁻ x, ENNReal.ofReal (hsSq (ξ₁ x - ξ₂ x)) ∂driverLaw (κ := SourceNoise ι) μ) /
          ENNReal.ofReal u

end RankFree

/-- The source-process theorem.
* `limit`: for `0 < s < T` and tests supported in `[s,T]` the transforms converge
  as `W → ∞` to `L` (unique critical limit), and `L` is the value of the positive construction:
  for some critical transmission limit `(P, μ)` at `κ ≡ 0` (whose law at `s` is the entrance),
  the finite-model values `Φ(K, h, M)` (`FiniteSourceModelValue`) converge to `L` when first
  `K → ∞`, `h ↓ 0` (current cutoff removed, along every sequence) and then `M → ∞`. Positivity
  and consistency under deleting tests/probes are properties of this construction.
* `restore`: for tests supported in `[0,T]`, the transforms converge, and the limit
  is the `s ↓ 0` limit of the limits for the truncated tests `q_a 1_{[s,T]}`. -/
structure SourceProcessContract : Prop where
  limit : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ s T : ℝ, 0 < s → s < T → ∀ (p : ℕ) (q : Fin p → ℝ → ℝ), (∀ i, IsSourceTest s T (q i)) →
    ∀ (J : ℕ) (a : Fin J → Fin p → ℝ), (∀ j i, 0 ≤ a j i) →
      ∃ L : ℝ, Tendsto (fun W => sourceTransform b E T q a W) atTop (𝓝 L) ∧
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
          (μ : ℝ → Ω → FiniteMeasure unitInterval), IsTransmissionLimit b E (fun _ => 0) P μ ∧
          ∃ Φ : ℕ → ℝ → ℕ → ℝ,
            (∀ K h M, 0 < h → 0 < M →
              FiniteSourceModelValue b E s T q h K M (entranceLaw P μ s) a (Φ K h M)) ∧
            IteratedCutoffLimit Φ L
  restore : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ T : ℝ, 0 < T → ∀ (p : ℕ) (q : Fin p → ℝ → ℝ), (∀ i, IsSourceTest 0 T (q i)) →
    ∀ (J : ℕ) (a : Fin J → Fin p → ℝ), (∀ j i, 0 ≤ a j i) →
      ∃ L : ℝ, Tendsto (fun W => sourceTransform b E T q a W) atTop (𝓝 L) ∧
        ∃ Ls : ℝ → ℝ, (∀ s, 0 < s → s < T →
            Tendsto (fun W => sourceTransform b E T (fun i => Set.indicator (Set.Icc s T) (q i))
              a W) atTop (𝓝 (Ls s))) ∧
          Tendsto Ls (𝓝[>] 0) (𝓝 L)
  rankFreeCoupling : RankFreeCoupling

/-!
## 3. Complex finite source models
-/

/-- The joint source data `(𝒦, M_pr, B_pr, J_pr)` as a point of a finite-dimensional space. -/
abbrev SourceData (np : ℕ) := Fin 4 → Matrix (Fin np) (Fin np) ℂ

/-- `𝒦` births: at a birth of mass `m_j` append the diagonal entry `a m_j`, zero cross entries. -/
def kBirthJump (E : ℝ) {np : ℕ} (τ m : Fin np → ℝ) (t : ℝ) : Matrix (Fin np) (Fin np) ℂ :=
  ∑ j, if τ j ≤ t then (matchedA E * (m j : ℂ)) • Matrix.single j j 1 else 0

/-- Continuous part of a `𝒦` coordinate. -/
def kCompensated {Ω π : Type*} (Kc JK : ℝ≥0 → Ω → Matrix π π ℂ) (i j : π) (t : ℝ≥0) (ω : Ω) :
    ℂ :=
  (Kc t ω - JK t ω) i j - (Kc 0 ω - JK 0 ω) i j

/-- **The complex source equation** `d𝒦 = -2iη V_pr* dA V_pr`, as a
martingale problem coupled to the Gram process `G` (probe columns `Sum.inr`): `𝒦 - J_𝒦` is
continuous, driftless, with the brackets of `dA` (`E|dZ_ij|² = 2dt`):
`d𝒦_ij d𝒦_kl = 0`, `d𝒦_ij d\bar𝒦_kl = 2η²D₀ B_ik (C₀)_lj dt`,
`d𝒦_ij dM_kl = -iηD₀ B_il (C₀)_kj dt`, `d𝒦_ij dB_kl = -iηD₀ B_il (C₁*)_kj dt`
("all cross brackets with Gram coordinates come from that same `dA`"), stopped at trace
levels. -/
structure IsComplexSourceExtension {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) (b E : ℝ) {K : ℕ} {π : Type*}
    [Fintype π] [DecidableEq π] (D : Matrix (SrcCol K π) (SrcCol K π) ℂ)
    (J G : ℝ≥0 → Ω → GramState (SrcCol K π)) (JK Kc : ℝ≥0 → Ω → Matrix π π ℂ) : Prop where
  adapted : ∀ t, StronglyMeasurable[𝓖 t] (Kc t)
  jump : ∀ t, StronglyMeasurable[𝓖 0] (JK t)
  continuous : ∀ᵐ ω ∂Q, Continuous fun t => Kc t ω - JK t ω
  martingale : ∀ (L : ℝ) (i j : π), ∃ N : ℝ≥0 → Ω → ℂ, Martingale N 𝓖 Q ∧ ∀ t,
    N t =ᵐ[Q] stoppedProcess (kCompensated Kc JK i j) (gramTraceStop G L) t
  holomorphic : ∀ (L : ℝ) (i j k l : π), ∃ N : ℝ≥0 → Ω → ℂ, Martingale N 𝓖 Q ∧ ∀ t,
    N t =ᵐ[Q] stoppedProcess (fun t ω => kCompensated Kc JK i j t ω * kCompensated Kc JK k l t ω)
      (gramTraceStop G L) t
  antiholomorphic : ∀ (L : ℝ) (i j k l : π), ∃ N : ℝ≥0 → Ω → ℂ, Martingale N 𝓖 Q ∧ ∀ t,
    N t =ᵐ[Q] stoppedProcess (fun t ω => kCompensated Kc JK i j t ω *
        conj (kCompensated Kc JK k l t ω) -
        ∫ s in Set.Ioc (0 : ℝ) t, ((2 * etaZ b E ^ 2 * transportD0 b E : ℝ) : ℂ) *
          (G s.toNNReal ω).2 (Sum.inr i) (Sum.inr k) *
          gramC0 (G s.toNNReal ω).1 (G s.toNNReal ω).2 D (Sum.inr l) (Sum.inr j))
      (gramTraceStop G L) t
  crossM : ∀ (L : ℝ) (i j : π) (k l : SrcCol K π), ∃ N : ℝ≥0 → Ω → ℂ, Martingale N 𝓖 Q ∧ ∀ t,
    N t =ᵐ[Q] stoppedProcess (fun t ω => kCompensated Kc JK i j t ω *
        bornCompensated (transportD0 b E) D G J (0, k, l) t ω -
        ∫ s in Set.Ioc (0 : ℝ) t, -(Complex.I * ((etaZ b E * transportD0 b E : ℝ) : ℂ)) *
          (G s.toNNReal ω).2 (Sum.inr i) l *
          gramC0 (G s.toNNReal ω).1 (G s.toNNReal ω).2 D k (Sum.inr j))
      (gramTraceStop G L) t
  crossB : ∀ (L : ℝ) (i j : π) (k l : SrcCol K π), ∃ N : ℝ≥0 → Ω → ℂ, Martingale N 𝓖 Q ∧ ∀ t,
    N t =ᵐ[Q] stoppedProcess (fun t ω => kCompensated Kc JK i j t ω *
        bornCompensated (transportD0 b E) D G J (1, k, l) t ω -
        ∫ s in Set.Ioc (0 : ℝ) t, -(Complex.I * ((etaZ b E * transportD0 b E : ℝ) : ℂ)) *
          (G s.toNNReal ω).2 (Sum.inr i) l *
          (gramC1 (G s.toNNReal ω).1 (G s.toNNReal ω).2 D)ᴴ k (Sum.inr j))
      (gramTraceStop G L) t

/-- **The complex finite source model** of the complex source law at cutoff `h`, cap `K`,
started at a source-free time `s` below all births: the entrance as in `IsFiniteSourceModel`,
the Gram law of the finite source SDE with a near birth of squared norm `d_* m_j` at `τ_j`, and
the complex source equation with the birth entry `a m_j` (`𝒦(s) = 0`: no probes yet). -/
structure IsFiniteComplexSourceModel (b E s : ℝ) {np : ℕ} (τ m : Fin np → ℝ) (h : ℝ) (K : ℕ)
    (entrance : Measure (Measure unitInterval)) {Ω : Type*} [MeasurableSpace Ω]
    (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)) (Q : Measure Ω)
    (tseq : Ω → ℕ → ℝ) (G : ℝ≥0 → Ω → GramState (SrcCol K (Fin np)))
    (Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ) : Prop where
  prob : IsProbabilityMeasure Q
  entrance_measurable : Measurable[𝓖 0] tseq
  entrance_sequence : ∀ᵐ ω ∂Q, IsTransmissionSequence (tseq ω)
  entrance_law : Q.map (fun ω => seqTraceMeasure (tseq ω)) = entrance
  initial : ∀ᵐ ω ∂Q, G 0 ω = initialGram K (Fin np) (tseq ω) h ∧ Kc 0 ω = 0
  solution : IsBornGramSolution Q 𝓖 (transportD0 b E) (srcSignature K (Fin np))
    (fun t _ => birthJump (fun j => τ j - s) (fun j => dStar b * m j) (t : ℝ)) G
  complex : IsComplexSourceExtension Q 𝓖 b E (srcSignature K (Fin np))
    (fun t _ => birthJump (fun j => τ j - s) (fun j => dStar b * m j) (t : ℝ)) G
    (fun t _ => kBirthJump E (fun j => τ j - s) m (t : ℝ)) Kc

/-- The model's source data `(𝒦, M_pr, B_pr, (M𝖣M)_pr)`; `(M𝖣M)_pr = V_pr*JV_pr`. -/
def modelSourceData {K np : ℕ} (D : Matrix (SrcCol K (Fin np)) (SrcCol K (Fin np)) ℂ)
    (Kc : Matrix (Fin np) (Fin np) ℂ) (G : GramState (SrcCol K (Fin np))) : SourceData np :=
  ![Kc, probeBlock G.1, probeBlock G.2, probeBlock (G.1 * D * G.1)]

/-- `v` is the value of the bounded test `Φ` under the complex finite model at `(h, K)` at the
final time `T`: a model exists and every model gives `v`. -/
def ComplexModelValue (b E s T : ℝ) {np : ℕ} (τ m : Fin np → ℝ) (h : ℝ) (K : ℕ)
    (entrance : Measure (Measure unitInterval)) (Φ : BoundedContinuousFunction (SourceData np) ℝ)
    (v : ℝ) : Prop :=
  (∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (𝓖 : Filtration ℝ≥0 mΩ) (Q : Measure Ω)
      (tseq : Ω → ℕ → ℝ) (G : ℝ≥0 → Ω → GramState (SrcCol K (Fin np)))
      (Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ),
      IsFiniteComplexSourceModel b E s τ m h K entrance 𝓖 Q tseq G Kc) ∧
  ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (𝓖 : Filtration ℝ≥0 mΩ) (Q : Measure Ω)
    (tseq : Ω → ℕ → ℝ) (G : ℝ≥0 → Ω → GramState (SrcCol K (Fin np)))
    (Kc : ℝ≥0 → Ω → Matrix (Fin np) (Fin np) ℂ),
    IsFiniteComplexSourceModel b E s τ m h K entrance 𝓖 Q tseq G Kc →
      ∫ ω, Φ (modelSourceData (srcSignature K (Fin np)) (Kc (T - s).toNNReal ω)
        (G (T - s).toNNReal ω)) ∂Q = v

/-- `ν` is the critical limit of the joint law of `(𝒦, M_pr, B_pr, J_pr)` at final time
`T` for tags of masses `m_j` born at `τ_j` (convergence against all bounded continuous tests). -/
def IsComplexSourceLimit (b E T : ℝ) {np : ℕ} (τ m : Fin np → ℝ) (ν : Measure (SourceData np)) :
    Prop :=
  IsProbabilityMeasure ν ∧ ∀ Φ : BoundedContinuousFunction (SourceData np) ℝ,
    Tendsto (fun W : ℕ => ∫ x, Φ (complexSourceData b E W ⌊(W : ℝ) * T⌋₊ τ m x)
      ∂probedPathLaw W np b) atTop (𝓝 (∫ y, Φ y ∂ν))

/-- Sum of `p`-th moduli of all entries of the source data. -/
def sourceDataMoment {np : ℕ} (p : ℝ) (y : SourceData np) : ℝ :=
  ∑ r, ∑ i, ∑ j, ‖y r i j‖ ^ p

/-- A normalized tag column `ξ = √(m/W) ι_k g` on path position `k`. -/
def tagVector (W n : ℕ) (k : Fin n) (m : ℝ) (g : Fin W → ℂ) : Fin n × Fin W → ℂ :=
  fun x => if x.1 = k then ((Real.sqrt (m / W) : ℝ) : ℂ) * g x.2 else 0

/-- `A_Q = W⁻² Q^{1/2} G Q^{1/2}`, `Q = diag(q_k I_W)`. -/
def extendedSourceMatrix (b E : ℝ) (W n : ℕ) (q : Fin n → ℝ) (ω : GrowthPath W) :
    Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ :=
  ((((W : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) •
    (Matrix.diagonal (fun x : Fin n × Fin W => ((Real.sqrt (q x.1) : ℝ) : ℂ)) *
      (fullInverse b E W n ω).toBlocks₁₁ *
      Matrix.diagonal (fun x : Fin n × Fin W => ((Real.sqrt (q x.1) : ℝ) : ℂ)))

/-- The complex source law.
* `limit`: the joint law of `(𝒦, M_pr, B_pr, J_pr)` converges (unique critical
  limit `ν`), and `ν` is the positive construction: for some critical transmission limit
  `(P, μ)` at `κ ≡ 0`, for every source-free start `0 < s < min τ_j` and every bounded
  continuous test `Φ`, the complex finite-model values (`ComplexModelValue`, births `d_*m_j` in
  the Gram and `a m_j` in `𝒦`) converge to `∫Φ dν` when first `K → ∞` and then `h ↓ 0`
  ("completed as in the source-process theorem").
* `moments`: all fixed source moments of the limit are bounded on
  bounded time intervals: for `p ≥ 1` and `T₀` there is `C` with `E_ν Σ|entries|^p ≤ C` for every
  final time `T ≤ T₀` (`T > max τ_j`). -/
structure ComplexSourceLawContract : Prop where
  limit : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ (np : ℕ) (τ m : Fin np → ℝ), Function.Injective τ → (∀ j, 0 < τ j) → (∀ j, 0 ≤ m j) →
    ∀ T : ℝ, (∀ j, τ j < T) →
      ∃ ν : Measure (SourceData np), IsComplexSourceLimit b E T τ m ν ∧
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
          (μ : ℝ → Ω → FiniteMeasure unitInterval), IsTransmissionLimit b E (fun _ => 0) P μ ∧
          ∀ s : ℝ, 0 < s → (∀ j, s < τ j) →
          ∀ Φ : BoundedContinuousFunction (SourceData np) ℝ,
            ∃ Ψ : ℕ → ℝ → ℝ,
              (∀ K h, 0 < h → ComplexModelValue b E s T τ m h K (entranceLaw P μ s) Φ (Ψ K h)) ∧
              ∃ Λ : ℝ → ℝ, (∀ h, 0 < h → Tendsto (fun K => Ψ K h) atTop (𝓝 (Λ h))) ∧
                Tendsto Λ (𝓝[>] 0) (𝓝 (∫ y, Φ y ∂ν))
  moments : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ E : ℝ, -2 < E → E < 2 →
    ∀ (np : ℕ) (τ m : Fin np → ℝ), Function.Injective τ → (∀ j, 0 < τ j) → (∀ j, 0 ≤ m j) →
    ∀ p : ℝ, 1 ≤ p → ∀ T₀ : ℝ, ∃ C : ℝ, ∀ T : ℝ, (∀ j, τ j < T) → T ≤ T₀ →
      ∀ ν : Measure (SourceData np), IsComplexSourceLimit b E T τ m ν →
        ∫⁻ y, ENNReal.ofReal (sourceDataMoment p y) ∂ν ≤ ENNReal.ofReal C
  rawTagMoments : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI → ∀ T p : ℝ, 1 ≤ p →
    ∃ C : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI, ∀ n : ℕ, (n : ℝ) ≤ T * W →
      ∀ (j k : Fin n) (mj mk : ℝ), 0 ≤ mj → 0 ≤ mk →
        (∫⁻ x, ENNReal.ofReal (‖star (tagVector W n j mj x.2.1) ⬝ᵥ
            ((fullInverse b E W n x.1).toBlocks₁₁ *ᵥ tagVector W n k mk x.2.2)‖ ^ p)
          ∂(growthPathLaw W b).prod
            ((circularVectorLaw (Fin W)).prod (circularVectorLaw (Fin W))) ≤
          ENNReal.ofReal (C * (mj * mk) ^ (p / 2))) ∧
        ∫⁻ x, ENNReal.ofReal (‖star (tagVector W n j mj x.2) ⬝ᵥ
            ((fullInverse b E W n x.1).toBlocks₁₁ *ᵥ tagVector W n j mj x.2)‖ ^ p)
          ∂(growthPathLaw W b).prod (circularVectorLaw (Fin W)) ≤
          ENNReal.ofReal (C * (mj * mj) ^ (p / 2))
  extendedSourceMoments : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κI : ℝ, 0 < κI →
    ∀ T p qmax : ℝ, 1 ≤ p → ∃ C : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI,
      ∀ n : ℕ, (n : ℝ) ≤ T * W → ∀ q : Fin n → ℝ, (∀ k, 0 ≤ q k ∧ q k ≤ qmax) →
        ∫⁻ ω, ENNReal.ofReal (‖(extendedSourceMatrix b E W n q ω).trace‖ ^ p +
            (Real.sqrt (∑ x, ∑ y, ‖extendedSourceMatrix b E W n q ω x y‖ ^ 2)) ^ p)
          ∂growthPathLaw W b ≤ ENNReal.ofReal C

end BlockBand.Internal.Contracts.TransmissionLaws
