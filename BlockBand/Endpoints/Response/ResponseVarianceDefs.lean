module

public import BlockBand.Endpoints.Response.PassDerivativeClosed
public import BlockBand.Endpoints.Sine.MicroscopicTagClock
public import BlockBand.Internal.Contracts.ClocksCommonPort
public import BlockBand.Statements

/-!
# Definitions for the physical Fourier variance bound of the signed response

* `rvCosineTest τ m s = q_m(s) = cos(2πms/τ)`;
* `rvLeadFrame = U = G₀V` (the port columns of `G₀ = 𝓜⁻¹`);
* `rvLeadClock = A = W⁻² U*U`, the complete matched-lead clock (interior and port positions);
* `rvConductance = g = Tr T_L`, `T_L = I - S₀₀*S₀₀` the near-port reflection defect of the
  zero-source scattering matrix `𝕊₀ = scatteringMatrix`;
* `rvSignedDeriv = ∂_q(F_L + F_R)` sample-wise: the explicit zero-source derivative along `q₊`
  minus the one along `q₋` (`portRatioDeriv`).
* `rvFourierVariance R E w m = V_{W,m} = E Σ_α w(u_α) |ν_α(e^{2πim·})|²`: the exact physical law
  `R.model.law`, the fixed ordered eigenpairs and profiles of the realization,
  `u_α = Nρ(E)(λ_α - E)` (`unfoldedEigenvalue`), `e^{2πim·} = fourier m` on the unit torus.

The hypotheses of the proof:
* `RvSignedTraceBound`: the signed response trace bound;
* `RvGaussianVarianceLower`: the Gaussian variance lower bound;
* `RvClockConductanceMoment`: `E[(Tr A)²(1+g)]` bounded by the full-clock fourth moment and the
  positive-time conductance second moment.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Layers
  BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.ClocksCommonPort
open scoped ENNReal NNReal

/-!
### The test, the source Gram matrix and the clock
-/

/-- `q_m(s) = cos(2πms/τ)`. -/
def rvCosineTest (τ : ℝ) (m : ℤ) (s : ℝ) : ℝ := Real.cos (2 * Real.pi * m * s / τ)

/-- `U = G₀V`: the port columns of the inverse of the full path with its matched leads. -/
def rvLeadFrame (b e : ℝ) (W r : ℕ) (ω : GrowthPath W) :
    Matrix (FullSite W r) (Fin 2 × Fin W) ℂ :=
  fullInverse b e W r ω * leadInclusion W r

/-- The signed source Gram matrix `B_q = U*(Q_q/W²)U`. -/
def rvSourceGram (b e : ℝ) (W r : ℕ) (q : ℝ → ℝ) (ω : GrowthPath W) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (rvLeadFrame b e W r ω)ᴴ * sourceDiag W r q * rvLeadFrame b e W r ω

/-- The complete matched-lead clock `A = W⁻² U*U`. -/
def rvLeadClock (b e : ℝ) (W r : ℕ) (ω : GrowthPath W) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  ((((W : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) • ((rvLeadFrame b e W r ω)ᴴ * rvLeadFrame b e W r ω)

/-- The zero-source conductance `g = Tr T_L`. -/
def rvConductance (b e : ℝ) (W r : ℕ) (ω : GrowthPath W) : ℝ :=
  (portDefect (scatteringMatrix b e W r ω) 0).trace.re

/-- The sample-wise signed derivative `∂_q(F_L + F_R) = ∂_{q₊} - ∂_{q₋}` at zero source. -/
def rvSignedDeriv (b e x y : ℝ) (W r : ℕ) (q : ℝ → ℝ) (ω : GrowthPath W) : ℝ :=
  portRatioDeriv b e x y W r (posPart q) ω - portRatioDeriv b e x y W r (negPart q) ω

/-!
### The physical Fourier variance
-/

/-- The physical Fourier variance `V_{W,m} = E Σ_α w(u_α)|ν_α(e^{2πim·})|²`: exact physical law,
fixed eigenpairs and mass profiles, physical unfolding `u_α = Nρ(E)(λ_α - E)`. -/
def rvFourierVariance {p : Parameters} (R : FiniteRealization p) (E : ℝ) (w : SpectralWeight)
    (m : ℤ) : ℝ :=
  ∫ H, ∑ α : Fin p.N, w (R.spectral.unfoldedEigenvalue E H α) *
      ‖∫ t, fourier m t ∂(R.spectral.profile H α : Measure Torus)‖ ^ 2
    ∂(R.model.law : Measure p.SiteMatrix)

/-!
### Hypotheses of the proof
-/

/-- The signed response trace bound (from the exact signed ratio derivative, the projection
identity `‖P - P'‖²_HS = 2g` and the Hilbert–Schmidt bound of `C - r₀I`). For fixed `x ≥ 0`,
`0 ≤ y < 1` there is `c = c_{x,y}`; for every sample with Hermitian blocks and invertible full
path matrix, at every bulk real energy and every signed `q`:
`|∂_q(F_L+F_R)| ≤ 4η((x + y)|Tr B_q| + c √g ‖B_q‖_HS)`, `η = Im z_b(e)`, `r₀ = x + y`. -/
def RvSignedTraceBound : Prop :=
  ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → y < 1 → ∃ c : ℝ, 0 ≤ c ∧
    ∀ b e : ℝ, 0 < b → b < 1 / 2 → -2 < e → e < 2 → ∀ (W r : ℕ) (q : ℝ → ℝ)
      (ω : GrowthPath W), (∀ k, (ω.1 k).IsHermitian) → IsUnit (fullPathMatrix b e W r ω).det →
      |rvSignedDeriv b e x y W r q ω| ≤ 4 * etaZ b e *
        ((x + y) * |(rvSourceGram b e W r q ω).trace.re| +
          c * Real.sqrt (rvConductance b e W r ω) *
            Real.sqrt (hsSq (rvSourceGram b e W r q ω)))

/-- The Gaussian variance lower bound, with an absolute constant `c`: for a standard complex
Gaussian `h ~ CN(0, I)` (`circularVectorLaw`), Hermitian `B` and `A ⪰ 0` with `-A ⪯ B ⪯ A` (so
that the ratio is bounded by `1`; the default `0/0 = 0` is used on the null event `h*Ah = 0`),
`(Tr B)² + Tr B² ≤ c (Tr A)² E_h|h*Bh / h*Ah|²`. -/
def RvGaussianVarianceLower : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ),
    IsSandwichedOn B A →
      B.trace.re ^ 2 + hsSq B ≤
        c * A.trace.re ^ 2 * ∫ h, (quadForm B h / quadForm A h) ^ 2 ∂circularVectorLaw ι

/-- The multiplier moment: `E[(Tr A)²(1 + g)]` is bounded by the full-clock fourth moment and the
positive-time conductance second moment. Fixed `b`, a bulk margin `κ`, a time floor `ε > 0` and a
horizon `T`; then `C, W₀`; for `W ≥ W₀`, every `e ∈ bulkInterval κ` and every length
`εW ≤ r ≤ TW`: `E[(1 + √g)²(Tr A)²] ≤ C` under `growthPathLaw W b`. -/
def RvClockConductanceMoment : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ ε T : ℝ, 0 < κ → 0 < ε →
    ∃ (C : ℝ) (W₀ : ℕ), ∀ W : ℕ, W₀ ≤ W → ∀ e ∈ bulkInterval κ, ∀ r : ℕ,
      ε * W ≤ r → (r : ℝ) ≤ T * W →
        ∫⁻ ω, ENNReal.ofReal ((1 + Real.sqrt (rvConductance b e W r ω)) ^ 2 *
            (rvLeadClock b e W r ω).trace.re ^ 2) ∂growthPathLaw W b ≤ ENNReal.ofReal C

/-!
### Measurability
-/

theorem rv_measurable_leadFrame_of (b : ℝ) (W r : ℕ) {α : Type*} [MeasurableSpace α]
    {e : α → ℝ} {Ω : α → GrowthPath W} (he : Measurable e) (hΩ : Measurable Ω) :
    Measurable (fun a => rvLeadFrame b (e a) W r (Ω a)) := by
  unfold rvLeadFrame
  exact (continuous_id.matrix_mul continuous_const).measurable.comp
    (measurable_fullInverse_of b W r he hΩ)

theorem rv_measurable_leadClock_of (b : ℝ) (W r : ℕ) {α : Type*} [MeasurableSpace α]
    {e : α → ℝ} {Ω : α → GrowthPath W} (he : Measurable e) (hΩ : Measurable Ω) :
    Measurable (fun a => rvLeadClock b (e a) W r (Ω a)) := by
  have h := (continuous_id.matrix_conjTranspose.matrix_mul continuous_id).measurable.comp
    (rv_measurable_leadFrame_of b W r he hΩ)
  refine Measurable.of_eval fun x => Measurable.of_eval fun y => ?_
  simp only [rvLeadClock, Matrix.smul_apply, smul_eq_mul]
  exact measurable_const.mul ((measurable_pi_apply y).comp ((measurable_pi_apply x).comp h))

theorem rv_measurable_sourceGram_of (b : ℝ) (W r : ℕ) (q : ℝ → ℝ) {α : Type*}
    [MeasurableSpace α] {e : α → ℝ} {Ω : α → GrowthPath W} (he : Measurable e)
    (hΩ : Measurable Ω) :
    Measurable (fun a => rvSourceGram b (e a) W r q (Ω a)) := by
  unfold rvSourceGram
  exact ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
    continuous_id).measurable.comp (rv_measurable_leadFrame_of b W r he hΩ)

theorem rv_measurable_scattering_of (b : ℝ) (W r : ℕ) {α : Type*} [MeasurableSpace α]
    {e : α → ℝ} {Ω : α → GrowthPath W} (he : Measurable e) (hΩ : Measurable Ω) :
    Measurable (fun a => scatteringMatrix b (e a) W r (Ω a)) := by
  have hG := measurable_fullInverse_of b W r he hΩ
  have hη : Measurable (fun a => (((2 * etaZ b (e a) : ℝ) : ℂ) * Complex.I)) := by
    unfold etaZ
    exact ((Complex.measurable_ofReal.comp
      (measurable_const.mul (Complex.measurable_im.comp ((measurable_boundaryZ b).comp he))))).mul
      measurable_const
  refine Measurable.of_eval fun x => Measurable.of_eval fun y => ?_
  simp only [scatteringMatrix, boundaryResolvent, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.toBlocks₂₂]
  exact measurable_const.sub (hη.mul ((measurable_pi_apply (Sum.inr y)).comp
    ((measurable_pi_apply (Sum.inr x)).comp hG)))

theorem rv_measurable_portDefect_of (b : ℝ) (W r : ℕ) (i : Fin 2) {α : Type*}
    [MeasurableSpace α] {e : α → ℝ} {Ω : α → GrowthPath W} (he : Measurable e)
    (hΩ : Measurable Ω) :
    Measurable (fun a => portDefect (scatteringMatrix b (e a) W r (Ω a)) i) := by
  have hS := rv_measurable_scattering_of b W r he hΩ
  have hP : Measurable (fun a => portBlock (scatteringMatrix b (e a) W r (Ω a)) i i) :=
    Measurable.of_eval fun x => Measurable.of_eval fun y => by
      simp only [portBlock, Matrix.of_apply]
      exact (measurable_pi_apply (i, y)).comp ((measurable_pi_apply (i, x)).comp hS)
  have hQ := (continuous_id.matrix_conjTranspose.matrix_mul continuous_id).measurable.comp hP
  refine Measurable.of_eval fun x => Measurable.of_eval fun y => ?_
  simp only [portDefect, Matrix.sub_apply]
  exact measurable_const.sub ((measurable_pi_apply y).comp ((measurable_pi_apply x).comp hQ))

theorem rv_measurable_conductance_of (b : ℝ) (W r : ℕ) {α : Type*} [MeasurableSpace α]
    {e : α → ℝ} {Ω : α → GrowthPath W} (he : Measurable e) (hΩ : Measurable Ω) :
    Measurable (fun a => rvConductance b (e a) W r (Ω a)) := by
  unfold rvConductance
  exact Complex.measurable_re.comp ((continuous_id.matrix_trace).measurable.comp
    (rv_measurable_portDefect_of b W r 0 he hΩ))

end BlockBand.Endpoints
