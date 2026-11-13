module

public import BlockBand.SourceProcess.SmallLeak.GrowthLayer
public import BlockBand.SourceProcess.SmallLeak.StartAlg
public import BlockBand.Transmission.Bridge.TransportFull

/-!
# The omitted flux as a function of the past; its one-step identity

For `n_s ≤ j`: `A_-` is a function of the past at length `j` (`omittedProj_extPast`); almost
surely `g_j = fluxAt(𝕏_j, A_-)` (`ae_omittedFlux_eq_past`) and
`g_{j+1} = fluxNext(𝕏_j, A_-, fresh_j)` (`ae_omittedFlux_succ`), by `J₊ = N*JN`; and
`0 ≤ g_j ≤ W` (`ae_omittedFlux_le`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SmallLeak

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.FullSourceStops
open BlockBand.SourceProcess.FullSource BlockBand.SourceProcess.ClosingAux
open BlockBand.Transmission.PathScalar
open scoped Matrix ComplexOrder

variable {W : ℕ}

theorem pathAt_extPast_of_le {n j : ℕ} (h : n ≤ j) (ω : GrowthPath W) :
    pathAt W n (extPast W j (pastCoords W j ω)) = pathAt W n ω := by
  rw [pathAt_eq_pathOfPast, Function.comp_apply, Function.comp_apply, pastCoords_restrict h,
    pastCoords_extPast, ← pastCoords_restrict]

theorem scatteringMatrix_extPast {n j : ℕ} (h : n ≤ j) (b E : ℝ) (ω : GrowthPath W) :
    scatteringMatrix b E W n (extPast W j (pastCoords W j ω)) = scatteringMatrix b E W n ω := by
  simp only [scatteringMatrix, boundaryResolvent, fullInverse, fullPathMatrix,
    pathAt_extPast_of_le h]

/-- `A_-` (cutoff `h`, closing length `n_s`) read from the past at length `j`. -/
def omittedPast (b E h s : ℝ) (W j : ℕ) (p : PastSample W j) : Matrix (Fin W) (Fin W) ℂ :=
  omittedProj b E h W ⌊(W : ℝ) * s⌋₊ (extPast W j p)

theorem omittedProj_extPast {b E h s : ℝ} {j : ℕ} (hj : ⌊(W : ℝ) * s⌋₊ ≤ j)
    (ω : GrowthPath W) :
    omittedPast b E h s W j (pastCoords W j ω) = omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω := by
  simp only [omittedPast, omittedProj, farTransmission, farReflection,
    scatteringMatrix_extPast hj]

theorem measurable_omittedPast (b E h s : ℝ) (j : ℕ) :
    Measurable (omittedPast b E h s W j) :=
  (measurable_omittedProj b E h _).comp (measurable_extPast _)

theorem omittedPast_conjTranspose (b E h s : ℝ) (j : ℕ) (p : PastSample W j) :
    (omittedPast b E h s W j p)ᴴ = omittedPast b E h s W j p :=
  omittedProj_conjTranspose b E h _ _

theorem omittedPast_mul_self (b E h s : ℝ) (j : ℕ) (p : PastSample W j) :
    omittedPast b E h s W j p * omittedPast b E h s W j p = omittedPast b E h s W j p :=
  omittedProj_mul_self b E h _ _

/-- `g_j` read from the past. -/
def fluxPast (b E h s : ℝ) (W j : ℕ) (p : PastSample W j) : ℝ :=
  fluxAt b E (pastXX E W j p) (omittedPast b E h s W j p)

theorem measurable_fluxAt_comp (b E : ℝ) {α : Type*} [MeasurableSpace α]
    {XX : α → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {A : α → Matrix (Fin W) (Fin W) ℂ}
    (hXX : Measurable XX) (hA : Measurable A) : Measurable fun a => fluxAt b E (XX a) (A a) := by
  have hS := (CompleteSourceGap.measurable_twoPortScattering (W := W) b E).comp hXX
  have hF := measurable_farEmbed hA
  exact measurable_trace_re (measurable_matrix_mul' (measurable_matrix_mul' hF
    (measurable_matrix_mul' (measurable_matrix_mul' (measurable_matrix_conjTranspose' hS)
      measurable_const) hS)) hF)

theorem measurable_fluxPast (b E h s : ℝ) (j : ℕ) : Measurable (fluxPast b E h s W j) :=
  measurable_fluxAt_comp b E (measurable_pastXX E j) (measurable_omittedPast b E h s j)

theorem omittedFlux_eq_fluxAt {b E h s : ℝ} {j : ℕ} (ω : GrowthPath W)
    (hF : IsUnit (pathMatrix (pathAt W j ω) - (E : ℂ) • 1)) :
    omittedFlux b E h s W j ω =
      fluxAt b E (pathSchur E (pathAt W j ω)) (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω) := by
  rw [omittedFlux, nearOut, scatteringMatrix_eq b E j ω hF]; rfl

/-- **`g_j` from the past**, almost surely, `n_s ≤ j`. -/
theorem ae_omittedFlux_eq_past {b E h s : ℝ} (hb : b < 1 / 2) (hW : 1 ≤ W) {j : ℕ}
    (hj : ⌊(W : ℝ) * s⌋₊ ≤ j) :
    ∀ᵐ ω ∂growthPathLaw W b, omittedFlux b E h s W j ω = fluxPast b E h s W j (pastCoords W j ω) := by
  filter_upwards [ae_isUnit_pathPencil_growth hb hW E] with ω hF
  rw [omittedFlux_eq_fluxAt ω (hF j), fluxPast, ← pastXX_eq, omittedProj_extPast hj]

/-- **The one-step identity** `g_{j+1} = fluxNext(𝕏_j, A_-, fresh_j)`, almost surely. -/
theorem ae_omittedFlux_succ {b E h s : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E)
    (hE2 : E < 2) (hW : 1 ≤ W) {j : ℕ} (hj1 : 1 ≤ j) (hj : ⌊(W : ℝ) * s⌋₊ ≤ j) :
    ∀ᵐ ω ∂growthPathLaw W b, omittedFlux b E h s W (j + 1) ω =
      fluxNext b E (pastXX E W j (pastCoords W j ω)) (omittedPast b E h s W j (pastCoords W j ω))
        (freshSample W j ω) := by
  filter_upwards [ae_isUnit_pathPencil_growth hb hW E, ae_pathCurrent_succ_full hb0 hb hE1 hE2 hW]
    with ω hF hJ
  have hJ' := hJ j hj1
  have hN : nearOut b E W (j + 1) ω = (transportN b E W j ω)ᴴ *
      (nearOut b E W j ω - nearProjection W) * transportN b E W j ω + nearProjection W := by
    calc nearOut b E W (j + 1) ω = pathCurrent b E W (j + 1) ω + nearProjection W :=
          (sub_add_cancel _ _).symm
      _ = _ := by rw [hJ']; rfl
  rw [omittedFlux, hN, fluxNext, omittedProj_extPast hj, ← pastXX_eq, farOmitted]
  rw [nearOut, scatteringMatrix_eq b E j ω (hF j)]
  rfl

/-- `fluxAt ≤ Re Tr A ≤ W` for a Hermitian two-port and `A = 1_{[0,h²]}(T)`. -/
theorem fluxAt_le_card {b E : ℝ} (hη : 0 < etaZ b E) {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hXX : XX.IsHermitian) (h : ℝ) {T : Matrix (Fin W) (Fin W) ℂ} (hT : T.IsHermitian) :
    fluxAt b E XX (cfc (omitIndicator h) T) ≤ W := by
  set A := cfc (omitIndicator h) T
  have hA : Aᴴ = A := cfc_conjTranspose _ _
  have hA2 : A * A = A := by
    have hc := fun f : ℝ → ℝ => T.finite_real_spectrum.continuousOn f
    simp only [A]
    rw [← cfc_mul _ _ T (hc _) (hc _)]
    congr 1; funext t; unfold omitIndicator; split_ifs <;> simp
  set S := twoPortScattering b E XX
  have hS := twoPortScattering_unitary b E XX hXX (by simpa [etaZ] using hη)
  have hF : (farEmbed A)ᴴ = farEmbed A := farEmbed_conjTranspose_of hA
  have h1 : (1 - scatOut b E XX).PosSemidef := by
    have : 1 - scatOut b E XX = Sᴴ * (1 - nearProjection W) * S := by
      rw [scatOut, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hS.1]
    rw [this]; exact one_sub_nearProjection_psd.conjTranspose_mul_mul_same S
  have h2 := (h1.conjTranspose_mul_mul_same (farEmbed A)).trace_nonneg
  rw [hF, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.trace_sub] at h2
  have h3 : 0 ≤ ((farEmbed A * farEmbed A).trace - (farEmbed A * scatOut b E XX *
      farEmbed A).trace).re := (Complex.nonneg_iff.mp h2).1
  rw [Complex.sub_re, farEmbed_mul, hA2, trace_farEmbed] at h3
  have h4 : A.trace.re ≤ W := by
    rw [trace_cfc_re hT]
    calc ∑ i, omitIndicator h (hT.eigenvalues i) ≤ ∑ _i : Fin W, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => by unfold omitIndicator; split_ifs <;> norm_num
      _ = W := by simp
  unfold fluxAt; linarith

/-- **`g_j ≤ W`** almost surely. -/
theorem ae_omittedFlux_le {b E h s : ℝ} (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hW : 1 ≤ W) (j : ℕ) : ∀ᵐ ω ∂growthPathLaw W b, omittedFlux b E h s W j ω ≤ W := by
  have hη : 0 < etaZ b E := boundaryZ_im_pos (by linarith) hE1 hE2
  filter_upwards [ae_isUnit_pathPencil_growth hb hW E, ae_growth_isHermitian W b] with ω hF hA
  rw [omittedFlux_eq_fluxAt ω (hF j)]
  exact fluxAt_le_card hη (pathSchur_isHermitian E j ω hA) h
    (isHermitian_farTransmission b E W _ ω)

end BlockBand.SourceProcess.SmallLeak
