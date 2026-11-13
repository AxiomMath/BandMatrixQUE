module

public import BlockBand.SourceProcess.PhysApprox.B3CurMain
public import BlockBand.SourceProcess.PhysApprox.B3FeasGram
public import BlockBand.SourceProcess.PhysApprox.B3FeasProj
public import BlockBand.SourceProcess.Closing.PhysHardy

/-!
# The finite-`W` closed Gram state is exactly feasible

* `closedGram_feasible` (deterministic): under the hypotheses of `closed_current_frame` at the
  length `j ≥ n_s`, with `|z| = 1`, the closed frame `V = C_jᴴX_j` satisfies
  `V𝖣Vᴴ = C_jᴴ(𝕊_jᴴP𝕊_j - P)C_j`, so `P + V𝖣Vᴴ = C_jᴴ𝕊_jᴴP𝕊_jC_j` is a projection of trace
  `Tr P` (`twoProjection_of_closed`), and `GramFeasible 𝖣 (b3ClosedGramAt … j …)`.
* **`ae_b3ClosedGram_feasible`**: on `FrameDomain`, eventually in `W`, almost surely on the cap
  event, for every length `j ≥ closeLen s W` (and every phase in the sample), the closed Gram
  state is feasible. The almost-sure set is that of `complexClosedCurrent_holds`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3Feas

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedSum
open BlockBand.SourceProcess.ClosedReduce BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess BlockBand.Transmission.Bridge
open BlockBand.SourceProcess.PhysApprox.B3 BlockBand.SourceProcess.PhysApprox.B3Cur

variable {W : ℕ} {b E s h : ℝ} {K : ℕ}

/-- **The closed Gram state at length `j ≥ n_s` is feasible** (deterministic), under the
hypotheses of `closed_current_frame`. -/
theorem closedGram_feasible {np : ℕ} (τ m : Fin np → ℝ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (y : ProbedPath W np × ℝ)
    {j : ℕ} (hj : closeLen s W ≤ j) (hs : 1 ≤ closeLen s W)
    (hU : ∀ j, scatteringMatrix b E W j y.1.1 * (scatteringMatrix b E W j y.1.1)ᴴ = 1)
    (hfar : ∀ j, 1 ≤ j → (1 - nearPortProj W) * scatteringMatrix b E W j y.1.1 *
      transportN b E W j y.1.1 = (1 - nearPortProj W) * scatteringMatrix b E W (j + 1) y.1.1)
    (hT : ∀ j, 1 ≤ j → ∀ z : ℂ, ‖z‖ ≤ 1 →
      (physClosingMapAt b E s h W (j + 1) y.1.1 z)ᴴ * (transportN b E W j y.1.1)ᴴ =
        ((1 - farEmbed (omittedProj b E h W (closeLen s W) y.1.1)) *
          (transportN b E W j y.1.1 * physClosingMapAt b E s h W (j + 1) y.1.1 z))ᴴ *
          (physClosingMapAt b E s h W j y.1.1 z)ᴴ)
    (hR : ∀ j, 1 ≤ j → ∀ z : ℂ, ‖z‖ ≤ 1 →
      IsUnit (1 - z • closingN (scatteringMatrix b E W j y.1.1)
        (farEmbed (omittedProj b E h W (closeLen s W) y.1.1))
        (farEmbed (closingPairing b E h W (closeLen s W) y.1.1))).det)
    (hcap : ∀ k, K ≤ k → physTseq b E s W y.1.1 k ≤ h ^ 2)
    (hlt : ∀ k : Fin K, h ^ 2 < physTseq b E s W y.1.1 k.val →
      physTseq b E s W y.1.1 k.val < 1)
    (hh : h ^ 2 < 1)
    (hG : gramPair (nearPortProj W) (Vs y.1.1) =
      curGramOf (initialGram K (Fin 0) (physTseq b E s W y.1.1) h))
    (hE : ∀ x k, ((physOutProj b E s W y.1.1 - nearPortProj W) * Vs y.1.1) x k =
      modeEig (physTseq b E s W y.1.1 k.1.val) k.2 * Vs y.1.1 x k) :
    GramFeasible (srcSignature K (Fin np)) (b3ClosedGramAt b E s h τ m W j Vs y) := by
  have hz : ‖phase y.2‖ = 1 := by
    rw [phase]; exact Complex.norm_exp_ofReal_mul_I y.2
  set C := physClosingMapAt b E s h W j y.1.1 (phase y.2)
  set X := b3ClosedFrameAt b E s h τ m W j Vs y
  set S := scatteringMatrix b E W j y.1.1
  set A := farEmbed (omittedProj b E h W (closeLen s W) y.1.1)
  set Pi := farEmbed (closingPairing b E h W (closeLen s W) y.1.1)
  have hcur : curBlock X = Cᴴ * (stepProd (fun i => transportN b E W i y.1.1) (closeLen s W)
      (j - closeLen s W))ᴴ * Vs y.1.1 := by
    rw [Matrix.mul_assoc]
    change curBlock (Cᴴ * b3OpenFrameAt b E s τ m W j Vs y.1) = _
    rw [curBlock_mul]
    congr 1
  have hsig : X * srcSignature K (Fin np) * Xᴴ = curBlock X * sig2 K * (curBlock X)ᴴ := by
    rw [srcSignature_eq_sel, ← mul_curSel]
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  have key := closed_current_frame (Vs y.1.1) hj hs hU hfar hT hR hcap hlt hh hG hE hz
  have hV : X * srcSignature K (Fin np) * Xᴴ =
      (closingMap S A Pi (phase y.2))ᴴ * (Sᴴ * nearPortProj W * S - nearPortProj W) *
        closingMap S A Pi (phase y.2) := by
    rw [hsig, hcur]
    exact key.symm
  have hAH : Aᴴ = A := by rw [farEmbed_conjTranspose, omittedProj_conjTranspose]
  have hAA : A * A = A := by rw [farEmbed_mul, omittedProj_mul_self]
  have hPi : Pi * Piᴴ = A := by
    rw [farEmbed_conjTranspose, farEmbed_mul, closingPairing_mul_conj b E h hh]
  have hTP := twoProjection_of_closed (hU j) nearPortProj_conjTranspose nearPortProj_mul_self
    hAH hAA hPi (nearPortProj_mul_farEmbed _) (nearPortProj_mul_farEmbed _)
    (farEmbed_mul_nearPortProj _) (hR j (hs.trans hj) (phase y.2) hz.le) hz hV
  exact gramFeasible_of_realization X nearPortProj_conjTranspose nearPortProj_mul_self hTP

/-- **The finite-`W` closed Gram state is exactly feasible**. On
`FrameDomain`, eventually in `W`, almost surely on the cap event, for every length
`j ≥ closeLen s W`, `GramFeasible 𝖣 (b3ClosedGramAt … j …)`. -/
theorem ae_b3ClosedGram_feasible {np : ℕ} {τ m : Fin np → ℝ} {T : ℝ}
    {Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hD : FrameDomain b E τ m T s h K Vs) :
    ∀ᶠ W in atTop, ∀ᵐ y ∂closedLaw b W np, y.1.1 ∈ physCapEventC b E s h K W →
      ∀ j, closeLen s W ≤ j →
        GramFeasible (srcSignature K (Fin np)) (b3ClosedGramAt b E s h τ m W j (Vs W) y) := by
  obtain ⟨⟨hb0, hb, hE1, hE2, -, -, -, -⟩, hs, -, hh0, hh1, hVs⟩ := hD
  have hh : h ^ 2 < 1 := by nlinarith
  filter_upwards [eventually_ge_atTop 1, eventually_one_le_closeLen hs, hVs] with W hW hsW hV
  have hgood : ∀ᵐ ω ∂growthPathLaw W b,
      (∀ j, scatteringMatrix b E W j ω * (scatteringMatrix b E W j ω)ᴴ = 1) ∧
      (∀ j, 1 ≤ j → (1 - nearPortProj W) * scatteringMatrix b E W j ω *
        transportN b E W j ω = (1 - nearPortProj W) * scatteringMatrix b E W (j + 1) ω) ∧
      (∀ j, 1 ≤ j → ∀ z : ℂ, ‖z‖ ≤ 1 →
        (physClosingMapAt b E s h W (j + 1) ω z)ᴴ * (transportN b E W j ω)ᴴ =
          ((1 - farEmbed (omittedProj b E h W (closeLen s W) ω)) *
            (transportN b E W j ω * physClosingMapAt b E s h W (j + 1) ω z))ᴴ *
            (physClosingMapAt b E s h W j ω z)ᴴ) ∧
      (∀ j, 1 ≤ j → ∀ z : ℂ, ‖z‖ ≤ 1 →
        IsUnit (1 - z • closingN (scatteringMatrix b E W j ω)
          (farEmbed (omittedProj b E h W (closeLen s W) ω))
          (farEmbed (closingPairing b E h W (closeLen s W) ω))).det) ∧
      (∀ k : Fin K, h ^ 2 < physTseq b E s W ω k.val → physTseq b E s W ω k.val < 1) ∧
      (ω ∈ physCapEventC b E s h K W → ∀ k, K ≤ k → physTseq b E s W ω k ≤ h ^ 2) ∧
      (gramPair (nearPortProj W) (Vs W ω) =
          curGramOf (initialGram K (Fin 0) (physTseq b E s W ω) h) ∧
        ∀ x k, ((physOutProj b E s W ω - nearPortProj W) * Vs W ω) x k =
          modeEig (physTseq b E s W ω k.1.val) k.2 * Vs W ω x k) := by
    filter_upwards [FullSourceStops.ae_scattering_unitary hb hE1 hE2 hW,
      ae_farOut_succ hb0 hb hE1 hE2 hW,
      ae_closedCol_transport_disc (s := s) (h := h) hb0 hb hE1 hE2 hW hh,
      ae_isUnit_closingResolvent (h := h) hb0 hb hE1 hE2 hW hh (closeLen s W),
      ae_hlt (s := s) hb hE1 hE2 hW, ae_cap_tseq hb hE1 hE2 hW s h K, hV.2]
      with ω hU hF hT hR hL hC hVω
    exact ⟨fun j => (hU j).1, hF, hT, hR, hL K h, hC, hVω⟩
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := growthPathLaw W b)
    (ν := Measure.pi fun _ : Fin np =>
      BlockBand.Internal.Contracts.CoareaPalm.circularVectorLaw (Fin W))).ae hgood
  have h2 := (Measure.quasiMeasurePreserving_fst (μ := probedPathLaw W np b)
    (ν := phaseLaw)).ae h1
  filter_upwards [h2] with y hg hcap j hj
  obtain ⟨hU, hF, hT, hR, hL, hC, hG, hE⟩ := hg
  exact closedGram_feasible τ m (Vs W) y hj hsW hU hF hT hR (hC hcap) hL hh hG hE

end BlockBand.SourceProcess.PhysApprox.B3Feas
