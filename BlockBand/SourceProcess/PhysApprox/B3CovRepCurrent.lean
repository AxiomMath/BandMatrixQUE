module

public import BlockBand.SourceProcess.PhysApprox.B3CovRepKBound
public import BlockBand.SourceProcess.PhysApprox.B3CurMain

/-!
# The closed current Gram identity `ClosedCurrentGram`

* `currentGram_of_frame` (deterministic): under the hypotheses of
  `B3Cur.closed_current_frame` at length `j`, `V_clᴴ(P𝕊C)ᴴ(P𝕊C)V_cl = B + M𝖣M` (`gramC0`). Proof:
  `(P𝕊C)ᴴ(P𝕊C) = Cᴴ(𝕊ᴴP𝕊 - P)C + CᴴPC`, `CᴴPC = P` (`closingMap_conj_near`), and the closed
  current is `V_cur sig2 V_curᴴ` with `V_cur` the current block of the closed frame;
* `ae_currentGram`: the hypotheses hold almost surely on the cap event (as in
  `B3Cur.complexClosedCurrent_holds`), hence the identity a.e. on the alive set;
* **`closedCurrentGram_holds : ClosedCurrentGram`**.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Inputs BlockBand.Internal.Contracts.Layers
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedSum
open BlockBand.SourceProcess.ClosedReduce BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess BlockBand.Transmission.Bridge
open BlockBand.SourceProcess.PhysApprox.B3Cur

variable {W np K : ℕ} {b E s h : ℝ}

/-- **The closed current Gram identity at one sample** (deterministic). -/
theorem currentGram_of_frame (τ m : Fin np → ℝ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (y : ProbedPath W np × ℝ)
    {n : ℕ} (hn : closeLen s W ≤ n) (hs : 1 ≤ closeLen s W)
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
    (b3ClosedFrameAt b E s h τ m W n Vs y)ᴴ *
        ((b3ClosedPS b E s h W n y.1.1 (phase y.2))ᴴ * b3ClosedPS b E s h W n y.1.1 (phase y.2)) *
        b3ClosedFrameAt b E s h τ m W n Vs y =
      gramC0 (b3ClosedGramAt b E s h τ m W n Vs y).1 (b3ClosedGramAt b E s h τ m W n Vs y).2
        (srcSignature K (Fin np)) := by
  have hz : ‖phase y.2‖ = 1 := by
    rw [phase]; exact Complex.norm_exp_ofReal_mul_I y.2
  set C := physClosingMapAt b E s h W n y.1.1 (phase y.2)
  set S := scatteringMatrix b E W n y.1.1
  set P := nearPortProj W
  set X := b3ClosedFrameAt b E s h τ m W n Vs y
  have hPH : Pᴴ = P := nearPortProj_conjTranspose
  have hPP : P * P = P := nearPortProj_mul_self
  have hcur : curBlock X = Cᴴ * (stepProd (fun j => transportN b E W j y.1.1) (closeLen s W)
      (n - closeLen s W))ᴴ * Vs y.1.1 := by
    rw [Matrix.mul_assoc]
    change curBlock (Cᴴ * b3OpenFrameAt b E s τ m W n Vs y.1) = _
    rw [curBlock_mul]
    congr 1
  have hPC : Cᴴ * P * C = P :=
    closingMap_conj_near nearPortProj_conjTranspose nearPortProj_mul_self
      (nearPortProj_mul_farEmbed _) (nearPortProj_mul_farEmbed _)
  have key := closed_current_frame (Vs y.1.1) hn hs hU hfar hT hR hcap hlt hh hG hE hz
  rw [← hcur] at key
  have h1 : (b3ClosedPS b E s h W n y.1.1 (phase y.2))ᴴ * b3ClosedPS b E s h W n y.1.1 (phase y.2) =
      P + curBlock X * sig2 K * (curBlock X)ᴴ := by
    rw [← key]
    change (P * S * C)ᴴ * (P * S * C) = P + Cᴴ * (Sᴴ * P * S - P) * C
    have e1 : (P * S * C)ᴴ * (P * S * C) = Cᴴ * Sᴴ * (P * P) * S * C := by
      simp only [conjTranspose_mul, hPH, Matrix.mul_assoc]
    rw [e1, hPP, Matrix.mul_sub, Matrix.sub_mul, hPC]
    simp only [Matrix.mul_assoc]
    abel
  rw [h1]
  simp only [b3ClosedGramAt, gramPair, gramC0, sourceGram, nearGram, srcSignature_eq_sel,
    ← mul_curSel]
  simp only [conjTranspose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  rfl

/-- **The closed current Gram identity holds a.e. on the alive set.** -/
theorem ae_currentGram (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hh : h ^ 2 < 1) (hW : 1 ≤ W) (τ m : Fin np → ℝ)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hV : IsTimeSFrame b E s h K W Vs) (hs : 1 ≤ closeLen s W) (R : ℝ) {j : ℕ}
    (hj : closeLen s W ≤ j) : CurrentGramAt b E s h τ m R W j Vs := by
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
      (gramPair (nearPortProj W) (Vs ω) =
          curGramOf (initialGram K (Fin 0) (physTseq b E s W ω) h) ∧
        ∀ x k, ((physOutProj b E s W ω - nearPortProj W) * Vs ω) x k =
          modeEig (physTseq b E s W ω k.1.val) k.2 * Vs ω x k) := by
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
  filter_upwards [h2] with y hg hyA
  obtain ⟨hU, hF, hT, hR, hL, hC, hG, hE⟩ := hg
  exact currentGram_of_frame τ m Vs y hj hs hU hF hT hR (hC hyA.1) hL hh hG hE

/-- **`ClosedCurrentGram` holds.** -/
theorem closedCurrentGram_holds : ClosedCurrentGram := by
  intro b E np τ m T s h K Vs hFD R
  obtain ⟨hb0, hb, hE1, hE2, -⟩ := hFD.1
  have hh : h ^ 2 < 1 := by nlinarith [hFD.2.2.2.1, hFD.2.2.2.2.1]
  filter_upwards [eventually_ge_atTop 1, eventually_one_le_closeLen hFD.2.1, hFD.2.2.2.2.2]
    with W hW hsW hV j hj
  have hj' := hj
  simp only [genNoBirthSteps, Finset.mem_filter, Finset.mem_Ico] at hj'
  exact ae_currentGram hb0 hb hE1 hE2 hh hW τ m hV hsW R hj'.1.1

/-- **`ConjLayerHyp b3CovErr b3CovZ` from the input hypotheses.** -/
theorem conjLayerHyp_holds (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) : ConjLayerHyp b3CovErr b3CovZ :=
  conjLayerHyp_of_current hGA hLp hP closedCurrentGram_holds

end BlockBand.SourceProcess.PhysApprox.B3
