module

public import BlockBand.SourceProcess.PhysApprox.B3LayerMeanCayley
public import BlockBand.SourceProcess.PhysApprox.B3CovRepCurrent

/-!
# Proof of `B3ClosedCurrentFrame`

* `closedCurrent_operator` (deterministic): under the hypotheses of
  `closed_current_frame` at length `n`,
  `(P𝕊_nC_n(1 - A))ᴴ(P𝕊_nC_n(1 - A)) - P = V_n𝖣V_nᴴ`, `V_n = b3ClosedFrameAt`,
  `𝖣 = srcSignature`. Route: `(P𝕊C)ᴴ(P𝕊C) = P + V_cur sig2 V_curᴴ` (the step `h1` of
  `currentGram_of_frame`, operator form), `AV_cur = 0`, and
  `srcSignature = curSel·sig2·curSelᴴ`.
* **`b3ClosedCurrentFrame_holds : B3LayerMean.B3ClosedCurrentFrame`**: the almost-sure
  hypotheses are those of `ae_currentGram` (the same good-set lemmas).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3LayerMean

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Inputs BlockBand.Internal.Contracts.Layers
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedSum
open BlockBand.SourceProcess.ClosedReduce BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess BlockBand.Transmission.Bridge
open BlockBand.SourceProcess.PhysApprox.B3 BlockBand.SourceProcess.PhysApprox.B3Cur

variable {W np K : ℕ} {b E s h : ℝ}

/-- **The closed current is carried by the closed frame** (deterministic, operator form). -/
theorem closedCurrent_operator (τ m : Fin np → ℝ)
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
    (nearPortProj W * scatteringMatrix b E W n y.1.1 *
        physClosingMapAt b E s h W n y.1.1 (phase y.2) *
        (1 - farEmbed (omittedProj b E h W (closeLen s W) y.1.1)))ᴴ *
      (nearPortProj W * scatteringMatrix b E W n y.1.1 *
        physClosingMapAt b E s h W n y.1.1 (phase y.2) *
        (1 - farEmbed (omittedProj b E h W (closeLen s W) y.1.1))) - nearPortProj W =
    b3ClosedFrameAt b E s h τ m W n Vs y * srcSignature K (Fin np) *
      (b3ClosedFrameAt b E s h τ m W n Vs y)ᴴ := by
  have hz : ‖phase y.2‖ = 1 := by
    rw [phase]; exact Complex.norm_exp_ofReal_mul_I y.2
  set C := physClosingMapAt b E s h W n y.1.1 (phase y.2)
  set S := scatteringMatrix b E W n y.1.1
  set P := nearPortProj W
  set A := farEmbed (omittedProj b E h W (closeLen s W) y.1.1)
  set X := b3ClosedFrameAt b E s h τ m W n Vs y
  have hPH : Pᴴ = P := nearPortProj_conjTranspose
  have hPP : P * P = P := nearPortProj_mul_self
  have hAH : Aᴴ = A := by rw [farEmbed_conjTranspose, omittedProj_conjTranspose]
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
  have h1 : (P * S * C)ᴴ * (P * S * C) = P + curBlock X * sig2 K * (curBlock X)ᴴ := by
    rw [← key]
    change (P * S * C)ᴴ * (P * S * C) = P + Cᴴ * (Sᴴ * P * S - P) * C
    have e1 : (P * S * C)ᴴ * (P * S * C) = Cᴴ * Sᴴ * (P * P) * S * C := by
      simp only [conjTranspose_mul, hPH, Matrix.mul_assoc]
    rw [e1, hPP, Matrix.mul_sub, Matrix.sub_mul, hPC]
    simp only [Matrix.mul_assoc]
    abel
  have hAX : A * curBlock X = 0 := by
    rw [← mul_curSel, ← Matrix.mul_assoc, A_mul_b3ClosedFrameAt, Matrix.zero_mul]
  have hX1 : (1 - A) * curBlock X = curBlock X := by
    rw [Matrix.sub_mul, Matrix.one_mul, hAX, sub_zero]
  have hX2 : (curBlock X)ᴴ * (1 - A) = (curBlock X)ᴴ := by
    have e : ((1 - A) * curBlock X)ᴴ = (curBlock X)ᴴ * (1 - A) := by
      rw [conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hAH]
    rw [← e, hX1]
  have hAP : (1 - A) * P = P := by
    rw [Matrix.sub_mul, Matrix.one_mul, farEmbed_mul_nearPortProj, sub_zero]
  have hPA : P * (1 - A) = P := by
    rw [Matrix.mul_sub, Matrix.mul_one, nearPortProj_mul_farEmbed, sub_zero]
  calc (P * S * C * (1 - A))ᴴ * (P * S * C * (1 - A)) - P =
        (1 - A) * ((P * S * C)ᴴ * (P * S * C)) * (1 - A) - P := by
          rw [conjTranspose_mul (P * S * C) (1 - A), conjTranspose_sub, conjTranspose_one, hAH]
          simp only [Matrix.mul_assoc]
    _ = curBlock X * sig2 K * (curBlock X)ᴴ := by
          rw [h1, Matrix.mul_add, Matrix.add_mul, hAP, hPA, ← Matrix.mul_assoc (1 - A),
            ← Matrix.mul_assoc (1 - A), hX1, Matrix.mul_assoc _ (curBlock X)ᴴ, hX2]
          abel
    _ = X * srcSignature K (Fin np) * Xᴴ := by
          rw [srcSignature_eq_sel, ← mul_curSel]
          simp only [conjTranspose_mul, Matrix.mul_assoc]

/-- **`B3ClosedCurrentFrame` holds.** -/
theorem b3ClosedCurrentFrame_holds : B3ClosedCurrentFrame := by
  intro b E np τ m T s h K Vs hFD R
  obtain ⟨hb0, hb, hE1, hE2, -⟩ := hFD.1
  have hh : h ^ 2 < 1 := by nlinarith [hFD.2.2.2.1, hFD.2.2.2.2.1]
  filter_upwards [eventually_ge_atTop 1, eventually_one_le_closeLen hFD.2.1, hFD.2.2.2.2.2]
    with W hW hsW hV j hj
  have hjc : closeLen s W ≤ j := (Finset.mem_Ico.mp (Finset.mem_filter.mp hj).1).1
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
  filter_upwards [h2] with y hg hyA
  obtain ⟨hU, hF, hT, hR, hL, hC, hG, hE⟩ := hg
  exact closedCurrent_operator τ m (Vs W) y hjc hsW hU hF hT hR (hC hyA.1) hL hh hG hE

end BlockBand.SourceProcess.PhysApprox.B3LayerMean
