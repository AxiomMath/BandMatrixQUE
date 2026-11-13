module

public import BlockBand.SourceProcess.PhysApprox.B3LayerMeanPad
public import BlockBand.SourceProcess.PhysApprox.B3LayerMeanSep
public import BlockBand.SourceProcess.PhysApprox.B3CurMain
public import BlockBand.SourceProcess.FullSourceStops.WordValue

/-!
# `B3CayleyChain` and `B3CayleySep` reduced to four estimates

Proved, for the Cayley state `𝕏 = b3ChainXX` at a length `n` with `1 - 𝕊_pad` invertible:
* `twoPortScattering_b3ChainXX`: `𝕊(𝕏) = 𝕊_pad` (the Cayley inverse is exact);
* `nearPortProj_mul_b3PadScatter`: `P𝕊_pad = P𝕊_nC_n(z)(1 - A)`;
* `A_mul_b3ClosedFrameAt`: `AV_n = 0` (closed columns are retained inputs);
* **`b3SepAt_b3ChainXX`**: the four contracting separators of `𝕏` on the closed frame are
  `b3ContrSep` (`B3SepAt`);
* **`contrGram_b3ChainXX`**: `contrGram(𝕏, V) = b3CovZ` (so `C = 1`);
* `currentOf_b3ChainXX`: `currentOf 𝕏 = (P𝕊C(1 - A))ᴴ(P𝕊C(1 - A)) - P`;
* `measurable_b3ChainXX`, `b3ChainXX_b3Ext`.

The estimates, stated here as hypotheses:
* `B3PadInvertible`: a.s. invertibility of `1 - zN_n` and of `1 - 𝕊_pad(n)` for `n ≥ n_s`. The
  first half is `ae_closedPhase_good`.
* `B3PadTransport`: on the alive set, `V_{j+1} = freshTransport(b3ChainXX_j, F_j)ᴴV_j` (the
  frame transport).
* `B3ClosedCurrentFrame`: on the alive set, `(P𝕊_jC_j(1 - A))ᴴ(P𝕊_jC_j(1 - A)) - P = V𝖣Vᴴ`
  (witness-free; the content of `closed_current_frame` at length `j`).
* `B3PadGrowth`: on the alive set, `b3ChainXX_{j+1} = freshTwoPortSchur(b3ChainXX_j, F_j)`.

Proved: **`b3CayleyChain_of_pad : B3PadInvertible → B3PadTransport → B3ClosedCurrentFrame →
B3CayleyChain`** and **`b3CayleySep_of_pad : B3PadInvertible → B3PadGrowth → B3CayleySep`**.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3LayerMean

open Matrix MeasureTheory Filter
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.SourceProcess.CompleteSourceGap
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosingAux BlockBand.SourceProcess.FullSourceStops
open BlockBand.SourceProcess.ContractingWords (currentOf)
open BlockBand.SourceProcess.ClosedSummedProof (contrGram contrSepSet)
open BlockBand.SourceProcess.PhysApprox.B3
open BlockBand.Transmission.Bridge

variable {W np K : ℕ}

/-!
## Abstract separator algebra
-/

section Abstract

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

theorem closingMap_mul_A' {S A Pi : Matrix ι ι ℂ} {z : ℂ} (hAA : A * A = A) :
    closingMap S A Pi z * A = 0 := by
  simp only [closingMap, closingT, Matrix.add_mul, Matrix.mul_assoc, Matrix.smul_mul,
    Matrix.mul_smul, compl_mul_A hAA, Matrix.mul_zero, smul_zero, zero_add]

/-- The four separator identities on a frame with `AV = 0`, from `PU = P𝕊C(1 - A)`. -/
theorem sep_core {P S C A U : Matrix ι ι ℂ} {V : Matrix ι κ ℂ} (hPH : Pᴴ = P) (hAH : Aᴴ = A)
    (hPU : P * U = P * S * C * (1 - A)) (hAV : A * V = 0) (hAP : (1 - A) * P = P)
    (hPA : P * (1 - A) = P) :
    Vᴴ * (P * S * C) * V = Vᴴ * (P * U) * V ∧
      Vᴴ * (P * S * C)ᴴ * V = Vᴴ * (Uᴴ * P) * V ∧
      Vᴴ * (P * S * C * P) * V = Vᴴ * (P * U * P) * V ∧
      Vᴴ * (P * (P * S * C)ᴴ) * V = Vᴴ * (P * Uᴴ * P) * V := by
  have hV : (1 - A) * V = V := by rw [Matrix.sub_mul, Matrix.one_mul, hAV, sub_zero]
  have hVh : Vᴴ * (1 - A) = Vᴴ := by
    have e : ((1 - A) * V)ᴴ = Vᴴ * (1 - A) := by
      rw [conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hAH]
    rw [← e, hV]
  have hUP : Uᴴ * P = (1 - A) * (P * S * C)ᴴ := by
    have e : Uᴴ * P = (P * U)ᴴ := by rw [conjTranspose_mul, hPH]
    rw [e, hPU, conjTranspose_mul (P * S * C) (1 - A), conjTranspose_sub, conjTranspose_one, hAH]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hPU]; simp only [Matrix.mul_assoc]; rw [hV]
  · rw [hUP]; simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc Vᴴ (1 - A), hVh]
  · rw [hPU, Matrix.mul_assoc (P * S * C) (1 - A) P, hAP]
  · rw [Matrix.mul_assoc P Uᴴ P, hUP, ← Matrix.mul_assoc P (1 - A), hPA]

end Abstract

/-!
## The Cayley state
-/

/-- `𝕊(b3ChainXX) = 𝕊_pad` when `1 - 𝕊_pad` is invertible. -/
theorem twoPortScattering_b3ChainXX {b E s h : ℝ} {n : ℕ} {y : ProbedPath W np × ℝ}
    (hη : 0 < etaZ b E) (hD : IsUnit (1 - b3PadScatter b E s h W n y.1.1 (phase y.2)).det) :
    twoPortScattering b E (b3ChainXX b E s h W n y) =
      b3PadScatter b E s h W n y.1.1 (phase y.2) := by
  set U := b3PadScatter b E s h W n y.1.1 (phase y.2)
  set c : ℂ := ((2 * etaZ b E : ℝ) : ℂ) * Complex.I
  have hc : c ≠ 0 := by
    have : ((2 * etaZ b E : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : 2 * etaZ b E ≠ 0)
    exact mul_ne_zero this Complex.I_ne_zero
  have hres : twoPortResolvent b E (b3ChainXX b E s h W n y) = c⁻¹ • (1 - U) := by
    have e : boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
        b3ChainXX b E s h W n y = c • (1 - U)⁻¹ := by
      change boundaryZ b E • 1 - (boundaryZ b E • 1 - c • (1 - U)⁻¹) = _
      abel
    rw [twoPortResolvent, e]
    refine Matrix.inv_eq_left_inv ?_
    rw [smul_mul_smul, mul_nonsing_inv _ hD, inv_mul_cancel₀ hc, one_smul]
  change 1 - c • twoPortResolvent b E (b3ChainXX b E s h W n y) = U
  rw [hres, smul_smul, mul_inv_cancel₀ hc, one_smul, sub_sub_cancel]

/-- `P𝕊_pad = P𝕊C(1 - A)`. -/
theorem nearPortProj_mul_b3PadScatter (b E s h : ℝ) (n : ℕ) (ω : GrowthPath W) (z : ℂ) :
    ClosedLimit.nearPortProj W * b3PadScatter b E s h W n ω z =
      ClosedLimit.nearPortProj W * scatteringMatrix b E W n ω *
        physClosingMapAt b E s h W n ω z *
        (1 - farEmbed (omittedProj b E h W (closeLen s W) ω)) := by
  have hP : ClosedLimit.nearPortProj W * (farEmbed (closingPairing b E h W (closeLen s W) ω))ᴴ =
      0 := by
    rw [farEmbed_conjTranspose]; exact B3Cur.nearPortProj_mul_farEmbed _
  change ClosedLimit.nearPortProj W *
      ((1 - (farEmbed (closingPairing b E h W (closeLen s W) ω))ᴴ *
          farEmbed (closingPairing b E h W (closeLen s W) ω)) * scatteringMatrix b E W n ω *
        physClosingMapAt b E s h W n ω z *
          (1 - farEmbed (omittedProj b E h W (closeLen s W) ω)) +
        (farEmbed (closingPairing b E h W (closeLen s W) ω))ᴴ *
          farEmbed (omittedProj b E h W (closeLen s W) ω)) = _
  have hPO : ClosedLimit.nearPortProj W *
      (1 - (farEmbed (closingPairing b E h W (closeLen s W) ω))ᴴ *
        farEmbed (closingPairing b E h W (closeLen s W) ω)) = ClosedLimit.nearPortProj W := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hP, Matrix.zero_mul, sub_zero]
  rw [Matrix.mul_add, ← Matrix.mul_assoc (ClosedLimit.nearPortProj W) (farEmbed _)ᴴ, hP,
    Matrix.zero_mul, add_zero, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPO]

/-- **Closed columns are retained inputs**: `AV_n = 0`. -/
theorem A_mul_b3ClosedFrameAt (b E s h : ℝ) (τ m : Fin np → ℝ) (n : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (y : ProbedPath W np × ℝ) :
    farEmbed (omittedProj b E h W (closeLen s W) y.1.1) * b3ClosedFrameAt b E s h τ m W n Vs y =
      0 := by
  set A := farEmbed (omittedProj b E h W (closeLen s W) y.1.1)
  have hAH : Aᴴ = A := by rw [farEmbed_conjTranspose, omittedProj_conjTranspose]
  have hAA : A * A = A := by rw [farEmbed_mul, omittedProj_mul_self]
  have h1 : A * (physClosingMapAt b E s h W n y.1.1 (phase y.2))ᴴ = 0 := by
    have e : (physClosingMapAt b E s h W n y.1.1 (phase y.2) * A)ᴴ =
        A * (physClosingMapAt b E s h W n y.1.1 (phase y.2))ᴴ := by
      rw [conjTranspose_mul, hAH]
    rw [← e]
    change (closingMap _ A _ _ * A)ᴴ = 0
    rw [closingMap_mul_A' hAA, conjTranspose_zero]
  rw [b3ClosedFrameAt, ← Matrix.mul_assoc, h1, Matrix.zero_mul]

/-- **The separators of the Cayley state on the closed frame are `b3ContrSep`.** -/
theorem b3SepAt_b3ChainXX {b E s h : ℝ} (τ m : Fin np → ℝ) {n : ℕ}
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) {y : ProbedPath W np × ℝ}
    (hη : 0 < etaZ b E) (hD : IsUnit (1 - b3PadScatter b E s h W n y.1.1 (phase y.2)).det) :
    B3SepAt b E s h τ m W n Vs (b3ChainXX b E s h W n y) y := by
  set A := farEmbed (omittedProj b E h W (closeLen s W) y.1.1)
  have hAH : Aᴴ = A := by rw [farEmbed_conjTranspose, omittedProj_conjTranspose]
  have hAP : (1 - A) * ClosedLimit.nearPortProj W = ClosedLimit.nearPortProj W := by
    rw [Matrix.sub_mul, Matrix.one_mul, farEmbed_mul_nearPortProj, sub_zero]
  have hPA : ClosedLimit.nearPortProj W * (1 - A) = ClosedLimit.nearPortProj W := by
    rw [Matrix.mul_sub, Matrix.mul_one, B3Cur.nearPortProj_mul_farEmbed, sub_zero]
  obtain ⟨h0, h1, h2, h3⟩ := sep_core (U := b3PadScatter b E s h W n y.1.1 (phase y.2))
    (V := b3ClosedFrameAt b E s h τ m W n Vs y) nearPortProj_conjTranspose hAH
    (nearPortProj_mul_b3PadScatter b E s h n y.1.1 (phase y.2))
    (A_mul_b3ClosedFrameAt b E s h τ m n Vs y) hAP hPA
  intro σ
  have hS := twoPortScattering_b3ChainXX (s := s) (h := h) (n := n) (y := y) hη hD
  fin_cases σ
  · simp only [b3ContrSep, b3ClosedPS, contrSepOf, sepOf, hS]; exact h0
  · simp only [b3ContrSep, b3ClosedPS, contrSepOf, sepOf, hS]; exact h1
  · simp only [b3ContrSep, b3ClosedPS, contrSepOf, sepOf, hS]; exact h2
  · simp only [b3ContrSep, b3ClosedPS, contrSepOf, sepOf, hS]; exact h3

/-- **`contrGram` at the Cayley state is the closed contracting sum `b3CovZ`.** -/
theorem contrGram_b3ChainXX {b E s h : ℝ} (τ m : Fin np → ℝ) {n : ℕ}
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) {y : ProbedPath W np × ℝ}
    (hη : 0 < etaZ b E) (hD : IsUnit (1 - b3PadScatter b E s h W n y.1.1 (phase y.2)).det) :
    contrGram b E (b3ChainXX b E s h W n y) (b3ClosedFrameAt b E s h τ m W n Vs y) =
      b3CovZ b E np τ m s h K W Vs n y := by
  have hsep := b3SepAt_b3ChainXX τ m Vs hη hD
  have hsum : ∀ f : Separator → ℝ, ∑ σ ∈ contrSepSet, f σ = ∑ i : Fin 4, f (contrSepOf i) := by
    intro f
    simp [contrSepSet, contrSepOf, Fin.sum_univ_four, add_assoc]
  rw [contrGram, hsum, b3CovZ, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  simp only [b3ContrCoord, hsep σ]

/-- The current of the Cayley state. -/
theorem currentOf_b3ChainXX {b E s h : ℝ} {n : ℕ} {y : ProbedPath W np × ℝ}
    (hη : 0 < etaZ b E) (hD : IsUnit (1 - b3PadScatter b E s h W n y.1.1 (phase y.2)).det) :
    currentOf b E (b3ChainXX b E s h W n y) =
      (ClosedLimit.nearPortProj W * scatteringMatrix b E W n y.1.1 *
          physClosingMapAt b E s h W n y.1.1 (phase y.2) *
          (1 - farEmbed (omittedProj b E h W (closeLen s W) y.1.1)))ᴴ *
        (ClosedLimit.nearPortProj W * scatteringMatrix b E W n y.1.1 *
          physClosingMapAt b E s h W n y.1.1 (phase y.2) *
          (1 - farEmbed (omittedProj b E h W (closeLen s W) y.1.1))) -
        ClosedLimit.nearPortProj W := by
  rw [← nearPortProj_mul_b3PadScatter]
  set U := b3PadScatter b E s h W n y.1.1 (phase y.2)
  rw [currentOf, twoPortScattering_b3ChainXX hη hD]
  change Uᴴ * ClosedLimit.nearPortProj W * U - ClosedLimit.nearPortProj W =
    (ClosedLimit.nearPortProj W * U)ᴴ * (ClosedLimit.nearPortProj W * U) -
      ClosedLimit.nearPortProj W
  congr 1
  rw [conjTranspose_mul, nearPortProj_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (ClosedLimit.nearPortProj W) (ClosedLimit.nearPortProj W),
    nearPortProj_mul_self]

theorem measurable_b3ChainXX (b E s h : ℝ) (n : ℕ) :
    Measurable (b3ChainXX (np := np) b E s h W n) := by
  have hω : Measurable fun y : ProbedPath W np × ℝ => y.1.1 := measurable_fst.comp measurable_fst
  have hz : Measurable fun y : ProbedPath W np × ℝ => phase y.2 :=
    measurable_phase.comp measurable_snd
  have hS := (measurable_scatteringMatrix b E n).comp hω
  have hA := measurable_farEmbed ((measurable_omittedProj b E h (closeLen s W)).comp hω)
  have hP := measurable_farEmbed ((measurable_closingPairing b E h (closeLen s W)).comp hω)
  have hC := measurable_physClosingMapAt_comp b E s h n hω hz
  have hPh := measurable_matrix_conjTranspose' hP
  have hU : Measurable fun y : ProbedPath W np × ℝ =>
      b3PadScatter b E s h W n y.1.1 (phase y.2) :=
    measurable_matrix_add (measurable_matrix_mul' (measurable_matrix_mul' (measurable_matrix_mul'
      (measurable_matrix_sub measurable_const (measurable_matrix_mul' hPh hP)) hS) hC)
      (measurable_matrix_sub measurable_const hA)) (measurable_matrix_mul' hPh hA)
  exact measurable_matrix_sub measurable_const (measurable_matrix_cmul measurable_const
    (measurable_matrix_inv.comp (measurable_matrix_sub measurable_const hU)))

theorem b3ChainXX_b3Ext {b E s h : ℝ} {n j : ℕ} (hs : closeLen s W ≤ n) (hnj : n ≤ j)
    (y : ProbedPath W np × ℝ) :
    b3ChainXX b E s h W n (b3Ext W j y) = b3ChainXX b E s h W n y := by
  simp only [b3Ext, b3ChainXX, b3PadScatter, ClosedSumProof.scatteringMatrix_extPast hnj,
    Modul.omittedProj_extPast b E h (hs.trans hnj),
    Modul.closingPairing_extPast b E h (hs.trans hnj),
    Modul.physClosingMapAt_extPast s h hs hnj]

/-!
## The estimates
-/

/-- **`B3PadInvertible`**: a.s. invertibility of `1 - zN_n` and `1 - 𝕊_pad(n)`. -/
def B3PadInvertible : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ᶠ W in atTop, ∀ n, closeLen s W ≤ n →
      ∀ᵐ y ∂closedLaw b W np,
        IsUnit (1 - phase y.2 • closingN (scatteringMatrix b E W n y.1.1)
          (farEmbed (omittedProj b E h W (closeLen s W) y.1.1))
          (farEmbed (closingPairing b E h W (closeLen s W) y.1.1))).det ∧
        IsUnit (1 - b3PadScatter b E s h W n y.1.1 (phase y.2)).det

/-- **`B3PadTransport`**: the closed frame is transported by the Cayley state. -/
def B3PadTransport : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ,
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W,
      ∀ᵐ y ∂closedLaw b W np, y ∈ b3Alive b E s h τ m R W j (Vs W) →
        b3ClosedFrameAt b E s h τ m W (j + 1) (Vs W) y =
          (freshTransport b E (b3ChainXX b E s h W j y) (freshSample W j y.1.1))ᴴ *
            b3ClosedFrameAt b E s h τ m W j (Vs W) y

/-- **`B3ClosedCurrentFrame`** (witness-free): the closed current is carried by the
closed frame. -/
def B3ClosedCurrentFrame : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ,
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W,
      ∀ᵐ y ∂closedLaw b W np, y ∈ b3Alive b E s h τ m R W j (Vs W) →
        (ClosedLimit.nearPortProj W * scatteringMatrix b E W j y.1.1 *
            physClosingMapAt b E s h W j y.1.1 (phase y.2) *
            (1 - farEmbed (omittedProj b E h W (closeLen s W) y.1.1)))ᴴ *
          (ClosedLimit.nearPortProj W * scatteringMatrix b E W j y.1.1 *
            physClosingMapAt b E s h W j y.1.1 (phase y.2) *
            (1 - farEmbed (omittedProj b E h W (closeLen s W) y.1.1))) -
          ClosedLimit.nearPortProj W =
        b3ClosedFrameAt b E s h τ m W j (Vs W) y * srcSignature K (Fin np) *
          (b3ClosedFrameAt b E s h τ m W j (Vs W) y)ᴴ

/-- **`B3PadGrowth`**: the Cayley state grows by the fresh Schur step. -/
def B3PadGrowth : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ,
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W,
      ∀ᵐ y ∂closedLaw b W np, y ∈ b3Alive b E s h τ m R W j (Vs W) →
        b3ChainXX b E s h W (j + 1) y =
          freshTwoPortSchur E (b3ChainXX b E s h W j y) (freshSample W j y.1.1)

/-!
## The reductions
-/

/-- `𝕊_n` is unitary a.s. under the closed law, at every length. -/
theorem ae_closed_scattering_unitary {b E : ℝ} (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hW : 1 ≤ W) :
    ∀ᵐ y ∂closedLaw b W np, ∀ n,
      (scatteringMatrix b E W n y.1.1)ᴴ * scatteringMatrix b E W n y.1.1 = 1 := by
  have hq : Measure.QuasiMeasurePreserving (fun y : ProbedPath W np × ℝ => y.1.1)
      (closedLaw b W np) (growthPathLaw W b) :=
    (Measure.quasiMeasurePreserving_fst (μ := growthPathLaw W b)).comp
      (Measure.quasiMeasurePreserving_fst (μ := probedPathLaw W np b))
  exact hq.ae (p := fun ω => ∀ n,
      (scatteringMatrix b E W n ω)ᴴ * scatteringMatrix b E W n ω = 1)
    (by filter_upwards [ae_scattering_unitary hb hE1 hE2 hW] with ω h n
        exact mul_eq_one_comm.mp (h n).1)

theorem frameDomain_facts {b E : ℝ} {np : ℕ} {τ m : Fin np → ℝ} {T s h : ℝ} {K : ℕ}
    {Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hF : FrameDomain b E τ m T s h K Vs) :
    b < 1 / 2 ∧ -2 < E ∧ E < 2 ∧ 0 < etaZ b E ∧ h ^ 2 < 1 := by
  obtain ⟨⟨hb0, hb, hE1, hE2, -⟩, -, -, hh0, hh1, -⟩ := hF
  refine ⟨hb, hE1, hE2, boundaryZ_im_pos (b := b) (by linarith) hE1 hE2, ?_⟩
  nlinarith

/-- **`B3CayleyChain` from the estimates.** -/
theorem b3CayleyChain_of_pad (hI : B3PadInvertible) (hT : B3PadTransport)
    (hJ : B3ClosedCurrentFrame) : B3CayleyChain := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨hb, hE1, hE2, hη, hh⟩ := frameDomain_facts hF
  filter_upwards [hI b E np τ m T s h K Vs hF, hT b E np τ m T s h K Vs hF R,
    hJ b E np τ m T s h K Vs hF R, eventually_ge_atTop 1] with W hIW hTW hJW hW j hj
  have hjc : closeLen s W ≤ j := (Finset.mem_Ico.mp (Finset.mem_filter.mp hj).1).1
  refine ⟨measurable_b3ChainXX b E s h j, fun y => b3ChainXX_b3Ext hjc le_rfl y, ?_⟩
  filter_upwards [hIW j hjc, hTW j hj, hJW j hj, ae_closed_scattering_unitary hb hE1 hE2 hW]
    with y hIy hTy hJy hSy hyA
  obtain ⟨hHerm, hNS⟩ := b3ChainXX_good τ m hη hh (hSy j) hIy.1 hIy.2
  refine ⟨hHerm, hNS, hTy hyA, ?_, ?_⟩
  · rw [currentOf_b3ChainXX hη hIy.2]; exact hJy hyA
  · rw [contrGram_b3ChainXX τ m (Vs W) hη hIy.2, one_mul]

/-- **`B3CayleySep` from the estimates.** -/
theorem b3CayleySep_of_pad (hI : B3PadInvertible) (hG : B3PadGrowth) : B3CayleySep := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨-, -, -, hη, -⟩ := frameDomain_facts hF
  filter_upwards [hI b E np τ m T s h K Vs hF, hG b E np τ m T s h K Vs hF R] with
    W hIW hGW j hj
  have hjc : closeLen s W ≤ j := (Finset.mem_Ico.mp (Finset.mem_filter.mp hj).1).1
  filter_upwards [hIW j hjc, hIW (j + 1) (hjc.trans (Nat.le_succ j)), hGW j hj] with
    y h0 h1 hg hyA
  exact ⟨b3SepAt_b3ChainXX τ m (Vs W) hη h0.2, hg hyA, b3SepAt_b3ChainXX τ m (Vs W) hη h1.2⟩

end BlockBand.SourceProcess.PhysApprox.B3LayerMean
