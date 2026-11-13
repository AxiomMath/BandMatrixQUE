module

public import BlockBand.SourceProcess.PhysApprox.B3LayerKTrans
public import BlockBand.SourceProcess.PhysApprox.B3LayerMeanPadZ

/-!
# The phase-`z` padding: `B3PadGrowthZ` and `B3PadTransportZ`

The phase-`z` padding `zΠᴴA` is the far padding `Q = farEmbed(zΠ₀ᴴ)` of `padScatQ`
(`padScatZ_eq_padScatQ`), so the deterministic commutations `cay_padScatQ_freshTwoPortSchur` and
`closingMap_mul_freshTransport` apply; the a.s. invertibility of `1 - 𝕊'_pad` is
`ae_isUnit_one_sub_b3PadScatterZ`, that of `1 - zN` is `ae_closedPhase_good`.

* **`b3PadGrowthZ_holds : B3PadGrowthZ`** (no hypothesis);
* **`b3PadTransportZ_holds : B3PadTransportZ`** (no hypothesis).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.CompleteSourceGap BlockBand.SourceProcess.Closing
open BlockBand.SourceProcess.ClosedPath BlockBand.Transmission.Bridge
open BlockBand.Transmission
open BlockBand.SourceProcess.FullSourceStops

variable {W np K : ℕ}

theorem padScatZ_eq_padScatQ {ι : Type*} [Fintype ι] [DecidableEq ι] (S A Pi : Matrix ι ι ℂ)
    (z : ℂ) : B3LayerMean.padScatZ S A Pi z = padScatQ S A Pi (z • Piᴴ) z := by
  rw [B3LayerMean.padScatZ, padScatQ, Matrix.smul_mul]

theorem farEmbed_smul (c : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) :
    c • farEmbed X = farEmbed (c • X) := by
  ext x y
  simp only [farEmbed, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  split_ifs <;> simp

/-- `b3ChainXXz` in Cayley form over the path two-port. -/
theorem b3ChainXXz_eq_cay (b E s h : ℝ) (W n : ℕ) (y : ProbedPath W np × ℝ)
    (hF : IsUnit (pathMatrix (pathAt W n y.1.1) - (E : ℂ) • 1)) :
    B3LayerMean.b3ChainXXz b E s h W n y =
      boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
        (((2 * etaZ b E : ℝ) : ℂ) * Complex.I) •
          (1 - padScatQ (twoPortScattering b E (pathSchur E (pathAt W n y.1.1)))
            (farEmbed (omittedProj b E h W (closeLen s W) y.1.1))
            (farEmbed (closingPairing b E h W (closeLen s W) y.1.1))
            (farEmbed (phase y.2 • (closingPairing b E h W (closeLen s W) y.1.1)ᴴ))
            (phase y.2))⁻¹ := by
  rw [B3LayerMean.b3ChainXXz, B3LayerMean.b3PadScatterZ, padScatZ_eq_padScatQ,
    farEmbed_conjTranspose, farEmbed_smul, scatteringMatrix_eq b E n y.1.1 hF]

theorem one_sub_b3PadScatterZ_eq (b E s h : ℝ) (W n : ℕ) (y : ProbedPath W np × ℝ)
    (hF : IsUnit (pathMatrix (pathAt W n y.1.1) - (E : ℂ) • 1)) :
    1 - B3LayerMean.b3PadScatterZ b E s h W n y.1.1 (phase y.2) =
      1 - padScatQ (twoPortScattering b E (pathSchur E (pathAt W n y.1.1)))
        (farEmbed (omittedProj b E h W (closeLen s W) y.1.1))
        (farEmbed (closingPairing b E h W (closeLen s W) y.1.1))
        (farEmbed (phase y.2 • (closingPairing b E h W (closeLen s W) y.1.1)ᴴ)) (phase y.2) := by
  rw [B3LayerMean.b3PadScatterZ, padScatZ_eq_padScatQ, farEmbed_conjTranspose, farEmbed_smul,
    scatteringMatrix_eq b E n y.1.1 hF]

/-- **`B3PadGrowthZ` holds.** -/
theorem b3PadGrowthZ_holds : B3LayerMean.B3PadGrowthZ := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨hb, hE1, hE2, hη, hh⟩ := B3LayerMean.frameDomain_facts hF
  have hb0 : 0 < b := hF.1.1
  have hηim : 0 < (boundaryZ b E).im := boundaryZ_im_pos (b := b) (by linarith) hE1 hE2
  filter_upwards [eventually_ge_atTop 1, B3Cur.eventually_one_le_closeLen hF.2.1] with
    W hW hs1 j hj
  have hjc : closeLen s W ≤ j := (Finset.mem_Ico.mp (Finset.mem_filter.mp hj).1).1
  have hj1 : 1 ≤ j := hs1.trans hjc
  have hZm := B3LayerMean.measurable_b3ChainXXz (np := np) (W := W) b E s h j
  have hZinv : ∀ y : ProbedPath W np × ℝ, B3LayerMean.b3ChainXXz b E s h W j (b3Ext W j y) =
      B3LayerMean.b3ChainXXz b E s h W j y := fun y => B3LayerMean.b3ChainXXz_b3Ext hjc le_rfl y
  filter_upwards [B3LayerMean.ae_isUnit_one_sub_b3PadScatterZ (np := np) hb hE1 hE2 s h hh hW j,
    B3LayerMean.ae_isUnit_one_sub_b3PadScatterZ (np := np) hb hE1 hE2 s h hh hW (j + 1),
    ae_closedPhase_good (W := W) (np := np) b E s h j,
    ae_closedPath_good (np := np) hb0 hb hE1 hE2 hW, ae_closed_pathSchur_succ (np := np) hb hW E,
    ae_isUnit_freshPivot hb hW E j hZm hZinv] with y hV hVg hPh hP hsucc hGp _hyA
  obtain ⟨hA, hFp, -, -⟩ := hP
  set Y := pathSchur E (pathAt W j y.1.1) with hYdef
  have hsj := hsucc j hj1
  have hK : IsUnit (boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - Y) :=
    portPencil_isUnit _ (pathSchur_isHermitian E j y.1.1 hA) hηim
  have hKg : IsUnit (boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
      freshTwoPortSchur E Y (freshSample W j y.1.1)) := by
    rw [← hsj]
    exact portPencil_isUnit _ (pathSchur_isHermitian E (j + 1) y.1.1 hA) hηim
  have hG := isUnit_freshPivot_path E y.1.1 (hFp j) (hFp (j + 1))
  have e0 := b3ChainXXz_eq_cay b E s h W j y (hFp j)
  have e1 := b3ChainXXz_eq_cay b E s h W (j + 1) y (hFp (j + 1))
  rw [hsj] at e1
  have hU := isUnit_iff_ne_zero.2 hPh.1
  have hUg := isUnit_iff_ne_zero.2 hPh.2.1
  rw [scatteringMatrix_eq b E j y.1.1 (hFp j)] at hU
  rw [scatteringMatrix_eq b E (j + 1) y.1.1 (hFp (j + 1)), hsj] at hUg
  rw [one_sub_b3PadScatterZ_eq b E s h W j y (hFp j)] at hV
  rw [one_sub_b3PadScatterZ_eq b E s h W (j + 1) y (hFp (j + 1)), hsj] at hVg
  rw [e0] at hGp
  rw [e1, e0]
  exact cay_padScatQ_freshTwoPortSchur b E hη (omittedProj_mul_self b E h _ _)
    (omittedProj_mul_closingPairing b E h _ _) (phase y.2) Y (freshSample W j y.1.1) hK hKg hG
    hU hUg hV hVg hGp

/-- **`B3PadTransportZ` holds.** -/
theorem b3PadTransportZ_holds : B3LayerMean.B3PadTransportZ := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨hb, hE1, hE2, hη, hh⟩ := B3LayerMean.frameDomain_facts hF
  have hb0 : 0 < b := hF.1.1
  have hηim : 0 < (boundaryZ b E).im := boundaryZ_im_pos (b := b) (by linarith) hE1 hE2
  filter_upwards [eventually_ge_atTop 1, B3Cur.eventually_one_le_closeLen hF.2.1] with
    W hW hs1 j hj
  have hjc : closeLen s W ≤ j := (Finset.mem_Ico.mp (Finset.mem_filter.mp hj).1).1
  have hj1 : 1 ≤ j := hs1.trans hjc
  have hnb : ∀ k : Fin np, ⌊(W : ℝ) * τ k⌋₊ ≠ j := fun k h' =>
    (Finset.mem_filter.mp hj).2 ⟨k, h'⟩
  have hZm := B3LayerMean.measurable_b3ChainXXz (np := np) (W := W) b E s h j
  have hZinv : ∀ y : ProbedPath W np × ℝ, B3LayerMean.b3ChainXXz b E s h W j (b3Ext W j y) =
      B3LayerMean.b3ChainXXz b E s h W j y := fun y => B3LayerMean.b3ChainXXz_b3Ext hjc le_rfl y
  filter_upwards [B3LayerMean.ae_isUnit_one_sub_b3PadScatterZ (np := np) hb hE1 hE2 s h hh hW j,
    ae_closedPhase_good (W := W) (np := np) b E s h j,
    ae_closedPath_good (np := np) hb0 hb hE1 hE2 hW, ae_closed_pathSchur_succ (np := np) hb hW E,
    ae_isUnit_freshPivot hb hW E j hZm hZinv,
    B3LayerMean.ae_closed_scattering_unitary (np := np) hb hE1 hE2 hW] with y hD hPh hP hsucc
    hGp hSu _hyA
  obtain ⟨hA, hFp, hBd, -⟩ := hP
  set Y := pathSchur E (pathAt W j y.1.1) with hYdef
  have hsj := hsucc j hj1
  have hK : IsUnit (boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - Y) :=
    portPencil_isUnit _ (pathSchur_isHermitian E j y.1.1 hA) hηim
  have hKg : IsUnit (boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
      freshTwoPortSchur E Y (freshSample W j y.1.1)) := by
    rw [← hsj]
    exact portPencil_isUnit _ (pathSchur_isHermitian E (j + 1) y.1.1 hA) hηim
  have hG := isUnit_freshPivot_path E y.1.1 (hFp j) (hFp (j + 1))
  have hXH := (B3LayerMean.b3ChainXXz_good τ m hη hh (hSu j) (isUnit_iff_ne_zero.2 hPh.1) hD).1
  have e0 := b3ChainXXz_eq_cay b E s h W j y (hFp j)
  have hU := isUnit_iff_ne_zero.2 hPh.1
  have hUg := isUnit_iff_ne_zero.2 hPh.2.1
  have hV := hD
  rw [scatteringMatrix_eq b E j y.1.1 (hFp j)] at hU
  rw [scatteringMatrix_eq b E (j + 1) y.1.1 (hFp (j + 1)), hsj] at hUg
  rw [one_sub_b3PadScatterZ_eq b E s h W j y (hFp j)] at hV
  rw [e0] at hGp hXH
  rw [e0]
  have key := closingMap_mul_freshTransport b E hη (omittedProj_mul_self b E h _ _)
    (omittedProj_mul_closingPairing b E h _ _) (phase y.2) Y (freshSample W j y.1.1)
    (pathSchur_isHermitian E j y.1.1 hA) (hA j) (hBd (j + 1)) hK hKg hG hU hUg hV hXH hGp
  set A := farEmbed (omittedProj b E h W (closeLen s W) y.1.1) with hAdef
  have hA2 : A * A = A := by rw [hAdef, farEmbed_mul, omittedProj_mul_self]
  have hAH : Aᴴ = A := by rw [hAdef, farEmbed_conjTranspose, omittedProj_conjTranspose]
  set Pi := farEmbed (closingPairing b E h W (closeLen s W) y.1.1) with hPidef
  have hfr := b3OpenFrameAt_succ b E s τ m hj1 hjc hnb (Vs W) y.1 hA hηim (hFp j) (hFp (j + 1))
    (hBd (j + 1))
  have hC0 : physClosingMapAt b E s h W j y.1.1 (phase y.2) =
      closingMap (twoPortScattering b E Y) A Pi (phase y.2) := by
    rw [physClosingMapAt, scatteringMatrix_eq b E j y.1.1 (hFp j)]
  have hC1 : physClosingMapAt b E s h W (j + 1) y.1.1 (phase y.2) =
      closingMap (twoPortScattering b E (freshTwoPortSchur E Y (freshSample W j y.1.1))) A Pi
        (phase y.2) := by
    rw [physClosingMapAt, scatteringMatrix_eq b E (j + 1) y.1.1 (hFp (j + 1)), hsj]
  have hadj := congrArg conjTranspose key
  simp only [conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hAH] at hadj
  have e0' := congrArg conjTranspose
    (closingMap_mul_one_sub (S := twoPortScattering b E Y) (Pi := Pi) hA2 (phase y.2))
  rw [conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hAH] at e0'
  have e1' := congrArg conjTranspose (closingMap_mul_one_sub
    (S := twoPortScattering b E (freshTwoPortSchur E Y (freshSample W j y.1.1))) (Pi := Pi) hA2
    (phase y.2))
  rw [conjTranspose_mul, conjTranspose_sub, conjTranspose_one, hAH] at e1'
  rw [e0', ← Matrix.mul_assoc, e1'] at hadj
  unfold b3ClosedFrameAt
  rw [hfr, hC0, hC1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hadj]

end BlockBand.SourceProcess.PhysApprox.B3
