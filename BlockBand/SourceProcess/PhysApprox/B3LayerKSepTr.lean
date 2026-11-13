module

public import BlockBand.SourceProcess.PhysApprox.B3LayerKSepAlg
public import BlockBand.SourceProcess.CompleteSourceGap.GapIdentity
public import BlockBand.SourceProcess.FullSource.WardNoise
public import BlockBand.Transmission.Bridge.Discharge

/-!
# The fresh transport on waves; closing commutes with the transport

* `transport_wave`: for linked waves, `(ζ - Z)w = N(ζ - Φ_FZ)v`, `N` the fresh transport.
* `closingMap_mul_freshTransport` (deterministic, general far padding): the closing map commutes
  with the fresh transport, `C_j(z)(1 - A)N(Cay 𝕊_pad, F) = N(Y, F)C_{j+1}(z)(1 - A)` for Hermitian
  `Y` and `Cay 𝕊_pad`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.SourceProcess.CompleteSourceGap BlockBand.SourceProcess.Closing
open BlockBand.SourceProcess.ClosedPath BlockBand.Transmission.Bridge
open BlockBand.Transmission.PassiveLayer
open scoped ComplexOrder

variable {W : ℕ}

/-- **The fresh transport on waves**: `(ζ - Z)w = N(ζ - Φ_FZ)v` for linked waves. -/
theorem transport_wave (b E : ℝ) (hη : 0 < etaZ b E) {Z : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hZ : Z.IsHermitian) {F : LayerSample W .oneBlockOnePort} (hA : (F.1 0).IsHermitian)
    (hB : IsUnit (F.2 0 0)) (hG : IsUnit (freshPivot E Z F)) {v w : Fin 2 × Fin W → ℂ}
    (h : FreshLink E Z F v w) :
    (boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - Z) *ᵥ w =
      freshTransport b E Z F *ᵥ
        ((boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
          freshTwoPortSchur E Z F) *ᵥ v) := by
  set ζ := boundaryZ b E with hζdef
  have hz : 0 < ζ.im := hη
  set X := nearSchur ζ Z with hXdef
  set K := ζ • (1 : Matrix (Fin W) (Fin W) ℂ) - X with hKdef
  set D := ζ • (1 : Matrix (Fin W) (Fin W) ℂ) - portBlock Z 1 1 with hDdef
  have hY : (passiveY X).PosSemidef := FullSource.nearSchur_passive hz hZ
  have hM : IsUnit (layerMatrix .oneBlockOnePort E ζ (liftX X) F) := by
    rw [layerSample_eta F]
    exact isUnit_layerMatrix_fresh b E X _ _ hA hY hz hB
  obtain ⟨-, -, -, -, hL5, hL6, -, -⟩ := layer_identities E ζ X F hM
  have hK : IsUnit K := by
    apply BlockBand.Transmission.isUnit_of_matrixImaginaryPart_posDef
    rw [BlockBand.Transmission.PassiveCovariance.matrixImaginaryPart_nearPencil]
    exact Matrix.PosDef.posSemidef_add hY (Matrix.PosDef.one.smul hη)
  have hKK : K * K⁻¹ = 1 := mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hK)
  have hD : IsUnit D :=
    BlockBand.Transmission.portPencil_isUnit _ (FullSource.portBlock_isHermitian hZ 1) hz
  have hDD : D⁻¹ * D = 1 := nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hD)
  have hrow := nearRow_twoPortResolvent b E hZ hη
  have hR01 : portBlock (twoPortResolvent b E Z) 0 1 = passiveResolvent b E X *
      portBlock Z 0 1 * (ζ • (1 : Matrix (Fin W) (Fin W) ℂ) - portBlock Z 1 1)⁻¹ := by
    have := congrArg (fun ρ => colBlock ρ 1) hrow
    simpa [FullSource.colBlock_nearSel_mul, colBlock_rowOf] using this
  have hPR : passiveResolvent b E X = K⁻¹ := rfl
  rw [hPR, ← hDdef] at hR01
  have hN00 : portBlock (freshTransport b E Z F) 0 0 = freshL b E X F := by
    rw [FullSource.portBlock_freshTransport]; simp; rfl
  have hN01 : portBlock (freshTransport b E Z F) 0 1 =
      freshDelta b E X F * portBlock (twoPortResolvent b E Z) 0 1 := by
    rw [FullSource.portBlock_freshTransport]; simp; rfl
  have hN10 : portBlock (freshTransport b E Z F) 1 0 = 0 := by
    rw [FullSource.portBlock_freshTransport]; simp
  have hN11 : portBlock (freshTransport b E Z F) 1 1 = 1 := by
    rw [FullSource.portBlock_freshTransport]; simp
  obtain ⟨hf, hn⟩ := fresh_wave hG h
  set p := nP w
  set q := fP v
  set r := nP v
  set B := F.2 0 0
  set Af := F.1 0 - (E : ℂ) • 1 with hAfdef
  have hnu : nP ((ζ • 1 - freshTwoPortSchur E Z F) *ᵥ v) = ζ • r + Bᴴ *ᵥ p := by
    rw [sub_mulVec, smul_mulVec, one_mulVec, nP_sub, nP_smul, hn, sub_neg_eq_add]
  have hfu : fP ((ζ • 1 - freshTwoPortSchur E Z F) *ᵥ v) = D *ᵥ q - portBlock Z 1 0 *ᵥ p := by
    rw [sub_mulVec, smul_mulVec, one_mulVec, fP_sub, fP_smul, hf, fP_mulVec, h.1, hDdef,
      sub_mulVec, smul_mulVec, one_mulVec]
    abel
  have hZw := h.2
  rw [nP_mulVec, h.1] at hZw
  have hZ01 : portBlock Z 0 1 *ᵥ q = Af *ᵥ p + B *ᵥ r - portBlock Z 0 0 *ᵥ p := by
    rw [← hZw]; abel
  have hΔ : freshDelta b E X F = K * g11 E ζ X F * K - K := rfl
  have hL : freshL b E X F = K * g12 E ζ X F := rfl
  have hXs : X = portBlock Z 0 0 + portBlock Z 0 1 * D⁻¹ * portBlock Z 1 0 := rfl
  have hAX : Af - X = F.1 0 - (E : ℂ) • 1 - X := rfl
  clear_value K X D
  refine vec_ext ?_ ?_
  · rw [nP_mulVec (freshTransport b E Z F), hN00, hN01, hR01, hnu, hfu, sub_mulVec,
      smul_mulVec, one_mulVec, nP_sub, nP_smul, h.2]
    have e0 : freshDelta b E X F * (K⁻¹ * portBlock Z 0 1 * D⁻¹) =
        (K * g11 E ζ X F - 1) * portBlock Z 0 1 * D⁻¹ := by
      rw [hΔ, Matrix.sub_mul, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc K K⁻¹, hKK, Matrix.one_mul]
    have hDq : D⁻¹ *ᵥ (D *ᵥ q) = q := by rw [mulVec_mulVec, hDD, one_mulVec]
    have e3 : ((K * g11 E ζ X F - 1) * portBlock Z 0 1 * D⁻¹) *ᵥ (portBlock Z 1 0 *ᵥ p) =
        (K * g11 E ζ X F - 1) *ᵥ ((X - portBlock Z 0 0) *ᵥ p) := by
      have hX0 : X - portBlock Z 0 0 = portBlock Z 0 1 * D⁻¹ * portBlock Z 1 0 := by
        rw [hXs, add_sub_cancel_left]
      rw [hX0]
      simp only [← mulVec_mulVec]
    have e1 : (freshDelta b E X F * (K⁻¹ * portBlock Z 0 1 * D⁻¹)) *ᵥ
        (D *ᵥ q - portBlock Z 1 0 *ᵥ p) =
        (K * g11 E ζ X F - 1) *ᵥ ((Af - X) *ᵥ p + B *ᵥ r) := by
      rw [e0, mulVec_sub, e3, ← mulVec_mulVec, hDq, ← mulVec_mulVec, hZ01, ← mulVec_sub]
      congr 1
      rw [sub_mulVec, sub_mulVec, hAfdef, sub_mulVec, sub_mulVec]
      abel
    rw [e1, hL]
    have h5 := congrArg (fun M => (K * M) *ᵥ p) hL5
    have h6 := congrArg (fun M => (K * M) *ᵥ r) hL6
    simp only [Matrix.mul_add, add_mulVec, Matrix.mul_one, Matrix.mul_zero, zero_mulVec,
      ← Matrix.mul_assoc] at h5 h6
    rw [← hAX] at h5
    have h6' : (K * g11 E ζ X F * B) *ᵥ r = -((K * g12 E ζ X F * (ζ • 1)) *ᵥ r) :=
      eq_neg_of_add_eq_zero_left h6
    calc ζ • p - (Af *ᵥ p + B *ᵥ r) = K *ᵥ p - (Af - X) *ᵥ p - B *ᵥ r := by
          rw [hKdef]; simp only [sub_mulVec, smul_mulVec, one_mulVec]; abel
      _ = ((K * g11 E ζ X F * (Af - X)) *ᵥ p + (K * g12 E ζ X F * Bᴴ) *ᵥ p) +
            ((K * g11 E ζ X F * B) *ᵥ r + (K * g12 E ζ X F * (ζ • 1)) *ᵥ r) -
            (Af - X) *ᵥ p - B *ᵥ r := by
          rw [h5, h6', neg_add_cancel, add_zero]
      _ = (K * g12 E ζ X F) *ᵥ (ζ • r + Bᴴ *ᵥ p) +
            (K * g11 E ζ X F - 1) *ᵥ ((Af - X) *ᵥ p + B *ᵥ r) := by
          simp only [← mulVec_mulVec, mulVec_add, mulVec_smul, smul_mulVec, one_mulVec,
            sub_mulVec]
          abel
  · rw [fP_mulVec (freshTransport b E Z F), hN10, hN11, zero_mulVec, zero_add, one_mulVec, hfu,
      sub_mulVec, smul_mulVec, one_mulVec, fP_sub, fP_smul, fP_mulVec, h.1, hDdef, sub_mulVec,
      smul_mulVec, one_mulVec]
    abel

/-- **The closing commutes with the fresh transport** (deterministic, general far padding):
`C_j(z)(1 - A)N(Cay 𝕊_pad, F) = N(Y, F)C_{j+1}(z)(1 - A)` for Hermitian `Y` and `Cay 𝕊_pad`. -/
theorem closingMap_mul_freshTransport (b E : ℝ) (hη : 0 < etaZ b E)
    {A₀ P₀ Q₀ : Matrix (Fin W) (Fin W) ℂ} (hA2 : A₀ * A₀ = A₀) (hAP : A₀ * P₀ = P₀) (z : ℂ)
    (Y : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (F : LayerSample W .oneBlockOnePort)
    (hYH : Y.IsHermitian) (hAF : (F.1 0).IsHermitian) (hB : IsUnit (F.2 0 0))
    (hK : IsUnit (boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - Y))
    (hKg : IsUnit (boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
      freshTwoPortSchur E Y F))
    (hG : IsUnit (freshPivot E Y F))
    (hU : IsUnit (1 - z • closingN (twoPortScattering b E Y) (farEmbed A₀) (farEmbed P₀)).det)
    (hUg : IsUnit (1 - z • closingN (twoPortScattering b E (freshTwoPortSchur E Y F))
      (farEmbed A₀) (farEmbed P₀)).det)
    (hV : IsUnit (1 - padScatQ (twoPortScattering b E Y) (farEmbed A₀)
      (farEmbed P₀) (farEmbed Q₀) z).det)
    (hXH : (boundaryZ b E • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
      (((2 * etaZ b E : ℝ) : ℂ) * Complex.I) • (1 - padScatQ (twoPortScattering b E Y)
        (farEmbed A₀) (farEmbed P₀) (farEmbed Q₀) z)⁻¹).IsHermitian)
    (hGp : IsUnit (freshPivot E (boundaryZ b E • 1 - (((2 * etaZ b E : ℝ) : ℂ) * Complex.I) •
      (1 - padScatQ (twoPortScattering b E Y) (farEmbed A₀) (farEmbed P₀) (farEmbed Q₀) z)⁻¹) F)) :
    closingMap (twoPortScattering b E Y) (farEmbed A₀) (farEmbed P₀) z * (1 - farEmbed A₀) *
        freshTransport b E (boundaryZ b E • 1 - (((2 * etaZ b E : ℝ) : ℂ) * Complex.I) •
          (1 - padScatQ (twoPortScattering b E Y) (farEmbed A₀) (farEmbed P₀) (farEmbed Q₀)
            z)⁻¹) F =
      freshTransport b E Y F *
        closingMap (twoPortScattering b E (freshTwoPortSchur E Y F)) (farEmbed A₀)
          (farEmbed P₀) z * (1 - farEmbed A₀) := by
  set ζ := boundaryZ b E
  set c : ℂ := ((2 * etaZ b E : ℝ) : ℂ) * Complex.I with hcdef
  have hc : c ≠ 0 := by
    have : ((2 * etaZ b E : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : 2 * etaZ b E ≠ 0)
    exact mul_ne_zero this Complex.I_ne_zero
  set A := farEmbed A₀ with hAdef
  set Pi := farEmbed P₀ with hPidef
  have hA2' : A * A = A := by rw [hAdef, farEmbed_mul, hA2]
  have hAPi' : A * Pi = Pi := by rw [hAdef, hPidef, farEmbed_mul, hAP]
  have hPiH : Piᴴ = farEmbed P₀ᴴ := farEmbed_conjTranspose _
  have hO : Piᴴ * Pi = farEmbed (P₀ᴴ * P₀) := by rw [hPiH, farEmbed_mul]
  set Yp := freshTwoPortSchur E Y F
  set S := twoPortScattering b E Y with hSdef
  set Sg := twoPortScattering b E Yp with hSgdef
  set V := padScatQ S A Pi (farEmbed Q₀) z with hVdef
  set Vg := padScatQ Sg A Pi (farEmbed Q₀) z with hVgdef
  set X := ζ • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - c • (1 - V)⁻¹ with hXdef
  
  have hSw : ∀ w, S *ᵥ ((ζ • 1 - Y) *ᵥ w) = (ζ • 1 - Y) *ᵥ w - c • w := fun w => by
    show (1 - c • (ζ • 1 - Y)⁻¹) *ᵥ ((ζ • 1 - Y) *ᵥ w) = _
    rw [mulVec_mulVec, scat_wave hK, sub_mulVec, smul_mulVec, one_mulVec]
  have hSgw : ∀ w, Sg *ᵥ ((ζ • 1 - Yp) *ᵥ w) = (ζ • 1 - Yp) *ᵥ w - c • w := fun w => by
    show (1 - c • (ζ • 1 - Yp)⁻¹) *ᵥ ((ζ • 1 - Yp) *ᵥ w) = _
    rw [mulVec_mulVec, scat_wave hKg, sub_mulVec, smul_mulVec, one_mulVec]
  have hXHx : X.IsHermitian := hXH
  have hVw : ∀ w, V *ᵥ ((ζ • 1 - X) *ᵥ w) = (ζ • 1 - X) *ᵥ w - c • w := fun w => by
    rw [mulVec_mulVec, hXdef, cay_wave hV, sub_mulVec, smul_mulVec, one_mulVec]
  clear_value X
  have hηim : 0 < ζ.im := hη
  have hXg : IsUnit (ζ • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
      freshTwoPortSchur E X F) :=
    BlockBand.Transmission.portPencil_isUnit _ (freshTwoPortSchur_isHermitian E hXHx hAF) hηim
  refine Matrix.toLin'.injective (LinearMap.ext fun x => ?_)
  simp only [Matrix.toLin'_apply]
  rw [← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec]
  set v'' := (ζ • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
    freshTwoPortSchur E X F)⁻¹ *ᵥ x
  have hx : (ζ • 1 - freshTwoPortSchur E X F) *ᵥ v'' = x := by
    rw [mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hXg), one_mulVec]
  rw [← hx]
  clear_value v''
  
  obtain ⟨w', hw'⟩ := fresh_wave_exists E X F hGp v''
  obtain ⟨hf'', hn''⟩ := fresh_wave hGp hw'
  set a' := (ζ • 1 - X) *ᵥ w' with ha'def
  have hb' : V *ᵥ a' = a' - c • w' := hVw w'
  clear_value a'
  
  set a := closingMap S A Pi z *ᵥ ((1 - A) *ᵥ a') with hadef
  obtain ⟨hfb, hla⟩ := feedback_closingMap hA2' hAPi' hU a'
  set w := (ζ • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - Y)⁻¹ *ᵥ a with hwdef
  have haw : (ζ • 1 - Y) *ᵥ w = a := by
    rw [hwdef, mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hK), one_mulVec]
  have hVa : V *ᵥ a' = (1 - Piᴴ * Pi) *ᵥ (S *ᵥ a) + farEmbed Q₀ *ᵥ (A *ᵥ a') := by
    rw [hadef]
    simp only [hVdef, padScatQ, add_mulVec, ← mulVec_mulVec]
  have hna : nP a = nP a' := by
    rw [hadef, nP_closingMap_mulVec hU, sub_mulVec, one_mulVec, nP_sub, hAdef, nP_farEmbed,
      sub_zero]
  rw [← hadef] at hfb hla
  clear_value w a
  have hba : S *ᵥ a = a - c • w := by
    have := hSw w
    rwa [haw] at this
  -- near parts agree
  have hnV : nP (V *ᵥ a') = nP (S *ᵥ a) := by
    rw [hVa, nP_add, hO, nP_one_sub_farEmbed, nP_farEmbed, add_zero]
  have hnw : nP w = nP w' := by
    have h1 : nP a' - c • nP w' = nP a - c • nP w := by
      rw [← nP_smul, ← nP_sub, ← hb', hnV, hba, nP_sub, nP_smul]
    rw [hna] at h1
    have h2 : c • nP w = c • nP w' := by
      have := congrArg (fun t => nP a' - t) h1
      simp only [sub_sub_cancel] at this
      exact this.symm
    exact smul_right_injective _ hc h2
  have hYw : Y *ᵥ w = ζ • w - a := by
    rw [← haw, sub_mulVec, smul_mulVec, one_mulVec]; abel
  have hXw : X *ᵥ w' = ζ • w' - a' := by
    rw [ha'def, sub_mulVec, smul_mulVec, one_mulVec]; abel
  
  set vg := pVec (nP v'') (fP w) with hvgdef
  have hlink : FreshLink E Y F vg w := by
    refine ⟨by rw [hvgdef, fP_pVec], ?_⟩
    rw [hvgdef, nP_pVec, hnw, hYw, nP_sub, nP_smul, hnw, hna, ← nP_smul, ← nP_sub, ← hXw]
    exact hw'.2
  obtain ⟨hfg, hng⟩ := fresh_wave hG hlink
  set ag := (ζ • 1 - Yp) *ᵥ vg with hagdef
  have hbg : Sg *ᵥ ag = ag - c • vg := hSgw vg
  have hfag : fP ag = fP a := by
    rw [hagdef, sub_mulVec, smul_mulVec, one_mulVec, fP_sub, hfg, fP_smul, hvgdef, fP_pVec,
      hYw, fP_sub, fP_smul]
    abel
  set a'' := (ζ • 1 - freshTwoPortSchur E X F) *ᵥ v'' with ha''def
  have hna'' : nP a'' = nP ag := by
    rw [ha''def, hagdef, sub_mulVec, sub_mulVec, smul_mulVec, smul_mulVec, one_mulVec,
      one_mulVec, nP_sub, nP_sub, hn'', hng, nP_smul, nP_smul, hvgdef, nP_pVec, hnw]
  have hfa'' : fP a'' = fP a' := by
    rw [ha''def, sub_mulVec, smul_mulVec, one_mulVec, fP_sub, hf'', fP_smul, ← hw'.1, ha'def,
      sub_mulVec, smul_mulVec, one_mulVec, fP_sub, fP_smul]
  
  have hfeed : A *ᵥ ag = z • (Pi *ᵥ (Sg *ᵥ ag)) := by
    rw [hAdef, farEmbed_mulVec_congr A₀ hfag, ← hAdef, hfb, hba, hbg, hPidef]
    congr 1
    refine farEmbed_mulVec_congr P₀ ?_
    rw [fP_sub, fP_sub, fP_smul, fP_smul, hfag, hvgdef, fP_pVec]
  have hCg := closingMap_mulVec_of_feedback hA2' hUg hfeed
  have hlA : (1 - A) *ᵥ a'' = (1 - A) *ᵥ ag := by
    refine vec_ext ?_ ?_
    · rw [hAdef, nP_one_sub_farEmbed, nP_one_sub_farEmbed, hna'']
    · have := congrArg fP hla
      rw [hAdef, fP_one_sub_farEmbed, fP_one_sub_farEmbed] at this
      rw [hAdef, fP_one_sub_farEmbed, fP_one_sub_farEmbed, hfa'', hfag, this]
  have htX : a' = freshTransport b E X F *ᵥ a'' := by
    rw [ha'def, ha''def]
    exact transport_wave b E hη hXHx hAF hB hGp hw'
  have htY : (ζ • 1 - Y) *ᵥ w = freshTransport b E Y F *ᵥ ag := by
    rw [hagdef]
    exact transport_wave b E hη hYH hAF hB hG hlink
  rw [← htX, ← hadef, ← haw, htY, hlA, hCg]

end BlockBand.SourceProcess.PhysApprox.B3
