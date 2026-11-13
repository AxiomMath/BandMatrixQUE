module

public import BlockBand.Transmission.LawForced.AbsScalar
public import BlockBand.Transmission.LawForced.RatioBulk
public import BlockBand.Transmission.LawFinite.Drift

/-!
# One absorbed layer, bulk-uniform

`ratio_layer_bulk` applied at the shifted passive input `X' = X − iε` (the fresh layer of the
absorbed path is the unabsorbed fresh layer at `X'`), plus the deterministic shift
(`abs_layer_split`, `inShiftErr_le`, `ratioDrift_shift_le`, `driftShift_le`).

**`abs_layer_bulk hGA hLp hP`**: `b ∈ (0,1/2)`, `κ_I > 0`, a chamber point `z` and `K ≥ 0`
first; then `C ≥ 0, W₀`; for `W ≥ W₀`, `E ∈ bulkInterval κ_I`, every stationary jet `s`, every
passive `X`, every `0 ≤ ε ≤ K/W²`, every profile `κ` and time `u`:
`|E F_z(T((X − iε)₊)) − F_z(T(X)) − ratioDrift D₀ E κ u z μ_{T(X)}/W| ≤
C·ratioP(X − iε)²⁷·W^{-3/2} + R·|h(u)/W − 4ηd_*εW|`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open Matrix Finset MeasureTheory
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.LawDuality BlockBand.Transmission.Generator
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.LawFinite
open BlockBand.Transmission.PathScalar
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {p W : ℕ}

theorem ratioP_facts {b E : ℝ} (s : ℂ) (X : Matrix (Fin W) (Fin W) ℂ)
    (hg : 0 ≤ (passiveTransmission b E X).trace.re) :
    1 ≤ ratioP b E s X ∧
      ((passiveTransmission b E X).trace.re + 1) ^ 3 * (W * jetDistance0 b E X + 1) ≤
        ratioP b E s X ^ 27 := by
  set A := (passiveTransmission b E X).trace.re + 1
  set D := (W : ℝ) * jetDistance0 b E X + 1
  set M3 := Real.sqrt W * (‖(passiveQ b E X * passiveF b E X).trace‖ +
    hsSandwich (passiveQ b E X) (passiveF b E X)) + 1
  set M4 := (W : ℝ) * jetDistance1 b E s X + 1
  have hA : 1 ≤ A := by simp only [A]; linarith
  have hD : 1 ≤ D := by
    have := mul_nonneg (Nat.cast_nonneg W) (norm_nonneg ((W : ℂ)⁻¹ *
      (passiveResolvent b E X).trace - matchedA E))
    simp only [D, jetDistance0]; linarith
  have h3 : 1 ≤ M3 := by
    have := mul_nonneg (Real.sqrt_nonneg (W : ℝ)) (add_nonneg (norm_nonneg
      (passiveQ b E X * passiveF b E X).trace) (Real.sqrt_nonneg
        ((passiveQ b E X) * passiveF b E X * passiveQ b E X * (passiveF b E X)ᴴ).trace.re))
    simp only [M3, hsSandwich]; linarith
  have h4 : 1 ≤ M4 := by
    have := mul_nonneg (Nat.cast_nonneg W) (norm_nonneg (deriv (fun w : ℂ => (W : ℂ)⁻¹ *
      ((w • (1 : Matrix (Fin W) (Fin W) ℂ) - X)⁻¹).trace) (boundaryZ b E) - s))
    simp only [M4, jetDistance1]; linarith
  have e : ratioP b E s X = A * D * M3 * M4 := rfl
  have hAD : A * D ≤ ratioP b E s X := by
    rw [e]
    have : 1 ≤ M3 * M4 := one_le_mul_of_one_le_of_one_le h3 h4
    have h0 : 0 ≤ A * D := by positivity
    nlinarith
  have hP1 : 1 ≤ ratioP b E s X := le_trans (one_le_mul_of_one_le_of_one_le hA hD) hAD
  refine ⟨hP1, ?_⟩
  have hAP : A ≤ ratioP b E s X := le_trans (le_mul_of_one_le_right (by linarith) hD) hAD
  have hDP : D ≤ ratioP b E s X := le_trans (le_mul_of_one_le_left (by linarith) hA) hAD
  have h4' : ratioP b E s X ^ 4 ≤ ratioP b E s X ^ 27 := pow_le_pow_right₀ hP1 (by norm_num)
  have : A ^ 3 * D ≤ ratioP b E s X ^ 3 * ratioP b E s X :=
    mul_le_mul (pow_le_pow_left₀ (by linarith) hAP 3) hDP (by linarith) (by positivity)
  calc A ^ 3 * D ≤ ratioP b E s X ^ 3 * ratioP b E s X := this
    _ = ratioP b E s X ^ 4 := by ring
    _ ≤ _ := h4'

theorem inv_sq_le_v3 (hW : 1 ≤ W) : (W : ℝ)⁻¹ ^ 2 ≤ (Real.sqrt W)⁻¹ ^ 3 := by
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hs : 1 ≤ Real.sqrt W := Real.one_le_sqrt.2 hWr
  set v := (Real.sqrt W)⁻¹
  have hv0 : 0 ≤ v := by positivity
  have hv1 : v ≤ 1 := inv_le_one_of_one_le₀ hs
  have hx : (W : ℝ)⁻¹ = v ^ 2 := by
    rw [inv_pow, Real.sq_sqrt (by linarith)]
  rw [hx, ← pow_mul]
  calc v ^ (2 * 2) = v ^ 3 * v := by ring
    _ ≤ v ^ 3 * 1 := mul_le_mul_of_nonneg_left hv1 (by positivity)
    _ = v ^ 3 := mul_one _

/-- The two shift terms of `abs_layer_split` at one passive input, in the bulk. -/
theorem abs_shift_terms {b κI : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκI : 0 < κI)
    {z : DualCoord p} (hz : z ∈ dualChamber p) {K : ℝ} {E : ℝ}
    (hE : E ∈ bulkInterval κI) (hW1 : 1 ≤ W) (hWs' : K / etaLow b κI ≤ W)
    {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef) {ε : ℝ} (hε : 0 ≤ ε)
    (hεK : ε ≤ K / (W : ℝ) ^ 2) (u : ℝ) :
    inShiftErr z (passiveTransmission b E X).trace.re (ε / etaZ b E) ε (etaZ b E)
        (jetDistance0 b E (absorbedInput X ε) + passiveMass b E (absorbedInput X ε) / W) W +
      |ratioDrift (transportD0 b E) E (fun _ => 0) u z
          (traceMeasure (passiveTransmission b E (absorbedInput X ε))) -
        ratioDrift (transportD0 b E) E (fun _ => 0) u z
          (traceMeasure (passiveTransmission b E X))| / W ≤
      (shK z (K / etaLow b κI) K (4 * etaLow b κI)⁻¹ +
        dsC z (K / etaLow b κI) (sigmaPlus b / (2 * etaLow b κI ^ 2))) *
        (((passiveTransmission b E (absorbedInput X ε)).trace.re + 1) ^ 3 *
          ((W : ℝ) * jetDistance0 b E (absorbedInput X ε) + 1) * ((W : ℝ)⁻¹) ^ 2) := by
  have hzr := IsRatioParameter.isRatioRange hz
  have hηL : 0 < etaLow b κI := etaLow_pos (by linarith) hκI
  have hR : 0 ≤ ∑ i, (z.1 i + z.2 i) := Finset.sum_nonneg fun i _ => by
    have := hzr.1 i; have := (hzr.2 i).1; linarith
  have hcq : 0 ≤ (4 * etaLow b κI)⁻¹ := by positivity
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  have hb1 : b < 1 := by linarith
  have hη := PassiveCovariance.etaZ_pos b E hb1 h1 h2
  have hηle := etaLow_le hb1 hκI hE
  have hY' := passiveY_absorbedInput hY hε
  have hT := passiveTransmission_posSemidef hb1 h1 h2 hY
  have hT1 := one_sub_passiveTransmission_posSemidef b E X
  have hT' := passiveTransmission_posSemidef hb1 h1 h2 hY'
  have hT1' := one_sub_passiveTransmission_posSemidef b E (absorbedInput X ε)
  have hg0 := (mm_trace_posSemidef hT).1
  have hg'0 := (mm_trace_posSemidef hT').1
  set g := (passiveTransmission b E X).trace.re
  set g' := (passiveTransmission b E (absorbedInput X ε)).trace.re
  set x : ℝ := (W : ℝ)⁻¹ with hx
  set sv := ε / etaZ b E
  have hsv0 : 0 ≤ sv := div_nonneg hε hη.le
  have hεK' : ε ≤ K * x ^ 2 := hεK.trans_eq (by rw [hx, inv_pow, div_eq_mul_inv])
  have hss : sv ≤ K / etaLow b κI * x ^ 2 := by
    have : ε / etaZ b E ≤ ε / etaLow b κI := div_le_div_of_nonneg_left hε hηL hηle
    have h3 : ε / etaLow b κI ≤ K * x ^ 2 / etaLow b κI :=
      div_le_div_of_nonneg_right hεK' hηL.le
    calc sv ≤ K * x ^ 2 / etaLow b κI := this.trans h3
      _ = K / etaLow b κI * x ^ 2 := by ring
  have hs1 : sv ≤ 1 := by
    refine hss.trans ?_
    have hxW : x ^ 2 * (W : ℝ) ^ 2 = 1 := by rw [hx, inv_pow, inv_mul_cancel₀ (by positivity)]
    have hW2 : (W : ℝ) ≤ (W : ℝ) ^ 2 := by nlinarith
    have : K / etaLow b κI * x ^ 2 ≤ (W : ℝ) ^ 2 * x ^ 2 :=
      mul_le_mul_of_nonneg_right (hWs'.trans hW2) (sq_nonneg _)
    linarith
  have hgA : g ≤ 4 * (g' + 1) := by
    have hq := passiveMass_le_absorb hb0 hb h1 h2 hY hε
    have eg : g = 4 * etaZ b E * passiveMass b E X := by
      simp only [g, passiveTransmission, trace_smul, smul_eq_mul, Complex.re_ofReal_mul]; rfl
    have eg' : g' = 4 * etaZ b E * passiveMass b E (absorbedInput X ε) := by
      simp only [g', passiveTransmission, trace_smul, smul_eq_mul, Complex.re_ofReal_mul]; rfl
    have hq'0 := PassiveCovariance.passiveMass_nonneg b E hY'
    have h4 : (1 + sv) ^ 2 ≤ 4 := by nlinarith
    have := mul_le_mul_of_nonneg_left hq (by positivity : (0 : ℝ) ≤ 4 * etaZ b E)
    rw [← eg] at this
    have h5 : 4 * etaZ b E * ((1 + sv) ^ 2 * passiveMass b E (absorbedInput X ε)) ≤
        4 * g' := by
      rw [eg']; nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 4 * etaZ b E) hq'0]
    linarith
  set A := g' + 1 with hAdef
  set D := (W : ℝ) * jetDistance0 b E (absorbedInput X ε) + 1 with hDdef
  have hA : 1 ≤ A := by linarith
  have hδ0 : 0 ≤ jetDistance0 b E (absorbedInput X ε) := norm_nonneg _
  have hD : 1 ≤ D := by have := mul_nonneg hW0.le hδ0; linarith
  have hq' := mass_le_bulk hb1 hκI hE hY'
  have hq'0 := PassiveCovariance.passiveMass_nonneg b E hY'
  have hdq0 : 0 ≤ jetDistance0 b E (absorbedInput X ε) +
      passiveMass b E (absorbedInput X ε) / W := by positivity
  have hdq : jetDistance0 b E (absorbedInput X ε) + passiveMass b E (absorbedInput X ε) / W ≤
      (D + (4 * etaLow b κI)⁻¹ * A) * x := by
    have a1 : jetDistance0 b E (absorbedInput X ε) ≤ D * x := by
      rw [hx, le_mul_inv_iff₀ hW0]; linarith
    have a2 : passiveMass b E (absorbedInput X ε) / W ≤ (4 * etaLow b κI)⁻¹ * A * x := by
      rw [hx, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (hq'.trans (mul_le_mul_of_nonneg_left (by linarith) hcq))
        (by positivity)
    have e : (D + (4 * etaLow b κI)⁻¹ * A) * x = D * x + (4 * etaLow b κI)⁻¹ * A * x := by ring
    linarith
  have hB := inShiftErr_le hzr hx hW1 hA hD hg0 hgA hsv0 hss hs1 hη rfl hε hεK' hcq hdq0 hdq
  have hTL := trLip_transmission_shift hb0 hb h1 h2 hY hε (W := W)
  have hn := norm_shift_le hb0 hb h1 h2 hY hε
  have hlog := logRatio_shift_le hzr hT hT1 hT' hT1' hn
  have hτ := abs_trace_shift_le (W := W) hb0 hb h1 h2 hY hε
  have hc0 : 0 ≤ (2 * sv + sv ^ 2) * g + 4 * ε * W / etaZ b E := by positivity
  have hℓ : |logRatio z (passiveTransmission b E (absorbedInput X ε)) -
      logRatio z (passiveTransmission b E X)| ≤ (∑ i, (z.1 i + z.2 i)) *
        ((2 * sv + sv ^ 2) * g + 4 * ε * W / etaZ b E) + shiftErr z g (6 * sv + sv ^ 2) W := by
    have k1 := abs_sub (logRatio z (passiveTransmission b E (absorbedInput X ε)) -
      logRatio z (passiveTransmission b E X) + (∑ i, (z.1 i + z.2 i)) *
        (passiveTransmission b E (absorbedInput X ε) - passiveTransmission b E X).trace.re)
      ((∑ i, (z.1 i + z.2 i)) *
        (passiveTransmission b E (absorbedInput X ε) - passiveTransmission b E X).trace.re)
    simp only [add_sub_cancel_right] at k1
    rw [abs_mul, abs_of_nonneg hR] at k1
    have := mul_le_mul_of_nonneg_left hτ hR
    linarith
  have hdr := ratioDrift_shift_le (transportD0 b E) E u hz hT hT1 hT' hT1' hc0 hTL hℓ
  obtain ⟨hD00, hDC⟩ := transportD0_le_bulk hb0 hb1 hκI hE
  have hD0 : |transportD0 b E| ≤ sigmaPlus b / (2 * etaLow b κI ^ 2) := by
    rw [abs_of_nonneg hD00]; exact hDC
  have hds := driftShift_le hzr hx hW1 hA hD hg0 hgA hsv0 hss hs1 hη rfl hε hAdef.symm hD0
  have hCb := (div_le_div_of_nonneg_right hdr hW0.le).trans hds
  rw [add_mul]
  exact add_le_add hB hCb

/-- **One absorbed layer, bulk-uniform.** -/
theorem abs_layer_bulk (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : GaussianPoincare) {b κI : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκI : 0 < κI)
    {z : DualCoord p} (hz : z ∈ dualChamber p) {K : ℝ} (hK : 0 ≤ K) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κI,
      ∀ s : ℂ, IsStationaryJet b E s → ∀ X : Matrix (Fin W) (Fin W) ℂ,
        (passiveY X).PosSemidef → ∀ ε : ℝ, 0 ≤ ε → ε ≤ K / (W : ℝ) ^ 2 →
        ∀ (κ : ℝ → ℝ) (u : ℝ),
        |∫ y, transmissionRatio z.1 z.2 (traceMeasure (passiveTransmission b E
            (freshSchur E (absorbedInput X ε) y))) ∂freshLaw W b -
          transmissionRatio z.1 z.2 (traceMeasure (passiveTransmission b E X)) -
          ratioDrift (transportD0 b E) E κ u z (traceMeasure (passiveTransmission b E X)) / W| ≤
        C * (ratioP b E s (absorbedInput X ε) ^ 27 * (Real.sqrt W)⁻¹ ^ 3) +
          (∑ i, (z.1 i + z.2 i)) *
            |absorptionRate E κ u / W - 4 * etaZ b E * dStar b * ε * W| := by
  obtain ⟨K₁, W₁, hK₁, hd⟩ := ratio_layer_bulk hGA hLp hP hb0 hb hκI hz
  have hzr := IsRatioParameter.isRatioRange hz
  have hηL : 0 < etaLow b κI := etaLow_pos (by linarith) hκI
  have hR : 0 ≤ ∑ i, (z.1 i + z.2 i) := Finset.sum_nonneg fun i _ => by
    have := hzr.1 i; have := (hzr.2 i).1; linarith
  have hs₀ : 0 ≤ K / etaLow b κI := by positivity
  have hcq : 0 ≤ (4 * etaLow b κI)⁻¹ := by positivity
  have hCe : 0 ≤ shCe z (K / etaLow b κI) := by
    unfold shCe; have := lamLip_nonneg hzr; have := quadK_nonneg z; have := cubK_nonneg hzr
    positivity
  have hCM : 0 ≤ shCM z (K / etaLow b κI) := by unfold shCM; positivity
  have hshK : 0 ≤ shK z (K / etaLow b κI) K (4 * etaLow b κI)⁻¹ := by unfold shK; positivity
  have hdsC : 0 ≤ dsC z (K / etaLow b κI) (sigmaPlus b / (2 * etaLow b κI ^ 2)) := by
    unfold dsC; have := dsB_nonneg hzr; have := dsK_nonneg hzr
    have : 0 ≤ sigmaPlus b := by
      unfold sigmaPlus kPlus; exact div_nonneg (by nlinarith) hb0.le
    positivity
  refine ⟨K₁ + shK z (K / etaLow b κI) K (4 * etaLow b κI)⁻¹ +
      dsC z (K / etaLow b κI) (sigmaPlus b / (2 * etaLow b κI ^ 2)),
    max W₁ (max 1 ⌈K / etaLow b κI⌉₊), by positivity,
    fun W hW E hE s hs X hY ε hε hεK κ u => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨hW₁, hW1, hWs⟩ := hW
  have hWs' : K / etaLow b κI ≤ W := (Nat.le_ceil _).trans (by exact_mod_cast hWs)
  have h1 : -2 < E := by have := hE.1; linarith
  have h2 : E < 2 := by have := hE.2; linarith
  have hb1 : b < 1 := by linarith
  have hY' := passiveY_absorbedInput hY hε
  have hg'0 := (mm_trace_posSemidef (passiveTransmission_posSemidef hb1 h1 h2 hY')).1
  have hsh := abs_shift_terms hb0 hb hκI hz hE hW1 hWs' hY hε hεK u
  have hA1 := hd W hW₁ E hE s hs (absorbedInput X ε) hY' u
  have hsplit := abs_layer_split hb0 hb h1 h2 hY hz hε (by omega : W ≠ 0) κ u
    (∫ y, transmissionRatio z.1 z.2 (traceMeasure (passiveTransmission b E
      (freshSchur E (absorbedInput X ε) y))) ∂freshLaw W b)
  obtain ⟨hP1, hfac⟩ := ratioP_facts s (absorbedInput X ε) hg'0
  have hP : ((passiveTransmission b E (absorbedInput X ε)).trace.re + 1) ^ 3 *
      ((W : ℝ) * jetDistance0 b E (absorbedInput X ε) + 1) * ((W : ℝ)⁻¹) ^ 2 ≤
      ratioP b E s (absorbedInput X ε) ^ 27 * (Real.sqrt W)⁻¹ ^ 3 :=
    mul_le_mul hfac (inv_sq_le_v3 hW1) (sq_nonneg _) (by positivity)
  have hC0 : 0 ≤ shK z (K / etaLow b κI) K (4 * etaLow b κI)⁻¹ +
      dsC z (K / etaLow b κI) (sigmaPlus b / (2 * etaLow b κI ^ 2)) := by positivity
  have hsh' := hsh.trans (mul_le_mul_of_nonneg_left hP hC0)
  set Pv := ratioP b E s (absorbedInput X ε) ^ 27 * (Real.sqrt W)⁻¹ ^ 3
  have e : (K₁ + shK z (K / etaLow b κI) K (4 * etaLow b κI)⁻¹ +
      dsC z (K / etaLow b κI) (sigmaPlus b / (2 * etaLow b κI ^ 2))) * Pv =
      K₁ * Pv + (shK z (K / etaLow b κI) K (4 * etaLow b κI)⁻¹ +
        dsC z (K / etaLow b κI) (sigmaPlus b / (2 * etaLow b κI ^ 2))) * Pv := by ring
  rw [e]
  linarith

end BlockBand.Transmission.LawForced
