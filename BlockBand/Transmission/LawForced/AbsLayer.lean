module

public import BlockBand.Transmission.LawForced.ShiftDriftPair
public import BlockBand.Transmission.LawForced.ShiftX

/-!
# One absorbed layer: the split into the `κ ≡ 0` layer at `X − iε` and the shift

* `trLip_of_contr`: a contraction bound gives `TrLip`;
* **`ratioDrift_shift_le`**: `|ratioDrift D₀ E 0 u z μ_{T'} − ratioDrift D₀ E 0 u z μ_T| ≤
  |D₀|/2·(ℓ·dsB(g'+1)² + dsK·c·(g+g'+1))` for `0 ⪯ T, T' ⪯ I`, `TrLip T' T c`,
  `|log F(T') − log F(T)| ≤ ℓ`;
* `ratioDrift_split`: `ratioDrift D₀ E κ u z ν = ratioDrift D₀ E 0 u z ν − h(u)R F_z(ν)`;
* **`abs_layer_split`**: at a passive `X`, `X' = X − iε`, `ε ≥ 0`,
  `|∫F(T(X'₊)) − F(T(X)) − ratioDrift_κ(u, μ_{T(X)})/W| ≤ |∫F(T(X'₊)) − F(T(X')) −
  ratioDrift_0(u, μ_{T(X')})/W| + inShiftErr + |ratioDrift_0(T(X')) − ratioDrift_0(T(X))|/W +
  R·|h(u)/W − 4ηd_*εW|`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open Matrix Finset MeasureTheory
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers
open BlockBand.Transmission.LawDuality BlockBand.Transmission.Generator
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.LawFinite
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {p W : ℕ}

theorem trLip_of_contr {A' A : Matrix (Fin W) (Fin W) ℂ} {c : ℝ}
    (h : ∀ N : Matrix (Fin W) (Fin W) ℂ, ‖N‖ ≤ 1 → ‖(N * (A' - A)).trace‖ ≤ c) :
    TrLip A' A c := fun K => by
  rcases eq_or_ne ‖K‖ 0 with hK | hK
  · rw [norm_eq_zero.1 hK]; simp
  have hK0 : 0 < ‖K‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hK)
  have hN : ‖(((‖K‖)⁻¹ : ℝ) : ℂ) • K‖ ≤ 1 := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hK0.le),
      inv_mul_cancel₀ hK]
  have h1 := h _ hN
  rw [Matrix.smul_mul, trace_smul, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg (inv_nonneg.2 hK0.le)] at h1
  rw [inv_mul_le_iff₀ hK0] at h1
  exact h1

theorem ratioDrift_zero_eq (D0 E u : ℝ) {z : DualCoord p} (hz : z ∈ dualChamber p)
    {T : Matrix (Fin W) (Fin W) ℂ} (hT : T.PosSemidef) (hT1 : (1 - T).PosSemidef) :
    ratioDrift D0 E (fun _ => 0) u z (traceMeasure T) =
      transmissionRatio z.1 z.2 (traceMeasure T) * (D0 / 2 * dsum z hT) := by
  rw [ratioDrift_traceMeasure _ _ _ _ hz hT hT1]
  unfold dsum
  simp only [absorptionRate, mul_zero, zero_mul, sub_zero]

/-- **The `κ ≡ 0` drift is trace-Lipschitz.** -/
theorem ratioDrift_shift_le (D0 E u : ℝ) {z : DualCoord p} (hz : z ∈ dualChamber p)
    {T T' : Matrix (Fin W) (Fin W) ℂ} (hT : T.PosSemidef) (hT1 : (1 - T).PosSemidef)
    (hT' : T'.PosSemidef) (hT1' : (1 - T').PosSemidef) {c : ℝ} (hc : 0 ≤ c)
    (hL : TrLip T' T c) {ℓ : ℝ} (hℓ : |logRatio z T' - logRatio z T| ≤ ℓ) :
    |ratioDrift D0 E (fun _ => 0) u z (traceMeasure T') -
        ratioDrift D0 E (fun _ => 0) u z (traceMeasure T)| ≤
      |D0| / 2 * (ℓ * (dsB z * (T'.trace.re + 1) ^ 2) +
        dsK z * c * (T.trace.re + T'.trace.re + 1)) := by
  have hzr := IsRatioParameter.isRatioRange hz
  rw [ratioDrift_zero_eq D0 E u hz hT hT1, ratioDrift_zero_eq D0 E u hz hT' hT1',
    transmissionRatio_traceMeasure_exp hzr hT hT1, transmissionRatio_traceMeasure_exp hzr hT' hT1']
  set F := Real.exp (logRatio z T)
  set F' := Real.exp (logRatio z T')
  have hF : |F' - F| ≤ ℓ :=
    (abs_exp_sub_exp_le (logRatio_nonpos hzr hT' hT1') (logRatio_nonpos hzr hT hT1)).trans hℓ
  have hF0 : 0 ≤ F := (Real.exp_pos _).le
  have hF1 : F ≤ 1 := Real.exp_le_one_iff.2 (logRatio_nonpos hzr hT hT1)
  obtain ⟨d0', d1'⟩ := dsum_nonneg_le hzr hT' hT1'
  have hd := abs_dsum_sub_le hT hT1 hT' hT1' hc hL hzr
  have e : F' * (D0 / 2 * dsum z hT') - F * (D0 / 2 * dsum z hT) =
      D0 / 2 * ((F' - F) * dsum z hT' + F * (dsum z hT' - dsum z hT)) := by ring
  rw [e, abs_mul, abs_div, abs_two]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg d0', abs_of_nonneg hF0]
  have a1 : |F' - F| * dsum z hT' ≤ ℓ * (dsB z * (T'.trace.re + 1) ^ 2) :=
    mul_le_mul hF d1' d0' ((abs_nonneg _).trans hF)
  have a2 : F * |dsum z hT' - dsum z hT| ≤ |dsum z hT' - dsum z hT| :=
    mul_le_of_le_one_left (abs_nonneg _) hF1
  linarith

theorem ratioDrift_split (D0 E : ℝ) (κ : ℝ → ℝ) (u : ℝ) (z : DualCoord p)
    (ν : FiniteMeasure unitInterval) :
    ratioDrift D0 E κ u z ν = ratioDrift D0 E (fun _ => 0) u z ν -
      absorptionRate E κ u * (∑ i, (z.1 i + z.2 i)) * transmissionRatio z.1 z.2 ν := by
  simp only [ratioDrift, absorptionRate, mul_zero, zero_mul, sub_zero]

section Layer

variable {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
  {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef)
include hb0 hb h1 h2 hY

theorem trLip_transmission_shift {ε : ℝ} (hε : 0 ≤ ε) :
    TrLip (passiveTransmission b E (absorbedInput X ε)) (passiveTransmission b E X)
      ((2 * (ε / etaZ b E) + (ε / etaZ b E) ^ 2) * (passiveTransmission b E X).trace.re +
        4 * ε * W / etaZ b E) := by
  exact trLip_of_contr (Absorbed.norm_trace_transmission_shift_le hb0 hb h1 h2 hY hε)

/-- **The split of one absorbed layer.** -/
theorem abs_layer_split {z : DualCoord p} (hz : z ∈ dualChamber p) {ε : ℝ} (hε : 0 ≤ ε)
    (hW : W ≠ 0) (κ : ℝ → ℝ) (u : ℝ) (I : ℝ) :
    |I - transmissionRatio z.1 z.2 (traceMeasure (passiveTransmission b E X)) -
        ratioDrift (transportD0 b E) E κ u z (traceMeasure (passiveTransmission b E X)) / W| ≤
      |I - transmissionRatio z.1 z.2
          (traceMeasure (passiveTransmission b E (absorbedInput X ε))) -
        ratioDrift (transportD0 b E) E (fun _ => 0) u z
          (traceMeasure (passiveTransmission b E (absorbedInput X ε))) / W| +
      inShiftErr z (passiveTransmission b E X).trace.re (ε / etaZ b E) ε (etaZ b E)
        (jetDistance0 b E (absorbedInput X ε) + passiveMass b E (absorbedInput X ε) / W) W +
      |ratioDrift (transportD0 b E) E (fun _ => 0) u z
          (traceMeasure (passiveTransmission b E (absorbedInput X ε))) -
        ratioDrift (transportD0 b E) E (fun _ => 0) u z
          (traceMeasure (passiveTransmission b E X))| / W +
      (∑ i, (z.1 i + z.2 i)) * |absorptionRate E κ u / W - 4 * etaZ b E * dStar b * ε * W| := by
  have hzr := IsRatioParameter.isRatioRange hz
  have hW0 : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero hW
  have hB := ratio_input_shift hb0 hb h1 h2 hY hzr hε hW
  set F := transmissionRatio z.1 z.2 (traceMeasure (passiveTransmission b E X))
  set F' := transmissionRatio z.1 z.2 (traceMeasure (passiveTransmission b E (absorbedInput X ε)))
  set r0 := ratioDrift (transportD0 b E) E (fun _ => 0) u z
    (traceMeasure (passiveTransmission b E X))
  set r0' := ratioDrift (transportD0 b E) E (fun _ => 0) u z
    (traceMeasure (passiveTransmission b E (absorbedInput X ε)))
  set R := ∑ i, (z.1 i + z.2 i)
  set j := 4 * etaZ b E * dStar b * ε * W
  have hR : 0 ≤ R := Finset.sum_nonneg fun i _ => by
    have := hzr.1 i; have := (hzr.2 i).1; linarith
  have hF : 0 ≤ F ∧ F ≤ 1 := by
    have := transmissionRatio_mem_vec hzr (traceMeasure (passiveTransmission b E X))
    exact ⟨this.1.le, this.2⟩
  rw [ratioDrift_split]
  have e : I - F - (r0 - absorptionRate E κ u * R * F) / W =
      (I - F' - r0' / W) + (F' - F + R * F * j) + (r0' - r0) / W +
        R * F * (absorptionRate E κ u / W - j) := by
    field_simp; ring
  rw [e]
  have a3 : |(r0' - r0) / W| = |r0' - r0| / W := by rw [abs_div, abs_of_pos hW0]
  have a4 : |R * F * (absorptionRate E κ u / W - j)| ≤ R * |absorptionRate E κ u / W - j| := by
    rw [abs_mul, abs_mul, abs_of_nonneg hR, abs_of_nonneg hF.1]
    have := mul_le_of_le_one_left (abs_nonneg (absorptionRate E κ u / W - j)) hF.2
    nlinarith [abs_nonneg (absorptionRate E κ u / W - j)]
  have := abs_add_three (I - F' - r0' / W) (F' - F + R * F * j) ((r0' - r0) / W)
  have := abs_add_le (I - F' - r0' / W + (F' - F + R * F * j) + (r0' - r0) / W)
    (R * F * (absorptionRate E κ u / W - j))
  linarith

end Layer

end BlockBand.Transmission.LawForced
