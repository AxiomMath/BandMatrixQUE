module

public import BlockBand.Transmission.LawForced.ShiftLog
public import BlockBand.Transmission.LawForced.ForcingRate
public import BlockBand.Transmission.Absorbed.ShiftTrace
public import BlockBand.Transmission.LawFinite.InjectionAlg

/-!
# The deterministic input shift of `F_z` carries the forcing

The proof does not use `absorbedL`: `LawFinite.absorbedL` is
`K𝒢₁₂(X − iε)` with the *old* `K = z − X`, so `L*TL` is neither the fresh `A` at `X` nor at
`X − iε`. But the absorbed step is `X_{j+1} = freshSchur(X_j − iε_j)`
(`PathScalar.ae_pathNearSchur_succ_abs`, `ε_j = κ((j+1)/W)/W²`), i.e. the **unabsorbed** fresh
layer at the passive input `X' = X − iε`. So the whole absorption is the deterministic
shift `T(X) ↦ T(X')`, followed by the `κ ≡ 0` one-layer drift at `X'`. This file treats the
shift; no injection mean or injection norm is needed: the injection is pathwise
`T(X') − T(X) = 4η(A*QA − Q) + 4ηεR'*R'` (the absorbed Ward identity, `A = 1 − iεR'`), and
`|W⁻¹Re Tr R'*R' − d_*| ≤ (δ₀(X') + q(X')/W)/η` (`normTrace_adjR_sub_dStar_le` at `X'`).

With `s = ε/η`, `g = Re Tr T(X)`:
* `norm_shift_le`: `‖T(X') − T(X)‖ ≤ 6s + s²`;
* `abs_trace_shift_le`: `|Re Tr(T(X') − T(X))| ≤ (2s + s²)g + 4εW/η`;
* `trace_shift_sub_le`: `|Re Tr(T(X') − T(X)) − 4ηd_*εW| ≤ (2s + s²)g + 4εW(δ₀' + q'/W)`;
* **`ratio_input_shift`**: `|F_z(T(X')) − F_z(T(X)) + R·F_z(T(X))·4ηd_*εW| ≤ inShiftErr`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawForced

open Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.LawDuality BlockBand.Transmission.Generator
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.LawFinite
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {p W : ℕ}

/-- The error of `ratio_input_shift` (`g = Re Tr T(X)`, `s = ε/η`, `dq = δ₀(X') + q(X')/W`). -/
def inShiftErr (z : DualCoord p) (g s ε η dq : ℝ) (W : ℕ) : ℝ :=
  shiftErr z g (6 * s + s ^ 2) W +
    ((∑ i, (z.1 i + z.2 i)) * ((2 * s + s ^ 2) * g + 4 * ε * W / η) +
      shiftErr z g (6 * s + s ^ 2) W) ^ 2 / 2 +
    4 * ((∑ i, (z.1 i + z.2 i)) * ((2 * s + s ^ 2) * g + 4 * ε * W / η) +
      shiftErr z g (6 * s + s ^ 2) W) ^ 3 +
    (∑ i, (z.1 i + z.2 i)) * ((2 * s + s ^ 2) * g + 4 * ε * W * dq)

/-- `A*QA − Q = −B*Q − QB + B*QB` for `A = 1 − B`. -/
theorem conj_sub_eq (B Q : Matrix (Fin W) (Fin W) ℂ) :
    (1 - B)ᴴ * Q * (1 - B) - Q = -(Bᴴ * Q) - Q * B + Bᴴ * Q * B := by
  rw [conjTranspose_sub, conjTranspose_one]; noncomm_ring

theorem norm_conj_sub_le {B Q : Matrix (Fin W) (Fin W) ℂ} {s : ℝ} (hB : ‖B‖ ≤ s) :
    ‖(1 - B)ᴴ * Q * (1 - B) - Q‖ ≤ (2 * s + s ^ 2) * ‖Q‖ := by
  have hBh : ‖Bᴴ‖ ≤ s := by rw [Matrix.l2_opNorm_conjTranspose]; exact hB
  have hs : 0 ≤ s := (norm_nonneg _).trans hB
  rw [conj_sub_eq]
  have n1 : ‖Bᴴ * Q‖ ≤ s * ‖Q‖ := (norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_right hBh (norm_nonneg _))
  have n2 : ‖Q * B‖ ≤ s * ‖Q‖ := (norm_mul_le _ _).trans (by
    rw [mul_comm s]; exact mul_le_mul_of_nonneg_left hB (norm_nonneg _))
  have n3 : ‖Bᴴ * Q * B‖ ≤ s ^ 2 * ‖Q‖ := (norm_mul_le _ _).trans (by
    calc ‖Bᴴ * Q‖ * ‖B‖ ≤ (s * ‖Q‖) * s := mul_le_mul n1 hB (norm_nonneg _) (by positivity)
      _ = s ^ 2 * ‖Q‖ := by ring)
  calc ‖-(Bᴴ * Q) - Q * B + Bᴴ * Q * B‖ ≤ ‖Bᴴ * Q‖ + ‖Q * B‖ + ‖Bᴴ * Q * B‖ := by
        refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
        refine (norm_sub_le _ _).trans ?_
        rw [norm_neg]
    _ ≤ (2 * s + s ^ 2) * ‖Q‖ := by nlinarith

theorem abs_trace_conj_sub_le {B Q : Matrix (Fin W) (Fin W) ℂ} (hQ : Q.PosSemidef) {s : ℝ}
    (hB : ‖B‖ ≤ s) : ‖((1 - B)ᴴ * Q * (1 - B) - Q).trace‖ ≤ (2 * s + s ^ 2) * Q.trace.re := by
  have e : ((1 - B)ᴴ * Q * (1 - B) - Q).trace = (((1 - B) * (1 - B)ᴴ - 1) * Q).trace := by
    rw [trace_sub, Matrix.sub_mul, trace_sub, Matrix.one_mul, Matrix.mul_assoc,
      trace_mul_comm, Matrix.mul_assoc, trace_mul_comm Q]
  rw [e]
  refine (norm_trace_mul_posSemidef_le hQ _).trans (mul_le_mul_of_nonneg_right ?_
    (SourceMixing.mm_trace_posSemidef hQ).1)
  have hBh : ‖Bᴴ‖ ≤ s := by rw [Matrix.l2_opNorm_conjTranspose]; exact hB
  have e2 : (1 - B) * (1 - B)ᴴ - 1 = -B - Bᴴ + B * Bᴴ := by
    rw [conjTranspose_sub, conjTranspose_one]; noncomm_ring
  rw [e2]
  have n3 : ‖B * Bᴴ‖ ≤ s ^ 2 := (norm_mul_le _ _).trans (by
    rw [sq]; exact mul_le_mul hB hBh (norm_nonneg _) ((norm_nonneg _).trans hB))
  calc ‖-B - Bᴴ + B * Bᴴ‖ ≤ ‖B‖ + ‖Bᴴ‖ + ‖B * Bᴴ‖ := by
        refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
        refine (norm_sub_le _ _).trans ?_
        rw [norm_neg]
    _ ≤ 2 * s + s ^ 2 := by linarith

section Shift

variable {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
  {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef)
include hb0 hb h1 h2 hY

/-- The pieces of the shift: `T(X') − T(X) = 4η(A*QA − Q) + 4ηεR'*R'`. -/
theorem transmission_shift_eq {ε : ℝ} (hε : 0 ≤ ε) :
    passiveTransmission b E (absorbedInput X ε) - passiveTransmission b E X =
      (((4 * etaZ b E : ℝ)) : ℂ) •
        ((1 - (((ε : ℝ) : ℂ) * Complex.I) • passiveResolvent b E (absorbedInput X ε))ᴴ *
          passiveQ b E X *
          (1 - (((ε : ℝ) : ℂ) * Complex.I) • passiveResolvent b E (absorbedInput X ε)) -
          passiveQ b E X) +
      (((4 * etaZ b E * ε : ℝ)) : ℂ) • ((passiveResolvent b E (absorbedInput X ε))ᴴ *
          passiveResolvent b E (absorbedInput X ε)) := by
  rw [passiveTransmission, passiveTransmission, Absorbed.passiveQ_absorb_split hb0 hb h1 h2 hY hε,
    ← smul_sub]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem norm_smulR_le {ε : ℝ} (hε : 0 ≤ ε) :
    ‖(((ε : ℝ) : ℂ) * Complex.I) • passiveResolvent b E (absorbedInput X ε)‖ ≤
      ε / etaZ b E := by
  have hY' := LawFinite.passiveY_absorbedInput hY hε
  have hR'n := norm_passiveResolvent_le hb0 hb h1 h2 hY'
  refine (norm_smul_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hε]
  exact (mul_le_mul_of_nonneg_left hR'n hε).trans_eq (div_eq_mul_inv _ _).symm

/-- `‖T(X') − T(X)‖ ≤ 6s + s²`. -/
theorem norm_shift_le {ε : ℝ} (hε : 0 ≤ ε) :
    ‖passiveTransmission b E (absorbedInput X ε) - passiveTransmission b E X‖ ≤
      6 * (ε / etaZ b E) + (ε / etaZ b E) ^ 2 := by
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hY' := LawFinite.passiveY_absorbedInput hY hε
  have hR'n := norm_passiveResolvent_le hb0 hb h1 h2 hY'
  set s := ε / etaZ b E
  have hs : 0 ≤ s := div_nonneg hε hη.le
  rw [transmission_shift_eq hb0 hb h1 h2 hY hε]
  have hT1 : ‖passiveTransmission b E X‖ ≤ 1 :=
    norm_le_one_of_psd (passiveTransmission_posSemidef (by linarith) h1 h2 hY)
      (one_sub_passiveTransmission_posSemidef b E _)
  have hTQ : ‖passiveTransmission b E X‖ = 4 * etaZ b E * ‖passiveQ b E X‖ := by
    rw [passiveTransmission, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have a1 := norm_conj_sub_le (Q := passiveQ b E X) (norm_smulR_le hb0 hb h1 h2 hY hε)
  have a2 : ‖(passiveResolvent b E (absorbedInput X ε))ᴴ *
      passiveResolvent b E (absorbedInput X ε)‖ ≤ (etaZ b E)⁻¹ ^ 2 := by
    refine (norm_mul_le _ _).trans ?_
    rw [Matrix.l2_opNorm_conjTranspose, sq]
    exact mul_le_mul hR'n hR'n (norm_nonneg _) (by positivity)
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  have b1 : 4 * etaZ b E * ‖(1 - (((ε : ℝ) : ℂ) * Complex.I) •
      passiveResolvent b E (absorbedInput X ε))ᴴ * passiveQ b E X *
      (1 - (((ε : ℝ) : ℂ) * Complex.I) • passiveResolvent b E (absorbedInput X ε)) -
      passiveQ b E X‖ ≤ 2 * s + s ^ 2 := by
    have := mul_le_mul_of_nonneg_left a1 (by positivity : (0 : ℝ) ≤ 4 * etaZ b E)
    have e : 4 * etaZ b E * ((2 * s + s ^ 2) * ‖passiveQ b E X‖) =
        (2 * s + s ^ 2) * ‖passiveTransmission b E X‖ := by rw [hTQ]; ring
    rw [e] at this
    nlinarith
  have b2 : 4 * etaZ b E * ε * ‖(passiveResolvent b E (absorbedInput X ε))ᴴ *
      passiveResolvent b E (absorbedInput X ε)‖ ≤ 4 * s := by
    have := mul_le_mul_of_nonneg_left a2 (by positivity : (0 : ℝ) ≤ 4 * etaZ b E * ε)
    refine this.trans (le_of_eq ?_)
    simp only [s]; field_simp
  linarith

/-- `|Re Tr(T(X') − T(X))| ≤ (2s + s²)g + 4εW/η`. -/
theorem abs_trace_shift_le {ε : ℝ} (hε : 0 ≤ ε) :
    |(passiveTransmission b E (absorbedInput X ε) - passiveTransmission b E X).trace.re| ≤
      (2 * (ε / etaZ b E) + (ε / etaZ b E) ^ 2) * (passiveTransmission b E X).trace.re +
        4 * ε * W / etaZ b E := by
  have h := Absorbed.norm_trace_transmission_shift_le hb0 hb h1 h2 hY hε 1
    PassiveLayer.norm_one_le'
  rw [Matrix.one_mul] at h
  exact (Complex.abs_re_le_norm _).trans h

/-- **The forcing in the shift**: `|Re Tr(T(X') − T(X)) − 4ηd_*εW| ≤ (2s+s²)g + 4εW(δ₀'+q'/W)`. -/
theorem trace_shift_sub_le {ε : ℝ} (hε : 0 ≤ ε) (hW : W ≠ 0) :
    |(passiveTransmission b E (absorbedInput X ε) - passiveTransmission b E X).trace.re -
        4 * etaZ b E * dStar b * ε * W| ≤
      (2 * (ε / etaZ b E) + (ε / etaZ b E) ^ 2) * (passiveTransmission b E X).trace.re +
        4 * ε * W * (jetDistance0 b E (absorbedInput X ε) +
          passiveMass b E (absorbedInput X ε) / W) := by
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hY' := LawFinite.passiveY_absorbedInput hY hε
  have hW0 : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero hW
  set R' := passiveResolvent b E (absorbedInput X ε)
  set Bm := (((ε : ℝ) : ℂ) * Complex.I) • R'
  set Q := passiveQ b E X
  have hQ : Q.PosSemidef := hY.conjTranspose_mul_mul_same _
  have hd := LawFinite.normTrace_adjR_sub_dStar_le hb0 hb h1 h2 hY' hW
  have a1 := abs_trace_conj_sub_le hQ (norm_smulR_le hb0 hb h1 h2 hY hε)
  have eg : (passiveTransmission b E X).trace.re = 4 * etaZ b E * Q.trace.re := by
    rw [passiveTransmission, trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  rw [transmission_shift_eq hb0 hb h1 h2 hY hε, trace_add, trace_smul, trace_smul, smul_eq_mul,
    smul_eq_mul, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul, eg]
  set x := ((1 - Bm)ᴴ * Q * (1 - Bm) - Q).trace
  set y := (R'ᴴ * R').trace.re
  have hx : |x.re| ≤ (2 * (ε / etaZ b E) + (ε / etaZ b E) ^ 2) * Q.trace.re :=
    (Complex.abs_re_le_norm _).trans a1
  have hy : |y - W * dStar b| ≤ W * ((jetDistance0 b E (absorbedInput X ε) +
      passiveMass b E (absorbedInput X ε) / W) / etaZ b E) := by
    have e : y - W * dStar b = W * ((W : ℝ)⁻¹ * y - dStar b) := by field_simp
    rw [e, abs_mul, abs_of_pos hW0]
    exact mul_le_mul_of_nonneg_left hd hW0.le
  have e : 4 * etaZ b E * x.re + 4 * etaZ b E * ε * y - 4 * etaZ b E * dStar b * ε * W =
      4 * etaZ b E * x.re + 4 * etaZ b E * ε * (y - W * dStar b) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul (4 * etaZ b E) x.re, abs_mul (4 * etaZ b E * ε) (y - W * dStar b),
    abs_of_pos (by positivity : (0 : ℝ) < 4 * etaZ b E),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * etaZ b E * ε)]
  have c1 := mul_le_mul_of_nonneg_left hx (by positivity : (0 : ℝ) ≤ 4 * etaZ b E)
  have c2 := mul_le_mul_of_nonneg_left hy (by positivity : (0 : ℝ) ≤ 4 * etaZ b E * ε)
  have e3 : 4 * etaZ b E * ε * (W * ((jetDistance0 b E (absorbedInput X ε) +
      passiveMass b E (absorbedInput X ε) / W) / etaZ b E)) = 4 * ε * W *
      (jetDistance0 b E (absorbedInput X ε) + passiveMass b E (absorbedInput X ε) / W) := by
    field_simp
  have e4 : 4 * etaZ b E * ((2 * (ε / etaZ b E) + (ε / etaZ b E) ^ 2) * Q.trace.re) =
      (2 * (ε / etaZ b E) + (ε / etaZ b E) ^ 2) * (4 * etaZ b E * Q.trace.re) := by ring
  linarith

/-- **The input shift of `F_z`**: `|F(T(X')) − F(T(X)) + R F(T(X)) 4ηd_*εW| ≤ inShiftErr`. -/
theorem ratio_input_shift {z : DualCoord p} (hz : IsRatioRange z.1 z.2) {ε : ℝ} (hε : 0 ≤ ε)
    (hW : W ≠ 0) :
    |transmissionRatio z.1 z.2 (traceMeasure (passiveTransmission b E (absorbedInput X ε))) -
        transmissionRatio z.1 z.2 (traceMeasure (passiveTransmission b E X)) +
        (∑ i, (z.1 i + z.2 i)) *
          transmissionRatio z.1 z.2 (traceMeasure (passiveTransmission b E X)) *
          (4 * etaZ b E * dStar b * ε * W)| ≤
      inShiftErr z (passiveTransmission b E X).trace.re (ε / etaZ b E) ε (etaZ b E)
        (jetDistance0 b E (absorbedInput X ε) + passiveMass b E (absorbedInput X ε) / W) W := by
  have hY' := LawFinite.passiveY_absorbedInput hY hε
  have hb1 : b < 1 := by linarith
  set T := passiveTransmission b E X
  set T' := passiveTransmission b E (absorbedInput X ε)
  have hT := passiveTransmission_posSemidef hb1 h1 h2 hY
  have hT1 := one_sub_passiveTransmission_posSemidef b E X
  have hT' := passiveTransmission_posSemidef hb1 h1 h2 hY'
  have hT1' := one_sub_passiveTransmission_posSemidef b E (absorbedInput X ε)
  have hm := ratio_shift_le hz hT hT1 hT' hT1' (norm_shift_le hb0 hb h1 h2 hY hε)
  have htr := abs_trace_shift_le (W := W) hb0 hb h1 h2 hY hε
  have hsub := trace_shift_sub_le hb0 hb h1 h2 hY hε hW
  set R := ∑ i, (z.1 i + z.2 i)
  have hR : 0 ≤ R := Finset.sum_nonneg fun i _ => by
    have := hz.1 i; have := (hz.2 i).1; linarith
  set F := transmissionRatio z.1 z.2 (traceMeasure T)
  have hF : 0 ≤ F ∧ F ≤ 1 := by
    have := transmissionRatio_mem_vec hz (traceMeasure T); exact ⟨this.1.le, this.2⟩
  have hg : 0 ≤ T.trace.re := (SourceMixing.mm_trace_posSemidef hT).1
  have hη := etaZ_pos b E hb1 h1 h2
  set e := shiftErr z T.trace.re (6 * (ε / etaZ b E) + (ε / etaZ b E) ^ 2) W
  have he : 0 ≤ e := shiftErr_nonneg hz hg (by positivity)
  set τ := (T' - T).trace.re
  set c := (2 * (ε / etaZ b E) + (ε / etaZ b E) ^ 2) * T.trace.re + 4 * ε * W / etaZ b E
  have hM : R * |τ| + e ≤ R * c + e := by
    have := mul_le_mul_of_nonneg_left htr hR; linarith
  have hM0 : 0 ≤ R * |τ| + e := by positivity
  have k2 : (R * |τ| + e) ^ 2 ≤ (R * c + e) ^ 2 := pow_le_pow_left₀ hM0 hM 2
  have k3 : (R * |τ| + e) ^ 3 ≤ (R * c + e) ^ 3 := pow_le_pow_left₀ hM0 hM 3
  have e1 : transmissionRatio z.1 z.2 (traceMeasure T') - F + R * F * (4 * etaZ b E * dStar b * ε * W)
      = (transmissionRatio z.1 z.2 (traceMeasure T') - F + R * F * τ) -
        R * F * (τ - 4 * etaZ b E * dStar b * ε * W) := by ring
  rw [e1]
  refine (abs_sub _ _).trans ?_
  have a2 : |R * F * (τ - 4 * etaZ b E * dStar b * ε * W)| ≤
      R * ((2 * (ε / etaZ b E) + (ε / etaZ b E) ^ 2) * T.trace.re +
        4 * ε * W * (jetDistance0 b E (absorbedInput X ε) +
          passiveMass b E (absorbedInput X ε) / W)) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hR, abs_of_nonneg hF.1]
    have := mul_le_of_le_one_right (abs_nonneg (τ - 4 * etaZ b E * dStar b * ε * W)) hF.2
    calc R * F * |τ - 4 * etaZ b E * dStar b * ε * W| = R * (F * |τ - 4 * etaZ b E * dStar b * ε * W|) := by ring
      _ ≤ R * |τ - 4 * etaZ b E * dStar b * ε * W| := mul_le_mul_of_nonneg_left (by linarith) hR
      _ ≤ _ := mul_le_mul_of_nonneg_left hsub hR
  unfold inShiftErr
  linarith

end Shift

end BlockBand.Transmission.LawForced
