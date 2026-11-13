module

public import BlockBand.Transmission.Absorbed.ShiftJet

/-!
# The input shift of the source-mixing atoms

**`mix_absorb_le`**: `‖Tr Q'f'‖ + hs(Q', f') ≤ ‖Tr Qf‖ + hs(Q, f) + mixErr b E ε q W`.

Route: `Q' = A*QA + εR'*R'`, `f' − f = R' − R = −R·iεR'`, so `‖f' − f‖ ≤ s/η`;
`Tr(A*QA f') = Tr(Q·Af'A*)` and `hs(A*QA, f') = hs(Q, Af'A*)` with
`‖Af'A* − f‖ ≤ (2s+s²)‖f'‖ + s/η`; the `εR'*R'` part by `hsSandwich_add_Q_le`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Absorbed

open Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Internal.Contracts.Layers
open BlockBand.Transmission BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.LawFinite
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.LawForced
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

variable {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
  {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef)
include hb0 hb h1 h2 hY

/-- **The input shift of `‖Tr Qf‖ + hs(Q, f)`.** -/
theorem mix_absorb_le {ε : ℝ} (hε : 0 ≤ ε) :
    ‖(passiveQ b E (absorbedInput X ε) * passiveF b E (absorbedInput X ε)).trace‖ +
        hsSandwich (passiveQ b E (absorbedInput X ε)) (passiveF b E (absorbedInput X ε)) ≤
      ‖(passiveQ b E X * passiveF b E X).trace‖ + hsSandwich (passiveQ b E X) (passiveF b E X) +
        mixErr b E ε (passiveMass b E X) W := by
  have hb1 : b < 1 := by linarith
  have hη := etaZ_pos b E hb1 h1 h2
  have hY' := passiveY_absorbedInput hY hε
  set η := etaZ b E
  set s := ε / η
  have hs : 0 ≤ s := div_nonneg hε hη.le
  set R := passiveResolvent b E X
  set R' := passiveResolvent b E (absorbedInput X ε)
  set Bm := (((ε : ℝ) : ℂ) * Complex.I) • R'
  set A := 1 - Bm
  set Q := passiveQ b E X
  set f := passiveF b E X
  set f' := passiveF b E (absorbedInput X ε)
  set q := passiveMass b E X
  have hQ : Q.PosSemidef := hY.conjTranspose_mul_mul_same _
  have hq0 : 0 ≤ q := (mm_trace_posSemidef hQ).1
  have hR : ‖R‖ ≤ η⁻¹ := norm_passiveResolvent_le hb0 hb h1 h2 hY
  have hR' : ‖R'‖ ≤ η⁻¹ := norm_passiveResolvent_le hb0 hb h1 h2 hY'
  have hBm : ‖Bm‖ ≤ s := norm_smulR_le hb0 hb h1 h2 hY hε
  have hBmh : ‖Bmᴴ‖ ≤ s := by rw [Matrix.l2_opNorm_conjTranspose]; exact hBm
  have hf' : ‖f'‖ ≤ 3 / (2 * η) := norm_passiveF_le hb0 hb h1 h2 hY'
  have hsplit := passiveQ_absorb_split hb0 hb h1 h2 hY hε
  -- `f' − f = −R Bm`
  have hff : ‖f' - f‖ ≤ s / η := by
    have e : f' - f = -(R * Bm) := by
      have hRA := resolvent_absorb_eq hb0 hb h1 h2 hY hε
      have e1 : f' - f = R' - R := sub_sub_sub_cancel_right _ _ _
      have e2 : R' - R = R * A - R := by rw [← hRA]
      rw [e1, e2]
      simp only [A, Matrix.mul_sub, Matrix.mul_one]; abel
    rw [e, norm_neg]
    refine (norm_mul_le _ _).trans ?_
    calc ‖R‖ * ‖Bm‖ ≤ η⁻¹ * s := mul_le_mul hR hBm (norm_nonneg _) (by positivity)
      _ = s / η := by rw [div_eq_inv_mul]
  -- `M = A f' A*`
  set M := A * f' * Aᴴ
  have hM : ‖M - f‖ ≤ (2 * s + s ^ 2) * (3 / (2 * η)) + s / η := by
    have h := norm_conj_sub_le (Q := f') hBmh
    have eA : (1 - Bmᴴ)ᴴ * f' * (1 - Bmᴴ) = M := by
      simp only [M, A, conjTranspose_sub, conjTranspose_one, conjTranspose_conjTranspose]
    rw [eA] at h
    have : M - f = (M - f') + (f' - f) := by abel
    rw [this]
    refine (norm_add_le _ _).trans (add_le_add (h.trans ?_) hff)
    exact mul_le_mul_of_nonneg_left hf' (by positivity)
  set m := (2 * s + s ^ 2) * (3 / (2 * η)) + s / η
  have hm0 : 0 ≤ m := by positivity
  set Q₁ := Aᴴ * Q * A
  set Q₂ := (ε : ℂ) • (R'ᴴ * R')
  have hQ₁ : Q₁.PosSemidef := hQ.conjTranspose_mul_mul_same A
  have hQ₂ : Q₂.PosSemidef := (posSemidef_conjTranspose_mul_self R').smul (by exact_mod_cast hε)
  have hRR : ‖R'ᴴ * R'‖ ≤ η⁻¹ ^ 2 := by
    refine (norm_mul_le _ _).trans ?_
    rw [Matrix.l2_opNorm_conjTranspose, sq]
    exact mul_le_mul hR' hR' (norm_nonneg _) (by positivity)
  have hQ₂n : ‖Q₂‖ ≤ ε * η⁻¹ ^ 2 := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hε]
    exact mul_le_mul_of_nonneg_left hRR hε
  have hQ₂t : Q₂.trace.re ≤ ε * (W * η⁻¹ ^ 2) := by
    rw [trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
    refine mul_le_mul_of_nonneg_left ((Complex.re_le_norm _).trans ?_) hε
    exact (norm_trace_le_mul _).trans (mul_le_mul_of_nonneg_left hRR (Nat.cast_nonneg W))
  have hQ₁t : Q₁.trace.re ≤ (1 + s) ^ 2 * q := by
    have h := abs_trace_conj_sub_le hQ hBm
    have : Q₁.trace.re - q ≤ (2 * s + s ^ 2) * q := by
      have := (Complex.re_le_norm _).trans h
      rwa [trace_sub, Complex.sub_re] at this
    nlinarith
  -- trace part
  have ht : ‖(passiveQ b E (absorbedInput X ε) * f').trace‖ ≤ ‖(Q * f).trace‖ + m * q +
      ε * W * (η⁻¹ ^ 2 * (3 / (2 * η))) := by
    rw [hsplit, Matrix.add_mul, trace_add, trace_conj_mul]
    have a1 : ‖(Q * M).trace‖ ≤ ‖(Q * f).trace‖ + m * q := by
      have e : Q * M = Q * f + Q * (M - f) := by rw [← Matrix.mul_add]; abel_nf
      rw [e, trace_add]
      refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
      exact (norm_trace_mul_psd' hQ _).trans (mul_le_mul_of_nonneg_right hM hq0)
    have a2 : ‖(Q₂ * f').trace‖ ≤ ε * W * (η⁻¹ ^ 2 * (3 / (2 * η))) := by
      rw [Matrix.smul_mul, trace_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg hε]
      have hn : ‖R'ᴴ * R' * f'‖ ≤ η⁻¹ ^ 2 * (3 / (2 * η)) :=
        (norm_mul_le _ _).trans (mul_le_mul hRR hf' (norm_nonneg _) (by positivity))
      have := (norm_trace_le_mul (R'ᴴ * R' * f')).trans
        (mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg W))
      calc ε * ‖(R'ᴴ * R' * f').trace‖ ≤ ε * (W * (η⁻¹ ^ 2 * (3 / (2 * η)))) :=
            mul_le_mul_of_nonneg_left this hε
        _ = _ := by ring
    exact (norm_add_le _ _).trans (by linarith)
  -- hs part
  have hh : hsSandwich (passiveQ b E (absorbedInput X ε)) f' ≤ hsSandwich Q f + m * q +
      Real.sqrt ((3 / (2 * η)) ^ 2 * (ε * η⁻¹ ^ 2) *
        (2 * ((1 + s) ^ 2 * q) + ε * (W * η⁻¹ ^ 2))) := by
    rw [hsplit]
    refine (hsSandwich_add_Q_le hQ₁ hQ₂ f').trans ?_
    rw [hsSandwich_conj]
    have a1 : hsSandwich Q M ≤ hsSandwich Q f + m * q := by
      have e : M = f + (M - f) := by abel
      rw [e]
      refine (hsSandwich_add_le hQ _ _).trans (add_le_add le_rfl ?_)
      exact (hsSandwich_le_norm hQ _).trans (mul_le_mul_of_nonneg_right hM hq0)
    refine add_le_add a1 (Real.sqrt_le_sqrt ?_)
    have hQ₁0 := (mm_trace_posSemidef hQ₁).1
    have hQ₂0 := (mm_trace_posSemidef hQ₂).1
    have k1 : ‖f'‖ ^ 2 ≤ (3 / (2 * η)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hf' 2
    have k2 : 2 * Q₁.trace.re + Q₂.trace.re ≤ 2 * ((1 + s) ^ 2 * q) + ε * (W * η⁻¹ ^ 2) := by
      linarith
    have k3 : ‖f'‖ ^ 2 * ‖Q₂‖ ≤ (3 / (2 * η)) ^ 2 * (ε * η⁻¹ ^ 2) :=
      mul_le_mul k1 hQ₂n (norm_nonneg _) (by positivity)
    exact mul_le_mul k3 k2 (by positivity) (by positivity)
  unfold mixErr
  have e2 : ε / etaZ b E / etaZ b E = s / η := rfl
  linarith

end BlockBand.Transmission.Absorbed
