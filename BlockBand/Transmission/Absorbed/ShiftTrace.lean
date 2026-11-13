module

public import BlockBand.Transmission.LawFinite.InjectionMean
public import BlockBand.Transmission.Generator.StepExact

/-!
# The absorbed modulus: the deterministic input shift of `Tr T^k`

The fresh layer of the absorbed path sees `X' = X - iε` (`absorbedInput X ε`), not `X`. The
input shift `d = Re Tr T(X')^k - Re Tr T(X)^k` is bounded here for every `k`, at every passive
`X` and `ε ≥ 0` (`s = ε/η`, `g = Re Tr T(X)`, `η = etaZ b E`):

* `norm_trace_mul_pow_sub_le` (abstract): `‖A‖, ‖B‖ ≤ 1` and `‖Tr N(A - B)‖ ≤ c` for every
  `‖N‖ ≤ 1` give `‖Tr M(A^k - B^k)‖ ≤ kc` for every `‖M‖ ≤ 1` (telescoping, no trace norm);
* `passiveQ_absorb_split`: `Q(X') = A*Q(X)A + εR'*R'`, `A = 1 - iεR'`;
* **`norm_trace_transmission_shift_le`**: `‖Tr N(T(X') - T(X))‖ ≤ (2s + s²)g + 4εW/η`;
* **`abs_powerTrace_shift_le`**: `|d| ≤ k((2s + s²)g + 4εW/η)`;
* **`abs_powerTrace_shift_le_div`**: for `ε ≤ K/W²`, `W ≥ 1`: `|d| ≤ k c_K (g + 1)/W`,
  `c_K = (K/η)(2 + K/η) + 4K/η`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Absorbed

open Matrix
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Transmission BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.LawFinite
open BlockBand.Transmission.Generator
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- **Telescoping without a trace norm.** -/
theorem norm_trace_mul_pow_sub_le {A B : Matrix (Fin W) (Fin W) ℂ} (hA : ‖A‖ ≤ 1)
    (hB : ‖B‖ ≤ 1) {c : ℝ}
    (hc : ∀ N : Matrix (Fin W) (Fin W) ℂ, ‖N‖ ≤ 1 → ‖(N * (A - B)).trace‖ ≤ c) (k : ℕ) :
    ∀ M : Matrix (Fin W) (Fin W) ℂ, ‖M‖ ≤ 1 → ‖(M * (A ^ k - B ^ k)).trace‖ ≤ k * c := by
  induction k with
  | zero => intro M _; simp
  | succ k ih =>
    intro M hM
    have e : M * (A ^ (k + 1) - B ^ (k + 1)) = (M * A ^ k) * (A - B) + M * (A ^ k - B ^ k) * B := by
      rw [pow_succ, pow_succ]; noncomm_ring
    have e2 : (M * (A ^ k - B ^ k) * B).trace = ((B * M) * (A ^ k - B ^ k)).trace := by
      rw [trace_mul_comm, Matrix.mul_assoc]
    have h1 : ‖M * A ^ k‖ ≤ 1 := by
      refine (norm_mul_le _ _).trans ?_
      have : ‖A ^ k‖ ≤ 1 := by
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · rw [pow_zero]; exact PassiveLayer.norm_one_le'
        · exact (norm_pow_le' A hk).trans (pow_le_one₀ (norm_nonneg _) hA)
      nlinarith [norm_nonneg M, norm_nonneg (A ^ k)]
    have h2 : ‖B * M‖ ≤ 1 := (norm_mul_le _ _).trans (by nlinarith [norm_nonneg M, norm_nonneg B])
    rw [e, trace_add, e2]
    refine (norm_add_le _ _).trans ?_
    have := ih (B * M) h2
    have := hc _ h1
    push_cast
    linarith

section Shift

variable {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
  {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef)
include hb0 hb h1 h2 hY

/-- `Q(X - iε) = A*Q(X)A + εR'*R'`, `A = 1 - iεR'`, `R' = R(X - iε)`. -/
theorem passiveQ_absorb_split {ε : ℝ} (hε : 0 ≤ ε) :
    passiveQ b E (absorbedInput X ε) =
      (1 - (((ε : ℝ) : ℂ) * Complex.I) • passiveResolvent b E (absorbedInput X ε))ᴴ *
          passiveQ b E X *
          (1 - (((ε : ℝ) : ℂ) * Complex.I) • passiveResolvent b E (absorbedInput X ε)) +
        (ε : ℂ) • ((passiveResolvent b E (absorbedInput X ε))ᴴ *
          passiveResolvent b E (absorbedInput X ε)) := by
  set R := passiveResolvent b E X
  set R' := passiveResolvent b E (absorbedInput X ε)
  set A := 1 - (((ε : ℝ) : ℂ) * Complex.I) • R'
  have hYe : passiveY (absorbedInput X ε) = passiveY X + (ε : ℂ) • 1 :=
    PathScalar.passiveY_absorb_eq X ε
  rw [passiveQ, hYe]
  conv_lhs => rw [show passiveResolvent b E (absorbedInput X ε) = R * A from
    resolvent_absorb_eq hb0 hb h1 h2 hY hε]
  rw [passiveQ, conjTranspose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one]
  congr 1
  · simp only [Matrix.mul_assoc, R]
  · congr 1
    rw [← conjTranspose_mul, ← resolvent_absorb_eq hb0 hb h1 h2 hY hε]

/-- **The one-step shift of `T` against a contraction**:
`‖Tr N(T(X') - T(X))‖ ≤ (2s + s²)g + 4εW/η`, `s = ε/η`. -/
theorem norm_trace_transmission_shift_le {ε : ℝ} (hε : 0 ≤ ε) (N : Matrix (Fin W) (Fin W) ℂ)
    (hN : ‖N‖ ≤ 1) :
    ‖(N * (passiveTransmission b E (absorbedInput X ε) - passiveTransmission b E X)).trace‖ ≤
      (2 * (ε / etaZ b E) + (ε / etaZ b E) ^ 2) * (passiveTransmission b E X).trace.re +
        4 * ε * W / etaZ b E := by
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hY' := LawFinite.passiveY_absorbedInput hY hε
  set R' := passiveResolvent b E (absorbedInput X ε)
  set Bm := (((ε : ℝ) : ℂ) * Complex.I) • R'
  set A := 1 - Bm
  set Q := passiveQ b E X
  set s := ε / etaZ b E
  have hs : 0 ≤ s := div_nonneg hε hη.le
  have hR'n : ‖R'‖ ≤ (etaZ b E)⁻¹ := norm_passiveResolvent_le hb0 hb h1 h2 hY'
  have hBn : ‖Bm‖ ≤ s := by
    refine (norm_smul_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hε]
    exact (mul_le_mul_of_nonneg_left hR'n hε).trans_eq (div_eq_mul_inv _ _).symm
  have hBn' : ‖Bmᴴ‖ ≤ s := by rw [Matrix.l2_opNorm_conjTranspose]; exact hBn
  have hQ : Q.PosSemidef := hY.conjTranspose_mul_mul_same _
  have hq0 : 0 ≤ Q.trace.re := passiveMass_nonneg b E hY
  have hsplit := passiveQ_absorb_split hb0 hb h1 h2 hY hε
  -- the `A*QA - Q` part
  have hP1 : ‖(N * (Aᴴ * Q * A - Q)).trace‖ ≤ (2 * s + s ^ 2) * Q.trace.re := by
    have e : (N * (Aᴴ * Q * A - Q)).trace = ((A * N * Aᴴ - N) * Q).trace := by
      rw [Matrix.mul_sub, trace_sub, Matrix.sub_mul, trace_sub]
      congr 1
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc,
        Matrix.mul_assoc, Matrix.mul_assoc]
    rw [e]
    refine (norm_trace_mul_posSemidef_le hQ _).trans (mul_le_mul_of_nonneg_right ?_ hq0)
    have e2 : A * N * Aᴴ - N = -(Bm * N) - N * Bmᴴ + Bm * N * Bmᴴ := by
      simp only [A, conjTranspose_sub, conjTranspose_one]; noncomm_ring
    rw [e2]
    have n1 : ‖Bm * N‖ ≤ s := (norm_mul_le _ _).trans (by nlinarith [norm_nonneg Bm, norm_nonneg N])
    have n2 : ‖N * Bmᴴ‖ ≤ s := (norm_mul_le _ _).trans (by nlinarith [norm_nonneg Bmᴴ, norm_nonneg N])
    have n3 : ‖Bm * N * Bmᴴ‖ ≤ s ^ 2 := (norm_mul_le _ _).trans
      (by nlinarith [norm_nonneg Bmᴴ, norm_nonneg (Bm * N)])
    calc ‖-(Bm * N) - N * Bmᴴ + Bm * N * Bmᴴ‖ ≤ ‖Bm * N‖ + ‖N * Bmᴴ‖ + ‖Bm * N * Bmᴴ‖ := by
          refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
          refine (norm_sub_le _ _).trans ?_
          rw [norm_neg]
      _ ≤ 2 * s + s ^ 2 := by linarith
  -- the `εR'*R'` part
  have hP2 : ‖(N * ((ε : ℂ) • (R'ᴴ * R'))).trace‖ ≤ ε * W / etaZ b E ^ 2 := by
    rw [Matrix.mul_smul, trace_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg hε]
    have hn : ‖N * (R'ᴴ * R')‖ ≤ (etaZ b E)⁻¹ ^ 2 := by
      refine (norm_mul_le _ _).trans ?_
      have : ‖R'ᴴ * R'‖ ≤ (etaZ b E)⁻¹ ^ 2 := by
        refine (norm_mul_le _ _).trans ?_
        rw [Matrix.l2_opNorm_conjTranspose, sq]
        exact mul_le_mul hR'n hR'n (norm_nonneg _) (by positivity)
      nlinarith [norm_nonneg (R'ᴴ * R')]
    have ht := (norm_trace_le_mul (N * (R'ᴴ * R'))).trans
      (mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg W))
    calc ε * ‖(N * (R'ᴴ * R')).trace‖ ≤ ε * (W * (etaZ b E)⁻¹ ^ 2) :=
          mul_le_mul_of_nonneg_left ht hε
      _ = ε * W / etaZ b E ^ 2 := by rw [inv_pow]; ring
  -- assemble
  have eT : N * (passiveTransmission b E (absorbedInput X ε) - passiveTransmission b E X) =
      (((4 * etaZ b E : ℝ)) : ℂ) • (N * (Aᴴ * Q * A - Q) + N * ((ε : ℂ) • (R'ᴴ * R'))) := by
    rw [passiveTransmission, passiveTransmission, ← smul_sub, Matrix.mul_smul, hsplit]
    congr 1
    rw [← Matrix.mul_add]
    congr 1
    abel
  have eg : (passiveTransmission b E X).trace.re = 4 * etaZ b E * Q.trace.re := by
    rw [passiveTransmission, trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  rw [eT, trace_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity), trace_add,
    eg]
  have h3 := (norm_add_le _ _).trans (add_le_add hP1 hP2)
  have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 4 * etaZ b E)
  refine h4.trans (le_of_eq ?_)
  field_simp

/-- **The input shift of `Re Tr T^k`**: `|d| ≤ k((2s + s²)g + 4εW/η)`. -/
theorem abs_powerTrace_shift_le {ε : ℝ} (hε : 0 ≤ ε) (k : ℕ) :
    |((passiveTransmission b E (absorbedInput X ε)) ^ k).trace.re -
        ((passiveTransmission b E X) ^ k).trace.re| ≤
      k * ((2 * (ε / etaZ b E) + (ε / etaZ b E) ^ 2) * (passiveTransmission b E X).trace.re +
        4 * ε * W / etaZ b E) := by
  have hY' := LawFinite.passiveY_absorbedInput hY hε
  have hA : ‖passiveTransmission b E (absorbedInput X ε)‖ ≤ 1 :=
    norm_le_one_of_psd (passiveTransmission_posSemidef (by linarith) h1 h2 hY')
      (one_sub_passiveTransmission_posSemidef b E _)
  have hB : ‖passiveTransmission b E X‖ ≤ 1 :=
    norm_le_one_of_psd (passiveTransmission_posSemidef (by linarith) h1 h2 hY)
      (one_sub_passiveTransmission_posSemidef b E _)
  have h := norm_trace_mul_pow_sub_le hA hB
    (fun N hN => norm_trace_transmission_shift_le hb0 hb h1 h2 hY hε N hN) k 1
    PassiveLayer.norm_one_le'
  rw [Matrix.one_mul, trace_sub] at h
  rw [← Complex.sub_re]
  exact (Complex.abs_re_le_norm _).trans h

/-- **The input shift at absorption `ε ≤ K/W²`**: `|d| ≤ k c_K (g+1)/W`. -/
theorem abs_powerTrace_shift_le_div {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hεK : ε ≤ K / (W : ℝ) ^ 2) (hW : 1 ≤ W) (k : ℕ) :
    |((passiveTransmission b E (absorbedInput X ε)) ^ k).trace.re -
        ((passiveTransmission b E X) ^ k).trace.re| ≤
      k * ((K / etaZ b E) * (2 + K / etaZ b E) + 4 * K / etaZ b E) *
        ((passiveTransmission b E X).trace.re + 1) / W := by
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hg : 0 ≤ (passiveTransmission b E X).trace.re :=
    (SourceMixing.mm_trace_posSemidef (passiveTransmission_posSemidef (by linarith) h1 h2 hY)).1
  set g := (passiveTransmission b E X).trace.re
  set η := etaZ b E
  have hεW : ε * W ≤ K / W := by
    rw [le_div_iff₀ hW0]
    calc ε * W * W = ε * (W : ℝ) ^ 2 := by ring
      _ ≤ K := by rwa [le_div_iff₀ (by positivity)] at hεK
  have hεW1 : ε ≤ K / W := by
    have : ε ≤ ε * W := le_mul_of_one_le_right hε hWr
    linarith
  have hs : ε / η ≤ K / η / W := by
    rw [div_div, mul_comm, ← div_div]; exact div_le_div_of_nonneg_right hεW1 hη.le
  have hs' : ε / η ≤ K / η := hs.trans (div_le_self (by positivity) hWr)
  have hs0 : 0 ≤ ε / η := div_nonneg hε hη.le
  refine (abs_powerTrace_shift_le hb0 hb h1 h2 hY hε k).trans ?_
  have a1 : (2 * (ε / η) + (ε / η) ^ 2) ≤ (K / η) * (2 + K / η) / W := by
    have : 2 * (ε / η) + (ε / η) ^ 2 = (ε / η) * (2 + ε / η) := by ring
    rw [this, mul_div_right_comm]
    exact mul_le_mul hs (by linarith) (by positivity) (by positivity)
  have a2 : 4 * ε * W / η ≤ 4 * K / η / W := by
    rw [div_div, mul_comm η, ← div_div, div_le_div_iff_of_pos_right hη]
    have := mul_le_mul_of_nonneg_left hεW (by norm_num : (0 : ℝ) ≤ 4)
    calc 4 * ε * W = 4 * (ε * W) := by ring
      _ ≤ 4 * (K / W) := this
      _ = 4 * K / W := by ring
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have b1 : (2 * (ε / η) + (ε / η) ^ 2) * g ≤ (K / η) * (2 + K / η) / W * g :=
    mul_le_mul_of_nonneg_right a1 hg
  have hc1 : 0 ≤ (K / η) * (2 + K / η) / W := by positivity
  have hc2 : 0 ≤ 4 * K / η / W := by positivity
  have b3 : (K / η) * (2 + K / η) / W * g + 4 * K / η / W ≤
      ((K / η) * (2 + K / η) + 4 * K / η) * (g + 1) / W := by
    rw [div_mul_eq_mul_div, ← add_div, div_le_div_iff_of_pos_right hW0]
    have : 0 ≤ (K / η) * (2 + K / η) := by positivity
    have : 0 ≤ 4 * K / η * g := by positivity
    nlinarith
  calc (k : ℝ) * ((2 * (ε / η) + (ε / η) ^ 2) * g + 4 * ε * W / η)
      ≤ k * ((K / η) * (2 + K / η) / W * g + 4 * K / η / W) :=
        mul_le_mul_of_nonneg_left (by linarith) hk
    _ ≤ k * (((K / η) * (2 + K / η) + 4 * K / η) * (g + 1) / W) :=
        mul_le_mul_of_nonneg_left b3 hk
    _ = _ := by ring

end Shift

end BlockBand.Transmission.Absorbed
