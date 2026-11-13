module

public import BlockBand.Transmission.LawForced.ShiftX
public import BlockBand.Transmission.PathJet.JetPathStep
public import BlockBand.Transmission.PathJet.JetMeanDeriv

/-!
# The input shift of `δ₁` and of the source-mixing atoms

* **`jetDistance1_absorb_le`**: `δ₁(X') ≤ δ₁(X) + 2ε/η³` (`crossTr X' z z = crossTr X (z+iε)
  (z+iε)`, `norm_crossTr_sub_le`).
* `hs_sq_add_le`, `hsSandwich_add_Q_le`: for `Q₁, Q₂ ⪰ 0`,
  `hs(Q₁+Q₂, f) ≤ hs(Q₁, f) + √(‖f‖²‖Q₂‖(2Tr Q₁ + Tr Q₂))` (`hs` is **not** subadditive in `Q`
  in general; the cross terms are controlled by `‖Q₂‖`);
* `hsSandwich_conj`: `hs(A*QA, f) = hs(Q, AfA*)`.

These give, in the sibling module, **`mix_absorb_le`**:
`‖Tr Q'f'‖ + hs(Q', f') ≤ ‖Tr Qf‖ + hs(Q, f) + 2mq + 3εW/(2η³) + √c₁`, with
`m = (2s+s²)·3/(2η) + s/η`, `c₁ = (3/(2η))²(ε/η²)(2(1+s)²q + εW/η²)`.
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

/-!
## Sandwich lemmas
-/

theorem trace_conj_mul (A Q f : Matrix (Fin W) (Fin W) ℂ) :
    (Aᴴ * Q * A * f).trace = (Q * (A * f * Aᴴ)).trace := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc]

theorem hsSandwich_conj (A Q f : Matrix (Fin W) (Fin W) ℂ) :
    hsSandwich (Aᴴ * Q * A) f = hsSandwich Q (A * f * Aᴴ) := by
  unfold hsSandwich
  congr 2
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem re_trace_sandwich_nonneg {Q : Matrix (Fin W) (Fin W) ℂ} (hQ : Q.PosSemidef)
    (f : Matrix (Fin W) (Fin W) ℂ) : 0 ≤ (Q * f * Q * fᴴ).trace.re := by
  rw [ts_trace_sandwich hQ, Complex.ofReal_re]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (ts_lam_nonneg hQ i) (ts_lam_nonneg hQ j)) (sq_nonneg _)

theorem norm_trace_mul_psd' {P : Matrix (Fin W) (Fin W) ℂ} (hP : P.PosSemidef)
    (M : Matrix (Fin W) (Fin W) ℂ) : ‖(P * M).trace‖ ≤ ‖M‖ * P.trace.re := by
  rw [trace_mul_comm]; exact norm_trace_mul_posSemidef_le hP M

theorem hs_sq_add_le {Q₁ Q₂ : Matrix (Fin W) (Fin W) ℂ} (h₁ : Q₁.PosSemidef)
    (h₂ : Q₂.PosSemidef) (f : Matrix (Fin W) (Fin W) ℂ) :
    ((Q₁ + Q₂) * f * (Q₁ + Q₂) * fᴴ).trace.re ≤ (Q₁ * f * Q₁ * fᴴ).trace.re +
      ‖f‖ ^ 2 * ‖Q₂‖ * (2 * Q₁.trace.re + Q₂.trace.re) := by
  have e : ((Q₁ + Q₂) * f * (Q₁ + Q₂) * fᴴ).trace = (Q₁ * f * Q₁ * fᴴ).trace +
      (Q₁ * (f * Q₂ * fᴴ)).trace + (Q₁ * (fᴴ * Q₂ * f)).trace + (Q₂ * (f * Q₂ * fᴴ)).trace := by
    have e2 : (Q₂ * f * Q₁ * fᴴ).trace = (Q₁ * (fᴴ * Q₂ * f)).trace := by
      rw [trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
      rw [trace_mul_comm]; simp only [Matrix.mul_assoc]
    rw [← e2]
    simp only [Matrix.add_mul, Matrix.mul_add, trace_add, Matrix.mul_assoc]
    ring
  have n1 : ‖f * Q₂ * fᴴ‖ ≤ ‖f‖ ^ 2 * ‖Q₂‖ := by
    refine (norm_mul_le _ _).trans ?_
    rw [Matrix.l2_opNorm_conjTranspose]
    have := norm_mul_le f Q₂
    nlinarith [norm_nonneg f, norm_nonneg Q₂, norm_nonneg (f * Q₂)]
  have n2 : ‖fᴴ * Q₂ * f‖ ≤ ‖f‖ ^ 2 * ‖Q₂‖ := by
    refine (norm_mul_le _ _).trans ?_
    have := norm_mul_le fᴴ Q₂
    rw [Matrix.l2_opNorm_conjTranspose] at this
    nlinarith [norm_nonneg f, norm_nonneg Q₂, norm_nonneg (fᴴ * Q₂)]
  have t1 := (Complex.re_le_norm _).trans ((norm_trace_mul_psd' h₁ (f * Q₂ * fᴴ)).trans
    (mul_le_mul_of_nonneg_right n1 (mm_trace_posSemidef h₁).1))
  have t2 := (Complex.re_le_norm _).trans ((norm_trace_mul_psd' h₁ (fᴴ * Q₂ * f)).trans
    (mul_le_mul_of_nonneg_right n2 (mm_trace_posSemidef h₁).1))
  have t3 := (Complex.re_le_norm _).trans ((norm_trace_mul_psd' h₂ (f * Q₂ * fᴴ)).trans
    (mul_le_mul_of_nonneg_right n1 (mm_trace_posSemidef h₂).1))
  rw [e, Complex.add_re, Complex.add_re, Complex.add_re]
  nlinarith

theorem hsSandwich_add_Q_le {Q₁ Q₂ : Matrix (Fin W) (Fin W) ℂ} (h₁ : Q₁.PosSemidef)
    (h₂ : Q₂.PosSemidef) (f : Matrix (Fin W) (Fin W) ℂ) :
    hsSandwich (Q₁ + Q₂) f ≤ hsSandwich Q₁ f +
      Real.sqrt (‖f‖ ^ 2 * ‖Q₂‖ * (2 * Q₁.trace.re + Q₂.trace.re)) := by
  have hc : 0 ≤ ‖f‖ ^ 2 * ‖Q₂‖ * (2 * Q₁.trace.re + Q₂.trace.re) := by
    have := (mm_trace_posSemidef h₁).1; have := (mm_trace_posSemidef h₂).1; positivity
  have h0 := re_trace_sandwich_nonneg h₁ f
  unfold hsSandwich
  refine (Real.sqrt_le_sqrt (hs_sq_add_le h₁ h₂ f)).trans ?_
  rw [Real.sqrt_le_left (by positivity)]
  have := Real.sq_sqrt h0
  have := Real.sq_sqrt hc
  nlinarith [Real.sqrt_nonneg ((Q₁ * f * Q₁ * fᴴ).trace.re),
    Real.sqrt_nonneg (‖f‖ ^ 2 * ‖Q₂‖ * (2 * Q₁.trace.re + Q₂.trace.re))]

section Shift

variable {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
  {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef)
include hb0 hb h1 h2 hY

/-- **`δ₁(X − iε) ≤ δ₁(X) + 2ε/η³`.** -/
theorem jetDistance1_absorb_le {ε : ℝ} (hε : 0 ≤ ε) (s : ℂ) :
    jetDistance1 b E s (absorbedInput X ε) ≤ jetDistance1 b E s X + 2 * ε / etaZ b E ^ 3 := by
  have hb1 : b < 1 := by linarith
  have hη := etaZ_pos b E hb1 h1 h2
  have hY' := passiveY_absorbedInput hY hε
  rw [PathJet.jetDistance1_eq_crossTr hb1 h1 h2 s hY',
    PathJet.jetDistance1_eq_crossTr hb1 h1 h2 s hY]
  have e : PathScalar.crossTr (absorbedInput X ε) (boundaryZ b E) (boundaryZ b E) =
      PathScalar.crossTr X (boundaryZ b E + (ε : ℂ) * Complex.I)
        (boundaryZ b E + (ε : ℂ) * Complex.I) := by
    unfold PathScalar.crossTr absorbedInput
    rw [show boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - (X - ((ε : ℂ) * Complex.I) • 1) =
      (boundaryZ b E + (ε : ℂ) * Complex.I) • 1 - X by rw [add_smul]; abel]
  have hζ : etaZ b E ≤ (boundaryZ b E + (ε : ℂ) * Complex.I).im := by
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, add_zero, etaZ]
    linarith
  have hc := PathJet.norm_crossTr_sub_le hY hη hη hζ (le_refl (etaZ b E))
  rw [e]
  have hn : ‖boundaryZ b E + (ε : ℂ) * Complex.I - boundaryZ b E‖ = ε := by
    rw [add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hε]
  rw [hn] at hc
  set a' := PathScalar.crossTr X (boundaryZ b E + (ε : ℂ) * Complex.I)
    (boundaryZ b E + (ε : ℂ) * Complex.I)
  set a := PathScalar.crossTr X (boundaryZ b E) (boundaryZ b E)
  have e2 : -a' - s = (-a - s) - (a' - a) := by ring
  rw [e2]
  refine (norm_sub_le _ _).trans ?_
  have : ε * ((etaZ b E)⁻¹ ^ 2 * (etaZ b E)⁻¹ + (etaZ b E)⁻¹ * (etaZ b E)⁻¹ ^ 2) =
      2 * ε / etaZ b E ^ 3 := by field_simp; ring
  linarith

/-- The error of `mix_absorb_le`. -/
def mixErr (b E ε q : ℝ) (W : ℕ) : ℝ :=
  2 * (((2 * (ε / etaZ b E) + (ε / etaZ b E) ^ 2) * (3 / (2 * etaZ b E)) +
      ε / etaZ b E / etaZ b E) * q) + ε * W * ((etaZ b E)⁻¹ ^ 2 * (3 / (2 * etaZ b E))) +
    Real.sqrt ((3 / (2 * etaZ b E)) ^ 2 * (ε * (etaZ b E)⁻¹ ^ 2) *
      (2 * ((1 + ε / etaZ b E) ^ 2 * q) + ε * (W * (etaZ b E)⁻¹ ^ 2)))

end Shift

end BlockBand.Transmission.Absorbed
