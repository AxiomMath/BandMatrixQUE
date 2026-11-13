module

public import BlockBand.Native.CEH.ETH.FlowIto
public import BlockBand.Native.CEH.Phase1.Resolvent

/-!
# CEH ETH: algebra of the imaginary chain `Z = Re⟨Im R₁ A Im R₂ Aᴴ⟩`

All statements are pointwise identities between complex `N × N` matrices; `⟨X⟩ = N⁻¹ tr X` is
`normalizedTrace`, `Im X = (2i)⁻¹ (X - Xᴴ)` is `External.CEH.imaginaryPart`, and `X̄ = Xᴴ`.

**Chain decomposition** (`fz_chain_eq`, `fz_re_chain_eq_reTr`): with `K = N⁻¹ Aᴴ`,
`Im R₁ A Im R₂ = -¼ (R₁AR₂ - R₁AR₂ᴴ - R₁ᴴAR₂ + R₁ᴴAR₂ᴴ)`, hence
`Z = -¼ (Re tr(K R₁AR₂) - Re tr(K R₁AR₂ᴴ) - Re tr(K R₁ᴴAR₂) + Re tr(K R₁ᴴAR₂ᴴ))`, a fixed real
combination of four chains `reTr K (P A Q)`, `P ∈ {R₁, R₁ᴴ}`, `Q ∈ {R₂, R₂ᴴ}`.

**Bracket functional** (`fz_D`, `fz_D_eq`, `fz_re_D_eq`): for a direction `E`,
`fz_imS R E = (2i)⁻¹ (RER - RᴴERᴴ)` and
`fz_D R₁ R₂ A E = ⟨fz_imS R₁ E · A Im R₂ Aᴴ⟩ + ⟨Im R₁ A · fz_imS R₂ E · Aᴴ⟩`. Then
`-Re fz_D(E)` is the same `-¼`-combination of the four first derivatives
`-Re tr(K(PEPAQ + PAQEQ))`. Since `∂_E R = -RER` and `∂_E Rᴴ = -RᴴERᴴ` (`E` Hermitian),
`∂_E Z = -Re fz_D(E)`.

**Drift.** `fz_driftC R₁ R₂ A m₁ m₂` is the `-¼`-combination of the four complex drifts
`⟨flowDrift2 P Q A m_P m_Q · Aᴴ⟩` (with `m_{Rᴴ} = m̄`); its real part is the drift of `Z`.
With `a_i = ⟨R_i⟩ - m_i`, `I_i = Im R_i`, `X = I₁AI₂Aᴴ`:
* `fz_driftC_eq` (any matrices `R₁, R₂`, no resolvent structure):
  `fz_driftC = a₁⟨R₁X⟩ + ā₁⟨I₁R₁ᴴAI₂Aᴴ⟩ + Im a₁⟨R₁R₁ᴴAI₂Aᴴ⟩
    + a₂⟨I₁AR₂I₂Aᴴ⟩ + ā₂⟨I₁AI₂R₂ᴴAᴴ⟩ + Im a₂⟨I₁AR₂R₂ᴴAᴴ⟩
    + ⟨I₁AR₂⟩⟨I₂AᴴR₁⟩ + ⟨I₁AI₂⟩⟨R₂ᴴAᴴR₁⟩ + ⟨R₁ᴴAR₂⟩⟨I₂AᴴI₁⟩ + ⟨R₁ᴴAI₂⟩⟨R₂ᴴAᴴI₁⟩`
  (from `(2i)⁻¹(aR² - āRᴴ²) = a R Im R + ā Im R Rᴴ + Im a · RRᴴ` and the polarization of the
  cross terms);
* `fz_driftC_eq_ceh` (resolvents `R_i = (H - w_i)⁻¹`, `H` Hermitian, `Im w_i ≠ 0`; Ward
  `RRᴴ = Im R / Im w` and `[Rᴴ, Im R] = 0`): exactly CEH (7.2) in variance time,
  `fz_driftC = (Im a₁/Im w₁ + Im a₂/Im w₂) ⟨X⟩
    + ⟨R₂ᴴAᴴR₁⟩⟨I₁AI₂⟩ + ⟨R₁ᴴAR₂⟩⟨I₂AᴴI₁⟩ + ⟨I₁AR₂⟩⟨I₂AᴴR₁⟩ + ⟨R₂ᴴAᴴI₁⟩⟨R₁ᴴAI₂⟩
    + a₁⟨I₁AI₂AᴴR₁⟩ + a₂⟨I₂AᴴI₁AR₂⟩ + ā₁⟨I₁AI₂AᴴR₁ᴴ⟩ + ā₂⟨I₂AᴴI₁AR₂ᴴ⟩`.
  Compared with the printed (7.2): `λ = 1`; no `+⟨X⟩dt` term (that term comes from CEH's
  Ornstein–Uhlenbeck time, absent in variance time); `M_i` is replaced by the characteristic
  parameter `m_i` (in CEH `m_i = M_i`); and `η_i` must be read as the **signed** `Im w_i`
  (`η_i = |Im w_i|` is correct only for `Im w_i > 0`, CEH's setting). The printed index-2 terms
  `⟨Im G₂ A* Im G₁ A G₂^{(*)}⟩` are correct as printed.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.ETH
open Matrix
open BlockBand.Native.CEH.Flow
open BlockBand.External.CEH (normalizedTrace)
open scoped ComplexConjugate

variable {N : ℕ}

/-- `(2i)⁻¹ (R E R - Rᴴ E Rᴴ)`, minus the derivative of `Im R` in a Hermitian direction `E`. -/
def fz_imS (R E : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  (2 * Complex.I)⁻¹ • (R * E * R - Rᴴ * E * Rᴴ)

/-- The bracket functional `⟨fz_imS R₁ E · A Im R₂ Aᴴ⟩ + ⟨Im R₁ A · fz_imS R₂ E · Aᴴ⟩`. -/
def fz_D (R₁ R₂ A E : Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  normalizedTrace (fz_imS R₁ E * A * External.CEH.imaginaryPart R₂ * Aᴴ) +
    normalizedTrace (External.CEH.imaginaryPart R₁ * A * fz_imS R₂ E * Aᴴ)

/-- The complex imaginary chain `⟨Im R₁ A Im R₂ Aᴴ⟩`. -/
def fz_chain (R₁ R₂ A : Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  normalizedTrace (External.CEH.imaginaryPart R₁ * A * External.CEH.imaginaryPart R₂ * Aᴴ)

/-- The complex drift: `-¼`-combination of the four drifts `⟨flowDrift2 P Q A m_P m_Q Aᴴ⟩`. -/
def fz_driftC (R₁ R₂ A : Matrix (Fin N) (Fin N) ℂ) (m₁ m₂ : ℂ) : ℂ :=
  -(1 / 4 : ℂ) * (normalizedTrace (flowDrift2 R₁ R₂ A m₁ m₂ * Aᴴ) -
    normalizedTrace (flowDrift2 R₁ R₂ᴴ A m₁ (conj m₂) * Aᴴ) -
    normalizedTrace (flowDrift2 R₁ᴴ R₂ A (conj m₁) m₂ * Aᴴ) +
    normalizedTrace (flowDrift2 R₁ᴴ R₂ᴴ A (conj m₁) (conj m₂) * Aᴴ))

theorem fz_two_I_inv_sq : (2 * Complex.I)⁻¹ * (2 * Complex.I)⁻¹ = -(1 / 4 : ℂ) := by
  rw [← mul_inv, show (2 * Complex.I) * (2 * Complex.I) = -4 by
    ring_nf; rw [Complex.I_sq]; ring]
  norm_num

theorem fz_ofReal_im (a : ℂ) : ((a.im : ℝ) : ℂ) = (2 * Complex.I)⁻¹ * (a - conj a) := by
  rw [Complex.sub_conj]
  push_cast
  field_simp

theorem fz_re_neg_quarter_mul (w : ℂ) : (-(1 / 4 : ℂ) * w).re = -(1 / 4) * w.re := by
  simp [Complex.mul_re]

/-!
### Chain decomposition
-/

/-- `⟨Im R₁ A Im R₂ Aᴴ⟩ = -¼ (⟨R₁AR₂Aᴴ⟩ - ⟨R₁AR₂ᴴAᴴ⟩ - ⟨R₁ᴴAR₂Aᴴ⟩ + ⟨R₁ᴴAR₂ᴴAᴴ⟩)`. -/
theorem fz_chain_eq (R₁ R₂ A : Matrix (Fin N) (Fin N) ℂ) :
    fz_chain R₁ R₂ A = -(1 / 4 : ℂ) * (normalizedTrace (R₁ * A * R₂ * Aᴴ) -
      normalizedTrace (R₁ * A * R₂ᴴ * Aᴴ) - normalizedTrace (R₁ᴴ * A * R₂ * Aᴴ) +
      normalizedTrace (R₁ᴴ * A * R₂ᴴ * Aᴴ)) := by
  rw [← fz_two_I_inv_sq]
  simp only [fz_chain, External.CEH.imaginaryPart, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, Phase1.normalizedTrace_sub,
    Phase1.normalizedTrace_smul]
  ring

/-- `Z = Re⟨Im R₁ A Im R₂ Aᴴ⟩` as the real `-¼`-combination of four chains, `K = N⁻¹Aᴴ`. -/
theorem fz_re_chain_eq_reTr (R₁ R₂ A : Matrix (Fin N) (Fin N) ℂ) :
    (fz_chain R₁ R₂ A).re = -(1 / 4) * (reTr ((N : ℂ)⁻¹ • Aᴴ) (R₁ * A * R₂) -
      reTr ((N : ℂ)⁻¹ • Aᴴ) (R₁ * A * R₂ᴴ) - reTr ((N : ℂ)⁻¹ • Aᴴ) (R₁ᴴ * A * R₂) +
      reTr ((N : ℂ)⁻¹ • Aᴴ) (R₁ᴴ * A * R₂ᴴ)) := by
  rw [fz_chain_eq, fz_re_neg_quarter_mul]
  simp only [reTr_avgRe, Complex.add_re, Complex.sub_re]

/-!
### The bracket functional
-/

/-- `fz_D` as the `-¼`-combination of the four derivative matrices `PEPAQ + PAQEQ`. -/
theorem fz_D_eq (R₁ R₂ A E : Matrix (Fin N) (Fin N) ℂ) :
    fz_D R₁ R₂ A E = -(1 / 4 : ℂ) *
      (normalizedTrace ((R₁ * E * R₁ * A * R₂ + R₁ * A * R₂ * E * R₂) * Aᴴ) -
        normalizedTrace ((R₁ * E * R₁ * A * R₂ᴴ + R₁ * A * R₂ᴴ * E * R₂ᴴ) * Aᴴ) -
        normalizedTrace ((R₁ᴴ * E * R₁ᴴ * A * R₂ + R₁ᴴ * A * R₂ * E * R₂) * Aᴴ) +
        normalizedTrace ((R₁ᴴ * E * R₁ᴴ * A * R₂ᴴ + R₁ᴴ * A * R₂ᴴ * E * R₂ᴴ) * Aᴴ)) := by
  rw [← fz_two_I_inv_sq]
  simp only [fz_D, fz_imS, External.CEH.imaginaryPart, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_assoc,
    Phase1.normalizedTrace_sub, Phase1.normalizedTrace_add, Phase1.normalizedTrace_smul]
  ring

/-- Real form: the `-¼`-combination of the four first derivatives
`-Re tr(K(PEPAQ + PAQEQ))`, `K = N⁻¹Aᴴ`, is `-Re fz_D(E)`. -/
theorem fz_re_D_eq (R₁ R₂ A E : Matrix (Fin N) (Fin N) ℂ) :
    -(1 / 4) * (-reTr ((N : ℂ)⁻¹ • Aᴴ) (R₁ * E * R₁ * A * R₂ + R₁ * A * R₂ * E * R₂) -
        -reTr ((N : ℂ)⁻¹ • Aᴴ) (R₁ * E * R₁ * A * R₂ᴴ + R₁ * A * R₂ᴴ * E * R₂ᴴ) -
        -reTr ((N : ℂ)⁻¹ • Aᴴ) (R₁ᴴ * E * R₁ᴴ * A * R₂ + R₁ᴴ * A * R₂ * E * R₂) +
        -reTr ((N : ℂ)⁻¹ • Aᴴ) (R₁ᴴ * E * R₁ᴴ * A * R₂ᴴ + R₁ᴴ * A * R₂ᴴ * E * R₂ᴴ)) =
      -(fz_D R₁ R₂ A E).re := by
  rw [fz_D_eq, fz_re_neg_quarter_mul]
  simp only [reTr_avgRe, Complex.add_re, Complex.sub_re]
  ring

/-!
### The drift
-/

/-- The real drift of `Z`: the `-¼`-combination of the four drifts. -/
theorem fz_re_driftC_eq_reTr (R₁ R₂ A : Matrix (Fin N) (Fin N) ℂ) (m₁ m₂ : ℂ) :
    (fz_driftC R₁ R₂ A m₁ m₂).re =
      -(1 / 4) * (reTr ((N : ℂ)⁻¹ • Aᴴ) (flowDrift2 R₁ R₂ A m₁ m₂) -
        reTr ((N : ℂ)⁻¹ • Aᴴ) (flowDrift2 R₁ R₂ᴴ A m₁ (conj m₂)) -
        reTr ((N : ℂ)⁻¹ • Aᴴ) (flowDrift2 R₁ᴴ R₂ A (conj m₁) m₂) +
        reTr ((N : ℂ)⁻¹ • Aᴴ) (flowDrift2 R₁ᴴ R₂ᴴ A (conj m₁) (conj m₂))) := by
  rw [fz_driftC, fz_re_neg_quarter_mul]
  simp only [reTr_avgRe, Complex.add_re, Complex.sub_re]

/-- **Drift identity, algebraic form** (arbitrary matrices `R₁, R₂`), `a_i = ⟨R_i⟩ - m_i`,
`I_i = Im R_i`. -/
theorem fz_driftC_eq (R₁ R₂ A : Matrix (Fin N) (Fin N) ℂ) (m₁ m₂ : ℂ) :
    fz_driftC R₁ R₂ A m₁ m₂ =
      (normalizedTrace R₁ - m₁) * normalizedTrace (R₁ * External.CEH.imaginaryPart R₁ * A *
          External.CEH.imaginaryPart R₂ * Aᴴ) +
        conj (normalizedTrace R₁ - m₁) * normalizedTrace (External.CEH.imaginaryPart R₁ * R₁ᴴ *
          A * External.CEH.imaginaryPart R₂ * Aᴴ) +
        (((normalizedTrace R₁ - m₁).im : ℝ) : ℂ) * normalizedTrace (R₁ * R₁ᴴ * A *
          External.CEH.imaginaryPart R₂ * Aᴴ) +
        (normalizedTrace R₂ - m₂) * normalizedTrace (External.CEH.imaginaryPart R₁ * A * R₂ *
          External.CEH.imaginaryPart R₂ * Aᴴ) +
        conj (normalizedTrace R₂ - m₂) * normalizedTrace (External.CEH.imaginaryPart R₁ * A *
          External.CEH.imaginaryPart R₂ * R₂ᴴ * Aᴴ) +
        (((normalizedTrace R₂ - m₂).im : ℝ) : ℂ) * normalizedTrace
          (External.CEH.imaginaryPart R₁ * A * R₂ * R₂ᴴ * Aᴴ) +
        normalizedTrace (External.CEH.imaginaryPart R₁ * A * R₂) *
          normalizedTrace (External.CEH.imaginaryPart R₂ * Aᴴ * R₁) +
        normalizedTrace (External.CEH.imaginaryPart R₁ * A * External.CEH.imaginaryPart R₂) *
          normalizedTrace (R₂ᴴ * Aᴴ * R₁) +
        normalizedTrace (R₁ᴴ * A * R₂) * normalizedTrace (External.CEH.imaginaryPart R₂ * Aᴴ *
          External.CEH.imaginaryPart R₁) +
        normalizedTrace (R₁ᴴ * A * External.CEH.imaginaryPart R₂) *
          normalizedTrace (R₂ᴴ * Aᴴ * External.CEH.imaginaryPart R₁) := by
  rw [fz_driftC, fz_ofReal_im, fz_ofReal_im, ← fz_two_I_inv_sq]
  simp only [normalizedTrace_flowDrift2_mul, Phase1.normalizedTrace_conjTranspose, map_sub,
    External.CEH.imaginaryPart, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.mul_assoc, Phase1.normalizedTrace_sub, Phase1.normalizedTrace_smul]
  ring

/-!
### CEH (7.2) form for resolvents
-/

section Resolvents

variable {H : Matrix (Fin N) (Fin N) ℂ}

/-- `Rᴴ Im R = Im R Rᴴ` for a resolvent. -/
theorem fz_conjTranspose_mul_imaginaryPart_comm (hH : H.IsHermitian) {w : ℂ} (hw : w.im ≠ 0) :
    (Phase1.resolvent H w)ᴴ * External.CEH.imaginaryPart (Phase1.resolvent H w) =
      External.CEH.imaginaryPart (Phase1.resolvent H w) * (Phase1.resolvent H w)ᴴ := by
  nth_rewrite 1 [Phase1.imaginaryPart_resolvent hH hw]
  rw [Phase1.imaginaryPart_resolvent' hH hw, Matrix.mul_smul, Matrix.smul_mul]
  simp only [Matrix.mul_assoc]

/-- **Drift identity, CEH (7.2) form**, in variance time (`λ = 1`, no `+Z` term), for resolvents
`R_i = (H - w_i)⁻¹`, `a_i = ⟨R_i⟩ - m_i`, `I_i = Im R_i`, with `η_i` the signed `Im w_i`. -/
theorem fz_driftC_eq_ceh (hH : H.IsHermitian) {w₁ w₂ : ℂ} (hw₁ : w₁.im ≠ 0) (hw₂ : w₂.im ≠ 0)
    (A : Matrix (Fin N) (Fin N) ℂ) (m₁ m₂ : ℂ) :
    fz_driftC (Phase1.resolvent H w₁) (Phase1.resolvent H w₂) A m₁ m₂ =
      (((normalizedTrace (Phase1.resolvent H w₁) - m₁).im / w₁.im +
          (normalizedTrace (Phase1.resolvent H w₂) - m₂).im / w₂.im : ℝ) : ℂ) *
          fz_chain (Phase1.resolvent H w₁) (Phase1.resolvent H w₂) A +
        normalizedTrace ((Phase1.resolvent H w₂)ᴴ * Aᴴ * Phase1.resolvent H w₁) *
          normalizedTrace (External.CEH.imaginaryPart (Phase1.resolvent H w₁) * A *
            External.CEH.imaginaryPart (Phase1.resolvent H w₂)) +
        normalizedTrace ((Phase1.resolvent H w₁)ᴴ * A * Phase1.resolvent H w₂) *
          normalizedTrace (External.CEH.imaginaryPart (Phase1.resolvent H w₂) * Aᴴ *
            External.CEH.imaginaryPart (Phase1.resolvent H w₁)) +
        normalizedTrace (External.CEH.imaginaryPart (Phase1.resolvent H w₁) * A *
            Phase1.resolvent H w₂) *
          normalizedTrace (External.CEH.imaginaryPart (Phase1.resolvent H w₂) * Aᴴ *
            Phase1.resolvent H w₁) +
        normalizedTrace ((Phase1.resolvent H w₂)ᴴ * Aᴴ *
            External.CEH.imaginaryPart (Phase1.resolvent H w₁)) *
          normalizedTrace ((Phase1.resolvent H w₁)ᴴ * A *
            External.CEH.imaginaryPart (Phase1.resolvent H w₂)) +
        (normalizedTrace (Phase1.resolvent H w₁) - m₁) *
          normalizedTrace (External.CEH.imaginaryPart (Phase1.resolvent H w₁) * A *
            External.CEH.imaginaryPart (Phase1.resolvent H w₂) * Aᴴ * Phase1.resolvent H w₁) +
        (normalizedTrace (Phase1.resolvent H w₂) - m₂) *
          normalizedTrace (External.CEH.imaginaryPart (Phase1.resolvent H w₂) * Aᴴ *
            External.CEH.imaginaryPart (Phase1.resolvent H w₁) * A * Phase1.resolvent H w₂) +
        conj (normalizedTrace (Phase1.resolvent H w₁) - m₁) *
          normalizedTrace (External.CEH.imaginaryPart (Phase1.resolvent H w₁) * A *
            External.CEH.imaginaryPart (Phase1.resolvent H w₂) * Aᴴ * (Phase1.resolvent H w₁)ᴴ) +
        conj (normalizedTrace (Phase1.resolvent H w₂) - m₂) *
          normalizedTrace (External.CEH.imaginaryPart (Phase1.resolvent H w₂) * Aᴴ *
            External.CEH.imaginaryPart (Phase1.resolvent H w₁) * A *
              (Phase1.resolvent H w₂)ᴴ) := by
  set R₁ := Phase1.resolvent H w₁
  set R₂ := Phase1.resolvent H w₂
  set I₁ := External.CEH.imaginaryPart R₁
  set I₂ := External.CEH.imaginaryPart R₂
  have e1 : normalizedTrace (R₁ * I₁ * A * I₂ * Aᴴ) = normalizedTrace (I₁ * A * I₂ * Aᴴ * R₁) := by
    rw [show R₁ * I₁ * A * I₂ * Aᴴ = R₁ * (I₁ * A * I₂ * Aᴴ) by simp only [Matrix.mul_assoc],
      Phase1.normalizedTrace_mul_comm]
  have e2 : normalizedTrace (I₁ * R₁ᴴ * A * I₂ * Aᴴ) =
      normalizedTrace (I₁ * A * I₂ * Aᴴ * R₁ᴴ) := by
    rw [← fz_conjTranspose_mul_imaginaryPart_comm hH hw₁,
      show R₁ᴴ * I₁ * A * I₂ * Aᴴ = R₁ᴴ * (I₁ * A * I₂ * Aᴴ) by simp only [Matrix.mul_assoc],
      Phase1.normalizedTrace_mul_comm]
  have e3 : normalizedTrace (R₁ * R₁ᴴ * A * I₂ * Aᴴ) = (w₁.im : ℂ)⁻¹ * fz_chain R₁ R₂ A := by
    rw [Phase1.resolvent_mul_conjTranspose hH hw₁]
    simp only [Matrix.smul_mul, Phase1.normalizedTrace_smul]
    rfl
  have e4 : normalizedTrace (I₁ * A * R₂ * I₂ * Aᴴ) = normalizedTrace (I₂ * Aᴴ * I₁ * A * R₂) := by
    rw [show I₁ * A * R₂ * I₂ * Aᴴ = (I₁ * A * R₂) * (I₂ * Aᴴ) by simp only [Matrix.mul_assoc],
      Phase1.normalizedTrace_mul_comm]
    simp only [Matrix.mul_assoc]
  have e5 : normalizedTrace (I₁ * A * I₂ * R₂ᴴ * Aᴴ) =
      normalizedTrace (I₂ * Aᴴ * I₁ * A * R₂ᴴ) := by
    rw [show I₁ * A * I₂ * R₂ᴴ * Aᴴ = I₁ * A * (I₂ * R₂ᴴ) * Aᴴ by simp only [Matrix.mul_assoc],
      ← fz_conjTranspose_mul_imaginaryPart_comm hH hw₂,
      show I₁ * A * (R₂ᴴ * I₂) * Aᴴ = (I₁ * A * R₂ᴴ) * (I₂ * Aᴴ) by simp only [Matrix.mul_assoc],
      Phase1.normalizedTrace_mul_comm]
    simp only [Matrix.mul_assoc]
  have e6 : normalizedTrace (I₁ * A * R₂ * R₂ᴴ * Aᴴ) = (w₂.im : ℂ)⁻¹ * fz_chain R₁ R₂ A := by
    rw [show I₁ * A * R₂ * R₂ᴴ * Aᴴ = I₁ * A * (R₂ * R₂ᴴ) * Aᴴ by simp only [Matrix.mul_assoc],
      Phase1.resolvent_mul_conjTranspose hH hw₂, Matrix.mul_smul, Matrix.smul_mul,
      Phase1.normalizedTrace_smul]
    rfl
  rw [fz_driftC_eq, e1, e2, e3, e4, e5, e6]
  push_cast
  ring

/-- The CEH (7.2) drift (variance time, `λ = 1`, signed `η_i = Im w_i`), as a function of the
matrices `R_i`, the parameters `m_i` and the spectral parameters `w_i`; see `fz_driftC_eq_ceh`. -/
def fz_cehDrift (R₁ R₂ A : Matrix (Fin N) (Fin N) ℂ) (m₁ m₂ w₁ w₂ : ℂ) : ℂ :=
  (((normalizedTrace R₁ - m₁).im / w₁.im + (normalizedTrace R₂ - m₂).im / w₂.im : ℝ) : ℂ) *
      fz_chain R₁ R₂ A +
    normalizedTrace (R₂ᴴ * Aᴴ * R₁) * normalizedTrace (External.CEH.imaginaryPart R₁ * A *
      External.CEH.imaginaryPart R₂) +
    normalizedTrace (R₁ᴴ * A * R₂) * normalizedTrace (External.CEH.imaginaryPart R₂ * Aᴴ *
      External.CEH.imaginaryPart R₁) +
    normalizedTrace (External.CEH.imaginaryPart R₁ * A * R₂) *
      normalizedTrace (External.CEH.imaginaryPart R₂ * Aᴴ * R₁) +
    normalizedTrace (R₂ᴴ * Aᴴ * External.CEH.imaginaryPart R₁) *
      normalizedTrace (R₁ᴴ * A * External.CEH.imaginaryPart R₂) +
    (normalizedTrace R₁ - m₁) * normalizedTrace (External.CEH.imaginaryPart R₁ * A *
      External.CEH.imaginaryPart R₂ * Aᴴ * R₁) +
    (normalizedTrace R₂ - m₂) * normalizedTrace (External.CEH.imaginaryPart R₂ * Aᴴ *
      External.CEH.imaginaryPart R₁ * A * R₂) +
    conj (normalizedTrace R₁ - m₁) * normalizedTrace (External.CEH.imaginaryPart R₁ * A *
      External.CEH.imaginaryPart R₂ * Aᴴ * R₁ᴴ) +
    conj (normalizedTrace R₂ - m₂) * normalizedTrace (External.CEH.imaginaryPart R₂ * Aᴴ *
      External.CEH.imaginaryPart R₁ * A * R₂ᴴ)

/-- `fz_driftC_eq_ceh` with the right side folded into `fz_cehDrift`. -/
theorem fz_driftC_eq_cehDrift (hH : H.IsHermitian) {w₁ w₂ : ℂ} (hw₁ : w₁.im ≠ 0)
    (hw₂ : w₂.im ≠ 0) (A : Matrix (Fin N) (Fin N) ℂ) (m₁ m₂ : ℂ) :
    fz_driftC (Phase1.resolvent H w₁) (Phase1.resolvent H w₂) A m₁ m₂ =
      fz_cehDrift (Phase1.resolvent H w₁) (Phase1.resolvent H w₂) A m₁ m₂ w₁ w₂ := by
  rw [fz_driftC_eq_ceh hH hw₁ hw₂]
  rfl

end Resolvents

end BlockBand.Native.CEH.ETH
