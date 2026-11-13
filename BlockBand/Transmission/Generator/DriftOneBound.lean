module

public import BlockBand.Transmission.Generator.DriftCond
public import BlockBand.Transmission.LengthUniform.BulkMassMoment

/-!
# The `k = 1` drift error: almost-sure bound

* `drift_one_alg`: `|4η(m - q) + D(4ηq)²/(2W)| ≤ 4ηρ + 8η²q²|D - D'|/W + 4ηα²q³/W²` when
  `|m - q/(1+αq/W)| ≤ ρ` and `α = 2ηD'` (the `-αq²/W` drift is `-(D₀/2)g²/W`, `g = 4ηq`).
* `driftError_one_le`: `b, κ` first, then `C, W₀`; for `W ≥ W₀`, `E' ∈ bulkInterval κ`, `r ≥ 1`,
  a.s. `|driftError_r| ≤ 4C·refinedErr(X_r) + 8q²|D₀(E) - D₀(E')|/W + 4α_L²q³/W²`.
* `rf_err_le`: `refinedErr ≤ 9(Wδ₀+1)²(√Wτ+1)(q+1)³/W^{3/2}` (normalised moments).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer BlockBand.Transmission.PathScalar
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.LengthUniform
open scoped ENNReal

variable {W : ℕ}

theorem etaZ_le_one {b E : ℝ} (hb0 : 0 < b) (hb : b < 1) (h1 : -2 < E) (h2 : E < 2) :
    etaZ b E ≤ 1 := by
  rw [PassiveCovariance.etaZ_eq b E h1 h2]
  have h := Complex.abs_im_le_norm (matchedA E)
  rw [PassiveCovariance.norm_matchedA E h1 h2] at h
  have := neg_abs_le (matchedA E).im
  nlinarith

/-- `α = 2ηD₀` (`α/(4η) = D₀/2`). -/
theorem alphaCoef_eq {b E : ℝ} (hb0 : 0 < b) (hb : b < 1) (h1 : -2 < E) (h2 : E < 2) :
    alphaCoef b E = 2 * etaZ b E * transportD0 b E := by
  have hη := PassiveCovariance.etaZ_pos b E hb h1 h2
  have hs := PassiveCovariance.sigmaPlus_eq b E hb0 h1 h2
  rw [sigmaPlus, kPlus] at hs
  rw [alphaCoef]
  field_simp
  have : (1 - b) ^ 2 = 1 - 2 * b + b ^ 2 := by ring
  rw [this]
  field_simp at hs
  nlinarith

/-- **Scalar drift algebra at `k = 1`.** -/
theorem drift_one_alg {m q η α D D' W ρ : ℝ} (hη : 0 < η) (hq : 0 ≤ q) (hα0 : 0 ≤ α)
    (hW : 0 < W) (hα : α = 2 * η * D') (hm : |m - q / (1 + α * q / W)| ≤ ρ) :
    |4 * η * (m - q) + D * (4 * η * q) ^ 2 / (2 * W)| ≤
      4 * η * ρ + 8 * η ^ 2 * q ^ 2 * |D - D'| / W + 4 * η * α ^ 2 * q ^ 3 / W ^ 2 := by
  set B := 1 + α * q / W
  have hB : 1 ≤ B := by have : 0 ≤ α * q / W := by positivity
                        simp only [B]; linarith
  have hB0 : 0 < B := by linarith
  have e : 4 * η * (m - q) + D * (4 * η * q) ^ 2 / (2 * W) =
      4 * η * (m - q / B) + 8 * η ^ 2 * q ^ 2 * (D - D') / W +
        4 * η * α * q ^ 2 / W * ((α * q / W) / B) := by
    have k1 : q - q / B = q * (α * q / W) / B := by
      rw [eq_div_iff hB0.ne', sub_mul, div_mul_cancel₀ _ hB0.ne']; simp only [B]; ring
    have k2 : (α * q / W) / B * (4 * η * α * q ^ 2 / W) + 4 * η * q * (α * q / W) / B =
        4 * η * α * q ^ 2 / W := by
      have h : (α * q / W) / B * (4 * η * α * q ^ 2 / W) + 4 * η * q * (α * q / W) / B =
          4 * η * α * q ^ 2 / W * (B / B) := by simp only [B]; ring
      rw [h, div_self hB0.ne', mul_one]
    linear_combination (-4 * η) * k1 - k2 + (-4 * η * q ^ 2 / W) * hα
  rw [e]
  have t1 : |4 * η * (m - q / B)| ≤ 4 * η * ρ := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * η)]
    exact mul_le_mul_of_nonneg_left hm (by positivity)
  have t2 : |8 * η ^ 2 * q ^ 2 * (D - D') / W| = 8 * η ^ 2 * q ^ 2 * |D - D'| / W := by
    rw [abs_div, abs_mul, abs_of_pos hW, abs_of_nonneg (by positivity)]
  have t3 : |4 * η * α * q ^ 2 / W * ((α * q / W) / B)| ≤ 4 * η * α ^ 2 * q ^ 3 / W ^ 2 := by
    rw [abs_of_nonneg (by positivity)]
    have : (α * q / W) / B ≤ α * q / W := div_le_self (by positivity) hB
    calc 4 * η * α * q ^ 2 / W * ((α * q / W) / B) ≤ 4 * η * α * q ^ 2 / W * (α * q / W) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by field_simp
  calc _ ≤ |4 * η * (m - q / B) + 8 * η ^ 2 * q ^ 2 * (D - D') / W| +
        |4 * η * α * q ^ 2 / W * ((α * q / W) / B)| := abs_add_le _ _
    _ ≤ |4 * η * (m - q / B)| + |8 * η ^ 2 * q ^ 2 * (D - D') / W| +
        |4 * η * α * q ^ 2 / W * ((α * q / W) / B)| := by gcongr; exact abs_add_le _ _
    _ ≤ _ := by rw [t2]; linarith

/-- **Almost-sure bound of the `k = 1` drift error**, bulk-uniform. -/
theorem driftError_one_le (hA : PassiveBoundsStatement) {b κ : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hκ : 0 < κ) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ 1 ≤ W₀ ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E' ∈ bulkInterval κ, ∀ E : ℝ,
      ∀ r : ℕ, 1 ≤ r → ∀ᵐ ω ∂growthPathLaw W b,
        |driftError b E E' W 1 r ω| ≤ 4 * C * refinedErr b E' (pathX b E' W r ω) +
          8 * qc b E' (pathX b E' W r ω) ^ 2 * |transportD0 b E - transportD0 b E'| / W +
          4 * ((1 - b) ^ 2 / (b * etaLow b κ)) ^ 2 * qc b E' (pathX b E' W r ω) ^ 3 /
            (W : ℝ) ^ 2 := by
  obtain ⟨C, W₁, hC, hR⟩ := massMeanRefined_bulk hA hb0 hb hκ
  obtain ⟨Cf, W₂, -, hF⟩ := ml_fresh_bulk hA hb0 hb hκ 1 le_rfl
  refine ⟨C, max (max W₁ W₂) 1, hC, le_max_right _ _, fun W hW E' hE' E r hr => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW1, hW2⟩, hW0⟩ := hW
  have h1 : -2 < E' := by have := hE'.1; linarith
  have h2 : E' < 2 := by have := hE'.2; linarith
  have hη := PassiveCovariance.etaZ_pos b E' (by linarith) h1 h2
  have hη1 := etaZ_le_one hb0 (by linarith) h1 h2
  have hηL : 0 < etaLow b κ := etaLow_pos (by linarith) hκ
  have hηLη : etaLow b κ ≤ etaZ b E' := etaLow_le (by linarith) hκ hE'
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW0
  filter_upwards [driftError_one_ae (E := E) (W := W) hb h1 h2 hW0 hr,
    mm_ae_passive (W := W) (b := b) (by linarith) h1 h2 r] with ω hω hY
  rw [hω]
  set X := pathX b E' W r ω
  have hm := (hF W hW2 E' hE' X hY).1
  rw [hm, qc_eq hY]
  have hq := PassiveCovariance.passiveMass_nonneg b E' hY
  have hα0 : 0 ≤ alphaCoef b E' := by rw [alphaCoef]; positivity
  have hbd := drift_one_alg (D := transportD0 b E) hη hq hα0 hWpos
    (alphaCoef_eq hb0 (by linarith) h1 h2) (hR W hW1 E' hE' X hY)
  refine hbd.trans ?_
  have hαL : alphaCoef b E' ≤ (1 - b) ^ 2 / (b * etaLow b κ) := by
    rw [alphaCoef]; gcongr
  have hErr := refinedErr_nonneg (W := W) b E' hY
  have a1 : 4 * etaZ b E' * (C * refinedErr b E' X) ≤ 4 * C * refinedErr b E' X := by
    have : etaZ b E' * (C * refinedErr b E' X) ≤ 1 * (C * refinedErr b E' X) :=
      mul_le_mul_of_nonneg_right hη1 (by positivity)
    linarith
  have a2 : 8 * etaZ b E' ^ 2 * passiveMass b E' X ^ 2 * |transportD0 b E - transportD0 b E'| / W
      ≤ 8 * passiveMass b E' X ^ 2 * |transportD0 b E - transportD0 b E'| / W := by
    have h5 : etaZ b E' ^ 2 ≤ 1 := by nlinarith
    have h6 : 0 ≤ 8 * passiveMass b E' X ^ 2 * |transportD0 b E - transportD0 b E'| / W := by
      positivity
    calc 8 * etaZ b E' ^ 2 * passiveMass b E' X ^ 2 * |transportD0 b E - transportD0 b E'| / W
        = etaZ b E' ^ 2 * (8 * passiveMass b E' X ^ 2 * |transportD0 b E - transportD0 b E'| / W) :=
          by ring
      _ ≤ 1 * (8 * passiveMass b E' X ^ 2 * |transportD0 b E - transportD0 b E'| / W) :=
          mul_le_mul_of_nonneg_right h5 h6
      _ = _ := one_mul _
  have a3 : 4 * etaZ b E' * alphaCoef b E' ^ 2 * passiveMass b E' X ^ 3 / (W : ℝ) ^ 2 ≤
      4 * ((1 - b) ^ 2 / (b * etaLow b κ)) ^ 2 * passiveMass b E' X ^ 3 / (W : ℝ) ^ 2 := by
    have : etaZ b E' * alphaCoef b E' ^ 2 ≤ 1 * ((1 - b) ^ 2 / (b * etaLow b κ)) ^ 2 :=
      mul_le_mul hη1 (pow_le_pow_left₀ hα0 hαL 2) (by positivity) zero_le_one
    have h4 : 4 * etaZ b E' * alphaCoef b E' ^ 2 = 4 * (etaZ b E' * alphaCoef b E' ^ 2) := by ring
    rw [h4]
    gcongr
    linarith
  linarith

/-- **Normalised form of `refinedErr`**: with `s = √W ≥ 1`,
`refinedErr ≤ 9(s²δ₀+1)²(sτ+1)(q+1)³/s³`. -/
theorem rf_err_le {δ τ q s : ℝ} (hs : 1 ≤ s) (hδ : 0 ≤ δ) (hτ : 0 ≤ τ) (hq : 0 ≤ q) :
    (δ + (s ^ 2)⁻¹ ^ 2) * τ + (δ + (s ^ 2)⁻¹ ^ 2) ^ 2 * q + (δ + (s ^ 2)⁻¹ ^ 2) * q ^ 2 / s ^ 2 +
        (s ^ 2)⁻¹ ^ 2 * q ≤
      9 * ((s ^ 2 * δ + 1) ^ 2 * (s * τ + 1) * (q + 1) ^ 3) / s ^ 3 := by
  have hs0 : 0 < s := by linarith
  set A := s ^ 2 * δ + 1
  set T := s * τ + 1
  set Q := q + 1
  have hA : 1 ≤ A := by simp only [A]; nlinarith
  have hT : 1 ≤ T := by simp only [T]; nlinarith
  have hQ : 1 ≤ Q := by simp only [Q]; linarith
  have hPpos : 1 ≤ A ^ 2 * T * Q ^ 3 :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hA) hT)
      (one_le_pow₀ hQ)
  set P := A ^ 2 * T * Q ^ 3
  have hδA : δ = (A - 1) / s ^ 2 := by simp only [A]; field_simp; ring
  have hτT : τ = (T - 1) / s := by simp only [T]; field_simp; ring
  have hqQ : q = Q - 1 := by simp only [Q]; ring
  have he : δ + (s ^ 2)⁻¹ ^ 2 ≤ 2 * A / s ^ 2 := by
    rw [hδA]
    have : (s ^ 2)⁻¹ ^ 2 ≤ 1 / s ^ 2 := by
      rw [inv_pow, ← pow_mul, one_div]
      exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hs (by norm_num))
    have h2 : (A - 1) / s ^ 2 + 1 / s ^ 2 = A / s ^ 2 := by field_simp; ring
    have h3 : A / s ^ 2 ≤ 2 * A / s ^ 2 := by
      apply div_le_div_of_nonneg_right _ (by positivity); linarith
    linarith
  have he0 : 0 ≤ δ + (s ^ 2)⁻¹ ^ 2 := by positivity
  set e := δ + (s ^ 2)⁻¹ ^ 2
  have hs3 : s ^ 3 ≤ s ^ 4 := pow_le_pow_right₀ hs (by norm_num)
  have hτ' : τ ≤ T / s := by rw [hτT]; apply div_le_div_of_nonneg_right _ hs0.le; linarith
  have hq' : q ≤ Q := by linarith
  have b1 : e * τ ≤ 2 * P / s ^ 3 := by
    calc e * τ ≤ 2 * A / s ^ 2 * (T / s) := mul_le_mul he hτ' hτ (by positivity)
      _ = 2 * (A * T) / s ^ 3 := by field_simp
      _ ≤ 2 * P / s ^ 3 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have : A * T ≤ P := by
          rw [show P = A * T * (A * Q ^ 3) by simp only [P]; ring]
          exact le_mul_of_one_le_right (by positivity)
            (one_le_mul_of_one_le_of_one_le hA (one_le_pow₀ hQ))
        linarith
  have b2 : e ^ 2 * q ≤ 4 * P / s ^ 3 := by
    calc e ^ 2 * q ≤ (2 * A / s ^ 2) ^ 2 * Q := mul_le_mul (pow_le_pow_left₀ he0 he 2) hq' hq
          (by positivity)
      _ = 4 * (A ^ 2 * Q) / s ^ 4 := by field_simp; ring
      _ ≤ 4 * (A ^ 2 * Q) / s ^ 3 := div_le_div_of_nonneg_left (by positivity) (by positivity) hs3
      _ ≤ 4 * P / s ^ 3 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have : A ^ 2 * Q ≤ P := by
          rw [show P = A ^ 2 * Q * (T * Q ^ 2) by simp only [P]; ring]
          exact le_mul_of_one_le_right (by positivity)
            (one_le_mul_of_one_le_of_one_le hT (one_le_pow₀ hQ))
        linarith
  have b3 : e * q ^ 2 / s ^ 2 ≤ 2 * P / s ^ 3 := by
    calc e * q ^ 2 / s ^ 2 ≤ 2 * A / s ^ 2 * Q ^ 2 / s ^ 2 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul he (pow_le_pow_left₀ hq hq' 2) (by positivity) (by positivity)
      _ = 2 * (A * Q ^ 2) / s ^ 4 := by field_simp
      _ ≤ 2 * (A * Q ^ 2) / s ^ 3 := div_le_div_of_nonneg_left (by positivity) (by positivity) hs3
      _ ≤ 2 * P / s ^ 3 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have : A * Q ^ 2 ≤ P := by
          rw [show P = A * Q ^ 2 * (A * T * Q) by simp only [P]; ring]
          exact le_mul_of_one_le_right (by positivity)
            (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hA hT) hQ)
        linarith
  have b4 : (s ^ 2)⁻¹ ^ 2 * q ≤ P / s ^ 3 := by
    calc (s ^ 2)⁻¹ ^ 2 * q ≤ Q / s ^ 4 := by
          rw [inv_pow, ← pow_mul, inv_mul_eq_div]
          exact div_le_div_of_nonneg_right hq' (by positivity)
      _ ≤ Q / s ^ 3 := div_le_div_of_nonneg_left (by positivity) (by positivity) hs3
      _ ≤ P / s ^ 3 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        rw [show P = Q * (A ^ 2 * T * Q ^ 2) by simp only [P]; ring]
        exact le_mul_of_one_le_right (by positivity)
          (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hA) hT)
            (one_le_pow₀ hQ))
  have hsum : 9 * P / s ^ 3 = 2 * P / s ^ 3 + 4 * P / s ^ 3 + 2 * P / s ^ 3 + P / s ^ 3 := by ring
  rw [hsum]
  linarith

end BlockBand.Transmission.Generator
