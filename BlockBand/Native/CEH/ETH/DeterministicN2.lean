module

public import BlockBand.Native.CEH.ETH.DeterministicWard

/-!
# CEH ETH: the deterministic bound `ρ₁ρ₂ s₂² ≤ C(s, K)`

For the `θ = 1` regularized observable and MDE solutions bounded by `K` with `Im⟨Mᵢ⟩ ≥ κ`, the
densities and the hybrid control satisfy (`density_mul_sTwo_sq_le`)
`ρ₁ρ₂ s₂² ≤ (1 + 2sK²)² (K² + K⁴/(2κ²)) / π²`.
Hypotheses: `s, κ > 0`, `‖Mᵢ‖ ≤ K`, `κ ≤ Im⟨Mᵢ⟩`, `s a(Mᵢ) ≤ 1` (automatic for MDE solutions,
`density_mul_sTwo_sq_le_mde`), `‖J‖ ≤ 1` and the CEH cutoff
`regularizationCoefficient (√s) M₁ M₂ᴴ = 1`; the bound is deterministic.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.ETH

open Matrix
open CEHNative.BlockBand CEHNative.BlockBand.External.CEH
open BlockBand.Internal.Contracts.Inputs (IsManuscriptMDE)
open scoped ComplexConjugate Matrix.Norms.L2Operator

variable {N : ℕ}

theorem norm_conjTranspose_eq (X : Matrix (Fin N) (Fin N) ℂ) : ‖Xᴴ‖ = ‖X‖ :=
  Matrix.l2_opNorm_conjTranspose X

theorem norm_matrixImaginaryPart_le (X : Matrix (Fin N) (Fin N) ℂ) :
    ‖matrixImaginaryPart X‖ ≤ ‖X‖ := by
  rw [matrixImaginaryPart, norm_smul]
  have h : ‖(-Complex.I / 2 : ℂ)‖ = 1 / 2 := by
    rw [norm_div, norm_neg, Complex.norm_I]; norm_num
  rw [h]
  have := norm_sub_le X Xᴴ
  rw [norm_conjTranspose_eq] at this
  linarith

theorem re_NTrace_matrixImaginaryPart (X : Matrix (Fin N) (Fin N) ℂ) :
    (NTrace (matrixImaginaryPart X)).re = (NTrace X).im :=
  gridPair_re_NTrace_matrixImaginaryPart X

/-- `‖Γ‖ ≤ ‖M‖ / Im⟨M⟩` for `Im⟨M⟩ > 0`. -/
theorem norm_gammaMatrix_le (X : Matrix (Fin N) (Fin N) ℂ) (ht : 0 < (NTrace X).im) :
    ‖gammaMatrix X‖ ≤ ‖X‖ / (NTrace X).im := by
  rw [gammaMatrix, norm_smul, norm_inv]
  have hre := Complex.re_le_norm (NTrace (matrixImaginaryPart X))
  rw [re_NTrace_matrixImaginaryPart] at hre
  have hpos : 0 < ‖NTrace (matrixImaginaryPart X)‖ := lt_of_lt_of_le ht hre
  rw [inv_mul_eq_div, div_le_div_iff₀ hpos ht]
  have := norm_matrixImaginaryPart_le X
  have h0 := norm_nonneg (matrixImaginaryPart X)
  nlinarith [norm_nonneg X]

/-- `|⟨X Y Z⟩| ≤ ‖X‖‖Y‖‖Z‖` (normalized trace, `L²` operator norm). -/
theorem norm_NTrace_mul₃_le (hN : 0 < N) (X Y Z : Matrix (Fin N) (Fin N) ℂ) :
    ‖NTrace (X * Y * Z)‖ ≤ ‖X‖ * ‖Y‖ * ‖Z‖ :=
  (CEHNative.BlockBand.CEH.norm_normalizedTrace_le_localETHNorm hN _).trans
    ((norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _))

theorem norm_NTrace_mul₄_le (hN : 0 < N) (W X Y Z : Matrix (Fin N) (Fin N) ℂ) :
    ‖NTrace (W * X * Y * Z)‖ ≤ ‖W‖ * ‖X‖ * ‖Y‖ * ‖Z‖ := by
  refine (CEHNative.BlockBand.CEH.norm_normalizedTrace_le_localETHNorm hN _).trans ?_
  refine (norm_mul_le _ _).trans ?_
  gcongr
  refine (norm_mul_le _ _).trans ?_
  gcongr
  exact norm_mul_le _ _

/-- **Norm of the `θ = 1` regularized observable**: if `θ = 1`, `‖Mᵢ‖ ≤ K` and `‖J‖ ≤ 1` then
`‖A°‖ ≤ 1 + 2 s K²`. -/
theorem norm_regularizedObservable_le (hN : 0 < N) {s K : ℝ} (hs : 0 < s)
    {M₁ M₂ J : Matrix (Fin N) (Fin N) ℂ} (hK₁ : ‖M₁‖ ≤ K) (hK₂ : ‖M₂‖ ≤ K) (hJ : ‖J‖ ≤ 1)
    (hθ : regularizationCoefficient (Real.sqrt s : ℂ) M₁ M₂ᴴ = 1) :
    ‖regularizedObservable 1 M₁ M₂ᴴ J‖ ≤ 1 + 2 * s * K ^ 2 := by
  have : NeZero N := ⟨hN.ne'⟩
  have hK : 0 ≤ K := (norm_nonneg _).trans hK₁
  have harg : 0 ≤ ((Real.sqrt s : ℂ) ^ 2 * NTrace (M₁ * M₂ᴴ)).re - 1 / 2 := by
    by_contra hneg
    unfold regularizationCoefficient at hθ
    rw [cehTheta_of_neg (not_le.mp hneg)] at hθ
    norm_num at hθ
  rw [← Complex.ofReal_pow, Real.sq_sqrt hs.le, Complex.re_ofReal_mul] at harg
  have hden : 1 / (2 * s) ≤ ‖NTrace (M₁ * M₂ᴴ)‖ := by
    have := Complex.re_le_norm (NTrace (M₁ * M₂ᴴ))
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hdenpos : 0 < ‖NTrace (M₁ * M₂ᴴ)‖ := lt_of_lt_of_le (by positivity) hden
  have hnum : ‖NTrace (M₁ * J * M₂ᴴ)‖ ≤ K * 1 * K := by
    refine (norm_NTrace_mul₃_le hN _ _ _).trans ?_
    rw [norm_conjTranspose_eq]
    gcongr
  have hratio : ‖NTrace (M₁ * J * M₂ᴴ) / NTrace (M₁ * M₂ᴴ)‖ ≤ 2 * s * K ^ 2 := by
    rw [norm_div, div_le_iff₀ hdenpos]
    calc ‖NTrace (M₁ * J * M₂ᴴ)‖ ≤ K * 1 * K := hnum
      _ = 2 * s * K ^ 2 * (1 / (2 * s)) := by field_simp
      _ ≤ _ := by gcongr
  unfold regularizedObservable
  calc ‖J - (((1 : ℝ) : ℂ) * (NTrace (M₁ * J * M₂ᴴ) / NTrace (M₁ * M₂ᴴ))) •
        (1 : Matrix (Fin N) (Fin N) ℂ)‖
      ≤ ‖J‖ + ‖(((1 : ℝ) : ℂ) * (NTrace (M₁ * J * M₂ᴴ) / NTrace (M₁ * M₂ᴴ))) •
        (1 : Matrix (Fin N) (Fin N) ℂ)‖ := norm_sub_le _ _
    _ ≤ 1 + 2 * s * K ^ 2 := by
      gcongr
      rw [norm_smul, norm_one, mul_one, Complex.ofReal_one, one_mul]
      exact hratio

/-- `cehDensityOf M = Im⟨M⟩ / π`. -/
theorem cehDensityOf_eq (X : Matrix (Fin N) (Fin N) ℂ) :
    cehDensityOf X = (NTrace X).im / Real.pi := by
  rw [cehDensityOf, re_NTrace_matrixImaginaryPart]

/-- **The bound `ρ₁ρ₂ s₂² ≤ C(s, K)`, generic form.** For `N > 0`, `s > 0`, `κ > 0`, matrices `M₁, M₂` with
`‖Mᵢ‖ ≤ K`, `κ ≤ Im⟨Mᵢ⟩`, `s a(Mᵢ) ≤ 1`, any `J` with `‖J‖ ≤ 1`, and `θ(z₁,z₂) = 1`:
`ρ₁ ρ₂ s₂(z₁,z₂;A°)² ≤ (1 + 2sK²)² (K² + K⁴/(2κ²)) / π²`. -/
theorem density_mul_sTwo_sq_le (hN : 0 < N) {s K κ : ℝ} (hs : 0 < s) (hκ : 0 < κ)
    {M₁ M₂ : Matrix (Fin N) (Fin N) ℂ} (hK₁ : ‖M₁‖ ≤ K) (hK₂ : ‖M₂‖ ≤ K)
    (hκ₁ : κ ≤ (NTrace M₁).im) (hκ₂ : κ ≤ (NTrace M₂).im)
    (ha₁ : s * wardMass M₁ ≤ 1) (ha₂ : s * wardMass M₂ ≤ 1)
    (J : Matrix (Fin N) (Fin N) ℂ) (hJ : ‖J‖ ≤ 1)
    (hθ : regularizationCoefficient (Real.sqrt s : ℂ) M₁ M₂ᴴ = 1) :
    cehDensityOf M₁ * cehDensityOf M₂ *
        sTwo 1 (Real.sqrt s : ℂ) M₁ M₂ (regularizedObservable 1 M₁ M₂ᴴ J) ^ 2 ≤
      (1 + 2 * s * K ^ 2) ^ 2 * (K ^ 2 + K ^ 4 / (2 * κ ^ 2)) / Real.pi ^ 2 := by
  set A := regularizedObservable 1 M₁ M₂ᴴ J with hA
  set L := 1 + 2 * s * K ^ 2 with hL
  set t₁ := (NTrace M₁).im with ht₁
  set t₂ := (NTrace M₂).im with ht₂
  have hK : 0 ≤ K := (norm_nonneg _).trans hK₁
  have ht₁p : 0 < t₁ := lt_of_lt_of_le hκ hκ₁
  have ht₂p : 0 < t₂ := lt_of_lt_of_le hκ hκ₂
  have hAL : ‖A‖ ≤ L := norm_regularizedObservable_le hN hs hK₁ hK₂ hJ hθ
  have hL0 : 0 ≤ L := (norm_nonneg _).trans hAL
  have hΓ₁ : ‖gammaMatrix M₁‖ ≤ K / t₁ :=
    (norm_gammaMatrix_le M₁ ht₁p).trans (by gcongr)
  have hΓ₂ : ‖gammaMatrix M₂‖ ≤ K / t₂ :=
    (norm_gammaMatrix_le M₂ ht₂p).trans (by gcongr)
  have hAs : ‖Aᴴ‖ ≤ L := by rw [norm_conjTranspose_eq]; exact hAL
  -- the base term
  have hbase : sTwoBase M₁ M₂ A ≤ (K / t₁) * L * (K / t₂) * L := by
    refine (Complex.re_le_norm _).trans ((norm_NTrace_mul₄_le hN _ _ _ _).trans ?_)
    gcongr
  -- the stable numerator
  have hX : ‖NTrace (M₁ * A * gammaMatrix M₂)‖ ≤ K * L * (K / t₂) :=
    (norm_NTrace_mul₃_le hN _ _ _).trans (by gcongr)
  have hY : ‖NTrace (gammaMatrix M₁ * Aᴴ * M₂)‖ ≤ (K / t₁) * L * K :=
    (norm_NTrace_mul₃_le hN _ _ _).trans (by gcongr)
  have hnum : sTwoNum M₁ M₂ A ≤ (K * L * (K / t₂)) * ((K / t₁) * L * K) := by
    rw [sTwoNum, norm_mul]
    exact mul_le_mul hX hY (norm_nonneg _) (by positivity)
  -- the stable denominator
  have hden : 2 * s * κ ^ 2 ≤ ‖hybridDen s M₁ M₂‖ := by
    have h := half_mul_sq_le_norm_one_sub hN hs.le M₁ M₂ ha₁ ha₂
    have : 2 * κ ≤ t₁ + t₂ := by linarith
    have h4 : (2 * κ) ^ 2 ≤ (t₁ + t₂) ^ 2 := pow_le_pow_left₀ (by linarith) this 2
    have : 2 * s * κ ^ 2 ≤ s * (t₁ + t₂) ^ 2 / 2 := by nlinarith
    exact this.trans h
  have hdenpos : 0 < ‖hybridDen s M₁ M₂‖ := lt_of_lt_of_le (by positivity) hden
  have hstable : s * sTwoNum M₁ M₂ A / ‖hybridDen s M₁ M₂‖ ≤
      s * ((K * L * (K / t₂)) * ((K / t₁) * L * K)) / (2 * s * κ ^ 2) := by
    have hn0 : 0 ≤ sTwoNum M₁ M₂ A := norm_nonneg _
    calc s * sTwoNum M₁ M₂ A / ‖hybridDen s M₁ M₂‖
        ≤ s * ((K * L * (K / t₂)) * ((K / t₁) * L * K)) / ‖hybridDen s M₁ M₂‖ := by
          gcongr
      _ ≤ _ := by gcongr
  have hsq : sTwoSq 1 (Real.sqrt s : ℂ) M₁ M₂ A ≤
      (K / t₁) * L * (K / t₂) * L +
        s * ((K * L * (K / t₂)) * ((K / t₁) * L * K)) / (2 * s * κ ^ 2) := by
    rw [← sTwoSqHybrid_target hs.le, sTwoSqHybrid_eq]
    linarith
  have hρ₁ : cehDensityOf M₁ = t₁ / Real.pi := cehDensityOf_eq M₁
  have hρ₂ : cehDensityOf M₂ = t₂ / Real.pi := cehDensityOf_eq M₂
  have hπ := Real.pi_pos
  have hC : 0 ≤ L ^ 2 * (K ^ 2 + K ^ 4 / (2 * κ ^ 2)) / Real.pi ^ 2 := by positivity
  rw [sTwo, Real.sq_sqrt', hρ₁, hρ₂]
  rcases le_total (sTwoSq 1 (Real.sqrt s : ℂ) M₁ M₂ A) 0 with hneg | hpos
  · rw [max_eq_right hneg, mul_zero]; exact hC
  · rw [max_eq_left hpos]
    have hρ : 0 ≤ t₁ / Real.pi * (t₂ / Real.pi) := by positivity
    calc t₁ / Real.pi * (t₂ / Real.pi) * sTwoSq 1 (Real.sqrt s : ℂ) M₁ M₂ A
        ≤ t₁ / Real.pi * (t₂ / Real.pi) * ((K / t₁) * L * (K / t₂) * L +
            s * ((K * L * (K / t₂)) * ((K / t₁) * L * K)) / (2 * s * κ ^ 2)) :=
          mul_le_mul_of_nonneg_left hsq hρ
      _ = L ^ 2 * (K ^ 2 + K ^ 4 / (2 * κ ^ 2)) / Real.pi ^ 2 := by
          field_simp

/-- **R50b N2, MDE form**: the same bound for MDE solutions `Mᵢ` at
nonreal `zᵢ` (the Ward condition `s a(Mᵢ) ≤ 1` is then automatic).
-/
theorem density_mul_sTwo_sq_le_mde (hN : 0 < N) {s K κ : ℝ} (hs : 0 < s) (hκ : 0 < κ)
    {F₁ F₂ : BlockBand.External.CEH.SourceHermitian N} {z₁ z₂ : ℂ}
    {M₁ M₂ : BlockBand.External.CEH.SourceMatrix N}
    (h₁ : IsManuscriptMDE s F₁ z₁ M₁) (h₂ : IsManuscriptMDE s F₂ z₂ M₂)
    (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0) (hK₁ : ‖M₁‖ ≤ K) (hK₂ : ‖M₂‖ ≤ K)
    (hκ₁ : κ ≤ (NTrace M₁).im) (hκ₂ : κ ≤ (NTrace M₂).im)
    (J : Matrix (Fin N) (Fin N) ℂ) (hJ : ‖J‖ ≤ 1)
    (hθ : regularizationCoefficient (Real.sqrt s : ℂ) M₁ M₂ᴴ = 1) :
    cehDensityOf M₁ * cehDensityOf M₂ *
        sTwo 1 (Real.sqrt s : ℂ) M₁ M₂ (regularizedObservable 1 M₁ M₂ᴴ J) ^ 2 ≤
      (1 + 2 * s * K ^ 2) ^ 2 * (K ^ 2 + K ^ 4 / (2 * κ ^ 2)) / Real.pi ^ 2 :=
  density_mul_sTwo_sq_le hN hs hκ hK₁ hK₂ hκ₁ hκ₂
    (mul_wardMass_mde_lt_one h₁ hz₁ hs.le).le (mul_wardMass_mde_lt_one h₂ hz₂ hs.le).le J hJ hθ

end BlockBand.Native.CEH.ETH
