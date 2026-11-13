module

public import BlockBand.SourceProcess.CompleteSourceGap.AlmostSure
public import BlockBand.SourceProcess.FullSourceCovariance.CovExpand
public import BlockBand.Transmission.PassiveCovariance.ResolventBound

/-!
# The mean of a transported contracting separator, letter by letter

For `0 < b < 1/2`, `-2 < E < 2`, `W ≥ 1`,
Hermitian `𝕏`, `X = nearSchur z 𝕏`, `Γ = gapLetter b E X`, `F = freshTransportedF b E X`,
`f = passiveF b E X`, every `θ : ℂ`:

* `mean_projS_le`: `‖E[NP𝕊₊N*] - θP𝕊‖ ≤ ‖EΓ - θI‖` (integrable `Γ`);
* `mean_projSProj_le`: `‖E[NP𝕊₊PN*] - θP𝕊P‖ ≤ 2η‖EF - θf‖`;
* `transportedSep_sStarProj`, `transportedSep_projSStarProj`, `matrixExpect_conjTranspose`: the
  conjugated letters are the adjoints ("taking adjoints proves both conjugate gaps").
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CompleteSourceGap

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.Transmission.PassiveLayer BlockBand.SourceProcess.FullSource
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

theorem matrixExpect_rect {Ω m n k l : Type*} [MeasurableSpace Ω] [Fintype n] [Fintype k]
    {μ : Measure Ω} (A : Matrix m n ℂ) (F : Ω → Matrix n k ℂ) (B : Matrix k l ℂ)
    (hF : ∀ x y, Integrable (fun ω => F ω x y) μ) :
    matrixExpect μ (fun ω => A * F ω * B) = A * matrixExpect μ F * B := by
  ext i j
  have h1 : ∀ c, Integrable (fun ω => ∑ a, A i a * F ω a c) μ := fun c =>
    integrable_finsetSum _ fun a _ => (hF a c).const_mul _
  simp only [matrixExpect, Matrix.of_apply, Matrix.mul_apply]
  rw [integral_finsetSum _ fun c _ => (h1 c).mul_const _]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [integral_mul_const, integral_finsetSum _ fun a _ => (hF a c).const_mul _]
  simp only [integral_const_mul]

theorem matrixExpect_smul {Ω m n : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (c : ℂ)
    (U : Ω → Matrix m n ℂ) : matrixExpect μ (fun ω => c • U ω) = c • matrixExpect μ U := by
  ext i j; simp [matrixExpect, integral_const_mul]

theorem matrixExpect_conjTranspose {Ω m n : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (U : Ω → Matrix m n ℂ) : matrixExpect μ (fun ω => (U ω)ᴴ) = (matrixExpect μ U)ᴴ := by
  ext i j
  simp only [matrixExpect, Matrix.of_apply, Matrix.conjTranspose_apply]
  exact integral_conj

theorem nearSel_lift_apply (M : Matrix (Fin W) (Fin W) ℂ) (a c : Fin 2 × Fin W) :
    ((nearSel W)ᴴ * M * nearSel W) a c = if a.1 = 0 ∧ c.1 = 0 then M a.2 c.2 else 0 := by
  obtain ⟨i, x⟩ := a; obtain ⟨k, y⟩ := c
  fin_cases i <;> fin_cases k <;>
    simp [Matrix.mul_apply, nearSel, Matrix.conjTranspose_apply]

theorem matrixExpect_lift {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (F : Ω → Matrix (Fin W) (Fin W) ℂ) :
    matrixExpect μ (fun ω => (nearSel W)ᴴ * F ω * nearSel W) =
      (nearSel W)ᴴ * matrixExpect μ F * nearSel W := by
  ext a c
  rw [nearSel_lift_apply]
  simp only [matrixExpect, Matrix.of_apply, nearSel_lift_apply]
  split_ifs <;> simp

theorem norm_nearSel_le : ‖nearSel W‖ ≤ 1 := by
  have := norm_nearSel_mul_le (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
  rw [Matrix.mul_one] at this
  exact this.trans BlockBand.Transmission.PassiveCovariance.norm_one_matrix_le

theorem norm_nearSel_conj_le : ‖(nearSel W)ᴴ‖ ≤ 1 := by
  rw [Matrix.l2_opNorm_conjTranspose]; exact norm_nearSel_le

theorem norm_scat_le (b E : ℝ) {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hXX : XX.IsHermitian) (hη : 0 < etaZ b E) : ‖twoPortScattering b E XX‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (twoPortScattering b E XX)
  rw [(twoPortScattering_unitary b E XX hXX hη).1] at h
  have h1 := BlockBand.Transmission.PassiveCovariance.norm_one_matrix_le
    (n := Fin 2 × Fin W)
  nlinarith [norm_nonneg (twoPortScattering b E XX)]

/-- `ι(·)ι*` and `ι(·)ι*𝕊` do not increase the norm. -/
theorem norm_sandwich_le (M : Matrix (Fin W) (Fin W) ℂ) (T : Matrix (Fin W) (Fin 2 × Fin W) ℂ)
    (hT : ‖T‖ ≤ 1) : ‖(nearSel W)ᴴ * M * T‖ ≤ ‖M‖ := by
  calc ‖(nearSel W)ᴴ * M * T‖ ≤ ‖(nearSel W)ᴴ‖ * ‖M‖ * ‖T‖ :=
        (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right
          (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ 1 * ‖M‖ * 1 := by
        gcongr
        exact norm_nearSel_conj_le
    _ = ‖M‖ := by ring

/-- **`P𝕊`**: `‖E[NP𝕊₊N*] - θP𝕊‖ ≤ ‖EΓ - θI‖`. -/
theorem mean_projS_le {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hW : 1 ≤ W) {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hXX : XX.IsHermitian)
    (hΓ : ∀ x y, Integrable (fun ω => gapLetter b E (nearSchur (boundaryZ b E) XX) ω x y)
      (freshLaw W b)) (θ : ℂ) :
    ‖matrixExpect (freshLaw W b) (transportedSep b E XX .projS) - θ • sepOf b E XX .projS‖ ≤
      ‖matrixExpect (freshLaw W b) (gapLetter b E (nearSchur (boundaryZ b E) XX)) -
        θ • (1 : Matrix (Fin W) (Fin W) ℂ)‖ := by
  have hη := BlockBand.Transmission.PassiveCovariance.etaZ_pos b E (by linarith) hE1 hE2
  rw [FullSourceCovariance.matrixExpect_congr_ae (ae_transportedSep_projS hb0 hb hE1 hE2 hW hXX),
    matrixExpect_rect _ _ _ hΓ]
  have e : θ • sepOf b E XX .projS =
      (nearSel W)ᴴ * (θ • (1 : Matrix (Fin W) (Fin W) ℂ)) * (nearSel W * twoPortScattering b E XX) := by
    rw [sepOf, ← FullSourceCovariance.nearSel_conj_mul_nearSel]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.mul_assoc]
  rw [e, ← Matrix.sub_mul, ← Matrix.mul_sub]
  refine norm_sandwich_le _ _ ((norm_nearSel_mul_le _).trans (norm_scat_le b E hXX hη))

/-- **`P𝕊P`**: `‖E[NP𝕊₊PN*] - θP𝕊P‖ ≤ 2η‖EF - θf‖`. -/
theorem mean_projSProj_le {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hW : 1 ≤ W) {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hXX : XX.IsHermitian) (θ : ℂ) :
    ‖matrixExpect (freshLaw W b) (transportedSep b E XX .projSProj) - θ • sepOf b E XX .projSProj‖ ≤
      2 * etaZ b E * ‖matrixExpect (freshLaw W b) (freshTransportedF b E (nearSchur (boundaryZ b E) XX)) -
        θ • passiveF b E (nearSchur (boundaryZ b E) XX)‖ := by
  have hη := BlockBand.Transmission.PassiveCovariance.etaZ_pos b E (by linarith) hE1 hE2
  set c : ℂ := (2 * Complex.I) * (etaZ b E : ℂ)
  rw [FullSourceCovariance.matrixExpect_congr_ae
    (ae_transportedSep_projSProj hb0 hb hE1 hE2 hW hXX), matrixExpect_smul, matrixExpect_lift]
  have hrow := nearRow_twoPortResolvent b E hXX hη
  have h00 : nearSel W * twoPortScattering b E XX * (nearSel W)ᴴ =
      (-c) • passiveF b E (nearSchur (boundaryZ b E) XX) := by
    have e : ∀ ρ : Matrix (Fin W) (Fin 2 × Fin W) ℂ, ρ * (nearSel W)ᴴ = colBlock ρ 0 := by
      intro ρ; ext x y; simp [colBlock, nearSel, Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [e, colBlock_nearSel_scat, hrow, colBlock_rowOf, colBlock_nearSel]
    simp only [ite_true, passiveF, smul_sub, neg_smul, smul_smul]
    rw [show -c * cZero b E = -1 by rw [neg_mul, cZero_mul b E hη]]
    simp only [neg_smul, one_smul, sub_neg_eq_add]
    abel
  have e : θ • sepOf b E XX .projSProj = (-c) • ((nearSel W)ᴴ *
      (θ • passiveF b E (nearSchur (boundaryZ b E) XX)) * nearSel W) := by
    rw [sepOf, ← FullSourceCovariance.nearSel_conj_mul_nearSel]
    rw [show (nearSel W)ᴴ * nearSel W * twoPortScattering b E XX * ((nearSel W)ᴴ * nearSel W) =
      (nearSel W)ᴴ * (nearSel W * twoPortScattering b E XX * (nearSel W)ᴴ) * nearSel W by
      simp only [Matrix.mul_assoc], h00]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_comm θ]
  rw [e, ← smul_sub, ← Matrix.sub_mul, ← Matrix.mul_sub, norm_smul]
  have hc : ‖-c‖ = 2 * etaZ b E := by
    simp [c, Complex.norm_real, abs_of_pos hη]
  rw [hc]
  gcongr
  exact norm_sandwich_le _ _ norm_nearSel_le

theorem transportedSep_sStarProj (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    transportedSep b E XX .sStarProj ω = (transportedSep b E XX .projS ω)ᴴ := by
  have hP : (nearProjection W)ᴴ = nearProjection W := by
    rw [← FullSourceCovariance.nearSel_conj_mul_nearSel, conjTranspose_mul,
      conjTranspose_conjTranspose]
  simp only [transportedSep, sepOf, conjTranspose_mul, conjTranspose_conjTranspose, hP,
    Matrix.mul_assoc]

theorem transportedSep_projSStarProj (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    transportedSep b E XX .projSStarProj ω = (transportedSep b E XX .projSProj ω)ᴴ := by
  have hP : (nearProjection W)ᴴ = nearProjection W := by
    rw [← FullSourceCovariance.nearSel_conj_mul_nearSel, conjTranspose_mul,
      conjTranspose_conjTranspose]
  simp only [transportedSep, sepOf, conjTranspose_mul, conjTranspose_conjTranspose, hP,
    Matrix.mul_assoc]

theorem sepOf_sStarProj (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    sepOf b E XX .sStarProj = (sepOf b E XX .projS)ᴴ := by
  have hP : (nearProjection W)ᴴ = nearProjection W := by
    rw [← FullSourceCovariance.nearSel_conj_mul_nearSel, conjTranspose_mul,
      conjTranspose_conjTranspose]
  simp only [sepOf, conjTranspose_mul, hP]

theorem sepOf_projSStarProj (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    sepOf b E XX .projSStarProj = (sepOf b E XX .projSProj)ᴴ := by
  have hP : (nearProjection W)ᴴ = nearProjection W := by
    rw [← FullSourceCovariance.nearSel_conj_mul_nearSel, conjTranspose_mul,
      conjTranspose_conjTranspose]
  simp only [sepOf, conjTranspose_mul, hP, Matrix.mul_assoc]

/-- The adjoint of a separator mean error has the same norm. -/
theorem norm_conj_err (M S : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (θ : ℂ) :
    ‖Mᴴ - star θ • Sᴴ‖ = ‖M - θ • S‖ := by
  rw [← Matrix.l2_opNorm_conjTranspose (M - θ • S), conjTranspose_sub, conjTranspose_smul]

end BlockBand.SourceProcess.CompleteSourceGap
