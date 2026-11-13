module

public import BlockBand.SourceProcess.FullSourceCovariance.ProjBlock
public import BlockBand.SourceProcess.FullSourceCovariance.CrossedOpp

/-!
# `PhiOppMean` holds: `W·EΦ'(x,x') = σ₊·x*x' + O(δ₀ + δ₁ + g/W + W⁻¹)`

Law `freshLaw W b`, strictly passive `X`,
`E ∈ bulkInterval κ`, near the jet (`δ₀ ≤ d₀`); constants uniform in `W ≥ W₀`, `E`, `X`, `x, x'`.

* `sTilde_eq`: `S̃ = c·P₁ + b·P₂` (`W ≠ 0`, `c = 1 - 2b`);
* `phiOpp_split`: `W·Φ'(x,x') = (ι₁x)*(c·K̂𝒢P₁(K̂𝒢)ᴴ + b·K̂𝒢P₂(K̂𝒢)ᴴ)(ι₁x')` pointwise;
* `sigmaPlus_eq_yStar`: `c·y*₀ + b·y*₁ = c/b + b = σ₊`;
* `epsOf_le_jetDist`: `epsOf ≤ max 1 η_L⁻¹·(jetDist + W⁻¹)` on the bulk (`g = 4ηq`);
* **`phiOppMean_holds hGA hLp : PhiOppMean`**. By `projBlock_mean_bulk`,
  `E[K̂𝒢P_p(K̂𝒢)ᴴ]₀₀ = y_p·KM(KM)ᴴ + O(W⁻²)`; `KM = 1 + O(epsOf)` (`matchedBasic_bulk`) and
  `y_p = y*_p + O(epsOf)` (`yP_matched_bulk`). Only the Gaussian inputs are used
  (`passiveBounds_holds hGA hLp`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceCovariance

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- The weighted block word `K̂𝒢P_p(K̂𝒢)ᴴ`. -/
def projWord (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) (p : Fin 2)
    (ω : LayerSample W .oneBlockOnePort) : LayerMat W :=
  kHat b E X * (gRes b E X ω * (bProj p * (kHat b E X * gRes b E X ω)ᴴ))

/-- `S̃ = c·P₁ + b·P₂`. -/
theorem sTilde_eq {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hW : W ≠ 0) :
    sTilde W b = ((1 - 2 * b : ℝ) : ℂ) • bProj 0 + (b : ℂ) • bProj 1 := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero hW
  have hW' : (W : ℂ) ≠ 0 := by exact_mod_cast hW
  rw [sTilde, bProj, bProj, ← diagonal_smul, ← diagonal_smul, diagonal_add]
  congr 1
  funext γ
  have hg' : max ((1 - 2 * b) / (W : ℝ)) 0 = (1 - 2 * b) / W :=
    max_eq_left (div_nonneg (by linarith) hWr.le)
  have hn' : max (b / (W : ℝ)) 0 = b / W := max_eq_left (div_nonneg hb0.le hWr.le)
  rcases γ with γ | γ <;> simp [physVar, bInd, blkOf, hg', hn'] <;> field_simp

theorem phiOpp_split {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (E : ℝ)
    (X : Matrix (Fin W) (Fin W) ℂ) (hW : W ≠ 0) (x x' : Fin W → ℂ)
    (ω : LayerSample W .oneBlockOnePort) :
    (W : ℂ) * phiOpp b E X x x' ω = star (physVec x) ⬝ᵥ
      ((((1 - 2 * b : ℝ) : ℂ) • projWord b E X 0 ω + (b : ℂ) • projWord b E X 1 ω) *ᵥ
        physVec x') := by
  have hW' : (W : ℂ) ≠ 0 := by exact_mod_cast hW
  rw [phiOpp_eq_wordForm b E X hW x x' ω, ← mul_assoc, mul_inv_cancel₀ hW', one_mul, wordForm]
  congr 2
  set M := kHat b E X * gRes b E X ω
  have hv : wordVal (kHat b E X) (gRes b E X ω) wdOpp (dOpp W b) = M * sTilde W b * Mᴴ := by
    simp [wordVal, List.ofFn_succ, wLetter, wdOpp, dOpp, M, Matrix.mul_assoc]
  rw [hv, sTilde_eq hb0 hb hW]
  simp only [projWord, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, M,
    Matrix.mul_assoc]

theorem sigmaPlus_eq_yStar {b : ℝ} (hb0 : 0 < b) :
    ((1 - 2 * b : ℝ) : ℂ) * yStar b 0 + (b : ℂ) * yStar b 1 = ((sigmaPlus b : ℝ) : ℂ) := by
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb0.ne'
  simp [yStar, ind, sigmaPlus, kPlus]
  field_simp

/-- `epsOf ≤ max 1 η_L⁻¹·(jetDist + W⁻¹)` on the bulk. -/
theorem epsOf_le_jetDist {b κ E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ)
    (hE : E ∈ bulkInterval κ) (s : ℂ) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef) (hW : 1 ≤ W) :
    SourceMixing.epsOf b E s X ≤
      max 1 (PathScalar.etaLow b κ)⁻¹ * (jetDist b E s X + (W : ℝ)⁻¹) := by
  obtain ⟨h1, h2⟩ := PathScalar.bulk_bounds hκ hE
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hgq : conductanceOf (passiveTransmission b E X) = 4 * etaZ b E * passiveMass b E X := by
    simp [conductanceOf, passiveTransmission, passiveMass, Matrix.trace_smul]
  have hq := passiveMass_nonneg b E hY
  have hδ0 : 0 ≤ jetDistance0 b E X := norm_nonneg _
  have hδ1 : 0 ≤ jetDistance1 b E s X := norm_nonneg _
  have hi := CovarianceBulk.inv_etaZ_le_bulk hb hκ hE
  set m := max 1 (PathScalar.etaLow b κ)⁻¹
  have hm1 : 1 ≤ m := le_max_left _ _
  have hmη : (etaZ b E)⁻¹ ≤ m := hi.trans (le_max_right _ _)
  -- `q/W ≤ m·g/W`
  have hqW : passiveMass b E X / W ≤ m * (conductanceOf (passiveTransmission b E X) / W) := by
    rw [hgq, ← mul_div_assoc]
    refine div_le_div_of_nonneg_right ?_ hW0.le
    have e : passiveMass b E X = (etaZ b E)⁻¹ * (etaZ b E * passiveMass b E X) := by
      field_simp
    calc passiveMass b E X = (etaZ b E)⁻¹ * (etaZ b E * passiveMass b E X) := e
      _ ≤ m * (etaZ b E * passiveMass b E X) := by gcongr
      _ ≤ m * (4 * etaZ b E * passiveMass b E X) := by
          gcongr; nlinarith [mul_nonneg hη.le hq]
  have hW2 : (W : ℝ)⁻¹ ^ 2 ≤ (W : ℝ)⁻¹ := by
    have : (W : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hWr
    nlinarith [inv_nonneg.mpr hW0.le]
  unfold SourceMixing.epsOf jetDist
  have hWi : 0 ≤ (W : ℝ)⁻¹ := inv_nonneg.mpr hW0.le
  nlinarith [mul_le_mul_of_nonneg_left hm1 hδ0, mul_le_mul_of_nonneg_left hm1 hδ1,
    mul_le_mul_of_nonneg_left hm1 hWi]

theorem bilinear_sub_smul_one (x x' : Fin W → ℂ) (M : Matrix (Fin W) (Fin W) ℂ) (σ : ℂ) :
    bilinear x M x' - σ * bilinear x 1 x' = bilinear x (M - σ • 1) x' := by
  simp only [bilinear, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul,
    smul_eq_mul]

theorem mean_split_aux (c b' σ y0 y1 u0 u1 : ℂ) (B0 B1 KK : Matrix (Fin W) (Fin W) ℂ)
    (hσ : c * u0 + b' * u1 = σ) :
    c • B0 + b' • B1 - σ • (1 : Matrix (Fin W) (Fin W) ℂ) =
      c • (B0 - y0 • KK) + b' • (B1 - y1 • KK) + (c * y0 + b' * y1) • (KK - 1) +
        (c * (y0 - u0) + b' * (y1 - u1)) • (1 : Matrix (Fin W) (Fin W) ℂ) := by
  subst hσ
  module

/-- **`PhiOppMean` holds** (Gaussian inputs only). -/
theorem phiOppMean_holds (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) :
    PhiOppMean := by
  intro b hb0 hb κ hκ
  have hA := passiveBounds_holds hGA hLp
  obtain ⟨Cp, Wp, hCp, hpb⟩ := projBlock_mean_bulk hA hb0 hb hκ
  obtain ⟨d₁, Cy, Wy, hd₁, hCy, hyb⟩ := yP_matched_bulk hA hb0 hb hκ
  obtain ⟨d₂, Cb, Wb, hd₂, hCb, hmb⟩ := CovarianceBulk.matchedBasic_bulk hA hb0 hb hκ
  set m := max 1 (PathScalar.etaLow b κ)⁻¹
  set K := 2 * Cp + 2 * Cp * (Cb * (Cp + 1)) + 2 * Cy
  refine ⟨min d₁ d₂, lt_min hd₁ hd₂, K * m, max (max Wp Wy) (max Wb 1),
    fun W hW E hE s hs X hY hd x x' => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWp, hWy⟩, hWb, hW1⟩ := hW
  obtain ⟨h1, h2⟩ := PathScalar.bulk_bounds hκ hE
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hW0 : W ≠ 0 := by omega
  have hWr : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero hW0
  have hg := conductance_nonneg b E hη.le hY.posSemidef
  have hJ : jetDistance0 b E X ≤ jetDist b E s X := by
    unfold jetDist; have := div_nonneg hg hWr.le
    have : 0 ≤ jetDistance1 b E s X := norm_nonneg _
    linarith
  have hd0₁ : jetDistance0 b E X ≤ d₁ := hJ.trans (hd.trans (min_le_left _ _))
  have hd0₂ : jetDistance0 b E X ≤ d₂ := hJ.trans (hd.trans (min_le_right _ _))
  set μ := freshLaw W b
  set c : ℂ := ((1 - 2 * b : ℝ) : ℂ)
  -- the mean as a bilinear form
  have hi0 := (hpb W hWp E hE X hY 0).1
  have hi1 := (hpb W hWp E hE X hY 1).1
  set F := fun ω => c • projWord b E X 0 ω + (b : ℂ) • projWord b E X 1 ω
  have hiF : ∀ α β, Integrable (fun ω => F ω α β) μ := fun α β =>
    ((hi0 α β).const_mul c).add ((hi1 α β).const_mul (b : ℂ))
  have hmean : (W : ℂ) * ∫ ω, phiOpp b E X x x' ω ∂μ =
      bilinear x (c • blkAt (matrixExpect μ (projWord b E X 0)) 0 0 +
        (b : ℂ) • blkAt (matrixExpect μ (projWord b E X 1)) 0 0) x' := by
    rw [← integral_const_mul]
    have e : (fun ω => (W : ℂ) * phiOpp b E X x x' ω) =
        fun ω => star (physVec x) ⬝ᵥ (F ω *ᵥ physVec x') :=
      funext fun ω => phiOpp_split hb0 hb E X hW0 x x' ω
    rw [e, integral_form F hiF]
    congr 1
    have hE' : matrixExpect μ F = c • matrixExpect μ (projWord b E X 0) +
        (b : ℂ) • matrixExpect μ (projWord b E X 1) := by
      ext α β
      simp only [matrixExpect, F, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply,
        smul_eq_mul]
      have i0 : Integrable (fun ω => c * projWord b E X 0 ω α β) μ := (hi0 α β).const_mul c
      have i1 : Integrable (fun ω => (b : ℂ) * projWord b E X 1 ω α β) μ :=
        (hi1 α β).const_mul (b : ℂ)
      rw [integral_add i0 i1, integral_const_mul, integral_const_mul]
    rw [hE', blkAt_add, SourceMixing.blkAt_smul, SourceMixing.blkAt_smul]
  rw [hmean, bilinear_sub_smul_one]
  -- the matrix error
  obtain ⟨-, hKM, hy0, hB0⟩ := hpb W hWp E hE X hY 0
  obtain ⟨-, -, hy1, hB1⟩ := hpb W hWp E hE X hY 1
  obtain ⟨-, -, -, hKM1, -⟩ := hmb W hWb E hE s X hY hd0₂
  have hY0 := hyb W hWy E hE s X hY hd0₁ 0
  have hY1 := hyb W hWy E hE s X hY hd0₁ 1
  set e := SourceMixing.epsOf b E s X
  obtain ⟨-, -, -, hεw, -⟩ := SourceMixing.epsOf_ge (b := b) (E := E) s hY.posSemidef
  have he : 0 ≤ e := by have := sq_nonneg ((W : ℝ)⁻¹); have : 0 ≤ jetDistance0 b E X := norm_nonneg _
                        linarith
  have hW2e : 1 / (W : ℝ) ^ 2 ≤ e := by
    have : 0 ≤ jetDistance0 b E X := norm_nonneg _
    rw [one_div, ← inv_pow]; linarith
  set KM := SourceMixing.kmOf b E X
  set B0 := blkAt (matrixExpect μ (projWord b E X 0)) 0 0
  set B1 := blkAt (matrixExpect μ (projWord b E X 1)) 0 0
  set y0 := yP b E X 0
  set y1 := yP b E X 1
  have hsplit := mean_split_aux c (b : ℂ) ((sigmaPlus b : ℝ) : ℂ) y0 y1 (yStar b 0) (yStar b 1)
    B0 B1 (KM * KMᴴ) (sigmaPlus_eq_yStar hb0)
  have hc : ‖c‖ ≤ 1 := by
    simp only [c]; rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]; linarith
  have hbn : ‖(b : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]; linarith
  have hKK : ‖KM * KMᴴ - 1‖ ≤ Cb * (Cp + 1) * e := by
    have e1 : KM * KMᴴ - 1 = (KM - 1) * KMᴴ + (KM - 1)ᴴ := by
      rw [Matrix.sub_mul, Matrix.one_mul, conjTranspose_sub, conjTranspose_one]; abel
    rw [e1]
    refine (norm_add_le _ _).trans ?_
    rw [Matrix.l2_opNorm_conjTranspose]
    have hm : ‖(KM - 1) * KMᴴ‖ ≤ ‖KM - 1‖ * ‖KM‖ := by
      have := Matrix.l2_opNorm_mul (KM - 1) KMᴴ
      rwa [Matrix.l2_opNorm_conjTranspose] at this
    calc ‖(KM - 1) * KMᴴ‖ + ‖KM - 1‖ ≤ ‖KM - 1‖ * ‖KM‖ + ‖KM - 1‖ := by linarith
      _ = ‖KM - 1‖ * (‖KM‖ + 1) := by ring
      _ ≤ (Cb * e) * (Cp + 1) := by gcongr
      _ = _ := by ring
  have h1n : ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ 1 := norm_one_matrix_le
  have hM : ‖c • B0 + (b : ℂ) • B1 - ((sigmaPlus b : ℝ) : ℂ) • 1‖ ≤ K * e := by
    rw [hsplit]
    have t1 : ‖c • (B0 - y0 • (KM * KMᴴ))‖ ≤ Cp * e :=
      (norm_smul_le _ _).trans (by
        calc ‖c‖ * ‖B0 - y0 • (KM * KMᴴ)‖ ≤ 1 * (Cp / (W : ℝ) ^ 2) := by gcongr; exact hB0
          _ = Cp * (1 / (W : ℝ) ^ 2) := by ring
          _ ≤ Cp * e := by gcongr)
    have t2 : ‖(b : ℂ) • (B1 - y1 • (KM * KMᴴ))‖ ≤ Cp * e :=
      (norm_smul_le _ _).trans (by
        calc ‖(b : ℂ)‖ * ‖B1 - y1 • (KM * KMᴴ)‖ ≤ 1 * (Cp / (W : ℝ) ^ 2) := by gcongr; exact hB1
          _ = Cp * (1 / (W : ℝ) ^ 2) := by ring
          _ ≤ Cp * e := by gcongr)
    have hcy : ‖c * y0 + (b : ℂ) * y1‖ ≤ 2 * Cp := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      nlinarith [norm_nonneg y0, norm_nonneg y1, norm_nonneg c, norm_nonneg (b : ℂ)]
    have t3 : ‖(c * y0 + (b : ℂ) * y1) • (KM * KMᴴ - 1)‖ ≤ 2 * Cp * (Cb * (Cp + 1) * e) :=
      (norm_smul_le _ _).trans (mul_le_mul hcy hKK (norm_nonneg _) (by positivity))
    have hcd : ‖c * (y0 - yStar b 0) + (b : ℂ) * (y1 - yStar b 1)‖ ≤ 2 * (Cy * e) := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
      have := norm_nonneg (y0 - yStar b 0); have := norm_nonneg (y1 - yStar b 1)
      nlinarith [norm_nonneg c, norm_nonneg (b : ℂ)]
    have t4 : ‖(c * (y0 - yStar b 0) + (b : ℂ) * (y1 - yStar b 1)) •
        (1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ 2 * (Cy * e) :=
      (norm_smul_le _ _).trans (by
        calc _ ≤ 2 * (Cy * e) * 1 := mul_le_mul hcd h1n (norm_nonneg _) (by positivity)
          _ = _ := by ring)
    calc _ ≤ ‖c • (B0 - y0 • (KM * KMᴴ))‖ + ‖(b : ℂ) • (B1 - y1 • (KM * KMᴴ))‖ +
          ‖(c * y0 + (b : ℂ) * y1) • (KM * KMᴴ - 1)‖ +
          ‖(c * (y0 - yStar b 0) + (b : ℂ) * (y1 - yStar b 1)) •
            (1 : Matrix (Fin W) (Fin W) ℂ)‖ := norm_add₄_le
      _ ≤ Cp * e + Cp * e + 2 * Cp * (Cb * (Cp + 1) * e) + 2 * (Cy * e) := by gcongr
      _ = K * e := by simp only [K]; ring
  have hem := epsOf_le_jetDist hb0 hb hκ hE s hY.posSemidef hW1
  have hK0 : 0 ≤ K := by positivity
  have nx := PassiveCovariance.vecNorm_nonneg x
  have nx' := PassiveCovariance.vecNorm_nonneg x'
  refine (PassiveCovariance.norm_bilinear_le _ _ _).trans ?_
  calc vecNorm x * ‖c • B0 + (b : ℂ) • B1 - ((sigmaPlus b : ℝ) : ℂ) • 1‖ * vecNorm x' ≤
      vecNorm x * (K * (m * (jetDist b E s X + (W : ℝ)⁻¹))) * vecNorm x' := by
        gcongr; exact hM.trans (mul_le_mul_of_nonneg_left hem hK0)
    _ = _ := by ring

end BlockBand.SourceProcess.FullSourceCovariance
