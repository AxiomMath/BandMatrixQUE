module

public import BlockBand.Transmission.PassiveCovariance.ZSys

/-!
# The `z_p` trace system, scalar form

**Hypothesis:** `PassiveBoundsStatement`. Law `layerLaw W b .oneBlockOnePort`, strictly passive
`X`, fixed `b ∈ (0, 1/2)`, `E ∈ (-2, 2)`; constants depend on `b, E` only, uniformly in `W ≥ W₀`,
`X`, `p`.

With `C_q = ⟨MMᴴMMᴴ⟩`, `I_z = s₁(s₁rB_pC_q + conj S_p·conj B) + S_ps₁B`:
* `conj_bOf`: `conj⟨M²Mᴴ⟩ = ⟨MMᴴMᴴ⟩`.
* **`zP_system`**: `|σz_p| ≤ C` and
  `σz_p(1 - k_hA) = k_hI_z + bv(1 + bt₁)conj v^p₁ + b²vv^p₀t₂ + O(W⁻²)`, from the trace equations
  `z^p₀ = I_z + σz_pA`, `z^p₁ = v((1 + bt₁)conj v^p₁ + bv^p₀t₂ + bz^p₀v̄)` (both `+ O(W⁻²)`;
  `⟨X''₁₁⟩ = conj v^p₁` exactly by `trMean_rv`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveCovariance

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

theorem conj_bOf (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    conj (SourceMixing.bOf b E X) = (W : ℂ)⁻¹ * (SourceMixing.mOf b E X *
      ((SourceMixing.mOf b E X)ᴴ * (SourceMixing.mOf b E X)ᴴ)).trace := by
  unfold SourceMixing.bOf
  rw [map_mul, map_inv₀, Complex.conj_natCast, ← Complex.star_def, ← trace_conjTranspose]
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]

/-- `C_q = ⟨MMᴴMMᴴ⟩`. -/
abbrev cqOf (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : ℂ :=
  (W : ℂ)⁻¹ * (SourceMixing.mOf b E X * ((SourceMixing.mOf b E X)ᴴ *
    (SourceMixing.mOf b E X * (SourceMixing.mOf b E X)ᴴ))).trace

/-- The trace of the leading physical block of the `z_p` system (pure algebra). -/
theorem z0_trace (M : Matrix (Fin W) (Fin W) ℂ) (s₁ S σ r cS : ℂ) :
    (W : ℂ)⁻¹ * (M * (s₁ • (Mᴴ * (r • (s₁ • (M * Mᴴ)) + cS • Mᴴ)) + S • (s₁ • (M * Mᴴ)) +
      σ • Mᴴ)).trace = s₁ * (s₁ * r * ((W : ℂ)⁻¹ * (M * (Mᴴ * (M * Mᴴ))).trace) +
        cS * ((W : ℂ)⁻¹ * (M * (Mᴴ * Mᴴ)).trace)) + S * s₁ * ((W : ℂ)⁻¹ * (M * (M * Mᴴ)).trace) +
      σ * ((W : ℂ)⁻¹ * (M * Mᴴ).trace) := by
  simp only [Matrix.mul_add, Matrix.mul_smul, trace_add, trace_smul, smul_eq_mul]
  ring

/-- The error of the leading physical block of the `z_p` system (pure algebra). -/
theorem z0_mat_bound {M X0 T0 G0h : Matrix (Fin W) (Fin W) ℂ} {s₁ S σ r cS : ℂ}
    {CD Cf Cg Cr C1 Cv Cz w : ℝ} (hM : ‖M‖ ≤ CD) (hs : ‖s₁‖ ≤ Cf) (hr : ‖r‖ ≤ Cr) (hS : ‖S‖ ≤ Cv)
    (hcS : ‖cS‖ ≤ Cv) (hσ : ‖σ‖ ≤ Cz) (hX0 : ‖X0 - Mᴴ * (r • T0 + cS • G0h)‖ ≤ Cg / w)
    (hT : ‖T0 - s₁ • (M * Mᴴ)‖ ≤ C1 / w) (hG : ‖G0h - Mᴴ‖ ≤ CD / w) (hCD : 0 ≤ CD) (hCf : 0 ≤ Cf)
    (hCr : 0 ≤ Cr) (hCv : 0 ≤ Cv) (hCz : 0 ≤ Cz) :
    ‖M * (s₁ • X0 + S • T0 + σ • G0h) -
        M * (s₁ • (Mᴴ * (r • (s₁ • (M * Mᴴ)) + cS • Mᴴ)) + S • (s₁ • (M * Mᴴ)) + σ • Mᴴ)‖ ≤
      CD * (Cf * Cg + Cf * (CD * (Cr * C1 + Cv * CD)) + Cv * C1 + Cz * CD) / w := by
  have e : M * (s₁ • X0 + S • T0 + σ • G0h) -
      M * (s₁ • (Mᴴ * (r • (s₁ • (M * Mᴴ)) + cS • Mᴴ)) + S • (s₁ • (M * Mᴴ)) + σ • Mᴴ) =
      M * (s₁ • (X0 - Mᴴ * (r • T0 + cS • G0h)) + s₁ • (Mᴴ * (r • (T0 - s₁ • (M * Mᴴ)) +
        cS • (G0h - Mᴴ))) + S • (T0 - s₁ • (M * Mᴴ)) + σ • (G0h - Mᴴ)) := by
    simp only [Matrix.mul_sub, smul_sub, Matrix.mul_add, Matrix.mul_smul, smul_add]; abel
  have hMh : ‖Mᴴ‖ ≤ CD := by rw [Matrix.l2_opNorm_conjTranspose]; exact hM
  have hCg : 0 ≤ Cg / w := (norm_nonneg _).trans hX0
  have hC1 : 0 ≤ C1 / w := (norm_nonneg _).trans hT
  have hCDw : 0 ≤ CD / w := (norm_nonneg _).trans hG
  rw [e]
  refine (Matrix.l2_opNorm_mul _ _).trans ?_
  have t1 : ‖s₁ • (X0 - Mᴴ * (r • T0 + cS • G0h))‖ ≤ Cf * (Cg / w) :=
    (norm_smul_le _ _).trans (mul_le_mul hs hX0 (norm_nonneg _) hCf)
  have t2a : ‖r • (T0 - s₁ • (M * Mᴴ)) + cS • (G0h - Mᴴ)‖ ≤ Cr * (C1 / w) + Cv * (CD / w) :=
    (norm_add_le _ _).trans (add_le_add
      ((norm_smul_le _ _).trans (mul_le_mul hr hT (norm_nonneg _) hCr))
      ((norm_smul_le _ _).trans (mul_le_mul hcS hG (norm_nonneg _) hCv)))
  have t2 : ‖s₁ • (Mᴴ * (r • (T0 - s₁ • (M * Mᴴ)) + cS • (G0h - Mᴴ)))‖ ≤
      Cf * (CD * (Cr * (C1 / w) + Cv * (CD / w))) :=
    (norm_smul_le _ _).trans (mul_le_mul hs ((Matrix.l2_opNorm_mul _ _).trans
      (mul_le_mul hMh t2a (norm_nonneg _) hCD)) (by positivity) hCf)
  have t3 : ‖S • (T0 - s₁ • (M * Mᴴ))‖ ≤ Cv * (C1 / w) :=
    (norm_smul_le _ _).trans (mul_le_mul hS hT (norm_nonneg _) hCv)
  have t4 : ‖σ • (G0h - Mᴴ)‖ ≤ Cz * (CD / w) :=
    (norm_smul_le _ _).trans (mul_le_mul hσ hG (norm_nonneg _) hCz)
  refine (mul_le_mul hM ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add ((norm_add_le _ _).trans (add_le_add t1 t2)) t3)) t4)) (by positivity) hCD).trans
    (le_of_eq ?_)
  ring

/-- The physical trace equation of the `z_p` system. -/
theorem zP_trace0 (hA : PassiveLayer.PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ p : Fin 2,
        ‖szP b E X p‖ ≤ C ∧ (∀ r, ‖zP b E X p r‖ ≤ C) ∧
        ‖zP b E X p 0 - ((SourceMixing.sOne b E X * (SourceMixing.sOne b E X * rB b E X p * cqOf b E X +
          conj (svP b E X p) * conj (SourceMixing.bOf b E X)) +
          svP b E X p * SourceMixing.sOne b E X * SourceMixing.bOf b E X) + szP b E X p * SourceMixing.aOf b E X)‖ ≤ C / (W : ℝ) ^ 2 := by
  obtain ⟨Cz, Wz, hCz, hZb⟩ := zP_blocks hA hb0 hb h1 h2
  obtain ⟨Cg, Wg, hCg, hGs⟩ := gsT_block hA hb0 hb h1 h2
  obtain ⟨C1, W1, hC1, hS1⟩ := SourceMixing.scalarS1_blocks hA hb0 hb h1 h2
  obtain ⟨CD, WD, hCD, hD⟩ := SourceMixing.dressedBlocks hA hb0 hb h1 h2
  obtain ⟨Cf, Wf, hCf, hF⟩ := SourceMixing.freshU_mean hA hb0 hb h1 h2
  obtain ⟨Cv, Wv, hCv, hVs⟩ := vP_system hA hb0 hb h1 h2
  obtain ⟨Cq, Wq, hCq, hQb⟩ := tP_blocks hA hb0 hb h1 h2
  set Cr := 1 + Cq
  set C₁ := Cz + CD * (Cf * Cg + Cf * (CD * (Cr * C1 + Cv * CD)) + Cv * C1 + Cz * CD) +
    CD * (b * Cz * CD)
  set K := (1 - 2 * b) + b + b ^ 2 * (CD * CD)
  have hK : 0 ≤ K := by have : 0 ≤ 1 - 2 * b := by linarith
                        positivity
  refine ⟨C₁, max (max (max Wz Wg) (max W1 WD)) (max (max Wf Wv) Wq),
    by positivity, fun W hW X hX p => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hWz, hWg⟩, hW1', hWD⟩, ⟨hWf, hWv⟩, hWq⟩ := hW
  obtain ⟨hzb, hentZ, hZ0, hZ1⟩ := hZb W hWz X hX p
  obtain ⟨hentX, hX0⟩ := hGs W hWg X hX p
  obtain ⟨hT00, -⟩ := hS1 W hW1' X hX
  obtain ⟨hW1r, -, hM, hv, -, -, hE0, hE1, -, -, -⟩ := hD W hWD X hX
  obtain ⟨-, hs, -⟩ := hF W hWf X hX
  obtain ⟨hS, -⟩ := hVs W hWv X hX p
  obtain ⟨ht, -, -, -⟩ := hQb W hWq X hX 0
  obtain ⟨ht1, -, hentT, -⟩ := hQb W hWq X hX 1
  rw [bProj_one] at hentT
  set μ := layerLaw W b .oneBlockOnePort
  set M := SourceMixing.mOf b E X
  set v := SourceMixing.vOf b E X
  set s₁ := SourceMixing.sOne b E X
  set S := svP b E X p
  set σ := szP b E X p
  set r := rB b E X p
  set G0 := blkAt (matrixExpect μ (gRes b E X)) 0 0
  set G1 := blkAt (matrixExpect μ (gRes b E X)) 1 1
  set T0 := blkAt (tMean b E X) 0 0
  set T1 := blkAt (tMean b E X) 1 1
  set X0 := blkAt (gsTMean b E X p) 0 0
  set X1 := blkAt (gsTMean b E X p) 1 1
  set c := 1 + (b : ℂ) * SourceMixing.tTwo b E X 0
  have nb : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
  have hσ : ‖σ‖ ≤ Cz := norm_sig1_le hb0 hb (hzb 0) (hzb 1)
  have hr : ‖r‖ ≤ Cr := (norm_add_le _ _).trans (add_le_add (norm_ind_le 0 p)
    (norm_sig1_le hb0 hb (ht p) (ht1 p)))
  have hW2' : (0 : ℝ) < (W : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ W := by exact_mod_cast hW1r
    positivity
  have hzt : ∀ r', zP b E X p r' = SourceMixing.blkTr (matrixExpect μ (fun ω => gRes b E X ω *
      (portProj * ((gRes b E X ω)ᴴ * (bProj p * (gRes b E X ω *
        (portProj * (gRes b E X ω)ᴴ))))))) r' := fun r' =>
    SourceMixing.integral_blkTr _ hentZ r'
  have hC₁ : 0 ≤ C₁ := by positivity
  -- the physical trace
  have hZ := z0_trace M s₁ S σ r (conj S)
  rw [← cqOf, ← SourceMixing.aOf, ← conj_bOf] at hZ
  change _ = s₁ * (s₁ * r * cqOf b E X + conj S * conj (SourceMixing.bOf b E X)) +
    S * s₁ * SourceMixing.bOf b E X + σ * SourceMixing.aOf b E X at hZ
  have hMh : ‖Mᴴ‖ ≤ CD := by rw [Matrix.l2_opNorm_conjTranspose]; exact hM
  have hG0h : ‖G0ᴴ - Mᴴ‖ ≤ CD / (W : ℝ) ^ 2 := by
    rw [SourceMixing.norm_conjTranspose_sub]; exact hE0
  have hcS : ‖conj S‖ ≤ Cv := by rw [Complex.norm_conj]; exact hS
  have hb2 := z0_mat_bound hM hs hr hS hcS hσ hX0 hT00 hG0h hCD hCf (by positivity) hCv hCz
  have d0 : ‖zP b E X p 0 - (s₁ * (s₁ * r * cqOf b E X + conj S * conj (SourceMixing.bOf b E X)) +
      S * s₁ * SourceMixing.bOf b E X + σ * SourceMixing.aOf b E X)‖ ≤ C₁ / (W : ℝ) ^ 2 := by
    rw [← hZ, hzt]
    refine (SourceMixing.norm_blkTr_sub_le _ 0 _).trans ?_
    refine (norm_sub_le_norm_sub_add_norm_sub _ (M * (s₁ • X0 + S • T0 + σ • G0ᴴ)) _).trans ?_
    refine (add_le_add hZ0 hb2).trans ?_
    rw [← add_div]; refine div_le_div_of_nonneg_right ?_ hW2'.le
    have : 0 ≤ CD * (b * Cz * CD) := by positivity
    simp only [C₁]; linarith
  exact ⟨hσ.trans (by simp only [C₁]; linarith [show 0 ≤ CD * (Cf * Cg + Cf * (CD * (Cr * C1 + Cv * CD)) +
    Cv * C1 + Cz * CD) + CD * (b * Cz * CD) by positivity]),
    fun r' => (hzb r').trans (by simp only [C₁]; linarith [show 0 ≤ CD * (Cf * Cg + Cf * (CD * (Cr * C1 +
      Cv * CD)) + Cv * C1 + Cz * CD) + CD * (b * Cz * CD) by positivity]), d0⟩

/-- The port trace equation of the `z_p` system. -/
theorem zP_trace1 (hA : PassiveLayer.PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ p : Fin 2,
        ‖zP b E X p 1 - SourceMixing.vOf b E X * ((1 + (b : ℂ) * SourceMixing.tTwo b E X 0) *
          conj (vP b E X p 1) + (b : ℂ) * vP b E X p 0 * SourceMixing.tTwo b E X 1 +
          (b : ℂ) * zP b E X p 0 * conj (SourceMixing.vOf b E X))‖ ≤ C / (W : ℝ) ^ 2 := by
  obtain ⟨Cz, Wz, hCz, hZb⟩ := zP_blocks hA hb0 hb h1 h2
  obtain ⟨Cg, Wg, hCg, hGs⟩ := gsT_block hA hb0 hb h1 h2
  obtain ⟨C1, W1, hC1, hS1⟩ := SourceMixing.scalarS1_blocks hA hb0 hb h1 h2
  obtain ⟨CD, WD, hCD, hD⟩ := SourceMixing.dressedBlocks hA hb0 hb h1 h2
  obtain ⟨Cf, Wf, hCf, hF⟩ := SourceMixing.freshU_mean hA hb0 hb h1 h2
  obtain ⟨Cv, Wv, hCv, hVs⟩ := vP_system hA hb0 hb h1 h2
  obtain ⟨Cq, Wq, hCq, hQb⟩ := tP_blocks hA hb0 hb h1 h2
  set Cr := 1 + Cq
  set C₁ := Cz + CD * (Cf * Cg + Cf * (CD * (Cr * C1 + Cv * CD)) + Cv * C1 + Cz * CD) +
    CD * (b * Cz * CD)
  set K := (1 - 2 * b) + b + b ^ 2 * (CD * CD)
  have hK : 0 ≤ K := by have : 0 ≤ 1 - 2 * b := by linarith
                        positivity
  refine ⟨C₁, max (max (max Wz Wg) (max W1 WD)) (max (max Wf Wv) Wq),
    by positivity, fun W hW X hX p => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hWz, hWg⟩, hW1', hWD⟩, ⟨hWf, hWv⟩, hWq⟩ := hW
  obtain ⟨hzb, hentZ, hZ0, hZ1⟩ := hZb W hWz X hX p
  obtain ⟨hentX, hX0⟩ := hGs W hWg X hX p
  obtain ⟨hT00, -⟩ := hS1 W hW1' X hX
  obtain ⟨hW1r, -, hM, hv, -, -, hE0, hE1, -, -, -⟩ := hD W hWD X hX
  obtain ⟨-, hs, -⟩ := hF W hWf X hX
  obtain ⟨hS, -⟩ := hVs W hWv X hX p
  obtain ⟨ht, -, -, -⟩ := hQb W hWq X hX 0
  obtain ⟨ht1, -, hentT, -⟩ := hQb W hWq X hX 1
  rw [bProj_one] at hentT
  set μ := layerLaw W b .oneBlockOnePort
  set M := SourceMixing.mOf b E X
  set v := SourceMixing.vOf b E X
  set s₁ := SourceMixing.sOne b E X
  set S := svP b E X p
  set σ := szP b E X p
  set r := rB b E X p
  set G0 := blkAt (matrixExpect μ (gRes b E X)) 0 0
  set G1 := blkAt (matrixExpect μ (gRes b E X)) 1 1
  set T0 := blkAt (tMean b E X) 0 0
  set T1 := blkAt (tMean b E X) 1 1
  set X0 := blkAt (gsTMean b E X p) 0 0
  set X1 := blkAt (gsTMean b E X p) 1 1
  set c := 1 + (b : ℂ) * SourceMixing.tTwo b E X 0
  have nb : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
  have hσ : ‖σ‖ ≤ Cz := norm_sig1_le hb0 hb (hzb 0) (hzb 1)
  have hr : ‖r‖ ≤ Cr := (norm_add_le _ _).trans (add_le_add (norm_ind_le 0 p)
    (norm_sig1_le hb0 hb (ht p) (ht1 p)))
  have hW2' : (0 : ℝ) < (W : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ W := by exact_mod_cast hW1r
    positivity
  have hzt : ∀ r', zP b E X p r' = SourceMixing.blkTr (matrixExpect μ (fun ω => gRes b E X ω *
      (portProj * ((gRes b E X ω)ᴴ * (bProj p * (gRes b E X ω *
        (portProj * (gRes b E X ω)ᴴ))))))) r' := fun r' =>
    SourceMixing.integral_blkTr _ hentZ r'
  have hC₁ : 0 ≤ C₁ := by positivity
  -- the port trace
  have hT1 : (W : ℂ)⁻¹ * T1.trace = SourceMixing.tTwo b E X 1 := by
    rw [← SourceMixing.blkTr_def, ← SourceMixing.integral_blkTr _ hentT]; rfl
  have hX1 : (W : ℂ)⁻¹ * X1.trace = conj (vP b E X p 1) := by
    rw [← SourceMixing.blkTr_def, ← SourceMixing.integral_blkTr _ hentX, ← trMean_rv]
  set Zt1 := v • (c • X1 + ((b : ℂ) * vP b E X p 0) • T1 + ((b : ℂ) * zP b E X p 0 * conj v) • 1)
  have hZ1 : (W : ℂ)⁻¹ * Zt1.trace = v * (c * conj (vP b E X p 1) +
      (b : ℂ) * vP b E X p 0 * SourceMixing.tTwo b E X 1 + (b : ℂ) * zP b E X p 0 * conj v) := by
    have hW' : (W : ℂ) ≠ 0 := by exact_mod_cast (show W ≠ 0 by omega)
    simp only [Zt1, trace_smul, trace_add, trace_one, Fintype.card_fin, smul_eq_mul]
    rw [← hT1, ← hX1]; field_simp
  have d1 : ‖zP b E X p 1 - v * (c * conj (vP b E X p 1) +
      (b : ℂ) * vP b E X p 0 * SourceMixing.tTwo b E X 1 + (b : ℂ) * zP b E X p 0 * conj v)‖ ≤
      C₁ / (W : ℝ) ^ 2 := by
    rw [← hZ1, hzt]
    refine (SourceMixing.norm_blkTr_sub_le _ 1 _).trans ?_
    have e : v • (c • X1 + ((b : ℂ) * vP b E X p 0) • T1 + ((b : ℂ) * zP b E X p 0) • G1ᴴ) - Zt1 =
        v • (((b : ℂ) * zP b E X p 0) • (G1 - v • 1)ᴴ) := by
      rw [conjTranspose_sub, conjTranspose_smul, conjTranspose_one]
      simp only [Zt1, smul_sub, smul_add, smul_smul, mul_assoc, Complex.star_def]; abel
    have hb2 : ‖v • (c • X1 + ((b : ℂ) * vP b E X p 0) • T1 + ((b : ℂ) * zP b E X p 0) • G1ᴴ) - Zt1‖ ≤
        CD * (b * Cz * CD) / (W : ℝ) ^ 2 := by
      rw [e]
      refine (norm_smul_le _ _).trans ((mul_le_mul hv ((norm_smul_le _ _).trans (mul_le_mul
        (show ‖(b : ℂ) * zP b E X p 0‖ ≤ b * Cz by
          rw [norm_mul, nb]; exact mul_le_mul_of_nonneg_left (hzb 0) hb0.le)
        (show ‖(G1 - v • 1)ᴴ‖ ≤ CD / (W : ℝ) ^ 2 by rw [Matrix.l2_opNorm_conjTranspose]; exact hE1)
        (norm_nonneg _) (by positivity))) (by positivity) hCD).trans (le_of_eq (by ring)))
    have := norm_sub_le_norm_sub_add_norm_sub (blkAt (matrixExpect μ (fun ω => gRes b E X ω *
      (portProj * ((gRes b E X ω)ᴴ * (bProj p * (gRes b E X ω *
        (portProj * (gRes b E X ω)ᴴ))))))) 1 1)
      (v • (c • X1 + ((b : ℂ) * vP b E X p 0) • T1 + ((b : ℂ) * zP b E X p 0) • G1ᴴ)) Zt1
    calc _ ≤ Cz / (W : ℝ) ^ 2 + CD * (b * Cz * CD) / (W : ℝ) ^ 2 := by linarith
      _ ≤ C₁ / (W : ℝ) ^ 2 := by
          rw [← add_div]; refine div_le_div_of_nonneg_right ?_ hW2'.le
          have : 0 ≤ CD * (Cf * Cg + Cf * (CD * (Cr * C1 + Cv * CD)) + Cv * C1 + Cz * CD) := by
            positivity
          simp only [C₁]; linarith
  exact d1

/-- **The `z_p` trace system.** -/
theorem zP_system (hA : PassiveLayer.PassiveBoundsStatement) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ,
      (passiveY X).PosDef → ∀ p : Fin 2,
        ‖szP b E X p‖ ≤ C ∧
        ‖szP b E X p * (1 - SourceMixing.khOf b E X * SourceMixing.aOf b E X) -
          (SourceMixing.khOf b E X * (SourceMixing.sOne b E X * (SourceMixing.sOne b E X *
              rB b E X p * cqOf b E X + conj (svP b E X p) * conj (SourceMixing.bOf b E X)) +
              svP b E X p * SourceMixing.sOne b E X * SourceMixing.bOf b E X) +
            (b : ℂ) * SourceMixing.vOf b E X * (1 + (b : ℂ) * SourceMixing.tTwo b E X 0) *
              conj (vP b E X p 1) +
            (b : ℂ) * ((b : ℂ) * SourceMixing.vOf b E X) * vP b E X p 0 *
              SourceMixing.tTwo b E X 1)‖ ≤ C / (W : ℝ) ^ 2 := by
  obtain ⟨C₀, W₀, hC₀, hz0⟩ := zP_trace0 hA hb0 hb h1 h2
  obtain ⟨C₂, W₂, hC₂, hz1⟩ := zP_trace1 hA hb0 hb h1 h2
  obtain ⟨CD, WD, hCD, hD⟩ := SourceMixing.dressedBlocks hA hb0 hb h1 h2
  set C₁ := C₀ + C₂
  set K := (1 - 2 * b) + b + b ^ 2 * (CD * CD)
  have hK : 0 ≤ K := by have : 0 ≤ 1 - 2 * b := by linarith
                        positivity
  refine ⟨C₀ + (K + 1) * C₁, max (max W₀ W₂) WD, by positivity, fun W hW X hX p => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨hW0, hW2⟩, hWD⟩ := hW
  obtain ⟨hσ, -, d0'⟩ := hz0 W hW0 X hX p
  have d1' := hz1 W hW2 X hX p
  obtain ⟨hW1r, -, -, hv, -⟩ := hD W hWD X hX
  have hW2' : (0 : ℝ) < (W : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ W := by exact_mod_cast hW1r
    positivity
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hc0 : C₀ ≤ C₁ := by simp only [C₁]; linarith
  have hc2 : C₂ ≤ C₁ := by simp only [C₁]; linarith
  have d0 := d0'.trans (div_le_div_of_nonneg_right hc0 hW2'.le)
  have d1 := d1'.trans (div_le_div_of_nonneg_right hc2 hW2'.le)
  have nb : ‖(b : ℂ)‖ = b := by rw [Complex.norm_real, Real.norm_of_nonneg hb0.le]
  set v := SourceMixing.vOf b E X
  set σ := szP b E X p
  set c := 1 + (b : ℂ) * SourceMixing.tTwo b E X 0
  have hup : ∀ c' : ℝ, c' ≤ C₀ + (K + 1) * C₁ → c' / (W : ℝ) ^ 2 ≤
      (C₀ + (K + 1) * C₁) / (W : ℝ) ^ 2 := fun c' hc' => div_le_div_of_nonneg_right hc' hW2'.le
  have hKC : 0 ≤ (K + 1) * C₁ := by positivity
  refine ⟨hσ.trans (by linarith), ?_⟩
  set A := SourceMixing.aOf b E X
  set I := SourceMixing.sOne b E X * (SourceMixing.sOne b E X * rB b E X p * cqOf b E X +
    conj (svP b E X p) * conj (SourceMixing.bOf b E X)) +
    svP b E X p * SourceMixing.sOne b E X * SourceMixing.bOf b E X
  set t₂ := SourceMixing.tTwo b E X 1
  have e : σ * (1 - SourceMixing.khOf b E X * A) - (SourceMixing.khOf b E X * I +
      (b : ℂ) * v * c * conj (vP b E X p 1) + (b : ℂ) * ((b : ℂ) * v) * vP b E X p 0 * t₂) =
      ((1 - 2 * b : ℝ) : ℂ) * (zP b E X p 0 - (I + σ * A)) +
        (b : ℂ) * (zP b E X p 1 - v * (c * conj (vP b E X p 1) + (b : ℂ) * vP b E X p 0 * t₂ +
          (b : ℂ) * zP b E X p 0 * conj v)) +
        (b : ℂ) ^ 2 * (v * conj v) * (zP b E X p 0 - (I + σ * A)) := by
    unfold SourceMixing.khOf SourceMixing.hOf
    rw [show σ = ((1 - 2 * b : ℝ) : ℂ) * zP b E X p 0 + (b : ℂ) * zP b E X p 1 from rfl]
    ring
  rw [e]
  have hh : ‖v * conj v‖ ≤ CD * CD := by
    rw [norm_mul, Complex.norm_conj]; exact mul_le_mul hv hv (norm_nonneg _) hCD
  have nc : ‖((1 - 2 * b : ℝ) : ℂ)‖ = 1 - 2 * b := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hW2 : (0 : ℝ) ≤ C₁ / (W : ℝ) ^ 2 := by positivity
  calc _ ≤ ‖((1 - 2 * b : ℝ) : ℂ) * (zP b E X p 0 - (I + σ * A))‖ +
        ‖(b : ℂ) * (zP b E X p 1 - v * (c * conj (vP b E X p 1) + (b : ℂ) * vP b E X p 0 * t₂ +
          (b : ℂ) * zP b E X p 0 * conj v))‖ +
        ‖(b : ℂ) ^ 2 * (v * conj v) * (zP b E X p 0 - (I + σ * A))‖ := norm_add₃_le
    _ ≤ (1 - 2 * b) * (C₁ / (W : ℝ) ^ 2) + b * (C₁ / (W : ℝ) ^ 2) +
        b ^ 2 * (CD * CD) * (C₁ / (W : ℝ) ^ 2) := by
        rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, nc, nb]
        have : 0 ≤ 1 - 2 * b := by linarith
        gcongr
    _ ≤ (C₀ + (K + 1) * C₁) / (W : ℝ) ^ 2 := by
        rw [show (1 - 2 * b) * (C₁ / (W : ℝ) ^ 2) + b * (C₁ / (W : ℝ) ^ 2) +
          b ^ 2 * (CD * CD) * (C₁ / (W : ℝ) ^ 2) = K * C₁ / (W : ℝ) ^ 2 by ring]
        refine hup _ ?_
        nlinarith

end BlockBand.Transmission.PassiveCovariance
