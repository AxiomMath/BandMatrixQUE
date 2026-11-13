module

public import BlockBand.Transmission.Generator.MeanScalar
public import BlockBand.Transmission.Generator.RefinedStrict

/-!
# The one-layer mean `Ū = E[LL*]` on the matched domain: operator and `G`-weighted bounds

The algebraic steps (`wm_op_alg`, `wm_wt_alg`, `wm_prep`) of the two bounds `wm_onDomain_op` (a) and
`wm_onDomain_wt` (b) (same explicit inputs as `rf_onDomain`), for a strictly passive `X`:
* (a) `‖Ū - c·I‖ ≤ K_a1 W⁻² + K_a2 e + K_a3 q/W`;
* (b) for **every** `G ⪰ 0`, with `g = Re Tr G`, `τ_G = |Tr(Gf)|`:
  `|Tr(GŪ) - c·Tr G| ≤ K₀W⁻²g + 4C_m eτ_G + K₂e²g + K₃eqg/W`.
(b) at `G = Q` is the refined mean bound (with the complex trace); the weight enters only through
the numerator `u_G = Tr(KMᴴGKM)` (`wm_u_expand`, `wm_scalar`); `Im s₁ = O(W⁻²)` is `rf_s_cplx`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PathScalar
open BlockBand.Transmission.SourceMixing BlockBand.Transmission.LengthUniform
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- The one-layer mean factor `c = (1 + αq/W)⁻¹`. -/
def meanC (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  (1 + alphaCoef b E * passiveMass b E X / W)⁻¹

/-- `u = Re Tr(MᴴYM)`. -/
def wmU (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  ((mOf b E X)ᴴ * passiveY X * mOf b E X).trace.re

/-- `D = bhη + k_h u/W`. -/
def wmD (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  b * Complex.normSq (vOf b E X) * etaZ b E +
    ((1 - 2 * b) + b ^ 2 * Complex.normSq (vOf b E X)) * (wmU b E X / W)

/-- `ρ = bhι/D`, `ι = η - Im ω`, `ω = z - ζ`: the real approximation of `s₁`. -/
def wmRho (b E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  b * Complex.normSq (vOf b E X) * (etaZ b E - (boundaryZ b E - zetaX b E X).im) / wmD b E X

/-- **Abstract operator step** of (a). -/
theorem wm_op_alg {U KM : Matrix (Fin W) (Fin W) ℂ} {s : ℂ} {ρ c Cf Cm e ε₀ D Li b q : ℝ}
    (hU : ‖U - s • (KM * KMᴴ)‖ ≤ Cf / (W : ℝ) ^ 2) (hsn : ‖s‖ ≤ Cf)
    (hKM1 : ‖KM - 1‖ ≤ Cm * e) (hKMn : ‖KM‖ ≤ 3 / 2) (hsρ : ‖s - (ρ : ℂ)‖ * D ≤ ε₀ / (W : ℝ) ^ 2)
    (hD0 : 0 < D) (hDinv : 1 / D ≤ 2 * Li / b)
    (hρc : |ρ - c| ≤ Cm * Li * e + 10 * Li / b * (q / W)) :
    ‖U - (c : ℂ) • 1‖ ≤ (Cf + ε₀ * (2 * Li / b)) * (W : ℝ)⁻¹ ^ 2 +
      (Cf * (5 / 2 * Cm) + Cm * Li) * e + 10 * Li / b * (q / W) := by
  have hCf : 0 ≤ Cf := (norm_nonneg _).trans hsn
  have hn1 : ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ 1 := PassiveLayer.norm_one_le'
  have hW2e : 0 ≤ ε₀ / (W : ℝ) ^ 2 := (mul_nonneg (norm_nonneg _) hD0.le).trans hsρ
  have hCme : 0 ≤ Cm * e := (norm_nonneg _).trans hKM1
  have hKK : ‖KM * KMᴴ - 1‖ ≤ 5 / 2 * (Cm * e) := by
    have e1 : KM * KMᴴ - 1 = (KM - 1) * KMᴴ + (KM - 1)ᴴ := by
      simp only [conjTranspose_sub, conjTranspose_one, Matrix.sub_mul, Matrix.one_mul]; abel
    rw [e1]
    refine (norm_add_le _ _).trans ?_
    rw [Matrix.l2_opNorm_conjTranspose]
    have := (Matrix.l2_opNorm_mul (KM - 1) KMᴴ).trans (mul_le_mul hKM1
      (show ‖KMᴴ‖ ≤ 3 / 2 by rw [Matrix.l2_opNorm_conjTranspose]; exact hKMn) (norm_nonneg _) hCme)
    linarith
  have e2 : U - (c : ℂ) • 1 = (U - s • (KM * KMᴴ)) + s • (KM * KMᴴ - 1) +
      ((s - (ρ : ℂ)) • 1 + (((ρ - c : ℝ)) : ℂ) • 1) := by
    push_cast; simp only [smul_sub, sub_smul]; abel
  rw [e2]
  have b1 : ‖s • (KM * KMᴴ - 1)‖ ≤ Cf * (5 / 2 * (Cm * e)) :=
    (norm_smul_le _ _).trans (mul_le_mul hsn hKK (norm_nonneg _) hCf)
  have b2 : ‖(s - (ρ : ℂ)) • (1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ ε₀ * (2 * Li / b) *
      (W : ℝ)⁻¹ ^ 2 := by
    refine (norm_smul_le _ _).trans ((mul_le_mul_of_nonneg_left hn1 (norm_nonneg _)).trans ?_)
    rw [mul_one]
    have : ‖s - (ρ : ℂ)‖ = ‖s - (ρ : ℂ)‖ * D * (1 / D) := by field_simp
    rw [this]
    calc ‖s - (ρ : ℂ)‖ * D * (1 / D) ≤ ε₀ / (W : ℝ) ^ 2 * (2 * Li / b) :=
          mul_le_mul hsρ hDinv (by positivity) hW2e
      _ = _ := by rw [inv_pow, div_eq_mul_inv]; ring
  have b3 : ‖(((ρ - c : ℝ)) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤
      Cm * Li * e + 10 * Li / b * (q / W) := by
    refine (norm_smul_le _ _).trans ((mul_le_mul_of_nonneg_left hn1 (norm_nonneg _)).trans ?_)
    rw [mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact hρc
  have b0 : ‖U - s • (KM * KMᴴ)‖ ≤ Cf * (W : ℝ)⁻¹ ^ 2 := by
    rw [inv_pow, ← div_eq_mul_inv]; exact hU
  have t1 := norm_add_le (U - s • (KM * KMᴴ)) (s • (KM * KMᴴ - 1))
  have t2 := norm_add_le ((s - (ρ : ℂ)) • (1 : Matrix (Fin W) (Fin W) ℂ))
    ((((ρ - c : ℝ)) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ))
  have t3 := norm_add_le (U - s • (KM * KMᴴ) + s • (KM * KMᴴ - 1))
    ((s - (ρ : ℂ)) • (1 : Matrix (Fin W) (Fin W) ℂ) +
      (((ρ - c : ℝ)) : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ))
  have e3 : (Cf + ε₀ * (2 * Li / b)) * (W : ℝ)⁻¹ ^ 2 + (Cf * (5 / 2 * Cm) + Cm * Li) * e =
      Cf * (W : ℝ)⁻¹ ^ 2 + Cf * (5 / 2 * (Cm * e)) + ε₀ * (2 * Li / b) * (W : ℝ)⁻¹ ^ 2 +
        Cm * Li * e := by ring
  linarith

/-- **Abstract weighted step** of (b). -/
theorem wm_wt_alg {G U KM : Matrix (Fin W) (Fin W) ℂ} (hGp : G.PosSemidef) {s : ℂ}
    {ρ c Cf ε₀ D Li b S : ℝ}
    (hU : ‖U - s • (KM * KMᴴ)‖ ≤ Cf / (W : ℝ) ^ 2) (hKMn : ‖KM‖ ≤ 3 / 2)
    (hsρ : ‖s - (ρ : ℂ)‖ * D ≤ ε₀ / (W : ℝ) ^ 2)
    (hD0 : 0 < D) (hDinv : 1 / D ≤ 2 * Li / b)
    (hS : |ρ * (KMᴴ * G * KM).trace.re - c * G.trace.re| ≤ S) :
    ‖(G * U).trace - (c : ℂ) * G.trace‖ ≤
      (Cf + ε₀ * (9 / 2 * Li / b)) * ((W : ℝ)⁻¹ ^ 2 * G.trace.re) + S := by
  set g := G.trace.re
  have hg0 : 0 ≤ g := (mm_trace_posSemidef hGp).1
  set uG := (KMᴴ * G * KM).trace.re
  obtain ⟨huG0, huGr⟩ := mm_trace_posSemidef (hGp.conjTranspose_mul_mul_same KM)
  have hW2e : 0 ≤ ε₀ / (W : ℝ) ^ 2 := (mul_nonneg (norm_nonneg _) hD0.le).trans hsρ
  have huGg : uG ≤ 9 / 4 * g := by
    have hh := norm_trace_mul_posSemidef_le hGp (KM * KMᴴ)
    have htQ : (KM * KMᴴ * G).trace = (uG : ℂ) := by
      rw [← huGr, trace_mul_comm, ← Matrix.mul_assoc, trace_mul_comm, ← Matrix.mul_assoc]
    rw [htQ, Complex.norm_real, Real.norm_of_nonneg huG0] at hh
    refine hh.trans (mul_le_mul_of_nonneg_right ?_ hg0)
    refine (Matrix.l2_opNorm_mul _ _).trans ?_
    rw [Matrix.l2_opNorm_conjTranspose]
    nlinarith [norm_nonneg KM]
  have htr : (G * (s • (KM * KMᴴ))).trace = s * (uG : ℂ) := by
    rw [Matrix.mul_smul, trace_smul, smul_eq_mul, ← huGr, ← Matrix.mul_assoc,
      trace_mul_comm, ← Matrix.mul_assoc]
  have e2 : (G * U).trace - (c : ℂ) * G.trace =
      (G * (U - s • (KM * KMᴴ))).trace + (s - (ρ : ℂ)) * (uG : ℂ) +
        (((ρ * uG - c * g : ℝ)) : ℂ) := by
    have hgr : G.trace = (g : ℂ) := (mm_trace_posSemidef hGp).2
    rw [Matrix.mul_sub, trace_sub, htr, hgr]
    push_cast; ring
  rw [e2]
  have c1 : ‖(G * (U - s • (KM * KMᴴ))).trace‖ ≤ Cf * ((W : ℝ)⁻¹ ^ 2 * g) := by
    rw [trace_mul_comm]
    refine (norm_trace_mul_posSemidef_le hGp _).trans ?_
    calc ‖U - s • (KM * KMᴴ)‖ * g ≤ Cf / (W : ℝ) ^ 2 * g := mul_le_mul_of_nonneg_right hU hg0
      _ = _ := by rw [inv_pow, div_eq_mul_inv]; ring
  have c2 : ‖(s - (ρ : ℂ)) * (uG : ℂ)‖ ≤ ε₀ * (9 / 2 * Li / b) * ((W : ℝ)⁻¹ ^ 2 * g) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg huG0]
    have : ‖s - (ρ : ℂ)‖ * uG = ‖s - (ρ : ℂ)‖ * D * (uG / D) := by field_simp
    rw [this]
    have huD : uG / D ≤ 9 / 2 * Li / b * g := by
      rw [div_eq_mul_one_div]
      calc uG * (1 / D) ≤ 9 / 4 * g * (2 * Li / b) :=
            mul_le_mul huGg hDinv (by positivity) (by positivity)
        _ = _ := by ring
    calc ‖s - (ρ : ℂ)‖ * D * (uG / D) ≤ ε₀ / (W : ℝ) ^ 2 * (9 / 2 * Li / b * g) :=
          mul_le_mul hsρ huD (by positivity) hW2e
      _ = _ := by rw [inv_pow, div_eq_mul_inv]; ring
  have c3 : ‖(((ρ * uG - c * g : ℝ)) : ℂ)‖ ≤ S := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hS
  have := norm_add_le ((G * (U - s • (KM * KMᴴ))).trace + (s - (ρ : ℂ)) * (uG : ℂ))
    (((ρ * uG - c * g : ℝ)) : ℂ)
  have := norm_add_le (G * (U - s • (KM * KMᴴ))).trace ((s - (ρ : ℂ)) * (uG : ℂ))
  have e3 : (Cf + ε₀ * (9 / 2 * Li / b)) * ((W : ℝ)⁻¹ ^ 2 * g) =
      Cf * ((W : ℝ)⁻¹ ^ 2 * g) + ε₀ * (9 / 2 * Li / b) * ((W : ℝ)⁻¹ ^ 2 * g) := by ring
  linarith

/-- **On-domain preparation**: `‖s₁ - ρ‖D ≤ ε₀/W²`, `D ≥ bη/2`, `‖KM‖ ≤ 3/2`, `u ≤ 9q/4`. -/
theorem wm_prep {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    (hW1 : 1 ≤ W) {X : Matrix (Fin W) (Fin W) ℂ} (hX : (passiveY X).PosDef)
    {Cf C2 CD Cm Li e : ℝ} (hLi : (etaZ b E)⁻¹ ≤ Li) (hCme : Cm * e ≤ 1 / 2)
    (hzζ : ‖boundaryZ b E - zetaX b E X‖ ≤ Cm * e) (hKM1 : ‖kmOf b E X - 1‖ ≤ Cm * e)
    (hh1 : |Complex.normSq (vOf b E X) - 1| ≤ Cm * e) (hz2 : ‖boundaryZ b E‖ ≤ 2)
    (hsn : ‖sOne b E X‖ ≤ Cf)
    (hG : ∀ α β, Integrable (fun ω => gRes b E X ω α β) (layerLaw W b .oneBlockOnePort))
    (hB0 : ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 0 0 - mOf b E X‖ ≤
      CD / (W : ℝ) ^ 2)
    (hB1 : ‖blkAt (matrixExpect (layerLaw W b .oneBlockOnePort) (gRes b E X)) 1 1 -
      vOf b E X • 1‖ ≤ CD / (W : ℝ) ^ 2)
    (hzM : (zetaX b E X • 1 - X) * mOf b E X = 1)
    (hS : ‖sOne b E X * (1 - khOf b E X * aOf b E X) - (b : ℂ) * hOf b E X‖ ≤
      C2 / (W : ℝ) ^ 2) :
    ‖sOne b E X - (wmRho b E X : ℂ)‖ * wmD b E X ≤ (3 * C2 + Cf * (2 * CD)) / (W : ℝ) ^ 2 ∧
      0 < wmD b E X ∧ 1 / wmD b E X ≤ 2 * Li / b ∧ ‖kmOf b E X‖ ≤ 3 / 2 ∧
      0 ≤ wmU b E X ∧ wmU b E X ≤ 9 / 4 * passiveMass b E X := by
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW1
  have hYs := hX.posSemidef
  obtain ⟨-, hRz⟩ := nearPencil_inverse hb0 hb h1 h2 hYs
  have hKMeq : kmOf b E X = (boundaryZ b E • 1 - X) * mOf b E X :=
    (blkAt_kHat_mul_zero b E X _).1
  have hRKM : passiveResolvent b E X * kmOf b E X = mOf b E X := by
    rw [hKMeq, ← Matrix.mul_assoc, hRz, Matrix.one_mul]
  obtain ⟨hu0, -, huq, -⟩ := mm_trace_decomp (Q := passiveQ b E X)
    (U := (1 : Matrix (Fin W) (Fin W) ℂ)) 0 hYs rfl hRKM
  have hKMn : ‖kmOf b E X‖ ≤ 3 / 2 := by
    have := norm_add_le (kmOf b E X - 1) 1
    rw [sub_add_cancel] at this
    have h1' : ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ 1 := PassiveLayer.norm_one_le'
    linarith
  have hιb : |(zetaX b E X).im| ≤ 3 := by
    have h' : ‖zetaX b E X‖ ≤ ‖boundaryZ b E‖ + ‖boundaryZ b E - zetaX b E X‖ := by
      have := norm_sub_le (boundaryZ b E) (boundaryZ b E - zetaX b E X)
      rwa [sub_sub_cancel] at this
    have := Complex.abs_im_le_norm (zetaX b E X)
    linarith
  have hsc := rf_s_cplx hW1 hb0 hb hG hB0 hB1 hzM hS hsn (hh1.trans hCme) hιb
  have hι : (zetaX b E X).im = etaZ b E - (boundaryZ b E - zetaX b E X).im := by
    simp only [etaZ, Complex.sub_im]; ring
  have hhlo : 1 / 2 ≤ Complex.normSq (vOf b E X) := by
    have := neg_abs_le (Complex.normSq (vOf b E X) - 1); linarith
  have hD : b * (1 / 2) * etaZ b E ≤ wmD b E X := by
    have a1 : 0 ≤ ((1 - 2 * b) + b ^ 2 * Complex.normSq (vOf b E X)) * (wmU b E X / W) :=
      mul_nonneg (by nlinarith [Complex.normSq_nonneg (vOf b E X)]) (div_nonneg hu0 hWpos.le)
    have a2 : b * (1 / 2) * etaZ b E ≤ b * Complex.normSq (vOf b E X) * etaZ b E :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhlo hb0.le) hη.le
    exact a2.trans (le_add_of_nonneg_right a1)
  have hD0 : 0 < wmD b E X := lt_of_lt_of_le (by positivity) hD
  have hLiη : 1 ≤ Li * etaZ b E := by
    have := mul_le_mul_of_nonneg_right hLi hη.le
    rwa [inv_mul_cancel₀ hη.ne'] at this
  refine ⟨?_, hD0, ?_, hKMn, hu0, huq.trans (mul_le_mul_of_nonneg_right
    (by have := pow_le_pow_left₀ (norm_nonneg _) hKMn 2; linarith)
    (passiveMass_nonneg b E hYs))⟩
  · have e1 : (sOne b E X - (wmRho b E X : ℂ)) * (wmD b E X : ℂ) = sOne b E X *
        (wmD b E X : ℂ) - ((b * Complex.normSq (vOf b E X) : ℝ) : ℂ) *
        (((zetaX b E X).im : ℝ) : ℂ) := by
      rw [hι, wmRho]; push_cast; field_simp
    have := congrArg norm e1
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hD0.le] at this
    rw [this]; exact hsc
  · rw [div_le_div_iff₀ hD0 hb0]
    nlinarith

end BlockBand.Transmission.Generator
