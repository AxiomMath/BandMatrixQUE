module

public import BlockBand.Endpoints.Response.ResponseVarianceDefs
public import BlockBand.Endpoints.Response.PassDerivativeLimitBridge
public import BlockBand.Endpoints.Response.PathFractionalInverseMoment
public import BlockBand.Endpoints.Sine.GUELawBridge
public import BlockBand.Endpoints.Sine.MicroscopicTagPort
public import BlockBand.Endpoints.Poisson.PhaseFractionalCollar
public import BlockBand.Internal.Contracts.TransmissionUniform
public import BlockBand.Internal.Contracts.Inputs

/-!
# The multiplier moment of the physical Fourier variance bound

In the response variance theorem, the multiplier costs `E[(Tr A)²(1+g)]`, bounded by the
full-clock fourth moment and the positive-time conductance second moment.

**Law.** The near-end-grown path law `growthPathLaw W b`, `0 < b < 1/2`.

**Quantifiers.** `b`, a bulk margin `κ > 0`, a time floor `ε > 0` and a horizon `T` first;
then `C, W₀`; for `W ≥ W₀`, every real energy `e ∈ bulkInterval κ` and every length
`εW ≤ r ≤ TW`: `E[(1 + √g)²(Tr A)²] ≤ C`, `A = W⁻²U*U` the complete matched-lead clock and
`g = Tr T_L` the zero-source near-port reflection defect.

**Proof.**
* `Tr U*U = Tr 𝒰*𝒰 + Tr ℝ*ℝ` (interior and port rows of `U = G V`);
  `Tr ℝ*ℝ ≤ 2W/η²` for Hermitian blocks (`portLeadMass_le`), `η ≥ etaMin` on the bulk;
* `g = pathConductance` almost surely (Schur complements at zero absorption, the algebraic
  identity `passive_scattering_physical`; a.s. invertibility of `H_path - e` from the Wegner
  count `path_ae_isUnit`, inputs `ConditionalBlockGUECount` and `guelawBridge_holds`);
* `(1 + √g)²X² ≤ 1 + 2X⁴ + g²`, `X⁴ ≤ 8(W⁻²Tr 𝒰*𝒰)⁴ + 8(2/η²)⁴`;
* the clock field of the hypothesis `FullSourceMomentsEnergyUniformContract` (`p = 4`, `E' = E`,
  `C_e = 0`) and the conductance field of the hypothesis `TransmissionLengthUniformContract`
  (`p = 2`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Layers
  BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.TransmissionUniform
  BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission
open scoped ENNReal NNReal ComplexOrder

variable {W n : ℕ}

/-!
### The zero-absorption bridge `g = pathConductance`
-/

theorem rvC_matrixImaginaryPart_of_isHermitian {m : Type*} {M : Matrix m m ℂ}
    (hM : M.IsHermitian) : matrixImaginaryPart M = 0 := by
  rw [matrixImaginaryPart, hM.eq, sub_self, smul_zero]

/-- **Bridge at zero absorption.** For Hermitian blocks, bulk `E`, `b < 1` and invertible
`H_path - E`, the near-port reflection defect of the unabsorbed full path is
`pathTransmission` at zero absorption. -/
theorem rvC_portDefect_scattering {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2)
    {ω : GrowthPath W} (hH : ∀ k, (ω.1 k).IsHermitian)
    (hA : IsUnit (pathMatrix (pathAt W n ω) - (E : ℂ) • 1).det) :
    portDefect (scatteringMatrix b E W n ω) 0 = pathTransmission b E (fun _ => 0) W n ω := by
  set z := boundaryZ b E
  set η := etaZ b E
  have hη : 0 < η := etaZ_pos hb hE1 hE2
  have hz : 0 < z.im := hη
  set A := pathMatrix (pathAt W n ω) - (E : ℂ) • 1
  have hHh : A.IsHermitian := by
    have h0 := pathMatrix_isHermitian (W := W) (n := n) (ω := pathAt W n ω) fun i => hH _
    refine h0.sub ?_
    unfold IsHermitian
    rw [conjTranspose_smul, conjTranspose_one, Complex.star_def, Complex.conj_ofReal]
  have hAinv : (-matrixImaginaryPart A⁻¹).PosSemidef := by
    rw [rvC_matrixImaginaryPart_of_isHermitian hHh.inv, neg_zero]
    exact PosSemidef.zero
  set C := pathPortCoupling (pathAt W n ω)
  set X := Cᴴ * A⁻¹ * C
  have hXim : (-matrixImaginaryPart X).PosSemidef := posSemidef_neg_im_conj C hAinv
  set K := z • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - X
  have hK : IsUnit K := isUnit_smul_one_sub hz hXim
  have hfull : boundaryResolvent b E W n ω = K⁻¹ := by
    have e : fullPathMatrix b E W n ω = fromBlocks A C Cᴴ (z • 1) := rfl
    rw [boundaryResolvent, fullInverse, e,
      toBlocks₂₂_inv_fromBlocks A C Cᴴ (z • 1) ((isUnit_iff_isUnit_det _).2 hA) hK]
  have h11 : IsUnit (portBlock K 1 1) := by
    rw [portBlock_eq_compression']
    apply isUnit_of_matrixImaginaryPart_posDef
    rw [matrixImaginaryPart_congruence]
    refine PosDef.conjTranspose_mul_mul_same ?_ (portInclusion_injective 1)
    rw [matrixImaginaryPart_smul_one_sub]
    refine PosDef.add_posSemidef ?_ hXim
    have : (z.im : ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) =
        z.im • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) := by
      ext i j; simp [Complex.real_smul]
    rw [this]
    exact PosDef.one.smul hz
  have hblk : ∀ i j : Fin 2, portBlock K i j =
      (if i = j then z • (1 : Matrix (Fin W) (Fin W) ℂ) else 0) - portBlock X i j := by
    intro i j
    ext a c
    by_cases hij : i = j
    · subst hij
      simp [portBlock, K, one_apply, Prod.ext_iff]
    · simp [portBlock, K, one_apply, Prod.ext_iff, hij]
  set N := nearSchur z X
  have hSchur : portBlock K 0 0 - portBlock K 0 1 * (portBlock K 1 1)⁻¹ * portBlock K 1 0 =
      z • (1 : Matrix (Fin W) (Fin W) ℂ) - N := by
    rw [hblk 0 0, hblk 0 1, hblk 1 0, hblk 1 1]
    simp only [ite_true, show (0 : Fin 2) ≠ 1 from by decide, show (1 : Fin 2) ≠ 0 from by decide,
      ite_false, zero_sub, Matrix.neg_mul, Matrix.mul_neg, neg_neg, N, nearSchur]
    abel
  have hR : portBlock K⁻¹ 0 0 = (z • (1 : Matrix (Fin W) (Fin W) ℂ) - N)⁻¹ := by
    rw [portBlock_inv_00 K h11 hK, hSchur]
  have hNu : IsUnit (z • (1 : Matrix (Fin W) (Fin W) ℂ) - N) := by
    rw [← hSchur]
    have hsub : IsUnit (K.submatrix (portSplit W) (portSplit W)) := by
      rw [isUnit_iff_isUnit_det, det_submatrix_equiv_self]
      exact (isUnit_iff_isUnit_det _).1 hK
    rw [submatrix_portSplit] at hsub
    exact isUnit_schur₂₂ _ _ _ _ h11 hsub
  set R := (z • (1 : Matrix (Fin W) (Fin W) ℂ) - N)⁻¹
  have hKR : (z • (1 : Matrix (Fin W) (Fin W) ℂ) - N) * R = 1 :=
    mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hNu)
  have hbal : (z • (1 : Matrix (Fin W) (Fin W) ℂ) - N) -
      star (z • (1 : Matrix (Fin W) (Fin W) ℂ) - N) =
      (2 * Complex.I * (η : ℂ)) • (1 : Matrix (Fin W) (Fin W) ℂ) +
        (2 * Complex.I) • passiveY N := by
    rw [star_eq_conjTranspose, conjTranspose_sub, conjTranspose_smul, conjTranspose_one,
      passiveY, matrixImaginaryPart]
    have hzc : z - star z = 2 * Complex.I * (η : ℂ) := by
      apply Complex.ext <;> simp [η, etaZ, z]
      ring
    have e1 : z • (1 : Matrix (Fin W) (Fin W) ℂ) - N - (star z • 1 - Nᴴ) =
        (z - star z) • (1 : Matrix (Fin W) (Fin W) ℂ) - (N - Nᴴ) := by
      rw [sub_smul]; abel
    rw [e1, hzc]
    have e2 : (2 * Complex.I) • -((-Complex.I / 2) • (N - Nᴴ)) = -(N - Nᴴ) := by
      rw [smul_neg, smul_smul]
      have : 2 * Complex.I * (-Complex.I / 2) = 1 := by
        field_simp; rw [Complex.I_sq]; ring
      rw [this, one_smul]
    rw [e2, sub_eq_add_neg]
  have hphys := passive_scattering_physical _ R (passiveY N) η hKR hbal
  have hS00 : portBlock (scatteringMatrix b E W n ω) 0 0 =
      1 - (2 * Complex.I * (η : ℂ)) • R := by
    rw [scatteringMatrix, hfull]
    have : portBlock (1 - (((2 * η : ℝ) : ℂ) * Complex.I) • K⁻¹) 0 0 =
        1 - (((2 * η : ℝ) : ℂ) * Complex.I) • portBlock K⁻¹ 0 0 := by
      ext a c
      simp [portBlock, one_apply, Prod.ext_iff]
    rw [this, hR]
    congr 2
    push_cast; ring
  have hX0 : absorbedPathSchur E (layerAbsorption W (fun _ => 0) n) (pathAt W n ω) = X := by
    have h : absorptionDiag (r := n) W (layerAbsorption W (fun _ => 0) n) = 0 := by
      ext x y; simp [absorptionDiag, layerAbsorption, diagonal_apply]
    simp only [absorbedPathSchur, h, add_zero, X, A, C]
  rw [portDefect, hS00, ← star_eq_conjTranspose, hphys]
  simp only [pathTransmission, passiveTransmission, passiveQ, passiveResolvent, pathNearSchur, hX0]
  rw [star_eq_conjTranspose]
  push_cast
  rfl

/-- Almost surely `g = rvConductance` is the conductance `g_r = pathConductance`. -/
theorem rvC_ae_conductance_eq (hCount : ConditionalBlockGUECount) {b E : ℝ} (hb : b < 1 / 2)
    (hE1 : -2 < E) (hE2 : E < 2) (hW : 0 < W) (r : ℕ) :
    ∀ᵐ ω ∂growthPathLaw W b, rvConductance b E W r ω = pathConductance b E W r ω := by
  have hDh : ∀ B, (pathBondPart W r B - (E : ℂ) • 1).IsHermitian := fun B => by
    refine (pathBondPart_isHermitian W r B).sub ?_
    unfold IsHermitian
    rw [conjTranspose_smul, conjTranspose_one, Complex.star_def, Complex.conj_ofReal]
  filter_upwards [path_ae_isUnit hCount guelawBridge_holds hW hb
    (fun B => pathBondPart W r B - (E : ℂ) • 1) ((measurable_pathBondPart W r).sub_const _) hDh,
    ae_growthPath_isHermitian W b] with ω h1 hH
  have hA : IsUnit (pathMatrix (pathAt W r ω) - (E : ℂ) • 1).det := by
    have : pathMatrix (pathAt W r ω) - (E : ℂ) • 1 =
        pathBondPart W r ω.2 - (E : ℂ) • 1 + blockSumOf (pathBlocks W r ω) := by
      rw [pathMatrix_pathAt_eq]; abel
    rw [this]; exact h1
  rw [rvConductance, rvC_portDefect_scattering (by linarith) hE1 hE2 hH hA]
  rfl

/-!
### The clock: interior and port parts
-/

theorem rvC_gram_trace_re {m k : Type*} [Fintype m] [Fintype k] (M : Matrix m k ℂ) :
    (Mᴴ * M).trace.re = ∑ a, ∑ x, ‖M x a‖ ^ 2 := by
  simp only [trace, diag, mul_apply, conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun x _ => ?_
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

theorem rvC_gram_trace_re_nonneg {m k : Type*} [Fintype m] [Fintype k] (M : Matrix m k ℂ) :
    0 ≤ (Mᴴ * M).trace.re := by
  rw [rvC_gram_trace_re]; positivity

theorem rvC_leadFrame_apply (b e : ℝ) (W r : ℕ) (ω : GrowthPath W) (x : FullSite W r)
    (a : Fin 2 × Fin W) : rvLeadFrame b e W r ω x a = fullInverse b e W r ω x (Sum.inr a) := by
  simp [rvLeadFrame, mul_apply, leadInclusion, Fintype.sum_sum_type]

/-- `U*U = 𝒰*𝒰 + ℝ*ℝ`. -/
theorem rvC_leadFrame_gram (b e : ℝ) (W r : ℕ) (ω : GrowthPath W) :
    (rvLeadFrame b e W r ω)ᴴ * rvLeadFrame b e W r ω =
      (boundaryToInterior b e W r ω)ᴴ * boundaryToInterior b e W r ω +
        (boundaryResolvent b e W r ω)ᴴ * boundaryResolvent b e W r ω := by
  ext a c
  simp only [mul_apply, conjTranspose_apply, Matrix.add_apply, Fintype.sum_sum_type,
    rvC_leadFrame_apply, boundaryToInterior, boundaryResolvent, toBlocks₁₂, toBlocks₂₂, of_apply]

/-- `Tr A = W⁻²(Tr 𝒰*𝒰 + Tr ℝ*ℝ)`. -/
theorem rvC_leadClock_trace (b e : ℝ) (W r : ℕ) (ω : GrowthPath W) :
    (rvLeadClock b e W r ω).trace.re = ((W : ℝ) ^ 2)⁻¹ *
      (((boundaryToInterior b e W r ω)ᴴ * boundaryToInterior b e W r ω).trace.re +
        ((boundaryResolvent b e W r ω)ᴴ * boundaryResolvent b e W r ω).trace.re) := by
  rw [rvLeadClock, trace_smul, rvC_leadFrame_gram, trace_add, smul_eq_mul, Complex.re_ofReal_mul,
    Complex.add_re]

/-- **Port clock**: `Tr ℝ*ℝ ≤ 2W/η²` for Hermitian blocks. -/
theorem rvC_port_trace_le {b e : ℝ} (hη : 0 < (boundaryZ b e).im) {r : ℕ}
    {ω : GrowthPath W} (hH : ∀ k, (ω.1 k).IsHermitian) :
    ((boundaryResolvent b e W r ω)ᴴ * boundaryResolvent b e W r ω).trace.re ≤
      2 * W / (boundaryZ b e).im ^ 2 := by
  classical
  rw [rvC_gram_trace_re]
  have hcol : ∀ a : Fin 2 × Fin W, ∑ x, ‖boundaryResolvent b e W r ω x a‖ ^ 2 ≤
      1 / (boundaryZ b e).im ^ 2 := by
    intro a
    have h := portLeadMass_le (r := r) hη hH (Pi.single a 1)
    rw [portLeadMass_eq] at h
    have h1 : vecNormSq (Pi.single a (1 : ℂ)) = 1 := by
      rw [vecNormSq, Finset.sum_eq_single a]
      · simp
      · intro x _ hx; simp [hx]
      · simp
    have h2 : vecNormSq (boundaryResolvent b e W r ω *ᵥ Pi.single a 1) =
        ∑ x, ‖boundaryResolvent b e W r ω x a‖ ^ 2 := by
      rw [vecNormSq]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [mulVec_single_one]; rfl
    rw [h1, h2] at h
    exact h
  calc ∑ a, ∑ x, ‖boundaryResolvent b e W r ω x a‖ ^ 2
      ≤ ∑ _a : Fin 2 × Fin W, 1 / (boundaryZ b e).im ^ 2 := Finset.sum_le_sum fun a _ => hcol a
    _ = 2 * W / (boundaryZ b e).im ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        Fintype.card_fin, nsmul_eq_mul]
      push_cast; ring

/-!
### Elementary inequalities
-/

/-- `(1 + √g)²X² ≤ 1 + 16F⁴ + 16K⁴ + g²` for `X = a + c`, `0 ≤ a ≤ F`, `0 ≤ c ≤ K`. -/
theorem rvC_pointwise {X g a c F K : ℝ} (hX : X = a + c) (ha : 0 ≤ a) (haF : a ≤ F)
    (hc : 0 ≤ c) (hcK : c ≤ K) :
    (1 + Real.sqrt g) ^ 2 * X ^ 2 ≤ 1 + 16 * F ^ 4 + 16 * K ^ 4 + g ^ 2 := by
  have h2 : (a + c) ^ 2 ≤ 2 * (a ^ 2 + c ^ 2) := by nlinarith [sq_nonneg (a - c)]
  have h4 : (a + c) ^ 4 ≤ 8 * (a ^ 4 + c ^ 4) := by
    have hs : 0 ≤ (a + c) ^ 2 := sq_nonneg _
    have : (a + c) ^ 4 ≤ (2 * (a ^ 2 + c ^ 2)) ^ 2 := by
      rw [show (a + c) ^ 4 = ((a + c) ^ 2) ^ 2 by ring]
      exact pow_le_pow_left₀ hs h2 2
    nlinarith [sq_nonneg (a ^ 2 - c ^ 2)]
  have ha4 : a ^ 4 ≤ F ^ 4 := pow_le_pow_left₀ ha haF 4
  have hc4 : c ^ 4 ≤ K ^ 4 := pow_le_pow_left₀ hc hcK 4
  have hX4 : X ^ 4 ≤ 8 * F ^ 4 + 8 * K ^ 4 := by rw [hX]; linarith
  have hX2 : 2 * X ^ 2 ≤ 1 + X ^ 4 := by nlinarith [sq_nonneg (X ^ 2 - 1)]
  have hmain : (1 + Real.sqrt g) ^ 2 * X ^ 2 ≤ 1 + 2 * X ^ 4 + g ^ 2 := by
    rcases le_or_gt 0 g with hg | hg
    · have hs := Real.sq_sqrt hg
      have hs0 := Real.sqrt_nonneg g
      have h1 : (1 + Real.sqrt g) ^ 2 ≤ 2 + 2 * g := by nlinarith [sq_nonneg (1 - Real.sqrt g)]
      have hXs : 0 ≤ X ^ 2 := sq_nonneg X
      nlinarith [sq_nonneg (X ^ 2 - g), mul_le_mul_of_nonneg_right h1 hXs]
    · rw [Real.sqrt_eq_zero_of_nonpos hg.le, add_zero, one_pow, one_mul]
      nlinarith [sq_nonneg g, sq_nonneg X, pow_two_nonneg (X ^ 2)]
  linarith

/-- `‖f‖_4 ≤ B` gives `∫⁻ ‖f‖ₑ⁴ ≤ B⁴`. -/
theorem rvC_lintegral_pow_four_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℂ} (hf : AEStronglyMeasurable f μ) {B : ℝ}
    (h : eLpNorm f (ENNReal.ofReal 4) μ ≤ ENNReal.ofReal B) :
    ∫⁻ x, ‖f x‖ₑ ^ (4 : ℕ) ∂μ ≤ ENNReal.ofReal B ^ (4 : ℕ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp) (by simp) hf] at h
  have h4 : (ENNReal.ofReal 4).toReal = ((4 : ℕ) : ℝ) := by norm_num
  rw [h4, one_div, ENNReal.rpow_inv_le_iff (by norm_num)] at h
  simpa only [ENNReal.rpow_natCast] using h

/-!
### The multiplier moment
-/

/-- **The multiplier moment** of the response variance theorem: the multiplier costs
`E[(Tr A)²(1+g)]`, bounded by the full-clock fourth moment and the positive-time conductance
second moment. Under `growthPathLaw W b`, for fixed `0 < b < 1/2`, bulk margin `κ > 0`, time floor
`ε > 0` and horizon `T`, there are `C, W₀` with `E[(1 + √g)²(Tr A)²] ≤ C` for all `W ≥ W₀`,
`e ∈ bulkInterval κ`, `εW ≤ r ≤ TW`. Inputs: `FullSourceMomentsEnergyUniformContract` (fourth
moment of the interior clock, `E' = E`) and `TransmissionLengthUniformContract` (second
conductance moment), and `ConditionalBlockGUECount` (a.s. invertibility of `H_path - e`, giving
`g = g_r` a.s.). -/
theorem rvClockConductanceMoment_of_contracts (hUnifMom : FullSourceMomentsEnergyUniformContract)
    (hLen : TransmissionLengthUniformContract) (hCount : ConditionalBlockGUECount) :
    RvClockConductanceMoment := by
  intro b hb0 hb1 κ ε T hκ hε
  obtain ⟨Cc, Wc, hc⟩ := hUnifMom.clock b hb0 hb1 κ 0 T 4 hκ (by norm_num)
  obtain ⟨Cg, hg⟩ := hLen.conductance b hb0 hb1 κ ε 2 hκ hε (by norm_num)
  obtain ⟨Wg, hg⟩ := hg T
  set η₀ := PhaseFractional.etaMin b κ
  have hη₀ : 0 < η₀ := PhaseFractional.etaMin_pos (by linarith) hκ
  set K : ℝ := 2 / η₀ ^ 2
  have hK : 0 ≤ K := by positivity
  set C' := max Cc 0
  have hC' : 0 ≤ C' := le_max_right _ _
  refine ⟨1 + 16 * K ^ 4 + 16 * (C' * (T + 1)) ^ 4 + max Cg 0, max (max Wc Wg) 1, ?_⟩
  intro W hW e he r hr1 hr2
  have hWc : Wc ≤ W := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hW
  have hWg : Wg ≤ W := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hW
  have hW1 : 1 ≤ W := le_trans (le_max_right _ _) hW
  have hWpos : 0 < W := hW1
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hWr0 : (0 : ℝ) < W := by linarith
  have he1 : -2 < e := by have := he.1; linarith
  have he2 : e < 2 := by have := he.2; linarith
  have hη : η₀ ≤ (boundaryZ b e).im := PhaseFractional.boundaryZ_im_ge (by linarith) hκ he
  have hηpos : 0 < (boundaryZ b e).im := hη₀.trans_le hη
  have hP := passDeriv_isProbabilityMeasure_growthPathLaw W b
  -- the interior clock
  set f : GrowthPath W → ℂ := fun ω => (W : ℂ)⁻¹ *
    ((boundaryToInterior b e W r ω)ᴴ * boundaryToInterior b e W r ω).trace
  have hU : Measurable (fun ω => boundaryToInterior b e W r ω) := by
    have hG := measurable_fullInverse_of b W r (measurable_const (a := e)) measurable_id
    refine Measurable.of_eval fun x => Measurable.of_eval fun y => ?_
    change Measurable fun ω => fullInverse b e W r ω (Sum.inl x) (Sum.inr y)
    exact (measurable_pi_apply (Sum.inr y)).comp ((measurable_pi_apply (Sum.inl x)).comp hG)
  have hf : Measurable f := measurable_const.mul
    ((continuous_id.matrix_conjTranspose.matrix_mul continuous_id).matrix_trace.measurable.comp hU)
  have hclock := hc W hWc e he e (by simp [IsNearEnergy]) r hr2
  have hclock' : eLpNorm f (ENNReal.ofReal 4) (growthPathLaw W b) ≤
      ENNReal.ofReal (C' * ((r : ℝ) + 1)) :=
    hclock.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
  have hF := rvC_lintegral_pow_four_le hf.aestronglyMeasurable hclock'
  -- the conductance
  have hG2 : ∫⁻ ω, ‖pathConductance b e W r ω‖ₑ ^ (2 : ℕ) ∂growthPathLaw W b ≤
      ENNReal.ofReal Cg := by
    have := hg W hWg e he r hr1 hr2
    simpa only [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast] using this
  -- pointwise bound
  set c₀ : ℝ≥0∞ := ENNReal.ofReal (1 + 16 * K ^ 4)
  set c₁ : ℝ≥0∞ := ENNReal.ofReal (16 * ((W : ℝ)⁻¹) ^ 4)
  have hpt : ∀ᵐ ω ∂growthPathLaw W b,
      ENNReal.ofReal ((1 + Real.sqrt (rvConductance b e W r ω)) ^ 2 *
          (rvLeadClock b e W r ω).trace.re ^ 2) ≤
        c₀ + (c₁ * ‖f ω‖ₑ ^ (4 : ℕ) + ‖pathConductance b e W r ω‖ₑ ^ (2 : ℕ)) := by
    filter_upwards [rvC_ae_conductance_eq hCount hb1 he1 he2 hWpos r,
      ae_growthPath_isHermitian W b] with ω hgω hH
    set t₁ := ((boundaryToInterior b e W r ω)ᴴ * boundaryToInterior b e W r ω).trace.re
    set t₂ := ((boundaryResolvent b e W r ω)ᴴ * boundaryResolvent b e W r ω).trace.re
    have ht₁ : 0 ≤ t₁ := rvC_gram_trace_re_nonneg _
    have ht₂ : 0 ≤ t₂ := rvC_gram_trace_re_nonneg _
    have ht₂' : t₂ ≤ 2 * W / (boundaryZ b e).im ^ 2 := rvC_port_trace_le hηpos hH
    have hnf : ‖f ω‖ = (W : ℝ)⁻¹ *
        ‖((boundaryToInterior b e W r ω)ᴴ * boundaryToInterior b e W r ω).trace‖ := by
      simp only [f, norm_mul, norm_inv, Complex.norm_natCast]
    have ht₁' : t₁ ≤ ‖((boundaryToInterior b e W r ω)ᴴ *
        boundaryToInterior b e W r ω).trace‖ := Complex.re_le_norm _
    have hWi : 0 < (W : ℝ)⁻¹ := inv_pos.2 hWr0
    have haF : ((W : ℝ) ^ 2)⁻¹ * t₁ ≤ (W : ℝ)⁻¹ * ‖f ω‖ := by
      rw [hnf, ← mul_assoc, ← sq, inv_pow]
      exact mul_le_mul_of_nonneg_left ht₁' (by positivity)
    have hcK : ((W : ℝ) ^ 2)⁻¹ * t₂ ≤ K := by
      have h1 : 2 * (W : ℝ) / (boundaryZ b e).im ^ 2 ≤ 2 * W / η₀ ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_left₀ hη₀.le hη 2)
      have h2 : ((W : ℝ) ^ 2)⁻¹ * (2 * W / η₀ ^ 2) = K * (W : ℝ)⁻¹ := by
        simp only [K]; field_simp
      have h3 : K * (W : ℝ)⁻¹ ≤ K := mul_le_of_le_one_right hK (inv_le_one_of_one_le₀ hWr)
      calc ((W : ℝ) ^ 2)⁻¹ * t₂ ≤ ((W : ℝ) ^ 2)⁻¹ * (2 * W / η₀ ^ 2) :=
            mul_le_mul_of_nonneg_left (ht₂'.trans h1) (by positivity)
        _ = K * (W : ℝ)⁻¹ := h2
        _ ≤ K := h3
    have hreal := rvC_pointwise (X := (rvLeadClock b e W r ω).trace.re)
      (g := rvConductance b e W r ω)
      (a := ((W : ℝ) ^ 2)⁻¹ * t₁) (c := ((W : ℝ) ^ 2)⁻¹ * t₂)
      (by rw [rvC_leadClock_trace, mul_add]) (by positivity) haF (by positivity) hcK
    rw [hgω] at hreal ⊢
    calc ENNReal.ofReal ((1 + Real.sqrt (pathConductance b e W r ω)) ^ 2 *
          (rvLeadClock b e W r ω).trace.re ^ 2)
        ≤ ENNReal.ofReal (1 + 16 * K ^ 4 + 16 * ((W : ℝ)⁻¹) ^ 4 * ‖f ω‖ ^ 4 +
            ‖pathConductance b e W r ω‖ ^ 2) := by
          apply ENNReal.ofReal_le_ofReal
          rw [Real.norm_eq_abs, sq_abs]
          nlinarith [hreal]
      _ = c₀ + (c₁ * ‖f ω‖ₑ ^ (4 : ℕ) + ‖pathConductance b e W r ω‖ₑ ^ (2 : ℕ)) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_pow (norm_nonneg _),
            ofReal_norm, ofReal_norm, add_assoc]
  -- integrate
  have hm : Measurable (fun ω => c₁ * ‖f ω‖ₑ ^ (4 : ℕ)) :=
    (hf.enorm.pow_const 4).const_mul _
  have hB : 0 ≤ C' * ((r : ℝ) + 1) := by positivity
  have hrT : ((r : ℝ) + 1) / W ≤ T + 1 := by
    rw [div_le_iff₀ hWr0]; nlinarith
  have hfin : 16 * ((W : ℝ)⁻¹) ^ 4 * (C' * ((r : ℝ) + 1)) ^ 4 ≤ 16 * (C' * (T + 1)) ^ 4 := by
    have h1 : 0 ≤ C' * (((r : ℝ) + 1) / W) := by positivity
    have h2 : C' * (((r : ℝ) + 1) / W) ≤ C' * (T + 1) := mul_le_mul_of_nonneg_left hrT hC'
    have h3 := pow_le_pow_left₀ h1 h2 4
    have : ((W : ℝ)⁻¹) ^ 4 * (C' * ((r : ℝ) + 1)) ^ 4 = (C' * (((r : ℝ) + 1) / W)) ^ 4 := by
      rw [← mul_pow]; congr 1; field_simp
    nlinarith
  calc ∫⁻ ω, ENNReal.ofReal ((1 + Real.sqrt (rvConductance b e W r ω)) ^ 2 *
          (rvLeadClock b e W r ω).trace.re ^ 2) ∂growthPathLaw W b
      ≤ ∫⁻ ω, (c₀ + (c₁ * ‖f ω‖ₑ ^ (4 : ℕ) + ‖pathConductance b e W r ω‖ₑ ^ (2 : ℕ)))
          ∂growthPathLaw W b := lintegral_mono_ae hpt
    _ = c₀ + (c₁ * ∫⁻ ω, ‖f ω‖ₑ ^ (4 : ℕ) ∂growthPathLaw W b +
          ∫⁻ ω, ‖pathConductance b e W r ω‖ₑ ^ (2 : ℕ) ∂growthPathLaw W b) := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_add_left hm, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ c₀ + (c₁ * ENNReal.ofReal (C' * ((r : ℝ) + 1)) ^ (4 : ℕ) + ENNReal.ofReal Cg) := by
        gcongr
    _ ≤ ENNReal.ofReal (1 + 16 * K ^ 4 + 16 * (C' * (T + 1)) ^ 4 + max Cg 0) := by
        rw [← ENNReal.ofReal_pow hB, ← ENNReal.ofReal_mul (by positivity)]
        have hg0 : ENNReal.ofReal Cg ≤ ENNReal.ofReal (max Cg 0) :=
          ENNReal.ofReal_le_ofReal (le_max_left _ _)
        calc c₀ + (ENNReal.ofReal (16 * ((W : ℝ)⁻¹) ^ 4 * (C' * ((r : ℝ) + 1)) ^ 4) +
              ENNReal.ofReal Cg)
            ≤ c₀ + (ENNReal.ofReal (16 * (C' * (T + 1)) ^ 4) + ENNReal.ofReal (max Cg 0)) := by
              gcongr
          _ = ENNReal.ofReal (1 + 16 * K ^ 4 + 16 * (C' * (T + 1)) ^ 4 + max Cg 0) := by
              rw [← ENNReal.ofReal_add (by positivity) (le_max_right _ _),
                ← ENNReal.ofReal_add (by positivity) (by positivity)]
              congr 1; ring

end BlockBand.Endpoints
