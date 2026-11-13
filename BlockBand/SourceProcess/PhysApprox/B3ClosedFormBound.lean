module

public import BlockBand.SourceProcess.PhysApprox.B3ClosedFormStep
public import BlockBand.SourceProcess.PhysApprox.B3ClosedFormPhase

/-!
# Frame bounds, passivity and almost-sure invertibility of the closed step

* `norm_closedNearU_le`, `norm_closedNearV_le`: `‖u_k‖² ≤ (M_cl)_kk ≤ Re Tr M_cl` and
  `‖v_l‖² ≤ (M_cl)_ll ≤ Re Tr M_cl` on `|z| = 1` (the second from the lossless-closing
  inequality `posSemidef_closed_gram_sub`; no bound on the closed port scattering is used);
* `passive_closedNearX`: `X_cl` is passive when `R_cl` is invertible;
* `closedNearR_eq_corner`, `isUnit_closedR0`: `R_cl = R₀ + zL(1 - zN)⁻¹R_t` with `R₀ = ι*ℝι`
  the unclosed near resolvent, invertible;
* the invertibilities used by `closedK_step` hold `closedLaw`-a.e.; this is proved in a sibling
  module (`ae_closedPhase_good`, `ae_closedPath_good`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosingAux BlockBand.SourceProcess.FullSourceStops
open BlockBand.SourceProcess.ComplexSourceLaw
open BlockBand.Transmission.Bridge BlockBand.Transmission.PassiveLayer
open BlockBand.SourceProcess.PhysApprox.ClosedForm
open scoped ComplexOrder

variable {W np K : ℕ}

/-!
## Squared norms
-/

theorem re_star_dot_self {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    (star v ⬝ᵥ v).re = ∑ i, ‖v i‖ ^ 2 := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum, Complex.star_def, Complex.conj_mul']
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

theorem re_dot_gram {α β : Type*} [Fintype α] [Fintype β] (A : Matrix α β ℂ) (x : β → ℂ) :
    (star x ⬝ᵥ ((Aᴴ * A) *ᵥ x)).re = ∑ i, ‖(A *ᵥ x) i‖ ^ 2 := by
  rw [← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec, re_star_dot_self]

theorem sum_sq_nearSel_le (w : Fin 2 × Fin W → ℂ) :
    ∑ x, ‖(nearSel W *ᵥ w) x‖ ^ 2 ≤ ∑ a, ‖w a‖ ^ 2 := by
  have e : ∀ x, (nearSel W *ᵥ w) x = w (0, x) := fun x => by
    simp [nearSel, mulVec, dotProduct]
  simp only [e, Fintype.sum_prod_type, Fin.sum_univ_two]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem col_sq_le_trace {ι c : Type*} [Fintype ι] [Fintype c] (F : Matrix ι c ℂ) (k : c) :
    ∑ a, ‖F a k‖ ^ 2 ≤ ((Fᴴ * F).trace).re := by
  have e : ((Fᴴ * F).trace).re = ∑ k', ∑ a, ‖F a k'‖ ^ 2 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, conjTranspose_apply, Complex.re_sum,
      Complex.star_def, Complex.conj_mul']
    refine Finset.sum_congr rfl fun k' _ => Finset.sum_congr rfl fun a _ => ?_
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  rw [e]
  exact Finset.single_le_sum (f := fun k' => ∑ a, ‖F a k'‖ ^ 2)
    (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ k)

theorem phase_mul_star (θ : ℝ) : phase θ * star (phase θ) = 1 := by
  rw [phase, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  simp

/-!
## The closed frame columns and the frame bounds
-/

theorem closedFrame_col (b E s h : ℝ) (τ m : Fin np → ℝ) (i : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (k : Fin np)
    (y : ProbedPath W np × ℝ) :
    (fun a => b3ClosedFrameAt b E s h τ m W i Vs y a (Sum.inr k)) =
      (physClosingMapAt b E s h W i y.1.1 (phase y.2))ᴴ *ᵥ probeCol b E τ m W i k y.1 := by
  funext a
  simp [b3ClosedFrameAt, b3OpenFrameAt, Matrix.mul_apply, mulVec, dotProduct, probeCol]

theorem sum_sq_closedCol_le (b E s h : ℝ) (τ m : Fin np → ℝ) (i : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (k : Fin np)
    (y : ProbedPath W np × ℝ) :
    ∑ a, ‖((physClosingMapAt b E s h W i y.1.1 (phase y.2))ᴴ *ᵥ probeCol b E τ m W i k y.1) a‖ ^ 2
      ≤ ((b3ClosedGramAt b E s h τ m W i Vs y).1.trace).re := by
  rw [← closedFrame_col b E s h τ m i Vs k y]
  exact col_sq_le_trace _ (Sum.inr k)

/-- **The left frame bound** `‖u_k‖² ≤ Re Tr M_cl`. -/
theorem norm_closedNearU_le (b E s h : ℝ) (τ m : Fin np → ℝ) (i : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (k : Fin np) {R : ℝ}
    (y : ProbedPath W np × ℝ) (hy : ((b3ClosedGramAt b E s h τ m W i Vs y).1.trace).re < R) :
    vecNorm (closedNearU b E s h τ m W i k y) ≤ Real.sqrt R :=
  Real.sqrt_le_sqrt ((sum_sq_nearSel_le _).trans ((sum_sq_closedCol_le b E s h τ m i Vs k y).trans
    hy.le))

/-- **The right frame bound** `‖v_l‖² ≤ Re Tr M_cl` on `|z| = 1` (lossless closing). -/
theorem norm_closedNearV_le (b E s h : ℝ) (hh : h ^ 2 < 1) (τ m : Fin np → ℝ) (i : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (l : Fin np) {R : ℝ}
    (y : ProbedPath W np × ℝ)
    (hS : scatteringMatrix b E W i y.1.1 * (scatteringMatrix b E W i y.1.1)ᴴ = 1)
    (hU : IsUnit (1 - phase y.2 • closingN (scatteringMatrix b E W i y.1.1)
      (farEmbed (omittedProj b E h W (closeLen s W) y.1.1))
      (farEmbed (closingPairing b E h W (closeLen s W) y.1.1))).det)
    (hy : ((b3ClosedGramAt b E s h τ m W i Vs y).1.trace).re < R) :
    vecNorm (closedNearV b E s h τ m W i l y) ≤ Real.sqrt R := by
  set S := scatteringMatrix b E W i y.1.1
  set A := farEmbed (omittedProj b E h W (closeLen s W) y.1.1)
  set Pi := farEmbed (closingPairing b E h W (closeLen s W) y.1.1)
  set z := phase y.2
  set x := probeCol b E τ m W i l y.1
  have hA2 : A * A = A := by rw [farEmbed_mul, omittedProj_mul_self]
  have hAH : Aᴴ = A := by rw [farEmbed_conjTranspose, omittedProj_conjTranspose]
  have hAPi : A * Pi = Pi := by rw [farEmbed_mul, omittedProj_mul_closingPairing]
  have hPi : Pi * Piᴴ = A := by
    rw [farEmbed_conjTranspose, farEmbed_mul, closingPairing_mul_conj b E h hh]
  have hD := posSemidef_closed_gram_sub hA2 hAH hAPi hPi hS (phase_mul_star y.2) hU
    (farEmbed_mul_nearSel_conj _) nearSel_mul_conjTranspose
  have h0 := hD.dotProduct_mulVec_nonneg x
  have h0' : 0 ≤ (star x ⬝ᵥ ((closingMap S A Pi z * (closingMap S A Pi z)ᴴ -
      (nearSel W * (S * (1 + closingZ S A Pi z)))ᴴ *
        (nearSel W * (S * (1 + closingZ S A Pi z)))) *ᵥ x)).re := by
    have := (Complex.le_def.1 h0).1
    simpa using this
  rw [sub_mulVec, dotProduct_sub, Complex.sub_re, re_dot_gram,
    ← conjTranspose_conjTranspose (closingMap S A Pi z), conjTranspose_conjTranspose
      ((closingMap S A Pi z)ᴴ), re_dot_gram, sub_nonneg] at h0'
  have hv : closedNearV b E s h τ m W i l y = (nearSel W * (S * (1 + closingZ S A Pi z))) *ᵥ x := by
    simp only [closedNearV, physClosingZAt, ← mulVec_mulVec]
    rfl
  refine Real.sqrt_le_sqrt ?_
  rw [hv]
  refine h0'.trans ((sum_sq_closedCol_le b E s h τ m i Vs l y).trans hy.le)

/-!
## The closed near resolvent and passivity
-/

theorem closedNearR_eq_corner (b E s h : ℝ) (j : ℕ) (ω : GrowthPath W) (z : ℂ) :
    closedNearR b E s h W j ω z =
      nearSel W * boundaryResolvent b E W j ω *
          (1 - farEmbed (omittedProj b E h W (closeLen s W) ω)) * (nearSel W)ᴴ +
        z • ((nearSel W * boundaryResolvent b E W j ω) *
          (1 - z • closingN (scatteringMatrix b E W j ω)
            (farEmbed (omittedProj b E h W (closeLen s W) ω))
            (farEmbed (closingPairing b E h W (closeLen s W) ω)))⁻¹ *
          (closingT (scatteringMatrix b E W j ω)
            (farEmbed (omittedProj b E h W (closeLen s W) ω))
            (farEmbed (closingPairing b E h W (closeLen s W) ω)) * (nearSel W)ᴴ)) := by
  simp only [closedNearR, physClosingMapAt, closingMap, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

/-- The unclosed near resolvent `R₀ = ι*ℝ(1 - A)ι = (z_∂ - X_j)⁻¹` is invertible. -/
theorem isUnit_closedR0 (b E h s : ℝ) (j : ℕ) (ω : GrowthPath W)
    (hA : ∀ k, (ω.1 k).IsHermitian) (hη : 0 < (boundaryZ b E).im)
    (hF : IsUnit (pathMatrix (pathAt W j ω) - (E : ℂ) • 1)) :
    IsUnit (nearSel W * boundaryResolvent b E W j ω *
      (1 - farEmbed (omittedProj b E h W (closeLen s W) ω)) * (nearSel W)ᴴ).det := by
  have hz : boundaryZ b E ≠ 0 := fun h0 => by rw [h0] at hη; simp at hη
  have e1 : nearSel W * boundaryResolvent b E W j ω *
      (1 - farEmbed (omittedProj b E h W (closeLen s W) ω)) * (nearSel W)ᴴ =
        nearSel W * boundaryResolvent b E W j ω * (nearSel W)ᴴ := by
    rw [Matrix.mul_assoc _ (1 - _), Matrix.sub_mul, Matrix.one_mul, farEmbed_mul_nearSel_conj,
      sub_zero]
  have h2 := (RawTag.boundary_eqs b E j ω hA hη hF).2
  obtain ⟨-, -, -, hCU⟩ := old_facts_at b E j ω hA hη hF
  rw [Matrix.mul_assoc, hCU, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub,
    nearSel_mul_conjTranspose, Matrix.smul_mul, Matrix.mul_smul, sub_right_inj] at h2
  have h3 : nearSel W * (boundaryResolvent b E W j ω * (nearSel W)ᴴ) =
      passiveResolvent b E (pathX b E W j ω) := by
    have := congrArg ((boundaryZ b E)⁻¹ • ·) h2
    simpa only [smul_smul, inv_mul_cancel₀ hz, one_smul] using this
  rw [e1, Matrix.mul_assoc, h3, passiveResolvent]
  refine isUnit_nonsing_inv_det _ ?_
  exact (isUnit_iff_isUnit_det _).mp (BlockBand.SourceProcess.TagBirth.isUnit_pencil hη
    (pathNearSchur_passive (κ := fun _ => 0) ⟨hA, fun _ => le_rfl, hη⟩ j))

/-- **`X_cl` is passive** on `|z| = 1` when `R_cl` is invertible. -/
theorem passive_closedNearX (b E s h : ℝ) (hh : h ^ 2 < 1) (j : ℕ) (ω : GrowthPath W) (θ : ℝ)
    (hη : 0 < (boundaryZ b E).im)
    (hS : scatteringMatrix b E W j ω * (scatteringMatrix b E W j ω)ᴴ = 1)
    (hU : IsUnit (1 - phase θ • closingN (scatteringMatrix b E W j ω)
      (farEmbed (omittedProj b E h W (closeLen s W) ω))
      (farEmbed (closingPairing b E h W (closeLen s W) ω))).det)
    (hR : IsUnit (closedNearR b E s h W j ω (phase θ)).det) :
    (passiveY (closedNearX b E s h W j ω (phase θ))).PosSemidef := by
  set S := scatteringMatrix b E W j ω
  set A := farEmbed (omittedProj b E h W (closeLen s W) ω)
  set Pi := farEmbed (closingPairing b E h W (closeLen s W) ω)
  set z := phase θ
  set ns := nearSel W
  set Ccl := closingMap S A Pi z
  set M := ns * (S * (1 + closingZ S A Pi z))
  have hA2 : A * A = A := by rw [farEmbed_mul, omittedProj_mul_self]
  have hAH : Aᴴ = A := by rw [farEmbed_conjTranspose, omittedProj_conjTranspose]
  have hAPi : A * Pi = Pi := by rw [farEmbed_mul, omittedProj_mul_closingPairing]
  have hPi : Pi * Piᴴ = A := by
    rw [farEmbed_conjTranspose, farEmbed_mul, closingPairing_mul_conj b E h hh]
  have hnn : ns * nsᴴ = 1 := nearSel_mul_conjTranspose
  have hD := posSemidef_closed_gram_sub hA2 hAH hAPi hPi hS (phase_mul_star θ) hU
    (farEmbed_mul_nearSel_conj _) hnn
  have hnC : ns * Ccl = ns :=
    ns_mul_closingMap (nearSel_mul_farEmbed _) (nearSel_mul_farEmbed _) hU
  have hAns : A * nsᴴ = 0 := farEmbed_mul_nearSel_conj _
  have hCns : Ccl * nsᴴ = (1 + closingZ S A Pi z) * nsᴴ := by
    simp only [Ccl, closingMap, closingT, closingZ, Matrix.add_mul, Matrix.sub_mul,
      Matrix.one_mul, hAns, sub_zero, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_zero]
  set c := boundaryZ b E - star (boundaryZ b E)
  have hRe : closedNearR b E s h W j ω z =
      ns * (boundaryResolvent b E W j ω * (Ccl * nsᴴ)) := by
    rw [closedNearR, Matrix.mul_assoc, Matrix.mul_assoc]; rfl
  have hr : 1 - c • closedNearR b E s h W j ω z = M * nsᴴ := by
    have hcS : S = 1 - c • boundaryResolvent b E W j ω := by
      simp only [S, scatteringMatrix, c, c_eq_sub_star]
    have e1 : M * nsᴴ = ns * (S * (Ccl * nsᴴ)) := by
      simp only [M, Matrix.mul_assoc]; rw [hCns]
    rw [e1, hcS, hRe, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.smul_mul,
      Matrix.mul_smul, ← Matrix.mul_assoc ns Ccl, hnC, hnn]
  have hCC : ns * (Ccl * Cclᴴ) * nsᴴ = 1 := by
    have e : ns * (Ccl * Cclᴴ) * nsᴴ = (ns * Ccl) * (ns * Ccl)ᴴ := by
      rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    rw [e, hnC, hnn]
  have hpsd : (1 - (1 - c • closedNearR b E s h W j ω z)ᴴ *
      (1 - c • closedNearR b E s h W j ω z)).PosSemidef := by
    rw [hr]
    have e : 1 - (M * nsᴴ)ᴴ * (M * nsᴴ) =
        nsᴴᴴ * (Ccl * Cclᴴ - Mᴴ * M) * nsᴴ := by
      rw [conjTranspose_conjTranspose, Matrix.mul_sub, Matrix.sub_mul, hCC, conjTranspose_mul,
        conjTranspose_conjTranspose]
      simp only [Matrix.mul_assoc]
    rw [e]
    exact hD.conjTranspose_mul_mul_same _
  exact passiveY_of_contraction hη (c_eq_sub_star b E).symm hR hpsd

end BlockBand.SourceProcess.PhysApprox.B3

