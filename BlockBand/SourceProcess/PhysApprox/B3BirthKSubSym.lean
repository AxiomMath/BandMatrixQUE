module

public import BlockBand.SourceProcess.PhysApprox.B3BirthKSubRes
public import BlockBand.SourceProcess.PhysApprox.ConjSym
public import BlockBand.Transmission.Bridge.Passive
public import BlockBand.Transmission.Bridge.Scattering

/-!
# The output resolvent estimate from the input one, by conjugation symmetry

Measure `growthPathLaw W b`, conjugation invariant (`lintegral_conjPath`). For Hermitian
blocks (almost surely), with `ω̄ = conjPath ω`, every phase `θ` and every length:

* `closingPairing_conjPath`: `Π(ω̄) = Πᵀ` (`g(1 − SSᴴ)S = Sg(1 − SᴴS)` by interpolation);
* `transmissionProcess_conjPath`: the homogeneous transmission trace measure is conjugation
  invariant (`X_r(ω̄) = X_r(ω)ᵀ`, `T(Xᵀ) = (1 − SSᴴ)ᵀ`, `charpoly(1 − SSᴴ) = charpoly(1 − SᴴS)`), so
  the physical cap event is invariant (`mem_physCapEventC_conjPath`);
* **`resIn_conjPath_trace`** (pathwise, no invertibility hypothesis):
  `Re Tr(M_in(ω̄)ᴴM_in(ω̄)Y(ω̄)) = Re Tr(M_out(ω)ᴴM_out(ω)Y(ω))`, with `M_in = R(θ)ᴴA`,
  `M_out = R(θ)Π𝕊`. Indeed `N(ω̄) = (O𝕊Π)ᵀ`, `O = ΠᴴΠ`, and by push-through
  (`(1 − BC)⁻¹B = B(1 − CB)⁻¹`, valid with Lean's inverse by Sylvester's determinant identity)
  both `(1 − zO𝕊Π)⁻¹O𝕊` and `(1 − zΠ𝕊A)⁻¹Π𝕊` equal `X𝕊(1 − zΠ𝕊)⁻¹` with `X = O`, resp. `Π`,
  and `ΠᴴΠ = OᴴO = O`.

Hence **`birthKResOutPath_of_in : BirthKResInPath → BirthKResOutPath`** (and its converse):
the two path-only resolvent estimates are the same statement in law, so `BirthKResInPath`
suffices. **`complexBirthKClosing_of_far_resIn`**: `ComplexBirthKClosing` from `BirthKFarIn`,
`BirthKFarOut` and `BirthKResInPath`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.BirthKSub

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Layers
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosingLeak BlockBand.SourceProcess.ComplexSourceLaw
open BlockBand.Transmission.Bridge
open scoped NNReal ENNReal ComplexConjugate

/-!
## Algebra
-/

section Alg

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Push-through** with Lean's inverse: `(1 − BC)⁻¹B = B(1 − CB)⁻¹`. -/
theorem inv_one_sub_mul_comm (B C : Matrix n n ℂ) : (1 - B * C)⁻¹ * B = B * (1 - C * B)⁻¹ := by
  by_cases h : IsUnit (1 - B * C).det
  · have h' : IsUnit (1 - C * B).det := by rwa [det_one_sub_mul_comm]
    have e : B * (1 - C * B) = (1 - B * C) * B := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
    calc (1 - B * C)⁻¹ * B = (1 - B * C)⁻¹ * B * ((1 - C * B) * (1 - C * B)⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ h', Matrix.mul_one]
      _ = (1 - B * C)⁻¹ * (B * (1 - C * B)) * (1 - C * B)⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = B * (1 - C * B)⁻¹ := by
          rw [e, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h, Matrix.one_mul]
  · have h' : ¬ IsUnit (1 - C * B).det := by rwa [det_one_sub_mul_comm]
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h',
      Matrix.zero_mul, Matrix.mul_zero]

theorem det_scalar_add_mul_comm (c : ℂ) (A B : Matrix n n ℂ) :
    (scalar n c + A * B).det = (scalar n c + B * A).det := by
  by_cases hc : c = 0
  · simp only [hc, map_zero, zero_add]
    exact det_mul_comm A B
  · have hs : scalar n c = c • (1 : Matrix n n ℂ) := by
      ext i j
      simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
    have e : ∀ X Y : Matrix n n ℂ, scalar n c + X * Y = c • (1 + (c⁻¹ • X) * Y) := by
      intro X Y
      rw [hs, smul_add, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hc, one_smul]
    rw [e, e, det_smul, det_smul, det_one_add_mul_comm, Matrix.mul_smul, Matrix.smul_mul]

/-- `charpoly(1 − AB) = charpoly(1 − BA)`. -/
theorem charpoly_one_sub_mul_comm (A B : Matrix n n ℂ) :
    (1 - A * B).charpoly = (1 - B * A).charpoly := by
  refine Polynomial.funext fun t => ?_
  have e : ∀ M : Matrix n n ℂ, scalar n t - (1 - M) = scalar n (t - 1) + M := by
    intro M
    rw [map_sub, map_one]
    abel
  rw [eval_charpoly, eval_charpoly, e, e, det_scalar_add_mul_comm]

end Alg

variable {W : ℕ}

theorem matConj_inv {n : Type*} [Fintype n] [DecidableEq n] (K : Matrix n n ℂ) :
    matConj K⁻¹ = (matConj K)⁻¹ := by
  rw [← conjTranspose_transpose', transpose_nonsing_inv, conjTranspose_nonsing_inv,
    conjTranspose_transpose']

theorem farEmbed_transpose (X : Matrix (Fin W) (Fin W) ℂ) : farEmbed Xᵀ = (farEmbed X)ᵀ := by
  ext x y
  by_cases hx : x.1 = 1 <;> by_cases hy : y.1 = 1 <;> simp [farEmbed, hx, hy]

/-!
## The pairing at the conjugated path
-/

/-- `g(1 − SSᴴ)S = Sg(1 − SᴴS)` for every real `g`. -/
theorem cfc_one_sub_semiconj (g : ℝ → ℝ) (S : Matrix (Fin W) (Fin W) ℂ) :
    cfc g (1 - S * Sᴴ) * S = S * cfc g (1 - Sᴴ * S) := by
  classical
  have hT : IsSelfAdjoint (1 - Sᴴ * S) :=
    (isHermitian_one.sub (isHermitian_conjTranspose_mul_self S)).isSelfAdjoint
  have hT' : IsSelfAdjoint (1 - S * Sᴴ) :=
    (isHermitian_one.sub (isHermitian_mul_conjTranspose_self S)).isSelfAdjoint
  have hfin : (spectrum ℝ (1 - Sᴴ * S) ∪ spectrum ℝ (1 - S * Sᴴ)).Finite :=
    (show (spectrum ℝ (1 - Sᴴ * S)).Finite from Matrix.finite_real_spectrum).union
      (show (spectrum ℝ (1 - S * Sᴴ)).Finite from Matrix.finite_real_spectrum)
  set p : Polynomial ℝ := Lagrange.interpolate hfin.toFinset id g
  have hnode : ∀ t ∈ spectrum ℝ (1 - Sᴴ * S) ∪ spectrum ℝ (1 - S * Sᴴ), p.eval t = g t :=
    fun t ht => Lagrange.eval_interpolate_at_node g (Set.injOn_id _) (hfin.mem_toFinset.2 ht)
  have h1 : cfc g (1 - Sᴴ * S) = Polynomial.aeval (1 - Sᴴ * S) p := by
    rw [← cfc_polynomial p (1 - Sᴴ * S) hT]
    exact cfc_congr fun t ht => (hnode t (Or.inl ht)).symm
  have h2 : cfc g (1 - S * Sᴴ) = Polynomial.aeval (1 - S * Sᴴ) p := by
    rw [← cfc_polynomial p (1 - S * Sᴴ) hT']
    exact cfc_congr fun t ht => (hnode t (Or.inr ht)).symm
  have hsemi : S * (1 - Sᴴ * S) = (1 - S * Sᴴ) * S := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
  rw [h1, h2, mul_aeval_of_semiconj hsemi p]

/-- **`Π(ω̄) = Πᵀ`** for Hermitian blocks. -/
theorem closingPairing_conjPath (b E h : ℝ) (n : ℕ) (ω : GrowthPath W)
    (hA : ∀ k, (ω.1 k).IsHermitian) :
    closingPairing b E h W n (conjPath ω) = (closingPairing b E h W n ω)ᵀ := by
  set S := farReflection b E W n ω
  have hX : (1 - S * Sᴴ).IsHermitian := isHermitian_one.sub (isHermitian_mul_conjTranspose_self _)
  rw [closingPairing, farTransmission_conjPath b E n ω hA, farReflection_conjPath b E n ω hA,
    cfc_matConj _ _ hX, conjTranspose_transpose', ← matConj_mul, cfc_one_sub_semiconj,
    closingPairing, farTransmission, transpose_eq_matConj_conjTranspose, conjTranspose_mul,
    conjTranspose_conjTranspose, cfc_conjTranspose]

/-!
## The cap event at the conjugated path
-/

theorem matConj_real_smul_one {n : Type*} [DecidableEq n] (E : ℝ) :
    matConj ((E : ℂ) • (1 : Matrix n n ℂ)) = (E : ℂ) • 1 := by
  ext i j
  simp only [matConj_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp

theorem pathSchur_sampleConj (E : ℝ) {r : ℕ} (p : PathSample W r) :
    pathSchur E (sampleConj p) = matConj (pathSchur E p) := by
  have hs : matConj (pathMatrix p - (E : ℂ) • 1) = matConj (pathMatrix p) - (E : ℂ) • 1 := by
    rw [matConj_sub, matConj_real_smul_one]
  rw [pathSchur, pathSchur, pathMatrix_sampleConj, pathPortCoupling_sampleConj, ← hs,
    ← matConj_inv, ← matConj_conjTranspose, ← matConj_mul, ← matConj_mul]

theorem nearSchur_transpose (z : ℂ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    nearSchur z XXᵀ = (nearSchur z XX)ᵀ := by
  have hb : ∀ i j, portBlock XXᵀ i j = (portBlock XX j i)ᵀ := fun i j => by
    ext
    rfl
  have hK : z • (1 : Matrix (Fin W) (Fin W) ℂ) - (portBlock XX 1 1)ᵀ =
      (z • 1 - portBlock XX 1 1)ᵀ := by
    rw [transpose_sub, transpose_smul, transpose_one]
  rw [nearSchur, nearSchur, hb, hb, hb, hb, hK, ← transpose_nonsing_inv, transpose_add,
    transpose_mul, transpose_mul]
  simp only [Matrix.mul_assoc]

theorem pathNearSchur_conjPath (b E : ℝ) (r : ℕ) (ω : GrowthPath W)
    (hA : ∀ k, (ω.1 k).IsHermitian) :
    pathNearSchur b E (fun _ => 0) W r (conjPath ω) =
      (pathNearSchur b E (fun _ => 0) W r ω)ᵀ := by
  rw [pathNearSchur, pathNearSchur, absorbedPathSchur_zero, absorbedPathSchur_zero,
    pathAt_conjPath, pathSchur_sampleConj,
    ← transpose_eq_matConj_of_isHermitian (pathSchur_isHermitian E r ω hA), nearSchur_transpose]

theorem passiveS_transpose (b E : ℝ) {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    passiveS b E Xᵀ = (passiveS b E X)ᵀ := by
  have hK : boundaryZ b E • (1 : Matrix (Fin n) (Fin n) ℂ) - Xᵀ =
      (boundaryZ b E • 1 - X)ᵀ := by
    rw [transpose_sub, transpose_smul, transpose_one]
  rw [passiveS, passiveS, passiveResolvent, passiveResolvent, hK, ← transpose_nonsing_inv,
    transpose_sub, transpose_one, transpose_smul]

theorem charpoly_passiveTransmission_transpose (b E : ℝ) {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    (passiveTransmission b E Xᵀ).charpoly = (passiveTransmission b E X).charpoly := by
  rw [passiveTransmission_eq_one_sub, passiveTransmission_eq_one_sub, passiveS_transpose]
  set S := passiveS b E X
  have e : (Sᵀ)ᴴ = (Sᴴ)ᵀ := by
    rw [conjTranspose_transpose', transpose_eq_matConj_conjTranspose Sᴴ,
      conjTranspose_conjTranspose]
  have e2 : (1 : Matrix (Fin n) (Fin n) ℂ) - (S * Sᴴ)ᵀ = (1 - S * Sᴴ)ᵀ := by
    rw [transpose_sub, transpose_one]
  rw [e, ← transpose_mul, e2, charpoly_transpose, charpoly_one_sub_mul_comm]

/-- **The transmission trace measure is conjugation invariant** (Hermitian blocks). -/
theorem transmissionProcess_conjPath (b E : ℝ) (t : ℝ) (ω : GrowthPath W)
    (hA : ∀ k, (ω.1 k).IsHermitian) :
    transmissionProcess b E (fun _ => 0) W t (conjPath ω) =
      transmissionProcess b E (fun _ => 0) W t ω := by
  rw [transmissionProcess, transmissionProcess, traceMeasure, traceMeasure, pathTransmission,
    pathTransmission, pathNearSchur_conjPath b E _ ω hA, charpoly_passiveTransmission_transpose]

theorem mem_physCapEventC_conjPath (b E s h : ℝ) (K : ℕ) (ω : GrowthPath W)
    (hA : ∀ k, (ω.1 k).IsHermitian) :
    conjPath ω ∈ physCapEventC b E s h K W ↔ ω ∈ physCapEventC b E s h K W := by
  simp only [physCapEventC, Set.mem_ofPred_eq, transmissionProcess_conjPath b E s ω hA]

/-!
## The resolvent integrands at the conjugated path
-/

/-- The resolvent-matrix identity behind `resIn_conjPath_trace`. -/
theorem hs_conj_identity {ι : Type*} [Fintype ι] [DecidableEq ι] (z : ℂ)
    {S Af Pf Of : Matrix ι ι ℂ} (hAP : Af * Pf = Pf) (hPO : Pf * Of = Pf) (hPP : Pfᴴ * Pf = Of)
    (hOH : Ofᴴ = Of) (hOO : Of * Of = Of) :
    ((1 - z • (Of * S * Pf))⁻¹ * Of * S)ᴴ * ((1 - z • (Of * S * Pf))⁻¹ * Of * S) =
      ((1 - z • (Pf * S * Af))⁻¹ * (Pf * S))ᴴ * ((1 - z • (Pf * S * Af))⁻¹ * (Pf * S)) := by
  set J := (1 - z • (Pf * S))⁻¹
  have e1 : (1 - z • (Of * S * Pf))⁻¹ * Of * S = Of * S * J := by
    rw [Matrix.mul_assoc, show z • (Of * S * Pf) = (Of * S) * (z • Pf) by rw [Matrix.mul_smul],
      inv_one_sub_mul_comm, show z • Pf * (Of * S) = z • (Pf * S) by
        rw [Matrix.smul_mul, ← Matrix.mul_assoc, hPO]]
  have e2 : (1 - z • (Pf * S * Af))⁻¹ * (Pf * S) = Pf * S * J := by
    rw [show z • (Pf * S * Af) = (Pf * S) * (z • Af) by rw [Matrix.mul_smul],
      inv_one_sub_mul_comm, show z • Af * (Pf * S) = z • (Pf * S) by
        rw [Matrix.smul_mul, ← Matrix.mul_assoc, hAP]]
  rw [e1, e2]
  simp only [conjTranspose_mul]
  calc Jᴴ * (Sᴴ * Ofᴴ) * (Of * S * J) = Jᴴ * Sᴴ * (Ofᴴ * Of) * S * J := by
        simp only [Matrix.mul_assoc]
    _ = Jᴴ * Sᴴ * (Pfᴴ * Pf) * S * J := by rw [hOH, hOO, hPP]
    _ = Jᴴ * (Sᴴ * Pfᴴ) * (Pf * S * J) := by simp only [Matrix.mul_assoc]

/-- **The `BirthKResIn` integrand at `ω̄` is the `BirthKResOut` integrand at `ω`** (Hermitian
blocks, `h² < 1`, every phase). -/
theorem resIn_conjPath_trace (b E s h : ℝ) (hh : h ^ 2 < 1) (n k : ℕ) (ω : GrowthPath W)
    (hA : ∀ k, (ω.1 k).IsHermitian) (θ : ℝ) :
    ((resInMat b E s h W n (conjPath ω) θ)ᴴ * resInMat b E s h W n (conjPath ω) θ *
        tagResponse b E W n k (conjPath ω)).trace.re =
      ((resOutMat b E s h W n ω θ)ᴴ * resOutMat b E s h W n ω θ *
        tagResponse b E W n k ω).trace.re := by
  set Pw := closingPairing b E h W (closeLen s W) ω
  set S := scatteringMatrix b E W n ω
  set Y := tagResponse b E W n k ω
  set z := phase θ
  set Pf := farEmbed Pw
  set Of := farEmbed (Pwᴴ * Pw)
  set Af := farEmbed (omittedProj b E h W (closeLen s W) ω)
  have hPPw : Pw * Pwᴴ = omittedProj b E h W (closeLen s W) ω :=
    closingPairing_mul_conj b E h hh _ _
  have hAPw : omittedProj b E h W (closeLen s W) ω * Pw = Pw :=
    omittedProj_mul_closingPairing b E h _ _
  have hAP : Af * Pf = Pf := omittedEmbed_mul_pairing b E h _ _
  have hPO : Pf * Of = Pf := by
    rw [farEmbed_mul, ← Matrix.mul_assoc, hPPw, hAPw]
  have hPP : Pfᴴ * Pf = Of := by rw [farEmbed_conjTranspose, farEmbed_mul]
  have hOH : Ofᴴ = Of := by
    rw [farEmbed_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]
  have hOO : Of * Of = Of := by
    rw [farEmbed_mul, show Pwᴴ * Pw * (Pwᴴ * Pw) = Pwᴴ * (Pw * Pwᴴ * Pw) by
      simp only [Matrix.mul_assoc], hPPw, hAPw]
  have hR : birthKRes b E s h W n (conjPath ω) θ = ((1 - z • (Of * S * Pf))⁻¹)ᵀ := by
    have e : (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) - z • (Pfᵀ * Sᵀ * Ofᵀ) =
        (1 - z • (Of * S * Pf))ᵀ := by
      rw [transpose_sub, transpose_one, transpose_smul, transpose_mul, transpose_mul,
        Matrix.mul_assoc]
    rw [birthKRes, closingN, scatteringMatrix_conjPath b E n ω hA,
      omittedProj_conjPath b E h hh _ ω hA, closingPairing_conjPath b E h _ ω hA,
      farEmbed_matConj, farEmbed_transpose, ← transpose_eq_matConj_of_isHermitian hOH, e,
      transpose_nonsing_inv]
  have hM : resInMat b E s h W n (conjPath ω) θ =
      matConj ((1 - z • (Of * S * Pf))⁻¹ * Of) := by
    rw [resInMat, hR, omittedProj_conjPath b E h hh _ ω hA, farEmbed_matConj,
      conjTranspose_transpose', matConj_mul]
  set B := (1 - z • (Of * S * Pf))⁻¹ * Of
  have hT : (Bᴴ * B * (S * Y * Sᴴ)).trace = ((B * S)ᴴ * (B * S) * Y).trace := by
    rw [show Bᴴ * B * (S * Y * Sᴴ) = (Bᴴ * B * S * Y) * Sᴴ by simp only [Matrix.mul_assoc],
      trace_mul_comm, conjTranspose_mul B S]
    simp only [Matrix.mul_assoc]
  have key : (B * S)ᴴ * (B * S) = (resOutMat b E s h W n ω θ)ᴴ * resOutMat b E s h W n ω θ :=
    hs_conj_identity z hAP hPO hPP hOH hOO
  rw [hM, tagResponse_conjPath b E n k ω hA, ← matConj_conjTranspose, ← matConj_mul,
    ← matConj_mul, re_trace_matConj, hT, key]

/-!
## The two path-only estimates are the same in law
-/

/-- The integrand of the path-only resolvent estimates. -/
def resPathIntegrand (b E s h : ℝ) (K : ℕ) (mc : ℝ) (W n k : ℕ)
    (M : GrowthPath W → ℝ → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (ω : GrowthPath W) :
    ℝ≥0∞ :=
  (physCapEventC b E s h K W).indicator (fun ω => ENNReal.ofReal (mc / W) *
    (∫⁻ θ, ENNReal.ofReal (Real.sqrt (((M ω θ)ᴴ * M ω θ * tagResponse b E W n k ω).trace.re))
      ∂phaseLaw) ^ 2) ω

theorem resPathIntegrand_conjPath (b E s h : ℝ) (hh : h ^ 2 < 1) (K : ℕ) (mc : ℝ) (n k : ℕ)
    (ω : GrowthPath W) (hA : ∀ k, (ω.1 k).IsHermitian) :
    resPathIntegrand b E s h K mc W n k (resInMat b E s h W n) (conjPath ω) =
      resPathIntegrand b E s h K mc W n k (resOutMat b E s h W n) ω := by
  unfold resPathIntegrand
  by_cases hω : ω ∈ physCapEventC b E s h K W
  · have hω' : conjPath ω ∈ physCapEventC b E s h K W :=
      (mem_physCapEventC_conjPath b E s h K ω hA).2 hω
    rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω']
    simp only [resIn_conjPath_trace b E s h hh n k ω hA]
  · have hω' : conjPath ω ∉ physCapEventC b E s h K W :=
      fun h' => hω ((mem_physCapEventC_conjPath b E s h K ω hA).1 h')
    rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω']

theorem lintegral_resPath_out_eq_in (b E s h : ℝ) (hh : h ^ 2 < 1) (K : ℕ) (mc : ℝ) (n k : ℕ) :
    ∫⁻ ω, resPathIntegrand b E s h K mc W n k (resOutMat b E s h W n) ω ∂growthPathLaw W b =
      ∫⁻ ω, resPathIntegrand b E s h K mc W n k (resInMat b E s h W n) ω
        ∂growthPathLaw W b := by
  rw [← lintegral_conjPath b (resPathIntegrand b E s h K mc W n k (resInMat b E s h W n))]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_growth_isHermitian W b] with ω hA
  exact (resPathIntegrand_conjPath b E s h hh K mc n k ω hA).symm

/-- **`BirthKResOutPath` from `BirthKResInPath`** (conjugation symmetry). -/
theorem birthKResOutPath_of_in (hI : BirthKResInPath) : BirthKResOutPath := by
  intro b E np τ m T s h K hD hs hsτ hh0 hh1
  obtain ⟨C, hC⟩ := hI b E np τ m T s h K hD hs hsτ hh0 hh1
  have hh : h ^ 2 < 1 := by nlinarith
  refine ⟨C, ?_⟩
  filter_upwards [hC] with W hW
  intro j hj1 hj2 hb c hcj
  have e := lintegral_resPath_out_eq_in (W := W) b E s h hh K (m c) (j + 1) ⌊(W : ℝ) * τ c⌋₊
  unfold resPathIntegrand at e
  rw [e]
  exact hW j hj1 hj2 hb c hcj

/-- **`BirthKResInPath` from `BirthKResOutPath`** (the converse). -/
theorem birthKResInPath_of_out (hO : BirthKResOutPath) : BirthKResInPath := by
  intro b E np τ m T s h K hD hs hsτ hh0 hh1
  obtain ⟨C, hC⟩ := hO b E np τ m T s h K hD hs hsτ hh0 hh1
  have hh : h ^ 2 < 1 := by nlinarith
  refine ⟨C, ?_⟩
  filter_upwards [hC] with W hW
  intro j hj1 hj2 hb c hcj
  have e := lintegral_resPath_out_eq_in (W := W) b E s h hh K (m c) (j + 1) ⌊(W : ℝ) * τ c⌋₊
  unfold resPathIntegrand at e
  rw [← e]
  exact hW j hj1 hj2 hb c hcj

/-- **`ComplexBirthKClosing`** from the two far estimates and the single resolvent estimate
`BirthKResInPath`. -/
theorem complexBirthKClosing_of_far_resIn (hFI : BirthKFarIn) (hFO : BirthKFarOut)
    (hRI : BirthKResInPath) : ComplexBirthKClosing :=
  complexBirthKClosing_of_parts hFI hFO (birthKResIn_of_path hRI)
    (birthKResOut_of_path (birthKResOutPath_of_in hRI))

end BlockBand.SourceProcess.PhysApprox.B3.BirthKSub
