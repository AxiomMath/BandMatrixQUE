module

public import BlockBand.SourceProcess.Stochastic.Angular.Regularity
public import BlockBand.SourceProcess.Stochastic.Dyson.ItoIdentities

/-!
# Complex angular contract: zero covariation with the eigenvalues

A step towards `TransmissionAngular.ComplexAngularContract`: the eigenvalue noise
`dB_i = √N u_i^* dG u_i` is orthogonal to the angular noise.

`arrayFn_cross`: `∑_a ∂_a F ∂_a λ_i = 0` on the simple-spectrum set, for `F = arrayFn V f₀`.
The gradient of `λ_i` is `P_i` (`sum_fderiv_lam_smul`), so the sum is `DF[P_i]`; and the first
variation of every projection along `P_i` vanishes, `dP_k[P_i] = ∑_{j≠k} (P_j P_i P_k + P_k P_i P_j)
/(λ_k - λ_j) = 0` (`dProjAt_proj_eq_zero`), so the local frame, a smooth function of the
projections (`frameArr_eq_comp`), does not move to first order.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.Stochastic.ComplexAngular
open MeasureTheory Filter Topology Matrix Set
open scoped Matrix ComplexConjugate ContDiff Matrix.Norms.Operator
open BlockBand.Internal.Contracts.Transmission BlockBand.Internal.Contracts.TransmissionAngular
open BlockBand.SourceProcess.Stochastic.Dyson

variable {N r : ℕ}

theorem dProjAt_proj_eq_zero {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) (i k : Fin N) :
    dProjAt N y k (proj N i y) = 0 := by
  have e : ∀ a b, proj N a y * proj N b y = if a = b then proj N a y else 0 := fun a b =>
    proj_mul_proj (vecHerm_isHermitian y) hy a b
  rw [dProjAt_eq]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hjk : j ≠ k := Finset.ne_of_mem_erase hj
  rw [e j i, Matrix.mul_assoc, e i j]
  by_cases hji : j = i
  · subst hji; simp [e, hjk, Ne.symm hjk]
  · simp [hji, Ne.symm hji]

theorem fderiv_proj_along_proj {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) (i k : Fin N) :
    fderiv ℝ (proj N k) y (hermVec N (proj N i y)) = 0 := by
  rw [fderiv_proj_eq hy,
    vecHerm_hermVec (H := proj N i y) (proj_isHermitian (vecHerm_isHermitian y) hy i)]
  exact dProjAt_proj_eq_zero hy i k

/-- The gradient of `λ_i` is `P_i`. -/
theorem sum_fderiv_lam_smul {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) (i : Fin N) :
    ∑ a, fderiv ℝ (lam N i) y (Pi.single a 1) • (Pi.single a 1 : Fin (N * N) → ℝ) =
      hermVec N (proj N i y) := by
  funext b
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [fderiv_lam_eq hy, vecHerm_single, hermVec, hermCoord, trace_mul_comm]

/-- The local frame as a function of the family of projections. -/
def frameMap (V : Matrix (Fin N) (Fin r) ℂ) (κ : Fin N → Fin N)
    (P : Fin N → Matrix (Fin N) (Fin N) ℂ) : AngularArray N r :=
  angularArray V fun i b =>
    (((Real.sqrt (P i (κ i) (κ i)).re)⁻¹ : ℝ) : ℂ) * P i b (κ i)

theorem frameArr_eq_comp (V : Matrix (Fin N) (Fin r) ℂ) (κ : Fin N → Fin N) :
    frameArr V κ = fun y => frameMap V κ fun k => proj N k y := rfl

theorem differentiableAt_frameMap (V : Matrix (Fin N) (Fin r) ℂ) {κ : Fin N → Fin N}
    {P : Fin N → Matrix (Fin N) (Fin N) ℂ} (hκ : ∀ i, 0 < (P i (κ i) (κ i)).re) :
    DifferentiableAt ℝ (frameMap V κ) P := by
  have hent : ∀ i a k, DifferentiableAt ℝ (fun P : Fin N → Matrix (Fin N) (Fin N) ℂ =>
      P i a k) P := fun i a k =>
    ((entryCLM a k).comp (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin N => Matrix (Fin N) (Fin N) ℂ) i)).differentiableAt (x := P)
  refine differentiableAt_pi.2 fun i => differentiableAt_pi.2 fun a => ?_
  simp only [frameMap, angularArray, Matrix.mulVec, dotProduct]
  refine DifferentiableAt.fun_sum fun b _ => (differentiableAt_const _).mul ?_
  have hre : DifferentiableAt ℝ (fun P : Fin N → Matrix (Fin N) (Fin N) ℂ =>
      (P i (κ i) (κ i)).re) P := Complex.reCLM.differentiableAt.comp P (hent i (κ i) (κ i))
  have hsq := ((Real.contDiffAt_sqrt (n := 1) (hκ i).ne').differentiableAt
    (by norm_num)).comp P hre
  have hinv := hsq.inv (Real.sqrt_pos.2 (hκ i)).ne'
  exact (Complex.ofRealCLM.differentiableAt.comp P hinv).mul (hent i b (κ i))

theorem fderiv_frameArr_along_proj (V : Matrix (Fin N) (Fin r) ℂ) {κ : Fin N → Fin N}
    {y : Fin (N * N) → ℝ} (hy : y ∈ simpleSet N) (hκ : ∀ i, 0 < (proj N i y (κ i) (κ i)).re)
    (i : Fin N) : fderiv ℝ (frameArr V κ) y (hermVec N (proj N i y)) = 0 := by
  have hP : DifferentiableAt ℝ (fun y => fun k => proj N k y) y :=
    differentiableAt_pi.2 fun k => (hasFDerivAt_proj hy k).differentiableAt
  rw [frameArr_eq_comp, show (fun y => frameMap V κ fun k => proj N k y) =
    frameMap V κ ∘ fun y => fun k => proj N k y from rfl,
    fderiv_comp y (differentiableAt_frameMap V hκ) hP, ContinuousLinearMap.comp_apply,
    fderiv_pi fun k => (hasFDerivAt_proj hy k).differentiableAt]
  have h0 : (fun k => fderiv ℝ (proj N k) y (hermVec N (proj N i y))) = 0 :=
    funext fun k => fderiv_proj_along_proj hy i k
  refine (congrArg (fderiv ℝ (frameMap V κ) fun k => proj N k y) ?_).trans (map_zero _)
  exact h0

/-- **Zero covariation of `F = arrayFn V f₀` with every eigenvalue.** -/
theorem arrayFn_cross (V : Matrix (Fin N) (Fin r) ℂ) {f₀ : AngularArray N r → ℝ}
    (hf : ContDiff ℝ 2 f₀) (hp : IsPhaseInvariant f₀) {y : Fin (N * N) → ℝ}
    (hy : y ∈ simpleSet N) (i : Fin N) :
    ∑ a, fderiv ℝ (arrayFn V f₀) y (Pi.single a 1) * fderiv ℝ (lam N i) y (Pi.single a 1) = 0 := by
  obtain ⟨κ, hκ⟩ := eventually_frame hy
  have hev : arrayFn V f₀ =ᶠ[𝓝 y] f₀ ∘ frameArr V κ := by
    filter_upwards [hκ] with y' hy'
    rw [arrayFn_of_mem hy'.1, phaseInv_frame hp V hy'.1 hy'.2]; rfl
  have hfr : DifferentiableAt ℝ (frameArr V κ) y :=
    (contDiffAt_frameArr (n := 1) V hy hκ.self_of_nhds.2).differentiableAt (by norm_num)
  have hsum : ∑ a, fderiv ℝ (arrayFn V f₀) y (Pi.single a 1) *
      fderiv ℝ (lam N i) y (Pi.single a 1) =
      fderiv ℝ (arrayFn V f₀) y (hermVec N (proj N i y)) := by
    rw [← sum_fderiv_lam_smul hy i, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  rw [hsum, hev.fderiv_eq, fderiv_comp y ((hf.differentiable (by norm_num)) _) hfr,
    ContinuousLinearMap.comp_apply, fderiv_frameArr_along_proj V hy hκ.self_of_nhds.2 i, map_zero]

end BlockBand.SourceProcess.Stochastic.ComplexAngular
