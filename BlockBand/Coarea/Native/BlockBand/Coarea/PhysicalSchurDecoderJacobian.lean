module

public import BlockBand.Coarea.Native.BlockBand.Coarea.PhysicalConditionalCoareaExact
public import BlockBand.Coarea.Native.BlockBand.Coarea.PhysicalSchurCoareaData

/-!
# Jacobian of the physical Schur eigenpair decoder

The physical decoder subtracts the energy-dependent Schur compression from the
nonlinear eigenpair decoder: `G(E,z,B) = H(z) diag(E,B) H(z)ᴴ - F(E)`.  Its
derivative is a rank-one energy update of the bare decoder derivative.
Conjugating by the base Householder frame, using that the framed bare
derivative fixes the energy coordinate (`CoherentProjectiveCorrectionExact`),
turns the update into an elementary transvection of determinant
`1 - vᴴ F'(E) v`.  With `F'(E) = -TᴴT` and `‖v‖ = 1` this is the Schur crossing
form `vᴴ (I + TᴴT) v`, so the absolute Jacobian is the affine projective
density times the squared complementary gap times `vᴴ 𝒟 v`, at every
`(E,z,B)`.  The physical compression `V - Cᴴ (H_R - E)⁻¹ C` is shown to have
this derivative off the exterior poles.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

@[expose] public section
noncomputable section
namespace CoareaNative.BlockBand

open Matrix

section PhysicalDerivative

open Filter Topology

/-- Resolvent identity: `R(s) - R(E) = (s - E) R(s) R(E)` off the poles. -/
theorem physicalCoareaResolvent_sub {r : ℕ} (H_R : Matrix (Fin r) (Fin r) ℂ) (s E : ℝ)
    (hs : (H_R - (s : ℂ) • 1).det ≠ 0) (hE : (H_R - (E : ℂ) • 1).det ≠ 0) :
    physicalCoareaResolvent H_R s - physicalCoareaResolvent H_R E =
      ((s : ℂ) - E) • (physicalCoareaResolvent H_R s * physicalCoareaResolvent H_R E) := by
  unfold physicalCoareaResolvent
  set A := H_R - (s : ℂ) • 1
  set B := H_R - (E : ℂ) • 1
  have h1 : A⁻¹ * A = 1 := nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hs)
  have h2 : B * B⁻¹ = 1 := mul_nonsing_inv B (isUnit_iff_ne_zero.mpr hE)
  have hBA : B - A = ((s : ℂ) - E) • 1 := by
    simp only [A, B, sub_smul]; abel
  have : A⁻¹ * (B - A) * B⁻¹ = A⁻¹ - B⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, h2, h1, Matrix.mul_one, Matrix.one_mul]
  rw [← this, hBA]
  simp

/-- The physical compression `F(E) = V - Cᴴ (H_R - E)⁻¹ C` has energy
derivative `-T(E)ᴴ T(E)` off the exterior poles (`H_R` Hermitian). -/
theorem hasDerivAt_physicalCoareaF {d r : ℕ}
    (H_R : Matrix (Fin r) (Fin r) ℂ) (hH : H_R.IsHermitian)
    (C : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (E : ℝ) (hE : (H_R - (E : ℂ) • 1).det ≠ 0) :
    HasDerivAt (physicalCoareaF H_R C V)
      (-((physicalCoareaT H_R C E)ᴴ * physicalCoareaT H_R C E)) E := by
  set R := physicalCoareaResolvent H_R
  have hdetc : Continuous fun s : ℝ => (H_R - (s:ℂ) • 1).det := by fun_prop
  have hev : ∀ᶠ s : ℝ in 𝓝 E, (H_R - (s:ℂ) • 1).det ≠ 0 :=
    hdetc.continuousAt.eventually_ne hE
  have hRc : ContinuousAt R E := by
    have h1 : ContinuousAt (Inv.inv : Matrix (Fin r) (Fin r) ℂ → _) (H_R - (E:ℂ) • 1) := by
      apply continuousAt_matrix_inv
      exact NormedRing.inverse_continuousAt (Units.mk0 _ hE)
    exact h1.comp (f := fun s : ℝ => H_R - (s:ℂ) • 1) (by fun_prop)
  have hlim : Tendsto (fun s => -(Cᴴ * (R s * R E) * C)) (𝓝[≠] E)
      (𝓝 (-(Cᴴ * (R E * R E) * C))) := by
    have : ContinuousAt (fun s => -(Cᴴ * (R s * R E) * C)) E := by
      have hc : Continuous fun M : Matrix (Fin r) (Fin r) ℂ => -(Cᴴ * (M * R E) * C) := by
        fun_prop
      exact hc.continuousAt.comp hRc
    exact this.tendsto.mono_left nhdsWithin_le_nhds
  have hT : (physicalCoareaT H_R C E)ᴴ * physicalCoareaT H_R C E = Cᴴ * (R E * R E) * C := by
    have hRh : (R E)ᴴ = R E := by
      simp only [R, physicalCoareaResolvent, conjTranspose_nonsing_inv]
      congr 1
      rw [conjTranspose_sub, hH.eq, conjTranspose_smul, conjTranspose_one]
      simp
    change (R E * C)ᴴ * (R E * C) = _
    rw [conjTranspose_mul, hRh]
    simp only [Matrix.mul_assoc]
  rw [hT]
  let _ : NormedAddCommGroup (Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ) :=
    Matrix.normedAddCommGroup
  let _ : NormedSpace ℝ (Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ) :=
    Matrix.normedSpace
  refine hasDerivAt_iff_tendsto_slope.mpr ?_
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hev] with s hs hdet
  have hsE : (s : ℂ) - E ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hs
  rw [slope_def_module]
  simp only [physicalCoareaF]
  have hsub : R s - R E = ((s : ℂ) - E) • (R s * R E) :=
    physicalCoareaResolvent_sub H_R s E hdet hE
  have : V - Cᴴ * R s * C - (V - Cᴴ * R E * C) = -(Cᴴ * (R s - R E) * C) := by
    rw [Matrix.mul_sub, Matrix.sub_mul]; abel
  rw [this, hsub]
  ext i j
  simp only [Matrix.smul_apply, Matrix.neg_apply, Matrix.mul_smul, Matrix.smul_mul, smul_eq_mul]
  rw [Complex.real_smul]
  push_cast
  field_simp

end PhysicalDerivative

section Decoder

variable {d : ℕ} (i : Fin d)

/-- The selected energy coordinate of a coherent Hermitian input. -/
def coherentEigenpairEnergyCLM : CoherentHermitianCoordinates d →L[ℝ] ℝ :=
  ((LinearMap.fst ℝ ℝ ((Fin (d - 1) → ℂ) × RealHermitianMatrix (Fin (d - 1)))).comp
    (coherentSelectedBlockInputLinearMap i)).toContinuousLinearMap

@[simp] theorem coherentEigenpairEnergyCLM_apply (x : CoherentHermitianCoordinates d) :
    coherentEigenpairEnergyCLM i x = (coherentSelectedBlockInputLinearMap i x).1 := rfl

/-- Selected-coordinate readback of a plain complex matrix. -/
def coherentMatrixReadbackCLM :
    Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ →L[ℝ]
      CoherentHermitianCoordinates d :=
  (coherentSelectedMatrixReadbackCLM i).comp
    ((coherentComplexMatrixEquiv (Unit ⊕ Fin (d - 1))).symm :
      Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ →L[ℝ]
        CoherentComplexMatrix (Unit ⊕ Fin (d - 1)))

/-- The physical decoder `G(E,z,B) = H(z) diag(E,B) H(z)ᴴ - F(E)`. -/
def coherentPhysicalSchurDecode
    (F : ℝ → Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (x : CoherentHermitianCoordinates d) : CoherentHermitianCoordinates d :=
  coherentSelectedEigenpairDecode i x -
    coherentMatrixReadbackCLM i (F (coherentEigenpairEnergyCLM i x))

/-- Derivative of the physical decoder. -/
theorem hasFDerivAt_coherentPhysicalSchurDecode
    (F : ℝ → Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (F' : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (x : CoherentHermitianCoordinates d)
    (hF : HasDerivAt F F' (coherentEigenpairEnergyCLM i x)) :
    HasFDerivAt (coherentPhysicalSchurDecode i F)
      (fderiv ℝ (coherentSelectedEigenpairDecode i) x -
        (coherentEigenpairEnergyCLM i).smulRight (coherentMatrixReadbackCLM i F')) x := by
  have hdec := (hasFDerivAt_coherentSelectedEigenpairDecode_explicit_global i x)
  rw [← hdec.fderiv] at hdec
  have hRF : HasDerivAt (fun t => coherentMatrixReadbackCLM i (F t))
      (coherentMatrixReadbackCLM i F') (coherentEigenpairEnergyCLM i x) := by
    have h : HasDerivAt
        (F := (Unit ⊕ Fin (d - 1)) → (Unit ⊕ Fin (d - 1)) → ℂ) (fun t => F t) F'
        (coherentEigenpairEnergyCLM i x) := hF
    let L : ((Unit ⊕ Fin (d - 1)) → (Unit ⊕ Fin (d - 1)) → ℂ) →L[ℝ]
        CoherentHermitianCoordinates d :=
      ⟨((coherentMatrixReadbackCLM i).toLinearMap :
        ((Unit ⊕ Fin (d - 1)) → (Unit ⊕ Fin (d - 1)) → ℂ) →ₗ[ℝ]
          CoherentHermitianCoordinates d), (coherentMatrixReadbackCLM i).continuous⟩
    exact L.hasFDerivAt.comp_hasDerivAt _ h
  have hFE := hRF.hasFDerivAt.comp x (coherentEigenpairEnergyCLM i).hasFDerivAt
  convert hdec.sub hFE using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro u
    simp [ContinuousLinearMap.smulRight_apply]

/-- Readback of a Hermitian matrix, in selected block coordinates, is its
energy/tangent/complement block encoding. -/
theorem coherentSelectedBlockCoordinate_matrixReadback
    (M : RealHermitianMatrix (Unit ⊕ Fin (d - 1))) :
    coherentSelectedBlockCoordinateLinearEquiv i (coherentMatrixReadbackCLM i M.1) =
      eigenpairHermitianBlockLinearEquiv (Fin (d - 1)) M := by
  have hdec := selectedMatrixFinCoordinateRead_decode i
    (eigenpairHermitianBlockLinearEquiv (Fin (d - 1)) M)
  rw [LinearEquiv.symm_apply_apply] at hdec
  have hval : (coherentMatrixReadbackCLM i M.1).value =
      selectedMatrixFinCoordinateReadCLM i M.1 := rfl
  change selectedEigenpairFinCoordinateLinearEquiv i
    (coherentMatrixReadbackCLM i M.1).value = _
  rw [hval, hdec, LinearEquiv.apply_symm_apply]

/-- The base frame compresses a matrix to its distinguished diagonal entry
`vᴴ M v`, where `v` is the normalized affine eigenvector. -/
theorem coherentEigenpairFrameAt_compress_inl (x : CoherentHermitianCoordinates d)
    (M : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ) :
    ((coherentEigenpairFrameAt i x)ᴴ * M * coherentEigenpairFrameAt i x)
        (Sum.inl Unit.unit) (Sum.inl Unit.unit) =
      star (fun a => projectiveUnitReconstruction (Sum.inl Unit.unit)
          (coherentSelectedProjectiveInputCLM i x).value a) ⬝ᵥ
        (M *ᵥ fun a => projectiveUnitReconstruction (Sum.inl Unit.unit)
          (coherentSelectedProjectiveInputCLM i x).value a) := by
  have hcol (a : Unit ⊕ Fin (d - 1)) :
      coherentEigenpairFrameAt i x a (Sum.inl Unit.unit) =
        projectiveUnitReconstruction (Sum.inl Unit.unit)
          (coherentSelectedProjectiveInputCLM i x).value a :=
    coherentProjectiveHouseholderFrame_apply_col _ a _
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hcol, dotProduct,
    Matrix.mulVec, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Determinant of the physical decoder derivative: a rank-one energy update
of the bare decoder derivative.  `F'` is any Hermitian energy derivative. -/
theorem det_fderiv_coherentPhysicalSchurDecode
    (F : ℝ → Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (F' : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ) (hF' : F'.IsHermitian)
    (x : CoherentHermitianCoordinates d)
    (hF : HasDerivAt F F' (coherentEigenpairEnergyCLM i x)) :
    LinearMap.det (fderiv ℝ (coherentPhysicalSchurDecode i F) x).toLinearMap =
      LinearMap.det (fderiv ℝ (coherentSelectedEigenpairDecode i) x).toLinearMap *
        (1 - (star (fun a => projectiveUnitReconstruction (Sum.inl Unit.unit)
            (coherentSelectedProjectiveInputCLM i x).value a) ⬝ᵥ
          (F' *ᵥ fun a => projectiveUnitReconstruction (Sum.inl Unit.unit)
            (coherentSelectedProjectiveInputCLM i x).value a)).re) := by
  rw [(hasFDerivAt_coherentPhysicalSchurDecode i F F' x hF).fderiv]
  set P := coherentSelectedBlockCoordinateLinearEquiv i
  set H := coherentEigenpairFrameAt i x
  have hU : H * Hᴴ = 1 :=
    coherentProjectiveHouseholderFrame_mul_conjTranspose (Sum.inl Unit.unit)
      (coherentSelectedProjectiveInputCLM i x)
  set N := coherentEigenpairFramedBlockDifferential i x
  set M : RealHermitianMatrix (Unit ⊕ Fin (d - 1)) := ⟨F', hF'⟩
  set w := eigenpairBlockConjLinearMap Hᴴ (eigenpairHermitianBlockLinearEquiv (Fin (d - 1)) M)
  let f : Module.Dual ℝ (EigenpairHermitianBlockCoordinates (Fin (d - 1))) :=
    -(LinearMap.fst ℝ ℝ ((Fin (d - 1) → ℂ) × RealHermitianMatrix (Fin (d - 1))))
  have hconj := eigenpairBlockConjLinearMap_comp_conjTranspose H hU
  have hfac : P.toLinearMap.comp ((fderiv ℝ (coherentSelectedEigenpairDecode i) x -
        (coherentEigenpairEnergyCLM i).smulRight
          (coherentMatrixReadbackCLM i F')).toLinearMap.comp P.symm.toLinearMap) =
      (eigenpairBlockConjLinearMap H).comp ((LinearMap.transvection f w).comp N) := by
    apply LinearMap.ext
    intro ξ
    have hN1 := coherentEigenpairFramedBlockDifferential_fst i x ξ
    have hNdef : eigenpairBlockConjLinearMap H (N ξ) =
        P ((fderiv ℝ (coherentSelectedEigenpairDecode i) x) (P.symm ξ)) := by
      have := congrArg (fun L => L (P.toLinearMap.comp
        ((fderiv ℝ (coherentSelectedEigenpairDecode i) x).toLinearMap.comp
          P.symm.toLinearMap) ξ)) hconj
      simpa [N, coherentEigenpairFramedBlockDifferential] using this
    have hw : eigenpairBlockConjLinearMap H w = P (coherentMatrixReadbackCLM i F') := by
      have := congrArg (fun L => L (eigenpairHermitianBlockLinearEquiv (Fin (d - 1)) M)) hconj
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
      rw [this]
      exact (coherentSelectedBlockCoordinate_matrixReadback i M).symm
    have hE : coherentEigenpairEnergyCLM i (P.symm ξ) = ξ.1 := by
      rw [coherentEigenpairEnergyCLM_apply, coherentSelectedBlockInputLinearMap_symm]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, ContinuousLinearMap.coe_coe,
      FunLike.coe_sub, Pi.sub_apply, ContinuousLinearMap.smulRight_apply, hE,
      map_sub, map_smul]
    change _ = eigenpairBlockConjLinearMap H (N ξ + f (N ξ) • w)
    have hf : f (N ξ) = -ξ.1 := by
      change -(N ξ).1 = -ξ.1
      rw [hN1]
    rw [map_add, map_smul, hNdef, hw, hf]
    rw [sub_eq_add_neg]
    congr 1
    exact (neg_smul ξ.1 (P (coherentMatrixReadbackCLM i F'))).symm
  have hw1 : w.1 = (star (fun a => projectiveUnitReconstruction (Sum.inl Unit.unit)
        (coherentSelectedProjectiveInputCLM i x).value a) ⬝ᵥ
      (F' *ᵥ fun a => projectiveUnitReconstruction (Sum.inl Unit.unit)
        (coherentSelectedProjectiveInputCLM i x).value a)).re := by
    rw [← coherentEigenpairFrameAt_compress_inl]
    have hw' : w = eigenpairHermitianBlockLinearEquiv (Fin (d - 1))
        (hermitianMatrixConjLinearMap Hᴴ M) := eigenpairBlockConjLinearMap_apply _ _
    rw [hw']
    change ((Hᴴ * F' * Hᴴᴴ) (Sum.inl Unit.unit) (Sum.inl Unit.unit)).re =
      ((Hᴴ * F' * H) (Sum.inl Unit.unit) (Sum.inl Unit.unit)).re
    rw [Matrix.conjTranspose_conjTranspose]
  rw [← LinearMap.det_conj _ P, hfac, LinearMap.det_comp, LinearMap.det_comp,
    LinearMap.transvection.det, det_fderiv_coherentSelectedEigenpairDecode_eq, ← hw1]
  change _ = _ * _ * (1 - w.1)
  have : f w = -w.1 := rfl
  rw [this]
  ring

/-- The crossing quadratic `vᴴ 𝒟 v` is strictly positive for every Schur
transfer `T` and every affine coordinate `z`. -/
theorem physicalEigenpairCrossingQuadratic_pos {n : Type*} [Fintype n]
    (T : Matrix n (Unit ⊕ Fin (d - 1)) ℂ) (z : Fin (d - 1) → ℂ) :
    0 < physicalEigenpairCrossingQuadratic T z := by
  have hv : (fun a => canonicalProjectiveUnitVector z a) ≠ 0 := by
    intro h
    have hn := norm_canonicalProjectiveUnitVector z
    have h0 : canonicalProjectiveUnitVector z = 0 := by
      ext a
      exact congrFun h a
    rw [h0, norm_zero] at hn
    norm_num at hn
  exact (Complex.pos_iff.mp (schurClock_quadratic_pos T hv)).1

/-- The normalized affine eigenvector has `vᴴ v = 1`. -/
theorem star_dotProduct_canonicalProjectiveUnitVector_re (z : Fin (d - 1) → ℂ) :
    (star (fun a => canonicalProjectiveUnitVector z a) ⬝ᵥ
      (fun a => canonicalProjectiveUnitVector z a)).re = 1 := by
  have hn := norm_canonicalProjectiveUnitVector z
  have hsq := EuclideanSpace.norm_sq_eq (canonicalProjectiveUnitVector z)
  rw [hn, one_pow] at hsq
  rw [hsq, dotProduct, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- `1 - vᴴ(-TᴴT)v = vᴴ 𝒟 v` for the normalized affine eigenvector. -/
theorem one_sub_neg_gram_eq_crossingQuadratic {n : Type*} [Fintype n]
    (T : Matrix n (Unit ⊕ Fin (d - 1)) ℂ) (z : Fin (d - 1) → ℂ) :
    1 - (star (fun a => canonicalProjectiveUnitVector z a) ⬝ᵥ
        (-(Tᴴ * T) *ᵥ fun a => canonicalProjectiveUnitVector z a)).re =
      physicalEigenpairCrossingQuadratic T z := by
  rw [physicalEigenpairCrossingQuadratic, schurClock, Matrix.add_mulVec, Matrix.one_mulVec,
    dotProduct_add, Complex.add_re, Matrix.neg_mulVec, dotProduct_neg, Complex.neg_re,
    sub_neg_eq_add]
  have h := star_dotProduct_canonicalProjectiveUnitVector_re z
  change 1 + _ = (star (fun a => canonicalProjectiveUnitVector z a) ⬝ᵥ
      (fun a => canonicalProjectiveUnitVector z a)).re + _
  rw [h]

/-- **Direct physical Schur decoder Jacobian** (density part of the coarea theorem: the
eigenpair coordinates of the eigenpair Jacobian lemma composed with the Schur compression, with
the crossing factor).  For the physical decoder `G(E,z,B) = H(z) diag(E,B) H(z)ᴴ - F(E)`
(read back in coherent selected Hermitian coordinates), whose compression has
energy derivative `F'(E) = -TᴴT` at `E`, the absolute real Jacobian at every
`(E,z,B)` is

`canonicalProjectiveAffineDensity z * |det (E I - B)|² * vᴴ (I + TᴴT) v`,

with `v = canonicalProjectiveUnitVector z` (`‖v‖ = 1`).  Normalization: real
Lebesgue coordinates on both sides; `canonicalProjectiveAffineDensity z =
(1 + ∑ |z_j|²)^{-d}`.  Quantifiers: every `i`, `E`, `z`, `B`, every matrix-valued
`F` and every `T` with the stated derivative at `E`; no gap hypothesis, no
zero-slice restriction, no limit. -/
theorem abs_det_fderiv_coherentPhysicalSchurDecode_globalInput {n : Type*} [Fintype n]
    (F : ℝ → Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (T : Matrix n (Unit ⊕ Fin (d - 1)) ℂ) (E : ℝ) (z : Fin (d - 1) → ℂ)
    (B : RealHermitianMatrix (Fin (d - 1)))
    (hF : HasDerivAt F (-(Tᴴ * T)) E) :
    |LinearMap.det (fderiv ℝ (coherentPhysicalSchurDecode i F)
      (coherentEigenpairGlobalInput i E z B)).toLinearMap| =
      canonicalProjectiveAffineDensity z *
        Complex.normSq (eigenpairGapMatrix E B.1).det *
        physicalEigenpairCrossingQuadratic T z := by
  have hE : coherentEigenpairEnergyCLM i (coherentEigenpairGlobalInput i E z B) = E := by
    rw [coherentEigenpairEnergyCLM_apply, coherentSelectedBlockInputLinearMap_globalInput]
  have hP : (coherentSelectedProjectiveInputCLM i
      (coherentEigenpairGlobalInput i E z B)).value = canonicalProjectiveChartCoordinates z := by
    rw [coherentSelectedProjectiveInputCLM_eq, coherentSelectedBlockInputLinearMap_globalInput]
  have hherm : (-(Tᴴ * T)).IsHermitian :=
    (Matrix.isHermitian_conjTranspose_mul_self T).neg
  have hF' : HasDerivAt F (-(Tᴴ * T))
      (coherentEigenpairEnergyCLM i (coherentEigenpairGlobalInput i E z B)) := by
    rw [hE]; exact hF
  rw [det_fderiv_coherentPhysicalSchurDecode i F (-(Tᴴ * T)) hherm _ hF', hP,
    abs_mul, abs_det_fderiv_coherentSelectedEigenpairDecode_globalInput]
  change _ * |1 - (star (fun a => canonicalProjectiveUnitVector z a) ⬝ᵥ
      (-(Tᴴ * T) *ᵥ fun a => canonicalProjectiveUnitVector z a)).re| = _
  rw [one_sub_neg_gram_eq_crossingQuadratic,
    abs_of_pos (physicalEigenpairCrossingQuadratic_pos T z),
    canonicalProjectiveAffineDensity_eq i z]

/-- **Physical specialization.**  For the physical compression
`F = physicalCoareaF H_R C V` with Hermitian exterior block `H_R`, at every
pole-free energy `E` and every `(z,B)`, the physical decoder has absolute
Jacobian `canonicalProjectiveAffineDensity z * |det (E I - B)|² * vᴴ 𝒟(E) v`,
`𝒟(E) = physicalCoareaD H_R C E = I + T(E)ᴴT(E)`, `v = canonicalProjectiveUnitVector z`. -/
theorem abs_det_fderiv_physicalSchurDecoder_globalInput {r : ℕ}
    (H_R : Matrix (Fin r) (Fin r) ℂ) (hH : H_R.IsHermitian)
    (C : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (E : ℝ) (hE : (H_R - (E : ℂ) • 1).det ≠ 0) (z : Fin (d - 1) → ℂ)
    (B : RealHermitianMatrix (Fin (d - 1))) :
    |LinearMap.det (fderiv ℝ (coherentPhysicalSchurDecode i (physicalCoareaF H_R C V))
      (coherentEigenpairGlobalInput i E z B)).toLinearMap| =
      canonicalProjectiveAffineDensity z *
        Complex.normSq (eigenpairGapMatrix E B.1).det *
        (star (canonicalProjectiveUnitVector z) ⬝ᵥ
          (physicalCoareaD H_R C E *ᵥ canonicalProjectiveUnitVector z)).re := by
  rw [abs_det_fderiv_coherentPhysicalSchurDecode_globalInput i _ (physicalCoareaT H_R C E)
    E z B (hasDerivAt_physicalCoareaF H_R hH C V E hE)]
  rfl

end Decoder

end CoareaNative.BlockBand
