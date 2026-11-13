module

public import BlockBand.Endpoints.Response.JetFixedDefs
public import BlockBand.Internal.Contracts.TransmissionUniform2
public import BlockBand.Model.Construction.GaussianPolynomialNull

/-!
# The jet distance of the fresh layer through its Schur complement

This file shows that, almost surely under the fresh one-port layer law, the jet distance of the
layer equals `jetDistance0` of its outgoing Schur matrix, and deduces the fixed-input jet
contraction `OnePortJetContractionFixed` from `PassiveScalarContractionContract`
(`onePortJetContractionFixed_of_contracts`).

* `jfx_inv_fromBlocks_toBlocks22`: `((A B; C D)⁻¹)₂₂ = (D - CA⁻¹B)⁻¹` for invertible `A` (both
  sides are `0` when the Schur complement is singular, by the `Matrix.inv` convention).
* `jfx_freshPortBlock_eq`: deterministically, `𝒢_{port,port}(X, ν) = (z - X₊)⁻¹` when
  `A - E - X` is invertible.
* `jfx_ae_gue_det_ne_zero`: under `gueMeasure ι t`, `t > 0`, `det(A - c) ≠ 0` a.s. for every
  deterministic `c` (Gaussian polynomial nullity, `volume_mvPolynomial_zeroSet_fintype`).
* `cec_freshJet0_ae_eq_jetDistance0_freshSchur`: for `b < 1/2`, `W ≥ 1`, every real `E` and
  every deterministic `X`, `cec_freshJet0 b E X ν = jetDistance0 b E (freshSchur E X ν)` for
  `freshLaw W b`-a.e. `ν`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal NNReal ComplexConjugate ComplexOrder
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Layers

/-!
## The Schur complement of an invertible top-left block
-/

/-- `((A B; C D)⁻¹)₂₂ = (D - CA⁻¹B)⁻¹` when `A` is invertible. If the Schur complement is
singular, so is the block matrix (`det_fromBlocks₁₁`) and both sides are `0`. -/
theorem jfx_inv_fromBlocks_toBlocks22 {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (A : Matrix m m ℂ) (B : Matrix m n ℂ) (C : Matrix n m ℂ) (D : Matrix n n ℂ)
    (hA : IsUnit A.det) : (fromBlocks A B C D)⁻¹.toBlocks₂₂ = (D - C * A⁻¹ * B)⁻¹ := by
  let := A.invertibleOfIsUnitDet hA
  have hAinv : ⅟A = A⁻¹ := Matrix.invOf_eq_nonsing_inv A
  by_cases hS : IsUnit (D - C * A⁻¹ * B).det
  · let : Invertible (D - C * ⅟A * B) := by
      rw [hAinv]; exact (D - C * A⁻¹ * B).invertibleOfIsUnitDet hS
    let := fromBlocks₁₁Invertible A B C D
    rw [← Matrix.invOf_eq_nonsing_inv (fromBlocks A B C D), invOf_fromBlocks₁₁_eq,
      toBlocks_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv]
    simp only [hAinv]
  · have hdet : ¬ IsUnit (fromBlocks A B C D).det := by
      rw [det_fromBlocks₁₁, hAinv]
      intro h
      exact hS (isUnit_of_mul_isUnit_right h)
    rw [Matrix.nonsing_inv_apply_not_isUnit _ hdet, Matrix.nonsing_inv_apply_not_isUnit _ hS]
    ext x y
    simp [toBlocks₂₂]

/-!
## The port block of the fresh layer resolvent
-/

/-- The top-left block `A - E - X` of the fresh one-port layer matrix
`𝒢⁻¹ = [[A - E - X, B], [B*, z]]` (`layerMatrix`), `X` placed on the single physical block. -/
def jfx_block (E : ℝ) {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ)
    (ν : LayerSample W .oneBlockOnePort) :
    Matrix (PhysSite W .oneBlockOnePort) (PhysSite W .oneBlockOnePort) ℂ :=
  blockDiag ν.1 - (E : ℂ) • 1 - Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2

/-- The reindexing `x ↦ (0, x)` of a single block. -/
abbrev jfx_e (W : ℕ) : Fin W ≃ Fin 1 × Fin W := (Equiv.uniqueProd (Fin W) (Fin 1)).symm

theorem jfx_block_submatrix (E : ℝ) {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ)
    (ν : LayerSample W .oneBlockOnePort) :
    (jfx_block E X ν).submatrix (jfx_e W) (jfx_e W) = ν.1 0 - (E : ℂ) • 1 - X := by
  ext x y
  simp [jfx_block, BlockBand.Internal.Contracts.Layers.blockDiag, one_apply, Fin.default_eq_zero]

theorem jfx_det_block (E : ℝ) {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ)
    (ν : LayerSample W .oneBlockOnePort) :
    (jfx_block E X ν).det = (ν.1 0 - (E : ℂ) • 1 - X).det := by
  rw [← jfx_block_submatrix, det_submatrix_equiv_self]

/-- Deterministic port-block identity. If `A - E - X` is invertible, the port block of the
fresh layer resolvent is the passive resolvent of the outgoing Schur matrix:
`𝒢_{port,port}(X, ν) = (z - X₊)⁻¹`, `X₊ = freshSchur E X ν = B*(A - E - X)⁻¹B`. -/
theorem jfx_freshPortBlock_eq (b E : ℝ) {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ)
    (ν : LayerSample W .oneBlockOnePort) (hM : IsUnit (jfx_block E X ν).det) :
    cec_freshPortBlock b E X ν = passiveResolvent b E (freshSchur E X ν) := by
  set S := layerSchur .oneBlockOnePort E (Matrix.of fun (u v : Fin 1 × Fin W) => X u.2 v.2) ν
  have hS : freshSchur E X ν = S.submatrix (jfx_e W) (jfx_e W) := by
    ext x y
    simp [freshSchur, S, Fin.default_eq_zero]
  have hR : passiveResolvent b E (freshSchur E X ν) =
      (boundaryZ b E • (1 : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ) - S)⁻¹.submatrix
        (jfx_e W) (jfx_e W) := by
    have h1 : (boundaryZ b E • (1 : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ) - S).submatrix
        (jfx_e W) (jfx_e W) = boundaryZ b E • 1 - S.submatrix (jfx_e W) (jfx_e W) := by
      ext x y
      simp [one_apply]
    rw [passiveResolvent, hS, ← h1, inv_submatrix_equiv]
  have hB := jfx_inv_fromBlocks_toBlocks22 (jfx_block E X ν)
    (bondMatrix .oneBlockOnePort ν.2) (bondMatrix .oneBlockOnePort ν.2)ᴴ
    (boundaryZ b E • (1 : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ)) hM
  rw [hR]
  ext x y
  have := congrFun (congrFun hB (0, x)) (0, y)
  simp only [toBlocks₂₂, of_apply] at this
  simp only [cec_freshPortBlock, freshLayer, layerResolvent, layerMatrix, of_apply,
    submatrix_apply]
  exact this

/-!
## Almost-sure invertibility of `A - c` under the GUE law
-/

section GUE

open BlockBand.Internal.Contracts.CoareaPalm BlockBand.SourceProcess BlockBand.Parameters

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The entry `(a, c)` of `gueSample t (circularBrownianCoordinates r)` as a complex polynomial
in the real coordinates `r`. -/
def jfx_entryPoly (t : ℝ≥0) (a c : ι) : MvPolynomial ((ι × ι) × Fin 2) ℂ :=
  MvPolynomial.C ((Real.sqrt ((t : ℝ) / 2) : ℂ) / (Real.sqrt 2 : ℂ)) *
    ((MvPolynomial.X ((a, c), 0) + MvPolynomial.C Complex.I * MvPolynomial.X ((a, c), 1)) +
      (MvPolynomial.X ((c, a), 0) - MvPolynomial.C Complex.I * MvPolynomial.X ((c, a), 1)))

omit [Fintype ι] [DecidableEq ι] in
theorem jfx_eval_entryPoly (t : ℝ≥0) (a c : ι) (r : (ι × ι) × Fin 2 → ℝ) :
    MvPolynomial.eval (fun i => (r i : ℂ)) (jfx_entryPoly t a c) =
      gueSample t (circularBrownianCoordinates r) a c := by
  simp [jfx_entryPoly, gueSample, circularBrownianCoordinates, map_div₀]
  ring

theorem jfx_eval_detPoly (t : ℝ≥0) (c₀ : Matrix ι ι ℂ) (r : (ι × ι) × Fin 2 → ℝ) :
    MvPolynomial.eval (fun i => (r i : ℂ))
        (Matrix.of fun a c => jfx_entryPoly t a c - MvPolynomial.C (c₀ a c)).det =
      (gueSample t (circularBrownianCoordinates r) - c₀).det := by
  rw [RingHom.map_det]
  congr 1
  ext a c
  simp [RingHom.mapMatrix_apply, jfx_eval_entryPoly]

/-- Some real shift `l` makes `l - c₀` invertible (the characteristic polynomial has finitely
many roots). -/
theorem jfx_exists_real_det_ne_zero (c₀ : Matrix ι ι ℂ) :
    ∃ l : ℝ, ((l : ℂ) • (1 : Matrix ι ι ℂ) - c₀).det ≠ 0 := by
  have hfin : {l : ℝ | ((l : ℂ) • (1 : Matrix ι ι ℂ) - c₀).det = 0}.Finite := by
    refine ((Polynomial.finite_setOfPred_isRoot c₀.charpoly_monic.ne_zero).preimage
      Complex.ofReal_injective.injOn).subset ?_
    intro l hl
    simp only [Set.mem_ofPred_eq] at hl
    rw [Set.mem_preimage, Set.mem_ofPred_eq, Polynomial.IsRoot, Matrix.eval_charpoly,
      Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
    exact hl
  obtain ⟨l, hl⟩ := hfin.exists_notMem
  exact ⟨l, hl⟩

omit [Fintype ι] in
/-- The witness coordinates: `gueSample t` of them is `l • 1`. -/
theorem jfx_gueSample_witness {t : ℝ≥0} (ht : 0 < t) (l : ℝ) :
    gueSample t (circularBrownianCoordinates
      (fun i : (ι × ι) × Fin 2 => if i.1.1 = i.1.2 ∧ i.2 = 0 then l / Real.sqrt t else 0)) =
      (l : ℂ) • (1 : Matrix ι ι ℂ) := by
  have ht' : (0 : ℝ) < t := ht
  have hst : 0 < Real.sqrt (t : ℝ) := Real.sqrt_pos.2 ht'
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have key : Real.sqrt ((t : ℝ) / 2) * (l / Real.sqrt t / Real.sqrt 2 +
      l / Real.sqrt t / Real.sqrt 2) = l := by
    rw [Real.sqrt_div ht'.le]
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    field_simp
    rw [h2]
    ring
  ext a c
  by_cases hac : a = c
  · subst hac
    simp only [gueSample, circularBrownianCoordinates, of_apply, Matrix.smul_apply, and_true,
      ite_true]
    have e := congrArg (fun x : ℝ => (x : ℂ)) key
    push_cast at e ⊢
    simpa [map_div₀] using e
  · simp [gueSample, circularBrownianCoordinates, hac, Ne.symm hac, one_apply]

/-- `A - c₀` is a.s. invertible under `GUE_ι(t)`, `t > 0`, for every deterministic `c₀`:
`det(A - c₀)` is a complex polynomial in the nondegenerate real Gaussian coordinates of `A`,
nonzero at `A = l • 1`, so its zero set is Lebesgue-null (`volume_mvPolynomial_zeroSet_fintype`)
and hence null for the absolutely continuous Gaussian product law. -/
theorem jfx_ae_gue_det_ne_zero {t : ℝ≥0} (ht : 0 < t) (c₀ : Matrix ι ι ℂ) :
    ∀ᵐ A ∂gueMeasure ι t, (A - c₀).det ≠ 0 := by
  have hcirc : Measurable (circularBrownianCoordinates (ι := ι)) := by
    unfold circularBrownianCoordinates; fun_prop
  have hg : Measurable (gueSample (ι := ι) t) := by unfold gueSample; fun_prop
  have hset : MeasurableSet {A : Matrix ι ι ℂ | (A - c₀).det ≠ 0} :=
    (isClosed_eq ((continuous_id.sub continuous_const).matrix_det)
      continuous_const).isOpen_compl.measurableSet
  unfold gueMeasure commonCircularIncrementLaw
  rw [Measure.map_map hg hcirc, ae_map_iff (hg.comp hcirc).aemeasurable hset]
  refine Measure.AbsolutelyContinuous.ae_le (pi_absolutelyContinuous_volume _
    fun _ => gaussianReal_absolutelyContinuous 0 one_ne_zero) ?_
  set P := (Matrix.of fun a c => jfx_entryPoly t a c - MvPolynomial.C (c₀ a c)).det
  obtain ⟨l, hl⟩ := jfx_exists_real_det_ne_zero c₀
  set r₀ : (ι × ι) × Fin 2 → ℝ :=
    fun i => if i.1.1 = i.1.2 ∧ i.2 = 0 then l / Real.sqrt t else 0
  have h0 : MvPolynomial.eval (fun i => (r₀ i : ℂ)) P ≠ 0 := by
    rw [jfx_eval_detPoly, jfx_gueSample_witness ht]
    exact hl
  have hQ : mvPolynomialNormSq P ≠ 0 := by
    intro h
    apply h0
    have e := eval_mvPolynomialNormSq P r₀
    rw [h, map_zero] at e
    exact Complex.normSq_eq_zero.1 e.symm
  refine ae_iff.2 ?_
  refine measure_mono_null ?_ (volume_mvPolynomial_zeroSet_fintype _ hQ)
  intro r hr
  simp only [Set.mem_ofPred_eq, not_not, Function.comp_apply] at hr ⊢
  rw [eval_mvPolynomialNormSq, jfx_eval_detPoly, hr, map_zero]

end GUE

/-!
## The almost-sure identity
-/

/-- Under the fresh one-port layer law, `A - E - X` is a.s. invertible (`b < 1/2`, `W ≥ 1`, every
real `E`, every deterministic `X`): `A ~ GUE_W((1-2b)/W)` with positive variance. -/
theorem jfx_ae_isUnit_block {b : ℝ} (hb : b < 1 / 2) {W : ℕ} (hW : 0 < W) (E : ℝ)
    (X : Matrix (Fin W) (Fin W) ℂ) : ∀ᵐ ν ∂freshLaw W b, IsUnit (jfx_block E X ν).det := by
  set t := Real.toNNReal ((1 - 2 * b) / W)
  have ht : 0 < t := Real.toNNReal_pos.2 (div_pos (by linarith) (Nat.cast_pos.2 hW))
  have hA := jfx_ae_gue_det_ne_zero ht ((E : ℂ) • (1 : Matrix (Fin W) (Fin W) ℂ) + X)
  have i1 : ∀ _ : Fin 1, IsProbabilityMeasure
      (BlockBand.Internal.Contracts.CoareaPalm.gueMeasure (Fin W) t) :=
    fun _ => passDeriv_isProbabilityMeasure_gue _ _
  have i2 : ∀ _ : Fin 1, ∀ _ : Fin 1, IsProbabilityMeasure
      (ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))) :=
    fun _ _ => passDeriv_isProbabilityMeasure_ginibre _ _ _
  have h1 := (measurePreserving_eval
    (fun _ : Fin 1 => BlockBand.Internal.Contracts.CoareaPalm.gueMeasure (Fin W) t)
      0).quasiMeasurePreserving.ae hA
  have h2 := (Measure.quasiMeasurePreserving_fst (μ := Measure.pi fun _ : Fin 1 =>
    BlockBand.Internal.Contracts.CoareaPalm.gueMeasure (Fin W) t)
      (ν := Measure.pi fun _ : Fin 1 => Measure.pi fun _ : Fin 1 =>
        ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W)))).ae h1
  filter_upwards [h2] with ν hν
  rw [isUnit_iff_ne_zero, jfx_det_block, sub_sub]
  exact hν

/-- **The almost-sure bridge**: for `b < 1/2`, `W ≥ 1`, every real `E` and every
deterministic old input `X`, for `freshLaw W b`-a.e. fresh one-port layer `ν`,
`cec_freshPortBlock b E X ν = passiveResolvent b E (freshSchur E X ν)`, i.e. the port block of
the fresh layer resolvent `𝒢_{port,port}` is `(z - X₊)⁻¹` with
`X₊ = freshSchur E X ν = B*(A - E - X)⁻¹B` (`cec_passiveResolvent_succ` along the path).
-/
theorem cec_freshPortBlock_ae_eq_passiveResolvent_freshSchur {b : ℝ} (hb : b < 1 / 2) {W : ℕ}
    (hW : 0 < W) (E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    ∀ᵐ ν ∂freshLaw W b, cec_freshPortBlock b E X ν = passiveResolvent b E (freshSchur E X ν) := by
  filter_upwards [jfx_ae_isUnit_block hb hW E X] with ν hν
  exact jfx_freshPortBlock_eq b E X ν hν

/-- **The almost-sure bridge, scalar form**: the jet `δ_{0,+} = cec_freshJet0 b E X ν` (read
from the fresh layer resolvent) equals `δ₀(X₊) = jetDistance0 b E (freshSchur E X ν)` for
`freshLaw W b`-a.e. `ν` (`b < 1/2`, `W ≥ 1`, every real `E`, every deterministic `X`).
-/
theorem cec_freshJet0_ae_eq_jetDistance0_freshSchur {b : ℝ} (hb : b < 1 / 2) {W : ℕ}
    (hW : 0 < W) (E : ℝ) (X : Matrix (Fin W) (Fin W) ℂ) :
    ∀ᵐ ν ∂freshLaw W b, cec_freshJet0 b E X ν = jetDistance0 b E (freshSchur E X ν) := by
  filter_upwards [cec_freshPortBlock_ae_eq_passiveResolvent_freshSchur hb hW E X] with ν hν
  rw [cec_freshJet0, jetDistance0, hν]

open BlockBand.Internal.Contracts.TransmissionUniform2 in

/-- **One-port input (c), fixed-moment form**: `PassiveScalarContractionContract` implies
`OnePortJetContractionFixed`. At `b`, `E ∈ (-2, 2)` and a stationary jet `s`: the bulk margin `κ = min(E+2, 2-E)` puts `E` in
`bulkInterval κ`; the jet radius is the `d₀`, so `cel_InJetDomain b E s d₀ X` gives
passivity and `δ₀(X) ≤ d₀`; the fluctuation is `ξ = ‖scalarFluct b E X ·‖`; the width threshold is
`max W₀ 1`; the order-`r` constants are those of the `fluct` field at `(b, κ, r)`.
The
a.s. contraction is the every-sample bound of the contract, transported by
`cec_freshJet0_ae_eq_jetDistance0_freshSchur`.
The stationary jet `s` and the bounds on `δ₁` and
on the conductance in the jet domain are not used.
-/
theorem onePortJetContractionFixed_of_contracts (h : PassiveScalarContractionContract) :
    OnePortJetContractionFixed := by
  intro b hb0 hb' E hE hE' s _
  set κ := min (E + 2) (2 - E) with hκdef
  have hκ : 0 < κ := lt_min (by linarith) (by linarith)
  have hEκ : E ∈ bulkInterval κ :=
    ⟨by have := min_le_left (E + 2) (2 - E); linarith,
      by have := min_le_right (E + 2) (2 - E); linarith⟩
  obtain ⟨d₀, ρ, C, W₀, hd₀, hρ0, hρ1, hC, hcon⟩ := h.contraction b hb0 hb' κ hκ
  have hfl : ∀ r : ℝ, ∃ (Cr : ℝ) (Wr : ℕ), 1 ≤ r → ∀ W : ℕ, Wr ≤ W →
      ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
        eLpNorm (scalarFluct b E X) (ENNReal.ofReal r) (freshLaw W b) ≤
          ENNReal.ofReal (Cr / W) := by
    intro r
    by_cases hr : 1 ≤ r
    · obtain ⟨Cr, Wr, -, hW⟩ := h.fluct b hb0 hb' κ hκ r hr
      exact ⟨Cr, Wr, fun _ W hWr X hX => hW W hWr E hEκ X hX⟩
    · exact ⟨0, 0, fun h1 => absurd h1 hr⟩
  choose Cr Wr hCr using hfl
  refine ⟨ρ, C, d₀, max W₀ 1, Cr, Wr, hρ0, hρ1, hC, hd₀, fun W hW X hX => ?_⟩
  have hW0 : W₀ ≤ W := le_trans (le_max_left _ _) hW
  have hW1 : 0 < W := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hW)
  obtain ⟨hint, -, hbd⟩ := hcon W hW0 E hEκ X hX.1 hX.2.1
  refine ⟨fun ν => ‖scalarFluct b E X ν‖, hint.aestronglyMeasurable.norm, ?_, ?_⟩
  · filter_upwards [cec_freshJet0_ae_eq_jetDistance0_freshSchur hb' hW1 E X] with ν hν
    rw [hν, abs_norm]
    exact hbd ν
  · intro r hr hWr
    rw [eLpNorm_norm _ hint.aestronglyMeasurable]
    exact hCr r hr W hWr X hX.1

end BlockBand.Endpoints
