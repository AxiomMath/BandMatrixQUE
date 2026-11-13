module

public import BlockBand.DeterminantScore.ExactScoreDensity
public import BlockBand.DeterminantScore.Statements

/-!
# The exact determinant score

The first display of the determinant score theorem: `∇_v log 𝔷_ℓ(v) = -4 R̄ Q K₀ v` (horizontal
real gradient, `Df[h] = Re(h*∇f)`, `h ⊥ v`).

`exactScore_holds` is exactly the `exact` clause of `DeterminantScoreStatement`: at every `p`,
rank `α`, pair `i`, `s > 0`, measurable pair frame `U`, exterior with `H_R`, `V` Hermitian, real
nonpole `E` and unit `v` with `𝔷_ℓ(v) ≠ 0`, the function `z ↦ log 𝔷_ℓ(z/‖z‖)` is real Fréchet
differentiable at `v` and its derivative on `h ⊥ v` is `Re(h* score)`, `score = -4 U_vR̄U_v* Q K₀ v`.
The hypotheses `s > 0` and `det(H_R - E) ≠ 0` are not used by the proof.
`determinantScore_of_moments` assembles `DeterminantScoreStatement` from its `moments` clause.

Proof. `𝔷_ℓ = ofReal 𝔷` with `𝔷 = pairAngularDensity` (`detFactor_eq_ofReal`), which is `C¹` and
scale invariant off `0`; so `log 𝔷_ℓ ∘ normalize = log 𝔷` near `v` and the derivative is
`L = 𝔷(v)⁻¹ D𝔷(v)`. `𝔷(v) > 0` forces `N_-(H_R - E) ≤ α`, so `𝔷` is the generic
`angularDensity` in the sector `ℓ = α - N_-(H_R - E)`, and
`angularDensity_fderiv_horizontal` (in the given frame `U_v`) gives
`D𝔷(v)[h] = -4 Re((U_v*h)* S (U_v*K₀v))`, `S = E[1 det² R]`. Finally `R̄ = condInverse = S/𝔷(v)`
(`condInverse_eq`: the `G_{d-1}(t)` matrix law is the image of the coordinate law,
`map_hermOfCoord_hermGaussian`, and `|det M|² = det(M)²`), and `U_v*Q = U_v*`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.ExactScore

open MeasureTheory Matrix Filter
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Angular.FiberAngular BlockBand.Angular.DetFactor BlockBand.DeterminantScore.Sector
open scoped NNReal Topology ENNReal Matrix.Norms.L2Operator

/-!
## The conditional inverse as a normalized inverse moment
-/

theorem measurable_inv_apply {κ : Type} [Fintype κ] [DecidableEq κ] (a c : κ) :
    Measurable fun M : Matrix κ κ ℂ => M⁻¹ a c := by
  have h : (fun M : Matrix κ κ ℂ => M⁻¹ a c) = fun M => (M.det)⁻¹ * M.adjugate a c := by
    funext M
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  rw [h]
  exact (measurable_inv.comp continuous_id.matrix_det.measurable).mul
    (continuous_id.matrix_adjugate.matrix_elem a c).measurable

/-- The integrand `|det M|² 1{N_-(M) + N = α} (M⁻¹)_{ac}` of `R̄`. -/
def sectorInvIntegrand {κ : Type} [Fintype κ] [DecidableEq κ] (α N : ℕ) (a c : κ)
    (M : Matrix κ κ ℂ) : ℂ :=
  ((Complex.normSq M.det * (if negativeCount M + N = α then 1 else 0) : ℝ) : ℂ) * M⁻¹ a c

theorem measurable_sectorInvIntegrand {κ : Type} [Fintype κ] [DecidableEq κ] (α N : ℕ)
    (a c : κ) : Measurable (sectorInvIntegrand α N a c) := by
  unfold sectorInvIntegrand
  refine Measurable.mul (Complex.measurable_ofReal.comp (Measurable.mul ?_
    (Measurable.ite ?_ measurable_const measurable_const))) (measurable_inv_apply a c)
  · exact (Complex.continuous_normSq.comp continuous_id.matrix_det).measurable
  · exact (measurableSet_singleton _).preimage (measurable_negativeCount_nat.add_const N)

variable {p : BlockBand.Parameters} {i : ZMod p.n}

/-- **`R̄ = S/𝔷(v)`**: the conditional inverse is the unnormalized inverse moment
`S = E[1{N_-=ℓ} det² R]` (frame coordinates of `U_v`, `ℓ = α - N_-(H_R - E)`) divided by
`𝔷(v)`. -/
theorem condInverse_eq (α : Fin p.N) (s : ℝ) {U : FrameMap p i} (hU : IsPairFrame p i U)
    {om : SplitState p i} (hR : om.1.IsHermitian) (hV : om.2.2.IsHermitian) (E : ℝ)
    {v : PairSite p i → ℂ} (hv : l2Norm v = 1)
    (hN : negativeCount (om.1 - (E : ℂ) • 1) ≤ α.val) :
    condInverse α s U (om, E, v) =
      (((pairAngularDensity p i α s om E v)⁻¹ : ℝ) : ℂ) •
        sectorInvMoment (2 * p.W - 1) (pairTime p s) ((U v)ᴴ * pairK p i om E * U v)
          (α.val - negativeCount (om.1 - (E : ℂ) • 1)) := by
  set N := negativeCount (om.1 - (E : ℂ) • 1)
  set A : Matrix (Fin (2 * p.W - 1)) (Fin (2 * p.W - 1)) ℂ := (U v)ᴴ * pairK p i om E * U v
  have hA : A.IsHermitian := isHermitian_conjTranspose_mul_mul _ (pairK_isHermitian p i hR hV E)
  have hZ : sectorZ α s U (om, E, v) = pairAngularDensity p i α s om E v := by
    rw [sectorZ, detFactor_eq_ofReal p i α s hU hR hV E hv,
      ENNReal.toReal_ofReal (pairAngularDensity_nonneg α s hR hV E v)]
  ext a c
  have hfun : (fun G' => (sectorWeight α U (om, E, v) G' : ℂ) * (outerM U (om, E, v) G')⁻¹ a c) =
      fun G' => sectorInvIntegrand α.val N a c (A + G') := by
    funext G'
    simp only [sectorWeight, outerM, frameM_eq_compress p i hU _ E hv]
    rfl
  have hint : (∫ G', (sectorWeight α U (om, E, v) G' : ℂ) * (outerM U (om, E, v) G')⁻¹ a c
      ∂gueMeasure (FrameIndex p) (pairTime p s)) =
      ∫ x, sectorDetSqInv A (α.val - N) a c x ∂hermGaussian (2 * p.W - 1) (pairTime p s) := by
    rw [hfun, ← map_hermOfCoord_hermGaussian,
      integral_map (f := fun G' => sectorInvIntegrand α.val N a c (A + G'))
      continuous_hermOfCoord.measurable.aemeasurable
      ((measurable_sectorInvIntegrand α.val N a c).comp
        (measurable_const_add A)).aestronglyMeasurable]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    have him := det_im_eq_zero (hA.add (isHermitian_hermOfCoord x))
    simp only [sectorInvIntegrand, sectorDetSqInv, InSector]
    by_cases hx : negativeCount (A + hermOfCoord x) = α.val - N
    · simp only [hx, Nat.sub_add_cancel hN, ↓reduceIte, mul_one]
      rw [Complex.normSq_eq_conj_mul_self, Complex.conj_eq_iff_im.2 him, pow_two]
    · have hl : ¬ negativeCount (A + hermOfCoord x) + N = α.val := by omega
      simp [hl, hx]
  simp only [condInverse, sectorAvgMat, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, hZ,
    sectorInvMoment]
  rw [hint]
  push_cast
  ring

/-- `h* (U_v X U_v*) Q y = (U_v*h)* X (U_v*y)` (`U_v*Q = U_v*`). -/
theorem dotProduct_embedFrame {U : FrameMap p i} {v : PairSite p i → ℂ}
    (hU0 : (U v)ᴴ *ᵥ v = 0) (X : FrameMatrix p) (h y : PairSite p i → ℂ) :
    star h ⬝ᵥ (embedFrame U v X *ᵥ (orthProj v *ᵥ y)) =
      star ((U v)ᴴ *ᵥ h) ⬝ᵥ (X *ᵥ ((U v)ᴴ *ᵥ y)) := by
  have hQ : (U v)ᴴ * orthProj v = (U v)ᴴ := by
    rw [orthProj, Matrix.mul_sub, Matrix.mul_one, mul_vecMulVec, hU0, zero_vecMulVec, sub_zero]
  rw [embedFrame, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_mulVec y (U v)ᴴ (orthProj v), hQ,
    dotProduct_mulVec, star_mulVec, conjTranspose_conjTranspose]

/-!
## The exact clause
-/

/-- **The exact determinant score**: the `exact` clause of `DeterminantScoreStatement`. -/
theorem exactScore_holds : ∀ (p : BlockBand.Parameters) (α : Fin p.N) (i : ZMod p.n) (s : ℝ),
    0 < s → ∀ U : FrameMap p i, IsPairFrame p i U →
    ∀ om : SplitState p i, om.1.IsHermitian → om.2.2.IsHermitian →
    ∀ E : ℝ, (om.1 - (E : ℂ) • 1).det ≠ 0 →
    ∀ v : PairSite p i → ℂ, l2Norm v = 1 → detFactor p i α s U om E v ≠ 0 →
      ∃ L : (PairSite p i → ℂ) →L[ℝ] ℝ,
        HasFDerivAt (fun z => Real.log (detFactor p i α s U om E (normalize z)).toReal) L v ∧
        ∀ h : PairSite p i → ℂ, star h ⬝ᵥ v = 0 →
          L h = (star h ⬝ᵥ score α s U (om, E, v)).re := by
  intro p α i s _ U hU om hR hV E _ v hv hz
  set Z := pairAngularDensity p i α s om E with hZdef
  have hZv : 0 < Z v := by
    rw [detFactor_eq_ofReal p i α s hU hR hV E hv] at hz
    refine lt_of_le_of_ne (pairAngularDensity_nonneg α s hR hV E v) fun h0 => hz ?_
    rw [show pairAngularDensity p i α s om E v = 0 from h0.symm, ENNReal.ofReal_zero]
  set N := negativeCount (om.1 - (E : ℂ) • 1)
  have hN : N ≤ α.val := by
    by_contra hN
    apply hZv.ne'
    rw [hZdef, pairAngularDensity]
    split_ifs with h
    · exact absurd h hN
    · rfl
  have hZeq : Z = angularDensity (2 * p.W - 1) (pairTime p s) (α.val - N) (pairK p i om E) := by
    funext z
    rw [hZdef, pairAngularDensity]
    split_ifs with h
    · rfl
    · exact absurd hN h
  have hv0 : v ≠ 0 := by
    rintro rfl
    simp [l2Norm] at hv
  have hopen : {z : PairSite p i → ℂ | z ≠ 0} ∈ 𝓝 v := isOpen_ne.mem_nhds hv0
  have hdiff : DifferentiableAt ℝ Z v :=
    ((contDiffOn_pairAngularDensity α s hR hV E).differentiableOn one_ne_zero).differentiableAt
      hopen
  have hD : HasFDerivAt Z (fderiv ℝ Z v) v := hdiff.hasFDerivAt
  have hf : (fun z => Real.log (detFactor p i α s U om E (normalize z)).toReal) =ᶠ[𝓝 v]
      fun z => Real.log (Z z) := by
    filter_upwards [hopen] with z hz0
    have hzpos : 0 < l2Norm z := by
      obtain ⟨j₀, hj⟩ := exists_patch hz0
      exact l2Norm_pos_of_apply j₀ hj
    have hnz : l2Norm (normalize z) = 1 := by
      rw [Angular.FiberAngular.normalize, l2Norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hzpos.le,
        inv_mul_cancel₀ hzpos.ne']
    rw [detFactor_eq_ofReal p i α s hU hR hV E hnz,
      ENNReal.toReal_ofReal (pairAngularDensity_nonneg α s hR hV E _)]
    have hsm : normalize z = (l2Norm z)⁻¹ • z := by
      rw [Angular.FiberAngular.normalize, ← Complex.coe_smul]
      push_cast
      rfl
    rw [hsm, isScaleInvariant_pairAngularDensity α s hR hV E z _ (inv_pos.2 hzpos)]
  refine ⟨(Z v)⁻¹ • fderiv ℝ Z v, (hD.log hZv.ne').congr_of_eventuallyEq hf, fun h hhv => ?_⟩
  have hD' : HasFDerivAt (angularDensity (2 * p.W - 1) (pairTime p s) (α.val - N)
      (pairK p i om E)) (fderiv ℝ Z v) v := hZeq ▸ hD
  have hvv : star v ⬝ᵥ v = 1 := by
    rw [star_dotProduct_self_eq, ← l2Norm_sq, hv]
    simp
  change (Z v)⁻¹ * fderiv ℝ Z v h = _
  rw [angularDensity_fderiv_horizontal (card_pairSite_eq p i) (pairTime p s)
      (pairK_isHermitian p i hR hV E) (α.val - N) (hU.2 v hv) hvv hD' hhv,
    score, condInverse_eq α s hU hR hV E hv hN, dotProduct_smul,
    dotProduct_embedFrame (hU.2 v hv).2, Matrix.smul_mulVec, dotProduct_smul,
    show outerK0 (om, E, v) = pairK p i om E from rfl, smul_eq_mul, smul_eq_mul]
  rw [show (-4 : ℂ) * ((((Z v)⁻¹ : ℝ) : ℂ) * (star ((U v)ᴴ *ᵥ h) ⬝ᵥ
      (sectorInvMoment (2 * p.W - 1) (pairTime p s) ((U v)ᴴ * pairK p i om E * U v) (α.val - N) *ᵥ
        ((U v)ᴴ *ᵥ (pairK p i om E *ᵥ v))))) =
      (((-4 * (Z v)⁻¹) : ℝ) : ℂ) * (star ((U v)ᴴ *ᵥ h) ⬝ᵥ
      (sectorInvMoment (2 * p.W - 1) (pairTime p s) ((U v)ᴴ * pairK p i om E * U v) (α.val - N) *ᵥ
        ((U v)ᴴ *ᵥ (pairK p i om E *ᵥ v)))) by push_cast; ring, Complex.re_ofReal_mul]
  ring

/-- `DeterminantScoreStatement` from its `moments` clause (the `exact` clause is
`exactScore_holds`). -/
theorem determinantScore_of_moments
    (hm : ∀ b T ϑ κ r : ℝ, 0 < ϑ → 0 < κ → 0 < r → r < 2 → ∃ C : ℝ,
      ∀ p : BlockBand.Parameters, p.b = b → (p.n : ℝ) ≤ T * (p.W : ℝ) →
      ∀ (model : p.GaussianRingModel) (α : Fin p.N), IsBulkRank p ϑ α →
      ∀ (i : ZMod p.n) (Pω : Measure (SplitState p i)), IsPairSplitting p i model (splitS p) Pω →
      ∀ U : FrameMap p i, IsPairFrame p i U →
        pairExpect α (splitS p) U Pω (fun θ _ =>
            (bulkInterval κ).indicator 1 θ.2.1 *
              ENNReal.ofReal (‖condInverse α (splitS p) U θ‖ ^ r +
                l2Norm (score α (splitS p) U θ) ^ r)) ≤
          ENNReal.ofReal C) :
    DeterminantScoreStatement :=
  ⟨exactScore_holds, hm⟩

end BlockBand.DeterminantScore.ExactScore
