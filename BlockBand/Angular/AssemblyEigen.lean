module

public import BlockBand.Angular.Assembly
public import BlockBand.Angular.StepTwoGlue
public import BlockBand.Coarea.SchurReconstruction

/-!
# The eigenvalue equation bounds `b₂`

`pairEigenB2` proves `Assembly.PairEigenB2Statement`: if `Hψ = Eψ`, the residual `H - G_e` is
Hermitian and `H_R - E` is invertible, then the block equations of `Hψ = Eψ` give
`(F(E) - E + G_e)ψ_S = 0` (`Coarea.physical_schur_eigenvector_equation`), so
`K₀ψ_S = -G_eψ_S` and `b₂ = ‖K₀ψ_S‖²/‖ψ_S‖² ≤ ‖G_e‖²` (`K₀` Hermitian). With it,
`physicalAngularLabel_of` needs only the good part, the two Gaussian tails and the pole
exclusion.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Angular.Assembly

open MeasureTheory Matrix BlockBand.Model.Construction
open BlockBand.Internal.Contracts.QUE BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Layers BlockBand.QUE.PhysicalAngularReduction
open BlockBand.Angular.ProjectiveStein BlockBand.DeterminantScore.GUENormTail
open scoped ComplexConjugate Matrix.Norms.L2Operator

theorem quadQuot_sq_le {ι : Type} [Fintype ι] [DecidableEq ι] {K G : Matrix ι ι ℂ}
    (hK : K.IsHermitian) {z : ι → ℂ} (hKz : K *ᵥ z = -(G *ᵥ z)) :
    quadQuot (K * K) z ≤ ‖G‖ ^ 2 := by
  unfold quadQuot
  by_cases hz : z = 0
  · subst hz
    simp only [Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero, Complex.zero_re]
    rw [zero_div]; positivity
  have hpos : 0 < normSqSum z := normSqSum_pos hz
  have hnum : (∑ a, conj (z a) * ((K * K) *ᵥ z) a).re = l2Norm (G *ᵥ z) ^ 2 := by
    have h1 : (∑ a, conj (z a) * ((K * K) *ᵥ z) a) = star z ⬝ᵥ (K *ᵥ (K *ᵥ z)) := by
      rw [← Matrix.mulVec_mulVec]; rfl
    have h2 : star z ᵥ* K = star (K *ᵥ z) := by rw [Matrix.star_mulVec, hK.eq]
    rw [h1, Matrix.dotProduct_mulVec, h2, hKz]
    rw [BlockBand.Angular.FiberAngular.l2Norm_sq_eq]
    simp only [dotProduct, Pi.star_apply, Pi.neg_apply, star_neg, neg_mul, mul_neg, neg_neg,
      Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_comm]
    change ((G *ᵥ z) a * conj ((G *ᵥ z) a)).re = _
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hden : normSqSum z = l2Norm z ^ 2 := (BlockBand.Angular.FiberAngular.l2Norm_sq_eq z).symm
  rw [hnum, hden, div_le_iff₀ (by rw [← hden]; exact hpos)]
  have := BlockBand.Angular.StepTwoGlue.l2Norm_mulVec_le_opNorm G z
  have h0 : 0 ≤ l2Norm (G *ᵥ z) := Real.sqrt_nonneg _
  calc l2Norm (G *ᵥ z) ^ 2 ≤ (‖G‖ * l2Norm z) ^ 2 := pow_le_pow_left₀ h0 this 2
    _ = ‖G‖ ^ 2 * l2Norm z ^ 2 := by ring

/-- **`K₀ψ_S = -G_eψ_S` gives `b₂ ≤ ‖G_e‖²`**. -/
theorem pairEigenB2 : PairEigenB2Statement := by
  intro p i H G hherm E ψ heig hdet
  set Hres := H - embedPair p i G with hHres
  set ψS : PairSite p i → ℂ := fun x => ψ x.1
  set ψR : ExteriorSite p i → ℂ := fun x => ψ x.1
  have hext : exteriorBlock p i Hres = exteriorBlock p i H := exteriorBlock_sub_embedPair p i H G
  have hdet' : (exteriorBlock p i Hres - (E : ℂ) • 1).det ≠ 0 := by rwa [hext]
  have hrow : ∀ x, ∑ y, H x y * ψ y = (E : ℂ) * ψ x := fun x => by
    have := congrFun heig x
    simpa [Matrix.mulVec, dotProduct] using this
  have hHx : ∀ x y, H x y = Hres x y + embedPair p i G x y := fun x y => by
    simp [hHres]
  have hExterior : couplingBlock p i Hres *ᵥ ψS +
      (exteriorBlock p i Hres - (E : ℂ) • 1) *ᵥ ψR = 0 := by
    funext x
    have h := hrow x.1
    rw [← Fintype.sum_subtype_add_sum_subtype (fun y : p.Site => y.1 = i ∨ y.1 = i + 1)] at h
    have hx := x.2
    have hR' : ∀ y, H x.1 y = Hres x.1 y := fun y => by rw [hHx]; simp [embedPair, hx]
    simp only [hR'] at h
    simp only [Pi.add_apply, Pi.zero_apply, Matrix.sub_mulVec, Pi.sub_apply,
      Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul]
    simp only [Matrix.mulVec, dotProduct, couplingBlock, exteriorBlock, ψS, ψR]
    rw [← h]; ring
  have hPair : (pairBlock p i Hres + G - (E : ℂ) • 1) *ᵥ ψS +
      (couplingBlock p i Hres)ᴴ *ᵥ ψR = 0 := by
    funext x
    have h := hrow x.1
    rw [← Fintype.sum_subtype_add_sum_subtype (fun y : p.Site => y.1 = i ∨ y.1 = i + 1)] at h
    have hx := x.2
    have hC : ∀ y : ExteriorSite p i, (couplingBlock p i Hres)ᴴ x y = Hres x.1 y.1 := fun y => by
      rw [Matrix.conjTranspose_apply]
      unfold couplingBlock
      exact (hherm.apply x.1 y.1)
    simp only [Pi.add_apply, Pi.zero_apply, Matrix.sub_mulVec, Matrix.add_mulVec, Pi.sub_apply,
      Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul]
    simp only [Matrix.mulVec, dotProduct, hC]
    have hS : ∀ y : PairSite p i, H x.1 y.1 = pairBlock p i Hres x y + G x y := fun y => by
      rw [hHx]; simp [embedPair, pairBlock, x.2, y.2]
    have hR : ∀ y : ExteriorSite p i, H x.1 y.1 = Hres x.1 y.1 := fun y => by
      rw [hHx]; simp [embedPair, y.2]
    simp only [hS, hR] at h
    rw [Finset.sum_congr rfl fun y _ => (add_mul (pairBlock p i Hres x y) (G x y) (ψ y.1))] at h
    rw [Finset.sum_add_distrib] at h
    simp only [ψS, ψR]
    linear_combination h
  have hA := BlockBand.Coarea.physical_schur_eigenvector_equation (exteriorBlock p i Hres)
    (couplingBlock p i Hres) (pairBlock p i Hres) G E hdet' ψS ψR hExterior hPair
  have hK : edgeSchur p i Hres E *ᵥ ψS = -(G *ᵥ ψS) := by
    unfold BlockBand.Coarea.physicalCoareaA at hA
    unfold edgeSchur
    refine eq_neg_of_add_eq_zero_left ?_
    rw [← Matrix.add_mulVec]
    convert hA using 2
    abel
  have hKh : (edgeSchur p i Hres E).IsHermitian :=
    BlockBand.Angular.FirstMoment.sub_real_smul_one_isHermitian
      (BlockBand.Angular.FiberAngular.physicalCoareaF_isHermitian
        (BlockBand.Angular.FirstMoment.exteriorBlock_isHermitian p i hherm) _
        (BlockBand.Angular.FirstMoment.pairBlock_isHermitian p i hherm) E) E
  exact quadQuot_sq_le hKh hK

/-- **The physical angular estimate** `PhysicalAngularLabel` for `0 < ϑ`, from the good part,
the `GUE` norm tail, the pair-row norm tail and the pole exclusion `PairPoleExclusionContract`
(the eigenvalue-equation bound is `pairEigenB2`). -/
theorem physicalAngularLabel_of {b θ T : ℝ} (hb : 0 < b) (hb' : b < 1 / 2) (hθ : 0 < θ)
    (hGood : GoodPartStatement b (min θ (1 / 4)) T hb hb') (hTail : GUENormTailStatement)
    (hRow : PairRowNormTailStatement) (hPole : PairPoleExclusionContract) :
    PhysicalAngularLabel b θ T hb hb' :=
  physicalAngularLabel_of_parts hb hb' hθ hGood pairEigenB2 hTail hRow hPole

end BlockBand.Angular.Assembly
