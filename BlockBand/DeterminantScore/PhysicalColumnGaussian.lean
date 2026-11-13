module

public import BlockBand.DeterminantScore.PhysicalColumnInertia
public import BlockBand.DeterminantScore.PhysicalColumnPolynomial
public import BlockBand.DeterminantScore.Sector.GUELaw
public import BlockBand.DeterminantScore.ExactScore
public import BlockBand.Angular.ConeDivergenceComplex

/-!
# The whole-row Gaussian bound at fixed outer data

For a Hermitian `K` on `Fin m` (`m ≠ 0`), `G ~ GUE_m(t)` (`CoareaPalm.gueMeasure`), `t > 0`, a
unit vector `x`, `n, α ∈ ℕ` and `2 ≤ q < 3` (`gue_core`):
`E[det(K+G)² 1{N_-(K+G) + n = α} ‖(K+G)⁻¹x‖^q]
   ≤ t^{-q/2} C_{2,q} Σ_{ℓ ∈ {α-1, α, α+1}} E[det(K+G)² 1{N_-(K+G) + n = ℓ}]`,
`C_{2,q} = gaussianGradientConstant 2 q` of the Gaussian polynomial gradient lemma.

Proof: rotate `x` to `e₀` (unitary invariance, `DetFactor.map_unitaryCoord_hermGaussian`), whiten
the coordinates and split them into the row touching `0` and the rest
(`lintegral_hermGaussian_row`); for fixed remaining coordinates `P = Re det` is a real polynomial
of degree `≤ 2` in the row (`rowPoly`), `det² ‖M⁻¹e₀‖^q ≤ t^{-q/2}‖∇P‖^q|P|^{2-q}`
(`gradient_lower_bound`), and the Gaussian lemma (`GaussianGradient.lintegral_gradientWeighted_le`)
bounds the row integral by `C E_row P²`; the selected inertia is dropped in the numerator only; if
the sector `α` is attained at some row value, every row value lies in one of the three neighbouring
sectors (`sector_neighbour`), which restores the three sector weights.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.PhysicalColumn

open MeasureTheory ProbabilityTheory Matrix MvPolynomial
open BlockBand.Internal.Contracts BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.DeterminantScore.Sector BlockBand.DeterminantScore.GaussianGradient
open BlockBand.Angular.DetFactor
open scoped NNReal ENNReal

/-!
## The sector weight
-/

/-- `det(M)² 1{N_-(M) + n = ℓ}` (as `|det M|²`). -/
def secW {κ : Type} [Fintype κ] [DecidableEq κ] (n ℓ : ℕ) (M : Matrix κ κ ℂ) : ℝ :=
  Complex.normSq M.det * (if negativeCount M + n = ℓ then 1 else 0)

theorem secW_nonneg {κ : Type} [Fintype κ] [DecidableEq κ] (n ℓ : ℕ) (M : Matrix κ κ ℂ) :
    0 ≤ secW n ℓ M := by
  unfold secW; split_ifs <;> simp [Complex.normSq_nonneg]

theorem measurable_secW {κ : Type} [Fintype κ] [DecidableEq κ] (n ℓ : ℕ) :
    Measurable (secW (κ := κ) n ℓ) := by
  unfold secW
  refine Measurable.mul ?_ (Measurable.ite ?_ measurable_const measurable_const)
  · exact (Complex.continuous_normSq.comp continuous_id.matrix_det).measurable
  · exact (measurableSet_singleton _).preimage (measurable_negativeCount_nat.add_const n)

theorem measurable_inv_mulVec {κ : Type} [Fintype κ] [DecidableEq κ] (x : κ → ℂ) :
    Measurable fun M : Matrix κ κ ℂ => M⁻¹ *ᵥ x := by
  refine measurable_pi_iff.mpr fun a => ?_
  simp only [mulVec, dotProduct]
  exact Finset.measurable_sum _ fun b _ => (ExactScore.measurable_inv_apply a b).mul_const _

theorem measurable_colTerm {κ : Type} [Fintype κ] [DecidableEq κ] (x : κ → ℂ) (q : ℝ) :
    Measurable fun M : Matrix κ κ ℂ => ENNReal.ofReal (l2Norm (M⁻¹ *ᵥ x) ^ q) :=
  ENNReal.measurable_ofReal.comp
    ((BlockBand.Angular.ConeDivergence.measurable_l2Norm.comp
      (measurable_inv_mulVec x)).pow_const q)

/-!
## Whitening and the row split
-/

variable {m : ℕ}

/-- The coordinate standard deviations. -/
def hermSd (m : ℕ) (t : ℝ≥0) (c : HermCoord m) : ℝ := Real.sqrt (hermVariance m t c)

theorem hermGaussian_eq_map (t : ℝ≥0) :
    hermGaussian m t = (standardGaussianCoordinates (ι := HermCoord m)).map
      (fun y c => hermSd m t c * y c) := by
  unfold standardGaussianCoordinates
  rw [Measure.pi_map_pi (fun c => (measurable_const_mul (hermSd m t c)).aemeasurable)]
  unfold hermGaussian Inputs.gaussianProduct
  congr 1
  funext c
  rw [gaussianReal_map_const_mul, mul_zero]
  congr 1
  ext
  simp only [NNReal.coe_mk, mul_one, hermSd]
  exact (Real.sq_sqrt (NNReal.coe_nonneg _)).symm

variable [NeZero m]

/-- **Whitened row split** of the `G_m(t)` coordinate law. -/
theorem lintegral_hermGaussian_row (t : ℝ≥0) (F : (HermCoord m → ℝ) → ℝ≥0∞)
    (hF : Measurable F) :
    (∫⁻ y, F y ∂hermGaussian m t) =
      ∫⁻ w, ∫⁻ u, F (rowPoint (hermSd m t) u w)
        ∂standardGaussianCoordinates (ι := RowIdx m)
        ∂standardGaussianCoordinates (ι := RestIdx m) := by
  rw [hermGaussian_eq_map, lintegral_map hF (measurable_pi_iff.mpr fun c =>
    (measurable_pi_apply c).const_mul _)]
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : HermCoord m => ℝ) IsRow
  have hmp := measurePreserving_piEquivPiSubtypeProd (fun _ : HermCoord m => gaussianReal 0 1)
    IsRow
  unfold standardGaussianCoordinates
  rw [← (hmp.symm e).lintegral_comp_emb e.symm.measurableEmbedding]
  rw [lintegral_prod_symm' (fun z => F fun c => hermSd m t c * e.symm z c)
    ((hF.comp (measurable_pi_iff.mpr fun c =>
    (measurable_pi_apply c).const_mul _)).comp e.symm.measurable)]
  rfl

/-!
## The row bound
-/

/-- Pointwise: `det² ‖M⁻¹e₀‖^q ≤ t^{-q/2}‖∇P‖^q|P|^{2-q}` (zero at a singular point). -/
theorem pointwise_row_bound {K : Matrix (Fin m) (Fin m) ℂ} (hK : K.IsHermitian) {t : ℝ≥0}
    (ht : 0 < t) {q : ℝ} (hq2 : 2 ≤ q) (u : RowIdx m → ℝ) (w : RestIdx m → ℝ) :
    Complex.normSq (K + hermOfCoord (rowPoint (hermSd m t) u w)).det *
        l2Norm ((K + hermOfCoord (rowPoint (hermSd m t) u w))⁻¹ *ᵥ Pi.single 0 1) ^ q ≤
      ((t : ℝ)⁻¹) ^ (q / 2) *
        gradientWeighted (rowPoly K (hermSd m t) w) q (WithLp.toLp 2 u) := by
  set M := K + hermOfCoord (rowPoint (hermSd m t) u w) with hMdef
  have hMH : M.IsHermitian := hK.add (isHermitian_hermOfCoord _)
  have hgw0 : 0 ≤ gradientWeighted (rowPoly K (hermSd m t) w) q (WithLp.toLp 2 u) :=
    gradientWeighted_nonneg _ _ _
  by_cases hdet : M.det = 0
  · rw [hdet, Complex.normSq_zero, zero_mul]
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) hgw0
  have hgrad := gradient_lower_bound hK t u w hdet
  set P := eval u (rowPoly K (hermSd m t) w)
  have hP : P = M.det.re := eval_rowPoly K _ u w
  have him := det_im_eq_zero hMH
  have hns : Complex.normSq M.det = P ^ 2 := by
    rw [Complex.normSq_apply, him, hP]; ring
  set S := ∑ a, ‖M⁻¹ a 0‖ ^ 2
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => by positivity
  have hl2 : l2Norm (M⁻¹ *ᵥ Pi.single 0 1) = Real.sqrt S := by
    unfold l2Norm
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [mulVec, dotProduct, Pi.single_apply]
  set g := ‖polynomialGradient (rowPoly K (hermSd m t) w) u‖
  have hgw : gradientWeighted (rowPoly K (hermSd m t) w) q (WithLp.toLp 2 u) =
      g ^ q * |P| ^ (2 - q) := by
    unfold gradientWeighted euclideanPolynomialGradient polynomialValue
    rw [Real.norm_eq_abs]
  have hPne : P ≠ 0 := by
    intro h0; apply hdet
    apply Complex.ext
    · rw [← hP, h0]; rfl
    · rw [him]; rfl
  have ha : 0 < |P| := abs_pos.mpr hPne
  have htpos : (0 : ℝ) < t := ht
  rw [hns, hl2, hgw]
  -- `P² (√S)^q = |P|^{2-q} (P² S)^{q/2}` and `(P² S)^{q/2} ≤ (t⁻¹ g²)^{q/2}`.
  have hq0 : 0 ≤ q / 2 := by linarith
  have h1 : Real.sqrt S ^ q = S ^ (q / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hS0]; ring_nf
  have h2 : P ^ 2 = |P| ^ (2 - q) * (P ^ 2) ^ (q / 2) := by
    rw [← sq_abs P, ← Real.rpow_natCast |P| 2, ← Real.rpow_mul (abs_nonneg P),
      ← Real.rpow_add ha]
    congr 1; push_cast; ring
  have hgrad' : (t : ℝ) * P ^ 2 * S ≤ g ^ 2 := hgrad
  have h3 : (P ^ 2 * S) ≤ (t : ℝ)⁻¹ * g ^ 2 := by
    rw [le_inv_mul_iff₀ htpos, ← mul_assoc]; exact hgrad'
  have h4 : (P ^ 2 * S) ^ (q / 2) ≤ ((t : ℝ)⁻¹ * g ^ 2) ^ (q / 2) :=
    Real.rpow_le_rpow (by positivity) h3 hq0
  have h5 : ((t : ℝ)⁻¹ * g ^ 2) ^ (q / 2) = ((t : ℝ)⁻¹) ^ (q / 2) * g ^ q := by
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast g 2,
      ← Real.rpow_mul (norm_nonneg _)]
    congr 2; push_cast; ring
  rw [h1, h2, mul_assoc, ← Real.mul_rpow (by positivity) hS0]
  calc |P| ^ (2 - q) * (P ^ 2 * S) ^ (q / 2)
      ≤ |P| ^ (2 - q) * (((t : ℝ)⁻¹) ^ (q / 2) * g ^ q) := by
        rw [← h5]; exact mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = _ := by ring

/-- Measurability of the whitened row point. -/
theorem measurable_rowPoint_left (t : ℝ≥0) (w : RestIdx m → ℝ) :
    Measurable fun u : RowIdx m → ℝ => rowPoint (hermSd m t) u w := by
  refine measurable_pi_iff.mpr fun c => ?_
  unfold rowPoint
  split_ifs with h
  · exact (measurable_pi_apply _).const_mul _
  · exact measurable_const

/-- **Row bound** at fixed remaining coordinates `w`: the selected-sector column moment is at
most `t^{-q/2}C_{2,q}` times the three neighbouring sector weights. -/
theorem row_bound {K : Matrix (Fin m) (Fin m) ℂ} (hK : K.IsHermitian) {t : ℝ≥0} (ht : 0 < t)
    {q : ℝ} (hq2 : 2 ≤ q) (hq3 : q < 3) (n α : ℕ) (w : RestIdx m → ℝ) :
    (∫⁻ u, ENNReal.ofReal (secW n α (K + hermOfCoord (rowPoint (hermSd m t) u w))) *
        ENNReal.ofReal (l2Norm ((K + hermOfCoord (rowPoint (hermSd m t) u w))⁻¹ *ᵥ
          Pi.single 0 1) ^ q) ∂standardGaussianCoordinates (ι := RowIdx m)) ≤
      ENNReal.ofReal (((t : ℝ)⁻¹) ^ (q / 2) * gaussianGradientConstant 2 q) *
        ∫⁻ u, (ENNReal.ofReal (secW n (α - 1) (K + hermOfCoord (rowPoint (hermSd m t) u w))) +
          ENNReal.ofReal (secW n α (K + hermOfCoord (rowPoint (hermSd m t) u w))) +
          ENNReal.ofReal (secW n (α + 1) (K + hermOfCoord (rowPoint (hermSd m t) u w))))
          ∂standardGaussianCoordinates (ι := RowIdx m) := by
  set Mu := fun u : RowIdx m → ℝ => K + hermOfCoord (rowPoint (hermSd m t) u w) with hMu
  set P := rowPoly K (hermSd m t) w
  have hMH : ∀ u, (Mu u).IsHermitian := fun u => hK.add (isHermitian_hermOfCoord _)
  by_cases hatt : ∃ u₀, negativeCount (Mu u₀) + n = α
  swap
  · simp only [not_exists, hMu] at hatt
    refine le_trans (le_of_eq ?_) (zero_le)
    refine lintegral_eq_zero_of_ae_eq_zero (Filter.Eventually.of_forall fun u => ?_)
    simp [secW, hatt u]
  obtain ⟨u₀, hu₀⟩ := hatt
  have hC0 := gaussianGradientConstant_nonneg 2 q hq2 hq3
  have htq : 0 ≤ ((t : ℝ)⁻¹) ^ (q / 2) := Real.rpow_nonneg (by positivity) _
  -- Pointwise bound by the gradient-weighted integrand (inertia dropped).
  have hstep1 : ∀ u, ENNReal.ofReal (secW n α (Mu u)) *
      ENNReal.ofReal (l2Norm ((Mu u)⁻¹ *ᵥ Pi.single 0 1) ^ q) ≤
      ENNReal.ofReal (((t : ℝ)⁻¹) ^ (q / 2)) *
        ENNReal.ofReal (gradientWeighted P q (WithLp.toLp 2 u)) := by
    intro u
    rw [← ENNReal.ofReal_mul (secW_nonneg _ _ _), ← ENNReal.ofReal_mul htq]
    refine ENNReal.ofReal_le_ofReal ?_
    refine le_trans ?_ (pointwise_row_bound hK ht hq2 u w)
    unfold secW
    split_ifs
    · rw [mul_one]
    · rw [mul_zero, zero_mul]
      exact mul_nonneg (Complex.normSq_nonneg _) (Real.rpow_nonneg (by
        unfold l2Norm; exact Real.sqrt_nonneg _) _)
  -- The Gaussian lemma on the row.
  have hmeasToLp : Measurable (WithLp.toLp 2 : (RowIdx m → ℝ) → EuclideanSpace ℝ (RowIdx m)) :=
    (PiLp.continuous_toLp 2 (fun _ : RowIdx m => ℝ)).measurable
  have hstep2 : (∫⁻ u, ENNReal.ofReal (gradientWeighted P q (WithLp.toLp 2 u))
      ∂standardGaussianCoordinates (ι := RowIdx m)) ≤
      ENNReal.ofReal (gaussianGradientConstant 2 q) *
        ∫⁻ u, ENNReal.ofReal (eval u P ^ 2) ∂standardGaussianCoordinates (ι := RowIdx m) := by
    have h := lintegral_gradientWeighted_le P 2 q (totalDegree_rowPoly_le K _ w) hq2 hq3
    have e1 : (∫⁻ x, ENNReal.ofReal (gradientWeighted P q x)
        ∂(standardGaussianCoordinates (ι := RowIdx m)).map (WithLp.toLp 2)) =
        ∫⁻ u, ENNReal.ofReal (gradientWeighted P q (WithLp.toLp 2 u))
          ∂standardGaussianCoordinates (ι := RowIdx m) :=
      lintegral_map (ENNReal.measurable_ofReal.comp (measurable_gradientWeighted P q)) hmeasToLp
    have e2 : (∫⁻ x, ENNReal.ofReal (polynomialValue P x ^ 2)
        ∂(standardGaussianCoordinates (ι := RowIdx m)).map (WithLp.toLp 2)) =
        ∫⁻ u, ENNReal.ofReal (eval u P ^ 2) ∂standardGaussianCoordinates (ι := RowIdx m) := by
      rw [lintegral_map (f := fun x => ENNReal.ofReal (polynomialValue P x ^ 2))
        (ENNReal.measurable_ofReal.comp (((continuous_polynomialValue P).pow 2).measurable))
        hmeasToLp]
      rfl
    rw [← standardGaussianCoordinates_toLp, e1, e2] at h
    exact h
  -- On an attained sector every row value lies in a neighbouring sector.
  have hstep3 : ∀ u, ENNReal.ofReal (eval u P ^ 2) ≤
      ENNReal.ofReal (secW n (α - 1) (Mu u)) + ENNReal.ofReal (secW n α (Mu u)) +
        ENNReal.ofReal (secW n (α + 1) (Mu u)) := by
    intro u
    have hP : eval u P = (Mu u).det.re := eval_rowPoly K _ u w
    have him := det_im_eq_zero (hMH u)
    have hns : eval u P ^ 2 = Complex.normSq (Mu u).det := by
      rw [Complex.normSq_apply, him, hP]; ring
    have hagree := hermOfCoord_row_agree K 0 (y := rowPoint (hermSd m t) u₀ w)
      (y' := rowPoint (hermSd m t) u w) (fun c h1 h2 => by
        have hc : ¬ IsRow c := by unfold IsRow; tauto
        simp only [rowPoint, hc, ↓reduceDIte])
    rcases sector_neighbour (hMH u₀) (hMH u) 0 hagree hu₀ with h | h | h
    · rw [hns]
      refine le_trans ?_ (le_add_right (le_add_right le_rfl))
      simp [secW, h]
    · rw [hns]
      refine le_trans ?_ (le_add_right (le_add_left le_rfl))
      simp [secW, h]
    · rw [hns]
      refine le_trans ?_ (le_add_left le_rfl)
      simp [secW, h]
  calc (∫⁻ u, ENNReal.ofReal (secW n α (Mu u)) *
          ENNReal.ofReal (l2Norm ((Mu u)⁻¹ *ᵥ Pi.single 0 1) ^ q)
          ∂standardGaussianCoordinates (ι := RowIdx m))
      ≤ ∫⁻ u, ENNReal.ofReal (((t : ℝ)⁻¹) ^ (q / 2)) *
          ENNReal.ofReal (gradientWeighted P q (WithLp.toLp 2 u))
          ∂standardGaussianCoordinates (ι := RowIdx m) := lintegral_mono hstep1
    _ = ENNReal.ofReal (((t : ℝ)⁻¹) ^ (q / 2)) *
          ∫⁻ u, ENNReal.ofReal (gradientWeighted P q (WithLp.toLp 2 u))
          ∂standardGaussianCoordinates (ι := RowIdx m) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (((t : ℝ)⁻¹) ^ (q / 2)) * (ENNReal.ofReal (gaussianGradientConstant 2 q) *
          ∫⁻ u, (ENNReal.ofReal (secW n (α - 1) (Mu u)) + ENNReal.ofReal (secW n α (Mu u)) +
            ENNReal.ofReal (secW n (α + 1) (Mu u)))
          ∂standardGaussianCoordinates (ι := RowIdx m)) := by
        gcongr
        exact hstep2.trans (by gcongr; exact hstep3 _)
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul htq]

/-!
## The coordinate bound at the basis vector `e₀`
-/

/-- **Coordinate core** at `x = e₀`. -/
theorem coord_core {K : Matrix (Fin m) (Fin m) ℂ} (hK : K.IsHermitian) {t : ℝ≥0} (ht : 0 < t)
    {q : ℝ} (hq2 : 2 ≤ q) (hq3 : q < 3) (n α : ℕ) :
    (∫⁻ y, ENNReal.ofReal (secW n α (K + hermOfCoord y)) *
        ENNReal.ofReal (l2Norm ((K + hermOfCoord y)⁻¹ *ᵥ Pi.single 0 1) ^ q)
        ∂hermGaussian m t) ≤
      ENNReal.ofReal (((t : ℝ)⁻¹) ^ (q / 2) * gaussianGradientConstant 2 q) *
        ((∫⁻ y, ENNReal.ofReal (secW n (α - 1) (K + hermOfCoord y)) ∂hermGaussian m t) +
          (∫⁻ y, ENNReal.ofReal (secW n α (K + hermOfCoord y)) ∂hermGaussian m t) +
          (∫⁻ y, ENNReal.ofReal (secW n (α + 1) (K + hermOfCoord y)) ∂hermGaussian m t)) := by
  have hcont : Continuous fun y : HermCoord m → ℝ => K + hermOfCoord y :=
    continuous_const.add continuous_hermOfCoord
  have hmS : ∀ ℓ, Measurable fun y : HermCoord m → ℝ =>
      ENNReal.ofReal (secW n ℓ (K + hermOfCoord y)) := fun ℓ =>
    ENNReal.measurable_ofReal.comp ((measurable_secW n ℓ).comp hcont.measurable)
  have hmL : Measurable fun y : HermCoord m → ℝ =>
      ENNReal.ofReal (secW n α (K + hermOfCoord y)) *
        ENNReal.ofReal (l2Norm ((K + hermOfCoord y)⁻¹ *ᵥ Pi.single 0 1) ^ q) :=
    (hmS α).mul ((measurable_colTerm _ q).comp hcont.measurable)
  have hm3 : Measurable fun y : HermCoord m → ℝ =>
      ENNReal.ofReal (secW n (α - 1) (K + hermOfCoord y)) +
        ENNReal.ofReal (secW n α (K + hermOfCoord y)) +
        ENNReal.ofReal (secW n (α + 1) (K + hermOfCoord y)) :=
    ((hmS _).add (hmS _)).add (hmS _)
  rw [← lintegral_add_right _ (hmS _), ← lintegral_add_right _ (hmS _),
    lintegral_hermGaussian_row t _ hmL, lintegral_hermGaussian_row t _ hm3,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun w => ?_
  exact row_bound hK ht hq2 hq3 n α w

/-!
## Rotation
-/

omit [NeZero m] in
theorem l2Norm_mulVec_of_unitary {V : Matrix (Fin m) (Fin m) ℂ} (hV : Vᴴ * V = 1)
    (z : Fin m → ℂ) : l2Norm (V *ᵥ z) = l2Norm z := by
  have key : ∀ y : Fin m → ℂ, ((∑ k, ‖y k‖ ^ 2 : ℝ) : ℂ) = star y ⬝ᵥ y := by
    intro y
    simp only [dotProduct, Pi.star_apply, RCLike.star_def]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    exact (Complex.conj_mul' (y k)).symm
  have h : (∑ k, ‖(V *ᵥ z) k‖ ^ 2 : ℝ) = ∑ k, ‖z k‖ ^ 2 := by
    apply Complex.ofReal_injective
    rw [key, key, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hV, one_mulVec]
  unfold l2Norm; rw [h]

omit [NeZero m] in
theorem l2Norm_le_one_smul {x : Fin m → ℂ} (hx : x ≠ 0) :
    x = ((l2Norm x : ℝ) : ℂ) • (((l2Norm x)⁻¹ : ℝ) : ℂ) • x ∧ l2Norm ((((l2Norm x)⁻¹ : ℝ) : ℂ) • x) = 1 := by
  have hpos : 0 < l2Norm x := by
    unfold l2Norm
    apply Real.sqrt_pos.mpr
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hx
    exact lt_of_lt_of_le (by positivity : 0 < ‖x k‖ ^ 2)
      (Finset.single_le_sum (f := fun k => ‖x k‖ ^ 2) (fun _ _ => by positivity)
        (Finset.mem_univ k))
  refine ⟨?_, ?_⟩
  · rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hpos.ne', Complex.ofReal_one, one_smul]
  · rw [BlockBand.Angular.FiberAngular.l2Norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ hpos.ne']

/-- A unitary sending a unit vector to `e₀`. -/
theorem exists_unitary_mulVec {x : Fin m → ℂ} (hx : l2Norm x = 1) :
    ∃ W : Matrix (Fin m) (Fin m) ℂ, Wᴴ * W = 1 ∧ W *ᵥ x = Pi.single 0 1 := by
  set e : EuclideanSpace ℂ (Fin m) := WithLp.toLp 2 x
  have he : ‖e‖ = 1 := by
    rw [EuclideanSpace.norm_eq]; simpa [l2Norm, e] using hx
  have hon : Orthonormal ℂ (({0} : Set (Fin m)).domRestrict fun _ : Fin m => e) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := Subsingleton.elim i j
    subst hij
    simp only [↓reduceIte, inner_self_eq_norm_sq_to_K]
    change ((‖e‖ : ℝ) : ℂ) ^ 2 = 1
    rw [he]; simp
  obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq (by simp)
  have hb0 : b 0 = e := hb 0 rfl
  set V : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun i j => b j i
  have hinner : ∀ i j, (Vᴴ * V) i j = inner ℂ (b i) (b j) := by
    intro i j
    simp only [Matrix.mul_apply, conjTranspose_apply, V, Matrix.of_apply, PiLp.inner_apply,
      RCLike.inner_apply, RCLike.star_def]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hVV : Vᴴ * V = 1 := by
    ext i j
    rw [hinner, orthonormal_iff_ite.mp b.orthonormal i j, Matrix.one_apply]
  refine ⟨Vᴴ, by rw [conjTranspose_conjTranspose]; exact mul_eq_one_comm.mp hVV, ?_⟩
  funext i
  have h1 : (Vᴴ *ᵥ x) i = inner ℂ (b i) (b 0) := by
    rw [hb0]
    simp only [mulVec, dotProduct, conjTranspose_apply, V, Matrix.of_apply, PiLp.inner_apply,
      RCLike.inner_apply, RCLike.star_def, e]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [h1, orthonormal_iff_ite.mp b.orthonormal i 0, Pi.single_apply]

omit [NeZero m] in
/-- `(WᴴAW)⁻¹ = WᴴA⁻¹W` for unitary `W`. -/
theorem inv_unitary_conj (A : Matrix (Fin m) (Fin m) ℂ) {W : Matrix (Fin m) (Fin m) ℂ}
    (hW : Wᴴ * W = 1) : (Wᴴ * A * W)⁻¹ = Wᴴ * A⁻¹ * W := by
  have hW' : W * Wᴴ = 1 := mul_eq_one_comm.mp hW
  have h1 : W⁻¹ = Wᴴ := Matrix.inv_eq_left_inv hW
  have h2 : (Wᴴ)⁻¹ = W := Matrix.inv_eq_left_inv hW'
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, h1, h2, Matrix.mul_assoc]

omit [NeZero m] in
theorem secW_unitary_conj {A W : Matrix (Fin m) (Fin m) ℂ} (hA : A.IsHermitian)
    (hW : Wᴴ * W = 1) (n ℓ : ℕ) : secW n ℓ (Wᴴ * A * W) = secW n ℓ A := by
  unfold secW
  rw [det_unitary_conj _ hW, negativeCount_unitary_conj hA hW]

omit [NeZero m] in
theorem lintegral_hermGaussian_unitary (t : ℝ≥0) {V : Matrix (Fin m) (Fin m) ℂ}
    (hV : Vᴴ * V = 1) (F : Matrix (Fin m) (Fin m) ℂ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ y, F (Vᴴ * hermOfCoord y * V) ∂hermGaussian m t) = ∫⁻ y, F (hermOfCoord y) ∂hermGaussian m t := by
  conv_rhs => rw [← map_unitaryCoord_hermGaussian t hV]
  rw [lintegral_map (f := fun y => F (hermOfCoord y)) (hF.comp continuous_hermOfCoord.measurable)
    (continuous_unitaryCoord V).measurable]
  simp only [hermOfCoord_unitaryCoord]

/-- **The fixed-`θ` whole-row bound** under `GUE_m(t)`: for Hermitian `K`, unit `x`, `t > 0`,
`n, α ∈ ℕ` and `2 ≤ q < 3`. -/
theorem gue_core {K : Matrix (Fin m) (Fin m) ℂ} (hK : K.IsHermitian) {t : ℝ≥0} (ht : 0 < t)
    {q : ℝ} (hq2 : 2 ≤ q) (hq3 : q < 3) {x : Fin m → ℂ} (hx : l2Norm x = 1) (n α : ℕ) :
    (∫⁻ G, ENNReal.ofReal (secW n α (K + G)) * ENNReal.ofReal (l2Norm ((K + G)⁻¹ *ᵥ x) ^ q)
        ∂gueMeasure (Fin m) t) ≤
      ENNReal.ofReal (((t : ℝ)⁻¹) ^ (q / 2) * gaussianGradientConstant 2 q) *
        ((∫⁻ G, ENNReal.ofReal (secW n (α - 1) (K + G)) ∂gueMeasure (Fin m) t) +
          (∫⁻ G, ENNReal.ofReal (secW n α (K + G)) ∂gueMeasure (Fin m) t) +
          (∫⁻ G, ENNReal.ofReal (secW n (α + 1) (K + G)) ∂gueMeasure (Fin m) t)) := by
  obtain ⟨W, hW, hWx⟩ := exists_unitary_mulVec hx
  have hW' : W * Wᴴ = 1 := mul_eq_one_comm.mp hW
  set K' := W * K * Wᴴ
  have hK' : K'.IsHermitian := by
    have := isHermitian_conjTranspose_mul_mul Wᴴ hK
    simpa [K', conjTranspose_conjTranspose, Matrix.mul_assoc] using this
  have hconj : ∀ G, K + Wᴴ * G * W = Wᴴ * (K' + G) * W := by
    intro G
    simp only [K', Matrix.mul_add, Matrix.add_mul]
    congr 1
    rw [show Wᴴ * (W * K * Wᴴ) * W = (Wᴴ * W) * K * (Wᴴ * W) by simp only [Matrix.mul_assoc],
      hW, Matrix.one_mul, Matrix.mul_one]
  have hmS : ∀ ℓ, Measurable fun G : Matrix (Fin m) (Fin m) ℂ =>
      ENNReal.ofReal (secW n ℓ (K + G)) := fun ℓ =>
    ENNReal.measurable_ofReal.comp ((measurable_secW n ℓ).comp (measurable_const_add K))
  have hmL : Measurable fun G : Matrix (Fin m) (Fin m) ℂ =>
      ENNReal.ofReal (secW n α (K + G)) * ENNReal.ofReal (l2Norm ((K + G)⁻¹ *ᵥ x) ^ q) :=
    (hmS α).mul ((measurable_colTerm x q).comp (measurable_const_add K))
  have hsec : ∀ ℓ, (∫⁻ G, ENNReal.ofReal (secW n ℓ (K + G)) ∂gueMeasure (Fin m) t) =
      ∫⁻ y, ENNReal.ofReal (secW n ℓ (K' + hermOfCoord y)) ∂hermGaussian m t := by
    intro ℓ
    rw [← map_hermOfCoord_hermGaussian, lintegral_map (hmS ℓ) continuous_hermOfCoord.measurable,
      ← lintegral_hermGaussian_unitary t hW _ (hmS ℓ)]
    refine lintegral_congr fun y => ?_
    rw [hconj, secW_unitary_conj (hK'.add (isHermitian_hermOfCoord y)) hW]
  have hcol : (∫⁻ G, ENNReal.ofReal (secW n α (K + G)) *
      ENNReal.ofReal (l2Norm ((K + G)⁻¹ *ᵥ x) ^ q) ∂gueMeasure (Fin m) t) =
      ∫⁻ y, ENNReal.ofReal (secW n α (K' + hermOfCoord y)) *
        ENNReal.ofReal (l2Norm ((K' + hermOfCoord y)⁻¹ *ᵥ Pi.single 0 1) ^ q)
        ∂hermGaussian m t := by
    rw [← map_hermOfCoord_hermGaussian, lintegral_map hmL continuous_hermOfCoord.measurable,
      ← lintegral_hermGaussian_unitary t hW _ hmL]
    refine lintegral_congr fun y => ?_
    rw [hconj, secW_unitary_conj (hK'.add (isHermitian_hermOfCoord y)) hW, inv_unitary_conj _ hW,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hWx,
      l2Norm_mulVec_of_unitary (by rw [conjTranspose_conjTranspose]; exact hW')]
  rw [hcol, hsec, hsec, hsec]
  exact coord_core hK' ht hq2 hq3 n α

end BlockBand.DeterminantScore.PhysicalColumn
