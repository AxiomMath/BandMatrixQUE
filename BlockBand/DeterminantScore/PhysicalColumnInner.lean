module

public import BlockBand.DeterminantScore.PhysicalColumnGaussian
public import BlockBand.DeterminantScore.Statements
public import BlockBand.Angular.ProjectiveStein

/-!
# The physical column: the inner (fixed outer data) bounds

At fixed outer data `θ = (ω, E, v)` with Hermitian blocks: `M = K_θ + G'`,
`K_θ = U_v*F(E)U_v - E` Hermitian (`outerM_eq`, `outerKs_isHermitian`), and
* `inner_col`: for `‖x‖ ≤ 1`,
  `E_{G'}[det² 1{sector α}‖M⁻¹x‖^q] ≤ t^{-q/2}C_{2,q} Σ_{ℓ=α-1}^{α+1} E_{G'}[det² 1{sector ℓ}]`
  (`gue_core` after normalizing `x`);
* `inner_hs`: the same with `‖M⁻¹‖_HS^q` and the extra factor `(d-1)^{q/2}`, from
  `‖R‖_HS^q ≤ (d-1)^{q/2-1} Σ_a ‖Re_a‖^q` (`invHS_rpow_le`, power-mean inequality).
* `l2Norm_conjTranspose_mulVec_le`: `‖U*w‖ ≤ ‖w‖` for orthonormal columns.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.PhysicalColumn

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Angular.FiberAngular BlockBand.DeterminantScore.Sector
open BlockBand.DeterminantScore.GaussianGradient
open scoped ENNReal NNReal

/-!
## Vector norms
-/

section Norms

variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem ofReal_sum_norm_sq (y : ι → ℂ) : ((∑ k, ‖y k‖ ^ 2 : ℝ) : ℂ) = star y ⬝ᵥ y := by
  simp only [dotProduct, Pi.star_apply, RCLike.star_def]
  push_cast
  exact Finset.sum_congr rfl fun k _ => (Complex.conj_mul' (y k)).symm

theorem l2Norm_mulVec_isometry {V : Matrix ι κ ℂ} (hV : Vᴴ * V = 1) (z : κ → ℂ) :
    l2Norm (V *ᵥ z) = l2Norm z := by
  have h : (∑ k, ‖(V *ᵥ z) k‖ ^ 2 : ℝ) = ∑ k, ‖z k‖ ^ 2 := by
    apply Complex.ofReal_injective
    rw [ofReal_sum_norm_sq, ofReal_sum_norm_sq, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec,
      hV, one_mulVec]
  unfold l2Norm; rw [h]

theorem l2Norm_nonneg' (z : ι → ℂ) : 0 ≤ l2Norm z := Real.sqrt_nonneg _

theorem l2Norm_sq' (z : ι → ℂ) : l2Norm z ^ 2 = ∑ k, ‖z k‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)

/-- Cauchy–Schwarz for `y* w`. -/
theorem norm_star_dotProduct_le (y w : ι → ℂ) : ‖star y ⬝ᵥ w‖ ≤ l2Norm y * l2Norm w := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 y : EuclideanSpace ℂ ι)
    (WithLp.toLp 2 w)
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.norm_eq,
    EuclideanSpace.norm_eq] at h
  rw [dotProduct_comm]
  exact h

/-- `‖U*w‖ ≤ ‖w‖` for a matrix with orthonormal columns. -/
theorem l2Norm_conjTranspose_mulVec_le {V : Matrix ι κ ℂ} (hV : Vᴴ * V = 1) (w : ι → ℂ) :
    l2Norm (Vᴴ *ᵥ w) ≤ l2Norm w := by
  set y := Vᴴ *ᵥ w
  have hy : (l2Norm y : ℂ) ^ 2 = star (V *ᵥ y) ⬝ᵥ w := by
    rw [← Complex.ofReal_pow, l2Norm_sq', ofReal_sum_norm_sq]
    have e1 : star (V *ᵥ y) = star y ᵥ* Vᴴ := star_mulVec _ _
    rw [e1, ← dotProduct_mulVec]
  have h1 : l2Norm y ^ 2 ≤ l2Norm y * l2Norm w := by
    have h2 := norm_star_dotProduct_le (V *ᵥ y) w
    rw [← hy, l2Norm_mulVec_isometry hV, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (l2Norm_nonneg' y)] at h2
    exact h2
  by_cases h0 : l2Norm y = 0
  · rw [h0]; exact l2Norm_nonneg' w
  · have hpos : 0 < l2Norm y := lt_of_le_of_ne (l2Norm_nonneg' y) (Ne.symm h0)
    nlinarith

theorem l2Norm_single (a : ι) : l2Norm (Pi.single a (1 : ℂ)) = 1 := by
  unfold l2Norm
  rw [Finset.sum_eq_single a (fun b _ hb => by simp [hb]) (by simp)]
  simp

end Norms

/-!
## Outer data
-/

variable {p : Parameters} {i : ZMod p.n}

theorem frameIndex_neZero (p : Parameters) : NeZero (2 * p.W - 1) :=
  ⟨by have := p.W_pos; omega⟩

/-- `N_-(H_R - E)`. -/
def nR (θ : OuterData p i) : ℕ := negativeCount (θ.1.1 - (θ.2.1 : ℂ) • 1)

/-- `K_θ = U_v*F(E)U_v - E`. -/
def outerKs (U : FrameMap p i) (θ : OuterData p i) : FrameMatrix p :=
  (U θ.2.2)ᴴ * physicalCoareaF θ.1.1 θ.1.2.1 θ.1.2.2 θ.2.1 * U θ.2.2 - (θ.2.1 : ℂ) • 1

theorem outerM_eq (U : FrameMap p i) (θ : OuterData p i) (G' : FrameMatrix p) :
    outerM U θ G' = outerKs U θ + G' := by
  unfold outerM frameM outerKs; abel

theorem outerKs_isHermitian (U : FrameMap p i) {θ : OuterData p i} (hR : θ.1.1.IsHermitian)
    (hV : θ.1.2.2.IsHermitian) : (outerKs U θ).IsHermitian := by
  refine (isHermitian_conjTranspose_mul_mul _
    (physicalCoareaF_isHermitian hR θ.1.2.1 hV θ.2.1)).sub ?_
  unfold IsHermitian; rw [conjTranspose_smul, conjTranspose_one]; simp

theorem sectorWeight_eq (α : Fin p.N) (U : FrameMap p i) (θ : OuterData p i)
    (G' : FrameMatrix p) : sectorWeight α U θ G' = secW (nR θ) α.val (outerM U θ G') := rfl

/-- The sector-`ℓ` determinant mass at `θ` (`ℓ ∈ ℕ`). -/
def zNat (s : ℝ) (U : FrameMap p i) (ℓ : ℕ) (θ : OuterData p i) : ℝ≥0∞ :=
  ∫⁻ G', ENNReal.ofReal (secW (nR θ) ℓ (outerM U θ G')) ∂gueMeasure (FrameIndex p) (pairTime p s)

theorem isProbabilityMeasure_gue (ι : Type) [Fintype ι] (t : ℝ≥0) :
    IsProbabilityMeasure (gueMeasure ι t) := by
  unfold gueMeasure BlockBand.SourceProcess.commonCircularIncrementLaw
  infer_instance

/-!
## The inner bounds
-/

/-- **Inner column bound** at fixed `θ` (Hermitian blocks, `‖x‖ ≤ 1`). -/
theorem inner_col (s : ℝ) (U : FrameMap p i) {θ : OuterData p i} (hR : θ.1.1.IsHermitian)
    (hV : θ.1.2.2.IsHermitian) (ht : 0 < pairTime p s) {q : ℝ} (hq2 : 2 ≤ q) (hq3 : q < 3)
    {x : FrameIndex p → ℂ} (hx : l2Norm x ≤ 1) (α : Fin p.N) :
    (∫⁻ G', ENNReal.ofReal (sectorWeight α U θ G') *
        ENNReal.ofReal (l2Norm ((outerM U θ G')⁻¹ *ᵥ x) ^ q)
        ∂gueMeasure (FrameIndex p) (pairTime p s)) ≤
      ENNReal.ofReal ((((pairTime p s : ℝ))⁻¹) ^ (q / 2) * gaussianGradientConstant 2 q) *
        (zNat s U (α.val - 1) θ + zNat s U α.val θ + zNat s U (α.val + 1) θ) := by
  have := frameIndex_neZero p
  have hK := outerKs_isHermitian U hR hV
  simp only [zNat, sectorWeight_eq, outerM_eq]
  by_cases hx0 : x = 0
  · subst hx0
    refine le_trans (le_of_eq ?_) (zero_le)
    refine lintegral_eq_zero_of_ae_eq_zero (Filter.Eventually.of_forall fun G => ?_)
    have hq0 : q ≠ 0 := by linarith
    simp [mulVec_zero, l2Norm, Real.zero_rpow hq0]
  set r := l2Norm x
  have hr : 0 < r := by
    have h := (l2Norm_le_one_smul hx0).2
    by_contra hle
    have h0 : r = 0 := le_antisymm (not_lt.mp hle) (l2Norm_nonneg' x)
    rw [show l2Norm x = r from rfl, h0, _root_.inv_zero, Complex.ofReal_zero, zero_smul] at h
    simp [l2Norm] at h
  obtain ⟨hxeq, hxu⟩ := l2Norm_le_one_smul hx0
  set xh := (((l2Norm x)⁻¹ : ℝ) : ℂ) • x
  have hpt : ∀ G : FrameMatrix p, ENNReal.ofReal (l2Norm ((outerKs U θ + G)⁻¹ *ᵥ x) ^ q) ≤
      ENNReal.ofReal (l2Norm ((outerKs U θ + G)⁻¹ *ᵥ xh) ^ q) := by
    intro G
    refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (l2Norm_nonneg' _) ?_ (by linarith))
    conv_lhs => rw [hxeq]
    rw [mulVec_smul, l2Norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    exact mul_le_of_le_one_left (l2Norm_nonneg' _) hx
  calc _ ≤ ∫⁻ G', ENNReal.ofReal (secW (nR θ) α.val (outerKs U θ + G')) *
        ENNReal.ofReal (l2Norm ((outerKs U θ + G')⁻¹ *ᵥ xh) ^ q)
        ∂gueMeasure (FrameIndex p) (pairTime p s) :=
        lintegral_mono fun G => mul_le_mul_right (hpt G) _
    _ ≤ _ := gue_core hK ht hq2 hq3 hxu (nR θ) α.val

/-- `‖R‖_HS^q ≤ (d-1)^{q/2-1} Σ_a ‖Re_a‖^q`. -/
theorem invHS_rpow_le (U : FrameMap p i) (θ : OuterData p i) (G' : FrameMatrix p) {q : ℝ}
    (hq2 : 2 ≤ q) :
    invHS U θ G' ^ q ≤ ((2 * p.W - 1 : ℕ) : ℝ) ^ (q / 2 - 1) *
      ∑ a : FrameIndex p, l2Norm ((outerM U θ G')⁻¹ *ᵥ Pi.single a 1) ^ q := by
  set R := (outerM U θ G')⁻¹
  have hcol : ∀ a : FrameIndex p, l2Norm (R *ᵥ Pi.single a 1) ^ 2 = ∑ c, ‖R c a‖ ^ 2 := by
    intro a
    rw [l2Norm_sq']
    refine Finset.sum_congr rfl fun c _ => ?_
    simp [mulVec, dotProduct, Pi.single_apply]
  have hS : (∑ a, ∑ c, ‖R a c‖ ^ 2) = ∑ c, l2Norm (R *ᵥ Pi.single c 1) ^ 2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => (hcol c).symm
  have hq1 : 1 ≤ q / 2 := by linarith
  have hpow := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (s := Finset.univ)
    (f := fun c : FrameIndex p => l2Norm (R *ᵥ Pi.single c 1) ^ 2) hq1
    (fun c _ => by positivity)
  rw [Finset.card_univ, Fintype.card_fin] at hpow
  have hinv : invHS U θ G' ^ q = (∑ c, l2Norm (R *ᵥ Pi.single c 1) ^ 2) ^ (q / 2) := by
    unfold invHS
    rw [hS, Real.sqrt_eq_rpow, ← Real.rpow_mul (Finset.sum_nonneg fun _ _ => by positivity)]
    ring_nf
  rw [hinv]
  refine hpow.trans (le_of_eq ?_)
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Real.rpow_natCast, ← Real.rpow_mul (l2Norm_nonneg' _)]
  push_cast; ring_nf

theorem measurable_inv_matrix {κ : Type} [Fintype κ] [DecidableEq κ] :
    Measurable fun M : Matrix κ κ ℂ => M⁻¹ :=
  measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun c =>
    ExactScore.measurable_inv_apply a c

/-- **Inner HS bound** at fixed `θ`. -/
theorem inner_hs (s : ℝ) (U : FrameMap p i) {θ : OuterData p i} (hR : θ.1.1.IsHermitian)
    (hV : θ.1.2.2.IsHermitian) (ht : 0 < pairTime p s) {q : ℝ} (hq2 : 2 ≤ q) (hq3 : q < 3)
    (α : Fin p.N) :
    (∫⁻ G', ENNReal.ofReal (sectorWeight α U θ G') * ENNReal.ofReal (invHS U θ G' ^ q)
        ∂gueMeasure (FrameIndex p) (pairTime p s)) ≤
      ENNReal.ofReal (((2 * p.W - 1 : ℕ) : ℝ) ^ (q / 2) *
          ((((pairTime p s : ℝ))⁻¹) ^ (q / 2) * gaussianGradientConstant 2 q)) *
        (zNat s U (α.val - 1) θ + zNat s U α.val θ + zNat s U (α.val + 1) θ) := by
  set m : ℝ := ((2 * p.W - 1 : ℕ) : ℝ)
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  set B := zNat s U (α.val - 1) θ + zNat s U α.val θ + zNat s U (α.val + 1) θ
  set C₁ := (((pairTime p s : ℝ))⁻¹) ^ (q / 2) * gaussianGradientConstant 2 q
  have hcm : Measurable fun G' : FrameMatrix p => outerM U θ G' := by
    simp only [outerM_eq]; exact measurable_const_add _
  have hmeas : ∀ a : FrameIndex p, Measurable fun G' : FrameMatrix p =>
      ENNReal.ofReal (sectorWeight α U θ G') *
        ENNReal.ofReal (l2Norm ((outerM U θ G')⁻¹ *ᵥ Pi.single a 1) ^ q) := fun a =>
    (ENNReal.measurable_ofReal.comp ((measurable_secW _ _).comp hcm)).mul
      ((measurable_colTerm _ q).comp hcm)
  have hpt : ∀ G' : FrameMatrix p, ENNReal.ofReal (sectorWeight α U θ G') *
      ENNReal.ofReal (invHS U θ G' ^ q) ≤
      ENNReal.ofReal (m ^ (q / 2 - 1)) * ∑ a : FrameIndex p, ENNReal.ofReal (sectorWeight α U θ G') *
        ENNReal.ofReal (l2Norm ((outerM U θ G')⁻¹ *ᵥ Pi.single a 1) ^ q) := by
    intro G'
    rw [← Finset.mul_sum, mul_left_comm]
    refine mul_le_mul_right ?_ _
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => by
      exact Real.rpow_nonneg (l2Norm_nonneg' _) _), ← ENNReal.ofReal_mul
      (Real.rpow_nonneg hm0 _)]
    exact ENNReal.ofReal_le_ofReal (invHS_rpow_le U θ G' hq2)
  have hcol : ∀ a : FrameIndex p, (∫⁻ G', ENNReal.ofReal (sectorWeight α U θ G') *
      ENNReal.ofReal (l2Norm ((outerM U θ G')⁻¹ *ᵥ Pi.single a 1) ^ q)
      ∂gueMeasure (FrameIndex p) (pairTime p s)) ≤ ENNReal.ofReal C₁ * B := fun a =>
    inner_col s U hR hV ht hq2 hq3 (le_of_eq (l2Norm_single a)) α
  calc _ ≤ ∫⁻ G', ENNReal.ofReal (m ^ (q / 2 - 1)) * ∑ a : FrameIndex p,
        ENNReal.ofReal (sectorWeight α U θ G') *
          ENNReal.ofReal (l2Norm ((outerM U θ G')⁻¹ *ᵥ Pi.single a 1) ^ q)
        ∂gueMeasure (FrameIndex p) (pairTime p s) := lintegral_mono hpt
    _ = ENNReal.ofReal (m ^ (q / 2 - 1)) * ∑ a : FrameIndex p, ∫⁻ G',
        ENNReal.ofReal (sectorWeight α U θ G') *
          ENNReal.ofReal (l2Norm ((outerM U θ G')⁻¹ *ᵥ Pi.single a 1) ^ q)
        ∂gueMeasure (FrameIndex p) (pairTime p s) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_finsetSum _ fun a _ => hmeas a]
    _ ≤ ENNReal.ofReal (m ^ (q / 2 - 1)) * ∑ _a : FrameIndex p, ENNReal.ofReal C₁ * B := by
        gcongr with a; exact hcol a
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
          ← mul_assoc]
        congr 1
        have hm : ((2 * p.W - 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal m := by simp [m]
        rw [hm, ← ENNReal.ofReal_mul (Real.rpow_nonneg hm0 _), ← ENNReal.ofReal_mul
          (by positivity)]
        congr 1
        have hm1 : 1 ≤ m := by
          have := p.W_pos
          simp only [m]; exact_mod_cast (by omega : 1 ≤ 2 * p.W - 1)
        rw [show m ^ (q / 2) = m ^ (q / 2 - 1) * m by
          rw [← Real.rpow_add_one (by linarith)]; ring_nf]

end BlockBand.DeterminantScore.PhysicalColumn
