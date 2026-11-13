module

public import BlockBand.Angular.ComparisonBasic
public import BlockBand.Angular.SteinForms

/-!
# Coefficient bounds on the cutoff for the angular comparison

At a unit vector `v` with `b₂(v) ≤ R₁` (the support of `χ(b₂)`), with `R = (K₀ - ζ)⁻¹`:
* `jensen`: `1 ≤ (√R₁ + Zb) ‖Rv‖` (from `1 = Re⟨(K₀ - ζ̄)v, Rv⟩`), hence
  `u₀ = s‖Rv‖² ≥ (σ P²)⁻¹`, `P = √R₁ + Zb` (`u₀_lower`);
* `abs_ratio_le`: `|r_A| ≤ P ‖RAv‖`;
* `l2_field_le`, `abs_corr_le`, `abs_fderiv_b₂_field_le`: `‖W_A‖`, `|Re(v*AΓK₀v) - r_A u₁|`
  and `|Db₂[W_A]|` are bounded, for `A = J` (a Hermitian contraction) and `A = K₀`.
Every constant depends only on `σ ≥ s, s⁻¹`, `Y ≥ (Im ζ)⁻¹`, `Zb ≥ |ζ|` and `R₁`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.Angular.Ratio

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Angular.DegreeZero
open BlockBand.Angular.ProjectiveStein BlockBand.Angular.Reference BlockBand.Angular.Stein
open BlockBand.Angular.Stein.AngularData (reInner quadNum reInner_comm normSqSum_eq_reInner
  reInner_mulVec_herm quadNum_real_smul quadQuot_of_unit)
open scoped ComplexConjugate

section L2

variable {n : Type} [Fintype n] [DecidableEq n]

theorem l2Norm_add_le' (x y : n → ℂ) : l2Norm (x + y) ≤ l2Norm x + l2Norm y := by
  rw [l2Norm_eq_norm, l2Norm_eq_norm, l2Norm_eq_norm, WithLp.toLp_add]; exact norm_add_le _ _

theorem l2Norm_sub_le' (x y : n → ℂ) : l2Norm (x - y) ≤ l2Norm x + l2Norm y := by
  rw [l2Norm_eq_norm, l2Norm_eq_norm, l2Norm_eq_norm, WithLp.toLp_sub]; exact norm_sub_le _ _

theorem l2Norm_smul' (c : ℂ) (x : n → ℂ) : l2Norm (c • x) = ‖c‖ * l2Norm x := by
  rw [l2Norm_eq, l2Norm_eq, normSqSum_smul, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (norm_nonneg _)]

theorem l2Norm_le_of_sq {x y : n → ℂ} {c : ℝ} (hc : 0 ≤ c)
    (h : normSqSum y ≤ c ^ 2 * normSqSum x) : l2Norm y ≤ c * l2Norm x := by
  calc l2Norm y = Real.sqrt (normSqSum y) := l2Norm_eq y
    _ ≤ Real.sqrt (c ^ 2 * normSqSum x) := Real.sqrt_le_sqrt h
    _ = c * l2Norm x := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc, l2Norm_eq]

theorem l2Norm_unit {v : n → ℂ} (hv : normSqSum v = 1) : l2Norm v = 1 := by
  rw [l2Norm_eq, hv, Real.sqrt_one]

end L2

/-- `M` has operator norm at most `m` (Euclidean). -/
def OpB {n : Type} [Fintype n] (M : Matrix n n ℂ) (m : ℝ) : Prop :=
  ∀ x, l2Norm (M *ᵥ x) ≤ m * l2Norm x

/-- A Hermitian contraction `J` (`‖Jx‖ ≤ ‖x‖`). -/
def IsContraction {n : Type} [Fintype n] (J : Matrix n n ℂ) : Prop :=
  J.IsHermitian ∧ ∀ x, normSqSum (J *ᵥ x) ≤ normSqSum x

/-!
## The constants
-/

/-- `c₁ = 1 + Zb Y` bounds `‖R K₀‖`. -/
def cOne (Y Zb : ℝ) : ℝ := 1 + Zb * Y

/-- The common operator bound `m = σY(Y + c₁)` of `Γ, ΓJ, ΓK₀, K₀Γ, JΓK₀`. -/
def mOp (σ Y Zb : ℝ) : ℝ := σ * Y * (Y + cOne Y Zb)

/-- `P = √R₁ + Zb`; Jensen gives `1 ≤ P‖Rv‖` on the cutoff. -/
def Pc (Zb R₁ : ℝ) : ℝ := Real.sqrt R₁ + Zb

/-- Bound for `|r_J|, |r_{K₀}|` on the cutoff. -/
def Kr (Y Zb R₁ : ℝ) : ℝ := Pc Zb R₁ * (Y + cOne Y Zb)

/-- Bound for `‖W_J‖, ‖W_{K₀}‖` on the cutoff. -/
def KW (σ Y Zb R₁ : ℝ) : ℝ := mOp σ Y Zb * (1 + Kr Y Zb R₁)

/-- Bound for `|Re(v*AΓK₀v) - r_A u₁|` (`A = J, K₀`) on the cutoff. -/
def Kcorr (σ Y Zb R₁ : ℝ) : ℝ :=
  σ + (1 + 2 * Zb + Zb ^ 2) * mOp σ Y Zb + Kr Y Zb R₁ * mOp σ Y Zb

/-- Bound for `|Db₂[W_A]|` (`A = J, K₀`) on the cutoff. -/
def Kb (σ Y Zb R₁ : ℝ) : ℝ :=
  2 * (σ * (1 + Pc Zb R₁ + Kr Y Zb R₁) + 2 * Zb * Kcorr σ Y Zb R₁)

/-- The fixed scale bounds: `s, s⁻¹ ≤ σ`, `(Im ζ)⁻¹ ≤ Y`, `|ζ| ≤ Zb`. -/
structure Scales {ι : Type} [Fintype ι] [DecidableEq ι] (D : AngularData ι) (σ Y Zb : ℝ) :
    Prop where
  s1 : D.s ≤ σ
  s2 : D.s⁻¹ ≤ σ
  hY : D.ζ.im⁻¹ ≤ Y
  hZb : ‖D.ζ‖ ≤ Zb

variable {ι : Type} [Fintype ι] [DecidableEq ι]

namespace Scales

variable {D : AngularData ι} {σ Y Zb : ℝ} (S : Scales D σ Y Zb)
include S

theorem Y_pos : 0 < Y := lt_of_lt_of_le (inv_pos.2 (im_pos D)) S.hY

theorem Zb_nonneg : 0 ≤ Zb := (norm_nonneg _).trans S.hZb

theorem one_le_σs : 1 ≤ σ * D.s := by
  have := mul_le_mul_of_nonneg_right S.s2 D.hs.le
  rwa [inv_mul_cancel₀ D.hs.ne'] at this

theorem σ_pos : 0 < σ := lt_of_lt_of_le D.hs S.s1

theorem inv_Y_le : Y⁻¹ ≤ D.ζ.im := by
  rw [inv_le_comm₀ S.Y_pos (im_pos D)]; exact S.hY

theorem im_le : D.ζ.im ≤ Zb := (Complex.im_le_norm _).trans S.hZb

theorem abs_aStar_le : |aStar D.ζ| ≤ 2 * Zb := by
  rw [aStar, abs_mul, abs_two]
  exact mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans S.hZb) zero_le_two

theorem cStar_le : cStar D.ζ ≤ Zb ^ 2 := by
  rw [cStar, Complex.normSq_eq_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) S.hZb 2

theorem cOne_pos : 0 < cOne Y Zb := by
  unfold cOne; have := S.Y_pos; have := S.Zb_nonneg; positivity

theorem mOp_nonneg : 0 ≤ mOp σ Y Zb := by
  unfold mOp; have := S.Y_pos; have := S.σ_pos; have := S.cOne_pos; positivity

theorem sYY_le : D.s * Y * Y ≤ mOp σ Y Zb := by
  have := S.Y_pos; have := S.cOne_pos
  unfold mOp
  calc D.s * Y * Y ≤ σ * Y * Y := by gcongr; exact S.s1
    _ ≤ σ * Y * (Y + cOne Y Zb) := by have := S.σ_pos; gcongr; linarith

theorem sYc_le : D.s * Y * cOne Y Zb ≤ mOp σ Y Zb := by
  have := S.Y_pos; have := S.cOne_pos
  unfold mOp
  calc D.s * Y * cOne Y Zb ≤ σ * Y * cOne Y Zb := by gcongr; exact S.s1
    _ ≤ σ * Y * (Y + cOne Y Zb) := by have := S.σ_pos; gcongr; linarith

/-!
## Operator bounds
-/

theorem l2_Rz (x : ι → ℂ) : l2Norm (Rz D *ᵥ x) ≤ Y * l2Norm x :=
  l2Norm_le_of_sq S.Y_pos.le (Rz_bound D S.hY x)

theorem l2_Rzh (x : ι → ℂ) : l2Norm ((Rz D)ᴴ *ᵥ x) ≤ Y * l2Norm x :=
  l2Norm_le_of_sq S.Y_pos.le (Rzh_bound D S.hY x)

theorem l2_RzK (x : ι → ℂ) : l2Norm (Rz D *ᵥ (D.K *ᵥ x)) ≤ cOne Y Zb * l2Norm x :=
  l2Norm_le_of_sq S.cOne_pos.le (RzK_bound D S.hY S.hZb x)

theorem l2_Γ (x : ι → ℂ) : l2Norm (D.Γ *ᵥ x) ≤ D.s * Y * l2Norm (Rz D *ᵥ x) := by
  rw [Γ_mulVec, l2Norm_smul', Complex.norm_real, Real.norm_of_nonneg D.hs.le, mul_assoc]
  exact mul_le_mul_of_nonneg_left (S.l2_Rzh _) D.hs.le

theorem opB_Γ : OpB D.Γ (mOp σ Y Zb) := fun x => by
  have := S.Y_pos
  calc l2Norm (D.Γ *ᵥ x) ≤ D.s * Y * l2Norm (Rz D *ᵥ x) := S.l2_Γ x
    _ ≤ D.s * Y * (Y * l2Norm x) := by have := D.hs; gcongr; exact S.l2_Rz x
    _ = D.s * Y * Y * l2Norm x := by ring
    _ ≤ mOp σ Y Zb * l2Norm x := mul_le_mul_of_nonneg_right S.sYY_le (l2Norm_nonneg _)

theorem l2_contraction {J : Matrix ι ι ℂ} (hJ : IsContraction J) (x : ι → ℂ) :
    l2Norm (J *ᵥ x) ≤ l2Norm x := by
  rw [l2Norm_eq, l2Norm_eq]; exact Real.sqrt_le_sqrt (hJ.2 x)

theorem opB_ΓJ {J : Matrix ι ι ℂ} (hJ : IsContraction J) : OpB (D.Γ * J) (mOp σ Y Zb) :=
  fun x => by
    rw [← mulVec_mulVec]
    exact (S.opB_Γ _).trans (mul_le_mul_of_nonneg_left (S.l2_contraction hJ x) S.mOp_nonneg)

theorem opB_ΓK : OpB (D.Γ * D.K) (mOp σ Y Zb) := fun x => by
  rw [← mulVec_mulVec]
  have := S.Y_pos
  calc l2Norm (D.Γ *ᵥ (D.K *ᵥ x)) ≤ D.s * Y * l2Norm (Rz D *ᵥ (D.K *ᵥ x)) := S.l2_Γ _
    _ ≤ D.s * Y * (cOne Y Zb * l2Norm x) := by have := D.hs; gcongr; exact S.l2_RzK x
    _ = D.s * Y * cOne Y Zb * l2Norm x := by ring
    _ ≤ mOp σ Y Zb * l2Norm x := mul_le_mul_of_nonneg_right S.sYc_le (l2Norm_nonneg _)

theorem opB_KΓ : OpB (D.K * D.Γ) (mOp σ Y Zb) := by rw [D.K_mul_Γ]; exact S.opB_ΓK

theorem opB_JΓK {J : Matrix ι ι ℂ} (hJ : IsContraction J) : OpB (J * D.Γ * D.K) (mOp σ Y Zb) :=
  fun x => by
    rw [Matrix.mul_assoc, ← mulVec_mulVec]
    exact (S.l2_contraction hJ _).trans (S.opB_ΓK x)

end Scales

/-!
## Unit vectors
-/

theorem abs_quadQuot_le_of_opB {M : Matrix ι ι ℂ} {m : ℝ} (hM : OpB M m) {v : ι → ℂ}
    (hv : normSqSum v = 1) : |quadQuot M v| ≤ m := by
  rw [quadQuot_of_unit hv, ← AngularData.reInner_mulVec_self]
  refine (abs_reInner_le _ _).trans ?_
  rw [l2Norm_unit hv, one_mul]
  simpa [l2Norm_unit hv] using hM v

namespace Scales

variable {D : AngularData ι} {σ Y Zb : ℝ} (S : Scales D σ Y Zb) {R₁ : ℝ} {v : ι → ℂ}
include S

/-- **Jensen**: on `b₂ ≤ R₁`, `1 ≤ (√R₁ + Zb)‖Rv‖`. -/
theorem jensen (hv : normSqSum v = 1) (hb : D.b₂ v ≤ R₁) :
    1 ≤ Pc Zb R₁ * l2Norm (Rz D *ᵥ v) := by
  have e : (D.K - D.ζ • (1 : Matrix ι ι ℂ)) *ᵥ (Rz D *ᵥ v) = v := by
    rw [mulVec_mulVec, Rz, resolvent_mul D.hK D.hz, one_mulVec]
  have h1 : normSqSum v = reInner (Rz D *ᵥ v) ((D.K - D.ζ • (1 : Matrix ι ι ℂ))ᴴ *ᵥ v) := by
    rw [← reInner_mulVec_left, e, reInner_self]
  have h2 : (D.K - D.ζ • (1 : Matrix ι ι ℂ))ᴴ *ᵥ v = D.K *ᵥ v - star D.ζ • v := by
    rw [conjTranspose_sub, D.hK.eq, conjTranspose_smul, conjTranspose_one, sub_mulVec,
      smul_mulVec, one_mulVec]
  have h3 : l2Norm (D.K *ᵥ v - star D.ζ • v) ≤ Pc Zb R₁ := by
    refine (l2Norm_sub_le' _ _).trans (add_le_add ?_ ?_)
    · rw [l2Norm_eq, ← b₂_unit D hv]; exact Real.sqrt_le_sqrt hb
    · rw [l2Norm_smul', l2Norm_unit hv, mul_one, norm_star]; exact S.hZb
  rw [hv, h2] at h1
  calc (1 : ℝ) ≤ |reInner (Rz D *ᵥ v) (D.K *ᵥ v - star D.ζ • v)| := by rw [← h1, abs_one]
    _ ≤ l2Norm (Rz D *ᵥ v) * l2Norm (D.K *ᵥ v - star D.ζ • v) := abs_reInner_le _ _
    _ ≤ l2Norm (Rz D *ᵥ v) * Pc Zb R₁ := mul_le_mul_of_nonneg_left h3 (l2Norm_nonneg _)
    _ = _ := mul_comm _ _

theorem Pc_pos (hv : normSqSum v = 1) (hb : D.b₂ v ≤ R₁) : 0 < Pc Zb R₁ := by
  have h := S.jensen hv hb
  by_contra hn; push Not at hn
  have : Pc Zb R₁ * l2Norm (Rz D *ᵥ v) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hn (l2Norm_nonneg _)
  linarith

theorem u₀_eq (hv : normSqSum v = 1) : D.u₀ v = D.s * l2Norm (Rz D *ᵥ v) ^ 2 := by
  rw [AngularData.u₀, quadQuot_of_unit hv, quadNum_Γ, l2Norm_sq]

/-- `u₀ ≥ (σP²)⁻¹` on the cutoff. -/
theorem u₀_lower (hv : normSqSum v = 1) (hb : D.b₂ v ≤ R₁) :
    (σ * Pc Zb R₁ ^ 2)⁻¹ ≤ D.u₀ v := by
  have hP := S.Pc_pos hv hb
  have hσ := S.σ_pos
  have hj := S.jensen hv hb
  have hj2 : 1 ≤ Pc Zb R₁ ^ 2 * l2Norm (Rz D *ᵥ v) ^ 2 := by
    have := pow_le_pow_left₀ zero_le_one hj 2
    rw [one_pow, mul_pow] at this; exact this
  rw [inv_le_iff_one_le_mul₀ (by positivity)]
  calc (1 : ℝ) ≤ σ * D.s := S.one_le_σs
    _ ≤ σ * D.s * (Pc Zb R₁ ^ 2 * l2Norm (Rz D *ᵥ v) ^ 2) :=
        le_mul_of_one_le_right (by have := D.hs; positivity) hj2
    _ = D.u₀ v * (σ * Pc Zb R₁ ^ 2) := by rw [S.u₀_eq hv]; ring

theorem quadQuot_ΓA (hv : normSqSum v = 1) (A : Matrix ι ι ℂ) :
    quadQuot (D.Γ * A) v = D.s * reInner (Rz D *ᵥ v) (Rz D *ᵥ (A *ᵥ v)) := by
  rw [quadQuot_of_unit hv, ← AngularData.reInner_mulVec_self, ← mulVec_mulVec, Γ_mulVec,
    reInner_smul_right, ← reInner_mulVec_left]

/-- `|r_A| ≤ P ‖RAv‖` on the cutoff. -/
theorem abs_ratio_le (hv : normSqSum v = 1) (hb : D.b₂ v ≤ R₁) (A : Matrix ι ι ℂ) {aA : ℝ}
    (haA : l2Norm (Rz D *ᵥ (A *ᵥ v)) ≤ aA) : |D.ratio A v| ≤ Pc Zb R₁ * aA := by
  have hj := S.jensen hv hb
  have hP := S.Pc_pos hv hb
  set l := l2Norm (Rz D *ᵥ v) with hl
  have hl0 : 0 ≤ l := l2Norm_nonneg _
  have haA0 : 0 ≤ aA := (l2Norm_nonneg _).trans haA
  have hu := D.u₀_pos (ne_zero_of_unit hv)
  rw [AngularData.ratio, abs_div, abs_of_pos hu, div_le_iff₀ hu, S.quadQuot_ΓA hv, S.u₀_eq hv,
    ← hl, abs_mul, abs_of_pos D.hs]
  have h1 : |reInner (Rz D *ᵥ v) (Rz D *ᵥ (A *ᵥ v))| ≤ l * aA :=
    (abs_reInner_le _ _).trans (mul_le_mul_of_nonneg_left haA hl0)
  calc D.s * |reInner (Rz D *ᵥ v) (Rz D *ᵥ (A *ᵥ v))| ≤ D.s * (l * aA) :=
        mul_le_mul_of_nonneg_left h1 D.hs.le
    _ ≤ D.s * (l * aA) * (Pc Zb R₁ * l) :=
        le_mul_of_one_le_right (by have := D.hs; positivity) hj
    _ = Pc Zb R₁ * aA * (D.s * l ^ 2) := by ring

theorem abs_ratio_J_le (hv : normSqSum v = 1) (hb : D.b₂ v ≤ R₁) {J : Matrix ι ι ℂ}
    (hJ : IsContraction J) : |D.ratio J v| ≤ Kr Y Zb R₁ := by
  have hP := S.Pc_pos hv hb
  refine (S.abs_ratio_le hv hb J (aA := Y + cOne Y Zb) ?_).trans le_rfl
  calc l2Norm (Rz D *ᵥ (J *ᵥ v)) ≤ Y * l2Norm (J *ᵥ v) := S.l2_Rz _
    _ ≤ Y * l2Norm v := mul_le_mul_of_nonneg_left (S.l2_contraction hJ v) S.Y_pos.le
    _ ≤ Y + cOne Y Zb := by rw [l2Norm_unit hv, mul_one]; linarith [S.cOne_pos]

theorem abs_ratio_K_le (hv : normSqSum v = 1) (hb : D.b₂ v ≤ R₁) :
    |D.ratio D.K v| ≤ Kr Y Zb R₁ := by
  refine (S.abs_ratio_le hv hb D.K (aA := Y + cOne Y Zb) ?_).trans le_rfl
  calc l2Norm (Rz D *ᵥ (D.K *ᵥ v)) ≤ cOne Y Zb * l2Norm v := S.l2_RzK _
    _ ≤ Y + cOne Y Zb := by rw [l2Norm_unit hv, mul_one]; linarith [S.Y_pos]

theorem Kr_nonneg (hv : normSqSum v = 1) (hb : D.b₂ v ≤ R₁) : 0 ≤ Kr Y Zb R₁ :=
  (abs_nonneg _).trans (S.abs_ratio_K_le hv hb)

theorem abs_a_le (hv : normSqSum v = 1) (hb : D.b₂ v ≤ R₁) : |D.a v| ≤ Pc Zb R₁ := by
  have h1 : |D.a v| ≤ Real.sqrt (D.b₂ v) := Real.abs_le_sqrt (a_sq_le_b₂ D hv)
  exact h1.trans ((Real.sqrt_le_sqrt hb).trans (le_add_of_nonneg_right S.Zb_nonneg))

/-- `‖W_A‖ ≤ m(1 + K_r)` on the cutoff. -/
theorem l2_field_le {A : Matrix ι ι ℂ} (hA : OpB (D.Γ * A) (mOp σ Y Zb)) (hv : normSqSum v = 1)
    (hr : |D.ratio A v| ≤ Kr Y Zb R₁) : l2Norm (D.field A v) ≤ KW σ Y Zb R₁ := by
  unfold AngularData.field KW
  refine (l2Norm_sub_le' _ _).trans ?_
  rw [l2Norm_smul', Complex.norm_real, Real.norm_eq_abs]
  have h1 : l2Norm (D.Γ *ᵥ (A *ᵥ v)) ≤ mOp σ Y Zb := by
    rw [mulVec_mulVec]; simpa [l2Norm_unit hv] using hA v
  have h2 : l2Norm (D.Γ *ᵥ v) ≤ mOp σ Y Zb := by simpa [l2Norm_unit hv] using S.opB_Γ v
  calc l2Norm (D.Γ *ᵥ (A *ᵥ v)) + |D.ratio A v| * l2Norm (D.Γ *ᵥ v) ≤
      mOp σ Y Zb + Kr Y Zb R₁ * mOp σ Y Zb :=
        add_le_add h1 (mul_le_mul hr h2 (l2Norm_nonneg _) ((abs_nonneg _).trans hr))
    _ = mOp σ Y Zb * (1 + Kr Y Zb R₁) := by ring

theorem abs_u₁_le (hv : normSqSum v = 1) : |D.u₁ v| ≤ mOp σ Y Zb :=
  abs_quadQuot_le_of_opB S.opB_KΓ hv

theorem abs_u₀_le (hv : normSqSum v = 1) : |D.u₀ v| ≤ mOp σ Y Zb :=
  abs_quadQuot_le_of_opB S.opB_Γ hv

/-- `|Re(v*K₀ΓK₀v)| = |u₂| ≤ σ + (2Zb + Zb²) m`. -/
theorem abs_quadQuot_KΓK_le (hv : normSqSum v = 1) :
    |quadQuot (D.K * D.Γ * D.K) v| ≤ σ + (1 + 2 * Zb + Zb ^ 2) * mOp σ Y Zb := by
  have e : D.K * D.Γ * D.K = (D.s : ℂ) • 1 + (aStar D.ζ : ℂ) • (D.K * D.Γ) -
      (cStar D.ζ : ℂ) • D.Γ := by
    rw [Matrix.mul_assoc, ← D.K_mul_Γ, ← Matrix.mul_assoc, D.KK_mul_Γ]
  have hq : quadQuot (D.K * D.Γ * D.K) v =
      D.s + aStar D.ζ * D.u₁ v - cStar D.ζ * D.u₀ v := by
    rw [e, quadQuot_of_unit hv, AngularData.quadNum_sub, AngularData.quadNum_add,
      quadNum_real_smul, quadNum_real_smul, quadNum_real_smul, AngularData.quadNum_one, hv,
      AngularData.u₁, AngularData.u₀, quadQuot_of_unit hv, quadQuot_of_unit hv, mul_one]
  rw [hq]
  have h1 := S.abs_u₁_le hv
  have h2 := S.abs_u₀_le hv
  have h3 := S.abs_aStar_le
  have h4 := S.cStar_le
  have hc0 : 0 ≤ cStar D.ζ := Complex.normSq_nonneg _
  have hm := S.mOp_nonneg
  have hZ := S.Zb_nonneg
  calc |D.s + aStar D.ζ * D.u₁ v - cStar D.ζ * D.u₀ v| ≤
      |D.s| + |aStar D.ζ| * |D.u₁ v| + cStar D.ζ * |D.u₀ v| := by
        refine (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans ?_) ?_)
        · rw [abs_mul]
        · rw [abs_mul, abs_of_nonneg hc0]
    _ ≤ σ + 2 * Zb * mOp σ Y Zb + Zb ^ 2 * mOp σ Y Zb := by
        rw [abs_of_pos D.hs]
        gcongr
        · exact S.s1
    _ ≤ σ + (1 + 2 * Zb + Zb ^ 2) * mOp σ Y Zb := by nlinarith

/-- `|Re(v*AΓK₀v) - r_A u₁| ≤ K_corr` for `A = J, K₀` (given the coefficient bounds). -/
theorem abs_corr_le {A : Matrix ι ι ℂ} (hv : normSqSum v = 1)
    (h3 : |quadQuot (A * D.Γ * D.K) v| ≤ σ + (1 + 2 * Zb + Zb ^ 2) * mOp σ Y Zb)
    (hr : |D.ratio A v| ≤ Kr Y Zb R₁) : |D.corr A v| ≤ Kcorr σ Y Zb R₁ := by
  unfold AngularData.corr Kcorr
  refine (abs_sub _ _).trans ?_
  rw [abs_mul]
  have := mul_le_mul hr (S.abs_u₁_le hv) (abs_nonneg _) ((abs_nonneg _).trans hr)
  linarith

theorem abs_quadQuot_JΓK_le {J : Matrix ι ι ℂ} (hJ : IsContraction J) (hv : normSqSum v = 1) :
    |quadQuot (J * D.Γ * D.K) v| ≤ σ + (1 + 2 * Zb + Zb ^ 2) * mOp σ Y Zb := by
  refine (abs_quadQuot_le_of_opB (S.opB_JΓK hJ) hv).trans ?_
  have := S.mOp_nonneg; have := S.Zb_nonneg; have := S.σ_pos
  nlinarith

/-!
## The derivative of `b₂` along the fields
-/

/-- `Re((W_A)*K₀²v) = s(Re v*Av - r_A) + a_*(Re v*AΓK₀v - r_A u₁)` at a unit vector. -/
theorem reInner_field_KK (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (hv : normSqSum v = 1) :
    reInner (D.field A v) ((D.K * D.K) *ᵥ v) =
      D.s * (quadQuot A v - D.ratio A v) + aStar D.ζ * D.corr A v := by
  have hv0 := ne_zero_of_unit hv
  rw [D.reInner_field A (D.K * D.K) hA v, D.Γ_mul_KK]
  have hAKK : A * D.Γ * (D.K * D.K) = A * (D.K * D.K * D.Γ) := by
    rw [Matrix.mul_assoc, D.Γ_mul_KK]
  rw [hAKK, D.KK_mul_Γ]
  simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]
  rw [AngularData.quadNum_sub, AngularData.quadNum_add, quadNum_real_smul, quadNum_real_smul,
    quadNum_real_smul, AngularData.quadNum_sub, AngularData.quadNum_add, quadNum_real_smul,
    quadNum_real_smul, quadNum_real_smul, AngularData.quadNum_one, hv]
  have e1 : quadNum (A * D.Γ) v = D.ratio A v * quadNum D.Γ v := by
    rw [← AngularData.quadNum_conjTranspose, conjTranspose_mul, hA.eq, D.Γ_isHermitian.eq]
    have := D.ratio_mul_u₀ A hv0
    unfold AngularData.u₀ at this
    rw [quadQuot_of_unit hv, quadQuot_of_unit hv] at this
    linarith
  have e2 : quadNum (A * (D.K * D.Γ)) v = quadNum (A * D.Γ * D.K) v := by
    rw [D.K_mul_Γ, Matrix.mul_assoc]
  rw [e1, e2, AngularData.corr, AngularData.u₁]
  simp only [quadQuot_of_unit hv]
  ring

/-- `Db₂[W_A] = 2(s(Re v*Av - r_A) + a_*(Re v*AΓK₀v - r_A u₁))` at a unit vector. -/
theorem fderiv_b₂_field (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (hv : normSqSum v = 1) :
    fderiv ℝ D.b₂ v (D.field A v) =
      2 * (D.s * (quadQuot A v - D.ratio A v) + aStar D.ζ * D.corr A v) := by
  have hKK : (D.K * D.K).IsHermitian := by
    unfold IsHermitian; rw [conjTranspose_mul, D.hK.eq]
  rw [AngularData.b₂, fderiv_quadQuot_apply hKK hv, S.reInner_field_KK A hA hv,
    D.reInner_field_self A hA (ne_zero_of_unit hv)]
  ring

/-- `|Db₂[W_A]| ≤ K_b` on the cutoff, given the coefficient bounds. -/
theorem abs_fderiv_b₂_field_le {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (hv : normSqSum v = 1)
    (hQ : |quadQuot A v| ≤ 1 + Pc Zb R₁) (hr : |D.ratio A v| ≤ Kr Y Zb R₁)
    (hc : |D.corr A v| ≤ Kcorr σ Y Zb R₁) :
    |fderiv ℝ D.b₂ v (D.field A v)| ≤ Kb σ Y Zb R₁ := by
  rw [S.fderiv_b₂_field A hA hv, Kb, abs_mul, abs_two]
  refine mul_le_mul_of_nonneg_left ?_ zero_le_two
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_pos D.hs]
    refine mul_le_mul S.s1 ((abs_sub _ _).trans (by linarith)) (abs_nonneg _) S.σ_pos.le
  · rw [abs_mul]
    exact mul_le_mul S.abs_aStar_le hc (abs_nonneg _) (by linarith [S.Zb_nonneg])

theorem abs_quadQuot_J_le {J : Matrix ι ι ℂ} (hJ : IsContraction J) (hv : normSqSum v = 1)
    (hb : D.b₂ v ≤ R₁) : |quadQuot J v| ≤ 1 + Pc Zb R₁ := by
  have h : |quadQuot J v| ≤ 1 := by
    refine (abs_quadQuot_le_of_opB (m := 1) (fun x => ?_) hv)
    rw [one_mul]; exact S.l2_contraction hJ x
  linarith [S.Pc_pos hv hb]

theorem abs_quadQuot_K_le (hv : normSqSum v = 1) (hb : D.b₂ v ≤ R₁) :
    |quadQuot D.K v| ≤ 1 + Pc Zb R₁ := by
  have := S.abs_a_le hv hb; unfold AngularData.a at this; linarith

end Scales

end BlockBand.Angular.Ratio
