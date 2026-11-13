module

public import BlockBand.DeterminantScore.ScoreMomentsCorner
public import BlockBand.DeterminantScore.ExactScore

/-!
# The moments clause of the physical determinant score

At the selected root `QK₀v = -QG_dv`, hence `‖∇ log 𝔷_ℓ‖ ≤ 4‖R̄‖‖G_d‖`, and the pair law has every
fixed Gaussian norm moment bounded. `determinantScore_of_statements`: `DeterminantScoreStatement`
from two intermediate statements:

* `RbarMomentStatement`: `E♯ 1{E ∈ I}‖R̄‖^ρ ≤ C` for `0 < ρ < 2`;
* `PairRowMomentStatement`: `E♯ 1{E ∈ I}‖QK₀v‖^q ≤ C` for every `q > 0`.

The exact clause is `ExactScore.exactScore_holds`. Proof of the moments clause: pointwise
`‖score‖ ≤ 4‖R̄‖‖QK₀v‖` (`U_v` is an isometry, `‖U_v*x‖ ≤ ‖x‖`), then Young with `ρ = (r+2)/2`,
`q = rρ/(ρ - r)`: `X^r + (4XY)^r ≤ 1 + (1 + 4^r)X^ρ + 4^rY^q`, and the pair law has mass at
most one (`pairExpect_one_le`). Young's inequality is used in place of Hölder's, with the same
exponents.

`cornerMoment_holds` gives `E♯ 1{E ∈ I}|w*Rw|^r ≤ C` for every measurable eigenvector `w` of `K`;
`RbarMomentStatement` follows by stabilizer invariance and conditional Jensen with a measurable
maximizing eigenvector (`RbarMoment.rbarMoment_of_corner`); `PairRowMomentStatement` is
`pairRowMoment_holds`; the composition is `DeterminantScoreHolds.determinantScore_holds`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.ScoreMoments

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Layers BlockBand.Angular.FiberAngular
open BlockBand.DeterminantScore BlockBand.DeterminantScore.Sector
open BlockBand.DeterminantScore.PhysicalColumn BlockBand.DeterminantScore.MinorTail
open BlockBand.DeterminantScore.MinorTailInverse
open scoped NNReal ENNReal Matrix.Norms.L2Operator

/-!
## The two intermediates
-/

/-- **The `‖R̄‖` half of the physical determinant score bound**: for `b, T, ϑ, κ` and
`0 < ρ < 2` there is `C` with `E♯ 1{E ∈ I}‖R̄‖^ρ ≤ C`, uniformly as in
`DeterminantScoreStatement.moments`. -/
def RbarMomentStatement : Prop :=
  ∀ b T ϑ κ ρ : ℝ, 0 < ϑ → 0 < κ → 0 < ρ → ρ < 2 → ∃ C : ℝ,
    ∀ p : Parameters, p.b = b → (p.n : ℝ) ≤ T * (p.W : ℝ) →
    ∀ (model : p.GaussianRingModel) (α : Fin p.N), IsBulkRank p ϑ α →
    ∀ (i : ZMod p.n) (Pω : Measure (SplitState p i)), IsPairSplitting p i model (splitS p) Pω →
    ∀ U : FrameMap p i, IsPairFrame p i U →
      pairExpect α (splitS p) U Pω (fun θ _ =>
          (bulkInterval κ).indicator 1 θ.2.1 *
            ENNReal.ofReal (‖condInverse α (splitS p) U θ‖ ^ ρ)) ≤
        ENNReal.ofReal C

/-- **Pair-law moments of the deleted row** (the pair law has every fixed Gaussian norm moment
bounded, used through `QK₀v = -QG_dv`): for `b, T, ϑ, κ` and `q > 0` there is `C` with
`E♯ 1{E ∈ I}‖QK₀v‖^q ≤ C`, uniformly as in `DeterminantScoreStatement.moments`. -/
def PairRowMomentStatement : Prop :=
  ∀ b T ϑ κ q : ℝ, 0 < ϑ → 0 < κ → 0 < q → ∃ C : ℝ,
    ∀ p : Parameters, p.b = b → (p.n : ℝ) ≤ T * (p.W : ℝ) →
    ∀ (model : p.GaussianRingModel) (α : Fin p.N), IsBulkRank p ϑ α →
    ∀ (i : ZMod p.n) (Pω : Measure (SplitState p i)), IsPairSplitting p i model (splitS p) Pω →
    ∀ U : FrameMap p i, IsPairFrame p i U →
      pairExpect α (splitS p) U Pω (fun θ _ =>
          (bulkInterval κ).indicator 1 θ.2.1 *
            ENNReal.ofReal (l2Norm (orthProj θ.2.2 *ᵥ (outerK0 θ *ᵥ θ.2.2)) ^ q)) ≤
        ENNReal.ofReal C

variable {p : Parameters} {i : ZMod p.n}

/-!
## The pointwise score bound
-/

theorem l2Norm_toLp {κ : Type} [Fintype κ] (x : κ → ℂ) :
    l2Norm x = ‖(WithLp.toLp 2 x : EuclideanSpace ℂ κ)‖ := by
  rw [EuclideanSpace.norm_eq]; rfl

theorem l2Norm_mulVec_le {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) (z : n → ℂ) : l2Norm (A *ᵥ z) ≤ ‖A‖ * l2Norm z := by
  rw [l2Norm_toLp, l2Norm_toLp]
  exact Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 z)

theorem l2Norm_isometry {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {V : Matrix m n ℂ} (hV : Vᴴ * V = 1) (z : n → ℂ) : l2Norm (V *ᵥ z) = l2Norm z := by
  rw [l2Norm_toLp, l2Norm_toLp]
  exact norm_toE_isometry hV (WithLp.toLp 2 z)

theorem l2Norm_conjTranspose_le {m n : Type} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] {V : Matrix m n ℂ} (hV : Vᴴ * V = 1) (z : m → ℂ) :
    l2Norm (Vᴴ *ᵥ z) ≤ l2Norm z := by
  rw [l2Norm_toLp, l2Norm_toLp]
  exact norm_toE_conjTranspose_le hV (WithLp.toLp 2 z)

theorem conj_mulVec_eq {m n : Type} [Fintype m] [Fintype n] (V : Matrix m n ℂ)
    (R : Matrix n n ℂ) (y : m → ℂ) : (V * R * Vᴴ) *ᵥ y = V *ᵥ (R *ᵥ (Vᴴ *ᵥ y)) := by
  simp only [mulVec_mulVec, Matrix.mul_assoc]

/-- `‖score‖ ≤ 4‖R̄‖‖QK₀v‖` for unit `v`. -/
theorem l2Norm_score_le (α : Fin p.N) (s : ℝ) {U : FrameMap p i} (hU : IsPairFrame p i U)
    {θ : OuterData p i} (hv : l2Norm θ.2.2 = 1) :
    l2Norm (score α s U θ) ≤
      4 * (‖condInverse α s U θ‖ * l2Norm (orthProj θ.2.2 *ᵥ (outerK0 θ *ᵥ θ.2.2))) := by
  obtain ⟨hUU, -⟩ := hU.2 θ.2.2 hv
  set R := condInverse α s U θ
  set V := U θ.2.2
  set y := orthProj θ.2.2 *ᵥ (outerK0 θ *ᵥ θ.2.2)
  have e : embedFrame U θ.2.2 R *ᵥ y = V *ᵥ (R *ᵥ (Vᴴ *ᵥ y)) := conj_mulVec_eq V R y
  have h1 : l2Norm (V *ᵥ (R *ᵥ (Vᴴ *ᵥ y))) = l2Norm (R *ᵥ (Vᴴ *ᵥ y)) :=
    l2Norm_isometry hUU _
  have h2 : l2Norm (R *ᵥ (Vᴴ *ᵥ y)) ≤ ‖R‖ * l2Norm (Vᴴ *ᵥ y) := l2Norm_mulVec_le R _
  have h3 : l2Norm (Vᴴ *ᵥ y) ≤ l2Norm y := l2Norm_conjTranspose_le hUU y
  unfold score
  rw [l2Norm_smul, e, h1]
  have hn : ‖(-4 : ℂ)‖ = 4 := by simp
  rw [hn]
  have hR : 0 ≤ ‖R‖ := norm_nonneg _
  nlinarith

/-!
## Young's inequality
-/

theorem rpow_le_one_add {X r ρ : ℝ} (hX : 0 ≤ X) (hr : 0 ≤ r) (hrρ : r ≤ ρ) :
    X ^ r ≤ 1 + X ^ ρ := by
  rcases le_or_gt X 1 with h | h
  · have := Real.rpow_le_one hX h hr
    have := Real.rpow_nonneg hX ρ
    linarith
  · have := Real.rpow_le_rpow_of_exponent_le h.le hrρ
    linarith

theorem young_rpow {X Y r ρ : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (hr : 0 < r) (hrρ : r < ρ) :
    X ^ r * Y ^ r ≤ X ^ ρ + Y ^ (r * ρ / (ρ - r)) := by
  have hρ : 0 < ρ := lt_trans hr hrρ
  have hw1 : 0 ≤ r / ρ := (div_pos hr hρ).le
  have hw2 : 0 ≤ 1 - r / ρ := by rw [sub_nonneg, div_le_one hρ]; exact hrρ.le
  have h := Real.geom_mean_le_arith_mean2_weighted hw1 hw2 (Real.rpow_nonneg hX ρ)
    (Real.rpow_nonneg hY (r * ρ / (ρ - r))) (by ring)
  have e1 : (X ^ ρ) ^ (r / ρ) = X ^ r := by
    rw [← Real.rpow_mul hX, mul_div_cancel₀ _ hρ.ne']
  have e2 : (Y ^ (r * ρ / (ρ - r))) ^ (1 - r / ρ) = Y ^ r := by
    rw [← Real.rpow_mul hY]
    congr 1
    field_simp [(sub_pos.mpr hrρ).ne']
  rw [e1, e2] at h
  have hw1' : r / ρ ≤ 1 := by rw [div_le_one hρ]; exact hrρ.le
  have hA := Real.rpow_nonneg hX ρ
  have hB := Real.rpow_nonneg hY (r * ρ / (ρ - r))
  nlinarith [mul_le_of_le_one_left hA hw1', mul_le_of_le_one_left hB (by linarith : 1 - r / ρ ≤ 1)]

/-- The pointwise bound `X^r + (4XY)^r ≤ 1 + (1 + 4^r)X^ρ + 4^rY^q`. -/
theorem pointwise_young {X Y S r ρ : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (hS0 : 0 ≤ S)
    (hS : S ≤ 4 * (X * Y)) (hr : 0 < r) (hrρ : r < ρ) :
    X ^ r + S ^ r ≤ (1 + 4 ^ r) * X ^ ρ + (1 + 4 ^ r * Y ^ (r * ρ / (ρ - r))) := by
  have h4 : (0 : ℝ) < 4 ^ r := by positivity
  have hSr : S ^ r ≤ 4 ^ r * (X ^ r * Y ^ r) := by
    calc S ^ r ≤ (4 * (X * Y)) ^ r := Real.rpow_le_rpow hS0 hS hr.le
      _ = 4 ^ r * (X ^ r * Y ^ r) := by
        rw [Real.mul_rpow (by norm_num) (mul_nonneg hX hY), Real.mul_rpow hX hY]
  have h1 := rpow_le_one_add hX hr.le hrρ.le
  have h2 := young_rpow hX hY hr hrρ
  nlinarith [mul_le_mul_of_nonneg_left h2 h4.le]

/-!
## Measurability of the row observable
-/

theorem measurable_rowObs (κ q : ℝ) :
    Measurable fun z : OuterData p i × FrameMatrix p =>
      (bulkInterval κ).indicator (1 : ℝ → ℝ≥0∞) z.1.2.1 *
        ENNReal.ofReal (l2Norm (orthProj z.1.2.2 *ᵥ (outerK0 z.1 *ᵥ z.1.2.2)) ^ q) := by
  have hF : Measurable fun θ : OuterData p i => physicalCoareaF θ.1.1 θ.1.2.1 θ.1.2.2 θ.2.1 :=
    measurable_physF.comp (measurable_fst.prodMk measurable_snd.fst)
  have hK0 : Measurable fun θ : OuterData p i => outerK0 θ :=
    measurable_matSub hF (measurable_smul_one measurable_snd.fst)
  have hQ : Continuous fun v : PairSite p i → ℂ => orthProj v := by
    unfold orthProj
    exact continuous_const.sub (continuous_id.matrix_vecMulVec continuous_id.star)
  have hl2 : Continuous fun x : PairSite p i → ℂ => l2Norm x := by
    unfold l2Norm
    exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun k _ =>
      (continuous_apply k).norm.pow 2)
  have hθ : Measurable fun θ : OuterData p i =>
      l2Norm (orthProj θ.2.2 *ᵥ (outerK0 θ *ᵥ θ.2.2)) :=
    hl2.measurable.comp (measurable_mulVec' (hQ.measurable.comp measurable_snd.snd)
      (measurable_mulVec' hK0 measurable_snd.snd))
  exact ((measurable_one.indicator measurableSet_Icc).comp (measurable_snd.fst.comp
    measurable_fst)).mul (ENNReal.measurable_ofReal.comp ((hθ.comp measurable_fst).pow_const q))

/-!
## The moments clause
-/

/-- **The physical determinant score bound** from `RbarMomentStatement` and
`PairRowMomentStatement`. -/
theorem moments_of_statements (hC : CoareaContract) (hR : RbarMomentStatement)
    (hRow : PairRowMomentStatement) :
    ∀ b T ϑ κ r : ℝ, 0 < ϑ → 0 < κ → 0 < r → r < 2 → ∃ C : ℝ,
      ∀ p : Parameters, p.b = b → (p.n : ℝ) ≤ T * (p.W : ℝ) →
      ∀ (model : p.GaussianRingModel) (α : Fin p.N), IsBulkRank p ϑ α →
      ∀ (i : ZMod p.n) (Pω : Measure (SplitState p i)), IsPairSplitting p i model (splitS p) Pω →
      ∀ U : FrameMap p i, IsPairFrame p i U →
        pairExpect α (splitS p) U Pω (fun θ _ =>
            (bulkInterval κ).indicator 1 θ.2.1 *
              ENNReal.ofReal (‖condInverse α (splitS p) U θ‖ ^ r +
                l2Norm (score α (splitS p) U θ) ^ r)) ≤
          ENNReal.ofReal C := by
  intro b T ϑ κ r hϑ hκ hr0 hr2
  set ρ : ℝ := (r + 2) / 2 with hρ
  have hrρ : r < ρ := by rw [hρ]; linarith
  have hρ2 : ρ < 2 := by rw [hρ]; linarith
  have hρ0 : 0 < ρ := by linarith
  set q : ℝ := r * ρ / (ρ - r) with hq
  have hq0 : 0 < q := div_pos (mul_pos hr0 hρ0) (sub_pos.mpr hrρ)
  obtain ⟨C₁, hC₁⟩ := hR b T ϑ κ ρ hϑ hκ hρ0 hρ2
  obtain ⟨C₂, hC₂⟩ := hRow b T ϑ κ q hϑ hκ hq0
  set c₁ : ℝ := 1 + 4 ^ r
  set c₂ : ℝ := 4 ^ r
  have hc₁ : 0 ≤ c₁ := by positivity
  have hc₂ : 0 ≤ c₂ := by positivity
  refine ⟨c₁ * max C₁ 0 + (1 + c₂ * max C₂ 0), ?_⟩
  intro p hb hn model α hα i Pω hPω U hU
  set s := splitS p
  set ind : OuterData p i → ℝ≥0∞ := fun θ => (bulkInterval κ).indicator 1 θ.2.1 with hind
  have hind1 : ∀ θ, ind θ ≤ 1 := fun θ => by
    simp only [hind, Set.indicator]; split_ifs <;> simp
  set Ψa : OuterData p i → FrameMatrix p → ℝ≥0∞ := fun θ _ =>
    ENNReal.ofReal c₁ * (ind θ * ENNReal.ofReal (‖condInverse α s U θ‖ ^ ρ))
  set Ψr : OuterData p i → FrameMatrix p → ℝ≥0∞ := fun θ _ =>
    ind θ * ENNReal.ofReal (l2Norm (orthProj θ.2.2 *ᵥ (outerK0 θ *ᵥ θ.2.2)) ^ q)
  set Ψb : OuterData p i → FrameMatrix p → ℝ≥0∞ := fun θ G' => 1 + ENNReal.ofReal c₂ * Ψr θ G'
  have hmr : Measurable fun z : OuterData p i × FrameMatrix p => Ψr z.1 z.2 :=
    measurable_rowObs κ q
  have hmb : Measurable fun z : OuterData p i × FrameMatrix p => Ψb z.1 z.2 :=
    measurable_const.add (hmr.const_mul _)
  have hpt : pairExpect α s U Pω (fun θ _ => ind θ *
      ENNReal.ofReal (‖condInverse α s U θ‖ ^ r + l2Norm (score α s U θ) ^ r)) ≤
      pairExpect α s U Pω (fun θ G' => Ψa θ G' + Ψb θ G') := by
    refine pairExpect_mono_ae hPω α U fun θ _ _ hv _ => Filter.Eventually.of_forall fun G' _ => ?_
    set X := ‖condInverse α s U θ‖
    set Y := l2Norm (orthProj θ.2.2 *ᵥ (outerK0 θ *ᵥ θ.2.2))
    set S := l2Norm (score α s U θ)
    have hX : 0 ≤ X := norm_nonneg _
    have hY : 0 ≤ Y := Real.sqrt_nonneg _
    have hS0 : 0 ≤ S := Real.sqrt_nonneg _
    have hpw := pointwise_young hX hY hS0 (l2Norm_score_le α s hU hv) hr0 hrρ
    have hXρ : 0 ≤ X ^ ρ := Real.rpow_nonneg hX ρ
    have hYq : 0 ≤ Y ^ q := Real.rpow_nonneg hY q
    simp only [Ψa, Ψb, Ψr]
    calc ind θ * ENNReal.ofReal (X ^ r + S ^ r)
        ≤ ind θ * ENNReal.ofReal (c₁ * X ^ ρ + (1 + c₂ * Y ^ q)) := by
          gcongr
      _ = ENNReal.ofReal c₁ * (ind θ * ENNReal.ofReal (X ^ ρ)) +
          ind θ * (1 + ENNReal.ofReal c₂ * ENNReal.ofReal (Y ^ q)) := by
          rw [ENNReal.ofReal_add (mul_nonneg hc₁ hXρ)
              (by linarith [mul_nonneg hc₂ hYq] : (0 : ℝ) ≤ 1 + c₂ * Y ^ q),
            ENNReal.ofReal_mul hc₁, ENNReal.ofReal_add zero_le_one (mul_nonneg hc₂ hYq),
            ENNReal.ofReal_mul hc₂, ENNReal.ofReal_one]
          ring
      _ ≤ ENNReal.ofReal c₁ * (ind θ * ENNReal.ofReal (X ^ ρ)) +
          (1 + ENNReal.ofReal c₂ * (ind θ * ENNReal.ofReal (Y ^ q))) := by
          gcongr
          calc ind θ * (1 + ENNReal.ofReal c₂ * ENNReal.ofReal (Y ^ q))
              = ind θ + ENNReal.ofReal c₂ * (ind θ * ENNReal.ofReal (Y ^ q)) := by ring
            _ ≤ _ := by gcongr; exact hind1 θ
  have hA : pairExpect α s U Pω Ψa ≤ ENNReal.ofReal c₁ * ENNReal.ofReal (max C₁ 0) := by
    rw [pairExpect_const_mul α s U Pω ENNReal.ofReal_ne_top]
    gcongr
    exact le_trans (hC₁ p hb hn model α hα i Pω hPω U hU)
      (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hB : pairExpect α s U Pω Ψb ≤ 1 + ENNReal.ofReal c₂ * ENNReal.ofReal (max C₂ 0) := by
    have hmr' : Measurable fun z : OuterData p i × FrameMatrix p =>
        ENNReal.ofReal c₂ * Ψr z.1 z.2 := hmr.const_mul _
    calc pairExpect α s U Pω Ψb
        ≤ pairExpect α s U Pω (fun _ _ => 1) +
          pairExpect α s U Pω (fun θ G' => ENNReal.ofReal c₂ * Ψr θ G') :=
          pairExpect_add_le_of_measurable α s hU.1 Pω _ _ hmr'
      _ ≤ 1 + ENNReal.ofReal c₂ * ENNReal.ofReal (max C₂ 0) := by
          rw [pairExpect_const_mul α s U Pω ENNReal.ofReal_ne_top]
          gcongr
          · exact pairExpect_one_le hC hPω hU α
          · exact le_trans (hC₂ p hb hn model α hα i Pω hPω U hU)
              (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  calc _ = pairExpect α s U Pω (fun θ _ => ind θ *
        ENNReal.ofReal (‖condInverse α s U θ‖ ^ r + l2Norm (score α s U θ) ^ r)) := rfl
    _ ≤ _ := hpt
    _ ≤ pairExpect α s U Pω Ψa + pairExpect α s U Pω Ψb :=
        pairExpect_add_le_of_measurable α s hU.1 Pω _ _ hmb
    _ ≤ ENNReal.ofReal c₁ * ENNReal.ofReal (max C₁ 0) +
        (1 + ENNReal.ofReal c₂ * ENNReal.ofReal (max C₂ 0)) := add_le_add hA hB
    _ = _ := by
        have h1 : 0 ≤ c₁ * max C₁ 0 := mul_nonneg hc₁ (le_max_right _ _)
        have h2 : 0 ≤ c₂ * max C₂ 0 := mul_nonneg hc₂ (le_max_right _ _)
        rw [← ENNReal.ofReal_mul hc₁, ← ENNReal.ofReal_mul hc₂, ← ENNReal.ofReal_one,
          ← ENNReal.ofReal_add zero_le_one h2,
          ← ENNReal.ofReal_add h1 (by linarith : (0 : ℝ) ≤ 1 + c₂ * max C₂ 0)]

/-- **The determinant score theorem** from `RbarMomentStatement` and `PairRowMomentStatement`;
the exact clause is `ExactScore.exactScore_holds`. -/
theorem determinantScore_of_statements (hC : CoareaContract) (hR : RbarMomentStatement)
    (hRow : PairRowMomentStatement) : DeterminantScoreStatement :=
  ExactScore.determinantScore_of_moments (moments_of_statements hC hR hRow)

end BlockBand.DeterminantScore.ScoreMoments
