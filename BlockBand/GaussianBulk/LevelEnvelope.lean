module

public import BlockBand.GaussianBulk.LevelAction

/-!
# The level action as a vertical envelope

In the squared-height variable `s = y²`, the real phase `levelEnvelopeAction` is strictly
concave on its pole-safe domain, and `s = y(x)²` is its unique global maximizer. This envelope
description gives the derivative `(ψ - E)/t` of the level action at every real `x`, including
the real gaps where the graph has zero height, without differentiating the maximizer.
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.GaussianBulk
open Filter Topology
open scoped BigOperators

/-- The pole-safe domain of squared heights: `s ≥ 0` and every `(x - d_j)² + s` positive. -/
def LevelEnvelopeDomain {N : ℕ} (d : Fin N → ℝ) (x s : ℝ) : Prop :=
  0 ≤ s ∧ ∀ j, 0 < (x-d j)^2+s

/-- The normalized level `N⁻¹ Σ_j ((x - d_j)² + s)⁻¹` in the squared-height variable. -/
def squaredVerticalLevel {N : ℕ} (d : Fin N → ℝ) (x s : ℝ) : ℝ :=
  realMean fun j => ((x-d j)^2+s)⁻¹

/-- The real logarithmic phase as a function of the squared height `s`. -/
def levelEnvelopeAction {N : ℕ} (d : Fin N → ℝ) (E t x s : ℝ) : ℝ :=
  ((x-E)^2-s)/(2*t)+realMean (fun j => Real.log ((x-d j)^2+s))/2

/-- The derivative of the phase in the squared-height direction. -/
def levelEnvelopeSlope {N : ℕ} (d : Fin N → ℝ) (t x s : ℝ) : ℝ :=
  (squaredVerticalLevel d x s-1/t)/2

private theorem envelope_mean_mul {N : ℕ} (c : ℝ) (f : Fin N → ℝ) :
    realMean (fun j => c*f j) = c*realMean f := by
  simp only [realMean,← Finset.mul_sum]
  ring

private theorem log_support_strict (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : b ≠ a) : Real.log b-Real.log a < (b-a)/a := by
  have hratio : b/a ≠ 1 := by
    intro h
    exact hab ((div_eq_one_iff_eq (ne_of_gt ha)).mp h)
  have h := Real.log_lt_sub_one_of_pos (div_pos hb ha) hratio
  rw [Real.log_div (ne_of_gt hb) (ne_of_gt ha)] at h
  have he : b/a-1=(b-a)/a := by field_simp
  simpa only [he] using h

/-- The phase has a strict supporting line at every admissible `s`: for `u ≠ s`, the increment is
strictly below `(u - s)` times the slope at `s`. -/
theorem levelEnvelope_strict_support {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t x s u : ℝ) (_ht : 0 < t)
    (hs : LevelEnvelopeDomain d x s) (hu : LevelEnvelopeDomain d x u)
    (hne : u ≠ s) :
    levelEnvelopeAction d E t x u-levelEnvelopeAction d E t x s <
      (u-s)*levelEnvelopeSlope d t x s := by
  have hterms (j : Fin N) :
      Real.log ((x-d j)^2+u)-Real.log ((x-d j)^2+s) <
        (u-s)*((x-d j)^2+s)⁻¹ := by
    have h := log_support_strict _ _ (hs.2 j) (hu.2 j) (by intro he; apply hne; linarith)
    have he : (((x-d j)^2+u)-((x-d j)^2+s))/((x-d j)^2+s) =
        (u-s)*((x-d j)^2+s)⁻¹ := by simp only [div_eq_mul_inv]; ring
    rwa [he] at h
  have hsum : (∑ j, (Real.log ((x-d j)^2+u)-Real.log ((x-d j)^2+s))) <
      ∑ j, (u-s)*((x-d j)^2+s)⁻¹ :=
    Finset.sum_lt_sum_of_nonempty ⟨⟨0,hN⟩,Finset.mem_univ _⟩ (fun j _ => hterms j)
  have hn : 0 < (N : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hN)
  have hmean := mul_lt_mul_of_pos_left hsum hn
  change realMean (fun j => Real.log ((x-d j)^2+u)-Real.log ((x-d j)^2+s)) <
    realMean (fun j => (u-s)*((x-d j)^2+s)⁻¹) at hmean
  rw [envelope_mean_mul] at hmean
  have hdiff : realMean (fun j => Real.log ((x-d j)^2+u)-Real.log ((x-d j)^2+s)) =
      realMean (fun j => Real.log ((x-d j)^2+u))-
        realMean (fun j => Real.log ((x-d j)^2+s)) := by
    simp only [realMean,Finset.sum_sub_distrib,mul_sub]
  rw [hdiff] at hmean
  unfold levelEnvelopeAction levelEnvelopeSlope squaredVerticalLevel
  have he : ((x-E)^2-u)/(2*t)-((x-E)^2-s)/(2*t)=-(u-s)/(2*t) := by ring
  rw [show ((x-E)^2-u)/(2*t)+realMean (fun j => Real.log ((x-d j)^2+u))/2-
    (((x-E)^2-s)/(2*t)+realMean (fun j => Real.log ((x-d j)^2+s))/2) =
    (((x-E)^2-u)/(2*t)-((x-E)^2-s)/(2*t))+
      (realMean (fun j => Real.log ((x-d j)^2+u))-
        realMean (fun j => Real.log ((x-d j)^2+s)))/2 by ring, he]
  have he2 : (u-s)*((realMean (fun j => ((x-d j)^2+s)⁻¹)-1/t)/2) =
    -(u-s)/(2*t)+(u-s)*realMean (fun j => ((x-d j)^2+s)⁻¹)/2 := by ring
  rw [he2]
  linarith

/-- The supporting-line inequality, including `u = s`. -/
theorem levelEnvelope_support {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t x s u : ℝ) (ht : 0 < t)
    (hs : LevelEnvelopeDomain d x s) (hu : LevelEnvelopeDomain d x u) :
    levelEnvelopeAction d E t x u-levelEnvelopeAction d E t x s ≤
      (u-s)*levelEnvelopeSlope d t x s := by
  by_cases hne : u ≠ s
  · exact (levelEnvelope_strict_support hN d E t x s u ht hs hu hne).le
  · have he := not_ne_iff.mp hne
    subst u
    simp

/-- The squared-height slope is strictly decreasing on the pole-safe domain. -/
theorem levelEnvelopeSlope_strictAnti {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t x s u : ℝ) (hs : LevelEnvelopeDomain d x s)
    (_hu : LevelEnvelopeDomain d x u) (hsu : s < u) :
    levelEnvelopeSlope d t x u < levelEnvelopeSlope d t x s := by
  have hsum : (∑ j, ((x-d j)^2+u)⁻¹) < ∑ j, ((x-d j)^2+s)⁻¹ := by
    apply Finset.sum_lt_sum_of_nonempty ⟨⟨0,hN⟩,Finset.mem_univ _⟩
    intro j _
    exact inv_strictAnti₀ (hs.2 j) (by linarith)
  have hn : 0 < (N : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hN)
  have hm := mul_lt_mul_of_pos_left hsum hn
  unfold levelEnvelopeSlope squaredVerticalLevel realMean
  linarith

/-- The squared graph height lies in the pole-safe domain. -/
theorem levelHeight_sq_envelopeDomain {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t x : ℝ) (ht : 0 < t) :
    LevelEnvelopeDomain d x ((levelHeight d t x)^2) :=
  ⟨sq_nonneg _,fun j => levelGraph_denominator_pos hN d t x ht j⟩

/-- At the graph the vertical slope is nonpositive, with complementary slackness: it vanishes at
positive height, and otherwise `s = 0`. -/
theorem levelHeight_sq_envelope_slackness {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t x : ℝ) (ht : 0 < t) :
    levelEnvelopeSlope d t x ((levelHeight d t x)^2) ≤ 0 ∧
      ((levelHeight d t x)^2)*levelEnvelopeSlope d t x ((levelHeight d t x)^2) = 0 := by
  have hl := levelGraph_level_le hN d t x ht
  have hdef := levelGraph_height_mul_defect hN d t x ht
  change verticalLevel d x (levelHeight d t x) ≤ 1/t at hl
  have he : squaredVerticalLevel d x ((levelHeight d t x)^2) =
      verticalLevel d x (levelHeight d t x) := rfl
  rw [levelEnvelopeSlope,he]
  constructor
  · linarith
  · have heq : ((levelHeight d t x)^2)*((verticalLevel d x (levelHeight d t x)-1/t)/2) =
      -(levelHeight d t x/(2*t))*
        (levelHeight d t x*(1-t*verticalLevel d x (levelHeight d t x))) := by
      field_simp [ne_of_gt ht]
      ring
    rw [heq,hdef,mul_zero]

/-- The squared graph height is the unique global maximizer of the phase over admissible `s`. -/
theorem levelHeight_sq_unique_envelope_max {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t x : ℝ) (ht : 0 < t) (s : ℝ) (hs : LevelEnvelopeDomain d x s)
    (hne : s ≠ ((levelHeight d t x)^2)) :
    levelEnvelopeAction d E t x s < levelAction d E t x := by
  have h := levelEnvelope_strict_support hN d E t x ((levelHeight d t x)^2) s ht
    (levelHeight_sq_envelopeDomain hN d t x ht) hs hne
  have hsl := levelHeight_sq_envelope_slackness hN d t x ht
  have hprod : (s-((levelHeight d t x)^2))*
      levelEnvelopeSlope d t x ((levelHeight d t x)^2) ≤ 0 := by
    have hp := mul_nonpos_of_nonneg_of_nonpos hs.1 hsl.1
    nlinarith [hsl.2]
  change levelEnvelopeAction d E t x s <
    levelEnvelopeAction d E t x ((levelHeight d t x)^2)
  linarith

/-- The phase at any admissible height is at most the level action. -/
theorem levelHeight_sq_envelope_max {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t x : ℝ) (ht : 0 < t) (s : ℝ) (hs : LevelEnvelopeDomain d x s) :
    levelEnvelopeAction d E t x s ≤ levelAction d E t x := by
  by_cases hne : s ≠ ((levelHeight d t x)^2)
  · exact (levelHeight_sq_unique_envelope_max hN d E t x ht s hs hne).le
  · have he := not_ne_iff.mp hne
    subst s
    exact le_rfl

/-- The squared graph height is continuous in `x`. -/
theorem levelHeight_sq_continuous {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t : ℝ) (ht : 0 < t) : Continuous (fun x => ((levelHeight d t x)^2)) :=
  (levelHeight_continuous hN d t ht).pow 2

/-- Two-sided bound on horizontal increments of the level action, from the maximizing property
at `x` and at `u` (given the cross admissibility conditions). -/
theorem levelEnvelope_increment_sandwich {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t x u : ℝ) (ht : 0 < t)
    (hxu : LevelEnvelopeDomain d u ((levelHeight d t x)^2))
    (hux : LevelEnvelopeDomain d x ((levelHeight d t u)^2)) :
    levelEnvelopeAction d E t u ((levelHeight d t x)^2)-levelAction d E t x ≤
      levelAction d E t u-levelAction d E t x ∧
    levelAction d E t u-levelAction d E t x ≤
      levelAction d E t u-levelEnvelopeAction d E t x ((levelHeight d t u)^2) := by
  constructor
  · exact sub_le_sub_right (levelHeight_sq_envelope_max hN d E t u ht _ hxu) _
  · exact sub_le_sub_left (levelHeight_sq_envelope_max hN d E t x ht _ hux) _

/-- The derivative of the phase in the squared height. -/
theorem hasDerivAt_levelEnvelope_vertical {N : ℕ} (d : Fin N → ℝ)
    (E t x s : ℝ) (_ht : 0 < t) (hs : LevelEnvelopeDomain d x s) :
    HasDerivAt (fun u => levelEnvelopeAction d E t x u)
      (levelEnvelopeSlope d t x s) s := by
  have hterms (j : Fin N) : HasDerivAt
      (fun u => Real.log ((x-d j)^2+u)) (((x-d j)^2+s)⁻¹) s := by
    simpa only [zero_add,one_div,Pi.add_apply,id_eq] using
      ((hasDerivAt_const s ((x-d j)^2)).add (hasDerivAt_id s)).log (ne_of_gt (hs.2 j))
  have hmain := ((hasDerivAt_const s ((x-E)^2)).sub (hasDerivAt_id s)).div_const (2*t)
  have hmean := ((HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hterms j)).const_mul
    (N : ℝ)⁻¹).div_const 2
  have h := hmain.add hmean
  apply h.congr_deriv
  change (0-1)/(2*t)+realMean (fun j => ((x-d j)^2+s)⁻¹)/2 =
    (realMean (fun j => ((x-d j)^2+s)⁻¹)-1/t)/2
  ring

/-- The horizontal partial derivative of the phase, squared height fixed. -/
theorem hasDerivAt_levelEnvelope_horizontal {N : ℕ} (d : Fin N → ℝ)
    (E t x s : ℝ) (_ht : 0 < t) (hs : LevelEnvelopeDomain d x s) :
    HasDerivAt (fun u => levelEnvelopeAction d E t u s)
      ((x-E)/t+realMean (fun j => (x-d j)/((x-d j)^2+s))) x := by
  have hterms (j : Fin N) : HasDerivAt
      (fun u => Real.log ((u-d j)^2+s)) (2*(x-d j)/((x-d j)^2+s)) x := by
    simpa only [Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,id_eq,add_zero,Pi.pow_apply] using
      ((((hasDerivAt_id x).sub_const (d j)).pow 2).add_const s).log (ne_of_gt (hs.2 j))
  have hmain := ((((hasDerivAt_id x).sub_const E).pow 2).sub_const s).div_const (2*t)
  have hmean := ((HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hterms j)).const_mul
    (N : ℝ)⁻¹).div_const 2
  have h := hmain.add hmean
  simp only [Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,id_eq] at h
  apply h.congr_deriv
  change 2*(x-E)/(2*t)+realMean (fun j => 2*(x-d j)/((x-d j)^2+s))/2 = _
  have hm : realMean (fun j => 2*(x-d j)/((x-d j)^2+s)) =
      2*realMean (fun j => (x-d j)/((x-d j)^2+s)) := by
    rw [← envelope_mean_mul]
    congr 1
    funext j
    ring
  rw [hm]
  ring

/-- The partial derivative at fixed height, at the graph, has the desired coefficient;
this is not the total derivative of the moving graph action.
-/
theorem hasDerivAt_levelEnvelope_horizontal_at_graph {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (E t x : ℝ) (ht : 0 < t) :
    HasDerivAt (fun u => levelEnvelopeAction d E t u ((levelHeight d t x)^2))
      ((levelPsi d t x-E)/t) x := by
  have h := hasDerivAt_levelEnvelope_horizontal d E t x ((levelHeight d t x)^2) ht
    (levelHeight_sq_envelopeDomain hN d t x ht)
  apply h.congr_deriv
  change (x-E)/t+realMean (fun j => (x-d j)/((x-d j)^2+((levelHeight d t x)^2))) =
    (x+t*realMean (fun j => (x-d j)/((x-d j)^2+((levelHeight d t x)^2)))-E)/t
  field_simp [ne_of_gt ht]
  ring

/-- The phase is strictly concave on its whole pole-safe domain, including `s = 0` when
admissible. -/
theorem levelEnvelope_strictConcaveOn {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t x : ℝ) (ht : 0 < t) :
    StrictConcaveOn ℝ {s | LevelEnvelopeDomain d x s} (levelEnvelopeAction d E t x) := by
  have hdom : {s | LevelEnvelopeDomain d x s} =
      Set.Ici 0 ∩ ⋂ j, Set.Ioi (-((x-d j)^2)) := by
    ext s
    simp only [Set.mem_ofPred_eq,LevelEnvelopeDomain,Set.mem_inter_iff,
      Set.mem_Ici,Set.mem_iInter,Set.mem_Ioi]
    constructor
    · intro hs
      exact ⟨hs.1,fun j => by have h := hs.2 j; linarith⟩
    · intro hs
      exact ⟨hs.1,fun j => by have h := hs.2 j; linarith⟩
  have hc : Convex ℝ {s | LevelEnvelopeDomain d x s} := by
    rw [hdom]
    exact (convex_Ici 0).inter (convex_iInter fun j => convex_Ioi (-((x-d j)^2)))
  have hcont : ContinuousOn (levelEnvelopeAction d E t x)
      {s | LevelEnvelopeDomain d x s} := by
    intro s hs
    exact (hasDerivAt_levelEnvelope_vertical d E t x s ht hs).continuousAt.continuousWithinAt
  apply StrictAntiOn.strictConcaveOn_of_deriv hc hcont
  intro s hs u hu hsu
  have hs' : LevelEnvelopeDomain d x s := (interior_subset : interior {s | LevelEnvelopeDomain d x s} ⊆ {s | LevelEnvelopeDomain d x s}) hs
  have hu' : LevelEnvelopeDomain d x u := (interior_subset : interior {s | LevelEnvelopeDomain d x s} ⊆ {s | LevelEnvelopeDomain d x s}) hu
  rw [(hasDerivAt_levelEnvelope_vertical d E t x u ht hu').deriv,
    (hasDerivAt_levelEnvelope_vertical d E t x s ht hs').deriv]
  exact levelEnvelopeSlope_strictAnti hN d t x s u hs' hu' hsu

/-- The cross admissibility conditions hold for all `u` near `x`. -/
theorem levelEnvelope_local_cross_admissible {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (t x : ℝ) (ht : 0 < t) :
    ∀ᶠ u in nhds x,
      LevelEnvelopeDomain d u ((levelHeight d t x)^2) ∧
        LevelEnvelopeDomain d x ((levelHeight d t u)^2) := by
  have hall : ∀ᶠ u in nhds x, ∀ j : Fin N,
      0 < (u-d j)^2+((levelHeight d t x)^2) ∧
        0 < (x-d j)^2+((levelHeight d t u)^2) := by
    rw [eventually_all]
    intro j
    have hpos := levelGraph_denominator_pos hN d t x ht j
    have hc₁ : Continuous (fun u : ℝ => (u-d j)^2+((levelHeight d t x)^2)) :=
      ((continuous_id.sub continuous_const).pow 2).add continuous_const
    have hc₂ : Continuous (fun u : ℝ => (x-d j)^2+((levelHeight d t u)^2)) :=
      continuous_const.add (levelHeight_sq_continuous hN d t ht)
    exact (hc₁.continuousAt.eventually (eventually_gt_nhds hpos)).and
      (hc₂.continuousAt.eventually (eventually_gt_nhds hpos))
  filter_upwards [hall] with u hu
  exact ⟨⟨sq_nonneg _,fun j => (hu j).1⟩,⟨sq_nonneg _,fun j => (hu j).2⟩⟩

/-- The two-sided increment bound holds for all `u` near `x`. -/
theorem levelEnvelope_local_increment_sandwich {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (E t x : ℝ) (ht : 0 < t) :
    ∀ᶠ u in nhds x,
      levelEnvelopeAction d E t u ((levelHeight d t x)^2)-levelAction d E t x ≤
        levelAction d E t u-levelAction d E t x ∧
      levelAction d E t u-levelAction d E t x ≤
        levelAction d E t u-levelEnvelopeAction d E t x ((levelHeight d t u)^2) := by
  filter_upwards [levelEnvelope_local_cross_admissible hN d t x ht] with u hu
  exact levelEnvelope_increment_sandwich hN d E t x u ht hu.1 hu.2

/-- The phase is C¹ as a function of `(x, s)` near every admissible point. -/
theorem contDiffAt_levelEnvelope {N : ℕ} (d : Fin N → ℝ)
    (E t x s : ℝ) (hs : LevelEnvelopeDomain d x s) :
    ContDiffAt ℝ 1 (fun p : ℝ × ℝ => levelEnvelopeAction d E t p.1 p.2) (x,s) := by
  have hmain : ContDiffAt ℝ 1 (fun p : ℝ × ℝ => ((p.1-E)^2-p.2)/(2*t)) (x,s) := by
    fun_prop
  have hterms (j : Fin N) : ContDiffAt ℝ 1
      (fun p : ℝ × ℝ => Real.log ((p.1-d j)^2+p.2)) (x,s) := by
    have hp : ContDiff ℝ 1 (fun p : ℝ × ℝ => (p.1-d j)^2+p.2) := by fun_prop
    exact hp.contDiffAt.log (ne_of_gt (hs.2 j))
  have hsum := ContDiffAt.sum (s := Finset.univ) (fun j _ => hterms j)
  have hc : ContDiffAt ℝ 1 (fun _ : ℝ × ℝ => (N : ℝ)⁻¹) (x,s) := contDiffAt_const
  have h := hmain.add ((hc.mul hsum).div_const 2)
  simpa only [levelEnvelopeAction,realMean,Pi.add_apply,Pi.mul_apply] using h

/-- Strict Fréchet differentiability of the phase in `(x, s)`. -/
theorem hasStrictFDerivAt_levelEnvelope {N : ℕ} (d : Fin N → ℝ)
    (E t x s : ℝ) (hs : LevelEnvelopeDomain d x s) :
    HasStrictFDerivAt (fun p : ℝ × ℝ => levelEnvelopeAction d E t p.1 p.2)
      (fderiv ℝ (fun p : ℝ × ℝ => levelEnvelopeAction d E t p.1 p.2) (x,s)) (x,s) :=
  (contDiffAt_levelEnvelope d E t x s hs).hasStrictFDerivAt (by norm_num)

/-- The horizontal remainder along the moving height `s = y(u)²` is `o(|u - x|)`, however fast
the height moves. -/
theorem levelEnvelope_moving_horizontal_remainder {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (E t x : ℝ) (ht : 0 < t) :
    (fun u => levelEnvelopeAction d E t u ((levelHeight d t u)^2)-
      levelEnvelopeAction d E t x ((levelHeight d t u)^2)-
        (u-x)*((levelPsi d t x-E)/t)) =o[nhds x] (fun u => u-x) := by
  let F : ℝ × ℝ → ℝ := fun p => levelEnvelopeAction d E t p.1 p.2
  let s₀ := (levelHeight d t x)^2
  let L := fderiv ℝ F (x,s₀)
  have hf : HasStrictFDerivAt F L (x,s₀) := hasStrictFDerivAt_levelEnvelope d E t x s₀
    (levelHeight_sq_envelopeDomain hN d t x ht)
  have hline : HasDerivAt (fun u : ℝ => (u,s₀)) (1,0) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_const x s₀)
  have hh : HasDerivAt (fun u => levelEnvelopeAction d E t u s₀) (L (1,0)) x := by
    convert! hf.hasFDerivAt.comp_hasDerivAt x hline using 1
  have hLc : L (1,0) = (levelPsi d t x-E)/t :=
    hh.unique (hasDerivAt_levelEnvelope_horizontal_at_graph hN d E t x ht)
  have hY := levelHeight_sq_continuous hN d t ht
  have hp : Tendsto (fun u => ((u,(levelHeight d t u)^2),(x,(levelHeight d t u)^2)))
      (nhds x) (nhds ((x,s₀),(x,s₀))) := by
    exact ((continuous_id.prodMk hY).prodMk (continuous_const.prodMk hY)).continuousAt
  have ho := hf.isLittleO.comp_tendsto hp
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  filter_upwards [ho.bound hε] with u hu
  have hdelta : (u,(levelHeight d t u)^2)-(x,(levelHeight d t u)^2) =
      (u-x) • ((1,0) : ℝ × ℝ) := by ext <;> simp
  simp only [Function.comp_apply] at hu
  rw [hdelta,map_smul,hLc] at hu
  simpa [F,smul_eq_mul,norm_smul] using hu

/-- The level action has derivative `(ψ - E)/t` at every real `x`, including the zero-height
gaps and their endpoints. -/
theorem hasDerivAt_levelAction_global {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t x : ℝ) (ht : 0 < t) :
    HasDerivAt (levelAction d E t) ((levelPsi d t x-E)/t) x := by
  have hlow := (hasDerivAt_levelEnvelope_horizontal_at_graph hN d E t x ht).isLittleO
  have hup := levelEnvelope_moving_horizontal_remainder hN d E t x ht
  apply HasDerivAt.of_isLittleO
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  filter_upwards [levelEnvelope_local_increment_sandwich hN d E t x ht,
    hlow.bound hε,hup.bound hε] with u hs hl hu
  change ‖levelEnvelopeAction d E t u ((levelHeight d t x)^2)-levelAction d E t x-
    (u-x)*((levelPsi d t x-E)/t)‖ ≤ ε*‖u-x‖ at hl
  change ‖levelAction d E t u-levelEnvelopeAction d E t x ((levelHeight d t u)^2)-
    (u-x)*((levelPsi d t x-E)/t)‖ ≤ ε*‖u-x‖ at hu
  simp only [Real.norm_eq_abs] at hl hu
  have hll := (abs_le.mp hl).1
  have huu := (abs_le.mp hu).2
  change ‖levelAction d E t u-levelAction d E t x-(u-x)*((levelPsi d t x-E)/t)‖ ≤ ε*‖u-x‖
  simp only [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · linarith [hs.1]
  · linarith [hs.2]

end BlockBand.GaussianBulk
