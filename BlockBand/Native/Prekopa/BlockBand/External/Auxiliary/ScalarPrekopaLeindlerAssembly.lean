module

public import BlockBand.Native.Prekopa.BlockBand.External.Auxiliary.ScalarPrekopaSpatialTruncation
public import BlockBand.Native.Prekopa.BlockBand.External.Auxiliary.CenteredIntervalRearrangement
public import Mathlib.Analysis.MeanInequalities

/-!
# Scalar Prékopa–Leindler from measurable one-dimensional Brunn–Minkowski

This module assembles the scalar three-function Prékopa–Leindler inequality from the
value and spatial truncations, Cavalieri's formula, and the centered-rearrangement
set input developed in the neighbouring auxiliary modules.  The only hypothesis
is the weighted Brunn–Minkowski inequality for nonempty measurable subsets of
`ℝ` having finite Lebesgue measure (`MeasurableWeightedBrunnMinkowski`, proved as
`measurableWeightedBrunnMinkowski`).  In particular, neither scalar Prékopa–Leindler
itself nor a bridge marginal-convexity conclusion is assumed.

The proof first treats finite-valued functions whose positive superlevels have finite
measure.  It normalizes both source heights, integrates the set-level weighted
Brunn–Minkowski inequality over their common layers, and applies weighted AM–GM.
Spatial truncation supplies finite superlevels, and value truncation followed by
monotone convergence removes all auxiliary restrictions.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace PrekopaNative.BlockBand

open Filter MeasureTheory Set
open scoped ENNReal Pointwise Topology

/-- The weighted Brunn–Minkowski inequality for measurable sets, stated in the mathematically
natural extended-nonnegative-real form.  Empty sets are excluded because a
positive weighted Minkowski sum with an empty summand is empty; the normalized
Cavalieri layers used below are nonempty.  Finiteness is required only of the
two source sets, exactly as supplied by spatial truncation.  No finiteness is
required of the Minkowski sum: when its volume is infinite the inequality is
correctly automatic. -/
def MeasurableWeightedBrunnMinkowski : Prop :=
  ∀ (A B : Set ℝ), MeasurableSet A → MeasurableSet B →
    volume A ≠ ∞ → volume B ≠ ∞ → A.Nonempty → B.Nonempty →
    ∀ (a b : ℝ), 0 < a → 0 < b → a + b = 1 →
      ENNReal.ofReal a * volume A + ENNReal.ofReal b * volume B ≤
        volume (a • A + b • B)

/-- Volume profiles of closed superlevels are measurable in the height variable. -/
theorem measurable_volume_superlevel_toReal (f : ℝ → ℝ≥0∞) :
    Measurable (fun t : ℝ => volume {x : ℝ | t ≤ (f x).toReal}) := by
  apply Antitone.measurable
  intro s t hst
  exact measure_mono (fun _ hx => hst.trans hx)

/-- Convert the real-volume formulation of the residual Brunn–Minkowski datum
back to an `ENNReal` measure inequality.  Only the two source masses need be
finite; an infinite target makes the conclusion automatic. -/
theorem ennreal_weighted_measure_le_of_brunnMinkowski
    {A B C : Set ℝ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hA : volume A ≠ ∞) (hB : volume B ≠ ∞)
    (hBM : WeightedBrunnMinkowskiData A B a b)
    (hsub : a • A + b • B ⊆ C) :
    ENNReal.ofReal a * volume A + ENNReal.ofReal b * volume B ≤ volume C := by
  by_cases hC : volume C = ∞
  · simp [hC]
  have hreal : a * volume.real A + b * volume.real B ≤ volume.real C :=
    hBM.trans (measureReal_mono hsub)
  rw [← ofReal_measureReal hA, ← ofReal_measureReal hB,
    ← ofReal_measureReal hC]
  rw [← ENNReal.ofReal_mul ha.le, ← ENNReal.ofReal_mul hb.le,
    ← ENNReal.ofReal_add (mul_nonneg ha.le measureReal_nonneg) (mul_nonneg hb.le measureReal_nonneg)]
  exact ENNReal.ofReal_le_ofReal hreal

/-- Weighted AM–GM for extended nonnegative reals, in the real-weight form
used by the scalar integral inequality. -/
theorem ennreal_geom_mean_le_arith_mean2_weighted
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (p q : ℝ≥0∞) :
    p ^ a * q ^ b ≤ ENNReal.ofReal a * p + ENNReal.ofReal b * q := by
  by_cases hp : p = ∞
  · rw [hp]
    have hwa : ENNReal.ofReal a ≠ 0 := (ENNReal.ofReal_pos.mpr ha).ne'
    simp [hwa]
  by_cases hq : q = ∞
  · rw [hq]
    have hwb : ENNReal.ofReal b ≠ 0 := (ENNReal.ofReal_pos.mpr hb).ne'
    simp [hwb]
  let wa : NNReal := ⟨a, ha.le⟩
  let wb : NNReal := ⟨b, hb.le⟩
  have hw : wa + wb = 1 := NNReal.eq hab
  have hnn := NNReal.geom_mean_le_arith_mean2_weighted
    wa wb p.toNNReal q.toNNReal hw
  have hcast :
      (↑(p.toNNReal ^ a * q.toNNReal ^ b) : ℝ≥0∞) ≤
        ↑(wa * p.toNNReal + wb * q.toNNReal) := by
    exact_mod_cast hnn
  have hwa : ENNReal.ofReal a = (wa : ℝ≥0∞) := by
    rw [ENNReal.coe_nnreal_eq]
    congr
  have hwb : ENNReal.ofReal b = (wb : ℝ≥0∞) := by
    rw [ENNReal.coe_nnreal_eq]
    congr
  rw [← ENNReal.coe_toNNReal hp, ← ENNReal.coe_toNNReal hq, hwa, hwb]
  rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_nonneg _ ha.le,
    ENNReal.coe_rpow_of_nonneg _ hb.le, ENNReal.coe_add,
    ENNReal.coe_mul, ENNReal.coe_mul] at hcast
  exact hcast

/-- Finite-layer normalized Prékopa–Leindler.  This is the Cavalieri assembly:
the source functions have height one, all values are finite, and positive source
superlevels have finite mass.  The conclusion follows solely from the stated
measurable-set Brunn–Minkowski input. -/
theorem scalarPrekopaLeindler_normalized_of_weightedBrunnMinkowski
    (hBM : MeasurableWeightedBrunnMinkowski)
    (f g h : ℝ → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (hh : Measurable h) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1)
    (hffinite : ∀ x, f x ≠ ∞) (hgfinite : ∀ x, g x ≠ ∞)
    (hhfinite : ∀ x, h x ≠ ∞)
    (hflevels : ∀ t : ℝ, 0 < t → volume {x : ℝ | t ≤ (f x).toReal} ≠ ∞)
    (hglevels : ∀ t : ℝ, 0 < t → volume {x : ℝ | t ≤ (g x).toReal} ≠ ∞)
    (hfsup : iSup f = 1) (hgsup : iSup g = 1)
    (hpw : ∀ x y, f x ^ a * g y ^ b ≤ h (a * x + b * y)) :
    (∫⁻ x, f x) ^ a * (∫⁻ y, g y) ^ b ≤ ∫⁻ z, h z := by
  let vf : ℝ → ℝ≥0∞ := fun t => volume {x : ℝ | t ≤ (f x).toReal}
  let vg : ℝ → ℝ≥0∞ := fun t => volume {x : ℝ | t ≤ (g x).toReal}
  let vh : ℝ → ℝ≥0∞ := fun t => volume {x : ℝ | t ≤ (h x).toReal}
  have hf_bound : ∀ x, f x ≤ 1 := fun x => by
    rw [← hfsup]
    exact le_iSup f x
  have hg_bound : ∀ x, g x ≤ 1 := fun x => by
    rw [← hgsup]
    exact le_iSup g x
  have hlayer (t : ℝ) (ht : 0 < t) (htone : t ≠ 1) :
      ENNReal.ofReal a * vf t + ENNReal.ofReal b * vg t ≤ vh t := by
    by_cases htlt : t < 1
    · have hAf : MeasurableSet {x : ℝ | t ≤ (f x).toReal} :=
        measurableSet_le measurable_const (ENNReal.measurable_toReal.comp hf)
      have hAg : MeasurableSet {x : ℝ | t ≤ (g x).toReal} :=
        measurableSet_le measurable_const (ENNReal.measurable_toReal.comp hg)
      have hAnon : {x : ℝ | t ≤ (f x).toReal}.Nonempty := by
        have hlt : ENNReal.ofReal t < iSup f := by
          rw [hfsup]
          exact ENNReal.ofReal_lt_one.mpr htlt
        rcases exists_lt_of_lt_ciSup hlt with ⟨x, hx⟩
        exact ⟨x, (ENNReal.ofReal_le_iff_le_toReal (hffinite x)).mp hx.le⟩
      have hBnon : {x : ℝ | t ≤ (g x).toReal}.Nonempty := by
        have hlt : ENNReal.ofReal t < iSup g := by
          rw [hgsup]
          exact ENNReal.ofReal_lt_one.mpr htlt
        rcases exists_lt_of_lt_ciSup hlt with ⟨x, hx⟩
        exact ⟨x, (ENNReal.ofReal_le_iff_le_toReal (hgfinite x)).mp hx.le⟩
      have hset :
          a • {x : ℝ | t ≤ (f x).toReal} + b • {x : ℝ | t ≤ (g x).toReal} ⊆
            {z : ℝ | t ≤ (h z).toReal} := by
        rintro z ⟨u, ⟨x, hx, rfl⟩, v, ⟨y, hy, rfl⟩, rfl⟩
        apply (ENNReal.ofReal_le_iff_le_toReal (hhfinite _)).mp
        have htx : ENNReal.ofReal t ≤ f x :=
          (ENNReal.ofReal_le_iff_le_toReal (hffinite x)).mpr hx
        have hty : ENNReal.ofReal t ≤ g y :=
          (ENNReal.ofReal_le_iff_le_toReal (hgfinite y)).mpr hy
        calc
          ENNReal.ofReal t = (ENNReal.ofReal t) ^ a * (ENNReal.ofReal t) ^ b := by
            rw [← ENNReal.rpow_add _ _ (ne_of_gt (ENNReal.ofReal_pos.mpr ht))
              ENNReal.ofReal_ne_top, hab, ENNReal.rpow_one]
          _ ≤ f x ^ a * g y ^ b := by
            exact mul_le_mul (ENNReal.rpow_le_rpow htx ha.le)
              (ENNReal.rpow_le_rpow hty hb.le) zero_le zero_le
          _ ≤ h (a * x + b * y) := hpw x y
      exact (hBM _ _ hAf hAg (hflevels t ht) (hglevels t ht)
        hAnon hBnon a b ha hb hab).trans (measure_mono (by
          simpa [smul_eq_mul] using hset))
    · have hone : 1 < t := lt_of_le_of_ne (not_lt.mp htlt) (Ne.symm htone)
      have hfempty : {x : ℝ | t ≤ (f x).toReal} = ∅ := by
        ext x
        constructor
        · intro hx
          have hle : (f x).toReal ≤ 1 := by
            have hmono := ENNReal.toReal_mono (by simp) (hf_bound x)
            simpa using hmono
          exact (not_le_of_gt hone) (hx.trans hle)
        · simp
      have hgempty : {x : ℝ | t ≤ (g x).toReal} = ∅ := by
        ext x
        constructor
        · intro hx
          have hle : (g x).toReal ≤ 1 := by
            have hmono := ENNReal.toReal_mono (by simp) (hg_bound x)
            simpa using hmono
          exact (not_le_of_gt hone) (hx.trans hle)
        · simp
      simp [vf, vg, hfempty, hgempty]
  have hintegral :
      ENNReal.ofReal a * (∫⁻ t in Ioi (0 : ℝ), vf t) +
          ENNReal.ofReal b * (∫⁻ t in Ioi (0 : ℝ), vg t) ≤
        ∫⁻ t in Ioi (0 : ℝ), vh t := by
    calc
      ENNReal.ofReal a * (∫⁻ t in Ioi (0 : ℝ), vf t) +
            ENNReal.ofReal b * (∫⁻ t in Ioi (0 : ℝ), vg t) =
          (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal a * vf t) +
            ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal b * vg t := by
              rw [lintegral_const_mul, lintegral_const_mul]
              · exact measurable_volume_superlevel_toReal g
              · exact measurable_volume_superlevel_toReal f
      _ = ∫⁻ t in Ioi (0 : ℝ),
            (ENNReal.ofReal a * vf t + ENNReal.ofReal b * vg t) := by
              rw [lintegral_add_left]
              exact (measurable_const.mul (measurable_volume_superlevel_toReal f))
      _ ≤ ∫⁻ t in Ioi (0 : ℝ), vh t := by
        apply lintegral_mono_ae
        rw [ae_restrict_iff]
        · have hne : ∀ᵐ t : ℝ ∂volume, t ≠ 1 := by
            rw [ae_iff]
            have hs : {t : ℝ | ¬t ≠ 1} = {1} := by
              ext t
              simp
            rw [hs]
            exact measure_singleton (μ := volume) (1 : ℝ)
          filter_upwards [hne] with t htne ht
          exact hlayer t ht htne
        · exact measurableSet_le
            ((measurable_const.mul (measurable_volume_superlevel_toReal f)).add
              (measurable_const.mul (measurable_volume_superlevel_toReal g)))
            (measurable_volume_superlevel_toReal h)

  rw [← ennreal_lintegral_eq_lintegral_superlevel_toReal f hf hffinite,
    ← ennreal_lintegral_eq_lintegral_superlevel_toReal g hg hgfinite,
    ← ennreal_lintegral_eq_lintegral_superlevel_toReal h hh hhfinite] at hintegral
  exact (ennreal_geom_mean_le_arith_mean2_weighted ha hb hab
    (∫⁻ x, f x) (∫⁻ y, g y)).trans hintegral

/-- Bounded-height scalar Prékopa–Leindler with finite source supports.  Height
normalization is internal, and the normalized target is clipped at one, so no
finiteness assumption is imposed on the original target. -/
theorem scalarPrekopaLeindler_boundedSupport_of_weightedBrunnMinkowski
    (hBM : MeasurableWeightedBrunnMinkowski)
    (f g h : ℝ → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (hh : Measurable h) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1)
    (hfsup : iSup f ≠ ∞) (hgsup : iSup g ≠ ∞)
    (hfsupport : volume {x : ℝ | f x ≠ 0} ≠ ∞)
    (hgsupport : volume {x : ℝ | g x ≠ 0} ≠ ∞)
    (hpw : ∀ x y, f x ^ a * g y ^ b ≤ h (a * x + b * y)) :
    (∫⁻ x, f x) ^ a * (∫⁻ y, g y) ^ b ≤ ∫⁻ z, h z := by
  by_cases hfzero : f = 0
  · simp [hfzero, ENNReal.zero_rpow_of_pos ha]
  by_cases hgzero : g = 0
  · simp [hgzero, ENNReal.zero_rpow_of_pos hb]
  let F : ℝ≥0∞ := iSup f
  let G : ℝ≥0∞ := iSup g
  let f' : ℝ → ℝ≥0∞ := fun x => f x * F⁻¹
  let g' : ℝ → ℝ≥0∞ := fun x => g x * G⁻¹
  let hraw : ℝ → ℝ≥0∞ := fun x => h x * F⁻¹ ^ a * G⁻¹ ^ b
  let h' : ℝ → ℝ≥0∞ := fun x => min (hraw x) 1
  have hF0 : F ≠ 0 := by
    intro hF
    apply hfzero
    funext x
    apply le_antisymm
    · exact (le_iSup f x).trans_eq hF
    · exact zero_le
  have hG0 : G ≠ 0 := by
    intro hG
    apply hgzero
    funext x
    apply le_antisymm
    · exact (le_iSup g x).trans_eq hG
    · exact zero_le
  have hFpos : 0 < F := pos_of_ne_zero hF0
  have hGpos : 0 < G := pos_of_ne_zero hG0
  have hf'meas : Measurable f' := hf.mul measurable_const
  have hg'meas : Measurable g' := hg.mul measurable_const
  have hrawmeas : Measurable hraw := (hh.mul measurable_const).mul measurable_const
  have h'meas : Measurable h' := hrawmeas.min measurable_const
  have hf'sup : iSup f' = 1 := by
    rw [show iSup f' = iSup f * F⁻¹ by
      simp only [f', ENNReal.iSup_mul]]
    exact ENNReal.mul_inv_cancel hF0 hfsup
  have hg'sup : iSup g' = 1 := by
    rw [show iSup g' = iSup g * G⁻¹ by
      simp only [g', ENNReal.iSup_mul]]
    exact ENNReal.mul_inv_cancel hG0 hgsup
  have hf'finite (x : ℝ) : f' x ≠ ∞ := by
    apply ENNReal.mul_ne_top
    · exact ne_top_of_le_ne_top hfsup (le_iSup f x)
    · exact ENNReal.inv_ne_top.mpr hF0
  have hg'finite (x : ℝ) : g' x ≠ ∞ := by
    apply ENNReal.mul_ne_top
    · exact ne_top_of_le_ne_top hgsup (le_iSup g x)
    · exact ENNReal.inv_ne_top.mpr hG0
  have h'finite (x : ℝ) : h' x ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  have hf'levels (t : ℝ) (ht : 0 < t) :
      volume {x : ℝ | t ≤ (f' x).toReal} ≠ ∞ := by
    apply ne_top_of_le_ne_top hfsupport
    apply measure_mono
    intro x hx
    change t ≤ (f' x).toReal at hx
    intro hzero
    have hz : (f' x).toReal = 0 := by simp [f', hzero]
    linarith
  have hg'levels (t : ℝ) (ht : 0 < t) :
      volume {x : ℝ | t ≤ (g' x).toReal} ≠ ∞ := by
    apply ne_top_of_le_ne_top hgsupport
    apply measure_mono
    intro x hx
    change t ≤ (g' x).toReal at hx
    intro hzero
    have hz : (g' x).toReal = 0 := by simp [g', hzero]
    linarith
  have hf'bound (x : ℝ) : f' x ≤ 1 := by
    rw [← hf'sup]
    exact le_iSup f' x
  have hg'bound (x : ℝ) : g' x ≤ 1 := by
    rw [← hg'sup]
    exact le_iSup g' x
  have hpw' : ∀ x y, f' x ^ a * g' y ^ b ≤ h' (a * x + b * y) := by
    intro x y
    apply le_min
    · dsimp [f', g', h', hraw]
      rw [ENNReal.mul_rpow_of_nonneg, ENNReal.mul_rpow_of_nonneg]
      · calc
          f x ^ a * F⁻¹ ^ a * (g y ^ b * G⁻¹ ^ b) =
              (f x ^ a * g y ^ b) * F⁻¹ ^ a * G⁻¹ ^ b := by ac_rfl
          _ ≤ h (a * x + b * y) * F⁻¹ ^ a * G⁻¹ ^ b := by
            gcongr
            exact hpw x y
      · exact hb.le
      · exact ha.le
    · calc
        f' x ^ a * g' y ^ b ≤ 1 ^ a * 1 ^ b :=
          mul_le_mul (ENNReal.rpow_le_rpow (hf'bound x) ha.le)
            (ENNReal.rpow_le_rpow (hg'bound y) hb.le) zero_le zero_le
        _ = 1 := by simp
  have hnorm := scalarPrekopaLeindler_normalized_of_weightedBrunnMinkowski
    hBM f' g' h' hf'meas hg'meas h'meas ha hb hab hf'finite hg'finite
      h'finite hf'levels hg'levels hf'sup hg'sup hpw'
  let fint := ∫⁻ x, f x
  let gint := ∫⁻ x, g x
  let hint := ∫⁻ x, h x
  let f'int := ∫⁻ x, f' x
  let g'int := ∫⁻ x, g' x
  let h'int := ∫⁻ x, h' x
  have hfint : f'int = fint * F⁻¹ := lintegral_mul_const F⁻¹ hf
  have hgint : g'int = gint * G⁻¹ := lintegral_mul_const G⁻¹ hg
  have hhint : h'int ≤ hint * F⁻¹ ^ a * G⁻¹ ^ b := by
    calc
      h'int ≤ ∫⁻ x, hraw x := lintegral_mono fun x => min_le_left _ _
      _ = hint * F⁻¹ ^ a * G⁻¹ ^ b := by
        dsimp [hraw, hint]
        rw [show (fun x => h x * F⁻¹ ^ a * G⁻¹ ^ b) =
            (fun x => h x * (F⁻¹ ^ a * G⁻¹ ^ b)) by
              funext x
              ac_rfl]
        rw [lintegral_mul_const _ hh]
        ac_rfl
  have hscaled : f'int ^ a * g'int ^ b ≤
      hint * F⁻¹ ^ a * G⁻¹ ^ b := hnorm.trans hhint
  have hFa0 : F ^ a ≠ 0 := (ENNReal.rpow_pos_of_nonneg hFpos ha.le).ne'
  have hGa0 : G ^ b ≠ 0 := (ENNReal.rpow_pos_of_nonneg hGpos hb.le).ne'
  have hFatop : F ^ a ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg ha.le hfsup
  have hGatop : G ^ b ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hb.le hgsup
  change fint ^ a * gint ^ b ≤ hint
  calc
    fint ^ a * gint ^ b = (f'int * F) ^ a * (g'int * G) ^ b := by
      rw [hfint, hgint]
      congr
      · exact (ENNReal.inv_mul_cancel_right hF0 hfsup).symm
      · exact (ENNReal.inv_mul_cancel_right hG0 hgsup).symm
    _ = (f'int ^ a * g'int ^ b) * (F ^ a * G ^ b) := by
      rw [ENNReal.mul_rpow_of_nonneg, ENNReal.mul_rpow_of_nonneg]
      · ac_rfl
      · exact hb.le
      · exact ha.le
    _ ≤ (hint * F⁻¹ ^ a * G⁻¹ ^ b) * (F ^ a * G ^ b) := by gcongr
    _ = hint * (F⁻¹ ^ a * F ^ a) * (G⁻¹ ^ b * G ^ b) := by ac_rfl
    _ = hint * ((F ^ a)⁻¹ * F ^ a) * ((G ^ b)⁻¹ * G ^ b) := by
      rw [ENNReal.inv_rpow, ENNReal.inv_rpow]
    _ = hint := by
      rw [ENNReal.inv_mul_cancel hFa0 hFatop, ENNReal.inv_mul_cancel hGa0 hGatop]
      simp

/-- Diagonal value-and-space truncation used in the final monotone passage. -/
def scalarPrekopaApproximation (f : ℝ → ℝ≥0∞) (n : ℕ) : ℝ → ℝ≥0∞ :=
  ennrealValueTruncation (ennrealSpatialTruncation f n) n

/-- The diagonal approximants are measurable. -/
theorem measurable_scalarPrekopaApproximation {f : ℝ → ℝ≥0∞}
    (hf : Measurable f) (n : ℕ) :
    Measurable (scalarPrekopaApproximation f n) :=
  measurable_ennrealValueTruncation (measurable_ennrealSpatialTruncation hf n) n

/-- The diagonal approximants increase simultaneously in window and height. -/
theorem monotone_scalarPrekopaApproximation (f : ℝ → ℝ≥0∞) :
    Monotone (scalarPrekopaApproximation f) := by
  intro n m hnm x
  exact min_le_min
    (monotone_ennrealSpatialTruncation f hnm x)
    (by exact_mod_cast hnm)

/-- Diagonal truncation converges pointwise to the original function. -/
theorem tendsto_scalarPrekopaApproximation_apply (f : ℝ → ℝ≥0∞) (x : ℝ) :
    Tendsto (fun n => scalarPrekopaApproximation f n x) atTop (𝓝 (f x)) := by
  apply (tendsto_ennrealValueTruncation (f x)).congr'
  filter_upwards [eventually_mem_realCompactWindow x] with n hn
  simp [scalarPrekopaApproximation, ennrealSpatialTruncation, hn,
    ennrealValueTruncation]

/-- Monotone convergence for the combined approximation. -/
theorem tendsto_lintegral_scalarPrekopaApproximation
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    Tendsto (fun n => ∫⁻ x, scalarPrekopaApproximation f n x) atTop
      (𝓝 (∫⁻ x, f x)) := by
  apply lintegral_tendsto_of_tendsto_of_monotone
  · intro n
    exact (measurable_scalarPrekopaApproximation hf n).aemeasurable
  · exact Filter.Eventually.of_forall fun x n m hnm =>
      monotone_scalarPrekopaApproximation f hnm x
  · exact Filter.Eventually.of_forall fun x =>
      tendsto_scalarPrekopaApproximation_apply f x

/-- Each diagonal approximant has bounded height. -/
theorem iSup_scalarPrekopaApproximation_ne_top (f : ℝ → ℝ≥0∞) (n : ℕ) :
    iSup (scalarPrekopaApproximation f n) ≠ ∞ := by
  apply ne_top_of_le_ne_top (ENNReal.natCast_ne_top n)
  apply iSup_le
  intro x
  exact min_le_right _ _

/-- The nonzero support of an approximant is contained in its compact window. -/
theorem volume_support_scalarPrekopaApproximation_ne_top
    (f : ℝ → ℝ≥0∞) (n : ℕ) :
    volume {x : ℝ | scalarPrekopaApproximation f n x ≠ 0} ≠ ∞ := by
  apply ne_top_of_le_ne_top (show volume (realCompactWindow n) ≠ ∞ by
    rw [realCompactWindow, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top)
  apply measure_mono
  intro x hx
  by_contra hnot
  have hz : ennrealSpatialTruncation f n x = 0 := by
    simp [ennrealSpatialTruncation, hnot]
  apply hx
  simp [scalarPrekopaApproximation, ennrealValueTruncation, hz]

/-- Complete scalar Prékopa–Leindler assembly.  The sole hypothesis is the
extended-nonnegative-real `MeasurableWeightedBrunnMinkowski` inequality
for nonempty measurable finite-volume source sets; all height normalization,
spatial truncation, value truncation, Cavalieri integration, and limiting
algebra are discharged here. -/
theorem scalarPrekopaLeindler_of_weightedBrunnMinkowski
    (hBM : MeasurableWeightedBrunnMinkowski) : ScalarPrekopaLeindler := by
  intro f g h hf hg hh a b ha hb hab hpw
  have happ (n : ℕ) :
      (∫⁻ x, scalarPrekopaApproximation f n x) ^ a *
          (∫⁻ y, scalarPrekopaApproximation g n y) ^ b ≤ ∫⁻ z, h z := by
    apply scalarPrekopaLeindler_boundedSupport_of_weightedBrunnMinkowski
      hBM (scalarPrekopaApproximation f n) (scalarPrekopaApproximation g n) h
      (measurable_scalarPrekopaApproximation hf n)
      (measurable_scalarPrekopaApproximation hg n) hh ha hb hab
      (iSup_scalarPrekopaApproximation_ne_top f n)
      (iSup_scalarPrekopaApproximation_ne_top g n)
      (volume_support_scalarPrekopaApproximation_ne_top f n)
      (volume_support_scalarPrekopaApproximation_ne_top g n)
    intro x y
    calc
      scalarPrekopaApproximation f n x ^ a *
          scalarPrekopaApproximation g n y ^ b ≤ f x ^ a * g y ^ b := by
        exact mul_le_mul
          (ENNReal.rpow_le_rpow
            ((ennrealValueTruncation_le _ _ x).trans
              (ennrealSpatialTruncation_le f n x)) ha.le)
          (ENNReal.rpow_le_rpow
            ((ennrealValueTruncation_le _ _ y).trans
              (ennrealSpatialTruncation_le g n y)) hb.le)
          zero_le zero_le
      _ ≤ h (a * x + b * y) := hpw x y
  have hfint := tendsto_lintegral_scalarPrekopaApproximation f hf
  have hgint := tendsto_lintegral_scalarPrekopaApproximation g hg
  let Fint : ℝ≥0∞ := (∫⁻ x, f x) ^ a
  let Gint : ℝ≥0∞ := (∫⁻ y, g y) ^ b
  by_cases hFint : Fint = 0
  · simp [Fint, hFint]
  by_cases hGint : Gint = 0
  · simp [Gint, hGint]
  have hlim : Tendsto
      (fun n => (∫⁻ x, scalarPrekopaApproximation f n x) ^ a *
        (∫⁻ y, scalarPrekopaApproximation g n y) ^ b)
      atTop (𝓝 (Fint * Gint)) :=
    ENNReal.Tendsto.mul (hfint.ennrpow_const a) (Or.inl hFint)
      (hgint.ennrpow_const b) (Or.inl hGint)
  change Fint * Gint ≤ ∫⁻ z, h z
  exact le_of_tendsto' hlim happ

end PrekopaNative.BlockBand
