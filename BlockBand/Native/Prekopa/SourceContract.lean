module

public import BlockBand.External.Prekopa.SourceStatement
public import BlockBand.Native.Prekopa.BlockBand.External.Auxiliary.BridgeMeshPrekopaLeindlerClosure
public import Mathlib.Analysis.Convex.Measure

/-!
# Proof of Prékopa's theorem on log-concave marginals

Prékopa's Theorem 6, in the form `BlockBand.External.Prekopa.SourceContract`, is proved from the
Prékopa–Leindler inequality on `ℝᵐ`: for a log-concave `f` on `ℝⁿ × ℝᵐ` and a convex `A ⊆ ℝᵐ`, the
slices `y ↦ 1_A(y) f(x, y)` are null-measurable and satisfy the pointwise Prékopa–Leindler
hypothesis, so the marginal `x ↦ ∫_A f(x, y) dy` is log-concave.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Native.Prekopa

open MeasureTheory Set
open scoped NNReal ENNReal

/-- Three-function Prékopa–Leindler for Lebesgue measure on `ℝᵐ` (`volume` on `Fin m → ℝ` is
the product of real Lebesgue measures), for measurable `ℝ≥0∞`-valued functions. -/
theorem prekopaLeindler_volume (m : ℕ) :
    PrekopaNative.BlockBand.MeasurePrekopaLeindler (Fin m → ℝ)
      (volume : Measure (Fin m → ℝ)) :=
  PrekopaNative.BlockBand.measurePrekopaLeindler_euclidean_pi_unconditional m

/-- Three-function Prékopa–Leindler on `ℝᵐ` with lower integrals: `u, v` arbitrary, `w`
a.e.-measurable for Lebesgue measure, `a, b > 0`, `a + b = 1`, and
`u y ^ a * v y' ^ b ≤ w (a • y + b • y')` everywhere. -/
theorem prekopaLeindler_of_aemeasurable {m : ℕ} (u v w : (Fin m → ℝ) → ℝ≥0∞)
    (hw : AEMeasurable w volume) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (h : ∀ y y', u y ^ a * v y' ^ b ≤ w (a • y + b • y')) :
    (∫⁻ y, u y) ^ a * (∫⁻ y, v y) ^ b ≤ ∫⁻ y, w y := by
  classical
  obtain ⟨u', hu'm, hu'le, hu'eq⟩ := exists_measurable_le_lintegral_eq volume u
  obtain ⟨v', hv'm, hv'le, hv'eq⟩ := exists_measurable_le_lintegral_eq volume v
  obtain ⟨N, hNsub, hNm, hN0⟩ : ∃ N : Set (Fin m → ℝ),
      {y | w y ≠ hw.mk w y} ⊆ N ∧ MeasurableSet N ∧ volume N = 0 :=
    ⟨toMeasurable volume _, subset_toMeasurable _ _, measurableSet_toMeasurable _ _, by
      rw [measure_toMeasurable]; exact ae_iff.1 hw.ae_eq_mk⟩
  let w' : (Fin m → ℝ) → ℝ≥0∞ := N.piecewise (fun _ => ∞) (hw.mk w)
  have hw'm : Measurable w' := Measurable.piecewise hNm measurable_const hw.measurable_mk
  have hww' : ∀ y, w y ≤ w' y := by
    intro y
    by_cases hy : y ∈ N
    · simp [w', hy]
    · have : w y = hw.mk w y := by
        by_contra hne
        exact hy (hNsub hne)
      simp [w', hy, this]
  have hw'eq : ∫⁻ y, w' y = ∫⁻ y, w y := by
    rw [lintegral_congr_ae hw.ae_eq_mk]
    apply lintegral_congr_ae
    have : ∀ᵐ y ∂(volume : Measure (Fin m → ℝ)), y ∉ N := by
      rw [ae_iff]
      simpa using hN0
    filter_upwards [this] with y hy
    simp [w', hy]
  have key := prekopaLeindler_volume m u' v' w' hu'm hv'm hw'm a b ha hb hab
    (fun y y' => (mul_le_mul' (ENNReal.rpow_le_rpow (hu'le y) ha.le)
      (ENNReal.rpow_le_rpow (hv'le y') hb.le)).trans ((h y y').trans (hww' _)))
  rw [hu'eq, hv'eq, ← hw'eq]
  exact key

/-- For a null-measurable integrand, the lower integral against the completed measure equals
the lower integral against the measure itself. -/
theorem lintegral_completion_eq {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (F : α → ℝ≥0∞) (hF : NullMeasurable F μ) :
    ∫⁻ y : NullMeasurableSpace α μ, F y ∂μ.completion = ∫⁻ y, F y ∂μ := by
  have hG := hF.aemeasurable
  -- the identity `NullMeasurableSpace α μ → α` is measurable and pushes `μ.completion` to `μ`
  let ι : NullMeasurableSpace α μ → α := fun y => y
  have hid : Measurable ι := fun s hs => MeasurableSet.nullMeasurableSet (μ := μ) hs
  have hmap : Measure.map ι μ.completion = μ := by
    ext s hs
    rw [Measure.map_apply hid hs]
    exact Measure.completion_apply μ s
  calc ∫⁻ y : NullMeasurableSpace α μ, F y ∂μ.completion
      = ∫⁻ y : NullMeasurableSpace α μ, hG.mk F (ι y) ∂μ.completion := by
        apply lintegral_congr_ae
        rw [Measure.ae_completion]
        exact hG.ae_eq_mk
    _ = ∫⁻ y, hG.mk F y ∂(Measure.map ι μ.completion) :=
        (lintegral_map (μ := μ.completion) hG.measurable_mk hid).symm
    _ = ∫⁻ y, hG.mk F y ∂μ := by rw [hmap]
    _ = ∫⁻ y, F y ∂μ := (lintegral_congr_ae hG.ae_eq_mk).symm

/-- The slice `y ↦ 1_A(y) f(x, y)` integrated in `BlockBand.External.Prekopa.marginal`. -/
def slice {n m : ℕ} (f : ((Fin n → ℝ) × (Fin m → ℝ)) → ℝ≥0) (A : Set (Fin m → ℝ))
    (x : Fin n → ℝ) : (Fin m → ℝ) → ℝ≥0∞ := by
  classical
  exact fun y => if y ∈ A then (f (x, y) : ℝ≥0∞) else 0

/-- The marginal is the lower integral of the slice against completed Lebesgue
measure (definitional). -/
theorem marginal_eq_slice {n m : ℕ} (f : ((Fin n → ℝ) × (Fin m → ℝ)) → ℝ≥0)
    (A : Set (Fin m → ℝ)) (x : Fin n → ℝ) :
    BlockBand.External.Prekopa.marginal f A x =
      ∫⁻ y : NullMeasurableSpace (Fin m → ℝ) (volume : Measure (Fin m → ℝ)), slice f A x y
        ∂(volume : Measure (Fin m → ℝ)).completion := rfl

/-- A weighted geometric mean of two `ℝ≥0∞` values above `t` is above `t`, if the first value
is finite (then so is their minimum). -/
theorem lt_geomMean {t p q : ℝ≥0∞} (hp : t < p) (hq : t < q) (hpt : p ≠ ∞)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) : t < p ^ a * q ^ b := by
  set r := min p q
  have hr : t < r := lt_min hp hq
  have hr0 : r ≠ 0 := (lt_of_le_of_lt zero_le hr).ne'
  have hrt : r ≠ ∞ := ne_top_of_le_ne_top hpt (min_le_left _ _)
  calc t < r := hr
    _ = r ^ a * r ^ b := by rw [← ENNReal.rpow_add a b hr0 hrt, hab, ENNReal.rpow_one]
    _ ≤ p ^ a * q ^ b :=
        mul_le_mul' (ENNReal.rpow_le_rpow (min_le_left _ _) ha.le)
          (ENNReal.rpow_le_rpow (min_le_right _ _) hb.le)

/-- Slices of a jointly log-concave finite density over a convex set are Lebesgue
null-measurable: every superlevel set is convex. -/
theorem slice_nullMeasurable {n m : ℕ} {f : ((Fin n → ℝ) × (Fin m → ℝ)) → ℝ≥0}
    {A : Set (Fin m → ℝ)} (hf : BlockBand.External.Prekopa.JointLogConcave n m f)
    (hA : Convex ℝ A) (x : Fin n → ℝ) :
    NullMeasurable (slice f A x) (volume : Measure (Fin m → ℝ)) := by
  classical
  refine measurable_of_Ioi fun t => ?_
  change NullMeasurableSet (slice f A x ⁻¹' Ioi t) volume
  apply Convex.nullMeasurableSet
  rw [convex_iff_forall_pos]
  intro y hy y' hy' a b ha hb hab
  simp only [slice, mem_preimage, mem_Ioi] at hy hy' ⊢
  by_cases hyA : y ∈ A
  · by_cases hy'A : y' ∈ A
    · have hmem : a • y + b • y' ∈ A := hA hyA hy'A ha.le hb.le hab
      simp only [hyA, hy'A, hmem, ↓reduceIte] at hy hy' ⊢
      have hb' : b = 1 - a := by linarith
      have hlc := hf (x, y) (x, y') a ha (by linarith)
      have hpt : a • (x, y) + b • (x, y') = (x, a • y + b • y') := by
        rw [Prod.smul_mk, Prod.smul_mk, Prod.mk_add_mk, ← add_smul, hab, one_smul]
      rw [← hb', hpt] at hlc
      exact (lt_geomMean hy hy' ENNReal.coe_ne_top ha hb hab).trans_le hlc
    · simp only [hy'A, ↓reduceIte] at hy'
      exact absurd hy' ENNReal.not_lt_zero
  · simp only [hyA, ↓reduceIte] at hy
    exact absurd hy ENNReal.not_lt_zero

/-- The pointwise Prékopa–Leindler hypothesis for the three slices at `x`, `x'` and
`a • x + (1 - a) • x'`. -/
theorem slice_pointwise {n m : ℕ} {f : ((Fin n → ℝ) × (Fin m → ℝ)) → ℝ≥0}
    {A : Set (Fin m → ℝ)} (hf : BlockBand.External.Prekopa.JointLogConcave n m f)
    (hA : Convex ℝ A) (x x' : Fin n → ℝ) {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (y y' : Fin m → ℝ) :
    slice f A x y ^ a * slice f A x' y' ^ (1 - a) ≤
      slice f A (a • x + (1 - a) • x') (a • y + (1 - a) • y') := by
  classical
  have hb : 0 < 1 - a := by linarith
  simp only [slice]
  by_cases hyA : y ∈ A
  · by_cases hy'A : y' ∈ A
    · have hmem : a • y + (1 - a) • y' ∈ A := hA hyA hy'A ha.le hb.le (by ring)
      simp only [hyA, hy'A, hmem, ↓reduceIte]
      have hlc := hf (x, y) (x', y') a ha ha1
      simpa only [Prod.smul_mk, Prod.mk_add_mk] using hlc
    · simp only [hy'A, ↓reduceIte, ENNReal.zero_rpow_of_pos hb, mul_zero]
      exact zero_le
  · simp only [hyA, ↓reduceIte, ENNReal.zero_rpow_of_pos ha, zero_mul]
    exact zero_le

/-- Prékopa (1973), Theorem 6, in the form `BlockBand.External.Prekopa.SourceContract`,
with no hypothesis: marginals over convex sets of jointly log-concave finite densities, taken as
lower integrals against completed Lebesgue measure, are log-concave in `ℝ≥0∞`.
-/
theorem sourceContract_holds : BlockBand.External.Prekopa.SourceContract where
  theorem6 n m f A hf hA := by
    intro x x' a ha ha1
    have hb : 0 < 1 - a := by linarith
    rw [marginal_eq_slice, marginal_eq_slice, marginal_eq_slice,
      lintegral_completion_eq _ _ (slice_nullMeasurable hf hA x),
      lintegral_completion_eq _ _ (slice_nullMeasurable hf hA x'),
      lintegral_completion_eq _ _ (slice_nullMeasurable hf hA _)]
    exact prekopaLeindler_of_aemeasurable _ _ _
      (slice_nullMeasurable hf hA _).aemeasurable a (1 - a) ha hb (by ring)
      (slice_pointwise hf hA x x' ha ha1)

/-- `sourceContract_holds` in `Nonempty` form (the contract is a `Prop`).
-/
theorem nonempty_sourceContract : Nonempty BlockBand.External.Prekopa.SourceContract :=
  ⟨sourceContract_holds⟩

end BlockBand.Native.Prekopa
