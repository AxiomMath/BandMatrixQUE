module
public import BlockBand.SourceProcess.Stochastic.SDE.NativeTools
public import BlockBand.SourceProcess.Stochastic.SDE.Gronwall
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Deterministic estimates for SDE uniqueness and Picard

Generic, sample-free lemmas (Lebesgue measure on `(0,t]`, `ℝ≥0∞`-valued integrals).

* `enorm_sq_le_coord`: on a finite-dimensional `E`, `‖v‖ₑ² ≤ C_E ∑_j ‖coord_j v‖ₑ²` for the
  coordinates of `Module.finBasis ℝ E` (`C_E < ∞`).
* `enorm_sq_add_le`: `‖a + b‖ₑ² ≤ 2‖a‖ₑ² + 2‖b‖ₑ²`.
* `enorm_sq_integral_sub_le`: `‖∫_{(0,t]} f − ∫_{(0,t]} g‖ₑ² ≤ t ∫⁻_{(0,t]} h²` if `‖f − g‖ₑ ≤ h`;
* `enorm_sq_functional_drift_sub_le`: pathwise Cauchy–Schwarz for drift differences,
  `‖ℓ(∫_{(0,t]} f) − ℓ(∫_{(0,t]} g)‖ₑ² ≤ ‖ℓ‖ₑ² · t · ∫⁻_{(0,t]} h²` whenever `‖f − g‖ₑ ≤ h`.
* `eq_zero_of_lintegral_volterra`: a bounded a.e.-measurable `Ψ : ℝ → ℝ≥0∞` with
  `Ψ t ≤ L ∫⁻_{(0,t]} Ψ` on `[0,T]` vanishes on `[0,T]` (via the real Gronwall lemma
  `SDE.eq_zero_of_le_volterra`).
-/

namespace BlockBand.SourceProcess.Stochastic.NativeSDE
open MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

section Coordinates

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Coordinate functionals of `Module.finBasis ℝ E` as continuous linear maps. -/
def coordCLM (j : Fin (Module.finrank ℝ E)) : E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord j)

theorem coordCLM_apply (j : Fin (Module.finrank ℝ E)) (v : E) :
    coordCLM E j v = (Module.finBasis ℝ E).coord j v := rfl

/-- Norm equivalence with the coordinate sum of squares. -/
theorem enorm_sq_le_coord : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
    ∀ v : E, ‖v‖ₑ ^ 2 ≤ C * ∑ j, ‖coordCLM E j v‖ₑ ^ 2 := by
  classical
  let B := Module.finBasis ℝ E
  refine ⟨ENNReal.ofReal (∑ j, ‖B j‖ ^ 2), ENNReal.ofReal_ne_top, fun v => ?_⟩
  have hv : v = ∑ j, (B.coord j v) • B j := (B.sum_repr v).symm
  have h1 : ‖v‖ ≤ ∑ j, ‖B j‖ * |B.coord j v| := by
    conv_lhs => rw [hv]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
    rw [norm_smul, Real.norm_eq_abs, mul_comm]
  have h2 : ‖v‖ ^ 2 ≤ (∑ j, ‖B j‖ ^ 2) * ∑ j, (B.coord j v) ^ 2 := by
    calc ‖v‖ ^ 2 ≤ (∑ j, ‖B j‖ * |B.coord j v|) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (∑ j, ‖B j‖ ^ 2) * ∑ j, |B.coord j v| ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = _ := by simp only [sq_abs]
  have h3 : ∀ j, ‖coordCLM E j v‖ₑ ^ 2 = ENNReal.ofReal ((B.coord j v) ^ 2) := fun j => by
    rw [coordCLM_apply, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  simp only [h3]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg _),
    ← ENNReal.ofReal_mul (Finset.sum_nonneg fun j _ => sq_nonneg _), ← ofReal_norm,
    ← ENNReal.ofReal_pow (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal h2

/-- A vector all of whose coordinates vanish is zero. -/
theorem eq_zero_of_coord {v : E} (h : ∀ j, coordCLM E j v = 0) : v = 0 := by
  have hv : v = ∑ j, ((Module.finBasis ℝ E).coord j v) • (Module.finBasis ℝ E) j :=
    ((Module.finBasis ℝ E).sum_repr v).symm
  rw [hv]
  exact Finset.sum_eq_zero fun j _ => by rw [← coordCLM_apply, h j, zero_smul]

end Coordinates

theorem enorm_sq_add_le {G : Type*} [NormedAddCommGroup G] (a b : G) :
    ‖a + b‖ₑ ^ 2 ≤ 2 * ‖a‖ₑ ^ 2 + 2 * ‖b‖ₑ ^ 2 := by
  have h1 : ‖a + b‖ₑ ≤ ‖a‖ₑ + ‖b‖ₑ := enorm_add_le a b
  calc ‖a + b‖ₑ ^ 2 ≤ (‖a‖ₑ + ‖b‖ₑ) ^ 2 := pow_le_pow_left₀ zero_le h1 2
    _ ≤ 2 * ‖a‖ₑ ^ 2 + 2 * ‖b‖ₑ ^ 2 := by
      rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _),
        ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_pow (norm_nonneg _),
        ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_ofNat 2,
        ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

/-- Pathwise Cauchy–Schwarz bound for differences of drift integrals. -/
theorem enorm_sq_integral_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f g : ℝ → E} {h : ℝ → ℝ≥0∞} {t : ℝ}
    (hf : IntegrableOn f (Ioc 0 t)) (hg : IntegrableOn g (Ioc 0 t))
    (hfg : ∀ s ∈ Ioc 0 t, ‖f s - g s‖ₑ ≤ h s) (hh : AEMeasurable h (volume.restrict (Ioc 0 t))) :
    ‖(∫ s in Ioc 0 t, f s) - ∫ s in Ioc 0 t, g s‖ₑ ^ 2 ≤
      ENNReal.ofReal t * ∫⁻ s in Ioc 0 t, h s ^ 2 := by
  rw [← integral_sub hf hg]
  have h1 : ‖∫ s in Ioc 0 t, (f s - g s)‖ₑ ≤ ∫⁻ s in Ioc 0 t, h s :=
    (enorm_integral_le_lintegral_enorm _).trans
      (setLIntegral_mono' measurableSet_Ioc fun s hs => hfg s hs)
  have h2 := lintegral_sq_le_measure_mul hh
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioc, sub_zero] at h2
  exact (pow_le_pow_left₀ zero_le h1 2).trans h2

/-- Pathwise Cauchy–Schwarz bound for differences of functionals of drift integrals. -/
theorem enorm_sq_functional_drift_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f g : ℝ → E} {h : ℝ → ℝ≥0∞} {t : ℝ}
    (hf : IntegrableOn f (Ioc 0 t)) (hg : IntegrableOn g (Ioc 0 t))
    (hfg : ∀ s ∈ Ioc 0 t, ‖f s - g s‖ₑ ≤ h s) (hh : AEMeasurable h (volume.restrict (Ioc 0 t)))
    (ℓ : E →L[ℝ] ℝ) :
    ‖ℓ (∫ s in Ioc 0 t, f s) - ℓ (∫ s in Ioc 0 t, g s)‖ₑ ^ 2 ≤
      ‖ℓ‖ₑ ^ 2 * (ENNReal.ofReal t * ∫⁻ s in Ioc 0 t, h s ^ 2) := by
  rw [← map_sub, ← integral_sub hf hg]
  have h1 : ‖ℓ (∫ s in Ioc 0 t, (f s - g s))‖ₑ ≤ ‖ℓ‖ₑ * ∫⁻ s in Ioc 0 t, h s := by
    refine (ContinuousLinearMap.le_opENorm ℓ _).trans (mul_le_mul_right ?_ _)
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    exact setLIntegral_mono' measurableSet_Ioc fun s hs => hfg s hs
  have h2 := lintegral_sq_le_measure_mul hh
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioc, sub_zero] at h2
  calc ‖ℓ (∫ s in Ioc 0 t, (f s - g s))‖ₑ ^ 2 ≤ (‖ℓ‖ₑ * ∫⁻ s in Ioc 0 t, h s) ^ 2 :=
        pow_le_pow_left₀ zero_le h1 2
    _ = ‖ℓ‖ₑ ^ 2 * (∫⁻ s in Ioc 0 t, h s) ^ 2 := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_right h2 _

/-- **Volterra vanishing in `ℝ≥0∞` form.** -/
theorem eq_zero_of_lintegral_volterra {Ψ : ℝ → ℝ≥0∞} {T : ℝ} (hT : 0 ≤ T)
    (hΨm : AEMeasurable Ψ (volume.restrict (Ioc 0 T))) {M L : ℝ≥0∞} (hM : M ≠ ⊤) (hL : L ≠ ⊤)
    (hbd : ∀ t ∈ Icc 0 T, Ψ t ≤ M) (hle : ∀ t ∈ Icc 0 T, Ψ t ≤ L * ∫⁻ s in Ioc 0 t, Ψ s) :
    ∀ t ∈ Icc 0 T, Ψ t = 0 := by
  have hfin : ∀ t ∈ Icc 0 T, Ψ t ≠ ⊤ := fun t ht => ne_top_of_le_ne_top hM (hbd t ht)
  have hint_fin : ∀ t ∈ Icc 0 T, ∫⁻ s in Ioc 0 t, Ψ s ≠ ⊤ := by
    intro t ht
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hM (ENNReal.ofReal_ne_top (r := t))) ?_
    calc ∫⁻ s in Ioc 0 t, Ψ s ≤ ∫⁻ _ in Ioc 0 t, M :=
          setLIntegral_mono' measurableSet_Ioc fun s hs =>
            hbd s ⟨hs.1.le, hs.2.trans ht.2⟩
      _ = M * ENNReal.ofReal t := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero]
  have hmeas : ∀ t ∈ Icc 0 T, AEMeasurable Ψ (volume.restrict (Ioc 0 t)) := fun t ht =>
    hΨm.mono_measure (Measure.restrict_mono (Ioc_subset_Ioc_right ht.2) le_rfl)
  have hreal : ∀ t ∈ Icc 0 T, ∫ s in (0 : ℝ)..t, (Ψ s).toReal = (∫⁻ s in Ioc 0 t, Ψ s).toReal := by
    intro t ht
    rw [intervalIntegral.integral_of_le ht.1]
    refine integral_toReal (hmeas t ht) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact lt_top_iff_ne_top.2 (hfin s ⟨hs.1.le, hs.2.trans ht.2⟩)
  have hii : IntervalIntegrable (fun s => (Ψ s).toReal) volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    refine Integrable.mono' (g := fun _ => M.toReal) (integrableOn_const (by simp))
      hΨm.ennreal_toReal.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_mono hM (hbd s ⟨hs.1.le, hs.2⟩)
  have hz := SDE.eq_zero_of_le_volterra (w := fun s => (Ψ s).toReal) (L := L.toReal)
    ENNReal.toReal_nonneg (fun t _ => ENNReal.toReal_nonneg) hii (fun t ht => by
      rw [hreal t ht, ← ENNReal.toReal_mul]
      exact ENNReal.toReal_mono (ENNReal.mul_ne_top hL (hint_fin t ht)) (hle t ht))
  intro t ht
  have h0 := hz t ht
  rcases (ENNReal.toReal_eq_zero_iff _).1 h0 with h | h
  · exact h
  · exact absurd h (hfin t ht)

end BlockBand.SourceProcess.Stochastic.NativeSDE
