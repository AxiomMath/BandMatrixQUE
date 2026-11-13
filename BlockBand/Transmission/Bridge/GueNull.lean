module

public import BlockBand.Transmission.Bridge.All

/-!
# `det(A + C) ≠ 0` for `A ~ GUE_W(t)`, `t > 0`, almost surely

The GUE blocks are `A ~ GUE_W(c/W)`, `c = 1 - 2b` (`CoareaPalm.gueMeasure`).

The normalization is checked, not assumed: `gueMeasure ι t` is the law of
`gueSample t X = √(t/2)(X + Xᴴ)` with `X = circularBrownianCoordinates ρ = (ρ₀ + iρ₁)/√2`, `ρ` iid
`gaussianReal 0 1` (`commonCircularIncrementLaw ι 1`), so the diagonal entry `(a,a)` is
`√(t/2)·(2/√2)·ρ_{(a,a),0}` (`gueRaw_diag_sub`, coefficient `gueDiagCoef t`, nonzero iff
`t ≠ 0`; it equals `√t`), and no other entry involves `ρ_{(a,a),0}`. For the path blocks
`t = ((1-2b)/W)₊ ≠ 0` iff `b < 1/2` and `W ≥ 1` (`gueVariance_ne_zero`).

Main result `ae_det_gue_add_ne_zero`: for every fixed `C` and `t ≠ 0`,
`∀ᵐ A ∂gueMeasure (Fin W) t, det(A + C) ≠ 0`. Proof: as in `pi_det_ginibreSample_null`, the
determinant is affine in `ρ_{(0,0),0}` with slope `gueDiagCoef t · cofactor`, and the cofactor is
again of the form `det(GUE + C')`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Bridge

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.SourceProcess
open scoped ENNReal NNReal Matrix ComplexConjugate

/-- The GUE sample in its real coordinates. -/
def gueRaw {n : ℕ} (t : ℝ≥0) (ρ : (Fin n × Fin n) × Fin 2 → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  gueSample t (circularBrownianCoordinates ρ)

/-- The coefficient of `ρ_{(a,a),0}` in the diagonal entry `(a,a)`. -/
def gueDiagCoef (t : ℝ≥0) : ℂ := (Real.sqrt ((t : ℝ) / 2) : ℂ) * 2 / (Real.sqrt 2 : ℂ)

theorem gueDiagCoef_eq_sqrt (t : ℝ≥0) : gueDiagCoef t = (Real.sqrt t : ℂ) := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs : Real.sqrt ((t : ℝ) / 2) = Real.sqrt t / Real.sqrt 2 := Real.sqrt_div' _ (by norm_num)
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hr : Real.sqrt ((t : ℝ) / 2) * 2 / Real.sqrt 2 = Real.sqrt t := by
    rw [hs]
    calc Real.sqrt t / Real.sqrt 2 * 2 / Real.sqrt 2 = Real.sqrt t * 2 / (Real.sqrt 2 * Real.sqrt 2) := by
          ring
      _ = Real.sqrt t := by rw [hsq]; ring
  rw [gueDiagCoef, ← hr]; push_cast; ring

theorem gueDiagCoef_ne_zero {t : ℝ≥0} (ht : t ≠ 0) : gueDiagCoef t ≠ 0 := by
  rw [gueDiagCoef_eq_sqrt]
  exact_mod_cast (Real.sqrt_pos.mpr (by exact_mod_cast pos_iff_ne_zero.mpr ht)).ne'

theorem gueMeasure_eq_map (n : ℕ) (t : ℝ≥0) :
    gueMeasure (Fin n) t =
      (Measure.pi fun _ : (Fin n × Fin n) × Fin 2 => gaussianReal 0 1).map (gueRaw t) := by
  rw [gueMeasure, commonCircularIncrementLaw, Measure.map_map (measurable_gueSample t)
    measurable_circularBrownianCoordinates]
  rfl

theorem measurable_gueRaw (n : ℕ) (t : ℝ≥0) : Measurable (gueRaw (n := n) t) :=
  (measurable_gueSample t).comp measurable_circularBrownianCoordinates

/-- The diagonal entry is `gueDiagCoef t · ρ_{(a,a),0}` plus terms free of `ρ_{(a,a),0}`. -/
theorem gueRaw_diag_sub {n : ℕ} (t : ℝ≥0) (ρ : (Fin n × Fin n) × Fin 2 → ℝ) (a : Fin n) :
    gueRaw t ρ a a - gueRaw t (Function.update ρ ((a, a), 0) 0) a a =
      (ρ ((a, a), 0) : ℂ) * gueDiagCoef t := by
  have h1 : (((a, a), (1 : Fin 2)) : (Fin n × Fin n) × Fin 2) ≠ ((a, a), 0) := by simp
  simp only [gueRaw, gueSample, circularBrownianCoordinates, Matrix.of_apply,
    Function.update_self, Function.update_of_ne h1, gueDiagCoef]
  simp only [map_div₀, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast; ring

/-- The cofactor coordinates `((i, j), k) ↦ ((i+1, j+1), k)`. -/
def gueMinorIndex (n : ℕ) (q : (Fin n × Fin n) × Fin 2) : (Fin (n + 1) × Fin (n + 1)) × Fin 2 :=
  ((q.1.1.succ, q.1.2.succ), q.2)

theorem gueMinorIndex_injective (n : ℕ) : Function.Injective (gueMinorIndex n) := by
  rintro ⟨⟨i, j⟩, k⟩ ⟨⟨i', j'⟩, k'⟩ h
  simp only [gueMinorIndex, Prod.mk.injEq, Fin.succ_inj] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h; rfl

/-- `det(G(ρ) + C) = ρ_{(0,0),0} · κ_t det(G(ρ∘e) + C₊₊) + det(G(ρ with ρ_{(0,0),0} = 0) + C)`. -/
theorem det_gueRaw_add_affine (n : ℕ) (t : ℝ≥0) (C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (ρ : (Fin (n + 1) × Fin (n + 1)) × Fin 2 → ℝ) :
    (gueRaw t ρ + C).det = (ρ ((0, 0), 0) : ℂ) * (gueDiagCoef t *
        (gueRaw t (fun q => ρ (gueMinorIndex n q)) + C.submatrix Fin.succ Fin.succ).det) +
      (gueRaw t (Function.update ρ ((0, 0), 0) 0) + C).det := by
  set ρ' := Function.update ρ ((0, 0), 0) 0
  have hminor : ∀ j : Fin (n + 1), (gueRaw t ρ + C).submatrix Fin.succ j.succAbove =
      (gueRaw t ρ' + C).submatrix Fin.succ j.succAbove := by
    intro j; ext i l
    simp [ρ', gueRaw, gueSample, circularBrownianCoordinates]
  have hcof : (gueRaw t ρ + C).submatrix Fin.succ Fin.succ =
      gueRaw t (fun q => ρ (gueMinorIndex n q)) + C.submatrix Fin.succ Fin.succ := by
    ext i l; rfl
  have hcof' : (gueRaw t ρ' + C).submatrix Fin.succ Fin.succ =
      gueRaw t (fun q => ρ (gueMinorIndex n q)) + C.submatrix Fin.succ Fin.succ := by
    rw [← hcof]; ext i l; simp [ρ', gueRaw, gueSample, circularBrownianCoordinates]
  have hrow : ∀ j : Fin n, (gueRaw t ρ + C) 0 j.succ = (gueRaw t ρ' + C) 0 j.succ := by
    intro j; simp [ρ', gueRaw, gueSample, circularBrownianCoordinates]
  have h00 : (gueRaw t ρ + C) 0 0 = (ρ ((0, 0), 0) : ℂ) * gueDiagCoef t + (gueRaw t ρ' + C) 0 0 := by
    simp only [Matrix.add_apply]
    rw [← gueRaw_diag_sub t ρ 0]; ring
  rw [Matrix.det_succ_row_zero, Matrix.det_succ_row_zero (gueRaw t ρ' + C), Fin.sum_univ_succ,
    Fin.sum_univ_succ]
  simp only [Fin.succAbove_zero]
  rw [hcof, hcof', h00]
  simp_rw [hrow, hminor]
  simp only [Fin.val_zero, pow_zero]
  ring

theorem measurable_det_gueRaw_add {n : ℕ} (t : ℝ≥0) (C : Matrix (Fin n) (Fin n) ℂ) :
    Measurable fun ρ : (Fin n × Fin n) × Fin 2 → ℝ => (gueRaw t ρ + C).det := by
  refine measurable_det.comp (Measurable.of_eval_matrix _ fun x y => ?_)
  simp only [Matrix.add_apply]
  exact (measurable_gueRaw n t).eval_matrix.add measurable_const

/-- **`det(GUE + C)` vanishes on a null set** of the real coordinates, for atomless `μ`. -/
theorem pi_det_gueRaw_add_null (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : ∀ x, μ {x} = 0)
    {t : ℝ≥0} (ht : t ≠ 0) :
    ∀ (n : ℕ) (C : Matrix (Fin n) (Fin n) ℂ), (Measure.pi fun _ : (Fin n × Fin n) × Fin 2 => μ)
      {ρ | (gueRaw t ρ + C).det = 0} = 0
  | 0, C => by simp [Matrix.det_fin_zero]
  | n + 1, C => by
    set c : ((Fin (n + 1) × Fin (n + 1)) × Fin 2 → ℝ) → ℂ := fun ρ => gueDiagCoef t *
      (gueRaw t (fun q => ρ (gueMinorIndex n q)) + C.submatrix Fin.succ Fin.succ).det
    set g : ((Fin (n + 1) × Fin (n + 1)) × Fin 2 → ℝ) → ℂ :=
      fun ρ => (gueRaw t (Function.update ρ ((0, 0), 0) 0) + C).det
    have hR : Measurable fun (ρ : (Fin (n + 1) × Fin (n + 1)) × Fin 2 → ℝ) q =>
        ρ (gueMinorIndex n q) := Measurable.of_eval fun _ => measurable_pi_apply _
    have hc : Measurable c :=
      measurable_const.mul ((measurable_det_gueRaw_add t _).comp hR)
    have hU : Measurable fun ρ : (Fin (n + 1) × Fin (n + 1)) × Fin 2 → ℝ =>
        Function.update ρ ((0, 0), 0) 0 :=
      (measurable_update_coord _).comp (measurable_id.prodMk measurable_const)
    have hg : Measurable g := (measurable_det_gueRaw_add t C).comp hU
    have hsub : {ρ | (gueRaw t ρ + C).det = 0} ⊆
        {ρ | (gueRaw t (fun q => ρ (gueMinorIndex n q)) + C.submatrix Fin.succ Fin.succ).det = 0} ∪
          {ρ | c ρ ≠ 0 ∧ (ρ ((0, 0), 0) : ℂ) * c ρ + g ρ = 0} := by
      intro ρ hρ
      by_cases h : (gueRaw t (fun q => ρ (gueMinorIndex n q)) +
          C.submatrix Fin.succ Fin.succ).det = 0
      · exact Or.inl h
      · exact Or.inr ⟨mul_ne_zero (gueDiagCoef_ne_zero ht) h,
          by rw [← det_gueRaw_add_affine]; exact hρ⟩
    refine measure_mono_null hsub (measure_union_null ?_ ?_)
    · have hmap := infinitePi_map_reindex μ (gueMinorIndex n) (gueMinorIndex_injective n)
      rw [Measure.infinitePi_eq_pi] at hmap
      have hmeas : MeasurableSet {ρ : (Fin n × Fin n) × Fin 2 → ℝ |
          (gueRaw t ρ + C.submatrix Fin.succ Fin.succ).det = 0} :=
        (measurableSet_singleton 0).preimage (measurable_det_gueRaw_add t _)
      have := pi_det_gueRaw_add_null μ hμ ht n (C.submatrix Fin.succ Fin.succ)
      rw [← hmap, Measure.map_apply hR hmeas] at this
      exact this
    · refine null_affine_coord μ hμ ((0, 0), 0) c g hc hg (fun ρ s => ?_) (fun ρ s => ?_)
      · simp only [c]
        congr 4
      · simp only [g, Function.update_idem]

/-- **A GUE block plus any fixed matrix is a.s. invertible** (`t ≠ 0`). -/
theorem ae_det_gue_add_ne_zero (W : ℕ) {t : ℝ≥0} (ht : t ≠ 0) (C : Matrix (Fin W) (Fin W) ℂ) :
    ∀ᵐ A ∂gueMeasure (Fin W) t, (A + C).det ≠ 0 := by
  have hset : MeasurableSet {A : Matrix (Fin W) (Fin W) ℂ | (A + C).det ≠ 0} := by
    refine (measurableSet_singleton 0).compl.preimage (measurable_det.comp ?_)
    exact Measurable.of_eval_matrix _ fun x y => Matrix.measurable_apply.add measurable_const
  rw [gueMeasure_eq_map, ae_map_iff (measurable_gueRaw W t).aemeasurable hset, ae_iff]
  simpa using pi_det_gueRaw_add_null (gaussianReal 0 1)
    (gaussianReal_singleton one_ne_zero) ht W C

/-- The block variance `t = ((1-2b)/W)₊` of the laws `layerLaw`, `pathLaw`, `growthPathLaw` is
nonzero for `b < 1/2`, `W ≥ 1` (it is `0` for `b ≥ 1/2`). -/
theorem gueVariance_ne_zero {W : ℕ} {b : ℝ} (hb : b < 1 / 2) (hW : 1 ≤ W) :
    Real.toNNReal ((1 - 2 * b) / W) ≠ 0 := by
  rw [Ne, Real.toNNReal_eq_zero, not_le]
  exact div_pos (by linarith) (by exact_mod_cast hW)

end BlockBand.Transmission.Bridge
