module

public import BlockBand.SourceProcess.PhysApprox.IdentK.FiniteWJet

/-!
# Abstract conditional-expectation and summation lemmas

Measure: a finite (probability) measure `μ` on `Ω`; a sub-σ-algebra `m ≤ m0`.

* `integral_mul_condExp_eq`: `∫ g Y = ∫ g E[Y | m]` for a bounded `m`-measurable complex `g`;
* **`enorm_integral_sub_le_cond`**: for an `m`-event `A`,
  `‖∫ g 1_A X − ∫ g 1_A P‖ₑ ≤ C_g ∫⁻ ‖1_A (E[1_A X | m] − P)‖ₑ` (the per-term error);
* `condExp_conj`: `E[conj f | m] = conj E[f | m]` a.e.;
* **`norm_sum_stopped_le`**: for a decreasing predicate `p`, the stopped sum
  `Σ_{n ≤ j < n'} 1_{p j}(a_{j+1} − a_j − c_j)` is at most `2 sup‖a‖ + Σ ‖c_j‖`;
* `cube_le`: `x³ ≤ η x² + x⁴/η` for `x ≥ 0`, `η > 0`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK.FW

open MeasureTheory Finset Filter

section Cond

variable {Ω : Type*} {m m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Pull-out for a bounded measurable complex factor**, integrated. -/
theorem integral_mul_condExp_eq [IsFiniteMeasure μ] (hm : m ≤ m0) {g Y : Ω → ℂ}
    (hg : StronglyMeasurable[m] g) {Cg : ℝ} (hgb : ∀ ω, ‖g ω‖ ≤ Cg) (hY : Integrable Y μ) :
    ∫ ω, g ω * Y ω ∂μ = ∫ ω, g ω * μ[Y | m] ω ∂μ := by
  have hgY : Integrable (fun ω => g ω * Y ω) μ :=
    hY.bdd_mul (hg.mono hm).aestronglyMeasurable (Eventually.of_forall hgb)
  have h := condExp_bilin_of_aestronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℂ)
    (m := m) (μ := μ) hg.aestronglyMeasurable (by simpa using hgY) hY
  simp only [ContinuousLinearMap.mul_apply'] at h
  rw [← integral_condExp hm (f := fun ω => g ω * Y ω)]
  exact integral_congr_ae h

/-- **The per-term error**: replacing `X` by `P` on an `m`-event, tested against a bounded
`m`-measurable factor, costs at most the summed conditional error. -/
theorem enorm_integral_sub_le_cond [IsFiniteMeasure μ] (hm : m ≤ m0) {A : Set Ω}
    (hA : MeasurableSet[m] A) {X P g : Ω → ℂ} (hX : Integrable (A.indicator X) μ)
    (hP : Integrable (A.indicator P) μ) (hg : StronglyMeasurable[m] g) {Cg : ℝ}
    (hgb : ∀ ω, ‖g ω‖ ≤ Cg) :
    ‖∫ ω, g ω * A.indicator X ω ∂μ - ∫ ω, g ω * A.indicator P ω ∂μ‖ₑ ≤
      ENNReal.ofReal Cg * ∫⁻ ω, ‖A.indicator (fun ω => μ[A.indicator X | m] ω - P ω) ω‖ₑ ∂μ := by
  have hgm : AEStronglyMeasurable g μ := (hg.mono hm).aestronglyMeasurable
  rw [integral_mul_condExp_eq hm hg hgb hX]
  have hind : μ[A.indicator X | m] =ᵐ[μ] A.indicator (μ[A.indicator X | m]) := by
    have h := condExp_indicator (m := m) (μ := μ) hX hA
    rwa [Set.indicator_indicator, Set.inter_self] at h
  have i1 : Integrable (fun ω => g ω * μ[A.indicator X | m] ω) μ :=
    integrable_condExp.bdd_mul hgm (Eventually.of_forall hgb)
  have i2 : Integrable (fun ω => g ω * A.indicator P ω) μ :=
    hP.bdd_mul hgm (Eventually.of_forall hgb)
  rw [← integral_sub i1 i2]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae (hind.mono fun ω hω => ?_)
  rw [hω, ← mul_sub, enorm_mul]
  have h1 : ‖g ω‖ₑ ≤ ENNReal.ofReal Cg := by
    rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hgb ω)
  have h2 : A.indicator (μ[A.indicator X | m]) ω - A.indicator P ω =
      A.indicator (fun ω => μ[A.indicator X | m] ω - P ω) ω := by
    by_cases h : ω ∈ A
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  rw [h2]
  exact mul_le_mul_left h1 _

/-- `E[conj f | m] = conj E[f | m]` a.e. -/
theorem condExp_conj {f : Ω → ℂ} :
    μ[fun ω => (starRingEnd ℂ) (f ω) | m] =ᵐ[μ] fun ω => (starRingEnd ℂ) (μ[f | m] ω) := by
  by_cases hf : Integrable f μ
  · exact ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp_condExp_comm hf).symm
  · have hf' : ¬ Integrable (fun ω => (starRingEnd ℂ) (f ω)) μ := fun h => hf (by
      have := (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp h
      simpa [Function.comp_def] using this)
    rw [condExp_of_not_integrable hf, condExp_of_not_integrable hf']
    exact Filter.Eventually.of_forall fun ω => by simp

end Cond

/-!
## The stopped telescoping sum
-/

theorem sum_Ico_tele (a : ℕ → ℂ) {n M : ℕ} (h : n ≤ M) :
    ∑ j ∈ Ico n M, (a (j + 1) - a j) = a M - a n := by
  rw [sum_Ico_eq_sum_range]
  have := sum_range_sub (fun k => a (n + k)) (M - n)
  simp only [add_zero, Nat.add_sub_cancel' h, ← Nat.add_assoc] at this
  exact this

/-- The stopped telescoping sum is a difference of two values. -/
theorem exists_sum_stopped_eq (a : ℕ → ℂ) {p : ℕ → Prop} [DecidablePred p]
    (hp : ∀ j, p (j + 1) → p j) (n M : ℕ) :
    ∃ k, ∑ j ∈ Ico n M, (if p j then a (j + 1) - a j else 0) = a k - a n := by
  induction M with
  | zero => exact ⟨n, by simp⟩
  | succ M ih =>
    by_cases hnM : n ≤ M
    · rw [sum_Ico_succ_top hnM]
      by_cases hpM : p M
      · refine ⟨M + 1, ?_⟩
        have hdown : ∀ d j, p (j + d) → p j := fun d => by
          induction d with
          | zero => exact fun j h => h
          | succ d ihd => exact fun j h => ihd j (hp _ (by simpa [Nat.add_assoc] using h))
        have hall : ∀ j ∈ Ico n (M + 1), p j := fun j hj => by
          have hjM : j ≤ M := Nat.lt_succ_iff.1 (mem_Ico.1 hj).2
          obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hjM
          exact hdown d j (hd ▸ hpM)
        rw [← sum_Ico_succ_top hnM (fun j => if p j then a (j + 1) - a j else 0),
          sum_congr rfl fun j hj => ite_eq_left_of_eq_true _ _ (eq_true (hall j hj))]
        exact sum_Ico_tele a (by omega)
      · obtain ⟨k, hk⟩ := ih
        exact ⟨k, by rw [hk, ite_eq_right_of_eq_false _ _ (eq_false hpM), add_zero]⟩
    · exact ⟨n, by rw [Ico_eq_empty (by omega)]; simp⟩

/-- **The stopped telescoping sum is bounded** by `2 sup‖a‖ + Σ‖c_j‖`. -/
theorem norm_sum_stopped_le (a c : ℕ → ℂ) {p : ℕ → Prop} [DecidablePred p]
    (hp : ∀ j, p (j + 1) → p j) {Ca : ℝ} (ha : ∀ j, ‖a j‖ ≤ Ca) (n M : ℕ) :
    ‖∑ j ∈ Ico n M, (if p j then a (j + 1) - a j - c j else 0)‖ ≤
      2 * Ca + ∑ j ∈ Ico n M, ‖c j‖ := by
  obtain ⟨k, hk⟩ := exists_sum_stopped_eq a hp n M
  have e : ∑ j ∈ Ico n M, (if p j then a (j + 1) - a j - c j else 0) =
      ∑ j ∈ Ico n M, (if p j then a (j + 1) - a j else 0) -
        ∑ j ∈ Ico n M, (if p j then c j else 0) := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun j _ => by split_ifs <;> simp
  rw [e, hk]
  have h1 : ‖∑ j ∈ Ico n M, (if p j then c j else 0)‖ ≤ ∑ j ∈ Ico n M, ‖c j‖ :=
    (norm_sum_le _ _).trans (sum_le_sum fun j _ => by split_ifs <;> simp)
  calc ‖a k - a n - ∑ j ∈ Ico n M, (if p j then c j else 0)‖
      ≤ ‖a k‖ + ‖a n‖ + ‖∑ j ∈ Ico n M, (if p j then c j else 0)‖ := by
        refine (norm_sub_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
    _ ≤ 2 * Ca + ∑ j ∈ Ico n M, ‖c j‖ := by linarith [ha k, ha n]

/-- `x³ ≤ η x² + x⁴ / η`. -/
theorem cube_le {x η : ℝ} (hx : 0 ≤ x) (hη : 0 < η) : x ^ 3 ≤ η * x ^ 2 + x ^ 4 / η := by
  rw [← sub_nonneg]
  have e : η * x ^ 2 + x ^ 4 / η - x ^ 3 = x ^ 2 * (η - x) ^ 2 / η + x ^ 3 := by
    field_simp; ring
  rw [e]
  positivity

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK.FW
