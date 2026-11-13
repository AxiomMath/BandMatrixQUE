module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-!
# Normalized first nonzero vector of a finite family

`firstNZ` returns the normalization of the first nonzero member of a finite family of vectors
(zero if all vanish); it is measurable and, when some member is nonzero, a unit multiple of a
member.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.EigenSelConstruct
open Matrix MeasureTheory

variable {ι : Type*} [Fintype ι]

/-- The squared Euclidean norm `∑ₓ |q x|²`. -/
def nrm (q : ι → ℂ) : ℝ := ∑ x, ‖q x‖ ^ 2

/-- The normalization `q / ‖q‖`. -/
def unitize (q : ι → ℂ) : ι → ℂ := (((Real.sqrt (nrm q))⁻¹ : ℝ) : ℂ) • q

/-- The normalized first nonzero vector of a finite family (zero if all vanish). -/
def firstNZ : (m : ℕ) → (Fin m → ι → ℂ) → ι → ℂ
  | 0, _ => 0
  | m + 1, Q => if 0 < nrm (Q 0) then unitize (Q 0) else firstNZ m (Fin.tail Q)

theorem nrm_nonneg (q : ι → ℂ) : 0 ≤ nrm q :=
  Finset.sum_nonneg fun x _ => by positivity

theorem nrm_eq_zero_iff (q : ι → ℂ) : nrm q = 0 ↔ q = 0 := by
  unfold nrm
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun x _ => by positivity)]
  constructor
  · intro h; funext x; simpa using h x (Finset.mem_univ x)
  · intro h x _; simp [h]

theorem nrm_pos_iff (q : ι → ℂ) : 0 < nrm q ↔ q ≠ 0 := by
  rw [lt_iff_le_and_ne, and_iff_right (nrm_nonneg q), ne_comm, Ne, nrm_eq_zero_iff]

theorem star_dotProduct_self_eq_nrm (q : ι → ℂ) : star q ⬝ᵥ q = ((nrm q : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, nrm, Complex.ofReal_sum, Complex.ofReal_pow]
  refine Finset.sum_congr rfl fun x _ => ?_
  exact Complex.conj_mul' (q x)

theorem unitize_unit {q : ι → ℂ} (hq : q ≠ 0) : star (unitize q) ⬝ᵥ unitize q = 1 := by
  have hpos := (nrm_pos_iff q).2 hq
  unfold unitize
  rw [star_smul, smul_dotProduct, dotProduct_smul, star_dotProduct_self_eq_nrm]
  simp only [Complex.star_def, Complex.conj_ofReal, smul_eq_mul]
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← mul_inv,
    Real.mul_self_sqrt hpos.le, inv_mul_cancel₀ hpos.ne', Complex.ofReal_one]

theorem measurable_nrm : Measurable (nrm : (ι → ℂ) → ℝ) :=
  Finset.measurable_sum _ fun x _ => (Measurable.norm (measurable_pi_apply (X := fun _ : ι => ℂ) x)).pow_const 2

theorem measurable_unitize : Measurable (unitize : (ι → ℂ) → ι → ℂ) := by
  refine Measurable.of_eval fun x => ?_
  simp only [unitize, Pi.smul_apply, smul_eq_mul]
  exact (Complex.measurable_ofReal.comp measurable_nrm.sqrt.inv).mul (measurable_pi_apply x)

theorem measurable_firstNZ : (m : ℕ) → Measurable (firstNZ (ι := ι) m)
  | 0 => measurable_const
  | m + 1 => by
    have h0 : Measurable fun Q : Fin (m + 1) → ι → ℂ => Q 0 := measurable_pi_apply 0
    have ht : Measurable fun Q : Fin (m + 1) → ι → ℂ => Fin.tail Q :=
      Measurable.of_eval fun i => measurable_pi_apply _
    exact Measurable.ite (measurableSet_lt measurable_const (measurable_nrm.comp h0))
      (measurable_unitize.comp h0) ((measurable_firstNZ m).comp ht)

/-- If some member is nonzero, `firstNZ` returns a unit multiple of some member. -/
theorem firstNZ_spec : (m : ℕ) → (Q : Fin m → ι → ℂ) → (∃ i, Q i ≠ 0) →
    (∃ (i : Fin m) (c : ℂ), firstNZ m Q = c • Q i) ∧ star (firstNZ m Q) ⬝ᵥ firstNZ m Q = 1
  | 0, _, ⟨i, _⟩ => i.elim0
  | m + 1, Q, ⟨i, hi⟩ => by
    by_cases h : 0 < nrm (Q 0)
    · simp only [firstNZ, h, ↓reduceIte]
      exact ⟨⟨0, _, rfl⟩, unitize_unit ((nrm_pos_iff _).1 h)⟩
    · simp only [firstNZ, h, ↓reduceIte]
      have hQ0 : Q 0 = 0 := by
        by_contra hne; exact h ((nrm_pos_iff _).2 hne)
      have hi0 : i ≠ 0 := fun e => hi (e ▸ hQ0)
      obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.2 hi0
      obtain ⟨⟨j, c, hj⟩, hu⟩ := firstNZ_spec m (Fin.tail Q) ⟨i', hi⟩
      exact ⟨⟨j.succ, c, hj⟩, hu⟩

end BlockBand.SourceProcess.EigenSelConstruct
