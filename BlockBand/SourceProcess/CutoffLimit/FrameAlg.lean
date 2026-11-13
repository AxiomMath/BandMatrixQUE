module

public import BlockBand.Internal.Contracts.TransmissionLaws

/-!
# Frame algebra for the cutoff comparison

* `probeBlock_posSemidef`: the probe block of `VᴴV` is `V_prᴴV_pr ⪰ 0`;
* `norm_sourceGram_le_hsSq`, `norm_sourceGram_sub_le`: `|A_ij| ≤ ‖V‖²_HS` and
  `|A₁ij − A₂ij| ≤ ‖V₁ − V₂‖_HS (‖V₁‖_HS + ‖V₂‖_HS)` (Cauchy–Schwarz; no dependence on `ι`);
* `hsSq_isometry_mul`: `‖E F‖²_HS = ‖F‖²_HS` for an isometry `EᴴE = 1`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.CutoffLimit

open Matrix
open BlockBand.SourceProcess BlockBand.Internal.Contracts.TransmissionLaws
open scoped ComplexConjugate ComplexOrder

variable {ι c : Type*} [Fintype ι] [Fintype c]

/-- Squared norm of a column. -/
def colSq (V : Matrix ι c ℂ) (j : c) : ℝ := ∑ x, ‖V x j‖ ^ 2

omit [Fintype c] in
theorem colSq_nonneg (V : Matrix ι c ℂ) (j : c) : 0 ≤ colSq V j :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem colSq_le_hsSq (V : Matrix ι c ℂ) (j : c) : colSq V j ≤ hsSq V :=
  Finset.sum_le_sum fun x _ =>
    Finset.single_le_sum (f := fun j => ‖V x j‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)

theorem hsSq_nonneg (V : Matrix ι c ℂ) : 0 ≤ hsSq V :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [Fintype c] in
theorem sourceGram_apply (V : Matrix ι c ℂ) (i j : c) :
    sourceGram V i j = ∑ x, conj (V x i) * V x j := by
  simp [sourceGram, mul_apply]

/-- Cauchy–Schwarz for complex finite sums. -/
theorem norm_sum_conj_mul_le (u v : ι → ℂ) :
    ‖∑ x, conj (u x) * v x‖ ≤ Real.sqrt (∑ x, ‖u x‖ ^ 2) * Real.sqrt (∑ x, ‖v x‖ ^ 2) := by
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_mul, Complex.norm_conj]
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

omit [Fintype c] in
theorem norm_sourceGram_le (V : Matrix ι c ℂ) (i j : c) :
    ‖sourceGram V i j‖ ≤ Real.sqrt (colSq V i) * Real.sqrt (colSq V j) := by
  rw [sourceGram_apply]
  exact norm_sum_conj_mul_le _ _

theorem norm_sourceGram_le_hsSq (V : Matrix ι c ℂ) (i j : c) : ‖sourceGram V i j‖ ≤ hsSq V := by
  refine (norm_sourceGram_le V i j).trans ?_
  have h := Real.sqrt_le_sqrt (colSq_le_hsSq V i)
  have h' := Real.sqrt_le_sqrt (colSq_le_hsSq V j)
  calc Real.sqrt (colSq V i) * Real.sqrt (colSq V j) ≤ Real.sqrt (hsSq V) * Real.sqrt (hsSq V) :=
        mul_le_mul h h' (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = hsSq V := Real.mul_self_sqrt (hsSq_nonneg V)

theorem norm_sourceGram_sub_le (V₁ V₂ : Matrix ι c ℂ) (i j : c) :
    ‖sourceGram V₁ i j - sourceGram V₂ i j‖ ≤
      Real.sqrt (hsSq (V₁ - V₂)) * (Real.sqrt (hsSq V₁) + Real.sqrt (hsSq V₂)) := by
  have hsplit : sourceGram V₁ i j - sourceGram V₂ i j =
      (∑ x, conj ((V₁ - V₂) x i) * V₁ x j) + ∑ x, conj (V₂ x i) * (V₁ - V₂) x j := by
    rw [sourceGram_apply, sourceGram_apply, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Matrix.sub_apply, map_sub]
    ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have hA := norm_sum_conj_mul_le (fun x => (V₁ - V₂) x i) (fun x => V₁ x j)
  have hB := norm_sum_conj_mul_le (fun x => V₂ x i) (fun x => (V₁ - V₂) x j)
  have s1 := Real.sqrt_le_sqrt (colSq_le_hsSq (V₁ - V₂) i)
  have s2 := Real.sqrt_le_sqrt (colSq_le_hsSq V₁ j)
  have s3 := Real.sqrt_le_sqrt (colSq_le_hsSq V₂ i)
  have s4 := Real.sqrt_le_sqrt (colSq_le_hsSq (V₁ - V₂) j)
  simp only [colSq] at s1 s2 s3 s4
  have e1 := mul_le_mul s1 s2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have e2 := mul_le_mul s3 s4 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  nlinarith

/-- The probe block of `VᴴV` is positive semidefinite. -/
theorem probeBlock_posSemidef {K : ℕ} {π : Type*} [Fintype π]
    (V : Matrix ι (SrcCol K π) ℂ) : (probeBlock (sourceGram V)).PosSemidef := by
  have h : probeBlock (sourceGram V) = (V.submatrix id Sum.inr)ᴴ * V.submatrix id Sum.inr := by
    ext i j
    simp [probeBlock, sourceGram, mul_apply]
  rw [h]
  exact posSemidef_conjTranspose_mul_self _

theorem hsSq_eq_re_trace (V : Matrix ι c ℂ) : hsSq V = (Vᴴ * V).trace.re := by
  rw [hsSq, trace, Complex.re_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [diag_apply, mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [conjTranspose_apply, Complex.star_def, Complex.conj_mul']
  norm_cast

/-- An isometry preserves the Hilbert–Schmidt norm. -/
theorem hsSq_isometry_mul {κ : Type*} [Fintype κ] [DecidableEq κ] {E : Matrix ι κ ℂ} (hE : Eᴴ * E = 1)
    (F : Matrix κ c ℂ) : hsSq (E * F) = hsSq F := by
  rw [hsSq_eq_re_trace, hsSq_eq_re_trace, conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc Eᴴ, hE, Matrix.one_mul]

end BlockBand.SourceProcess.CutoffLimit
