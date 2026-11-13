module

public import BlockBand.DeterminantScore.SpectralConvexity
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# The Vandermonde integral over an interlacing box

A component of the radial half of the Weyl integration formula
(`WeylEigenLawStatement`).

For `λ : Fin (n+1) → ℝ` monotone, the interlacing box is
`B(λ) = ∏_i (λ_i, λ_{i+1}) ⊂ ℝ^n` and

`∫_{B(λ)} Δ(μ) dμ = Δ(λ) / n!`   (`lintegral_interlaceBox_vandermonde`),

with Lebesgue measure on `Fin n → ℝ` and `Δ = SpectralConvexity.vandermonde`. Proof: expand
`Δ(μ) = det[μ_i^j]` over permutations, integrate each product factorwise, and identify the
resulting determinant `det[(λ_{i+1}^{j+1} - λ_i^{j+1})/(j+1)]` with `Δ(λ)/n!` by subtracting
consecutive rows of the `(n+1) × (n+1)` Vandermonde matrix (`det_diffVandermonde`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.WeylIntegration

open MeasureTheory Matrix
open scoped ENNReal

variable {n : ℕ}

theorem vandermonde_eq_det {m : ℕ} (v : Fin m → ℝ) :
    SpectralConvexity.vandermonde v = (Matrix.vandermonde v).det := by
  rw [Matrix.det_vandermonde]
  unfold SpectralConvexity.vandermonde
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_filter]
  congr 1
  ext j
  simp

theorem vandermonde_nonneg_of_monotone {m : ℕ} {v : Fin m → ℝ} (hv : Monotone v) :
    0 ≤ SpectralConvexity.vandermonde v :=
  Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => by
    split_ifs with hij
    · exact sub_nonneg.2 (hv hij.le)
    · exact zero_le_one

theorem continuous_vandermonde {m : ℕ} :
    Continuous fun v : Fin m → ℝ => SpectralConvexity.vandermonde v := by
  unfold SpectralConvexity.vandermonde
  refine continuous_finsetProd _ fun i _ => continuous_finsetProd _ fun j _ => ?_
  split_ifs
  · exact (continuous_apply j).sub (continuous_apply i)
  · exact continuous_const

/-!
## Consecutive differences of a Vandermonde matrix
-/

/-- `B_{ij} = λ_{i+1}^{j+1} - λ_i^{j+1}` (`i, j < n`). -/
def diffVandermonde (lam : Fin (n + 1) → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => lam i.succ ^ ((j : ℕ) + 1) - lam i.castSucc ^ ((j : ℕ) + 1)

/-- The down-shift matrix `S_{k,l} = 1{k = l + 1}`. -/
def shiftDown (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun k l => if (k : ℕ) = (l : ℕ) + 1 then 1 else 0

theorem shiftDown_mul_zero (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (j : Fin (n + 1)) :
    (shiftDown n * A) 0 j = 0 := by
  simp [shiftDown, Matrix.mul_apply]

theorem shiftDown_mul_succ (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin n)
    (j : Fin (n + 1)) : (shiftDown n * A) i.succ j = A i.castSucc j := by
  simp only [shiftDown, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.sum_eq_single i.castSucc]
  · simp
  · intro l _ hl
    have hne : ¬ ((i : ℕ) = (l : ℕ)) := by
      intro h
      apply hl
      ext
      simp only [Fin.val_castSucc]
      omega
    simp [hne]
  · simp

theorem det_one_sub_shiftDown : (1 - shiftDown n).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    simp [shiftDown]
  · intro i j hij
    have hij' : i < j := hij
    have hne : i ≠ j := hij'.ne
    have hne' : ¬ ((i : ℕ) = (j : ℕ) + 1) := by
      have := Fin.lt_def.1 hij'
      omega
    simp [Matrix.one_apply_ne hne, shiftDown, hne']

/-- `det B = Δ(λ)` for the `(n+1)`-point Vandermonde: subtract consecutive rows and expand along
the first column. -/
theorem det_diffVandermonde (lam : Fin (n + 1) → ℝ) :
    (diffVandermonde lam).det = (Matrix.vandermonde lam).det := by
  set V := Matrix.vandermonde lam
  have h1 : ((1 - shiftDown n) * V).det = V.det := by
    rw [Matrix.det_mul, det_one_sub_shiftDown, one_mul]
  rw [← h1, Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have hz : ∀ i : Fin n, ((1 - shiftDown n) * V) i.succ 0 = 0 := by
    intro i
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, shiftDown_mul_succ]
    simp [V, Matrix.vandermonde]
  simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  have h0 : ((1 - shiftDown n) * V) 0 0 = 1 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, shiftDown_mul_zero]
    simp [V, Matrix.vandermonde]
  rw [h0, Fin.succAbove_zero]
  simp only [Fin.val_zero, pow_zero, one_mul]
  congr 1
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply,
    shiftDown_mul_succ, diffVandermonde, Matrix.of_apply, V, Matrix.vandermonde, Fin.val_succ]

/-- The permutation expansion along rows: `det A = Σ_σ ε(σ) ∏_i A_{i,σ(i)}`. -/
theorem det_eq_sum_rows {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) :
    A.det = ∑ σ : Equiv.Perm (Fin k), (Equiv.Perm.sign σ : ℝ) * ∏ i, A i (σ i) := by
  rw [← Matrix.det_transpose, Matrix.det_apply']
  rfl

/-!
## The interlacing box
-/

/-- The interlacing box `∏_i (λ_i, λ_{i+1})`. -/
def interlaceBox (lam : Fin (n + 1) → ℝ) : Set (Fin n → ℝ) :=
  Set.univ.pi fun i => Set.Ioo (lam i.castSucc) (lam i.succ)

theorem measurableSet_interlaceBox (lam : Fin (n + 1) → ℝ) : MeasurableSet (interlaceBox lam) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioo

theorem strictMono_of_mem_interlaceBox {lam : Fin (n + 1) → ℝ} (hlam : Monotone lam)
    {μ : Fin n → ℝ} (hμ : μ ∈ interlaceBox lam) : StrictMono μ := by
  intro i j hij
  have hi := (hμ i (Set.mem_univ _)).2
  have hj := (hμ j (Set.mem_univ _)).1
  have hle : lam i.succ ≤ lam j.castSucc := hlam (by
    rw [Fin.le_def]
    simp only [Fin.val_succ, Fin.val_castSucc]
    exact Fin.lt_def.1 hij)
  linarith

theorem integral_Ioo_pow {a b : ℝ} (hab : a ≤ b) (k : ℕ) :
    ∫ t in Set.Ioo a b, t ^ k = (b ^ (k + 1) - a ^ (k + 1)) / ((k : ℝ) + 1) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab, integral_pow]

theorem factorial_eq_prod_fin (n : ℕ) : (n.factorial : ℝ) = ∏ j : Fin n, ((j : ℝ) + 1) := by
  rw [Fin.prod_univ_eq_prod_range (fun j : ℕ => (j : ℝ) + 1) n,
    ← Finset.prod_range_add_one_eq_factorial]
  push_cast
  rfl

/-- `∫_{B(λ)} det[μ_i^j] dμ = det B(λ) / n!`. -/
theorem integral_interlaceBox_det (lam : Fin (n + 1) → ℝ) (hlam : Monotone lam) :
    ∫ μ in interlaceBox lam, (Matrix.vandermonde μ).det =
      (diffVandermonde lam).det / n.factorial := by
  have hab : ∀ i : Fin n, lam i.castSucc ≤ lam i.succ := fun i =>
    hlam (Fin.castSucc_le_succ i)
  have hint : ∀ (i : Fin n) (k : ℕ),
      Integrable (fun t : ℝ => t ^ k) (volume.restrict (Set.Ioo (lam i.castSucc) (lam i.succ))) :=
    fun i k => ((continuous_pow k).integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
  simp_rw [det_eq_sum_rows (Matrix.vandermonde _), Matrix.vandermonde_apply]
  unfold interlaceBox
  rw [volume_pi, Measure.restrict_pi_pi, integral_finsetSum]
  · simp_rw [integral_const_mul]
    rw [div_eq_mul_inv, det_eq_sum_rows, Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [integral_fintype_prod_eq_prod (fun i (t : ℝ) => t ^ ((σ i : ℕ))), mul_assoc]
    congr 1
    simp_rw [integral_Ioo_pow (hab _)]
    rw [factorial_eq_prod_fin, ← Finset.prod_inv_distrib,
      ← Equiv.prod_comp σ (fun j : Fin n => ((j : ℝ) + 1)⁻¹), ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [diffVandermonde, Matrix.of_apply]
    rw [div_eq_mul_inv]
  · intro σ _
    exact (Integrable.fintype_prod (f := fun i (t : ℝ) => t ^ ((σ i : ℕ)))
      fun i => hint i _).const_mul _

/-- **Interlacing Vandermonde integral.** For monotone `λ : Fin (n+1) → ℝ`,
`∫_{∏(λ_i, λ_{i+1})} Δ(μ) dμ = Δ(λ)/n!` (Lebesgue measure on `ℝ^n`). -/
theorem lintegral_interlaceBox_vandermonde (lam : Fin (n + 1) → ℝ) (hlam : Monotone lam) :
    ∫⁻ μ in interlaceBox lam, ENNReal.ofReal (SpectralConvexity.vandermonde μ) =
      ENNReal.ofReal (SpectralConvexity.vandermonde lam / n.factorial) := by
  have hK : IsCompact (Set.univ.pi fun i : Fin n => Set.Icc (lam i.castSucc) (lam i.succ)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hsub : interlaceBox lam ⊆ Set.univ.pi fun i : Fin n => Set.Icc (lam i.castSucc) (lam i.succ) :=
    Set.pi_mono fun _ _ => Set.Ioo_subset_Icc_self
  have hI : IntegrableOn (fun μ => SpectralConvexity.vandermonde μ) (interlaceBox lam) :=
    (continuous_vandermonde.continuousOn.integrableOn_compact hK).mono_set hsub
  rw [← ofReal_integral_eq_lintegral_ofReal hI
    (ae_restrict_of_forall_mem (measurableSet_interlaceBox lam) fun μ hμ =>
      vandermonde_nonneg_of_monotone (strictMono_of_mem_interlaceBox hlam hμ).monotone)]
  congr 1
  simp_rw [vandermonde_eq_det]
  rw [integral_interlaceBox_det lam hlam, det_diffVandermonde]

end BlockBand.DeterminantScore.WeylIntegration
