module

public import BlockBand.SourceProcess.ProjSeparator.Split

/-!
# `L²` size of the centered quadratic form `x*(DQ(DQ)*)y`

Abstract probability space `μ`, random `D` with integrable entries, `D⁰ = D - ED`, and bilinear
moment bounds `‖x*D⁰y‖_{L²} ≤ c₂‖x‖‖y‖`, `‖x*D⁰y‖_{L⁴} ≤ c₄‖x‖‖y‖`. In the paper one diagonalizes
`A` and applies the bilinear `W^{-1/2}` estimate to its two centered factors; here the columns of
`Q` replace the eigenvectors of `A = QQ*`, with `Σ_j ‖q_j‖² = Tr A`.

* `eLpNorm_quadPart_le`: `‖Σ_j (x*D⁰q_j)conj(y*D⁰q_j)‖_{L²} ≤ c₄² ‖x‖‖y‖ frob Q` (Hölder `(4,4,2)`);
* `eLpNorm_gamma_centered`: `‖x*(DQ(DQ)*)y - E[·]‖_{L²} ≤ c₂‖x‖‖w_y‖ + c₂‖y‖‖w_x‖ + 2c₄²‖x‖‖y‖ frob Q`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ProjSeparator

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.SourceProcess.FullSourceCovariance BlockBand.Transmission.PassiveCovariance
open scoped ENNReal ComplexOrder

variable {W : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem holderTriple_442 : ENNReal.HolderTriple (4 : ℝ≥0∞) 4 2 := by
  rw [ENNReal.holderTriple_iff, ← ENNReal.toReal_eq_toReal_iff' (by simp) (by simp),
    ENNReal.toReal_add (by simp) (by simp)]
  simp; norm_num

/-- Hölder `‖f·conj g‖₂ ≤ ‖f‖₄‖g‖₄` for complex `f, g`. -/
theorem eLpNorm_mul_star_le {f g : Ω → ℂ} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) :
    eLpNorm (fun ω => f ω * star (g ω)) 2 μ ≤ eLpNorm f 4 μ * eLpNorm g 4 μ := by
  have := holderTriple_442
  have h := eLpNorm_smul_le_mul_eLpNorm (p := 4) (q := 4) (r := 2) hf hg.star
  rw [eLpNorm_star] at h
  exact h

/-- **`L²` bound of the quadratic part.** -/
theorem eLpNorm_quadPart_le (D : Ω → Matrix (Fin W) (Fin W) ℂ) (Q : Matrix (Fin W) (Fin W) ℂ)
    {c₄ : ℝ} (hc₄ : 0 ≤ c₄)
    (h4 : ∀ x y, eLpNorm (fun ω => bilinear x (D ω - matrixExpect μ D) y) 4 μ ≤
      ENNReal.ofReal (c₄ * vecNorm x * vecNorm y)) (x y : Fin W → ℂ) :
    eLpNorm (fun ω => quadPart (D ω - matrixExpect μ D) Q x y) 2 μ ≤
      ENNReal.ofReal (c₄ ^ 2 * vecNorm x * vecNorm y * frob Q) := by
  set F : Fin W → Ω → ℂ := fun j ω => bilinear x (D ω - matrixExpect μ D) (colQ Q j) *
    star (bilinear y (D ω - matrixExpect μ D) (colQ Q j))
  have hm : ∀ u v, AEStronglyMeasurable (fun ω => bilinear u (D ω - matrixExpect μ D) v) μ :=
    fun u v => MemLp.aestronglyMeasurable (lt_of_le_of_lt (h4 u v) ENNReal.ofReal_lt_top)
  have e : (fun ω => quadPart (D ω - matrixExpect μ D) Q x y) = ∑ j, F j := by
    funext ω; simp [quadPart, F, Finset.sum_apply]
  rw [e]
  refine (eLpNorm_sum_le (by norm_num)).trans ?_
  have hx := vecNorm_nonneg x; have hy := vecNorm_nonneg y
  calc ∑ j, eLpNorm (F j) 2 μ
      ≤ ∑ j, ENNReal.ofReal (c₄ ^ 2 * vecNorm x * vecNorm y * vecNorm (colQ Q j) ^ 2) := by
        refine Finset.sum_le_sum fun j _ => (eLpNorm_mul_star_le (hm _ _) (hm _ _)).trans ?_
        have hq := vecNorm_nonneg (colQ Q j)
        refine (mul_le_mul' (h4 x (colQ Q j)) (h4 y (colQ Q j))).trans ?_
        rw [← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))
    _ = ENNReal.ofReal (c₄ ^ 2 * vecNorm x * vecNorm y * frob Q) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity), ← sum_vecNorm_colQ_sq,
          Finset.mul_sum]

/-- `‖E f‖ₑ ≤ ‖f‖₂` on a probability space. -/
theorem enorm_integral_le_eLpNorm_two [IsProbabilityMeasure μ] {f : Ω → ℂ}
    (hf : AEStronglyMeasurable f μ) : ‖∫ ω, f ω ∂μ‖ₑ ≤ eLpNorm f 2 μ := by
  refine (enorm_integral_le_lintegral_enorm f).trans ?_
  rw [← eLpNorm_one_eq_lintegral_enorm hf]
  exact eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)

/-- **The centered quadratic form in `L²`.** -/
theorem eLpNorm_gamma_centered [IsProbabilityMeasure μ] (D : Ω → Matrix (Fin W) (Fin W) ℂ)
    (Q : Matrix (Fin W) (Fin W) ℂ) (hD : ∀ i j, Integrable (fun ω => D ω i j) μ) {c₂ c₄ : ℝ}
    (hc₂ : 0 ≤ c₂) (hc₄ : 0 ≤ c₄)
    (h2 : ∀ x y, eLpNorm (fun ω => bilinear x (D ω - matrixExpect μ D) y) 2 μ ≤
      ENNReal.ofReal (c₂ * vecNorm x * vecNorm y))
    (h4 : ∀ x y, eLpNorm (fun ω => bilinear x (D ω - matrixExpect μ D) y) 4 μ ≤
      ENNReal.ofReal (c₄ * vecNorm x * vecNorm y)) (x y : Fin W → ℂ) :
    eLpNorm (fun ω => bilinear x (D ω * Q * (D ω * Q)ᴴ) y -
        ∫ ω', bilinear x (D ω' * Q * (D ω' * Q)ᴴ) y ∂μ) 2 μ ≤
      ENNReal.ofReal (c₂ * vecNorm x * vecNorm (wVec (matrixExpect μ D) Q y) +
        c₂ * vecNorm y * vecNorm (wVec (matrixExpect μ D) Q x) +
        2 * (c₄ ^ 2 * vecNorm x * vecNorm y * frob Q)) := by
  set M := matrixExpect μ D
  have hL2 : ∀ u v, MemLp (fun ω => bilinear u (D ω - M) v) 2 μ :=
    fun u v => lt_of_le_of_lt (h2 u v) ENNReal.ofReal_lt_top
  obtain ⟨-, m1, -, m2, i3, m3⟩ := split_means D Q hD hL2 x y
  obtain ⟨-, hI⟩ := integral_bilinear_gamma D Q hD hL2 x y
  set f1 : Ω → ℂ := fun ω => bilinear x (D ω - M) (wVec M Q y)
  set f2 : Ω → ℂ := fun ω => bilinear y (D ω - M) (wVec M Q x)
  set f3 : Ω → ℂ := fun ω => quadPart (D ω - M) Q x y
  set κ := ∫ ω, f3 ω ∂μ
  have e : (fun ω => bilinear x (D ω * Q * (D ω * Q)ᴴ) y -
      ∫ ω', bilinear x (D ω' * Q * (D ω' * Q)ᴴ) y ∂μ) =
      f1 + star f2 + (f3 - fun _ => κ) := by
    funext ω
    rw [hI, ← m3, bilinear_gamma_split (D ω) M Q x y]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.star_apply, f1, f2, f3, κ]
    ring
  have hm3 : AEStronglyMeasurable f3 μ := i3.aestronglyMeasurable
  have hq := eLpNorm_quadPart_le D Q hc₄ h4 x y
  have hκ : eLpNorm (fun _ : Ω => κ) 2 μ ≤ eLpNorm f3 2 μ := by
    rw [eLpNorm_const κ (by norm_num) (IsProbabilityMeasure.ne_zero μ), measure_univ,
      ENNReal.one_rpow, mul_one]
    exact enorm_integral_le_eLpNorm_two hm3
  have hx := vecNorm_nonneg x; have hy := vecNorm_nonneg y
  have hwx := vecNorm_nonneg (wVec M Q x); have hwy := vecNorm_nonneg (wVec M Q y)
  have hfQ := frob_nonneg Q
  rw [e]
  calc eLpNorm (f1 + star f2 + (f3 - fun _ => κ)) 2 μ
      ≤ eLpNorm f1 2 μ + eLpNorm f2 2 μ + (eLpNorm f3 2 μ + eLpNorm f3 2 μ) := by
        refine (eLpNorm_add_le (by norm_num)).trans (add_le_add ?_ ?_)
        · refine (eLpNorm_add_le (by norm_num)).trans ?_
          rw [eLpNorm_star]
        · exact (eLpNorm_sub_le (by norm_num)).trans (add_le_add le_rfl hκ)
    _ ≤ ENNReal.ofReal (c₂ * vecNorm x * vecNorm (wVec M Q y)) +
          ENNReal.ofReal (c₂ * vecNorm y * vecNorm (wVec M Q x)) +
          (ENNReal.ofReal (c₄ ^ 2 * vecNorm x * vecNorm y * frob Q) +
            ENNReal.ofReal (c₄ ^ 2 * vecNorm x * vecNorm y * frob Q)) := by
        gcongr
        · exact h2 x _
        · exact h2 y _
    _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

end BlockBand.SourceProcess.ProjSeparator
