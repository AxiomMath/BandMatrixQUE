module

public import BlockBand.SourceProcess.ProjSeparator.Algebra
public import BlockBand.SourceProcess.FullSource.MomentStep
public import BlockBand.SourceProcess.FullSourceCovariance.Interface

/-!
# The quadratic form `x*(DQQ*D*)y` of a random `D`: split and mean

Abstract: any probability space `μ`, a random `D : Ω → Mat_W` with integrable entries, `M = ED`
(entrywise), a deterministic `Q`, `D⁰ = D - M`.

* `bilinear_gamma_split` (deterministic): `x*(DQ(DQ)*)y = x*(MQ(MQ)*)y + x*D⁰w_y + conj(y*D⁰w_x)
  + Σ_j (x*D⁰q_j)conj(y*D⁰q_j)`, `w_x = QQ*M*x` (`wVec`), `q_j` the columns of `Q`;
* `split_means`: the two linear terms have mean `0`; the quadratic term is integrable with mean
  `Σ_j E[(x*D⁰q_j)conj(y*D⁰q_j)]` (`bilinearCrossCovariance`), given `L²` bilinear forms of `D⁰`;
* `integral_bilinear_gamma`: hence `E x*(DQ(DQ)*)y = x*(MQ(MQ)*)y + Σ_j crossCov(x, q_j, y, q_j)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ProjSeparator

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.SourceProcess.FullSourceCovariance
open scoped ENNReal ComplexOrder

variable {W : ℕ}

/-- `w_x = QQ*M*x`. -/
def wVec (M Q : Matrix (Fin W) (Fin W) ℂ) (x : Fin W → ℂ) : Fin W → ℂ := (Q * Qᴴ * Mᴴ) *ᵥ x

/-- `Σ_j (x*D⁰q_j)·conj(y*D⁰q_j)`. -/
def quadPart (D0 Q : Matrix (Fin W) (Fin W) ℂ) (x y : Fin W → ℂ) : ℂ :=
  ∑ j, bilinear x D0 (colQ Q j) * star (bilinear y D0 (colQ Q j))

theorem bilinear_add_mat {n : Type*} [Fintype n] (u : n → ℂ) (A B : Matrix n n ℂ) (v : n → ℂ) :
    bilinear u (A + B) v = bilinear u A v + bilinear u B v := by
  simp [bilinear, Matrix.add_mulVec, dotProduct_add]

theorem bilinear_mul_right {n : Type*} [Fintype n] (u : n → ℂ) (A B : Matrix n n ℂ) (v : n → ℂ) :
    bilinear u (A * B) v = bilinear u A (B *ᵥ v) := by
  simp [bilinear, Matrix.mulVec_mulVec]

/-- **The split** of `x*(DQ(DQ)*)y` around `M`. -/
theorem bilinear_gamma_split (D M Q : Matrix (Fin W) (Fin W) ℂ) (x y : Fin W → ℂ) :
    bilinear x (D * Q * (D * Q)ᴴ) y = bilinear x (M * Q * (M * Q)ᴴ) y +
      bilinear x (D - M) (wVec M Q y) + star (bilinear y (D - M) (wVec M Q x)) +
      quadPart (D - M) Q x y := by
  set D0 := D - M
  have hD : D = M + D0 := by simp [D0]
  have e : D * Q * (D * Q)ᴴ = M * Q * (M * Q)ᴴ + D0 * (Q * Qᴴ * Mᴴ) +
      (D0 * (Q * Qᴴ * Mᴴ))ᴴ + D0 * Q * (D0 * Q)ᴴ := by
    rw [hD]
    simp only [conjTranspose_mul, conjTranspose_add, conjTranspose_conjTranspose, Matrix.add_mul,
      Matrix.mul_add, Matrix.mul_assoc]
    abel
  have h1 : bilinear x (D0 * (Q * Qᴴ * Mᴴ)) y = bilinear x D0 (wVec M Q y) :=
    bilinear_mul_right _ _ _ _
  have h2 : bilinear x (D0 * (Q * Qᴴ * Mᴴ))ᴴ y = star (bilinear y D0 (wVec M Q x)) := by
    rw [FullSource.bilinear_conjTranspose, bilinear_mul_right]; rfl
  rw [e, bilinear_add_mat, bilinear_add_mat, bilinear_add_mat, h1, h2, bilinear_cqqc x y D0 Q]
  rfl

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem integrable_centered_entry [IsFiniteMeasure μ] (D : Ω → Matrix (Fin W) (Fin W) ℂ)
    (hD : ∀ i j, Integrable (fun ω => D ω i j) μ) (i j : Fin W) :
    Integrable (fun ω => (D ω - matrixExpect μ D) i j) μ := by
  refine ((hD i j).sub (integrable_const (matrixExpect μ D i j))).congr
    (Filter.Eventually.of_forall fun ω => ?_)
  simp

theorem integrable_star' {f : Ω → ℂ} (hf : Integrable f μ) : Integrable (fun ω => star (f ω)) μ :=
  memLp_one_iff_integrable.mp (memLp_one_iff_integrable.mpr hf).star

/-- The centered linear forms have mean `0`. -/
theorem integral_bilinear_centered [IsProbabilityMeasure μ] (D : Ω → Matrix (Fin W) (Fin W) ℂ)
    (hD : ∀ i j, Integrable (fun ω => D ω i j) μ) (x w : Fin W → ℂ) :
    ∫ ω, bilinear x (D ω - matrixExpect μ D) w ∂μ = 0 := by
  rw [FullSource.integral_bilinear _ (integrable_centered_entry D hD) x w,
    ContractingWords.matrixExpect_sub_const D _ hD, sub_self]
  simp [bilinear]

/-- **Means of the split.** -/
theorem split_means [IsProbabilityMeasure μ] (D : Ω → Matrix (Fin W) (Fin W) ℂ) (Q : Matrix (Fin W) (Fin W) ℂ)
    (hD : ∀ i j, Integrable (fun ω => D ω i j) μ)
    (h2 : ∀ x y, MemLp (fun ω => bilinear x (D ω - matrixExpect μ D) y) 2 μ) (x y : Fin W → ℂ) :
    Integrable (fun ω => bilinear x (D ω - matrixExpect μ D) (wVec (matrixExpect μ D) Q y)) μ ∧
      ∫ ω, bilinear x (D ω - matrixExpect μ D) (wVec (matrixExpect μ D) Q y) ∂μ = 0 ∧
      Integrable (fun ω => star (bilinear y (D ω - matrixExpect μ D)
        (wVec (matrixExpect μ D) Q x))) μ ∧
      ∫ ω, star (bilinear y (D ω - matrixExpect μ D) (wVec (matrixExpect μ D) Q x)) ∂μ = 0 ∧
      Integrable (fun ω => quadPart (D ω - matrixExpect μ D) Q x y) μ ∧
      ∫ ω, quadPart (D ω - matrixExpect μ D) Q x y ∂μ =
        ∑ j, bilinearCrossCovariance μ D x (colQ Q j) y (colQ Q j) := by
  have hc := integrable_centered_entry D hD
  have hT : ∀ j, Integrable (fun ω => bilinear x (D ω - matrixExpect μ D) (colQ Q j) *
      star (bilinear y (D ω - matrixExpect μ D) (colQ Q j))) μ := fun j =>
    (h2 x (colQ Q j)).integrable_mul (h2 y (colQ Q j)).star
  refine ⟨FullSource.integrable_bilinear _ hc _ _, integral_bilinear_centered D hD _ _,
    integrable_star' (FullSource.integrable_bilinear _ hc _ _), ?_, ?_, ?_⟩
  · have := integral_conj (μ := μ) (𝕜 := ℂ)
      (f := fun ω => bilinear y (D ω - matrixExpect μ D) (wVec (matrixExpect μ D) Q x))
    simp only [starRingEnd_apply] at this
    rw [this, integral_bilinear_centered D hD, star_zero]
  · unfold quadPart; exact integrable_finsetSum _ fun j _ => hT j
  · unfold quadPart
    rw [integral_finsetSum _ fun j _ => hT j]
    rfl

/-- **`E x*(DQ(DQ)*)y = x*(MQ(MQ)*)y + Σ_j crossCov(x, q_j, y, q_j)`.** -/
theorem integral_bilinear_gamma [IsProbabilityMeasure μ] (D : Ω → Matrix (Fin W) (Fin W) ℂ)
    (Q : Matrix (Fin W) (Fin W) ℂ) (hD : ∀ i j, Integrable (fun ω => D ω i j) μ)
    (h2 : ∀ x y, MemLp (fun ω => bilinear x (D ω - matrixExpect μ D) y) 2 μ) (x y : Fin W → ℂ) :
    Integrable (fun ω => bilinear x (D ω * Q * (D ω * Q)ᴴ) y) μ ∧
      ∫ ω, bilinear x (D ω * Q * (D ω * Q)ᴴ) y ∂μ =
        bilinear x (matrixExpect μ D * Q * (matrixExpect μ D * Q)ᴴ) y +
          ∑ j, bilinearCrossCovariance μ D x (colQ Q j) y (colQ Q j) := by
  obtain ⟨i1, m1, i2, m2, i3, m3⟩ := split_means D Q hD h2 x y
  have e : (fun ω => bilinear x (D ω * Q * (D ω * Q)ᴴ) y) = fun ω =>
      bilinear x (matrixExpect μ D * Q * (matrixExpect μ D * Q)ᴴ) y +
        bilinear x (D ω - matrixExpect μ D) (wVec (matrixExpect μ D) Q y) +
        star (bilinear y (D ω - matrixExpect μ D) (wVec (matrixExpect μ D) Q x)) +
        quadPart (D ω - matrixExpect μ D) Q x y := by
    funext ω; exact bilinear_gamma_split _ _ _ x y
  set c := bilinear x (matrixExpect μ D * Q * (matrixExpect μ D * Q)ᴴ) y
  have j1 : Integrable (fun ω => c +
      bilinear x (D ω - matrixExpect μ D) (wVec (matrixExpect μ D) Q y)) μ :=
    (integrable_const c).add i1
  have j2 : Integrable (fun ω => c +
      bilinear x (D ω - matrixExpect μ D) (wVec (matrixExpect μ D) Q y) +
      star (bilinear y (D ω - matrixExpect μ D) (wVec (matrixExpect μ D) Q x))) μ := j1.add i2
  rw [e]
  refine ⟨j2.add i3, ?_⟩
  rw [integral_add j2 i3, integral_add j1 i2, integral_add (integrable_const _) i1, m1,
    m2, m3, integral_const]
  simp

end BlockBand.SourceProcess.ProjSeparator
