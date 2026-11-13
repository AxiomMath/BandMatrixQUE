module

public import BlockBand.SourceProcess.ComplexSourceLaw.SourceBound

/-!
# Entries of `𝒦` under the probed-path law are raw tag forms

Each entry of the complex source matrix is a bilinear form `u*Gv` of the interior resolvent in the
tag vectors of the probes (`complexSourceK_apply`, `probeColumn_eq_tagVector`), and a pair of
distinct probe Gaussians has the product law (`pi_map_pair`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexSourceLaw

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.FullSourceStops

variable {W : ℕ}

/-- The bilinear form `u*Gv`. -/
def tagForm {n : ℕ} (G : Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ) (u v : Fin n × Fin W → ℂ) :
    ℂ :=
  star u ⬝ᵥ (G *ᵥ v)

theorem complexSourceK_apply (b E : ℝ) {np : ℕ} (n : ℕ) (τ m : Fin np → ℝ) (x : ProbedPath W np)
    (i j : Fin np) :
    complexSourceK b E W n τ m x i j = tagForm (fullInverse b E W n x.1).toBlocks₁₁
      (fun y => probeColumns W n τ m x.2 y i) (fun y => probeColumns W n τ m x.2 y j) := by
  simp only [complexSourceK, tagForm, Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct,
    mulVec, Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => by ring

/-- The probe column of a tag inside the path is the tag vector at position `n - 1 - ⌊Wτ⌋`. -/
theorem probeColumn_eq_tagVector {np : ℕ} (n : ℕ) (τ m : Fin np → ℝ) (g : Fin np → Fin W → ℂ)
    (i : Fin np) (h : ⌊(W : ℝ) * τ i⌋₊ < n) :
    (fun y => probeColumns W n τ m g y i) =
      tagVector W n ⟨n - 1 - ⌊(W : ℝ) * τ i⌋₊, by omega⟩ (m i) (g i) := by
  funext y
  simp only [probeColumns, tagVector, Fin.ext_iff, h, true_and]

/-- A tag outside the path has a zero probe column. -/
theorem probeColumn_eq_zero {np : ℕ} (n : ℕ) (τ m : Fin np → ℝ) (g : Fin np → Fin W → ℂ)
    (i : Fin np) (h : ¬ ⌊(W : ℝ) * τ i⌋₊ < n) : (fun y => probeColumns W n τ m g y i) = 0 := by
  funext y
  simp [probeColumns, h]

theorem measurable_tagVector (n : ℕ) (k : Fin n) (mk : ℝ) :
    Measurable fun g : Fin W → ℂ => tagVector W n k mk g := by
  refine Measurable.of_eval fun y => ?_
  simp only [tagVector]
  split_ifs
  · exact measurable_const.mul (measurable_pi_apply _)
  · exact measurable_const

theorem measurable_tagForm {α : Type*} [MeasurableSpace α] {n : ℕ}
    {G : α → Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ} {u v : α → Fin n × Fin W → ℂ}
    (hG : Measurable G) (hu : Measurable u) (hv : Measurable v) :
    Measurable fun a => tagForm (G a) (u a) (v a) := by
  simp only [tagForm, dotProduct, mulVec, Pi.star_apply]
  exact Finset.measurable_sum _ fun y _ =>
    (Complex.continuous_conj.measurable.comp ((measurable_pi_apply y).comp hu)).mul
      (Finset.measurable_sum _ fun z _ => hG.eval_matrix.mul ((measurable_pi_apply z).comp hv))

theorem measurable_interior (b E : ℝ) (n : ℕ) :
    Measurable fun ω : GrowthPath W => (fullInverse b E W n ω).toBlocks₁₁ :=
  Measurable.of_eval_matrix _ fun _ _ => (measurable_fullInverse b E n).eval_matrix

/-- `(gᵢ, gⱼ)` under `Measure.pi` (`i ≠ j`) has the product law. -/
theorem pi_map_pair {ι β : Type*} [Fintype ι] [MeasurableSpace β] (ρ : Measure β)
    [IsProbabilityMeasure ρ] {i j : ι} (hij : i ≠ j) :
    (Measure.pi fun _ : ι => ρ).map (fun g => (g i, g j)) = ρ.prod ρ := by
  have hind : iIndepFun (fun k (g : ι → β) => g k) (Measure.pi fun _ : ι => ρ) :=
    iIndepFun_pi (X := fun _ => id) fun _ => aemeasurable_id
  have h2 := (hind.indepFun hij).map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
    (measurable_pi_apply j).aemeasurable
  rw [h2, (measurePreserving_eval (fun _ : ι => ρ) i).map_eq,
    (measurePreserving_eval (fun _ : ι => ρ) j).map_eq]

end BlockBand.SourceProcess.ComplexSourceLaw
