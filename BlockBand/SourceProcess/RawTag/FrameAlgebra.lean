module

public import BlockBand.SourceProcess.RawTag.MomentTools

/-!
# The boundary frame of a unit tag as a Gaussian linear image

The boundary frame `𝒰*ξ` of a unit tag is `W^{-1/2}` times a fixed matrix `tagRows` applied to the
probe `g` (`frame_eq_smul`), with `Tr Y = Σ |tagRows|²` (`trace_tagResponse_eq`) and the norm
formula `norm_frame_rpow`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.RawTag

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open scoped Matrix ComplexOrder

variable {W : ℕ}

/-- The rows `S_{c,a} = conj 𝒰_{(l-1-β, a), c}` of the frame map. -/
def tagRows (b E : ℝ) (W l β : ℕ) (ω : GrowthPath W) : Matrix (Fin 2 × Fin W) (Fin W) ℂ :=
  fun c a => if h : β < l then star (boundaryToInterior b E W l ω (⟨l - 1 - β, by omega⟩, a) c)
    else 0

theorem frame_eq_smul (b E : ℝ) (l β : ℕ) (ω : GrowthPath W) (g : Fin W → ℂ) :
    frame b E W l β ω g = ((Real.sqrt (1 / W) : ℝ) : ℂ) • (tagRows b E W l β ω *ᵥ g) := by
  funext c
  simp only [frame, mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, conjTranspose_apply,
    unitTag, tagRows]
  by_cases h : β < l
  · set p : Fin l := ⟨l - 1 - β, by omega⟩
    rw [Fintype.sum_prod_type, Finset.sum_eq_single p]
    · simp only [h, and_true, dite_true, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [p, ↓reduceIte]; ring
    · intro i _ hi
      refine Finset.sum_eq_zero fun a _ => ?_
      have : ¬ (i.val = l - 1 - β ∧ β < l) := fun h' => hi (Fin.ext h'.1)
      simp [this]
    · simp
  · simp [h]

theorem trace_tagResponse_eq (b E : ℝ) (l β : ℕ) (ω : GrowthPath W) :
    (tagResponse b E W l β ω).trace =
      ((∑ c, ∑ a, ‖tagRows b E W l β ω c a‖ ^ 2 : ℝ) : ℂ) := by
  simp only [tagResponse, tagProjection, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.diagonal_apply, conjTranspose_apply]
  push_cast
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, tagRows]
  by_cases h : β < l
  · set p : Fin l := ⟨l - 1 - β, by omega⟩
    rw [Fintype.sum_prod_type, Finset.sum_eq_single p]
    · refine Finset.sum_congr rfl fun a _ => ?_
      simp only [h, true_and, p, ↓reduceIte, dite_true, mul_one, norm_star]
      rw [← Complex.conj_mul', Complex.star_def]
    · intro i _ hi
      refine Finset.sum_eq_zero fun a _ => ?_
      have : ¬ (β < l ∧ i.val = l - 1 - β) := fun h' => hi (Fin.ext h'.2)
      simp [this]
    · simp
  · simp [h]

theorem norm_frame_rpow (b E : ℝ) (l β : ℕ) (ω : GrowthPath W) (g : Fin W → ℂ) (r : ℝ) :
    vecNorm (frame b E W l β ω g) ^ r =
      ((W : ℝ)⁻¹) ^ (r / 2) * (∑ c, ‖(tagRows b E W l β ω *ᵥ g) c‖ ^ 2) ^ (r / 2) := by
  rw [vecNorm, Real.sqrt_eq_rpow, ← Real.rpow_mul (Finset.sum_nonneg fun _ _ => by positivity),
    ← Real.mul_rpow (by positivity) (Finset.sum_nonneg fun _ _ => by positivity)]
  congr 1
  · rw [frame_eq_smul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow,
      sq_abs, Real.sq_sqrt (by positivity), one_div]
  · ring

end BlockBand.SourceProcess.RawTag
