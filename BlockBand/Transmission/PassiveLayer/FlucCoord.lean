module

public import BlockBand.Transmission.PassiveLayer.BilMain

/-!
# Hilbert–Schmidt covariance contraction of the fresh layer derivative

* `gue_trace_coeff`, `ginibre_trace_coeff`: `tr(A G(ρ))` is a linear form in the Gaussian
  coordinates with coefficient energy `≤ 2t‖A‖²_HS` (GUE), `≤ 4(‖A‖²_HS + ‖A'‖²_HS)` (Ginibre
  and its adjoint).
* `layerDir_trace_sum_le`: `Σ_i v_i |tr(A ∂_iM)|² ≤ (4/W)‖A‖²_HS` (`hsSq`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveLayer

open Matrix MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.PassiveCovariance
open BlockBand.Internal.Contracts.CoareaPalm
open scoped Matrix.Norms.L2Operator ComplexOrder NNReal ENNReal ComplexConjugate

open BlockBand.Transmission

variable {W : ℕ}

/-- The squared Hilbert–Schmidt norm. -/
def hsSq {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) : ℝ := ∑ x, ∑ y, ‖A x y‖ ^ 2

theorem gueRaw_entry' (t : ℝ≥0) (ρ : (Fin W × Fin W) × Fin 2 → ℝ) (a b : Fin W) :
    Bridge.gueRaw t ρ a b = ((Real.sqrt t : ℂ) / 2) *
      (((ρ ((a, b), 0) : ℂ) + (ρ ((a, b), 1) : ℂ) * Complex.I) +
        ((ρ ((b, a), 0) : ℂ) - (ρ ((b, a), 1) : ℂ) * Complex.I)) := by
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have hs : (Real.sqrt ((t : ℝ) / 2) : ℂ) = (Real.sqrt t : ℂ) / (Real.sqrt 2 : ℂ) := by
    rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 2)]; push_cast; ring
  have hsq : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  simp only [Bridge.gueRaw, gueSample, BlockBand.SourceProcess.circularBrownianCoordinates,
    Matrix.of_apply, map_div₀, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, hs]
  field_simp
  rw [sq, hsq]
  ring

/-- Trace coefficients of a GUE sample: `tr(AG) = Σ ρ_k c_k`, `Σ|c_k|² ≤ t‖A‖²_HS`. -/
theorem gue_trace_coeff (t : ℝ≥0) (A : Matrix (Fin W) (Fin W) ℂ) :
    ∃ c : (Fin W × Fin W) × Fin 2 → ℂ, (∀ ρ, (A * Bridge.gueRaw t ρ).trace = ∑ k, (ρ k : ℂ) * c k) ∧
      ∑ k, ‖c k‖ ^ 2 ≤ 2 * t * hsSq A := by
  set α : ℂ := (Real.sqrt t : ℂ) / 2
  refine ⟨fun k => if k.2 = 0 then α * (A k.1.2 k.1.1 + A k.1.1 k.1.2)
    else α * Complex.I * (A k.1.2 k.1.1 - A k.1.1 k.1.2), fun ρ => ?_, ?_⟩
  · have hL : (A * Bridge.gueRaw t ρ).trace = ∑ x, ∑ y, A x y * Bridge.gueRaw t ρ y x := by
      simp [Matrix.trace, Matrix.mul_apply]
    have hR : ∑ k, (ρ k : ℂ) * (if k.2 = 0 then α * (A k.1.2 k.1.1 + A k.1.1 k.1.2)
        else α * Complex.I * (A k.1.2 k.1.1 - A k.1.1 k.1.2)) =
        ∑ a, ∑ b, ((ρ ((a, b), 0) : ℂ) * (α * (A b a + A a b)) +
          (ρ ((a, b), 1) : ℂ) * (α * Complex.I * (A b a - A a b))) := by
      rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
      simp [Fin.sum_univ_two]
    rw [hL, hR]
    simp only [gueRaw_entry']
    calc ∑ x, ∑ y, A x y * (α * ((ρ ((y, x), 0) : ℂ) + (ρ ((y, x), 1) : ℂ) * Complex.I +
          ((ρ ((x, y), 0) : ℂ) - (ρ ((x, y), 1) : ℂ) * Complex.I)))
        = ∑ x, ∑ y, A x y * α * ((ρ ((y, x), 0) : ℂ) + (ρ ((y, x), 1) : ℂ) * Complex.I) +
          ∑ x, ∑ y, A x y * α * ((ρ ((x, y), 0) : ℂ) - (ρ ((x, y), 1) : ℂ) * Complex.I) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun y _ => by ring
      _ = ∑ x, ∑ y, A y x * α * ((ρ ((x, y), 0) : ℂ) + (ρ ((x, y), 1) : ℂ) * Complex.I) +
          ∑ x, ∑ y, A x y * α * ((ρ ((x, y), 0) : ℂ) - (ρ ((x, y), 1) : ℂ) * Complex.I) := by
          rw [Finset.sum_comm (f := fun x y => A x y * α *
            ((ρ ((y, x), 0) : ℂ) + (ρ ((y, x), 1) : ℂ) * Complex.I))]
      _ = _ := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun y _ => by ring
  · rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp only [Fin.sum_univ_two, Fin.isValue, ↓reduceIte, one_ne_zero]
    have hα : ‖α‖ ^ 2 = (t : ℝ) / 4 := by
      simp only [α, norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), div_pow,
        Real.sq_sqrt (NNReal.coe_nonneg t)]
      norm_num
    have hpt : ∀ a b : Fin W, ‖α * (A b a + A a b)‖ ^ 2 + ‖α * Complex.I * (A b a - A a b)‖ ^ 2 ≤
        (t : ℝ) / 4 * (2 * ‖A b a‖ ^ 2 + 2 * ‖A a b‖ ^ 2) * 2 := by
      intro a b
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, mul_pow, mul_pow, hα]
      have h1 := norm_add_sq_le' (A b a) (A a b)
      have h2 := norm_add_sq_le' (A b a) (-A a b)
      rw [norm_neg, ← sub_eq_add_neg] at h2
      have ht : (0 : ℝ) ≤ t / 4 := by positivity
      nlinarith
    calc ∑ a, ∑ b, (‖α * (A b a + A a b)‖ ^ 2 + ‖α * Complex.I * (A b a - A a b)‖ ^ 2)
        ≤ ∑ a, ∑ b, ((t : ℝ) / 4 * (2 * ‖A b a‖ ^ 2 + 2 * ‖A a b‖ ^ 2) * 2) :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hpt a b
      _ = (t : ℝ) * (∑ a, ∑ b, ‖A b a‖ ^ 2) + (t : ℝ) * hsSq A := by
          simp only [hsSq, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
      _ = 2 * t * hsSq A := by
          rw [show (∑ a, ∑ b, ‖A b a‖ ^ 2) = hsSq A from Finset.sum_comm]; ring

/-- Trace coefficients of a Ginibre sample and its adjoint. -/
theorem ginibre_trace_coeff (A A' : Matrix (Fin W) (Fin W) ℂ) :
    ∃ c : Fin W × Fin W × Fin 2 → ℂ,
      (∀ ρ, (A * ginibreRaw ρ).trace + (A' * (ginibreRaw ρ)ᴴ).trace = ∑ k, (ρ k : ℂ) * c k) ∧
      ∑ k, ‖c k‖ ^ 2 ≤ 4 * (hsSq A + hsSq A') := by
  refine ⟨fun k => if k.2.2 = 0 then A k.2.1 k.1 + A' k.1 k.2.1
    else Complex.I * A k.2.1 k.1 - Complex.I * A' k.1 k.2.1, fun ρ => ?_, ?_⟩
  · have hL : (A * ginibreRaw ρ).trace + (A' * (ginibreRaw ρ)ᴴ).trace =
        ∑ x, ∑ y, (A y x * ginibreRaw ρ x y + A' x y * star (ginibreRaw ρ x y)) := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
      rw [Finset.sum_comm (f := fun x y => A x y * ginibreRaw ρ y x), ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Finset.sum_add_distrib]
    rw [hL, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [ginibreRaw, Matrix.of_apply, Fin.sum_univ_two, Fin.isValue, ↓reduceIte,
      one_ne_zero, star_add, star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
    ring
  · rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.isValue, ↓reduceIte, one_ne_zero]
    have hpt : ∀ a b : Fin W, ‖A b a + A' a b‖ ^ 2 + ‖Complex.I * A b a - Complex.I * A' a b‖ ^ 2 ≤
        4 * ‖A b a‖ ^ 2 + 4 * ‖A' a b‖ ^ 2 := by
      intro a b
      have h1 := norm_add_sq_le' (A b a) (A' a b)
      have h2 := norm_add_sq_le' (Complex.I * A b a) (-(Complex.I * A' a b))
      rw [norm_neg, ← sub_eq_add_neg, norm_mul, norm_mul, Complex.norm_I, one_mul, one_mul] at h2
      linarith
    calc ∑ a, ∑ b, (‖A b a + A' a b‖ ^ 2 + ‖Complex.I * A b a - Complex.I * A' a b‖ ^ 2)
        ≤ ∑ a, ∑ b, (4 * ‖A b a‖ ^ 2 + 4 * ‖A' a b‖ ^ 2) :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hpt a b
      _ = 4 * (∑ a, ∑ b, ‖A b a‖ ^ 2) + 4 * hsSq A' := by
          simp only [hsSq, Finset.mul_sum, ← Finset.sum_add_distrib]
      _ = 4 * (hsSq A + hsSq A') := by
          rw [show (∑ a, ∑ b, ‖A b a‖ ^ 2) = hsSq A from Finset.sum_comm]; ring

theorem trace_mul_fromBlocks {m : Type*} [Fintype m] (A : Matrix (m ⊕ m) (m ⊕ m) ℂ)
    (P Q R : Matrix m m ℂ) :
    (A * fromBlocks P Q R 0).trace = (A.toBlocks₁₁ * P).trace + (A.toBlocks₂₁ * Q).trace +
      (A.toBlocks₁₂ * R).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_sum_type, fromBlocks_apply₁₁,
    fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.toBlocks₁₁,
    Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply, mul_zero,
    Finset.sum_const_zero, add_zero, Finset.sum_add_distrib]

theorem trace_mul_liftX (M : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ)
    (D : Matrix (Fin W) (Fin W) ℂ) :
    (M * liftX D).trace = (M.submatrix embed0 embed0 * D).trace := by
  simp [Matrix.trace, Matrix.mul_apply, liftX, embed0, Fintype.sum_prod_type]

theorem hsSq_submatrix_embed0 (M : Matrix (Fin 1 × Fin W) (Fin 1 × Fin W) ℂ) :
    hsSq (M.submatrix embed0 embed0) = hsSq M := by
  simp [hsSq, embed0, Fintype.sum_prod_type]

theorem hsSq_blocks {m : Type*} [Fintype m] (A : Matrix (m ⊕ m) (m ⊕ m) ℂ) :
    hsSq A.toBlocks₁₁ + hsSq A.toBlocks₁₂ + hsSq A.toBlocks₂₁ + hsSq A.toBlocks₂₂ = hsSq A := by
  simp only [hsSq, Fintype.sum_sum_type, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁,
    Matrix.toBlocks₂₂, Matrix.of_apply, Finset.sum_add_distrib]
  ring

theorem hsSq_nonneg {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) : 0 ≤ hsSq A := by
  unfold hsSq; positivity

/-- **Hilbert–Schmidt covariance contraction of the layer derivative**:
`Σ_i v_i |tr(A ∂_iM)|² ≤ (4/W)‖A‖²_HS`. -/
theorem layerDir_trace_sum_le {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hW : 1 ≤ W)
    (A : Matrix (LayerSite W .oneBlockOnePort) (LayerSite W .oneBlockOnePort) ℂ) :
    ∑ i, (coordVar W b i : ℝ) * ‖(A * layerDir b (Pi.single i 1)).trace‖ ^ 2 ≤
      4 / W * hsSq A := by
  set A₁₁ := A.toBlocks₁₁.submatrix embed0 embed0
  set A₁₂ := A.toBlocks₁₂.submatrix embed0 embed0
  set A₂₁ := A.toBlocks₂₁.submatrix embed0 embed0
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have htA : ((tA W b : ℝ≥0) : ℝ) ≤ 1 / W := by
    rw [tA, Real.coe_toNNReal _ (by apply div_nonneg <;> linarith)]
    exact div_le_div_of_nonneg_right (by linarith) hW'.le
  have htB : ((Real.toNNReal (b / W) : ℝ≥0) : ℝ) ≤ 1 / W := by
    rw [Real.coe_toNNReal _ (by positivity)]
    exact div_le_div_of_nonneg_right (by linarith) hW'.le
  obtain ⟨g, hg, hgv⟩ := gue_trace_coeff (tA W b) A₁₁
  obtain ⟨d, hd, hdv⟩ := ginibre_trace_coeff A₂₁ A₁₂
  have g0 : Bridge.gueRaw (tA W b) (0 : (Fin W × Fin W) × Fin 2 → ℝ) = 0 := by
    ext; simp [Bridge.gueRaw, gueSample, BlockBand.SourceProcess.circularBrownianCoordinates]
  have gi0 : ginibreRaw (0 : Fin W × Fin W × Fin 2 → ℝ) = 0 := by ext; simp [ginibreRaw]
  have l0 : liftX (0 : Matrix (Fin W) (Fin W) ℂ) = 0 := by ext; simp [liftX]
  have hinl : ∀ k, (A * layerDir b (Pi.single (Sum.inl k) 1)).trace = g k := by
    intro k
    have e1 : (fun j => (Pi.single (Sum.inl k) (1 : ℝ) : CoordW W → ℝ) (Sum.inr j)) = 0 := by
      funext j; simp
    have e2 : (fun j => (Pi.single (Sum.inl k) (1 : ℝ) : CoordW W → ℝ) (Sum.inl j)) =
        Pi.single k 1 := by
      funext j; by_cases h : j = k <;> simp [h]
    rw [layerDir, e1, e2, gi0, l0, conjTranspose_zero, trace_mul_fromBlocks, trace_mul_liftX]
    simp only [Matrix.mul_zero, trace_zero, add_zero]
    have := hg (Pi.single k 1)
    rw [sum_single_mul] at this
    exact this
  have hinr : ∀ k, (A * layerDir b (Pi.single (Sum.inr k) 1)).trace = d k := by
    intro k
    have e1 : (fun j => (Pi.single (Sum.inr k) (1 : ℝ) : CoordW W → ℝ) (Sum.inl j)) = 0 := by
      funext j; simp
    have e2 : (fun j => (Pi.single (Sum.inr k) (1 : ℝ) : CoordW W → ℝ) (Sum.inr j)) =
        Pi.single k 1 := by
      funext j; by_cases h : j = k <;> simp [h]
    rw [layerDir, e1, e2, g0, l0, trace_mul_fromBlocks]
    simp only [Matrix.mul_zero, trace_zero, zero_add]
    rw [trace_mul_liftX, ← liftX_conjTranspose, trace_mul_liftX, ← sum_single_mul k d, ← hd]
  rw [Fintype.sum_sum_type]
  simp only [coordVar, Sum.elim_inl, Sum.elim_inr, NNReal.coe_one, one_mul, hinl, hinr]
  have hB : ∑ k, ((Real.toNNReal (b / W) / 2 : ℝ≥0) : ℝ) * ‖d k‖ ^ 2 ≤
      (1 / W) / 2 * (4 * (hsSq A₂₁ + hsSq A₁₂)) := by
    rw [← Finset.mul_sum]
    have h0 : (0 : ℝ) ≤ ∑ k, ‖d k‖ ^ 2 := by positivity
    have : ((Real.toNNReal (b / W) / 2 : ℝ≥0) : ℝ) ≤ (1 / W) / 2 := by
      rw [NNReal.coe_div]; push_cast; linarith
    exact mul_le_mul this hdv h0 (by positivity)
  have hG : ∑ k, ‖g k‖ ^ 2 ≤ 2 * (1 / W) * hsSq A₁₁ := by
    refine hgv.trans ?_
    have := hsSq_nonneg A₁₁
    nlinarith
  have hblk := hsSq_blocks A
  rw [← hsSq_submatrix_embed0 A.toBlocks₁₁, ← hsSq_submatrix_embed0 A.toBlocks₁₂,
    ← hsSq_submatrix_embed0 A.toBlocks₂₁] at hblk
  have h22 := hsSq_nonneg A.toBlocks₂₂
  have h11 := hsSq_nonneg A₁₁
  have h12 := hsSq_nonneg A₁₂
  have h21 := hsSq_nonneg A₂₁
  have hw0 : (0 : ℝ) ≤ 1 / W := by positivity
  have e : (4 : ℝ) / W = 4 * (1 / W) := by ring
  rw [e]
  nlinarith

end BlockBand.Transmission.PassiveLayer
