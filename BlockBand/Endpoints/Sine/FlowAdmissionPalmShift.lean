module

public import BlockBand.Endpoints.Sine.FlowAdmissionPalmFiber

/-!
# Algebra of the scalar pair shift on the coarea fiber

* `fap_assemble_shift`: `H + aP_S = assemble ω_a G` for `H = assemble ω G`.
* `fap_coareaF_shift`, `fap_frameM_shift`, `fap_recon_shift`: `F_{ω_a} = F + aI`,
  `M_{ω_a}(G') = M_ω(G' + aI)`, `G^{rec}_{ω_a}(G') = G^{rec}_ω(G' + aI) - aI` (for `U_v*U_v = 1`).
* `fap_frame_complete`: `vv* + U_vU_v* = 1` for a unit `v` and an orthonormal frame of `v^⊥`
  (square-matrix argument, `card S = 1 + (𝒩 - 1)`).
* `fap_trace_recon`: `Tr G^{rec} = E + Tr G' - v*F(E)v`.
* `fap_regression_shift`: `𝓡(E,v,F + aI) = 𝓡(E,v,F) exp((2a(E - Re v*Fv) - a²)/(2t))`.
* `fap_weight_shift`: `ρ'_a(G') 𝓡(E,v,F + aI) = 𝓡(E,v,F) ρ_a(G^{rec}_ω(G'))`, the likelihoods of
  `fap_lintegral_gue_shift` on `GUE_{𝒩-1}(t)` and `GUE_𝒩(t)`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Clocks
  BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal ComplexConjugate

section Algebra

variable (p : Parameters) (i : ZMod p.n)

theorem fap_star_dotProduct_self_eq_one {ι : Type*} [Fintype ι] (v : ι → ℂ)
    (hv : l2Norm v = 1) : star v ⬝ᵥ v = 1 := by
  have h : star v ⬝ᵥ v = ((∑ k, ‖v k‖ ^ 2 : ℝ) : ℂ) := by
    simp only [dotProduct, Pi.star_apply, RCLike.star_def, Complex.conj_mul']
    push_cast
    rfl
  rw [h, fap_sum_normSq_eq_one v hv, Complex.ofReal_one]

/-- `H + aP_S = assemble (H_R, C, V + aI) G`. -/
theorem fap_assemble_shift (a : ℝ) (ω : SplitState p i) (G : PairMatrix p i) :
    assemble p i ω G + (a : ℂ) • pairProjector p i =
      assemble p i (fa_shiftExterior p i a ω) G := by
  ext x y
  simp only [Matrix.add_apply, Matrix.smul_apply, pairProjector, Matrix.diagonal_apply,
    assemble, fa_shiftExterior, Matrix.one_apply, smul_eq_mul]
  by_cases hx : x.1 = i ∨ x.1 = i + 1 <;> by_cases hy : y.1 = i ∨ y.1 = i + 1
  · simp only [hx, hy, dite_true, ite_true]
    by_cases hxy : x = y
    · subst hxy; simp; ring
    · simp [hxy]
  · have hxy : x ≠ y := fun h => hy (h ▸ hx)
    simp [hx, hy, hxy]
  · have hxy : x ≠ y := fun h => hx (h ▸ hy)
    simp [hx, hy, hxy]
  · simp [hx, hy]

/-- Frame completeness: `vv* + U_vU_v* = 1` for a unit `v` and an orthonormal frame of `v^⊥`. -/
theorem fap_frame_complete (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ)
    (v : PairSite p i → ℂ) (hv : l2Norm v = 1) (hUU : (U v)ᴴ * U v = 1)
    (hUv : (U v)ᴴ *ᵥ v = 0) :
    vecMulVec v (star v) + U v * (U v)ᴴ = 1 := by
  classical
  set A₁ : Matrix (PairSite p i) Unit ℂ := replicateCol Unit v
  have hcard : Fintype.card (PairSite p i) = Fintype.card (Unit ⊕ FrameIndex p) := by
    rw [card_pairSite, Fintype.card_sum, Fintype.card_unit, Fintype.card_fin]
    have := p.W_pos
    omega
  have hvv := fap_star_dotProduct_self_eq_one v hv
  have hRC : fromRows A₁ᴴ (U v)ᴴ * fromCols A₁ (U v) = 1 := by
    rw [fromRows_mul_fromCols, hUU, ← Matrix.fromBlocks_one]
    congr 1
    · ext a b
      simp only [A₁, Matrix.mul_apply, Matrix.conjTranspose_apply, replicateCol_apply,
        Matrix.one_apply_eq]
      simpa [dotProduct] using hvv
    · ext a j
      have h := congrFun hUv j
      simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Pi.zero_apply] at h
      simp only [A₁, Matrix.mul_apply, Matrix.conjTranspose_apply, replicateCol_apply,
        Matrix.zero_apply]
      have h' := congrArg star h
      simp only [star_sum, star_mul', star_star, star_zero] at h'
      rw [← h']
      exact Finset.sum_congr rfl fun x _ => mul_comm _ _
    · ext j a
      have h := congrFun hUv j
      simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Pi.zero_apply] at h
      simp only [A₁, Matrix.mul_apply, Matrix.conjTranspose_apply, replicateCol_apply,
        Matrix.zero_apply]
      exact h
  have hCR := (mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq hcard)).mpr hRC
  rw [fromCols_mul_fromRows] at hCR
  rw [← hCR, vecMulVec_eq Unit, conjTranspose_replicateCol]

/-- `F_{ω_a}(E) = F_ω(E) + aI`. -/
theorem fap_coareaF_shift (a : ℝ) (ω : SplitState p i) (E : ℝ) :
    physicalCoareaF (fa_shiftExterior p i a ω).1 (fa_shiftExterior p i a ω).2.1
        (fa_shiftExterior p i a ω).2.2 E =
      physicalCoareaF ω.1 ω.2.1 ω.2.2 E + (a : ℂ) • 1 := by
  simp only [fa_shiftExterior, physicalCoareaF]
  abel

theorem fap_UFU_shift (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ)
    (v : PairSite p i → ℂ) (hUU : (U v)ᴴ * U v = 1) (F : PairMatrix p i) (a : ℝ) :
    (U v)ᴴ * (F + (a : ℂ) • 1) * U v = (U v)ᴴ * F * U v + (a : ℂ) • 1 := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hUU]

/-- `M_{ω_a}(G') = M_ω(G' + aI)`. -/
theorem fap_frameM_shift (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ)
    (a : ℝ) (ω : SplitState p i) (E : ℝ) (v : PairSite p i → ℂ) (hUU : (U v)ᴴ * U v = 1)
    (G' : Matrix (FrameIndex p) (FrameIndex p) ℂ) :
    frameM p i U (fa_shiftExterior p i a ω) E v G' = frameM p i U ω E v (G' + (a : ℂ) • 1) := by
  unfold frameM
  rw [fap_coareaF_shift, fap_UFU_shift p i U v hUU]
  abel

/-- `G^{rec}_{ω_a}(G') = G^{rec}_ω(G' + aI) - aI`. -/
theorem fap_recon_shift (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ)
    (a : ℝ) (ω : SplitState p i) (E : ℝ) (v : PairSite p i → ℂ) (hUU : (U v)ᴴ * U v = 1)
    (G' : Matrix (FrameIndex p) (FrameIndex p) ℂ) :
    reconstructedGaussian p i U (fa_shiftExterior p i a ω) E v G' =
      reconstructedGaussian p i U ω E v (G' + (a : ℂ) • 1) - (a : ℂ) • 1 := by
  unfold reconstructedGaussian
  dsimp only
  rw [fap_coareaF_shift, fap_UFU_shift p i U v hUU]
  have h : (U v)ᴴ * physicalCoareaF ω.1 ω.2.1 ω.2.2 E * U v + (a : ℂ) • 1 + G' =
      (U v)ᴴ * physicalCoareaF ω.1 ω.2.1 ω.2.2 E * U v + (G' + (a : ℂ) • 1) := by abel
  rw [h]
  abel

/-- `Tr G^{rec} = E + Tr G' - v*F(E)v` for a unit `v` and an orthonormal frame of `v^⊥`. -/
theorem fap_trace_recon (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ)
    (ω : SplitState p i) (E : ℝ) (v : PairSite p i → ℂ) (hv : l2Norm v = 1)
    (hUU : (U v)ᴴ * U v = 1) (hUv : (U v)ᴴ *ᵥ v = 0)
    (G' : Matrix (FrameIndex p) (FrameIndex p) ℂ) :
    (reconstructedGaussian p i U ω E v G').trace =
      (E : ℂ) + G'.trace - star v ⬝ᵥ (physicalCoareaF ω.1 ω.2.1 ω.2.2 E *ᵥ v) := by
  unfold reconstructedGaussian
  dsimp only
  set F := physicalCoareaF ω.1 ω.2.1 ω.2.2 E
  have hcomp := fap_frame_complete p i U v hv hUU hUv
  have hUUt : U v * (U v)ᴴ = 1 - vecMulVec v (star v) := by
    rw [← hcomp]; abel
  have h1 : (U v * ((U v)ᴴ * F * U v + G') * (U v)ᴴ).trace =
      ((U v)ᴴ * F * U v).trace + G'.trace := by
    rw [trace_mul_cycle, hUU, Matrix.one_mul, trace_add]
  have h2 : ((U v)ᴴ * F * U v).trace = F.trace - star v ⬝ᵥ (F *ᵥ v) := by
    rw [trace_mul_cycle, hUUt, Matrix.sub_mul, Matrix.one_mul, trace_sub, vecMulVec_mul,
      trace_vecMulVec, dotProduct_comm, ← Matrix.dotProduct_mulVec]
  have h3 : v ⬝ᵥ star v = 1 := by
    rw [dotProduct_comm]; exact fap_star_dotProduct_self_eq_one v hv
  rw [trace_sub, trace_add, trace_smul, trace_vecMulVec, h3, h1, h2, smul_eq_mul, mul_one]
  ring

/-- `𝓡(E, v, F + aI) = 𝓡(E, v, F) exp((2a(E - Re v*Fv) - a²)/(2t))` for a unit `v`. -/
theorem fap_regression_shift {ι : Type*} [Fintype ι] [DecidableEq ι] (t E a : ℝ)
    (v : ι → ℂ) (hv : l2Norm v = 1) (F : Matrix ι ι ℂ) :
    regressionFactor t E v (F + (a : ℂ) • 1) =
      regressionFactor t E v F *
        Real.exp ((2 * a * (E - (star v ⬝ᵥ (F *ᵥ v)).re) - a ^ 2) / (2 * t)) := by
  have hvv := fap_star_dotProduct_self_eq_one v hv
  have hmv : (F + (a : ℂ) • 1) *ᵥ v = F *ᵥ v + (a : ℂ) • v := by
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hq : star v ⬝ᵥ ((F + (a : ℂ) • 1) *ᵥ v) = star v ⬝ᵥ (F *ᵥ v) + (a : ℂ) := by
    rw [hmv, dotProduct_add, dotProduct_smul, hvv, smul_eq_mul, mul_one]
  have hr : (F + (a : ℂ) • 1) *ᵥ v - (star v ⬝ᵥ ((F + (a : ℂ) • 1) *ᵥ v)) • v =
      F *ᵥ v - (star v ⬝ᵥ (F *ᵥ v)) • v := by
    rw [hq, hmv, add_smul]; abel
  unfold regressionFactor
  dsimp only
  rw [hr, hq, ← Real.exp_add]
  congr 1
  simp only [Complex.add_re, Complex.ofReal_re]
  by_cases ht : t = 0
  · simp [ht]
  · field_simp
    ring

end Algebra

/-!
## The fixed-exterior coarea identity transfers along the pair shift
-/

section Transfer

variable (p : Parameters) (i : ZMod p.n)

theorem fap_pairTime_ne_zero : pairTime p (pairS p) ≠ 0 := by
  have hs : 0 < pairS p := lt_min p.b_pos p.c_pos
  have hW : (0 : ℝ) < 2 * (p.W : ℝ) := by have := p.W_pos; positivity
  exact (Real.toNNReal_pos.mpr (div_pos hs hW)).ne'

theorem fap_card_frameIndex : (Fintype.card (FrameIndex p) : ℝ) = 2 * (p.W : ℝ) - 1 := by
  rw [Fintype.card_fin]
  have : 1 ≤ 2 * p.W := by have := p.W_pos; omega
  push_cast [this]
  ring

/-- Rearrangement in `[0,∞]`. -/
theorem fap_rearrange (A B C D I X : ℝ≥0∞) (h : D * B = A * C) :
    A * I * (C * X) = D * (B * I * X) := by
  rw [← mul_assoc, mul_right_comm A I C, ← h]; ring

/-- **The weight identity**: `ρ'_a(G'') 𝓡(E,v,F + aI) = 𝓡(E,v,F) ρ_a(G^{rec}_ω(G''))`, times any
nonnegative factor, for a unit `v` with an orthonormal frame of `v^⊥`. -/
theorem fap_weight_shift (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ)
    (a : ℝ) (ω : SplitState p i) (E : ℝ) (v : PairSite p i → ℂ) (hv : l2Norm v = 1)
    (hUU : (U v)ᴴ * U v = 1) (hUv : (U v)ᴴ *ᵥ v = 0) (c y x : ℝ) (hc : 0 ≤ c) (hy : 0 ≤ y)
    (hx : 0 ≤ x) (G'' : Matrix (FrameIndex p) (FrameIndex p) ℂ) :
    fap_gueDensity (pairTime p (pairS p)) a G'' *
        ENNReal.ofReal (c * regressionFactor (pairTime p (pairS p)) E v
          (physicalCoareaF ω.1 ω.2.1 ω.2.2 E + (a : ℂ) • 1) * y * x) =
      ENNReal.ofReal (c * regressionFactor (pairTime p (pairS p)) E v
          (physicalCoareaF ω.1 ω.2.1 ω.2.2 E) * y * x) *
        fap_gueDensity (pairTime p (pairS p)) a (reconstructedGaussian p i U ω E v G'') := by
  set t := pairTime p (pairS p)
  have ht : (t : ℝ) ≠ 0 := fun h => fap_pairTime_ne_zero p (NNReal.coe_eq_zero.mp h)
  set F := physicalCoareaF ω.1 ω.2.1 ω.2.2 E
  have hR0 : 0 ≤ regressionFactor t E v F := (Real.exp_pos _).le
  unfold fap_gueDensity
  rw [fap_regression_shift (t : ℝ) E a v hv F, fap_trace_recon p i U ω E v hv hUU hUv,
    fap_card_frameIndex, card_pairSite]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (mul_nonneg hc hR0) hy) hx)]
  congr 1
  have key : Real.exp ((a * G''.trace.re - (2 * (p.W : ℝ) - 1) * a ^ 2 / 2) / t) *
      Real.exp ((2 * a * (E - (star v ⬝ᵥ (F *ᵥ v)).re) - a ^ 2) / (2 * t)) =
      Real.exp ((a * ((E : ℂ) + G''.trace - star v ⬝ᵥ (F *ᵥ v)).re -
        ((2 * p.W : ℕ) : ℝ) * a ^ 2 / 2) / t) := by
    rw [← Real.exp_add]
    congr 1
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re]
    push_cast
    field_simp
    ring
  rw [← key]
  ring

/-- The pair shift is a measurable affine map in the frame Gaussian. -/
theorem fap_measurable_recon_G (U : (PairSite p i → ℂ) → Matrix (PairSite p i) (FrameIndex p) ℂ)
    (ω : SplitState p i) (E : ℝ) (v : PairSite p i → ℂ) :
    Measurable fun G'' : Matrix (FrameIndex p) (FrameIndex p) ℂ =>
      reconstructedGaussian p i U ω E v G'' := by
  unfold reconstructedGaussian
  exact fap_measurable_matrix_sub (fap_measurable_matrix_add measurable_const
    (measurable_mul_matrixC (measurable_mul_matrixC measurable_const
      (fap_measurable_matrix_add measurable_const measurable_id)) measurable_const))
    measurable_const

end Transfer

end BlockBand.Endpoints
