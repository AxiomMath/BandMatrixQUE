module

public import BlockBand.Palm.ReferenceFlowStatic
public import BlockBand.Critical.RelativeVectors.RelativeDuhamel.RFSplit

/-!
# Derivatives of affine averages and Euclidean array bounds

* `integral_affine_fderiv_clm`: for random affine maps `z ↦ A_ω z + b_ω` with `‖A_ω‖ ≤ M` a.s.
  and a bounded-`C²` test `f` (sup-norm operator norms), the average
  `g(z) = ∫ f(A_ω z + b_ω) dP` is `C²` with `Dg(z) = ∫ Df(A z + b) ∘ A` and
  `D²g(z) = ∫ affD2 f A (A z + b)` as identities of continuous (bi)linear maps. This is
  `integral_affine_contDiff` in operator form.
* Euclidean array norm: `√(arrayNormSq v) ≤ N r ‖v‖` (sup norm `‖v‖`), so an
  `IsArrayC2Bounded C` test has sup-norm derivative bounds `C N r` and `C (N r)²`.
* `ℓ²` contractions: entries of an `ℓ²`-contraction have modulus `≤ 1`, and `lmul K` contracts
  `arrayNormSq` columnwise.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors.AbstractFlow

open MeasureTheory Set Filter Matrix
open BlockBand.Palm.ReferenceFlow
open BlockBand.Internal.Contracts.CoareaPalm

section Affine

variable {Ω X : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The second-derivative integrand `(u, v) ↦ D²f(x)[A u, A v]` as a bilinear map. -/
def affD2 (f : X → ℝ) (A : X →L[ℝ] X) (x : X) : X →L[ℝ] X →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ X X ℝ).flip A).comp ((fderiv ℝ (fderiv ℝ f) x).comp A)

theorem affD2_apply (f : X → ℝ) (A : X →L[ℝ] X) (x u v : X) :
    affD2 f A x u v = fderiv ℝ (fderiv ℝ f) x (A u) (A v) := rfl

theorem norm_affD2_le {f : X → ℝ} {C : ℝ} (hb : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ C)
    (A : X →L[ℝ] X) (x : X) : ‖affD2 f A x‖ ≤ ‖A‖ * (C * ‖A‖) := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  refine mul_le_mul ?_ ?_ (norm_nonneg _) (norm_nonneg _)
  · refine (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun φ => ?_)
    simpa [mul_comm] using ContinuousLinearMap.opNorm_comp_le φ A
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (hb _) (norm_nonneg _))

theorem fderiv_fderiv_comp_affine_eq {f : X → ℝ} (hf : ContDiff ℝ 2 f) (A : X →L[ℝ] X)
    (b z : X) :
    fderiv ℝ (fderiv ℝ (fun z => f (A z + b))) z = affD2 f A (A z + b) := by
  rw [fderiv_comp_affine hf A b, (hasFDerivAt_fderiv_comp_affine hf A b z).fderiv]
  rfl

/-- **Average of a `C²` test along random affine maps, operator form.** -/
theorem integral_affine_fderiv_clm {A : Ω → X →L[ℝ] X} {b : Ω → X}
    (hA : AEStronglyMeasurable A P) (hbm : AEStronglyMeasurable b P) {M : ℝ}
    (hAM : ∀ᵐ ω ∂P, ‖A ω‖ ≤ M) {C : ℝ} {f : X → ℝ} (hf : ContDiff ℝ 2 f)
    (h0 : ∀ z, |f z| ≤ C) (h1 : ∀ z, ‖fderiv ℝ f z‖ ≤ C)
    (h2 : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ C) :
    (∀ z, fderiv ℝ (fun z => ∫ ω, f (A ω z + b ω) ∂P) z =
        ∫ ω, (fderiv ℝ f (A ω z + b ω)).comp (A ω) ∂P) ∧
      (∀ z, fderiv ℝ (fderiv ℝ (fun z => ∫ ω, f (A ω z + b ω) ∂P)) z =
        ∫ ω, affD2 f (A ω) (A ω z + b ω) ∂P) := by
  have hfc : Continuous f := hf.continuous
  have hf1c : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have hAb : AEStronglyMeasurable (fun ω => (A ω, b ω)) P := hA.prodMk hbm
  have hm0 : ∀ z, AEStronglyMeasurable (fun ω => f (A ω z + b ω)) P := fun z =>
    (hfc.comp ((continuous_fst.clm_apply continuous_const).add
      continuous_snd)).comp_aestronglyMeasurable hAb
  have hm1 : ∀ z, AEStronglyMeasurable (fun ω => fderiv ℝ (fun z => f (A ω z + b ω)) z) P := by
    intro z
    simp_rw [fderiv_comp_affine hf]
    exact ((hf1c.comp ((continuous_fst.clm_apply continuous_const).add continuous_snd)).clm_comp
      continuous_fst).comp_aestronglyMeasurable hAb
  have hm2 : ∀ z, AEStronglyMeasurable
      (fun ω => fderiv ℝ (fderiv ℝ (fun z => f (A ω z + b ω))) z) P := by
    intro z
    have hcm := (continuous_secondDerivIntegrand hf z).comp_aestronglyMeasurable hAb
    exact hcm.congr (Eventually.of_forall fun ω =>
      (fderiv_fderiv_comp_affine_eq hf (A ω) (b ω) z).symm)
  have hi : ∀ z, Integrable (fun ω => f (A ω z + b ω)) P := fun z =>
    integrable_of_bound' (hm0 z) (Eventually.of_forall fun ω => by
      simpa [Real.norm_eq_abs] using h0 (A ω z + b ω))
  have hC : 0 ≤ C := (norm_nonneg _).trans (h1 0)
  have hb1 : ∀ᵐ ω ∂P, ∀ z, ‖fderiv ℝ (fun z => f (A ω z + b ω)) z‖ ≤ C * M := by
    filter_upwards [hAM] with ω hω z
    rw [fderiv_comp_affine hf]
    exact (norm_fderiv_comp_affine_le h1 (A ω) (b ω) z).trans
      (mul_le_mul_of_nonneg_left hω hC)
  have hb2 : ∀ᵐ ω ∂P, ∀ z, ‖fderiv ℝ (fderiv ℝ (fun z => f (A ω z + b ω))) z‖ ≤
      M * (C * M) := by
    filter_upwards [hAM] with ω hω z
    refine (norm_fderiv_fderiv_comp_affine_le hf h2 (A ω) (b ω) z).trans ?_
    exact mul_le_mul hω (mul_le_mul_of_nonneg_left hω hC)
      (mul_nonneg hC (norm_nonneg _)) ((norm_nonneg _).trans hω)
  obtain ⟨_, hd1, hd2⟩ := integral_contDiff_two (P := P)
    (h := fun ω z => f (A ω z + b ω)) (Eventually.of_forall fun ω => contDiff_comp_affine hf _ _)
    hb1 hb2 hm0 hi hm1 hm2
  refine ⟨fun z => ?_, fun z => ?_⟩
  · rw [hd1 z]
    simp_rw [fderiv_comp_affine hf]
  · rw [hd2 z]
    simp_rw [fderiv_fderiv_comp_affine_eq hf]

end Affine

section Array

variable {N r : ℕ}

theorem arrayNormSq_le (v : Fin N → Fin r → ℂ) : arrayNormSq v ≤ (N * r : ℝ) * ‖v‖ ^ 2 := by
  unfold arrayNormSq
  calc ∑ i, ∑ q, ‖v i q‖ ^ 2 ≤ ∑ _i : Fin N, ∑ _q : Fin r, ‖v‖ ^ 2 := by
        gcongr with i _ q _
        exact (norm_le_pi_norm (v i) q).trans (norm_le_pi_norm v i)
    _ = (N * r : ℝ) * ‖v‖ ^ 2 := by simp [mul_assoc]

/-- The Euclidean array norm is at most `N r` times the sup norm. -/
theorem sqrt_arrayNormSq_le (v : Fin N → Fin r → ℂ) :
    Real.sqrt (arrayNormSq v) ≤ (N * r : ℝ) * ‖v‖ := by
  refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
  have hn : ((N * r : ℕ) : ℝ) ≤ ((N * r : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast Nat.le_self_pow two_ne_zero (N * r)
  push_cast at hn
  calc arrayNormSq v ≤ (N * r : ℝ) * ‖v‖ ^ 2 := arrayNormSq_le v
    _ ≤ (N * r : ℝ) ^ 2 * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right hn (by positivity)
    _ = ((N * r : ℝ) * ‖v‖) ^ 2 := by ring

theorem norm_fderiv_le_of_array {C : ℝ} {g : (Fin N → Fin r → ℂ) → ℝ}
    (hg : IsArrayC2Bounded C g) (z : Fin N → Fin r → ℂ) :
    ‖fderiv ℝ g z‖ ≤ C * (N * r) := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hg.bound z)
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (by positivity)) fun v => ?_
  rw [Real.norm_eq_abs, mul_assoc]
  exact (hg.deriv_bound z v).trans (mul_le_mul_of_nonneg_left (sqrt_arrayNormSq_le v) hC)

theorem norm_fderiv_fderiv_le_of_array {C : ℝ} {g : (Fin N → Fin r → ℂ) → ℝ}
    (hg : IsArrayC2Bounded C g) (z : Fin N → Fin r → ℂ) :
    ‖fderiv ℝ (fderiv ℝ g) z‖ ≤ C * (N * r) * (N * r) := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hg.bound z)
  have hK : 0 ≤ C * (N * r) * (N * r) := mul_nonneg (mul_nonneg hC (by positivity)) (by positivity)
  refine ContinuousLinearMap.opNorm_le_bound _ hK fun v => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hK (norm_nonneg v)) fun w => ?_
  rw [Real.norm_eq_abs]
  refine (hg.hessian_bound z v w).trans ?_
  calc C * Real.sqrt (arrayNormSq v) * Real.sqrt (arrayNormSq w) ≤
        C * ((N * r : ℝ) * ‖v‖) * ((N * r : ℝ) * ‖w‖) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (sqrt_arrayNormSq_le v) hC)
          (sqrt_arrayNormSq_le w) (Real.sqrt_nonneg _) (mul_nonneg hC (by positivity))
    _ = C * (N * r) * (N * r) * ‖v‖ * ‖w‖ := by ring

/-- Entries of an `ℓ²`-contraction have modulus at most `1`. -/
theorem norm_entry_le_one {K : Matrix (Fin N) (Fin N) ℂ}
    (hK : ∀ v : Fin N → ℂ, l2Norm (K *ᵥ v) ≤ l2Norm v) (i j : Fin N) : ‖K i j‖ ≤ 1 := by
  have h := hK (Pi.single j 1)
  have h1 : l2Norm (Pi.single j (1 : ℂ) : Fin N → ℂ) = 1 := by
    unfold l2Norm
    rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb])
      (fun hj => absurd (Finset.mem_univ j) hj)]
    simp
  have h2 : ‖K i j‖ ≤ l2Norm (K *ᵥ Pi.single j 1) := by
    unfold l2Norm
    refine Real.le_sqrt_of_sq_le ?_
    have := Finset.single_le_sum (f := fun k => ‖(K *ᵥ Pi.single j 1) k‖ ^ 2)
      (fun k _ => by positivity) (Finset.mem_univ i)
    simpa [mulVec_single_one] using this
  linarith

/-- `lmul K` contracts the Euclidean array norm when `K` is an `ℓ²`-contraction (columnwise). -/
theorem arrayNormSq_lmul_le {K : Matrix (Fin N) (Fin N) ℂ}
    (hK : ∀ v : Fin N → ℂ, l2Norm (K *ᵥ v) ≤ l2Norm v) (v : Fin N → Fin r → ℂ) :
    arrayNormSq (lmul K v) ≤ arrayNormSq v := by
  have hcol : ∀ q, ∑ i, ‖lmul K v i q‖ ^ 2 ≤ ∑ i, ‖v i q‖ ^ 2 := by
    intro q
    have h := hK (fun j => v j q)
    unfold l2Norm at h
    rw [Real.sqrt_le_sqrt_iff (by positivity)] at h
    simpa [lmul, Matrix.mulVec, dotProduct] using h
  unfold arrayNormSq
  rw [Finset.sum_comm, Finset.sum_comm (f := fun i q => ‖v i q‖ ^ 2)]
  exact Finset.sum_le_sum fun q _ => hcol q

end Array

end BlockBand.Critical.RelativeVectors.AbstractFlow
