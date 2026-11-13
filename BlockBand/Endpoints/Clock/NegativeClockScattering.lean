module

public import BlockBand.Internal.Contracts.TransmissionPath
public import BlockBand.Endpoints.Clock.PhaseResolution
public import BlockBand.Layers.PathGrowthLaw

/-!
# Almost-sure unitarity and invertible transmission of the finite path

All Gaussian bonds are invertible almost surely; successive block inversion then makes the
finite-path transmission `t` invertible, and unitarity gives `tt* = I - r'r'* ≻ 0`. The
deterministic core `phase_resolution_average` takes `S Sᴴ = 1` and `IsUnit (transmission S).det`
as hypotheses; this file proves both for the scattering matrix `𝕊 = I - 2iηℝ`
(`TransmissionPath.scatteringMatrix`) of the near-end-grown Gaussian path of length `n ≥ 1`,
almost surely under `growthPathLaw W b`.

## Results

* `negativeClock_etaZ_pos`: `η = Im z_∂ > 0` for `0 < b < 1`, `|E| < 2`.
* `negativeClock_scattering_of_bonds` (deterministic): if every block `ω.1 k` is Hermitian and
  every bond `ω.2 k` is invertible, `η > 0` and `n ≥ 1`, then `𝕊 𝕊ᴴ = I` and the transmission
  block `t = 𝕊₁₀` is invertible. Method: `𝓜 - 𝓜ᴴ = diag(0, 2iη I)` gives invertibility of `𝓜`
  (imaginary part of `ψ*𝓜ψ`) and `ℝ - ℝᴴ = -2iη ℝℝᴴ`, hence unitarity; a downward propagation
  through the block-tridiagonal rows (bonds invertible) shows that a solution with zero far-port
  amplitude and no interior/far source vanishes, hence `ker t = 0`.
* `negativeClock_ae_scattering`: the hypotheses of the deterministic statement hold
  `growthPathLaw W b`-a.s. for `0 < b < 1/2`, `|E| < 2`: GUE samples are Hermitian, and a
  Ginibre matrix of positive variance is a.s. invertible (its determinant is a nonzero
  polynomial in the real Gaussian coordinates, `volume_mvPolynomial_zeroSet_fintype`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath
open scoped ENNReal NNReal ComplexConjugate Matrix

namespace NegativeClockScattering

/-!
## 1. Algebra
-/

/-- `star ψ ⬝ᵥ (Mᴴ ψ) = star (star ψ ⬝ᵥ (M ψ))`. -/
theorem dot_conjTranspose_mulVec {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) (ψ : ι → ℂ) :
    star ψ ⬝ᵥ (Mᴴ *ᵥ ψ) = star (star ψ ⬝ᵥ (M *ᵥ ψ)) := by
  simp only [dotProduct, mulVec, conjTranspose_apply, Pi.star_apply, star_sum, star_mul',
    star_star, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

section Unitary

variable {m p : Type*} [Fintype m] [Fintype p] [DecidableEq m] [DecidableEq p]

/-- If `M - Mᴴ = diag(0, κ I)` with `κ̄ = -κ`, then `𝕊 = I - κ (M⁻¹)₂₂` is unitary
(`𝕊𝕊ᴴ = I`). If `M` is singular, `M⁻¹ = 0` (Lean's totalized inverse) and `𝕊 = I`. -/
theorem unitary_of_skew (M : Matrix (m ⊕ p) (m ⊕ p) ℂ) (κ : ℂ) (hκ : star κ = -κ)
    (hD : M - Mᴴ = fromBlocks 0 0 0 (κ • 1)) :
    (1 - κ • (M⁻¹).toBlocks₂₂) * (1 - κ • (M⁻¹).toBlocks₂₂)ᴴ = 1 := by
  by_cases hM : IsUnit M.det
  · set G := M⁻¹ with hG
    set R := G.toBlocks₂₂ with hR
    have hGM : G * M = 1 := nonsing_inv_mul M hM
    have hMG : (Mᴴ * Gᴴ) = 1 := by rw [← conjTranspose_mul, hGM, conjTranspose_one]
    have key : G * (M - Mᴴ) * Gᴴ = Gᴴ - G := by
      rw [mul_sub, sub_mul, hGM, Matrix.one_mul, Matrix.mul_assoc, hMG, Matrix.mul_one]
    have hblk : (G * (M - Mᴴ) * Gᴴ).toBlocks₂₂ = κ • (R * Rᴴ) := by
      rw [hD, ← fromBlocks_toBlocks G, fromBlocks_conjTranspose, fromBlocks_multiply,
        fromBlocks_multiply, toBlocks_fromBlocks₂₂]
      simp [hR]
    have hblk2 : (Gᴴ - G).toBlocks₂₂ = Rᴴ - R := by
      ext i j; simp [hR, toBlocks₂₂, conjTranspose_apply]
    rw [key, hblk2] at hblk
    rw [conjTranspose_sub, conjTranspose_one, conjTranspose_smul, hκ, sub_mul, Matrix.one_mul,
      mul_sub, Matrix.mul_one, smul_mul_smul_comm]
    have e : (κ * -κ) • (R * Rᴴ) = -(κ • (κ • (R * Rᴴ))) := by
      rw [smul_smul, ← neg_smul, mul_neg]
    rw [e, ← hblk, smul_sub, neg_smul]
    abel
  · have : M⁻¹ = 0 := nonsing_inv_apply_not_isUnit M hM
    have h0 : (M⁻¹).toBlocks₂₂ = 0 := by rw [this]; ext i j; simp [toBlocks₂₂]
    simp [h0]

end Unitary

/-!
## 2. The block-tridiagonal rows of the path
-/

section Rows

variable {W n : ℕ}

/-- The full matrix with an arbitrary port diagonal `z`. -/
def fullM (E : ℝ) (z : ℂ) (P : PathSample W n) :
    Matrix (FullSite W n) (FullSite W n) ℂ :=
  fromBlocks (pathMatrix P - (E : ℂ) • 1) (pathPortCoupling P) (pathPortCoupling P)ᴴ (z • 1)

/-- The path matrix is Hermitian when its diagonal blocks are. -/
theorem pathMatrix_isHermitian {W r : ℕ} (P : PathSample W r) (hP : ∀ i, (P.1 i).IsHermitian) :
    (pathMatrix P).IsHermitian := by
  ext x y
  simp only [conjTranspose_apply, pathMatrix]
  by_cases h1 : y.1 = x.1
  · have h1' : x.1 = y.1 := h1.symm
    rw [ite_eq_left h1, ite_eq_left h1']
    rw [h1]; exact (hP x.1).apply x.2 y.2
  · have h1' : ¬ x.1 = y.1 := fun h => h1 h.symm
    rw [ite_eq_right h1, ite_eq_right h1']
    by_cases h2 : y.1.val + 1 = x.1.val
    · have h3 : ¬ x.1.val + 1 = y.1.val := by omega
      rw [dite_eq_left h2, dite_eq_right h3, dite_eq_left h2]
    · rw [dite_eq_right h2]
      by_cases h3 : x.1.val + 1 = y.1.val
      · rw [dite_eq_left h3, dite_eq_left h3, star_star]
      · rw [dite_eq_right h3, dite_eq_right h3, dite_eq_right h2, star_zero]

theorem far_row (P : PathSample W n) (hn : 0 < n) (ψ₁ : Fin n × Fin W → ℂ) (c : Fin W) :
    ((pathPortCoupling P)ᴴ *ᵥ ψ₁) (1, c) =
      ((P.2.2 1)ᴴ *ᵥ fun a => ψ₁ (⟨n - 1, by omega⟩, a)) c := by
  simp only [mulVec, dotProduct, conjTranspose_apply, pathPortCoupling, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (⟨n - 1, by omega⟩ : Fin n)]
  · refine Finset.sum_congr rfl fun a _ => ?_
    have : (n - 1) + 1 = n := by omega
    simp [this]
  · intro k _ hk
    refine Finset.sum_eq_zero fun a _ => ?_
    have : ¬ (k.val + 1 = n) := fun h => hk (Fin.ext (by simp; omega))
    simp [this]
  · simp

theorem coupling_row_pos (P : PathSample W n) (ψ₂ : Fin 2 × Fin W → ℂ)
    (hfar : ∀ c, ψ₂ (1, c) = 0) (i : Fin n) (hi : 1 ≤ i.val) (a : Fin W) :
    (pathPortCoupling P *ᵥ ψ₂) (i, a) = 0 := by
  simp only [mulVec, dotProduct, pathPortCoupling, Fintype.sum_prod_type, Fin.sum_univ_two]
  have h0 : ¬ i.val = 0 := by omega
  simp [h0, hfar]

theorem coupling_row_zero (P : PathSample W n) (hn : 0 < n) (ψ₂ : Fin 2 × Fin W → ℂ)
    (hfar : ∀ c, ψ₂ (1, c) = 0) (a : Fin W) :
    (pathPortCoupling P *ᵥ ψ₂) (⟨0, hn⟩, a) = (P.2.2 0 *ᵥ fun c => ψ₂ (0, c)) a := by
  simp only [mulVec, dotProduct, pathPortCoupling, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp [hfar]

theorem interior_row (P : PathSample W n) (ψ₁ : Fin n × Fin W → ℂ) (i : Fin n) (hi : 1 ≤ i.val)
    (hzero : ∀ k : Fin n, i.val ≤ k.val → ∀ c, ψ₁ (k, c) = 0) (a : Fin W) :
    (pathMatrix P *ᵥ ψ₁) (i, a) =
      ((P.2.1 ⟨i.val - 1, by omega⟩)ᴴ *ᵥ fun c => ψ₁ (⟨i.val - 1, by omega⟩, c)) a := by
  simp only [mulVec, dotProduct, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (⟨i.val - 1, by omega⟩ : Fin n)]
  · refine Finset.sum_congr rfl fun c _ => ?_
    have h1 : ¬ i = (⟨i.val - 1, by omega⟩ : Fin n) := fun h => by
      have := congrArg Fin.val h; simp at this; omega
    have h2 : ¬ i.val + 1 = i.val - 1 := by omega
    have h3 : i.val - 1 + 1 = i.val := by omega
    simp [pathMatrix, h1, h2, h3]
  · intro k _ hk
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hki : i.val ≤ k.val
    · simp [hzero k hki c]
    · have hk' : k.val ≠ i.val - 1 := fun h => hk (Fin.ext h)
      have e1 : ¬ i = k := fun h => hki (h ▸ le_rfl)
      have e2 : ¬ i.val + 1 = k.val := by omega
      have e3 : ¬ k.val + 1 = i.val := by omega
      simp [pathMatrix, e1, e2, e3]
  · simp

/-- Kernel of an invertible matrix. -/
theorem eq_zero_of_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : IsUnit A.det) {v : ι → ℂ} (h : A *ᵥ v = 0) : v = 0 := by
  have := congrArg (fun w => A⁻¹ *ᵥ w) h
  simpa [mulVec_mulVec, nonsing_inv_mul _ hA] using this

theorem propagate (E : ℝ) (z : ℂ) (P : PathSample W n) (hn : 0 < n)
    (hint : ∀ i, IsUnit (P.2.1 i).det) (hport : ∀ q, IsUnit (P.2.2 q).det)
    (ψ e : FullSite W n → ℂ) (h : fullM E z P *ᵥ ψ = e) (he1 : ∀ x, e (Sum.inl x) = 0)
    (he2 : ∀ c, e (Sum.inr (1, c)) = 0) (hfar : ∀ c, ψ (Sum.inr (1, c)) = 0) :
    (∀ x, ψ (Sum.inl x) = 0) ∧ ∀ c, ψ (Sum.inr (0, c)) = 0 := by
  set ψ₁ : Fin n × Fin W → ℂ := ψ ∘ Sum.inl with hψ₁
  set ψ₂ : Fin 2 × Fin W → ℂ := ψ ∘ Sum.inr with hψ₂
  have hfar' : ∀ c, ψ₂ (1, c) = 0 := hfar
  have hrow1 : ∀ x, ((pathMatrix P - (E : ℂ) • 1) *ᵥ ψ₁) x + (pathPortCoupling P *ᵥ ψ₂) x = 0 := by
    intro x
    have := congrFun h (Sum.inl x)
    rw [fullM, fromBlocks_mulVec] at this
    simpa [he1] using this
  have hrow2 : ∀ q, ((pathPortCoupling P)ᴴ *ᵥ ψ₁) q + ((z • 1 : Matrix _ _ ℂ) *ᵥ ψ₂) q =
      e (Sum.inr q) := by
    intro q
    have := congrFun h (Sum.inr q)
    rw [fullM, fromBlocks_mulVec] at this
    simpa using this
  -- far port row
  have hlast : ∀ c, ψ₁ (⟨n - 1, by omega⟩, c) = 0 := by
    have hv : (P.2.2 1)ᴴ *ᵥ (fun a => ψ₁ (⟨n - 1, by omega⟩, a)) = 0 := by
      funext c
      have := hrow2 (1, c)
      rw [far_row P hn, he2] at this
      simpa [smul_mulVec, hfar'] using this
    have hu : IsUnit (P.2.2 1)ᴴ.det := by rw [det_conjTranspose]; exact (hport 1).star
    exact congrFun (eq_zero_of_mulVec hu hv)
  -- downward propagation
  have hind : ∀ m, m < n → ∀ k : Fin n, n - 1 - m ≤ k.val → ∀ c, ψ₁ (k, c) = 0 := by
    intro m
    induction m with
    | zero =>
      intro _ k hk c
      have : k = ⟨n - 1, by omega⟩ := Fin.ext (by have := k.isLt; simp; omega)
      rw [this]; exact hlast c
    | succ m ih =>
      intro hm k hk c
      have hprev := ih (by omega)
      set i : Fin n := ⟨n - 1 - m, by omega⟩ with hi
      have hi1 : 1 ≤ i.val := by simp [hi]; omega
      have hz : ∀ k : Fin n, i.val ≤ k.val → ∀ c, ψ₁ (k, c) = 0 := fun k hk => hprev k hk
      have hv : (P.2.1 ⟨i.val - 1, by omega⟩)ᴴ *ᵥ
          (fun c => ψ₁ (⟨i.val - 1, by omega⟩, c)) = 0 := by
        funext a
        have := hrow1 (i, a)
        rw [sub_mulVec, Pi.sub_apply, interior_row P ψ₁ i hi1 hz,
          coupling_row_pos P ψ₂ hfar' i hi1] at this
        simpa [smul_mulVec, hz i le_rfl] using this
      have hu : IsUnit (P.2.1 ⟨i.val - 1, by omega⟩)ᴴ.det := by
        rw [det_conjTranspose]; exact (hint _).star
      have hzero := congrFun (eq_zero_of_mulVec hu hv)
      by_cases hk' : k.val = i.val - 1
      · have : k = ⟨i.val - 1, by omega⟩ := Fin.ext hk'
        rw [this]; exact hzero c
      · exact hz k (by simp [hi] at hk' ⊢; omega) c
  have hall : ∀ x, ψ₁ x = 0 := fun x => hind (n - 1) (by omega) x.1 (by omega) x.2
  refine ⟨hall, fun c => ?_⟩
  have hv : P.2.2 0 *ᵥ (fun c => ψ₂ (0, c)) = 0 := by
    funext a
    have := hrow1 (⟨0, hn⟩, a)
    have h0 : ψ₁ = 0 := funext hall
    rw [coupling_row_zero P hn ψ₂ hfar', h0] at this
    simpa using this
  exact congrFun (eq_zero_of_mulVec (hport 0) hv) c

end Rows

/-!
## 3. The full matrix with matched leads
-/

section Full

variable {W n : ℕ}

theorem fullM_sub_conj (E : ℝ) (z : ℂ) (P : PathSample W n) (hH : (pathMatrix P).IsHermitian) :
    fullM E z P - (fullM E z P)ᴴ = fromBlocks 0 0 0 ((z - star z) • 1) := by
  have hA : (pathMatrix P - (E : ℂ) • 1)ᴴ = pathMatrix P - (E : ℂ) • 1 := by
    rw [conjTranspose_sub, hH.eq, conjTranspose_smul, conjTranspose_one, Complex.star_def,
      Complex.conj_ofReal]
  rw [fullM, fromBlocks_conjTranspose, hA, conjTranspose_conjTranspose, conjTranspose_smul,
    conjTranspose_one, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add, add_neg_cancel,
    add_neg_cancel, add_neg_cancel, ← sub_eq_add_neg, sub_smul]

theorem ports_zero (E : ℝ) (z : ℂ) (hz : 0 < z.im) (P : PathSample W n)
    (hH : (pathMatrix P).IsHermitian) (ψ : FullSite W n → ℂ) (h : fullM E z P *ᵥ ψ = 0) :
    ∀ q, ψ (Sum.inr q) = 0 := by
  have h1 : star ψ ⬝ᵥ ((fullM E z P - (fullM E z P)ᴴ) *ᵥ ψ) = 0 := by
    rw [sub_mulVec, dotProduct_sub, dot_conjTranspose_mulVec, h, dotProduct_zero, star_zero,
      sub_zero]
  rw [fullM_sub_conj E z P hH, fromBlocks_mulVec] at h1
  simp only [zero_mulVec, add_zero, zero_add, smul_mulVec, one_mulVec] at h1
  rw [dotProduct, Fintype.sum_sum_type] at h1
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
    zero_add, Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.star_apply] at h1
  have hs : z - star z ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp at this; linarith
  have hsum : ∑ q, star (ψ (Sum.inr q)) * ψ (Sum.inr q) = 0 := by
    have : ∑ q, star (ψ (Sum.inr q)) * ((z - star z) * ψ (Sum.inr q)) =
        (z - star z) * ∑ q, star (ψ (Sum.inr q)) * ψ (Sum.inr q) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun q _ => by ring
    rw [this] at h1
    exact (mul_eq_zero.mp h1).resolve_left hs
  have hre : ∑ q, Complex.normSq (ψ (Sum.inr q)) = 0 := by
    have := congrArg Complex.re hsum
    simpa [Complex.star_def, Complex.mul_re, Complex.normSq_apply, ← sq] using this
  intro q
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun q _ => Complex.normSq_nonneg _)).mp hre q
    (Finset.mem_univ _)
  exact Complex.normSq_eq_zero.mp this

end Full

/-!
## 4. Almost-sure Hermitian blocks and invertible bonds
-/

/-- Entry polynomial of a Ginibre matrix in its real coordinates. -/
noncomputable def ginPoly (W : ℕ) : Matrix (Fin W) (Fin W) (MvPolynomial (Fin W × Fin W × Fin 2) ℂ) :=
  fun x y => MvPolynomial.X (x, y, 0) + MvPolynomial.X (x, y, 1) * MvPolynomial.C Complex.I

theorem eval_det_ginPoly (W : ℕ) (r : Fin W × Fin W × Fin 2 → ℝ) :
    MvPolynomial.eval (fun i => (r i : ℂ)) (ginPoly W).det =
      (BlockBand.Layers.ginibreAssemble (ι := Fin W) (κ := Fin W) r).det := by
  rw [RingHom.map_det]
  congr 1
  ext x y
  simp [ginPoly, BlockBand.Layers.ginibreAssemble]

theorem ae_isUnit_det_ginibre (W : ℕ) {t : ℝ≥0} (ht : t ≠ 0) :
    ∀ᵐ B ∂ginibreMeasure (Fin W) (Fin W) t, IsUnit B.det := by
  have hS : MeasurableSet {B : Matrix (Fin W) (Fin W) ℂ | B.det = 0} :=
    measurableSet_eq_fun (continuous_id.matrix_det).measurable measurable_const
  rw [BlockBand.Layers.ginibreMeasure_eq_map, ae_iff]
  simp only [isUnit_iff_ne_zero, not_not]
  rw [Measure.map_apply BlockBand.Layers.measurable_ginibreAssemble hS]
  set Q := BlockBand.Parameters.mvPolynomialNormSq (ginPoly W).det
  have hQx : ∀ r, MvPolynomial.eval r Q =
      Complex.normSq (BlockBand.Layers.ginibreAssemble (ι := Fin W) (κ := Fin W) r).det := by
    intro r
    rw [BlockBand.Parameters.eval_mvPolynomialNormSq, eval_det_ginPoly]
  have hQ : Q ≠ 0 := by
    intro h0
    have h := hQx (fun i => if i.1 = i.2.1 ∧ i.2.2 = 0 then 1 else 0)
    have hone : BlockBand.Layers.ginibreAssemble (ι := Fin W) (κ := Fin W)
        (fun i => if i.1 = i.2.1 ∧ i.2.2 = 0 then 1 else 0) = 1 := by
      ext x y
      by_cases hxy : x = y
      · subst hxy; simp [BlockBand.Layers.ginibreAssemble]
      · simp [BlockBand.Layers.ginibreAssemble, hxy]
    rw [hone, det_one, h0, map_zero] at h
    simp at h
  have hnull := BlockBand.Parameters.volume_mvPolynomial_zeroSet_fintype Q hQ
  have hv : t / 2 ≠ 0 := by simpa using ht
  have hac := BlockBand.Parameters.pi_absolutelyContinuous_volume
    (fun _ : Fin W × Fin W × Fin 2 => gaussianReal 0 (t / 2))
    (fun _ => gaussianReal_absolutelyContinuous 0 hv)
  apply hac
  convert hnull using 2
  ext r
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, hQx, Complex.normSq_eq_zero]

theorem ae_isHermitian_gue (W : ℕ) (t : ℝ≥0) :
    ∀ᵐ A ∂gueMeasure (Fin W) t, A.IsHermitian := by
  have hS : MeasurableSet {A : Matrix (Fin W) (Fin W) ℂ | A.IsHermitian} :=
    (isClosed_eq (by fun_prop : Continuous (fun A : Matrix (Fin W) (Fin W) ℂ => Aᴴ))
      continuous_id).measurableSet
  rw [BlockBand.Layers.gueMeasure_eq_map, ae_map_iff
    (BlockBand.Layers.measurable_gueOfCoords W t).aemeasurable hS]
  exact Filter.Eventually.of_forall fun r => BlockBand.Layers.gueOfCoords_isHermitian W t r

theorem ae_growth_good (W : ℕ) {b : ℝ} (hb0 : 0 < b) :
    ∀ᵐ ω ∂growthPathLaw W b, (∀ k, (ω.1 k).IsHermitian) ∧ ∀ k, IsUnit (ω.2 k).det := by
  rcases Nat.eq_zero_or_pos W with rfl | hW
  · refine Filter.Eventually.of_forall fun ω => ⟨fun k => ?_, fun k => ?_⟩
    · ext i; exact i.elim0
    · rw [Matrix.det_isEmpty]; exact isUnit_one
  have := fun t => BlockBand.Layers.isProbabilityMeasure_gueMeasure W t
  have ht : Real.toNNReal (b / W) ≠ 0 :=
    (Real.toNNReal_pos.mpr (div_pos hb0 (by exact_mod_cast hW))).ne'
  set μ := Measure.infinitePi fun _ : ℕ => gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W))
  set ν := Measure.infinitePi fun _ : ℕ =>
    ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))
  have h1 : ∀ᵐ ω ∂growthPathLaw W b, ∀ k, (ω.1 k).IsHermitian := by
    refine ae_all_iff.mpr fun k => ?_
    have h := (measurePreserving_eval_infinitePi (fun _ : ℕ =>
      gueMeasure (Fin W) (Real.toNNReal ((1 - 2 * b) / W))) k).comp
      (measurePreserving_fst (μ := μ) (ν := ν))
    exact h.quasiMeasurePreserving.ae (ae_isHermitian_gue W _)
  have h2 : ∀ᵐ ω ∂growthPathLaw W b, ∀ k, IsUnit (ω.2 k).det := by
    refine ae_all_iff.mpr fun k => ?_
    have h := (measurePreserving_eval_infinitePi (fun _ : ℕ =>
      ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))) k).comp
      (measurePreserving_snd (μ := μ) (ν := ν))
    exact h.quasiMeasurePreserving.ae (ae_isUnit_det_ginibre W ht)
  filter_upwards [h1, h2] with ω hω1 hω2
  exact ⟨hω1, hω2⟩

end NegativeClockScattering

open NegativeClockScattering

/-- `η = Im z_∂ = (1-b)√(4-E²)/2 > 0` for `b < 1` and `|E| < 2`. -/
theorem negativeClock_etaZ_pos {b E : ℝ} (hb1 : b < 1) (hE0 : -2 < E) (hE1 : E < 2) :
    0 < etaZ b E := by
  have h4 : 0 < 4 - E ^ 2 := by nlinarith
  set s := Real.sqrt (4 - E ^ 2) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr h4
  have hss : s ^ 2 = 4 - E ^ 2 := Real.sq_sqrt h4.le
  have hn : Complex.normSq (matchedA E) = 1 := by
    rw [Complex.normSq_apply]; simp only [matchedA]; nlinarith
  unfold etaZ boundaryZ
  rw [Complex.add_im, Complex.inv_im, hn, Complex.mul_im]
  simp only [matchedA, Complex.ofReal_re, Complex.ofReal_im]
  rw [← hs]
  nlinarith

/-- **Deterministic core** (proof of the phase-resolution lemma). For a
growth sample `ω` whose blocks `ω.1 k` are all Hermitian and whose bonds `ω.2 k` are all
invertible, with `η = Im z_∂ > 0` and path length `n ≥ 1`: the scattering matrix
`𝕊 = I - 2iηℝ` of the path of length `n` satisfies `𝕊𝕊ᴴ = I`, and its transmission block
`t = 𝕊₁₀` (near incoming → far outgoing) is invertible. -/
theorem negativeClock_scattering_of_bonds {b E : ℝ} {W n : ℕ} (hn : 0 < n)
    (hη : 0 < etaZ b E) (ω : GrowthPath W) (hH : ∀ k, (ω.1 k).IsHermitian)
    (hB : ∀ k, IsUnit (ω.2 k).det) :
    scatteringMatrix b E W n ω * (scatteringMatrix b E W n ω)ᴴ = 1 ∧
      IsUnit (transmission (scatteringMatrix b E W n ω)).det := by
  set P := pathAt W n ω with hP
  set z := boundaryZ b E with hz
  have hzim : 0 < z.im := hη
  have hPH : (pathMatrix P).IsHermitian := pathMatrix_isHermitian P fun i => hH _
  have hint : ∀ i, IsUnit (P.2.1 i).det := fun i => by
    simp only [hP, pathAt]; rw [det_conjTranspose]; exact (hB _).star
  have hport : ∀ q, IsUnit (P.2.2 q).det := fun q => by
    fin_cases q <;> simp only [hP, pathAt] <;> simp <;> exact (hB _).ne_zero
  have hM : fullPathMatrix b E W n ω = fullM E z P := rfl
  set κ : ℂ := z - star z with hκ
  have hκs : star κ = -κ := by simp [hκ]
  have hκ2 : (((2 * etaZ b E : ℝ) : ℂ) * Complex.I) = κ := by
    rw [hκ, Complex.star_def, Complex.sub_conj]; rfl
  have hS : scatteringMatrix b E W n ω = 1 - κ • (fullM E z P)⁻¹.toBlocks₂₂ := by
    rw [scatteringMatrix, hκ2]; rfl
  have hD := fullM_sub_conj E z P hPH
  -- invertibility of `𝓜`
  have hMu : IsUnit (fullM E z P).det := by
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    obtain ⟨ψ, hψ0, hψ⟩ := exists_mulVec_eq_zero_iff.mpr h0
    have hpz := ports_zero E z hzim P hPH ψ hψ
    obtain ⟨h1, -⟩ := propagate E z P hn hint hport ψ 0 hψ (fun _ => rfl) (fun _ => rfl)
      (fun c => hpz _)
    apply hψ0
    funext x
    rcases x with x | q
    · exact h1 x
    · exact hpz q
  refine ⟨?_, ?_⟩
  · rw [hS]; exact unitary_of_skew _ κ hκs hD
  · refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    obtain ⟨u, hu0, hu⟩ := exists_mulVec_eq_zero_iff.mpr h0
    set G := (fullM E z P)⁻¹ with hG
    set e : FullSite W n → ℂ := Sum.elim 0 (fun q => if q.1 = 0 then u q.2 else 0) with he
    set ψ := G *ᵥ e with hψ
    have hMψ : fullM E z P *ᵥ ψ = e := by
      rw [hψ, mulVec_mulVec, mul_nonsing_inv _ hMu, one_mulVec]
    have hκ0 : κ ≠ 0 := by
      intro h; have := congrArg Complex.im h; simp [hκ] at this; linarith
    have hfar : ∀ c, ψ (Sum.inr (1, c)) = 0 := by
      intro c
      have ht : ∀ c, (transmission (scatteringMatrix b E W n ω) *ᵥ u) c =
          -κ * ψ (Sum.inr (1, c)) := by
        intro c
        rw [hψ, hS]
        simp only [transmission, scatteringBlock, mulVec, dotProduct, Matrix.of_apply,
          Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, toBlocks₂₂, he,
          Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, mul_zero,
          Finset.sum_const_zero, zero_add, Fintype.sum_prod_type, Fin.sum_univ_two]
        simp [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring
      have := ht c
      rw [hu, Pi.zero_apply] at this
      exact (mul_eq_zero.mp this.symm).resolve_left (neg_ne_zero.mpr hκ0)
    obtain ⟨h1, h2⟩ := propagate E z P hn hint hport ψ e hMψ (fun _ => rfl)
      (fun c => by simp [he]) hfar
    have hψ0 : ψ = 0 := by
      funext x; rcases x with x | ⟨q, c⟩
      · exact h1 x
      · fin_cases q
        · exact h2 c
        · exact hfar c
    apply hu0
    funext c
    have := congrFun hMψ (Sum.inr (0, c))
    rw [hψ0, mulVec_zero] at this
    simpa [he] using this.symm

/-- Successive block inversion then makes the finite-path transmission `t` invertible").
For `0 < b < 1/2`, `|E| < 2`, every width `W` and every path length `n ≥ 1`,
`growthPathLaw W b`-a.s. the scattering matrix `𝕊` of the path of length `n` is unitary
(`𝕊𝕊ᴴ = I`) and its transmission block `t = 𝕊₁₀` is invertible.
These are exactly the
hypotheses of `phase_resolution_average`.
-/
theorem negativeClock_ae_scattering {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) {E : ℝ}
    (hE0 : -2 < E) (hE1 : E < 2) (W n : ℕ) (hn : 0 < n) :
    ∀ᵐ ω ∂growthPathLaw W b,
      scatteringMatrix b E W n ω * (scatteringMatrix b E W n ω)ᴴ = 1 ∧
        IsUnit (transmission (scatteringMatrix b E W n ω)).det := by
  have hη := negativeClock_etaZ_pos (b := b) (by linarith) hE0 hE1
  filter_upwards [ae_growth_good W hb0] with ω hω
  exact negativeClock_scattering_of_bonds hn hη ω hω.1 hω.2

end BlockBand.Endpoints.Clock
