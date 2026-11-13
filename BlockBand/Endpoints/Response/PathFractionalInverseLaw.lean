module

public import BlockBand.Endpoints.Response.PathFractionalInverseWegner
public import BlockBand.Endpoints.Response.PassDerivative
public import BlockBand.Endpoints.Sine.CrossingSine

/-!
# The path law as a block model

This file writes the path law `growthPathLaw W b` as an instance of the block model of the
Wegner estimate and draws the consequences.

* `pathMatrix_pathAt_eq`: `H_path = ⊕_i A_{n-1-i} + (bond part)`, the bond part
  `pathBondPart W n (bonds)` and the port coupling depending on the bonds only.
* `path_lintegral_norm_inv_rpow_le`: `E ‖(D(bonds) + ⊕A + iδ)⁻¹‖^s ≤ (C/√c · nW)^s/(1-s)`
  under `growthPathLaw W b`, uniformly in `D`, `δ ∈ ℝ`, `n`, `W ≥ 1`.
* `path_ae_isUnit`: `D(bonds) + ⊕A` is almost surely invertible (the eigenvalue count on the
  degenerate interval `[0, 0]`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open Matrix MeasureTheory ProbabilityTheory Complex Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Inputs BlockBand.Foundations.Spectral
open scoped NNReal ComplexOrder Matrix.Norms.L2Operator

/-- Blocks of the path of length `n` in path order. -/
noncomputable def pathBlocks (W n : ℕ) (ω : GrowthPath W) : Fin n → Matrix (Fin W) (Fin W) ℂ :=
  fun i => ω.1 (n - 1 - i.val)

/-- The bond part of the path matrix (zero diagonal blocks); a function of the bonds only. -/
noncomputable def pathBondPart (W n : ℕ) (B : ℕ → Matrix (Fin W) (Fin W) ℂ) :
    Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ :=
  pathMatrix (pathAt W n (0, B))

theorem pathMatrix_pathAt_eq (W n : ℕ) (ω : GrowthPath W) :
    pathMatrix (pathAt W n ω) = blockSumOf (pathBlocks W n ω) + pathBondPart W n ω.2 := by
  ext x y
  simp only [pathMatrix, pathAt, pathBondPart, blockSumOf, pathBlocks, Matrix.add_apply]
  split_ifs <;> simp

theorem pathPortCoupling_pathAt_eq (W n : ℕ) (ω : GrowthPath W) :
    pathPortCoupling (pathAt W n ω) = pathPortCoupling (pathAt W n (0, ω.2)) := rfl

theorem pathBondPart_isHermitian (W n : ℕ) (B : ℕ → Matrix (Fin W) (Fin W) ℂ) :
    (pathBondPart W n B).IsHermitian :=
  pathMatrix_isHermitian fun i => by simp [pathAt, IsHermitian]

instance pfi_isProbabilityMeasure_gue (ι : Type*) [Fintype ι] (t : ℝ≥0) :
    IsProbabilityMeasure (BlockBand.Internal.Contracts.CoareaPalm.gueMeasure ι t) :=
  passDeriv_isProbabilityMeasure_gue ι t

instance pfi_isProbabilityMeasure_ginibre (ι κ : Type*) [Fintype ι] [Fintype κ] (t : ℝ≥0) :
    IsProbabilityMeasure (ginibreMeasure ι κ t) :=
  passDeriv_isProbabilityMeasure_ginibre ι κ t

/-- Independence transfers along the first factor of a product of probability measures. -/
theorem iIndepFun_comp_fst {ι : Type*} [Fintype ι] {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁]
    [MeasurableSpace Ω₂] {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    {Y : ∀ i, Ω₁ → β i} (hY : ∀ i, Measurable (Y i)) (h : iIndepFun Y μ₁) :
    iIndepFun (fun i ω => Y i ω.1) (μ₁.prod μ₂) := by
  refine (iIndepFun_iff_map_fun_eq_pi_map (f := fun i (ω : Ω₁ × Ω₂) => Y i ω.1)
    (fun i => ((hY i).comp measurable_fst).aemeasurable)).2 ?_
  have hfst : (μ₁.prod μ₂).map Prod.fst = μ₁ := measurePreserving_fst.map_eq
  have e1 : (μ₁.prod μ₂).map (fun ω i => Y i ω.1) = μ₁.map (fun a i => Y i a) := by
    conv_rhs => rw [← hfst]
    rw [Measure.map_map (Measurable.of_eval hY) measurable_fst]
    rfl
  have e2 : ∀ i, (μ₁.prod μ₂).map (fun ω => Y i ω.1) = μ₁.map (Y i) := fun i => by
    conv_rhs => rw [← hfst]
    rw [Measure.map_map (hY i) measurable_fst]
    rfl
  rw [e1, h.map_fun_eq_pi_map (fun i => (hY i).aemeasurable)]
  simp_rw [e2]

/-- The Hermitianized `GUE` block, `(A + A*)/2` (equal to `A` almost surely). -/
noncomputable def hermBlock {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ) : Matrix (Fin W) (Fin W) ℂ :=
  (BlockModelCount.toHerm A).1

theorem measurable_hermBlock {W : ℕ} : Measurable (hermBlock (W := W)) :=
  measurable_subtype_coe.comp BlockModelCount.measurable_toHerm

theorem hermBlock_isHermitian {W : ℕ} (A : Matrix (Fin W) (Fin W) ℂ) :
    (hermBlock A).IsHermitian := (BlockModelCount.toHerm A).2

theorem gueMeasure_map_hermBlock (W : ℕ) (t : ℝ≥0) :
    (BlockBand.Internal.Contracts.CoareaPalm.gueMeasure (Fin W) t).map hermBlock =
      BlockBand.Internal.Contracts.CoareaPalm.gueMeasure (Fin W) t := by
  have h : hermBlock =ᵐ[BlockBand.Internal.Contracts.CoareaPalm.gueMeasure (Fin W) t] id := by
    filter_upwards [ae_gueMeasure_isHermitian (ι := Fin W) t] with A hA
    exact BlockModelCount.toHerm_of_isHermitian hA
  rw [Measure.map_congr h, Measure.map_id]

/-- **The path block model.** Under the path law `growthPathLaw W b`, the `n` path blocks
(Hermitianized) and an arbitrary measurable Hermitian deformation `D(bonds)` form a
`BlockModel`.
-/
noncomputable def pathBlockModel (W n : ℕ) (b : ℝ)
    (D : (ℕ → Matrix (Fin W) (Fin W) ℂ) → Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ)
    (hDm : Measurable D) (hDh : ∀ B, (D B).IsHermitian) : BlockModel n W where
  Ω := GrowthPath W
  P := growthPathLaw W b
  prob := passDeriv_isProbabilityMeasure_growthPathLaw W b
  A := fun ω i => hermBlock (pathBlocks W n ω i)
  D := fun ω => D ω.2
  Y := fun _ => 0
  measurable_A := by
    exact Measurable.of_eval fun i => measurable_hermBlock.comp
      ((measurable_pi_apply _).comp measurable_fst)
  measurable_D := hDm.comp measurable_snd
  measurable_Y := measurable_const
  hermitian_A := fun ω i => hermBlock_isHermitian _
  hermitian_D := fun ω => hDh ω.2
  posSemidef_Y := fun _ => PosSemidef.zero

theorem gueMeasure_eq_gueMatrixLaw (hGUE : GUELawBridge) (W : ℕ) (t : ℝ≥0) :
    BlockBand.Internal.Contracts.CoareaPalm.gueMeasure (Fin W) t = gueMatrixLaw W t := by
  have := hGUE (Fin W) W (Equiv.refl _) t
  rwa [show (Matrix.reindex (Equiv.refl (Fin W)) (Equiv.refl (Fin W)) :
    Matrix (Fin W) (Fin W) ℂ → Matrix (Fin W) (Fin W) ℂ) = id from
      funext fun A => reindex_refl_refl A, Measure.map_id] at this

theorem hasLaw_pathBlock (hGUE : GUELawBridge) (W n : ℕ) (b : ℝ) (j : Fin n) :
    HasLaw (fun ω : GrowthPath W => hermBlock (pathBlocks W n ω j))
      (gueMatrixLaw W (Real.toNNReal ((1 - 2 * b) / W))) (growthPathLaw W b) := by
  have hm : Measurable (fun ω : GrowthPath W => hermBlock (pathBlocks W n ω j)) :=
    measurable_hermBlock.comp ((measurable_pi_apply _).comp measurable_fst)
  refine ⟨hm.aemeasurable, ?_⟩
  have e : (fun ω : GrowthPath W => hermBlock (pathBlocks W n ω j)) =
      hermBlock ∘ (fun a : ℕ → Matrix (Fin W) (Fin W) ℂ => a (n - 1 - j.val)) ∘ Prod.fst := rfl
  rw [e, growthPathLaw,
    ← Measure.map_map measurable_hermBlock ((measurable_pi_apply _).comp measurable_fst),
    ← Measure.map_map (measurable_pi_apply _) measurable_fst, measurePreserving_fst.map_eq,
    Measure.infinitePi_map_eval, gueMeasure_map_hermBlock, gueMeasure_eq_gueMatrixLaw hGUE]

theorem iIndepFun_pathBlocks (W n : ℕ) (b : ℝ) :
    iIndepFun (fun (j : Fin n) (ω : GrowthPath W) => hermBlock (pathBlocks W n ω j))
      (growthPathLaw W b) := by
  have h0 : iIndepFun (fun (k : ℕ) (a : ℕ → Matrix (Fin W) (Fin W) ℂ) => hermBlock (a k))
      (Measure.infinitePi fun _ : ℕ =>
        BlockBand.Internal.Contracts.CoareaPalm.gueMeasure (Fin W)
          (Real.toNNReal ((1 - 2 * b) / W))) :=
    iIndepFun_infinitePi (X := fun _ A => hermBlock A) (fun _ => measurable_hermBlock)
  have h1 : iIndepFun (fun (j : Fin n) (a : ℕ → Matrix (Fin W) (Fin W) ℂ) =>
      hermBlock (a (n - 1 - j.val)))
      (Measure.infinitePi fun _ : ℕ =>
        BlockBand.Internal.Contracts.CoareaPalm.gueMeasure (Fin W)
          (Real.toNNReal ((1 - 2 * b) / W))) := by
    refine h0.precomp (g := fun j : Fin n => n - 1 - j.val) ?_
    intro i j hij
    have := i.isLt; have := j.isLt
    exact Fin.ext (by simp only at hij; omega)
  rw [growthPathLaw]
  exact iIndepFun_comp_fst (μ₂ := Measure.infinitePi fun _ : ℕ =>
    ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W)))
    (Y := fun (j : Fin n) (a : ℕ → Matrix (Fin W) (Fin W) ℂ) => hermBlock (a (n - 1 - j.val)))
    (fun j => measurable_hermBlock.comp (measurable_pi_apply _)) h1

theorem indepFun_bonds_pathBlocks (W n : ℕ) (b : ℝ) {β : Type*} [MeasurableSpace β]
    {F : (ℕ → Matrix (Fin W) (Fin W) ℂ) → β} (hF : Measurable F) :
    IndepFun (fun ω : GrowthPath W => F ω.2)
      (fun ω (i : Fin n) => hermBlock (pathBlocks W n ω i)) (growthPathLaw W b) := by
  rw [growthPathLaw]
  exact (indepFun_prod (X := fun (a : ℕ → Matrix (Fin W) (Fin W) ℂ) (i : Fin n) =>
    hermBlock (a (n - 1 - i.val))) (Y := F)
    (Measurable.of_eval fun i => measurable_hermBlock.comp (measurable_pi_apply _)) hF).symm

theorem pathBlockModel_isIndependent (hGUE : GUELawBridge) {W n : ℕ} (b : ℝ)
    (D : (ℕ → Matrix (Fin W) (Fin W) ℂ) → Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ)
    (hDm : Measurable D) (hDh : ∀ B, (D B).IsHermitian) :
    (pathBlockModel W n b D hDm hDh).IsIndependent (1 - 2 * b) :=
  ⟨fun j => hasLaw_pathBlock hGUE W n b j, iIndepFun_pathBlocks W n b,
    indepFun_bonds_pathBlocks W n b (F := fun B => (D B, (0 : Matrix (Fin n × Fin W)
      (Fin n × Fin W) ℂ))) (hDm.prodMk measurable_const)⟩

/-!
### Consequences of the Wegner estimate under the path law
-/

theorem blockModel_H_pathBlockModel {W n : ℕ} (b : ℝ)
    (D : (ℕ → Matrix (Fin W) (Fin W) ℂ) → Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ)
    (hDm : Measurable D) (hDh : ∀ B, (D B).IsHermitian) (ω : GrowthPath W) :
    (pathBlockModel W n b D hDm hDh).H ω =
      D ω.2 + blockSumOf (fun i => hermBlock (pathBlocks W n ω i)) := rfl

theorem ae_hermBlock_pathBlocks (W n : ℕ) (b : ℝ) :
    ∀ᵐ ω ∂growthPathLaw W b, (fun i => hermBlock (pathBlocks W n ω i)) = pathBlocks W n ω := by
  filter_upwards [ae_growthPath_isHermitian W b] with ω hω
  funext i
  exact BlockModelCount.toHerm_of_isHermitian (hω _)

/-- Fractional inverse moment under the path law. -/
theorem path_lintegral_norm_inv_rpow_le (hCount : ConditionalBlockGUECount)
    (hGUE : GUELawBridge) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W n : ℕ), 0 < W → ∀ b : ℝ, b < 1 / 2 →
      ∀ (D : (ℕ → Matrix (Fin W) (Fin W) ℂ) → Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ),
        Measurable D → (∀ B, (D B).IsHermitian) → ∀ (δ s : ℝ), 0 < s → s < 1 →
        ∫⁻ ω, ENNReal.ofReal (‖(D ω.2 + blockSumOf (pathBlocks W n ω) +
            ((δ : ℂ) * I) • 1)⁻¹‖ ^ s) ∂growthPathLaw W b ≤
          ENNReal.ofReal ((C / Real.sqrt (1 - 2 * b) * ((n * W : ℕ) : ℝ)) ^ s / (1 - s)) := by
  obtain ⟨C, hC, hmain⟩ := blockModel_lintegral_norm_inv_rpow_le hCount
  refine ⟨C, hC, fun W n hW b hb D hDm hDh δ s hs0 hs1 => ?_⟩
  have h := hmain n W hW (1 - 2 * b) (by linarith) (pathBlockModel W n b D hDm hDh)
    (pathBlockModel_isIndependent hGUE b D hDm hDh) δ s hs0 hs1
  refine le_of_eq_of_le (lintegral_congr_ae ?_) h
  filter_upwards [ae_hermBlock_pathBlocks W n b] with ω hω
  rw [blockModel_H_pathBlockModel, hω]

/-- An eigenvalue in `I` is counted by the increasing-eigenvalue count. -/
theorem one_le_count_of_mem {k W : ℕ} {H : Matrix (Fin k × Fin W) (Fin k × Fin W) ℂ}
    (hH : H.IsHermitian) {I : Set ℝ} [DecidablePred (· ∈ I)] {j : Fin k × Fin W}
    (hj : hH.eigenvalues j ∈ I) :
    1 ≤ (Finset.univ.filter fun i => increasingEigenvalue hH i ∈ I).card := by
  rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  push Not
  refine ⟨((Fintype.equivOfCardEq (Fintype.card_fin _)).symm j).rev, Finset.mem_univ _, ?_⟩
  have he : increasingEigenvalue hH ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm j).rev =
      hH.eigenvalues j := by
    simp [increasingEigenvalue, Matrix.IsHermitian.eigenvalues]
  rw [he]
  exact hj

/-- Almost-sure invertibility at real energy: `D(bonds) + ⊕A` is almost surely invertible
(the eigenvalue count of the degenerate interval `[0, 0]` has expectation `0`). -/
theorem path_ae_isUnit (hCount : ConditionalBlockGUECount) (hGUE : GUELawBridge) {W n : ℕ}
    (hW : 0 < W) {b : ℝ} (hb : b < 1 / 2)
    (D : (ℕ → Matrix (Fin W) (Fin W) ℂ) → Matrix (Fin n × Fin W) (Fin n × Fin W) ℂ)
    (hDm : Measurable D) (hDh : ∀ B, (D B).IsHermitian) :
    ∀ᵐ ω ∂growthPathLaw W b, IsUnit (D ω.2 + blockSumOf (pathBlocks W n ω)).det := by
  obtain ⟨C, hC, hmain⟩ := BlockModelCount.blockModel_count_le hCount
  set M := pathBlockModel W n b D hDm hDh
  obtain ⟨hint, hle⟩ := hmain n W hW (1 - 2 * b) (by linarith) M
    (pathBlockModel_isIndependent hGUE b D hDm hDh) 0 0 le_rfl
  rw [sub_self, mul_zero] at hle
  have hnn : 0 ≤ᵐ[M.P] fun w => ((Finset.univ.filter fun i =>
      increasingEigenvalue (BlockModelCount.isHermitian_H M w) i ∈ Icc (0 : ℝ) 0).card : ℝ) :=
    ae_of_all _ fun w => Nat.cast_nonneg _
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hnn hint).1
    (le_antisymm hle (integral_nonneg_of_ae hnn))
  have hzero' : ∀ᵐ ω ∂growthPathLaw W b, IsUnit (M.H ω).det := by
    filter_upwards [hzero] with w hw
    have hw' : ((Finset.univ.filter fun i =>
        increasingEigenvalue (BlockModelCount.isHermitian_H M w) i ∈ Icc (0 : ℝ) 0).card) = 0 := by
      have : (((Finset.univ.filter fun i =>
          increasingEigenvalue (BlockModelCount.isHermitian_H M w) i ∈ Icc (0 : ℝ) 0).card : ℕ)
          : ℝ) = 0 := by simpa using hw
      exact_mod_cast this
    rw [isUnit_iff_ne_zero, (BlockModelCount.isHermitian_H M w).det_eq_prod_eigenvalues,
      Finset.prod_ne_zero_iff]
    intro j _ h0
    have h0' : (BlockModelCount.isHermitian_H M w).eigenvalues j = 0 := by simpa using h0
    have h1 := one_le_count_of_mem (BlockModelCount.isHermitian_H M w) (I := Icc (0 : ℝ) 0)
      (j := j) (by rw [h0']; exact ⟨le_rfl, le_rfl⟩)
    omega
  filter_upwards [hzero', ae_hermBlock_pathBlocks W n b] with ω h1 h2
  change IsUnit (D ω.2 + blockSumOf (fun i => hermBlock (pathBlocks W n ω i))).det at h1
  rwa [h2] at h1

end BlockBand.Endpoints
