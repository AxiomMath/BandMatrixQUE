module
public import BlockBand.QUE.Fourier.PhysicalPairTilt
public import BlockBand.QUE.Fourier.Reduction
public import BlockBand.QUE.Haar.PhysicalBridge
/-!
# Fourier diagonalization of the physical block-test variance

Under the physical law, the variance of a block test diagonalizes over the nonzero Fourier modes
with the `1/n` baseline removed; a uniform nonzero-mode estimate then bounds every bounded block
test, and with the Haar residual `1/(W+1)` every site test (`physical_site_test_bound`).
-/
set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.QUE.Fourier
open MeasureTheory BlockBand.Model.Construction
open scoped BigOperators

/-- Complex Fourier covariance diagonalization on every finite mode set. -/
theorem physical_fourier_diagonalization (p : Parameters) (model : p.GaussianRingModel)
    (α : Fin p.N) (S : Finset (ZMod p.n)) (c : ZMod p.n → ℂ) :
    (∫ H, (∑ m ∈ S, c m * physicalMode p α m H) *
      starRingEnd ℂ (∑ m ∈ S, c m * physicalMode p α m H)
      ∂(model.law : Measure p.SiteMatrix)) =
    ∑ m ∈ S, (‖c m‖ ^ 2 : ℝ) •
      (∫ H, physicalMode p α m H * starRingEnd ℂ (physicalMode p α m H)
        ∂(model.law : Measure p.SiteMatrix)) := by
  have he (H : p.SiteMatrix) : (∑ m ∈ S, c m * physicalMode p α m H) *
      starRingEnd ℂ (∑ m ∈ S, c m * physicalMode p α m H) =
      ∑ m ∈ S, ∑ k ∈ S, (c m * starRingEnd ℂ (c k)) *
        (physicalMode p α m H * starRingEnd ℂ (physicalMode p α k H)) := by
    simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun m _ => integrable_finsetSum _ (fun k _ =>
    (integrable_physicalMode_product p model α m k).const_mul _))]
  apply Finset.sum_congr rfl
  intro m hm
  rw [integral_finsetSum _ (fun k _ => (integrable_physicalMode_product p model α m k).const_mul _)]
  simp_rw [integral_const_mul]
  rw [Finset.sum_eq_single m]
  · simp only [Complex.mul_conj', ← Complex.ofReal_pow, Complex.real_smul]
  · intro k _ hkm
    rw [physical_expected_distinct_mode_orthogonality p model α m k (Ne.symm hkm), mul_zero]
  · exact fun h => False.elim (h hm)

/-- Real Fourier variance diagonalization, with deterministic weights outside the expectation. -/
theorem physical_real_fourier_diagonalization (p : Parameters) (model : p.GaussianRingModel)
    (α : Fin p.N) (S : Finset (ZMod p.n)) (c : ZMod p.n → ℂ) :
    (∫ H, ‖∑ m ∈ S, c m * physicalMode p α m H‖ ^ 2
      ∂(model.law : Measure p.SiteMatrix)) =
    ∑ m ∈ S, ‖c m‖ ^ 2 *
      (∫ H, ‖physicalMode p α m H‖ ^ 2 ∂(model.law : Measure p.SiteMatrix)) := by
  have h := physical_fourier_diagonalization p model α S c
  simp only [Complex.mul_conj', ← Complex.ofReal_pow,
    Complex.real_smul] at h
  exact_mod_cast h
/-- Physical block tests expand in only nonzero modes, with the `1/n` baseline. -/
theorem physical_block_test_expansion_ae (p : Parameters) (model : p.GaussianRingModel)
    (α : Fin p.N) (t : ZMod p.n → ℝ) :
    ∀ᵐ H ∂(model.law : Measure p.SiteMatrix),
      ((∑ k, t k * (physicalOrderedBlockMass p H α k - (p.n : ℝ)⁻¹) : ℝ) : ℂ) =
      ∑ m ∈ Finset.univ.erase 0, coefficient (fun k => (t k : ℂ)) m * physicalMode p α m H := by
  filter_upwards [physicalOrderedBlockMass_sum_ae p model] with H hH
  have hzero : physicalMode p α 0 H = 1 := by
    unfold physicalMode
    rw [mode_zero, ← Complex.ofReal_sum, hH α]
    norm_num
  have hc : coefficient (fun k => (t k : ℂ)) 0 =
      (p.n : ℂ)⁻¹ * ∑ k, (t k : ℂ) := by
    simp only [coefficient, neg_zero, ZMod.dft_apply_zero]
  have hp := coefficient_mode_pairing (fun k => (t k : ℂ))
    (fun k => (physicalOrderedBlockMass p H α k : ℂ))
  have hs := Finset.sum_erase_add (s := Finset.univ)
    (f := fun m => coefficient (fun k => (t k : ℂ)) m * physicalMode p α m H)
    (Finset.mem_univ (0 : ZMod p.n))
  change (∑ m ∈ Finset.univ.erase 0, coefficient (fun k => (t k : ℂ)) m * physicalMode p α m H) +
    coefficient (fun k => (t k : ℂ)) 0 * physicalMode p α 0 H =
      ∑ m, coefficient (fun k => (t k : ℂ)) m * physicalMode p α m H at hs
  rw [hzero, mul_one, hc] at hs
  change (∑ m, coefficient (fun k => (t k : ℂ)) m * physicalMode p α m H) =
      ∑ k, (t k : ℂ) * (physicalOrderedBlockMass p H α k : ℂ) at hp
  rw [hp] at hs
  rw [eq_sub_of_add_eq hs]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  push_cast
  ring

/-- Variance diagonalization for a deterministic block test; the test and the Fourier weights stay
outside the expectation. -/
theorem physical_block_test_diagonalization (p : Parameters) (model : p.GaussianRingModel)
    (α : Fin p.N) (t : ZMod p.n → ℝ) :
    (∫ H, |∑ k, t k * (physicalOrderedBlockMass p H α k - (p.n : ℝ)⁻¹)| ^ 2
      ∂(model.law : Measure p.SiteMatrix)) =
    ∑ m ∈ Finset.univ.erase 0, ‖coefficient (fun k => (t k : ℂ)) m‖ ^ 2 *
      (∫ H, ‖physicalMode p α m H‖ ^ 2 ∂(model.law : Measure p.SiteMatrix)) := by
  rw [← physical_real_fourier_diagonalization]
  apply integral_congr_ae
  filter_upwards [physical_block_test_expansion_ae p model α t] with H hH
  rw [← hH, Complex.norm_real, Real.norm_eq_abs]
/-- Every deterministic bounded block test obeys the variance bound given by a uniform
nonzero-mode estimate, which is a hypothesis. -/
theorem physical_block_test_bound (p : Parameters) (model : p.GaussianRingModel)
    (α : Fin p.N) (t : ZMod p.n → ℝ) (ht : ∀ k, |t k| ≤ 1)
    (C : ℝ) (hC : 0 ≤ C)
    (hmode : ∀ m : ZMod p.n, m ≠ 0 →
      (∫ H, ‖physicalMode p α m H‖ ^ 2 ∂(model.law : Measure p.SiteMatrix)) ≤ C) :
    (∫ H, |∑ k, t k * (physicalOrderedBlockMass p H α k - (p.n : ℝ)⁻¹)| ^ 2
      ∂(model.law : Measure p.SiteMatrix)) ≤ C := by
  rw [physical_block_test_diagonalization]
  have he : (∑ m ∈ Finset.univ.erase 0, ‖coefficient (fun k => (t k : ℂ)) m‖ ^ 2) ≤ 1 := by
    calc
      _ ≤ ∑ m, ‖coefficient (fun k => (t k : ℂ)) m‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun _ _ _ => sq_nonneg _)
      _ ≤ 1 := coefficient_energy_le_one (fun k => (t k : ℂ))
        (fun k => by simpa only [Complex.norm_real, Real.norm_eq_abs] using ht k)
  calc
    _ ≤ ∑ m ∈ Finset.univ.erase 0, ‖coefficient (fun k => (t k : ℂ)) m‖ ^ 2 * C := by
      apply Finset.sum_le_sum
      intro m hm
      exact mul_le_mul_of_nonneg_left (hmode m (Finset.ne_of_mem_erase hm)) (sq_nonneg _)
    _ = (∑ m ∈ Finset.univ.erase 0, ‖coefficient (fun k => (t k : ℂ)) m‖ ^ 2) * C :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ C := by simpa using mul_le_mul_of_nonneg_right he hC

/-- Site-test reduction for the physical model: the cyclic, spectral and Haar identities supply
the law and moment inputs; the only hypothesis is a uniform nonzero-mode estimate, and the
residual is `1/(W+1)`. -/
theorem physical_site_test_bound {p : Parameters} {model : p.GaussianRingModel}
    (spectral : p.SpectralRealization model) (α : Fin p.N) (w : p.Site → ℝ)
    (hw : ∀ x, |w x| ≤ 1) (C : ℝ) (hC : 0 ≤ C)
    (hmode : ∀ m : ZMod p.n, m ≠ 0 →
      (∫ H, ‖physicalMode p α m H‖ ^ 2 ∂(model.law : Measure p.SiteMatrix)) ≤ C) :
    spectral.queStatistic α w ≤ C + 1 / ((p.W : ℝ) + 1) := by
  have hc : (∫ H, |∑ b : ZMod p.n,
      BlockBand.Foundations.FiniteBlock.average w b *
        (BlockBand.QUE.Haar.physicalBlockMass spectral α H b - (p.n : ℝ)⁻¹)| ^ 2
      ∂(model.law : Measure p.SiteMatrix)) =
      ∫ H, |∑ b : ZMod p.n, BlockBand.Foundations.FiniteBlock.average w b *
        (physicalOrderedBlockMass p H α b - (p.n : ℝ)⁻¹)| ^ 2
      ∂(model.law : Measure p.SiteMatrix) := by
    apply integral_congr_ae
    filter_upwards [BlockBand.QUE.Haar.spectral_blockMass_eq_canonical_ae spectral] with H hH
    have he (b : ZMod p.n) : BlockBand.QUE.Haar.physicalBlockMass spectral α H b =
        physicalOrderedBlockMass p H α b := hH α b
    simp_rw [he]
  have hb := physical_block_test_bound p model α
    (BlockBand.Foundations.FiniteBlock.average w)
    (BlockBand.QUE.average_abs_le_one w hw) C hC hmode
  exact (BlockBand.QUE.Haar.physical_haar_bound spectral α w hw).trans
    (by rw [hc]; exact add_le_add hb le_rfl)
end BlockBand.QUE.Fourier
