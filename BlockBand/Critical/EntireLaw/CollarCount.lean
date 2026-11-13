module

public import BlockBand.Critical.EntireLaw.CollarSpectral
public import BlockBand.Critical.EntireLaw.RingInvariance
public import BlockBand.Critical.EntireLaw.Statements
public import BlockBand.Critical.Collar.Density.SpectralSum
public import BlockBand.Counting.PhysicalCountingComplete

/-!
# The entire law: cyclic invariance and counting for `Tr |R|`

* `measurable_absResolvent` (via `Collar.Density.rawCfc`).
* Cyclic invariance (`lintegral_blockAbsMass_eq`, `lintegral_totalAbsMass_eq`,
  `lintegral_collarAbsMass_le`): `n E[Σ_{collar} Re|R|_xx] ≤ 3 E[Tr |R|]` (cyclic invariance
  gives `E Tr(Π f(R)) = (3/n) E Tr f(R)`; here with `≤`, valid for every `n ≥ 4`).
* Counting: `physicalSpectralSetCount_zero_eq` (the count of the counting theorem for a Hermitian
  `H` is its eigenvalue count), `integral_count_le` (`E #{λ ∈ [E-r, E+r]} ≤ (C/√c) N 2r`),
  `integral_totalAbsMass_le` (`E Tr|R| ≤ N (1 + 2(C/√c)(K+1))` at `δ = 2^{-(K+1)}`, the first
  truncated-inverse bound on the ring), `gap_of_count_eq_zero`,
  `measure_count_pos_le` (`P(𝓔^c) ≤ (C/√c) N 2δ`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.EntireLaw

open MeasureTheory Matrix Set
open BlockBand.Internal.Contracts.CoareaPalm
open scoped ENNReal

section Measurable

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem measurable_collarWeight (E δ : ℝ) : Measurable (collarWeight E δ) := by
  unfold collarWeight
  refine Measurable.ite (measurableSet_lt measurable_const
    ((measurable_id.sub_const E).abs)) ((measurable_id.sub_const E).abs.inv) measurable_const

theorem absResolvent_eq_ite (E δ : ℝ) (H : Matrix ι ι ℂ) :
    absResolvent E δ H =
      if H.IsHermitian then BlockBand.Critical.Collar.Density.rawCfc (collarWeight E δ) H
      else 0 := by
  split_ifs with hH
  · exact (BlockBand.Critical.Collar.Density.rawCfc_eq_cfc hH _).symm
  · have hH' : ¬ IsSelfAdjoint H := hH
    exact cfc_apply_of_not_predicate H hH'

omit [DecidableEq ι] in
theorem measurableSet_isHermitian : MeasurableSet {H : Matrix ι ι ℂ | H.IsHermitian} :=
  (isClosed_eq (continuous_id.matrix_conjTranspose) continuous_id).measurableSet

theorem measurable_absResolvent_apply (E δ : ℝ) (x y : ι) :
    Measurable fun H : Matrix ι ι ℂ => absResolvent E δ H x y := by
  have heq : (fun H : Matrix ι ι ℂ => absResolvent E δ H x y) = fun H =>
      if H.IsHermitian then BlockBand.Critical.Collar.Density.rawCfc (collarWeight E δ) H x y
      else 0 := by
    funext H
    rw [absResolvent_eq_ite]
    split_ifs <;> rfl
  have h := BlockBand.Critical.Collar.Density.measurable_rawCfc_apply (ι := ι)
    (M := fun H : Matrix ι ι ℂ => H) measurable_id (measurable_collarWeight E δ) x y
  rw [heq]
  exact Measurable.ite measurableSet_isHermitian h measurable_const

theorem measurable_absResolvent (E δ : ℝ) :
    Measurable fun H : Matrix ι ι ℂ => absResolvent E δ H :=
  Measurable.of_eval fun x => Measurable.of_eval fun y => measurable_absResolvent_apply E δ x y

end Measurable

/-!
## Rotation invariance of the block masses of `|R|`
-/

section Rotation

variable {p : Parameters}

/-- Mass of `|R|` on the ring block `j`: `Σ_{x ∈ block j} Re |R|_{xx}`. -/
def blockAbsMass (p : Parameters) (E δ : ℝ) (j : ZMod p.n) (H : p.SiteMatrix) : ℝ :=
  ∑ x : p.Site, if x.1 = j then (absResolvent E δ H x x).re else 0

/-- Total mass `Σ_x Re |R|_{xx} = Σ_i w_δ(λ_i)`. -/
def totalAbsMass (p : Parameters) (E δ : ℝ) (H : p.SiteMatrix) : ℝ :=
  ∑ x : p.Site, (absResolvent E δ H x x).re

/-- Mass of `|R|` on the collar `{n-1, 0, 1}`. -/
def collarAbsMass (p : Parameters) (E δ : ℝ) (H : p.SiteMatrix) : ℝ :=
  ∑ x : p.Site, if IsCollarBlock p x.1 then (absResolvent E δ H x x).re else 0

theorem blockAbsMass_nonneg (E δ : ℝ) (j : ZMod p.n) (H : p.SiteMatrix) :
    0 ≤ blockAbsMass p E δ j H :=
  Finset.sum_nonneg fun x _ => by
    split_ifs
    · exact re_absResolvent_diag_nonneg E δ H x
    · exact le_rfl

theorem measurable_blockAbsMass (E δ : ℝ) (j : ZMod p.n) :
    Measurable (blockAbsMass p E δ j) := by
  unfold blockAbsMass
  refine Finset.measurable_sum _ fun x _ => ?_
  split_ifs
  · exact Complex.measurable_re.comp (measurable_absResolvent_apply E δ x x)
  · exact measurable_const

theorem measurable_totalAbsMass (E δ : ℝ) : Measurable (totalAbsMass p E δ) :=
  Finset.measurable_sum _ fun x _ =>
    Complex.measurable_re.comp (measurable_absResolvent_apply E δ x x)

theorem sum_blockAbsMass (E δ : ℝ) (H : p.SiteMatrix) :
    ∑ j, blockAbsMass p E δ j H = totalAbsMass p E δ H := by
  unfold blockAbsMass totalAbsMass
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_ite_eq]
  simp

theorem collarAbsMass_le (E δ : ℝ) (H : p.SiteMatrix) :
    collarAbsMass p E δ H ≤
      blockAbsMass p E δ 0 H + blockAbsMass p E δ 1 H + blockAbsMass p E δ (-1) H := by
  unfold collarAbsMass blockAbsMass
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun x _ => ?_
  have h0 := re_absResolvent_diag_nonneg E δ H x
  unfold IsCollarBlock
  split_ifs <;> simp_all

/-- Rotation by `s`: `(j, a) ↦ (j + s, a)`. -/
theorem blockAbsMass_rotate {H : p.SiteMatrix} (hH : H.IsHermitian) (E δ : ℝ)
    (j s : ZMod p.n) :
    blockAbsMass p E δ j (p.siteReindexMatrix (blockSiteEquiv p (Equiv.addRight s)) H) =
      blockAbsMass p E δ (j + s) H := by
  set e := blockSiteEquiv p (Equiv.addRight s)
  have hsub : p.siteReindexMatrix e H = H.submatrix e e := rfl
  unfold blockAbsMass
  rw [hsub, absResolvent_submatrix hH]
  rw [← Equiv.sum_comp e.symm]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [submatrix_apply, Equiv.apply_symm_apply]
  have : (e.symm y).1 = y.1 - s := by simp [e, blockSiteEquiv, sub_eq_add_neg]
  simp only [this, sub_eq_iff_eq_add]

/-- **Cyclic invariance**: every block carries the same expected mass of
`|R|`. -/
theorem lintegral_blockAbsMass_eq (model : p.GaussianRingModel) (E δ : ℝ) (j : ZMod p.n) :
    ∫⁻ H, ENNReal.ofReal (blockAbsMass p E δ j H) ∂(model.law : Measure p.SiteMatrix) =
      ∫⁻ H, ENNReal.ofReal (blockAbsMass p E δ 0 H) ∂(model.law : Measure p.SiteMatrix) := by
  set e := blockSiteEquiv p (Equiv.addRight j)
  have hmap := map_blockSiteReindex model (isRingSymmetry_addRight (p := p) j)
  have hm : Measurable fun H : p.SiteMatrix => ENNReal.ofReal (blockAbsMass p E δ 0 H) :=
    ENNReal.measurable_ofReal.comp (measurable_blockAbsMass E δ 0)
  conv_rhs => rw [← hmap]
  rw [lintegral_map hm (p.measurable_siteReindexMatrix e)]
  refine lintegral_congr_ae ((model.isPhysical.1).mono fun H hH => ?_)
  simp only [e, blockAbsMass_rotate hH, zero_add]

/-- `n · E[mass of block j] = E[total mass]`. -/
theorem lintegral_totalAbsMass_eq (model : p.GaussianRingModel) (E δ : ℝ) :
    ∫⁻ H, ENNReal.ofReal (totalAbsMass p E δ H) ∂(model.law : Measure p.SiteMatrix) =
      p.n * ∫⁻ H, ENNReal.ofReal (blockAbsMass p E δ 0 H) ∂(model.law : Measure p.SiteMatrix) := by
  have h : ∀ H, ENNReal.ofReal (totalAbsMass p E δ H) =
      ∑ j, ENNReal.ofReal (blockAbsMass p E δ j H) := fun H => by
    rw [← sum_blockAbsMass, ENNReal.ofReal_sum_of_nonneg fun j _ => blockAbsMass_nonneg E δ j H]
  simp_rw [h]
  rw [lintegral_finsetSum (f := fun j H => ENNReal.ofReal (blockAbsMass p E δ j H)) _
    fun j _ => ENNReal.measurable_ofReal.comp (measurable_blockAbsMass E δ j)]
  simp_rw [lintegral_blockAbsMass_eq model E δ]
  rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]

/-- **Collar mass**: `E[mass of |R| on the collar] ≤ (3/n) E[Tr |R|]`. -/
theorem lintegral_collarAbsMass_le (model : p.GaussianRingModel) (E δ : ℝ) :
    p.n * ∫⁻ H, ENNReal.ofReal (collarAbsMass p E δ H) ∂(model.law : Measure p.SiteMatrix) ≤
      3 * ∫⁻ H, ENNReal.ofReal (totalAbsMass p E δ H) ∂(model.law : Measure p.SiteMatrix) := by
  rw [lintegral_totalAbsMass_eq model E δ]
  have hle : ∫⁻ H, ENNReal.ofReal (collarAbsMass p E δ H) ∂(model.law : Measure p.SiteMatrix) ≤
      3 * ∫⁻ H, ENNReal.ofReal (blockAbsMass p E δ 0 H) ∂(model.law : Measure p.SiteMatrix) := by
    have hpt : ∀ H, ENNReal.ofReal (collarAbsMass p E δ H) ≤
        ENNReal.ofReal (blockAbsMass p E δ 0 H) + ENNReal.ofReal (blockAbsMass p E δ 1 H) +
          ENNReal.ofReal (blockAbsMass p E δ (-1) H) := fun H => by
      have h0 := blockAbsMass_nonneg E δ 0 H
      have h1 := blockAbsMass_nonneg E δ 1 H
      rw [← ENNReal.ofReal_add h0 h1,
        ← ENNReal.ofReal_add (add_nonneg h0 h1) (blockAbsMass_nonneg E δ (-1) H)]
      exact ENNReal.ofReal_le_ofReal (collarAbsMass_le E δ H)
    refine (lintegral_mono hpt).trans (le_of_eq ?_)
    have hm : ∀ j, Measurable fun H : p.SiteMatrix => ENNReal.ofReal (blockAbsMass p E δ j H) :=
      fun j => ENNReal.measurable_ofReal.comp (measurable_blockAbsMass E δ j)
    have hm01 : Measurable fun H : p.SiteMatrix => ENNReal.ofReal (blockAbsMass p E δ 0 H) +
        ENNReal.ofReal (blockAbsMass p E δ 1 H) := (hm 0).add (hm 1)
    rw [lintegral_add_left hm01, lintegral_add_left (hm 0),
      lintegral_blockAbsMass_eq model E δ 1, lintegral_blockAbsMass_eq model E δ (-1)]
    ring
  calc (p.n : ℝ≥0∞) * ∫⁻ H, ENNReal.ofReal (collarAbsMass p E δ H) ∂(model.law : Measure p.SiteMatrix)
      ≤ p.n * (3 * ∫⁻ H, ENNReal.ofReal (blockAbsMass p E δ 0 H) ∂(model.law : Measure p.SiteMatrix)) :=
        mul_le_mul_right hle _
    _ = 3 * (p.n * ∫⁻ H, ENNReal.ofReal (blockAbsMass p E δ 0 H) ∂(model.law : Measure p.SiteMatrix)) := by
        ring

end Rotation

/-!
## Counting (the counting theorem for the Gaussian ring)
-/

section Counting

variable {p : Parameters}

/-- The zero deformation. -/
def zeroHermitian (p : Parameters) : BlockBand.External.PSSS.HermitianMatrix p.Site :=
  ⟨0, isHermitian_zero⟩

theorem increasingEigenvalue_congr' {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ} (h : A = B) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    BlockBand.Foundations.Spectral.increasingEigenvalue hA =
      BlockBand.Foundations.Spectral.increasingEigenvalue hB := by
  subst h
  rfl

/-- The count of the counting theorem for `H` (no deformation) on `J`, for Hermitian `H`, is the number of
eigenvalues in `J`. -/
theorem physicalSpectralSetCount_zero_eq {H : p.SiteMatrix} (hH : H.IsHermitian) (J : Set ℝ) :
    (BlockBand.Counting.physicalSpectralSetCount p (zeroHermitian p) J H : ℝ) =
      ∑ i, J.indicator (fun _ => (1 : ℝ)) (hH.eigenvalues i) := by
  classical
  have hM : (p.physicalHermitianVersion H).1 + (zeroHermitian p).1 = H := by
    change p.gaussianReconstruction (p.gaussianExtraction H) + (0 : p.SiteMatrix) = H
    rw [p.gaussianReconstruction_gaussianExtraction H hH, add_zero]
  unfold BlockBand.Counting.physicalSpectralSetCount BlockBand.External.PSSS.eigenCount
  rw [increasingEigenvalue_congr' hM _ hH]
  rw [Finset.natCast_card_filter]
  rw [← Equiv.sum_comp (BlockBand.Foundations.Spectral.increasingIndex (ι := p.Site))
    (fun i => J.indicator (fun _ => (1 : ℝ)) (hH.eigenvalues i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [BlockBand.Foundations.Spectral.eigenvalue_increasingIndex]
  simp only [Set.indicator_apply]

theorem card_filter_abs_le_eq {ι : Type*} [Fintype ι] (lam : ι → ℝ) (E r : ℝ) :
    ((Finset.univ.filter fun i => |lam i - E| ≤ r).card : ℝ) =
      ∑ i, (Icc (E - r) (E + r)).indicator (fun _ => (1 : ℝ)) (lam i) := by
  classical
  rw [Finset.natCast_card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Set.indicator_apply, mem_Icc, abs_sub_le_iff]
  congr 1
  apply propext
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

/-- **Expected count** (counting theorem, first clause, `r = 1`, no deformation):
`E #{λ ∈ [E - r, E + r]} ≤ (C/√c) N 2r`. -/
theorem integral_count_le (model : p.GaussianRingModel)
    (source : BlockBand.External.PSSS.SourceContract.{0}) (E : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    ∫ H, (BlockBand.Counting.physicalSpectralSetCount p (zeroHermitian p) (Icc (E - r) (E + r))
        H : ℝ) ∂(model.law : Measure p.SiteMatrix) ≤
      source.C / Real.sqrt p.c * p.N * (2 * r) := by
  have h := BlockBand.Counting.physicalSpectralSetCount_factorialBound p model source
    (zeroHermitian p) (Icc (E - r) (E + r)) measurableSet_Icc (E - r) (E + r) (by linarith)
    subset_rfl 1 le_rfl
  rw [pow_one] at h
  have hc : (E + r - (E - r)) = 2 * r := by ring
  rw [hc] at h
  refine le_of_eq_of_le ?_ h
  refine integral_congr_ae (Filter.Eventually.of_forall fun H => ?_)
  simp [BlockBand.External.PSSS.factorialCount]

theorem integrable_count (model : p.GaussianRingModel) (J : Set ℝ) (hJ : MeasurableSet J) :
    Integrable (fun H => (BlockBand.Counting.physicalSpectralSetCount p (zeroHermitian p) J H : ℝ))
      (model.law : Measure p.SiteMatrix) := by
  have h := BlockBand.External.PSSS.integrable_factorialCount (model.law : Measure p.SiteMatrix)
    (BlockBand.Counting.measurable_physicalSpectralSetCount p (zeroHermitian p) J hJ)
    (fun H => BlockBand.External.PSSS.eigenCount_le_dimension _ _) 1
  refine h.congr (Filter.Eventually.of_forall fun H => ?_)
  simp [BlockBand.External.PSSS.factorialCount]

theorem card_site (p : Parameters) : (Fintype.card p.Site : ℝ) = p.N := by
  simp [Parameters.N, Parameters.Site, ZMod.card]

theorem collarWeight_le_inv {E δ : ℝ} (hδ : 0 < δ) (x : ℝ) : collarWeight E δ x ≤ δ⁻¹ := by
  unfold collarWeight
  split_ifs with h
  · exact inv_anti₀ hδ h.le
  · positivity

theorem totalAbsMass_le (E : ℝ) {δ : ℝ} (hδ : 0 < δ) (H : p.SiteMatrix) :
    totalAbsMass p E δ H ≤ p.N * δ⁻¹ := by
  by_cases hH : H.IsHermitian
  · rw [totalAbsMass, sum_re_absResolvent_diag hH, ← card_site, ← nsmul_eq_mul,
      ← Finset.card_univ, ← Finset.sum_const]
    exact Finset.sum_le_sum fun i _ => collarWeight_le_inv hδ _
  · have : absResolvent E δ H = 0 := by
      have hH' : ¬ IsSelfAdjoint H := hH
      exact cfc_apply_of_not_predicate H hH'
    simp only [totalAbsMass, this, Matrix.zero_apply, Complex.zero_re, Finset.sum_const_zero]
    positivity

theorem totalAbsMass_nonneg (E δ : ℝ) (H : p.SiteMatrix) : 0 ≤ totalAbsMass p E δ H :=
  Finset.sum_nonneg fun x _ => re_absResolvent_diag_nonneg E δ H x

/-- **The expected truncated trace** (first truncated-inverse bound on the ring, dyadic
form): at `δ = 2^{-(K+1)}`, `E Tr |R| ≤ N (1 + 2 (C/√c)(K + 1))`. -/
theorem integral_totalAbsMass_le (model : p.GaussianRingModel)
    (source : BlockBand.External.PSSS.SourceContract.{0}) (E : ℝ) (K : ℕ) :
    ∫ H, totalAbsMass p E ((1 / 2 : ℝ) ^ (K + 1)) H ∂(model.law : Measure p.SiteMatrix) ≤
      p.N * (1 + 2 * (source.C / Real.sqrt p.c) * (K + 1)) := by
  set C' := source.C / Real.sqrt p.c
  set cnt : ℕ → p.SiteMatrix → ℝ := fun k H =>
    (BlockBand.Counting.physicalSpectralSetCount p (zeroHermitian p)
      (Icc (E - (1 / 2 : ℝ) ^ k) (E + (1 / 2 : ℝ) ^ k)) H : ℝ)
  have hint : ∀ k, Integrable (cnt k) (model.law : Measure p.SiteMatrix) := fun k =>
    integrable_count model _ measurableSet_Icc
  have hpt : ∀ᵐ H ∂(model.law : Measure p.SiteMatrix),
      totalAbsMass p E ((1 / 2 : ℝ) ^ (K + 1)) H ≤
        p.N + ∑ k ∈ Finset.range (K + 1), (2 : ℝ) ^ k * cnt k H := by
    filter_upwards [model.isPhysical.1] with H hH
    rw [totalAbsMass, sum_re_absResolvent_diag hH, ← card_site]
    refine (sum_collarWeight_le hH.eigenvalues E K).trans (le_of_eq ?_)
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [card_filter_abs_le_eq, ← physicalSpectralSetCount_zero_eq hH]
  have hTm : Integrable (fun H => totalAbsMass p E ((1 / 2 : ℝ) ^ (K + 1)) H)
      (model.law : Measure p.SiteMatrix) := by
    refine Integrable.of_bound (measurable_totalAbsMass E _).aestronglyMeasurable
      (p.N * ((1 / 2 : ℝ) ^ (K + 1))⁻¹) (Filter.Eventually.of_forall fun H => ?_)
    rw [Real.norm_of_nonneg (totalAbsMass_nonneg E _ H)]
    exact totalAbsMass_le E (by positivity) H
  have hRint : Integrable (fun H => (p.N : ℝ) + ∑ k ∈ Finset.range (K + 1), (2 : ℝ) ^ k * cnt k H)
      (model.law : Measure p.SiteMatrix) :=
    (integrable_const _).add (integrable_finsetSum _ fun k _ => (hint k).const_mul _)
  refine (integral_mono_ae hTm hRint hpt).trans ?_
  rw [integral_add (integrable_const _) (integrable_finsetSum _ fun k _ => (hint k).const_mul _),
    integral_finsetSum _ fun k _ => (hint k).const_mul _]
  simp only [integral_const, probReal_univ, one_smul, integral_const_mul]
  have hk : ∀ k ∈ Finset.range (K + 1), (2 : ℝ) ^ k * ∫ H, cnt k H ∂(model.law : Measure p.SiteMatrix)
      ≤ 2 * C' * p.N := by
    intro k _
    have h := integral_count_le model source E (r := (1 / 2 : ℝ) ^ k) (by positivity)
    calc (2 : ℝ) ^ k * ∫ H, cnt k H ∂(model.law : Measure p.SiteMatrix)
        ≤ 2 ^ k * (C' * p.N * (2 * (1 / 2 : ℝ) ^ k)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = 2 * C' * p.N := by
          rw [div_pow, one_pow]
          field_simp
  calc (p.N : ℝ) + ∑ k ∈ Finset.range (K + 1),
        (2 : ℝ) ^ k * ∫ H, cnt k H ∂(model.law : Measure p.SiteMatrix)
      ≤ p.N + ∑ _k ∈ Finset.range (K + 1), 2 * C' * p.N := by
        linarith [Finset.sum_le_sum hk]
    _ = p.N * (1 + 2 * C' * (K + 1)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-- **No eigenvalue near `E`** (the event behind `P(𝓔_ε^c) ≤ Cε`): if `H` is Hermitian and the count on
`[E - δ, E + δ]` vanishes, every eigenvalue is at distance `> δ` from `E`. -/
theorem gap_of_count_eq_zero {H : p.SiteMatrix} (hH : H.IsHermitian) {E δ : ℝ}
    (h0 : BlockBand.Counting.physicalSpectralSetCount p (zeroHermitian p) (Icc (E - δ) (E + δ)) H
      = 0) : ∀ i, δ < |hH.eigenvalues i - E| := by
  intro i
  by_contra hi
  rw [not_lt] at hi
  have h := physicalSpectralSetCount_zero_eq hH (Icc (E - δ) (E + δ))
  rw [h0, Nat.cast_zero] at h
  have hmem : hH.eigenvalues i ∈ Icc (E - δ) (E + δ) := by
    rw [abs_sub_le_iff] at hi
    constructor <;> linarith [hi.1, hi.2]
  have hpos : (0 : ℝ) < ∑ j, (Icc (E - δ) (E + δ)).indicator (fun _ => (1 : ℝ))
      (hH.eigenvalues j) := by
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun j =>
      (Icc (E - δ) (E + δ)).indicator (fun _ => (1 : ℝ)) (hH.eigenvalues j))
      (fun j _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _) (Finset.mem_univ i))
    simp [Set.indicator_of_mem hmem]
  linarith

/-- `P(some eigenvalue within δ of E) ≤ (C/√c) N 2δ` (Markov on the count). -/
theorem measure_count_pos_le (model : p.GaussianRingModel)
    (source : BlockBand.External.PSSS.SourceContract.{0}) (E : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (model.law : Measure p.SiteMatrix)
        {H | 1 ≤ BlockBand.Counting.physicalSpectralSetCount p (zeroHermitian p)
          (Icc (E - δ) (E + δ)) H} ≤
      ENNReal.ofReal (source.C / Real.sqrt p.c * p.N * (2 * δ)) := by
  set f : p.SiteMatrix → ℝ := fun H =>
    (BlockBand.Counting.physicalSpectralSetCount p (zeroHermitian p) (Icc (E - δ) (E + δ)) H : ℝ)
  have hf := integrable_count model (Icc (E - δ) (E + δ)) measurableSet_Icc
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := (model.law : Measure p.SiteMatrix))
    (Filter.Eventually.of_forall fun H => (Nat.cast_nonneg _ : (0 : ℝ) ≤ f H)) hf 1
  rw [one_mul] at hmk
  have hset : {H : p.SiteMatrix | 1 ≤ BlockBand.Counting.physicalSpectralSetCount p
      (zeroHermitian p) (Icc (E - δ) (E + δ)) H} = {H | (1 : ℝ) ≤ f H} := by
    ext H; simp [f]
  rw [hset, ← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal (hmk.trans (integral_count_le model source E hδ))

end Counting

end BlockBand.Critical.EntireLaw
