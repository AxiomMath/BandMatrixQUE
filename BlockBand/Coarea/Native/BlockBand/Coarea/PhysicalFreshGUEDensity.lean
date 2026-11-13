module

public import BlockBand.Coarea.Native.BlockBand.Coarea.PhysicalConditionalCoareaManuscript

/-!
# Lebesgue density of the fresh finite-product GUE block

The fresh GUE block of `PhysicalHermitianGaussianSplit` is the product of
diagonal `N(0,t)` and strict-upper real/imaginary `N(0,t/2)` coordinate laws.
For positive `t` this file identifies that product measure with Lebesgue
measure on the real coordinate space weighted by the matrix density
`Z_d(t)⁻¹ exp (-Tr(G²)/(2t))`, `Z_d(t) = gueNormalizer d t`.

The proof is the coordinatewise Gaussian density, the product of densities on a
finite product (proved here by induction on the number of coordinates), the
exact Hilbert–Schmidt coordinate identity
`Tr(G²) = ∑ᵢ xᵢᵢ² + 2 ∑_{i<j} (Re² + Im²)`, and the factorization of
`gueNormalizer`.  This proves `FreshGUECoordinateDensityIdentification`
for `0 < t` (it is false at `t = 0` for `d > 0`), and rewrites the fresh-GUE side of
`physicalConditionalCoareaManuscript_bridge`, after residual translation, as an explicit
Lebesgue integral over the coordinates of the total exposed block.

It then computes the chart weight exactly
(`physicalSchurOuterWeight_eq_matrixForm`): it is
`c_{d,t} exp(-‖M - F(E)‖²/(2t)) ⟨v, 𝒟(E) v⟩`, centred at the energy-dependent
Schur compression `F(E)`.  For the uncoupled readback (`C = 0`, `V` the
residual) it equals `κ_d(t) = c_{d,t} Z_d(t)` times the fresh GUE density, and
`κ_2(1) ≠ 1`, so the identification `weight = density` is false.  The
joined equality "fresh GUE side = chart sum" is proved with the
factor `κ_d(t)` on the decoded union, and on the whole space conditionally on a
named a.e.-cover hypothesis.  All statements are at fixed finite `d`; no limit
or uniformity is asserted.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section
namespace CoareaNative.BlockBand

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal MatrixOrder

/-!
### Products of densities on finite products
-/

/-- Tonelli for a finite product of one-variable functions over a finite
product of σ-finite measures on `ℝ`. -/
theorem lintegral_pi_fin_prod_eq_prod :
    ∀ (n : ℕ) (μ : Fin n → Measure ℝ) [∀ i, SigmaFinite (μ i)]
      (f : Fin n → ℝ → ℝ≥0∞), (∀ i, Measurable (f i)) →
      ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ y, f i y ∂μ i
  | 0, μ, _, f, _ => by
      simp
  | n + 1, μ, _, f, hf => by
      have hmp := (measurePreserving_piFinSuccAbove μ 0).symm
      rw [← hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
      simp_rw [Fin.prod_univ_succ]
      have hcomp : ∀ p : ℝ × (Fin n → ℝ),
          (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm p 0 = p.1 ∧
          ∀ j : Fin n,
            (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm p j.succ =
              p.2 j := by
        intro p
        simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.cons_succ]
      simp_rw [fun p => (hcomp p).1, fun p j => (hcomp p).2 j]
      simp only [Fin.succAbove_zero]
      have hg : Measurable (fun y : Fin n → ℝ => ∏ j, f j.succ (y j)) :=
        Finset.measurable_prod _ fun j _ => (hf j.succ).comp (measurable_pi_apply j)
      rw [lintegral_prod_mul (f := f 0) (g := fun y : Fin n → ℝ => ∏ j, f j.succ (y j))
          (hf 0).aemeasurable hg.aemeasurable,
        lintegral_pi_fin_prod_eq_prod n (fun j => μ j.succ) (fun j => f j.succ)
          (fun j => hf j.succ)]

/-- A finite product of densities against σ-finite measures on `ℝ` is the
product measure with the product density. -/
theorem pi_fin_withDensity_eq {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ i, SigmaFinite (μ i)] (f : Fin n → ℝ → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    Measure.pi (fun i => (μ i).withDensity (f i)) =
      (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i)) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi,
    lintegral_pi_fin_prod_eq_prod n _ f hf]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i)]

/-!
### The Hilbert–Schmidt coordinate identity
-/

/-- A double sum over `Fin d × Fin d` splits into the diagonal, the strict
upper triangle and the strict lower triangle (indexed by its transpose). -/
theorem sum_fin_pairs_eq_diag_add_upper_add_lower {d : ℕ}
    (g : Fin d → Fin d → ℝ) :
    ∑ i, ∑ j, g i j =
      ∑ i, g i i + ∑ ij : StrictUpperIndex d, g ij.1.1 ij.1.2 +
        ∑ ij : StrictUpperIndex d, g ij.1.2 ij.1.1 := by
  rw [← Fintype.sum_prod_type' (f := g)]
  have hsplit : ∀ p : Fin d × Fin d, g p.1 p.2 =
      ((if p.1 = p.2 then g p.1 p.2 else 0) +
        (if p.1 < p.2 then g p.1 p.2 else 0)) +
        (if p.2 < p.1 then g p.1 p.2 else 0) := by
    intro p
    rcases lt_trichotomy p.1 p.2 with h | h | h
    · simp [h, h.ne, not_lt_of_gt h]
    · simp [h]
    · simp [h, h.ne', not_lt_of_gt h]
  rw [Finset.sum_congr rfl fun p _ => hsplit p, Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  have hupper : ∀ h : Fin d × Fin d → ℝ,
      (∑ p : Fin d × Fin d, if p.1 < p.2 then h p else 0) =
        ∑ ij : StrictUpperIndex d, h ij.1 := by
    intro h
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (fun p => by simp) h
  congr 1
  · congr 1
    · rw [Fintype.sum_prod_type' (f := fun i j => if i = j then g i j else 0)]
      simp
    · exact hupper fun p => g p.1 p.2
  · rw [← (Equiv.prodComm (Fin d) (Fin d)).sum_comp]
    exact hupper fun p => g p.2 p.1

/-- The number of strict-upper positions satisfies `2 · #{i<j} = d (d - 1)`. -/
theorem two_mul_card_strictUpperIndex (d : ℕ) :
    2 * (Fintype.card (StrictUpperIndex d) : ℝ) = (d : ℝ) * ((d : ℝ) - 1) := by
  have h := sum_fin_pairs_eq_diag_add_upper_add_lower (d := d) (fun _ _ => (1 : ℝ))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one] at h
  linarith

/-- Exact Hilbert–Schmidt identity in Hermitian coordinates:
`Tr(G²) = ∑ᵢ xᵢᵢ² + 2 ∑_{i<j} ((Re Gᵢⱼ)² + (Im Gᵢⱼ)²)`. -/
theorem hilbertSchmidtNormSq_hermitianMatrixOfCoordinates {d : ℕ}
    (y : HermitianCoordinate d → ℝ) :
    hilbertSchmidtNormSq (hermitianMatrixOfCoordinates y) =
      ∑ i, y (.inl i) ^ 2 +
        2 * ∑ ij : StrictUpperIndex d,
          (y (.inr (.inl ij)) ^ 2 + y (.inr (.inr ij)) ^ 2) := by
  unfold hilbertSchmidtNormSq
  rw [sum_fin_pairs_eq_diag_add_upper_add_lower]
  have hdiag : ∀ i, Complex.normSq (hermitianMatrixOfCoordinates y i i) =
      y (.inl i) ^ 2 := by
    intro i
    simp [hermitianMatrixOfCoordinates, Complex.normSq_ofReal, sq]
  have hup : ∀ ij : StrictUpperIndex d,
      Complex.normSq (hermitianMatrixOfCoordinates y ij.1.1 ij.1.2) =
        y (.inr (.inl ij)) ^ 2 + y (.inr (.inr ij)) ^ 2 := by
    intro ij
    simp [hermitianMatrixOfCoordinates, ij.2.ne, ij.2, hermitianUpperEntry,
      Complex.normSq_add_mul_I]
  have hlow : ∀ ij : StrictUpperIndex d,
      Complex.normSq (hermitianMatrixOfCoordinates y ij.1.2 ij.1.1) =
        y (.inr (.inl ij)) ^ 2 + y (.inr (.inr ij)) ^ 2 := by
    intro ij
    simp [hermitianMatrixOfCoordinates, ij.2.ne', not_lt_of_gt ij.2,
      hermitianUpperEntry, Complex.normSq_apply]
    ring
  simp only [hdiag, hup, hlow]
  ring

/-!
### Identification of the fresh GUE coordinate law
-/

/-- The real variance of a fresh coordinate after reindexing through the
canonical coordinate equivalence. -/
theorem hermitianGUEFinCoordinateVariance_equivFin_inl (d : ℕ) {t : ℝ}
    (ht : 0 ≤ t) (i : Fin d) :
    ((hermitianGUEFinCoordinateVariance d t ht
      (hermitianCoordinateEquivFin d (.inl i)) : ℝ≥0) : ℝ) = t := by
  simp only [hermitianGUEFinCoordinateVariance, Equiv.symm_apply_apply]
  rfl

/-- Strict-upper real coordinates carry variance `t/2`. -/
theorem hermitianGUEFinCoordinateVariance_equivFin_inr (d : ℕ) {t : ℝ}
    (ht : 0 ≤ t) (c : StrictUpperIndex d ⊕ StrictUpperIndex d) :
    ((hermitianGUEFinCoordinateVariance d t ht
      (hermitianCoordinateEquivFin d (.inr c)) : ℝ≥0) : ℝ) = t / 2 := by
  simp only [hermitianGUEFinCoordinateVariance, Equiv.symm_apply_apply]
  rfl

/-- Pointwise: the product of the coordinate Gaussian densities is the
GUE matrix density `Z_d(t)⁻¹ exp (-Tr(G²)/(2t))` of the
reconstructed block.  Positive variance `0 < t`; fixed finite `d`. -/
theorem prod_gaussianPDF_eq_hermitianGUEDensity (d : ℕ) {t : ℝ} (ht : 0 < t)
    (x : HermitianCoordinateSpace d) :
    ∏ k, gaussianPDF 0 (hermitianGUEFinCoordinateVariance d t ht.le k) (x k) =
      hermitianGUEDensity d t (hermitianGUEBlock d x) := by
  simp only [gaussianPDF]
  rw [← ENNReal.ofReal_prod_of_nonneg fun k _ => gaussianPDFReal_nonneg _ _ _]
  unfold hermitianGUEDensity
  congr 1
  rw [← (hermitianCoordinateEquivFin d).prod_comp, Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [gaussianPDFReal_def, sub_zero,
    hermitianGUEFinCoordinateVariance_equivFin_inl,
    hermitianGUEFinCoordinateVariance_equivFin_inr]
  change _ = Real.exp (-hilbertSchmidtNormSq
      (hermitianMatrixOfCoordinates (x ∘ hermitianCoordinateEquivFin d)) / (2 * t)) /
        gueNormalizer d t
  rw [hilbertSchmidtNormSq_hermitianMatrixOfCoordinates]
  simp only [Function.comp_apply, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← Real.exp_sum]
  have hS := two_mul_card_strictUpperIndex d
  set S := Fintype.card (StrictUpperIndex d)
  have hb : Real.sqrt (2 * Real.pi * (t / 2)) ^ 2 = Real.pi * t := by
    rw [Real.sq_sqrt (by positivity)]
    ring
  have hZ : gueNormalizer d t =
      Real.sqrt (2 * Real.pi * t) ^ d * Real.sqrt (2 * Real.pi * (t / 2)) ^ (2 * S) := by
    unfold gueNormalizer
    rw [pow_mul, hb, ← Real.rpow_natCast (Real.pi * t), ← hS,
      Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 2
    · ring
    · ring
  rw [hZ]
  have ha : 0 < Real.sqrt (2 * Real.pi * t) := by positivity
  have hb0 : 0 < Real.sqrt (2 * Real.pi * (t / 2)) := by positivity
  have hexp : ∀ (A B C : ℝ), Real.exp (-A / (2 * t)) * Real.exp (-B / (2 * (t / 2))) *
      Real.exp (-C / (2 * (t / 2))) = Real.exp (-(A + 2 * (B + C)) / (2 * t)) := by
    intro A B C
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    field_simp
    ring
  simp only [← Finset.sum_div, Finset.sum_neg_distrib, Finset.sum_add_distrib]
  rw [← hexp]
  ring

/-- Every fresh coordinate variance is nonzero for positive `t`. -/
theorem hermitianGUEFinCoordinateVariance_ne_zero (d : ℕ) {t : ℝ} (ht : 0 < t)
    (k : Fin (Fintype.card (HermitianCoordinate d))) :
    hermitianGUEFinCoordinateVariance d t ht.le k ≠ 0 := by
  rw [ne_eq, ← NNReal.coe_eq_zero, ← Equiv.apply_symm_apply (hermitianCoordinateEquivFin d) k]
  rcases (hermitianCoordinateEquivFin d).symm k with i | c
  · rw [hermitianGUEFinCoordinateVariance_equivFin_inl]
    exact ht.ne'
  · rw [hermitianGUEFinCoordinateVariance_equivFin_inr]
    positivity

/-- Measurability of the GUE matrix density in the fresh real coordinates. -/
theorem measurable_hermitianGUEDensity_comp_block (d : ℕ) (t : ℝ) :
    Measurable (fun x : HermitianCoordinateSpace d =>
      hermitianGUEDensity d t (hermitianGUEBlock d x)) := by
  have hG : Measurable fun x : HermitianCoordinateSpace d => (hermitianGUEBlock d x).1 :=
    measurable_subtype_coe.comp (measurable_hermitianGUEBlock d)
  have hHS : Measurable fun x : HermitianCoordinateSpace d =>
      hilbertSchmidtNormSq (hermitianGUEBlock d x).1 := by
    unfold hilbertSchmidtNormSq
    refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
    exact Complex.continuous_normSq.measurable.comp hG.eval_matrix
  unfold hermitianGUEDensity
  exact ENNReal.measurable_ofReal.comp
    ((Real.measurable_exp.comp (hHS.neg.div_const _)).div_const _)

/-- **Fresh GUE coordinate density identification**.

For every finite `d` and every positive variance `t`, the product of the
diagonal `N(0,t)` and strict-upper real/imaginary `N(0,t/2)` coordinate laws
equals Lebesgue measure on `Fin (#coordinates) → ℝ` with density
`Z_d(t)⁻¹ exp (-Tr(G²)/(2t))` of the reconstructed block `G`,
`Z_d(t) = gueNormalizer d t`.  The hypothesis `0 < t` is necessary: see
`hermitianGUECoordinateMeasure_ne_withDensity_zero`. -/
theorem hermitianGUECoordinateMeasure_eq_withDensity (d : ℕ) {t : ℝ} (ht : 0 < t) :
    hermitianGUECoordinateMeasure d t ht.le =
      volume.withDensity (fun x =>
        hermitianGUEDensity d t (hermitianGUEBlock d x)) := by
  have hv := hermitianGUEFinCoordinateVariance_ne_zero d ht
  have hfun : (fun k => gaussianReal 0 (hermitianGUEFinCoordinateVariance d t ht.le k)) =
      fun k => volume.withDensity
        (gaussianPDF 0 (hermitianGUEFinCoordinateVariance d t ht.le k)) :=
    funext fun k => gaussianReal_of_var_ne_zero 0 (hv k)
  have : ∀ k, SigmaFinite (volume.withDensity
      (gaussianPDF 0 (hermitianGUEFinCoordinateVariance d t ht.le k))) := fun k => by
    rw [← gaussianReal_of_var_ne_zero 0 (hv k)]
    infer_instance
  unfold hermitianGUECoordinateMeasure
  rw [hfun, pi_fin_withDensity_eq (fun _ => volume) _
    (fun k => measurable_gaussianPDF 0 _), ← volume_pi]
  congr 1
  funext x
  exact prod_gaussianPDF_eq_hermitianGUEDensity d ht x

/-- The identification fails at `t = 0` for every nonempty block: the product
of the degenerate laws `N(0,0)` is a probability measure, whereas Lean's
`gueNormalizer d 0 = 0` makes the displayed density identically `0`. -/
theorem hermitianGUECoordinateMeasure_ne_withDensity_zero {d : ℕ} (hd : 0 < d) :
    hermitianGUECoordinateMeasure d 0 le_rfl ≠
      volume.withDensity (fun x =>
        hermitianGUEDensity d 0 (hermitianGUEBlock d x)) := by
  intro h
  have hZ : gueNormalizer d 0 = 0 := by
    unfold gueNormalizer
    rw [mul_zero, Real.zero_rpow (by positivity), zero_mul]
  have hdens : (fun x : HermitianCoordinateSpace d =>
      hermitianGUEDensity d 0 (hermitianGUEBlock d x)) = 0 := by
    funext x
    simp [hermitianGUEDensity, hZ]
  have h1 := measure_univ (μ := hermitianGUECoordinateMeasure d 0 le_rfl)
  rw [h, hdens, withDensity_zero] at h1
  simp at h1

/-- The fresh GUE integral of an arbitrary (not necessarily measurable)
observable is its Lebesgue integral against the matrix density, `0 < t`. -/
theorem lintegral_hermitianGUECoordinateMeasure_eq (d : ℕ) {t : ℝ} (ht : 0 < t)
    (F : HermitianCoordinateSpace d → ℝ≥0∞) :
    ∫⁻ g, F g ∂hermitianGUECoordinateMeasure d t ht.le =
      ∫⁻ g, hermitianGUEDensity d t (hermitianGUEBlock d g) * F g := by
  rw [hermitianGUECoordinateMeasure_eq_withDensity d ht,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _
      (measurable_hermitianGUEDensity_comp_block d t)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rfl

/-- Reconstruction is additive: `V(z) + G(g) = H(z + g)`. -/
theorem hermitianMatrixAdd_hermitianOfFinCoordinates (d : ℕ)
    (z g : HermitianCoordinateSpace d) :
    hermitianMatrixAdd (hermitianOfFinCoordinates d z) (hermitianGUEBlock d g) =
      hermitianOfFinCoordinates d (z + g) := by
  apply Subtype.ext
  exact ((hermitianCoordinatesLinearMap d).map_add
    (z ∘ hermitianCoordinateEquivFin d) (g ∘ hermitianCoordinateEquivFin d)).symm

/-- **Residual translation** of the fresh GUE integral.  For a fixed residual coordinate vector `z` and
`0 < t`, the fresh-GUE average of `Φ(V + G)` is the Lebesgue integral over the
coordinates `x` of the total block `H = V + G`, weighted by the GUE density of
`G = H - V`.  `Φ` is arbitrary; no measurability is needed. -/
theorem lintegral_hermitianGUE_residual_translate (d : ℕ) {t : ℝ} (ht : 0 < t)
    (z : HermitianCoordinateSpace d) (Φ : HermitianMatrix (Fin d) → ℝ≥0∞) :
    ∫⁻ g, Φ (hermitianMatrixAdd (hermitianOfFinCoordinates d z) (hermitianGUEBlock d g))
        ∂hermitianGUECoordinateMeasure d t ht.le =
      ∫⁻ x, hermitianGUEDensity d t (hermitianOfFinCoordinates d (x - z)) *
        Φ (hermitianOfFinCoordinates d x) := by
  rw [lintegral_hermitianGUECoordinateMeasure_eq d ht]
  simp_rw [hermitianMatrixAdd_hermitianOfFinCoordinates]
  rw [← lintegral_add_left_eq_self
    (fun x => hermitianGUEDensity d t (hermitianOfFinCoordinates d (x - z)) *
      Φ (hermitianOfFinCoordinates d x)) z]
  simp only [add_sub_cancel_left]
  rfl

/-!
### The fresh GUE coordinate density identification
-/

/-- `FreshGUECoordinateDensityIdentification d t` holds for every finite `d`
and every positive variance `t`. -/
theorem freshGUECoordinateDensityIdentification (d : ℕ) {t : ℝ} (ht : 0 < t) :
    FreshGUECoordinateDensityIdentification d t ht.le :=
  hermitianGUECoordinateMeasure_eq_withDensity d ht

/-- The nonnegative-`t` form is false at `t = 0` for every nonempty block, so
`0 < t` in `freshGUECoordinateDensityIdentification` cannot be dropped. -/
theorem not_freshGUECoordinateDensityIdentification_zero {d : ℕ} (hd : 0 < d) :
    ¬ FreshGUECoordinateDensityIdentification d 0 le_rfl :=
  hermitianGUECoordinateMeasure_ne_withDensity_zero hd

/-- The fresh GUE variance `s/(2W)` is positive for positive split parameter. -/
theorem coareaGUEVariance_pos (p : Params) {s : ℝ} (hs : 0 < s) :
    0 < coareaGUEVariance p s := by
  unfold coareaGUEVariance
  have hW : (0 : ℝ) < p.W := p.real_W_pos
  positivity

/-- Coordinate readback inverts reconstruction. -/
theorem hermitianFinCoordinateReadback_hermitianOfFinCoordinates (d : ℕ)
    (x : HermitianCoordinateSpace d) :
    hermitianFinCoordinateReadback d (hermitianOfFinCoordinates d x) = x :=
  (hermitianFinCoordinatesLinearEquiv d).symm_apply_apply x

/-- Lebesgue form of the fresh-GUE Tonelli split for the paper's phase-free
observable.

For `0 < s ≤ min(c, b)`, after fixing residual coordinates `z.1` and exterior
datum `z.2`, the fresh GUE average is the Lebesgue integral over the real
coordinates `x` of the total exposed block `H = V + G`, with density
`Z_{2W}(t)⁻¹ exp (-Tr((H - V)²)/(2t))`, `t = s/(2W)`, against the coordinate
observable `phaseFreeOrderedProjectorObservable ρ Ψ x` used by the chart side.
Fixed `W`, ranks and exterior law; no limit is asserted. -/
theorem lintegral_physicalPhaseFreeGaussian_lebesgue
    {Ξ : Type*} [MeasurableSpace Ξ]
    (p : Params) {s : ℝ}
    (hs : 0 < s) (hsc : s ≤ p.c) (hsb : s ≤ p.b)
    (exteriorLaw : Measure Ξ)
    (ρ : HermitianEigenRank (2 * p.W))
    (Ψ : Matrix (Fin (2 * p.W)) (Fin (2 * p.W)) ℂ → ℝ≥0∞)
    (hΨ : Measurable Ψ) :
    (∫⁻ ω,
      physicalMatrixPhaseFreeObservable ρ Ψ
        (physicalHermitianExposedPair ω)
      ∂physicalHermitianSplitMeasure (2 * p.W) (coareaGUEVariance p s)
        (coareaGUEVariance_nonneg p hs.le)
        (physicalExposedPairResidualMeasure p hs.le hsc hsb) exteriorLaw) =
      ∫⁻ z, (∫⁻ x,
          hermitianGUEDensity (2 * p.W) (coareaGUEVariance p s)
              (hermitianOfFinCoordinates (2 * p.W) (x - z.1)) *
            phaseFreeOrderedProjectorObservable ρ Ψ x)
        ∂((physicalExposedPairResidualMeasure p hs.le hsc hsb).prod exteriorLaw) := by
  rw [lintegral_physicalPhaseFreeGaussian_split p hs.le hsc hsb exteriorLaw ρ Ψ hΨ]
  refine lintegral_congr fun z => ?_
  rw [lintegral_hermitianGUE_residual_translate (2 * p.W) (coareaGUEVariance_pos p hs)]
  refine lintegral_congr fun x => ?_
  unfold physicalMatrixPhaseFreeObservable
  rw [hermitianFinCoordinateReadback_hermitianOfFinCoordinates]

/-- **Lebesgue form of `physicalConditionalCoareaManuscript_bridge`**.

Under the same hypotheses, now with `0 < s`, the fresh finite-product GUE
average of the phase-free observable is rewritten — using
`FreshGUECoordinateDensityIdentification` and residual translation — as an
iterated Lebesgue integral over the total-block coordinates with the explicit
GUE density, and the dependent correction-free moving-root coarea identity
holds for the same observable.  All dimensions, ranks, exterior data and pole
charts are fixed; no limit or uniformity is asserted. -/
theorem physicalConditionalCoareaManuscript_bridge_lebesgue
    {Ξ : Type*} [MeasurableSpace Ξ]
    (p₀ : Params) {s : ℝ}
    (hs : 0 < s) (hsc : s ≤ p₀.c) (hsb : s ≤ p₀.b)
    (exteriorLaw : Measure Ξ)
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {r : ℕ} {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix (Fin (2 * p₀.W)) (Fin (2 * p₀.W)) ℂ)
    (coupling : Matrix (Fin (2 * p₀.W)) n ℂ)
    (D : Matrix n n ℂ) (hA : A.IsHermitian) (hD : D.IsHermitian)
    (α : Fin (Fintype.card (Fin (2 * p₀.W) ⊕ n)))
    (R : HermitianCoordinateSpace r)
    (cover : PhysicalCoareaPoleChartCover κ α.val R)
    (hpoleFree : ∀ a E, E ∈ cover.interval a →
      IsUnit (physicalExteriorPencil D E).det)
    (hloewner : ∀ a E₁, E₁ ∈ cover.interval a →
      ∀ E₂, E₂ ∈ cover.interval a → E₁ < E₂ →
        physicalSchurMatrix A coupling D E₂ ≤
          physicalSchurMatrix A coupling D E₁ -
            ((E₂ - E₁ : ℝ) : ℂ) • 1)
    (hsimple : ∀ a E, E ∈ cover.interval a →
      Function.Injective
        (orderedEigenvalue (physicalSchurFamily A coupling D hA hD E)))
    (H_R : Matrix (Fin r) (Fin r) ℂ)
    (C : Matrix (Fin r) (Unit ⊕ Fin (2 * p₀.W - 1)) ℂ)
    (V : Matrix (Unit ⊕ Fin (2 * p₀.W - 1))
      (Unit ⊕ Fin (2 * p₀.W - 1)) ℂ)
    (ρ : HermitianEigenRank (2 * p₀.W))
    (Ψ : Matrix (Fin (2 * p₀.W)) (Fin (2 * p₀.W)) ℂ → ℝ≥0∞)
    (hΨ : Measurable Ψ) :
    ((∫⁻ ω,
      physicalMatrixPhaseFreeObservable ρ Ψ
        (physicalHermitianExposedPair ω)
      ∂physicalHermitianSplitMeasure (2 * p₀.W) (coareaGUEVariance p₀ s)
        (coareaGUEVariance_nonneg p₀ hs.le)
        (physicalExposedPairResidualMeasure p₀ hs.le hsc hsb) exteriorLaw) =
      ∫⁻ z, (∫⁻ x,
          hermitianGUEDensity (2 * p₀.W) (coareaGUEVariance p₀ s)
              (hermitianOfFinCoordinates (2 * p₀.W) (x - z.1)) *
            phaseFreeOrderedProjectorObservable ρ Ψ x)
        ∂((physicalExposedPairResidualMeasure p₀ hs.le hsc hsb).prod exteriorLaw)) ∧
    ((∀ a : κ,
      Function.Bijective
          (physicalFixedRankEigenEnergyMap A coupling D hA hD
            (cover.interval a) α (hpoleFree a)) ∧
        ∀ u v : MovingFixedRankSchurCrossing
            (physicalSchurFamily A coupling D hA hD) (cover.interval a)
            (fun E => negativeEigenvalueCount
              (physicalExteriorFamily D hD E).property) α.val,
          u.1.1 = v.1.1 → u.1.2 = v.1.2) ∧
    ((∑ a : κ, ∑ rank : HermitianEigenRank (2 * p₀.W),
      ∑ chart : OrderedEigenlineChartIndex (2 * p₀.W),
      ∫⁻ K in selectedEigenpairFinCoordinateChartDecode (ofLex chart).1 ''
          cover.source a rank chart,
        eigenpairChartTransportWeight (ofLex chart).1
          (cover.source a rank chart)
          (physicalSchurOuterWeight (coareaGUEVariance p₀ s)
            H_R C V (ofLex chart).1) K *
            phaseFreeOrderedProjectorObservable ρ Ψ K) =
      ∑ a : κ, ∑ rank : HermitianEigenRank (2 * p₀.W),
        ∑ chart : OrderedEigenlineChartIndex (2 * p₀.W),
        ∫⁻ x in cover.source a rank chart,
          physicalSchurManuscriptDensity (coareaGUEVariance p₀ s)
            H_R C V (ofLex chart).1 x *
            phaseFreeOrderedProjectorObservable ρ Ψ
              (selectedEigenpairFinCoordinateChartDecode
                (ofLex chart).1 x))) := by
  refine ⟨lintegral_physicalPhaseFreeGaussian_lebesgue p₀ hs hsc hsb exteriorLaw ρ Ψ hΨ,
    ?_⟩
  exact (physicalConditionalCoareaManuscript_bridge p₀ hs.le hsc hsb exteriorLaw
    A coupling D hA hD α R cover hpoleFree hloewner hsimple H_R C V ρ Ψ hΨ).2

/-!
### Exact form of the paper's chart weight
-/

/-- Hilbert–Schmidt norm as a trace. -/
theorem hilbertSchmidtNormSq_eq_re_trace {m : Type*} [Fintype m]
    (A : Matrix m m ℂ) :
    hilbertSchmidtNormSq A = ((Aᴴ * A).trace).re := by
  unfold hilbertSchmidtNormSq
  rw [Matrix.trace, Complex.re_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_re, Complex.conj_re,
    Complex.conj_im, Complex.normSq_apply]
  ring

/-- Unitary conjugation preserves the Hilbert–Schmidt norm. -/
theorem hilbertSchmidtNormSq_unitary_conj {m : Type*} [Fintype m] [DecidableEq m]
    (U A : Matrix m m ℂ) (hU : Uᴴ * U = 1) :
    hilbertSchmidtNormSq (U * A * Uᴴ) = hilbertSchmidtNormSq A := by
  rw [hilbertSchmidtNormSq_eq_re_trace, hilbertSchmidtNormSq_eq_re_trace]
  congr 1
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  calc (U * (Aᴴ * Uᴴ) * (U * A * Uᴴ)).trace
      = (U * (Aᴴ * (Uᴴ * U) * A) * Uᴴ).trace := by simp only [Matrix.mul_assoc]
    _ = ((Aᴴ * A) * (Uᴴ * U)).trace := by
        rw [hU, Matrix.mul_one, Matrix.trace_mul_cycle, ← Matrix.mul_assoc, hU,
          Matrix.one_mul, Matrix.mul_one]
    _ = (Aᴴ * A).trace := by rw [hU, Matrix.mul_one]

/-- Simultaneous reindexing preserves the Hilbert–Schmidt norm. -/
theorem hilbertSchmidtNormSq_reindex {m n : Type*} [Fintype m] [Fintype n]
    (e : m ≃ n) (A : Matrix m m ℂ) :
    hilbertSchmidtNormSq (Matrix.reindex e e A) = hilbertSchmidtNormSq A := by
  unfold hilbertSchmidtNormSq
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← e.sum_comp]
  simp

/-- The phase-fixed Householder frame of the canonical projective vector is
unitary. -/
theorem physicalCoareaFrame_unitary {d : ℕ} (z : Fin (d - 1) → ℂ) :
    (physicalCoareaFrame z)ᴴ * physicalCoareaFrame z = 1 := by
  unfold physicalCoareaFrame
  exact phaseFixedHouseholderFrame_unitary _ _ (norm_canonicalProjectiveUnitVector z)
    (by rw [canonicalProjectiveUnitVector_selected]; simp)
    (canonicalProjectiveUnitVector_selected_re_pos z)

/-- Matrix of a decoded chart point: the selected-coordinate unreindexing of
`U_v diag(E, B) U_vᴴ`. -/
theorem hermitianOfFinCoordinates_selectedEigenpairFinCoordinateChartDecode
    {d : ℕ} (i : Fin d) (x : HermitianCoordinateSpace d) :
    (hermitianOfFinCoordinates d (selectedEigenpairFinCoordinateChartDecode i x)).1 =
      Matrix.reindex (selectedCoordinateEquiv i).symm (selectedCoordinateEquiv i).symm
        (physicalCoareaFrame (eigenpairIncidenceCoordinates i x).2.1 *
          Matrix.fromBlocks
            (((eigenpairIncidenceCoordinates i x).1 : ℂ) • (1 : Matrix Unit Unit ℂ)) 0 0
            (eigenpairIncidenceCoordinates i x).2.2.1 *
          (physicalCoareaFrame (eigenpairIncidenceCoordinates i x).2.1)ᴴ) := by
  change ((hermitianFinCoordinatesLinearEquiv d)
    (selectedEigenpairFinCoordinateChartDecode i x)).1 = _
  simp only [selectedEigenpairFinCoordinateChartDecode,
    selectedEigenpairCoordinateChartDecode, selectedEigenpairFinCoordinateLinearEquiv,
    LinearEquiv.trans_symm, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.apply_symm_apply]
  have h0 : eigenpairTangentColumn (0 : Fin (d - 1) → ℂ) = 0 := by
    funext a b
    rfl
  change Matrix.reindex _ _ (phaseFixedHouseholderFrame _ _ *
    (decodeEigenpairHermitianBlocks _).1 * (phaseFixedHouseholderFrame _ _)ᴴ) = _
  simp only [decodeEigenpairHermitianBlocks, h0, Matrix.conjTranspose_zero]
  rfl

/-- For Hermitian `F(E)`, the frame compression has the regression block form
`[[f, qᴴ], [q, F_v]]`. -/
theorem physicalCoareaFrameCompression_eq_fromBlocks {r d : ℕ}
    (H_R : Matrix (Fin r) (Fin r) ℂ)
    (C : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (E : ℝ) (z : Fin (d - 1) → ℂ)
    (hF : (physicalCoareaF H_R C V E).IsHermitian) :
    physicalCoareaFrameCompression H_R C V E z =
      Matrix.fromBlocks ((physicalCoarea_f H_R C V E z : ℂ) • (1 : Matrix Unit Unit ℂ))
        (eigenpairTangentColumn (physicalCoarea_q H_R C V E z))ᴴ
        (eigenpairTangentColumn (physicalCoarea_q H_R C V E z))
        (physicalCoareaFv H_R C V E z) := by
  have hC : (physicalCoareaFrameCompression H_R C V E z).IsHermitian := by
    unfold physicalCoareaFrameCompression
    exact Matrix.isHermitian_conjTranspose_mul_mul _ hF
  ext a b
  rcases a with a | a <;> rcases b with b | b
  · cases a; cases b
    simp only [Matrix.fromBlocks_apply₁₁, physicalCoarea_f, Matrix.smul_apply,
      Matrix.one_apply_eq, smul_eq_mul, mul_one]
    exact (hC.coe_re_apply_self _).symm
  · cases a
    simp only [Matrix.fromBlocks_apply₁₂, Matrix.conjTranspose_apply,
      eigenpairTangentColumn, physicalCoarea_q]
    exact (hC.apply _ _).symm
  · cases b
    rfl
  · rfl

/-- **Exact form of the paper's chart weight**.  For Hermitian `H_R, V` and `0 < t`, at every
incidence point `x` of chart `i`, with `E` the incidence energy, `v` the projective
vector and `M` the matrix of the decoded chart point,
`physicalSchurOuterWeight = c_{d,t} · exp(-‖M - F̃(E)‖²_HS/(2t)) · ⟨v, 𝒟(E) v⟩`,
where `F̃(E)` is `F(E) = V - Cᴴ(H_R-E)⁻¹C` unreindexed through chart `i`.
The Gaussian is centred at the energy-dependent Schur compression, and the
constant is `c_{d,t}`, not `Z_d(t)⁻¹`. -/
theorem physicalSchurOuterWeight_eq_matrixForm {r d : ℕ} {t : ℝ} (ht : 0 < t)
    (H_R : Matrix (Fin r) (Fin r) ℂ)
    (C : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (hR : H_R.IsHermitian) (hV : V.IsHermitian)
    (i : Fin d) (x : HermitianCoordinateSpace d) :
    physicalSchurOuterWeight t H_R C V i x =
      ENNReal.ofReal (coareaGaussianDensityConstant d t) *
        ENNReal.ofReal (Real.exp (-hilbertSchmidtNormSq
          ((hermitianOfFinCoordinates d (selectedEigenpairFinCoordinateChartDecode i x)).1 -
            Matrix.reindex (selectedCoordinateEquiv i).symm (selectedCoordinateEquiv i).symm
              (physicalCoareaF H_R C V (eigenpairIncidenceCoordinates i x).1)) / (2 * t))) *
        ENNReal.ofReal (physicalEigenpairCrossingQuadratic
          (physicalCoareaT H_R C (eigenpairIncidenceCoordinates i x).1)
          (eigenpairIncidenceCoordinates i x).2.1) := by
  set E := (eigenpairIncidenceCoordinates i x).1
  set z := (eigenpairIncidenceCoordinates i x).2.1
  set B := (eigenpairIncidenceCoordinates i x).2.2
  set U := physicalCoareaFrame z
  set F := physicalCoareaF H_R C V E
  have hU : Uᴴ * U = 1 := physicalCoareaFrame_unitary z
  have hU' : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  have hF : F.IsHermitian := physicalCoareaF_isHermitian H_R C V hR hV E
  have hHS : hilbertSchmidtNormSq
      ((hermitianOfFinCoordinates d (selectedEigenpairFinCoordinateChartDecode i x)).1 -
        Matrix.reindex (selectedCoordinateEquiv i).symm (selectedCoordinateEquiv i).symm F) =
      hilbertSchmidtNormSq
        (Matrix.fromBlocks ((E : ℂ) • (1 : Matrix Unit Unit ℂ)) 0 0 B.1 -
          physicalCoareaFrameCompression H_R C V E z) := by
    rw [hermitianOfFinCoordinates_selectedEigenpairFinCoordinateChartDecode]
    have hsub : ∀ A A' : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ,
        Matrix.reindex (selectedCoordinateEquiv i).symm (selectedCoordinateEquiv i).symm A -
          Matrix.reindex (selectedCoordinateEquiv i).symm (selectedCoordinateEquiv i).symm A' =
        Matrix.reindex (selectedCoordinateEquiv i).symm (selectedCoordinateEquiv i).symm
          (A - A') := by
      intro A A'
      ext a b
      simp
    rw [hsub, hilbertSchmidtNormSq_reindex]
    · have : U * Matrix.fromBlocks ((E : ℂ) • (1 : Matrix Unit Unit ℂ)) 0 0 B.1 * Uᴴ - F =
          U * (Matrix.fromBlocks ((E : ℂ) • (1 : Matrix Unit Unit ℂ)) 0 0 B.1 -
            physicalCoareaFrameCompression H_R C V E z) * Uᴴ := by
        unfold physicalCoareaFrameCompression
        rw [Matrix.mul_sub, Matrix.sub_mul]
        congr 1
        change F = U * (Uᴴ * F * U) * Uᴴ
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU', Matrix.one_mul,
          Matrix.mul_assoc, hU', Matrix.mul_one]
      rw [this, hilbertSchmidtNormSq_unitary_conj _ _ hU]
  unfold physicalSchurOuterWeight physicalEigenpairOuterWeight
  simp only []
  rw [hHS, physicalCoareaFrameCompression_eq_fromBlocks H_R C V E z hF,
    canonicalGaussianExponentialFactorization E _ _ B.1 _ ht,
    ENNReal.ofReal_mul (by unfold canonicalGaussianRegressionFactor; positivity)]
  ring

/-- With no exterior coupling the Schur crossing factor is `‖v‖² = 1`. -/
theorem physicalEigenpairCrossingQuadratic_zero {r d : ℕ} (z : Fin (d - 1) → ℂ) :
    physicalEigenpairCrossingQuadratic
      (0 : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ) z = 1 := by
  have h := EuclideanSpace.norm_sq_eq (canonicalProjectiveUnitVector z)
  rw [norm_canonicalProjectiveUnitVector, one_pow] at h
  unfold physicalEigenpairCrossingQuadratic schurClock
  simp only [Matrix.conjTranspose_zero, Matrix.zero_mul, add_zero, Matrix.one_mulVec,
    dotProduct, Complex.re_sum, Pi.star_apply]
  rw [h]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

/-- With no exterior coupling the Schur compression is `V`. -/
theorem physicalCoareaF_zero_coupling {r d : ℕ}
    (H_R : Matrix (Fin r) (Fin r) ℂ)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ) (E : ℝ) :
    physicalCoareaF H_R (0 : Matrix (Fin r) (Unit ⊕ Fin (d - 1)) ℂ) V E = V := by
  simp [physicalCoareaF]

/-- The normalization mismatch `κ_d(t) = c_{d,t} · Z_d(t)` between the
chart constant of the paper and the GUE matrix normalizer. -/
def chartGUENormalizationRatio (d : ℕ) (t : ℝ) : ℝ :=
  coareaGaussianDensityConstant d t * gueNormalizer d t

/-- `κ_d(t) = π^{d-1}/(d-1)! · Z_{d-1}(t)` for `d > 0`, `t > 0`. -/
theorem chartGUENormalizationRatio_eq {d : ℕ} (hd : 0 < d) {t : ℝ} (ht : 0 < t) :
    chartGUENormalizationRatio d t =
      Real.pi ^ (d - 1) / (d - 1).factorial * gueNormalizer (d - 1) t := by
  unfold chartGUENormalizationRatio
  rw [← projectiveJacobian_mul_gueNormalizerRatio hd ht]
  have hZ : gueNormalizer d t ≠ 0 := (gueNormalizer_pos ht).ne'
  field_simp

/-- Counter-computation: `κ_2(1) = π √(2π) ≠ 1`. -/
theorem chartGUENormalizationRatio_two_one_ne_one :
    chartGUENormalizationRatio 2 1 ≠ 1 := by
  rw [chartGUENormalizationRatio_eq (by norm_num) one_pos]
  have hpi := Real.two_le_pi
  have hZ : 1 ≤ gueNormalizer 1 1 := by
    unfold gueNormalizer
    norm_num
    exact Real.one_le_rpow (by nlinarith) (by norm_num)
  simp only [show (2 : ℕ) - 1 = 1 from rfl, pow_one, Nat.factorial_one, Nat.cast_one,
    div_one]
  apply ne_of_gt
  nlinarith

/-- The GUE density of `K - z₀` in terms of matrices. -/
theorem hermitianGUEDensity_sub_eq {d : ℕ} (t : ℝ) (K z₀ : HermitianCoordinateSpace d) :
    hermitianGUEDensity d t (hermitianOfFinCoordinates d (K - z₀)) =
      ENNReal.ofReal (Real.exp (-hilbertSchmidtNormSq
        ((hermitianOfFinCoordinates d K).1 - (hermitianOfFinCoordinates d z₀).1) /
          (2 * t)) / gueNormalizer d t) := by
  have h : (hermitianOfFinCoordinates d (K - z₀)).1 =
      (hermitianOfFinCoordinates d K).1 - (hermitianOfFinCoordinates d z₀).1 :=
    congrArg Subtype.val ((hermitianFinCoordinatesLinearEquiv d).map_sub K z₀)
  unfold hermitianGUEDensity
  rw [h]

/-- **Weight identification for the uncoupled readback.**  With `C = 0`,
Hermitian `H_R`, and `V` the chart-`i` reindexing of the residual block
`V₀ = H(z₀)`, the paper's chart weight at a decoded point `K` is
`κ_d(t)` times the fresh GUE density of `K - z₀`.  Thus the identity
`weight = density` holds iff `κ_d(t) = 1`; it fails e.g. at `d = 2, t = 1`
(`chartGUENormalizationRatio_two_one_ne_one`). -/
theorem physicalSchurOuterWeight_zero_coupling_eq {r d : ℕ} {t : ℝ} (ht : 0 < t)
    (H_R : Matrix (Fin r) (Fin r) ℂ)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ)
    (hR : H_R.IsHermitian) (hV : V.IsHermitian)
    (z₀ : HermitianCoordinateSpace d) (i : Fin d)
    (hVz : Matrix.reindex (selectedCoordinateEquiv i).symm (selectedCoordinateEquiv i).symm V =
      (hermitianOfFinCoordinates d z₀).1)
    (x : HermitianCoordinateSpace d) :
    physicalSchurOuterWeight t H_R 0 V i x =
      ENNReal.ofReal (chartGUENormalizationRatio d t) *
        hermitianGUEDensity d t
          (hermitianOfFinCoordinates d (selectedEigenpairFinCoordinateChartDecode i x - z₀)) := by
  rw [physicalSchurOuterWeight_eq_matrixForm ht H_R 0 V hR hV i x,
    physicalCoareaF_zero_coupling, hVz, physicalCoareaT, Matrix.mul_zero,
    physicalEigenpairCrossingQuadratic_zero, ENNReal.ofReal_one, mul_one,
    hermitianGUEDensity_sub_eq]
  have hZ := gueNormalizer_pos (d := d) ht
  unfold chartGUENormalizationRatio
  have hc : 0 ≤ coareaGaussianDensityConstant d t := by
    unfold coareaGaussianDensityConstant
    positivity
  rw [← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_mul (mul_nonneg hc hZ.le)]
  congr 1
  field_simp

/-- The weight identification `weight = density` is false: for `d = 2`, `t = 1`, `C = 0`,
`V = 0`, residual `z₀ = 0` and every chart point, the transported chart
weight differs from the fresh GUE density. -/
theorem chartTransportWeight_ne_hermitianGUEDensity {r : ℕ}
    (H_R : Matrix (Fin r) (Fin r) ℂ) (hR : H_R.IsHermitian) (i : Fin 2)
    (x : HermitianCoordinateSpace 2) :
    eigenpairChartTransportWeight i {x}
        (physicalSchurOuterWeight 1 H_R 0 0 i)
        (selectedEigenpairFinCoordinateChartDecode i x) ≠
      hermitianGUEDensity 2 1
        (hermitianOfFinCoordinates 2 (selectedEigenpairFinCoordinateChartDecode i x - 0)) := by
  have hz : Matrix.reindex (selectedCoordinateEquiv i).symm (selectedCoordinateEquiv i).symm
      (0 : Matrix (Unit ⊕ Fin (2 - 1)) (Unit ⊕ Fin (2 - 1)) ℂ) =
      (hermitianOfFinCoordinates 2 0).1 := by
    have h0 := congrArg Subtype.val ((hermitianFinCoordinatesLinearEquiv 2).map_zero)
    ext a b
    exact (congrFun (congrFun h0 a) b).symm
  rw [eigenpairChartTransportWeight_decode i {x} _ (Set.injOn_singleton _ _) rfl,
    physicalSchurOuterWeight_zero_coupling_eq one_pos H_R 0 hR
      (Matrix.isHermitian_zero) 0 i hz x]
  intro h
  set D := hermitianGUEDensity 2 1
    (hermitianOfFinCoordinates 2 (selectedEigenpairFinCoordinateChartDecode i x - 0))
  have hD0 : D ≠ 0 := by
    simp only [D, hermitianGUEDensity, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact div_pos (Real.exp_pos _) (gueNormalizer_pos one_pos)
  have hDtop : D ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpos : 0 ≤ chartGUENormalizationRatio 2 1 := by
    unfold chartGUENormalizationRatio coareaGaussianDensityConstant
    have := gueNormalizer_pos (d := 2) one_pos
    positivity
  have hr := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hpos] at hr
  have hDr : 0 < D.toReal := ENNReal.toReal_pos hD0 hDtop
  apply chartGUENormalizationRatio_two_one_ne_one
  have h0 : (chartGUENormalizationRatio 2 1 - 1) * D.toReal = 0 := by linarith
  rcases mul_eq_zero.mp h0 with h0 | h0
  · linarith
  · linarith

/-!
### The joined lintegral equality
-/

/-- The finite-coordinate chart decoder is Borel measurable. -/
theorem measurable_selectedEigenpairFinCoordinateChartDecode {d : ℕ} (i : Fin d) :
    Measurable (selectedEigenpairFinCoordinateChartDecode i) :=
  (Differentiable.continuous fun x =>
    differentiableAt_selectedEigenpairFinCoordinateChartDecode i x).measurable

/-- Every decoded piece of a physical pole/chart cover is measurable
(Lusin–Souslin: injective Borel image of a Borel set). -/
theorem PhysicalCoareaPoleChartCover.measurableSet_decodedImage
    {κ : Type*} [Fintype κ] {dR d : ℕ} {α : ℕ} {R : HermitianCoordinateSpace dR}
    (cover : PhysicalCoareaPoleChartCover κ (d := d) α R)
    (a : κ) (rank : HermitianEigenRank d) (p : OrderedEigenlineChartIndex d) :
    MeasurableSet (selectedEigenpairFinCoordinateChartDecode (ofLex p).1 ''
      cover.source a rank p) :=
  MeasurableSet.image_of_measurable_injOn (cover.source_measurable a rank p)
    (measurable_selectedEigenpairFinCoordinateChartDecode _)
    ((injOn_selectedEigenpairFinCoordinateChartDecode_fixedRankSource rank p).mono
      (cover.source_in_chart a rank p))

/-- **Joined chart equality on the decoded union, uncoupled readback**.

Hypotheses: `0 < t`; exterior coupling `C = 0`; `H_R`, `V` Hermitian; and
`hVz`: for every chart index `i`, the chart-`i` unreindexing of `V` is the
residual block `H(z₀)` (the paper's chart sum uses one `V` for all charts).
Then `κ_d(t)` times the Lebesgue integral of the fresh GUE density of
`K - z₀` against the phase-free observable, over the disjoint union of the
decoded cover pieces, equals the paper's chart sum.  The factor
`κ_d(t) = c_{d,t} Z_d(t)` is the exact normalization mismatch
(`chartGUENormalizationRatio_eq`).  Fixed `d`, ranks, cover; no limit. -/
theorem lintegral_decodedUnion_freshGUE_eq_manuscriptChartSum
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {r d : ℕ} (α : ℕ) (R : HermitianCoordinateSpace r)
    (cover : PhysicalCoareaPoleChartCover κ α R)
    {t : ℝ} (ht : 0 < t)
    (H_R : Matrix (Fin r) (Fin r) ℂ) (hR : H_R.IsHermitian)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ) (hV : V.IsHermitian)
    (z₀ : HermitianCoordinateSpace d)
    (hVz : ∀ i : Fin d,
      Matrix.reindex (selectedCoordinateEquiv i).symm (selectedCoordinateEquiv i).symm V =
        (hermitianOfFinCoordinates d z₀).1)
    (ρ : HermitianEigenRank d)
    (Ψ : Matrix (Fin d) (Fin d) ℂ → ℝ≥0∞) (hΨ : Measurable Ψ) :
    ENNReal.ofReal (chartGUENormalizationRatio d t) *
        ∫⁻ K in cover.decodedUnion,
          hermitianGUEDensity d t (hermitianOfFinCoordinates d (K - z₀)) *
            phaseFreeOrderedProjectorObservable ρ Ψ K =
      ∑ a : κ, ∑ rank : HermitianEigenRank d,
        ∑ p : OrderedEigenlineChartIndex d,
        ∫⁻ x in cover.source a rank p,
          physicalSchurManuscriptDensity t H_R 0 V (ofLex p).1 x *
            phaseFreeOrderedProjectorObservable ρ Ψ
              (selectedEigenpairFinCoordinateChartDecode (ofLex p).1 x) := by
  rw [← lintegral_physicalSchurCoarea_manuscript_finiteCover α R cover t H_R 0 V ρ Ψ hΨ]
  have hU := lintegral_iUnion (μ := volume)
    (s := fun arp : κ × HermitianEigenRank d × OrderedEigenlineChartIndex d =>
      selectedEigenpairFinCoordinateChartDecode (ofLex arp.2.2).1 ''
        cover.source arp.1 arp.2.1 arp.2.2)
    (fun arp => cover.measurableSet_decodedImage arp.1 arp.2.1 arp.2.2)
    cover.decodedImage_pairwise_disjoint
    (fun K => hermitianGUEDensity d t (hermitianOfFinCoordinates d (K - z₀)) *
      phaseFreeOrderedProjectorObservable ρ Ψ K)
  change ENNReal.ofReal _ * ∫⁻ K in ⋃ arp : κ × HermitianEigenRank d ×
      OrderedEigenlineChartIndex d,
      selectedEigenpairFinCoordinateChartDecode (ofLex arp.2.2).1 ''
        cover.source arp.1 arp.2.1 arp.2.2, _ = _
  rw [hU, tsum_fintype, Finset.mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun rank _ => Finset.sum_congr rfl fun p _ => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun (cover.measurableSet_decodedImage a rank p) ?_
  rintro K ⟨x, hx, rfl⟩
  have hinj := (injOn_selectedEigenpairFinCoordinateChartDecode_fixedRankSource rank p).mono
    (cover.source_in_chart a rank p)
  dsimp only
  rw [eigenpairChartTransportWeight_decode _ _ _ hinj hx,
    physicalSchurOuterWeight_zero_coupling_eq ht H_R V hR hV z₀ _ (hVz _) x, mul_assoc]

/-- **Joined fresh-GUE = chart sum, conditional on an a.e. cover**.

This is a conditional integration theorem: besides the uncoupled readback
hypotheses of `lintegral_decodedUnion_freshGUE_eq_manuscriptChartSum`, it takes
the named hypothesis `hcover`, that the decoded cover pieces exhaust Lebesgue
almost all total-block coordinates.  `PhysicalCoareaPoleChartCover` does not
provide `hcover` (its pieces are restricted to an energy region, a rank sector
and gap-free sources).  Under these hypotheses, `κ_d(t)` times the fresh GUE
average of the phase-free observable of `V₀ + G`, `V₀ = H(z₀)`, is the
chart sum of the paper. -/
theorem freshGUE_eq_manuscriptChartSum_of_aeCover
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {r d : ℕ} (α : ℕ) (R : HermitianCoordinateSpace r)
    (cover : PhysicalCoareaPoleChartCover κ α R)
    (hcover : volume (cover.decodedUnionᶜ) = 0)
    {t : ℝ} (ht : 0 < t)
    (H_R : Matrix (Fin r) (Fin r) ℂ) (hR : H_R.IsHermitian)
    (V : Matrix (Unit ⊕ Fin (d - 1)) (Unit ⊕ Fin (d - 1)) ℂ) (hV : V.IsHermitian)
    (z₀ : HermitianCoordinateSpace d)
    (hVz : ∀ i : Fin d,
      Matrix.reindex (selectedCoordinateEquiv i).symm (selectedCoordinateEquiv i).symm V =
        (hermitianOfFinCoordinates d z₀).1)
    (ρ : HermitianEigenRank d)
    (Ψ : Matrix (Fin d) (Fin d) ℂ → ℝ≥0∞) (hΨ : Measurable Ψ) :
    ENNReal.ofReal (chartGUENormalizationRatio d t) *
        ∫⁻ g, physicalMatrixPhaseFreeObservable ρ Ψ
          (hermitianMatrixAdd (hermitianOfFinCoordinates d z₀) (hermitianGUEBlock d g))
          ∂hermitianGUECoordinateMeasure d t ht.le =
      ∑ a : κ, ∑ rank : HermitianEigenRank d,
        ∑ p : OrderedEigenlineChartIndex d,
        ∫⁻ x in cover.source a rank p,
          physicalSchurManuscriptDensity t H_R 0 V (ofLex p).1 x *
            phaseFreeOrderedProjectorObservable ρ Ψ
              (selectedEigenpairFinCoordinateChartDecode (ofLex p).1 x) := by
  rw [← lintegral_decodedUnion_freshGUE_eq_manuscriptChartSum α R cover ht H_R hR V hV
    z₀ hVz ρ Ψ hΨ, lintegral_hermitianGUE_residual_translate d ht,
    Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hcover)]
  congr 1
  refine lintegral_congr fun x => ?_
  unfold physicalMatrixPhaseFreeObservable
  rw [hermitianFinCoordinateReadback_hermitianOfFinCoordinates]

end CoareaNative.BlockBand
