module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.TwoResolventGaussianIBPFubini

/-!
# Conditional product rule and full-product GUE loop identity

Gaussian integration by parts in each real coordinate of the normalized GUE product law, for the
two-resolvent word, via conditioning on the complementary coordinates; summing over coordinates
gives the aggregate loop identity with covariance kernel contracted to `N⁻¹ Tr(X) I`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.External.CEH

open Matrix MeasureTheory ProbabilityTheory
open CEHNative.BlockBand
open scoped BigOperators ComplexConjugate NNReal ComplexOrder

/-- Relabel the finite GUE coordinates by `e` and split the chosen coordinate
`k₀` from all complementary coordinates. -/
def normalizedGUESplitMap {N n : ℕ}
    (e : Fin (n + 1) ≃ Fin (Fintype.card (HermitianCoordinate N)))
    (k₀ : Fin (n + 1)) :
    HermitianCoordinateSpace N ≃ᵐ
      ℝ × (Fin n → ℝ) :=
  (MeasurableEquiv.piCongrLeft
      (fun _ : Fin (Fintype.card (HermitianCoordinate N)) => ℝ) e).symm |>.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) k₀)

/-- `measurePreserving_piFinSuccAbove`, specialized to an arbitrary
normalized GUE coordinate after an arbitrary finite relabeling.  Choosing
`e k₀ = k` isolates any requested coordinate `k`. -/
theorem measurePreserving_normalizedGUESplitMap
    {N n : ℕ} (hN : 0 < N)
    (e : Fin (n + 1) ≃ Fin (Fintype.card (HermitianCoordinate N)))
    (k₀ : Fin (n + 1)) :
    MeasurePreserving (normalizedGUESplitMap e k₀)
      (hermitianGUECoordinateMeasure N (1 / (N : ℝ)) (by positivity))
      ((gaussianReal 0
          (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
            (by positivity) (e k₀))).prod
        (Measure.pi fun j : Fin n =>
          gaussianReal 0
            (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
              (by positivity) (e (k₀.succAbove j))))) := by
  let μ := fun k : Fin (Fintype.card (HermitianCoordinate N)) =>
    gaussianReal 0
      (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
        (by positivity) k)
  have hreindex := (measurePreserving_piCongrLeft μ e).symm
  have hsplit := measurePreserving_piFinSuccAbove (fun i => μ (e i)) k₀
  exact hsplit.comp hreindex

/-- Exact change of variables from the full normalized GUE product to a
chosen coordinate times its complementary-coordinate product. -/
theorem integral_normalizedGUE_eq_split
    {N n : ℕ} (hN : 0 < N)
    (e : Fin (n + 1) ≃ Fin (Fintype.card (HermitianCoordinate N)))
    (k₀ : Fin (n + 1)) (Φ : HermitianCoordinateSpace N → ℂ) :
    (∫ y, Φ y
      ∂hermitianGUECoordinateMeasure N (1 / (N : ℝ)) (by positivity)) =
      ∫ p : ℝ × (Fin n → ℝ),
        Φ ((normalizedGUESplitMap e k₀).symm p)
      ∂((gaussianReal 0
          (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
            (by positivity) (e k₀))).prod
        (Measure.pi fun j : Fin n =>
          gaussianReal 0
            (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
              (by positivity) (e (k₀.succAbove j))))) := by
  have h := (measurePreserving_normalizedGUESplitMap hN e k₀).integral_comp'
    (fun p : ℝ × (Fin n → ℝ) =>
      Φ ((normalizedGUESplitMap e k₀).symm p))
  simpa using h

/-- Reconstructing a split configuration inserts its distinguished coordinate
into a fixed complementary background. -/
theorem normalizedGUESplitMap_symm_eq_update
    {N n : ℕ}
    (e : Fin (n + 1) ≃ Fin (Fintype.card (HermitianCoordinate N)))
    (k₀ : Fin (n + 1)) (x : ℝ) (c : Fin n → ℝ) :
    (normalizedGUESplitMap e k₀).symm (x, c) =
      Function.update ((normalizedGUESplitMap e k₀).symm (0, c)) (e k₀) x := by
  ext k
  simp only [normalizedGUESplitMap, MeasurableEquiv.trans_symm,
    MeasurableEquiv.coe_trans, Function.comp_apply,
    MeasurableEquiv.piFinSuccAbove_symm_apply]
  change (MeasurableEquiv.piCongrLeft (fun _ : Fin (Fintype.card (HermitianCoordinate N)) => ℝ) e)
      ((Fin.insertNthEquiv (fun _ : Fin (n + 1) => ℝ) k₀) (x, c)) k =
    Function.update
      ((MeasurableEquiv.piCongrLeft (fun _ : Fin (Fintype.card (HermitianCoordinate N)) => ℝ) e)
        ((Fin.insertNthEquiv (fun _ : Fin (n + 1) => ℝ) k₀) (0, c)))
      (e k₀) x k
  by_cases hk : k = e k₀
  · subst k
    rw [MeasurableEquiv.piCongrLeft_apply_apply]
    simp [Fin.insertNthEquiv]
  · have hk' : e.symm k ≠ k₀ := by
      intro h
      apply hk
      simpa using congrArg e h
    rw [← e.apply_symm_apply k]
    rw [MeasurableEquiv.piCongrLeft_apply_apply]
    have hbase :
        (MeasurableEquiv.piCongrLeft
          (fun _ : Fin (Fintype.card (HermitianCoordinate N)) => ℝ) e)
            ((Fin.insertNthEquiv (fun _ : Fin (n + 1) => ℝ) k₀) (0, c)) k =
          ((Fin.insertNthEquiv (fun _ : Fin (n + 1) => ℝ) k₀) (0, c)) (e.symm k) := by
      conv_lhs => rw [← e.apply_symm_apply k]
      rw [MeasurableEquiv.piCongrLeft_apply_apply]
    simp only [Function.update, e.apply_symm_apply]
    simp only [hk]
    simp only [dite_false]
    rw [hbase]
    obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq hk'
    rw [← hl]
    simp

/-- The displayed two-resolvent product-rule observable is the real coordinate derivative of
the conditioned full reconstructed word. -/
theorem hasDerivAt_fullGUEPlainTwoResolvent_conditioned
    {N : ℕ}
    (H₁ H₂ A : Matrix (Fin N) (Fin N) ℂ)
    (hH₁ : H₁.IsHermitian) (hH₂ : H₂.IsHermitian)
    {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (k : Fin (Fintype.card (HermitianCoordinate N)))
    (i j : Fin N) (y : HermitianCoordinateSpace N) (x : ℝ) :
    HasDerivAt
      (fun u : ℝ => fullGUEPlainTwoResolventEntry
        H₁ H₂ A z₁ z₂ i j (Function.update y k u))
      (fullGUEPlainTwoResolventDerivativeEntry
        H₁ H₂ A z₁ z₂ k i j (Function.update y k x)) x := by
  let D := gueCoordinateDirection N k
  let B₁ := H₁ + complementaryGUEBackground N k y -
    z₁ • (1 : Matrix (Fin N) (Fin N) ℂ)
  let B₂ := H₂ + complementaryGUEBackground N k y -
    z₂ • (1 : Matrix (Fin N) (Fin N) ℂ)
  let G₁ := coordinateResolvent B₁ D
  let G₂ := coordinateResolvent B₂ D
  have hB₁ (u : ℝ) : IsUnit (coordinatePencil B₁ D u).det :=
    isUnit_det_coordinateHermitianPencil
      (H₁ + complementaryGUEBackground N k y) D
      (hH₁.add (complementaryGUEBackground_isHermitian N k y))
      (gueCoordinateDirection_isHermitian N k) hz₁ u
  have hB₂ (u : ℝ) : IsUnit (coordinatePencil B₂ D u).det :=
    isUnit_det_coordinateHermitianPencil
      (H₂ + complementaryGUEBackground N k y) D
      (hH₂.add (complementaryGUEBackground_isHermitian N k y))
      (gueCoordinateDirection_isHermitian N k) hz₂ u
  have hG₁ (p q : Fin N) :
      HasDerivAt (fun u => G₁ u p q) (-(G₁ x * D * G₁ x) p q) x :=
    hasDerivAt_coordinateResolvent_entry B₁ D p q x (hB₁ x)
  have hG₂ (p q : Fin N) :
      HasDerivAt (fun u => G₂ u p q) (-(G₂ x * D * G₂ x) p q) x :=
    hasDerivAt_coordinateResolvent_entry B₂ D p q x (hB₂ x)
  have hword : HasDerivAt
      (fun u => (G₁ u * A * G₂ u) i j)
      (((-(G₁ x * D * G₁ x)) * A * G₂ x +
        G₁ x * A * (-(G₂ x * D * G₂ x))) i j) x := by
    simp only [Matrix.add_apply, Matrix.mul_apply]
    convert HasDerivAt.fun_sum (u := Finset.univ) (x := x)
      (A := fun b u => (∑ a, G₁ u i a * A a b) * G₂ u b j)
      (A' := fun b =>
        (∑ a, (-(G₁ x * D * G₁ x)) i a * A a b) * G₂ x b j +
        (∑ a, G₁ x i a * A a b) * (-(G₂ x * D * G₂ x)) b j)
      (fun b hb => by
        apply HasDerivAt.mul
        · convert HasDerivAt.fun_sum (u := Finset.univ) (x := x)
            (A := fun a u => G₁ u i a * A a b)
            (A' := fun a => (-(G₁ x * D * G₁ x)) i a * A a b)
            (fun a ha => (hG₁ i a).mul_const (A a b)) using 1
        · exact hG₂ b j) using 1
    all_goals simp only [Finset.sum_add_distrib]
  have hfun :
      (fun u : ℝ => fullGUEPlainTwoResolventEntry
        H₁ H₂ A z₁ z₂ i j (Function.update y k u)) =
      (fun u => (G₁ u * A * G₂ u) i j) := by
    funext u
    unfold fullGUEPlainTwoResolventEntry
    rw [fullGUEResolvent_update_eq_coordinateResolvent,
      fullGUEResolvent_update_eq_coordinateResolvent]
  rw [hfun]
  convert hword using 1
  unfold fullGUEPlainTwoResolventDerivativeEntry
  rw [fullGUEResolvent_update_eq_coordinateResolvent,
    fullGUEResolvent_update_eq_coordinateResolvent]

/-- Conditional scalar Gaussian integration by parts for the two-resolvent section, with all
three density-integrability premises discharged by the nonreal resolvent bounds. -/
theorem normalizedGUEFullTwoResolvent_conditionalCoordinate_IBP
    {N : ℕ} (hN : 0 < N)
    (H₁ H₂ A : Matrix (Fin N) (Fin N) ℂ)
    (hH₁ : H₁.IsHermitian) (hH₂ : H₂.IsHermitian)
    {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (k : Fin (Fintype.card (HermitianCoordinate N)))
    (i j : Fin N) (y : HermitianCoordinateSpace N) :
    (∫ x : ℝ, (x : ℂ) *
        fullGUEPlainTwoResolventEntry H₁ H₂ A z₁ z₂ i j
          (Function.update y k x)
      ∂gaussianReal 0
        (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
          (by positivity) k)) =
      (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
        (by positivity) k : ℝ) *
        ∫ x : ℝ,
          fullGUEPlainTwoResolventDerivativeEntry
            H₁ H₂ A z₁ z₂ k i j (Function.update y k x)
        ∂gaussianReal 0
          (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
            (by positivity) k) := by
  let v := hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
    (by positivity) k
  let f : ℝ → ℂ := fun x =>
    fullGUEPlainTwoResolventEntry H₁ H₂ A z₁ z₂ i j
      (Function.update y k x)
  let f' : ℝ → ℂ := fun x =>
    fullGUEPlainTwoResolventDerivativeEntry H₁ H₂ A z₁ z₂ k i j
      (Function.update y k x)
  have hv : v ≠ 0 := ne_of_gt
    (hermitianGUEFinCoordinateVariance_pos N
      (show 0 < 1 / (N : ℝ) by positivity) k)
  have hderiv (x : ℝ) : HasDerivAt f (f' x) x :=
    hasDerivAt_fullGUEPlainTwoResolvent_conditioned
      H₁ H₂ A hH₁ hH₂ hz₁ hz₂ k i j y x
  have hfcont : Continuous f := by
    rw [continuous_iff_continuousAt]
    exact fun x => (hderiv x).continuousAt
  have hfpmeas : AEStronglyMeasurable f' := by
    apply Measurable.aestronglyMeasurable
    exact (measurable_fullGUEPlainTwoResolventDerivativeEntry
      H₁ H₂ A z₁ z₂ k i j).comp (by fun_prop)
  let C := |z₁.im|⁻¹ * |z₂.im|⁻¹ *
    ∑ a : Fin N, ∑ b : Fin N, ‖A a b‖
  let C' :=
    (|z₁.im|⁻¹ ^ 2 *
        ∑ a : Fin N, ∑ b : Fin N, ‖gueCoordinateDirection N k a b‖) *
        |z₂.im|⁻¹ * (∑ a : Fin N, ∑ b : Fin N, ‖A a b‖) +
      |z₁.im|⁻¹ *
        (|z₂.im|⁻¹ ^ 2 *
          ∑ a : Fin N, ∑ b : Fin N, ‖gueCoordinateDirection N k a b‖) *
          (∑ a : Fin N, ∑ b : Fin N, ‖A a b‖)
  have hfbd : ∀ᵐ x : ℝ, ‖f x‖ ≤ C :=
    ae_of_all _ fun x =>
      norm_fullGUEPlainTwoResolventEntry_le
        H₁ H₂ A hH₁ hH₂ hz₁ hz₂ i j (Function.update y k x)
  have hfpbd : ∀ᵐ x : ℝ, ‖f' x‖ ≤ C' :=
    ae_of_all _ fun x =>
      norm_fullGUEPlainTwoResolventDerivativeEntry_le
        H₁ H₂ A hH₁ hH₂ hz₁ hz₂ k i j (Function.update y k x)
  have hpdf : Integrable
      (fun x : ℝ => ((gaussianPDFReal 0 v x : ℝ) : ℂ)) :=
    (integrable_gaussianPDFReal 0 v).ofReal
  have hxpdf : Integrable
      (fun x : ℝ => ((x * gaussianPDFReal 0 v x : ℝ) : ℂ)) :=
    (integrable_mul_centeredGaussianPDFReal v hv).ofReal
  exact realGaussianIntegrationByParts_density v hv f f' hderiv
    (hxpdf.mul_bdd hfcont.aestronglyMeasurable hfbd)
    (hpdf.mul_bdd hfpmeas hfpbd)
    (hpdf.mul_bdd hfcont.aestronglyMeasurable hfbd)

/-- Full-product scalar Gaussian IBP in an arbitrary selected normalized
GUE coordinate.  The relabeling hypothesis `e k₀ = k` is encoded by writing
the selected coordinate as `e k₀`; thus no distinguished-coordinate
assumption remains. -/
theorem normalizedGUEFullTwoResolvent_coordinate_IBP
    {N n : ℕ} (hN : 0 < N)
    (e : Fin (n + 1) ≃ Fin (Fintype.card (HermitianCoordinate N)))
    (k₀ : Fin (n + 1))
    (H₁ H₂ A : Matrix (Fin N) (Fin N) ℂ)
    (hH₁ : H₁.IsHermitian) (hH₂ : H₂.IsHermitian)
    {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (i j : Fin N) :
    (∫ y : HermitianCoordinateSpace N, (y (e k₀) : ℂ) *
        fullGUEPlainTwoResolventEntry H₁ H₂ A z₁ z₂ i j y
      ∂hermitianGUECoordinateMeasure N (1 / (N : ℝ)) (by positivity)) =
      (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
        (by positivity) (e k₀) : ℝ) *
        ∫ y : HermitianCoordinateSpace N,
          fullGUEPlainTwoResolventDerivativeEntry
            H₁ H₂ A z₁ z₂ (e k₀) i j y
        ∂hermitianGUECoordinateMeasure N (1 / (N : ℝ)) (by positivity) := by
  let μ := hermitianGUECoordinateMeasure N (1 / (N : ℝ)) (by positivity)
  let ν :=
    (gaussianReal 0
      (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
        (by positivity) (e k₀))).prod
      (Measure.pi fun l : Fin n =>
        gaussianReal 0
          (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
            (by positivity) (e (k₀.succAbove l))))
  let S := normalizedGUESplitMap e k₀
  have hmp : MeasurePreserving S μ ν :=
    measurePreserving_normalizedGUESplitMap hN e k₀
  have hleftFull : Integrable (fun y : HermitianCoordinateSpace N =>
      (y (e k₀) : ℂ) *
        fullGUEPlainTwoResolventEntry H₁ H₂ A z₁ z₂ i j y) μ :=
    integrable_coordinate_mul_fullGUEPlainTwoResolventEntry
      H₁ H₂ A hH₁ hH₂ hz₁ hz₂ (e k₀) i j
  have hrightFull : Integrable
      (fullGUEPlainTwoResolventDerivativeEntry
        H₁ H₂ A z₁ z₂ (e k₀) i j) μ :=
    integrable_fullGUEPlainTwoResolventDerivativeEntry
      H₁ H₂ A hH₁ hH₂ hz₁ hz₂ (e k₀) i j
  have hleftSplit : Integrable (fun p : ℝ × (Fin n → ℝ) =>
      (((S.symm p) (e k₀) : ℝ) : ℂ) *
        fullGUEPlainTwoResolventEntry H₁ H₂ A z₁ z₂ i j (S.symm p)) ν := by
    change Integrable ((fun y : HermitianCoordinateSpace N =>
      (y (e k₀) : ℂ) *
        fullGUEPlainTwoResolventEntry H₁ H₂ A z₁ z₂ i j y) ∘ S.symm) ν
    exact hmp.symm.integrable_comp_of_integrable hleftFull
  have hrightSplit : Integrable (fun p : ℝ × (Fin n → ℝ) =>
      fullGUEPlainTwoResolventDerivativeEntry
        H₁ H₂ A z₁ z₂ (e k₀) i j (S.symm p)) ν := by
    change Integrable
      (fullGUEPlainTwoResolventDerivativeEntry
        H₁ H₂ A z₁ z₂ (e k₀) i j ∘ S.symm) ν
    exact hmp.symm.integrable_comp_of_integrable hrightFull
  rw [integral_normalizedGUE_eq_split hN e k₀]
  rw [integral_normalizedGUE_eq_split hN e k₀]
  change (∫ p : ℝ × (Fin n → ℝ),
      (((S.symm p) (e k₀) : ℝ) : ℂ) *
        fullGUEPlainTwoResolventEntry H₁ H₂ A z₁ z₂ i j (S.symm p) ∂ν) =
    (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
      (by positivity) (e k₀) : ℝ) *
      ∫ p : ℝ × (Fin n → ℝ),
        fullGUEPlainTwoResolventDerivativeEntry
          H₁ H₂ A z₁ z₂ (e k₀) i j (S.symm p) ∂ν
  rw [integral_prod_symm _ hleftSplit, integral_prod_symm _ hrightSplit]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with c
  have hcond := normalizedGUEFullTwoResolvent_conditionalCoordinate_IBP
    hN H₁ H₂ A hH₁ hH₂ hz₁ hz₂ (e k₀) i j (S.symm (0, c))
  convert hcond using 1
  · apply integral_congr_ae
    filter_upwards with x
    rw [show S.symm (x, c) =
      Function.update (S.symm (0, c)) (e k₀) x by
        exact normalizedGUESplitMap_symm_eq_update e k₀ x c]
    simp
  · apply congrArg
    apply integral_congr_ae
    filter_upwards with x
    rw [show S.symm (x, c) =
      Function.update (S.symm (0, c)) (e k₀) x by
        exact normalizedGUESplitMap_symm_eq_update e k₀ x c]

/-- Full-product scalar Gaussian IBP for every normalized GUE coordinate,
with the finite-product splitting data constructed internally. -/
theorem normalizedGUEFullTwoResolvent_coordinate_IBP_arbitrary
    {N : ℕ} (hN : 0 < N)
    (H₁ H₂ A : Matrix (Fin N) (Fin N) ℂ)
    (hH₁ : H₁.IsHermitian) (hH₂ : H₂.IsHermitian)
    {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (k : Fin (Fintype.card (HermitianCoordinate N)))
    (i j : Fin N) :
    (∫ y : HermitianCoordinateSpace N, (y k : ℂ) *
        fullGUEPlainTwoResolventEntry H₁ H₂ A z₁ z₂ i j y
      ∂hermitianGUECoordinateMeasure N (1 / (N : ℝ)) (by positivity)) =
      (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
        (by positivity) k : ℝ) *
        ∫ y : HermitianCoordinateSpace N,
          fullGUEPlainTwoResolventDerivativeEntry
            H₁ H₂ A z₁ z₂ k i j y
        ∂hermitianGUECoordinateMeasure N (1 / (N : ℝ)) (by positivity) := by
  let c := Fintype.card (HermitianCoordinate N)
  have hc : 1 ≤ c := by
    exact (Nat.one_le_iff_ne_zero).2 (by
      intro h
      have : IsEmpty (Fin c) := Fin.isEmpty_iff.mpr h
      exact this.false k)
  have hcEq : c - 1 + 1 = c := Nat.sub_add_cancel hc
  let e : Fin (c - 1 + 1) ≃ Fin c := Equiv.cast (congrArg Fin hcEq)
  let k₀ : Fin (c - 1 + 1) := e.symm k
  simpa [e, k₀] using
    (normalizedGUEFullTwoResolvent_coordinate_IBP
      (n := c - 1) hN e k₀ H₁ H₂ A hH₁ hH₂ hz₁ hz₂ i j)

/-- Tonelli/Fubini assembly of the coordinate identities under the full normalized product law.
Both finite coordinate sums are inside the expectation; the variance on each diagonal or paired
real/imaginary coordinate is therefore retained exactly. -/
theorem normalizedGUEFullTwoResolvent_sumCoordinate_IBP
    {N : ℕ} (hN : 0 < N)
    (H₁ H₂ A : Matrix (Fin N) (Fin N) ℂ)
    (hH₁ : H₁.IsHermitian) (hH₂ : H₂.IsHermitian)
    {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (i j : Fin N) :
    (∫ y : HermitianCoordinateSpace N,
        ∑ k : Fin (Fintype.card (HermitianCoordinate N)),
          (y k : ℂ) *
            fullGUEPlainTwoResolventEntry H₁ H₂ A z₁ z₂ i j y
      ∂hermitianGUECoordinateMeasure N (1 / (N : ℝ)) (by positivity)) =
      ∫ y : HermitianCoordinateSpace N,
        ∑ k : Fin (Fintype.card (HermitianCoordinate N)),
          (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
            (by positivity) k : ℂ) *
            fullGUEPlainTwoResolventDerivativeEntry
              H₁ H₂ A z₁ z₂ k i j y
      ∂hermitianGUECoordinateMeasure N (1 / (N : ℝ)) (by positivity) := by
  let μ := hermitianGUECoordinateMeasure N (1 / (N : ℝ)) (by positivity)
  have hleft (k : Fin (Fintype.card (HermitianCoordinate N))) :
      Integrable (fun y : HermitianCoordinateSpace N =>
        (y k : ℂ) *
          fullGUEPlainTwoResolventEntry H₁ H₂ A z₁ z₂ i j y) μ :=
    integrable_coordinate_mul_fullGUEPlainTwoResolventEntry
      H₁ H₂ A hH₁ hH₂ hz₁ hz₂ k i j
  have hright (k : Fin (Fintype.card (HermitianCoordinate N))) :
      Integrable (fun y : HermitianCoordinateSpace N =>
        (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
          (by positivity) k : ℂ) *
          fullGUEPlainTwoResolventDerivativeEntry
            H₁ H₂ A z₁ z₂ k i j y) μ :=
    (integrable_fullGUEPlainTwoResolventDerivativeEntry
      H₁ H₂ A hH₁ hH₂ hz₁ hz₂ k i j).const_mul _
  rw [integral_finsetSum Finset.univ (fun k hk => hleft k)]
  rw [integral_finsetSum Finset.univ (fun k hk => hright k)]
  apply Finset.sum_congr rfl
  intro k hk
  simpa only [μ, integral_const_mul] using
    (normalizedGUEFullTwoResolvent_coordinate_IBP_arbitrary
      hN H₁ H₂ A hH₁ hH₂ hz₁ hz₂ k i j)

/-- **Unconditional normalized GUE aggregate loop identity.** Finite coordinate summation is
commuted through the full normalized product integral, and the exact diagonal plus
paired-real/imaginary covariance kernel is contracted to `N⁻¹ Tr(X) I`. Here `X` is the
common-background two-resolvent word. -/
theorem normalizedGUEFullTwoResolvent_aggregateLoop
    {N : ℕ} (hN : 0 < N)
    (H₁ H₂ A : Matrix (Fin N) (Fin N) ℂ)
    (hH₁ : H₁.IsHermitian) (hH₂ : H₂.IsHermitian)
    {z₁ z₂ : ℂ} (hz₁ : z₁.im ≠ 0) (hz₂ : z₂.im ≠ 0)
    (p q : Fin N) :
    (∑ k : Fin (Fintype.card (HermitianCoordinate N)),
      ∫ y : HermitianCoordinateSpace N,
        (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
          (by positivity) k : ℂ) *
          (gueCoordinateDirection N k *
            (fullGUEResolvent H₁ z₁ y * A *
              fullGUEResolvent H₂ z₂ y) *
            gueCoordinateDirection N k) p q
      ∂hermitianGUECoordinateMeasure N (1 / (N : ℝ))
        (by positivity)) =
      ∫ y : HermitianCoordinateSpace N,
        (((N : ℂ)⁻¹ *
          (fullGUEResolvent H₁ z₁ y * A *
            fullGUEResolvent H₂ z₂ y).trace) •
          (1 : Matrix (Fin N) (Fin N) ℂ)) p q
      ∂hermitianGUECoordinateMeasure N (1 / (N : ℝ))
        (by positivity) := by
  let μ := hermitianGUECoordinateMeasure N (1 / (N : ℝ)) (by positivity)
  let X : HermitianCoordinateSpace N → Matrix (Fin N) (Fin N) ℂ :=
    fun y => fullGUEResolvent H₁ z₁ y * A * fullGUEResolvent H₂ z₂ y
  have hInt (k : Fin (Fintype.card (HermitianCoordinate N))) :
      Integrable (fun y =>
        (hermitianGUEFinCoordinateVariance N (1 / (N : ℝ))
          (by positivity) k : ℂ) *
          (gueCoordinateDirection N k * X y *
            gueCoordinateDirection N k) p q) μ := by
    simp only [Matrix.mul_apply]
    apply Integrable.const_mul
    apply integrable_finsetSum Finset.univ
    intro b hb
    apply Integrable.mul_const
    apply integrable_finsetSum Finset.univ
    intro a ha
    apply Integrable.const_mul
    exact integrable_fullGUEPlainTwoResolventEntry
      H₁ H₂ A hH₁ hH₂ hz₁ hz₂ a b
  rw [← integral_finsetSum Finset.univ (fun k hk => hInt k)]
  apply integral_congr_ae
  filter_upwards with y
  change normalizedGUECovarianceContraction N (X y) p q =
    (((N : ℂ)⁻¹ * (X y).trace) •
      (1 : Matrix (Fin N) (Fin N) ℂ)) p q
  exact congrFun (congrFun
    (normalizedGUECovarianceContraction_eq hN (X y)) p) q

end CEHNative.BlockBand.External.CEH
