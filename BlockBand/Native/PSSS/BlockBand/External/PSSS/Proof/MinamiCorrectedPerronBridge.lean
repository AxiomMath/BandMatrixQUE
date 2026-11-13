module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiCorrectedFiniteStageSuccessor

/-!
# Perron bridge and public order successor

The weighted public Perron approximant is disintegrated blockwise before the
canonical selected-block reduction.  All energy, Cauchy, and radial variables
are then reassociated with the same normalization used by the auxiliary mesh.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 12000000

namespace PSSSNative.BlockBand.PSSS

open Filter Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators ComplexOrder Matrix.Norms.L2Operator

private def perronBridgeKernel
    {k : ℕ} {dims : Fin k → ℕ}
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    {eta : ℝ} (heta : 0 < eta) (a b : ℝ) (r : ℕ)
    (p : (BlockProductDisintegration.ExteriorSample dims j ×
      BlockProductDisintegration.SelectedSample dims j) × ((ℝ × ℝ) × ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / Real.pi) *
    ENNReal.ofReal (standardCauchyWeight p.2.1.2) *
    ((eigenCount
      (correctedSelectedAuxiliaryHermitian A₀ j heta
        ((((p.1.1, p.1.2), p.2.1.1), p.2.1.2), p.2.2))
      (Set.Ioo (-p.2.2) p.2.2) : ℝ≥0∞) *
      fullPublicFixedPredecessorWeight A₀ a b r
        ((BlockProductDisintegration.split dims j).symm p.1)) *
    ENNReal.ofReal (poissonRadialWeight eta p.2.2)

private theorem measurable_perronBridgeKernel
    {k : ℕ} (dims : Fin k → ℕ)
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    {eta : ℝ} (heta : 0 < eta) (a b : ℝ) (r : ℕ) :
    Measurable (perronBridgeKernel A₀ j heta a b r) := by
  unfold perronBridgeKernel
  have hc : Measurable (fun p :
      (BlockProductDisintegration.ExteriorSample dims j ×
        BlockProductDisintegration.SelectedSample dims j) × ((ℝ × ℝ) × ℝ) =>
      ENNReal.ofReal (standardCauchyWeight p.2.1.2)) := by
    apply ENNReal.measurable_ofReal.comp
    unfold standardCauchyWeight
    fun_prop (discharger := intro x; positivity)
  let pull := fun p :
      (BlockProductDisintegration.ExteriorSample dims j ×
        BlockProductDisintegration.SelectedSample dims j) × ((ℝ × ℝ) × ℝ) =>
    ((((p.1.1, p.1.2), p.2.1.1), p.2.1.2), p.2.2)
  have hpull : Measurable pull := by
    exact (((((measurable_fst.comp measurable_fst).prodMk
      (measurable_snd.comp measurable_fst)).prodMk
        (measurable_fst.comp (measurable_fst.comp measurable_snd))).prodMk
          (measurable_snd.comp (measurable_fst.comp measurable_snd))).prodMk
            (measurable_snd.comp measurable_snd))
  have hn := (measurable_correctedSelectedAuxiliaryOpenCount
    dims A₀ j heta).comp hpull
  have hw : Measurable (fun p :
      (BlockProductDisintegration.ExteriorSample dims j ×
        BlockProductDisintegration.SelectedSample dims j) × ((ℝ × ℝ) × ℝ) =>
      fullPublicFixedPredecessorWeight A₀ a b r
        ((BlockProductDisintegration.split dims j).symm p.1)) :=
    (measurable_fullPublicFixedPredecessorWeight dims A₀ a b r).comp
      ((BlockProductDisintegration.split dims j).symm.measurable.comp
        measurable_fst)
  have hr : Measurable (fun p :
      (BlockProductDisintegration.ExteriorSample dims j ×
        BlockProductDisintegration.SelectedSample dims j) × ((ℝ × ℝ) × ℝ) =>
      ENNReal.ofReal (poissonRadialWeight eta p.2.2)) := by
    apply ENNReal.measurable_ofReal.comp
    unfold poissonRadialWeight
    fun_prop
  exact (((measurable_const.mul hc).mul (hn.mul hw)).mul hr)

private theorem normalized_fullPredecessor_selectedTrace_eq_perronBridgeIntegral
    {k : ℕ} (dims : Fin k → ℕ) (j : Fin k)
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    (a b : ℝ) (r n : ℕ)
    (p : (BlockProductDisintegration.ExteriorSample dims j ×
      BlockProductDisintegration.SelectedSample dims j) × ℝ) :
    (ENNReal.ofReal (1 / Real.pi) *
      fullPublicFixedPredecessorWeight A₀ a b r
        ((BlockProductDisintegration.split dims j).symm p.1)) *
      publicBlockRegulatedSelectedTrace A₀ j p.2
        (canonicalWegnerEta n)
        ((BlockProductDisintegration.split dims j).symm p.1) =
    ∫⁻ t : ℝ, ∫⁻ xi : ℝ in Set.Ioi 0,
      perronBridgeKernel A₀ j (canonicalWegnerEta_pos n) a b r
        (p.1, ((p.2, t), xi)) := by
  let W := fullPublicFixedPredecessorWeight A₀ a b r
  have hWtop : ∀ G, W G ≠ ⊤ := fun G => ennreal_descFactorial_ne_top _ _
  have hred := weighted_selectedTrace_eq_auxiliaryCountAverage
    A₀ j p.1.1 p.1.2 p.2 (canonicalWegnerEta_pos n)
    (ENNReal.ofReal (1 / Real.pi) *
      W ((BlockProductDisintegration.split dims j).symm p.1))
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (hWtop ((BlockProductDisintegration.split dims j).symm p.1)))
  rw [hred]
  unfold perronBridgeKernel canonicalSelectedAuxiliaryCountIntegrand W
  apply lintegral_congr
  intro t
  rw [← MeasureTheory.lintegral_const_mul]
  · apply setLIntegral_congr_fun measurableSet_Ioi
    intro xi hxi
    ac_rfl
  · have hn : Measurable (fun xi : ℝ =>
        (eigenCount
          (correctedSelectedAuxiliaryHermitian A₀ j
            (canonicalWegnerEta_pos n)
            ((((p.1.1, p.1.2), p.2), t), xi))
          (Set.Ioo (-xi) xi) : ℝ≥0∞)) :=
      (measurable_correctedSelectedAuxiliaryOpenCount dims A₀ j
        (canonicalWegnerEta_pos n)).comp (by fun_prop)
    have hr : Measurable (fun xi : ℝ =>
        ENNReal.ofReal
          (poissonRadialWeight (canonicalWegnerEta n) xi)) := by
      apply ENNReal.measurable_ofReal.comp
      unfold poissonRadialWeight
      fun_prop
    change Measurable (fun xi : ℝ =>
      (ENNReal.ofReal (1 / Real.pi) *
        fullPublicFixedPredecessorWeight A₀ a b r
          ((BlockProductDisintegration.split dims j).symm p.1)) *
      (correctedSelectedAuxiliaryOpenCount A₀ j
          (canonicalWegnerEta_pos n)
          ((((p.1.1, p.1.2), p.2), t), xi) *
        ENNReal.ofReal
          (poissonRadialWeight (canonicalWegnerEta n) xi)))
    exact measurable_const.mul (hn.mul hr)

private theorem measurable_uncurry_normalized_fullPredecessor_selectedTrace
    {k : ℕ} (dims : Fin k → ℕ) (j : Fin k)
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    (a b : ℝ) (r n : ℕ) :
    Measurable (Function.uncurry (fun s :
      BlockProductDisintegration.ExteriorSample dims j ×
        BlockProductDisintegration.SelectedSample dims j =>
      fun e : ℝ =>
        (ENNReal.ofReal (1 / Real.pi) *
          fullPublicFixedPredecessorWeight A₀ a b r
            ((BlockProductDisintegration.split dims j).symm s)) *
        publicBlockRegulatedSelectedTrace A₀ j e
          (canonicalWegnerEta n)
          ((BlockProductDisintegration.split dims j).symm s))) := by
  let W := fullPublicFixedPredecessorWeight A₀ a b r
  have hWtop : ∀ G, W G ≠ ⊤ := fun G => ennreal_descFactorial_ne_top _ _
  let K := perronBridgeKernel A₀ j (canonicalWegnerEta_pos n) a b r
  have hK : Measurable K :=
    measurable_perronBridgeKernel dims A₀ j
      (canonicalWegnerEta_pos n) a b r
  let Q := fun p :
      (BlockProductDisintegration.ExteriorSample dims j ×
        BlockProductDisintegration.SelectedSample dims j) × ℝ =>
    ∫⁻ t : ℝ, ∫⁻ xi : ℝ in Set.Ioi 0,
      K (p.1, ((p.2, t), xi))
  have hQ : Measurable Q := by
    let T := fun p :
        ((BlockProductDisintegration.ExteriorSample dims j ×
          BlockProductDisintegration.SelectedSample dims j) × ℝ) × ℝ =>
      ∫⁻ xi : ℝ in Set.Ioi 0,
        K (p.1.1, ((p.1.2, p.2), xi))
    have hT : Measurable T := by
      have hc : Measurable (Function.uncurry (fun p :
          ((BlockProductDisintegration.ExteriorSample dims j ×
            BlockProductDisintegration.SelectedSample dims j) × ℝ) × ℝ =>
          fun xi : ℝ => K (p.1.1, ((p.1.2, p.2), xi)))) := by
        exact hK.comp (by fun_prop)
      exact hc.lintegral_prod_right
    exact hT.lintegral_prod_right
  convert hQ using 1
  funext p
  exact normalized_fullPredecessor_selectedTrace_eq_perronBridgeIntegral
    dims j A₀ a b r n p

theorem lintegral_weightedPerron_eq_energyOuter
    {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i)
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    {a b : ℝ} (hab : a ≤ b) (r n : ℕ) :
    (∫⁻ G, publicBlockWeightedPerronApprox A₀ a b r n G
      ∂BlockGUE.publicBlockProductMeasure dims hd) =
    ∫⁻ e : ℝ in Set.Ioc a b, ∫⁻ G,
      fullPublicFixedPredecessorWeight A₀ a b r G *
        publicBlockPerronKernel A₀ n G e
      ∂BlockGUE.publicBlockProductMeasure dims hd := by
  let μ := BlockGUE.publicBlockProductMeasure dims hd
  let W := fullPublicFixedPredecessorWeight A₀ a b r
  have hW : Measurable W :=
    measurable_fullPublicFixedPredecessorWeight dims A₀ a b r
  have hWtop : ∀ G, W G ≠ ⊤ := fun G => ennreal_descFactorial_ne_top _ _
  let P := fun G : BlockGUE.PublicBlockSample dims => fun e : ℝ =>
    W G * publicBlockPerronKernel A₀ n G e
  have hP : Measurable (Function.uncurry P) :=
    (hW.comp measurable_fst).mul
      (measurable_uncurry_publicBlockPerronKernel dims A₀ n)
  calc
    _ = ∫⁻ G, W G * (∫⁻ e : ℝ in Set.Ioc a b,
        publicBlockPerronKernel A₀ n G e) ∂μ := by
      apply lintegral_congr
      intro G
      unfold publicBlockWeightedPerronApprox
      rw [publicBlockPerronApprox_eq_lintegral_Ioc A₀ G n hab]
      rfl
    _ = ∫⁻ G, (∫⁻ e : ℝ in Set.Ioc a b, P G e) ∂μ := by
      apply lintegral_congr
      intro G
      rw [lintegral_const_mul' _ _ (hWtop G)]
    _ = _ := lintegral_lintegral_swap hP.aemeasurable

theorem energyOuter_weightedTrace_le_sum
    {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i)
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    (a b : ℝ) (r n : ℕ) :
    (∫⁻ e : ℝ in Set.Ioc a b, ∫⁻ G,
      fullPublicFixedPredecessorWeight A₀ a b r G *
        publicBlockPerronKernel A₀ n G e
      ∂BlockGUE.publicBlockProductMeasure dims hd) ≤
    ∫⁻ e : ℝ in Set.Ioc a b, ∑ j : Fin k,
      ENNReal.ofReal (1 / Real.pi) *
        (∫⁻ Gext, ∫⁻ Gj,
          fullPublicFixedPredecessorWeight A₀ a b r
              ((BlockProductDisintegration.split dims j).symm (Gext, Gj)) *
            publicBlockRegulatedSelectedTrace A₀ j e
              (canonicalWegnerEta n)
              ((BlockProductDisintegration.split dims j).symm (Gext, Gj))
          ∂BlockProductDisintegration.selectedMeasure dims hd j
          ∂BlockProductDisintegration.exteriorMeasure dims hd j) := by
  apply setLIntegral_mono' measurableSet_Ioc
  intro e he
  unfold publicBlockPerronKernel
  rw [show (fun G => fullPublicFixedPredecessorWeight A₀ a b r G *
      (ENNReal.ofReal (1 / Real.pi) *
        publicBlockRegulatedTrace A₀ e (canonicalWegnerEta n) G)) =
      fun G => ENNReal.ofReal (1 / Real.pi) *
        (fullPublicFixedPredecessorWeight A₀ a b r G *
          publicBlockRegulatedTrace A₀ e
            (canonicalWegnerEta n) G) by funext G; ac_rfl,
    MeasureTheory.lintegral_const_mul]
  · have hh := mul_le_mul_right
      (lintegral_fullPublicPredecessor_mul_regulatedTrace_le_sum_split
        dims hd A₀ a b r e (canonicalWegnerEta n))
      (ENNReal.ofReal (1 / Real.pi))
    rw [Finset.mul_sum] at hh
    simpa [mul_comm] using hh
  · exact (measurable_fullPublicFixedPredecessorWeight dims A₀ a b r).mul
      (measurable_publicBlockRegulatedTrace_sample dims A₀ e
        (canonicalWegnerEta n) (canonicalWegnerEta_pos n))

/-- The exact public Perron/disintegration bridge before the final
Tonelli reassociation.  It is uniform in the Perron index `n`: the energy
variable remains outermost, while every selected block retains the
predecessor `fullPublicFixedPredecessorWeight` and the exact `1/π` normalization. -/
theorem lintegral_publicBlockWeightedPerronApprox_le_energyOuter_sum
    {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i)
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    {a b : ℝ} (hab : a ≤ b) (r n : ℕ) :
    (∫⁻ G, publicBlockWeightedPerronApprox A₀ a b r n G
      ∂BlockGUE.publicBlockProductMeasure dims hd) ≤
    ∫⁻ e : ℝ in Set.Ioc a b, ∑ j : Fin k,
      ENNReal.ofReal (1 / Real.pi) *
        (∫⁻ Gext, ∫⁻ Gj,
          fullPublicFixedPredecessorWeight A₀ a b r
              ((BlockProductDisintegration.split dims j).symm (Gext, Gj)) *
            publicBlockRegulatedSelectedTrace A₀ j e
              (canonicalWegnerEta n)
              ((BlockProductDisintegration.split dims j).symm (Gext, Gj))
          ∂BlockProductDisintegration.selectedMeasure dims hd j
          ∂BlockProductDisintegration.exteriorMeasure dims hd j) := by
  rw [lintegral_weightedPerron_eq_energyOuter dims hd A₀ hab r n]
  exact energyOuter_weightedTrace_le_sum dims hd A₀ a b r n

end PSSSNative.BlockBand.PSSS
