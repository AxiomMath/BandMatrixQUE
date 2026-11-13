module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.MinamiCorrectedPerronBridge

/-!
# Uniform Minami successor bound

Each weighted Perron approximant of the public block-GUE factorial count is bounded, uniformly
in the Perron index, by a sum over blocks of parameter-product integrals of the auxiliary
selected-block eigenvalue count. The proof reorders the energy, exterior and selected-block
integrals by Tonelli and applies the first-reduction formula to each block.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
set_option maxHeartbeats 12000000

namespace PSSSNative.BlockBand.PSSS

open Filter Matrix MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators ComplexOrder Matrix.Norms.L2Operator

/-- The finite-mesh event kernel is bounded with an order-independent constant: the constant is
chosen before the dimensions, the mesh size `M` and the order `r`. -/
theorem orderIndependent_correctedMeshConstant :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i) (j : Fin k)
      (A₀ : HermitianMatrix (BlockGUE.Index dims)) {eta : ℝ} (heta : 0 < eta)
      (Gext : BlockProductDisintegration.ExteriorSample dims j)
      (e t a b xi : ℝ), 0 < xi → ∀ (M r : ℕ),
      (∫⁻ φ, ∫⁻ Gj,
        correctedMeshEventKernel A₀ j heta Gext a b M r
          ((φ, Gj), ((e, t), xi))
        ∂BlockProductDisintegration.selectedMeasure dims hd j
        ∂uniformSphere (dims j)) ≤
      ENNReal.ofReal (1 / Real.pi) *
        ENNReal.ofReal (standardCauchyWeight t) *
        ENNReal.ofReal (10 * C * dims j * xi) *
        (∫⁻ φ, ∫⁻ Gj,
          fixedSelectedPredecessorWeight A₀ j φ a b r (Gext, Gj)
          ∂BlockProductDisintegration.selectedMeasure dims hd j
          ∂uniformSphere (dims j)) *
        ENNReal.ofReal (poissonRadialWeight eta xi) :=
  correctedMeshEventKernel_sample_le

private def uniformPerronBridgeKernel
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

private theorem measurable_uniformPerronBridgeKernel
    {k : ℕ} (dims : Fin k → ℕ)
    (A₀ : HermitianMatrix (BlockGUE.Index dims)) (j : Fin k)
    {eta : ℝ} (heta : 0 < eta) (a b : ℝ) (r : ℕ) :
    Measurable (uniformPerronBridgeKernel A₀ j heta a b r) := by
  unfold uniformPerronBridgeKernel
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

private theorem nested_uniformPerronBridgeKernel_eq_parameterProduct
    {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i) (j : Fin k)
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    {eta : ℝ} (heta : 0 < eta) (a b : ℝ) (r : ℕ) :
    (∫⁻ Gext,
      (∫⁻ Gj,
        (∫⁻ e : ℝ in Set.Ioc a b, ∫⁻ t : ℝ,
          ∫⁻ xi : ℝ in Set.Ioi 0,
            uniformPerronBridgeKernel A₀ j heta a b r
              ((Gext, Gj), ((e, t), xi)))
        ∂BlockProductDisintegration.selectedMeasure dims hd j)
      ∂BlockProductDisintegration.exteriorMeasure dims hd j) =
    ∫⁻ q, ∫⁻ Gext, ∫⁻ Gj,
      uniformPerronBridgeKernel A₀ j heta a b r ((Gext, Gj), q)
      ∂BlockProductDisintegration.selectedMeasure dims hd j
      ∂BlockProductDisintegration.exteriorMeasure dims hd j
      ∂(((volume.restrict (Set.Ioc a b)).prod volume).prod
        (volume.restrict (Set.Ioi 0))) := by
  let μs := (BlockProductDisintegration.exteriorMeasure dims hd j).prod
    (BlockProductDisintegration.selectedMeasure dims hd j)
  let μp : Measure ((ℝ × ℝ) × ℝ) :=
    ((volume.restrict (Set.Ioc a b)).prod volume).prod
    (volume.restrict (Set.Ioi 0))
  let K := uniformPerronBridgeKernel A₀ j heta a b r
  have hK : Measurable K :=
    measurable_uniformPerronBridgeKernel dims A₀ j heta a b r
  have hKc : Measurable (Function.uncurry (fun s q => K (s, q))) := by
    change Measurable K
    exact hK
  have hs : Measurable (fun s =>
      ∫⁻ q, K (s, q) ∂μp) := hKc.lintegral_prod_right
  have hp : Measurable (fun q =>
      ∫⁻ s, K (s, q) ∂μs) := by
    have hswap : Measurable (Function.uncurry (fun q s => K (s, q))) :=
      hK.comp (measurable_snd.prodMk measurable_fst)
    exact hswap.lintegral_prod_right
  let N := fun s :
      BlockProductDisintegration.ExteriorSample dims j ×
        BlockProductDisintegration.SelectedSample dims j =>
    ∫⁻ e : ℝ in Set.Ioc a b, ∫⁻ t : ℝ,
      ∫⁻ xi : ℝ in Set.Ioi 0, K (s, ((e, t), xi))
  have hN_eq : N = fun s => ∫⁻ q, K (s, q) ∂μp := by
    funext s
    unfold N
    rw [MeasureTheory.lintegral_prod]
    · let g := fun et : ℝ × ℝ =>
        ∫⁻ xi : ℝ in Set.Ioi 0, K (s, (et, xi))
      have hg : Measurable g := by
        have hc : Measurable (Function.uncurry
            (fun et : ℝ × ℝ => fun xi : ℝ => K (s, (et, xi)))) := by
          change Measurable (fun q : (ℝ × ℝ) × ℝ => K (s, q))
          exact hK.comp (measurable_const.prodMk measurable_id)
        exact hc.lintegral_prod_right
      rw [MeasureTheory.lintegral_prod g hg.aemeasurable]
    · exact (hK.comp
        (measurable_const.prodMk measurable_id)).aemeasurable
  have hN : Measurable N := by rw [hN_eq]; exact hs
  calc
    _ = ∫⁻ s, N s ∂μs := by
      exact (MeasureTheory.lintegral_prod N hN.aemeasurable).symm
    _ = ∫⁻ s, ∫⁻ q, K (s, q) ∂μp ∂μs := by rw [hN_eq]
    _ = ∫⁻ q, ∫⁻ s, K (s, q) ∂μs ∂μp :=
      lintegral_lintegral_swap hK.aemeasurable
    _ = _ := by
      rw [show (fun q => ∫⁻ s, K (s, q) ∂μs) =
          fun q => ∫⁻ Gext, ∫⁻ Gj, K ((Gext, Gj), q)
            ∂BlockProductDisintegration.selectedMeasure dims hd j
            ∂BlockProductDisintegration.exteriorMeasure dims hd j by
        funext q
        exact MeasureTheory.lintegral_prod _ <|
          (hK.comp (measurable_id.prodMk measurable_const)).aemeasurable]

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
      uniformPerronBridgeKernel A₀ j (canonicalWegnerEta_pos n) a b r
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
  unfold uniformPerronBridgeKernel canonicalSelectedAuxiliaryCountIntegrand W
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
  let K := uniformPerronBridgeKernel A₀ j (canonicalWegnerEta_pos n) a b r
  have hK : Measurable K :=
    measurable_uniformPerronBridgeKernel dims A₀ j
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

/-- One-block Tonelli reassociation from energy-first order to
exterior/selected/energy order. -/
theorem energyOuter_selectedTrace_eq_sampleOuter
    {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i) (j : Fin k)
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    (a b : ℝ) (r n : ℕ) :
    (∫⁻ e : ℝ in Set.Ioc a b,
      ENNReal.ofReal (1 / Real.pi) *
        (∫⁻ Gext, ∫⁻ Gj,
          fullPublicFixedPredecessorWeight A₀ a b r
              ((BlockProductDisintegration.split dims j).symm (Gext, Gj)) *
            publicBlockRegulatedSelectedTrace A₀ j e
              (canonicalWegnerEta n)
              ((BlockProductDisintegration.split dims j).symm (Gext, Gj))
          ∂BlockProductDisintegration.selectedMeasure dims hd j
          ∂BlockProductDisintegration.exteriorMeasure dims hd j)) =
    (∫⁻ Gext,
      (∫⁻ Gj,
        (∫⁻ e : ℝ in Set.Ioc a b,
          (ENNReal.ofReal (1 / Real.pi) *
            fullPublicFixedPredecessorWeight A₀ a b r
              ((BlockProductDisintegration.split dims j).symm (Gext, Gj))) *
            publicBlockRegulatedSelectedTrace A₀ j e
              (canonicalWegnerEta n)
              ((BlockProductDisintegration.split dims j).symm (Gext, Gj)))
        ∂BlockProductDisintegration.selectedMeasure dims hd j)
      ∂BlockProductDisintegration.exteriorMeasure dims hd j) := by
  let F := fun s :
      BlockProductDisintegration.ExteriorSample dims j ×
        BlockProductDisintegration.SelectedSample dims j => fun e : ℝ =>
    (ENNReal.ofReal (1 / Real.pi) *
      fullPublicFixedPredecessorWeight A₀ a b r
        ((BlockProductDisintegration.split dims j).symm s)) *
      publicBlockRegulatedSelectedTrace A₀ j e
        (canonicalWegnerEta n)
        ((BlockProductDisintegration.split dims j).symm s)
  let μs := (BlockProductDisintegration.exteriorMeasure dims hd j).prod
    (BlockProductDisintegration.selectedMeasure dims hd j)
  have hF : Measurable (Function.uncurry F) :=
    measurable_uncurry_normalized_fullPredecessor_selectedTrace
      dims j A₀ a b r n
  have hs : Measurable (fun s =>
      ∫⁻ e : ℝ in Set.Ioc a b, F s e) :=
    hF.lintegral_prod_right
  calc
    _ = ∫⁻ e : ℝ in Set.Ioc a b, ∫⁻ s, F s e ∂μs := by
      apply setLIntegral_congr_fun measurableSet_Ioc
      intro e he
      unfold μs
      dsimp only
      rw [MeasureTheory.lintegral_prod]
      · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        apply lintegral_congr
        intro Gext
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        apply lintegral_congr
        intro Gj
        unfold F
        ac_rfl
      · exact (hF.comp
          (measurable_id.prodMk measurable_const)).aemeasurable
    _ = ∫⁻ s, (∫⁻ e : ℝ in Set.Ioc a b, F s e) ∂μs :=
      (lintegral_lintegral_swap hF.aemeasurable).symm
    _ = _ := by
      rw [MeasureTheory.lintegral_prod _ hs.aemeasurable]

private theorem measurable_energyOuter_selectedTrace
    {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i) (j : Fin k)
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    (a b : ℝ) (r n : ℕ) :
    Measurable (fun e : ℝ =>
      ENNReal.ofReal (1 / Real.pi) *
        (∫⁻ Gext, ∫⁻ Gj,
          fullPublicFixedPredecessorWeight A₀ a b r
              ((BlockProductDisintegration.split dims j).symm (Gext, Gj)) *
            publicBlockRegulatedSelectedTrace A₀ j e
              (canonicalWegnerEta n)
              ((BlockProductDisintegration.split dims j).symm (Gext, Gj))
          ∂BlockProductDisintegration.selectedMeasure dims hd j
          ∂BlockProductDisintegration.exteriorMeasure dims hd j)) := by
  let F := fun s :
      BlockProductDisintegration.ExteriorSample dims j ×
        BlockProductDisintegration.SelectedSample dims j => fun e : ℝ =>
    (ENNReal.ofReal (1 / Real.pi) *
      fullPublicFixedPredecessorWeight A₀ a b r
        ((BlockProductDisintegration.split dims j).symm s)) *
      publicBlockRegulatedSelectedTrace A₀ j e
        (canonicalWegnerEta n)
        ((BlockProductDisintegration.split dims j).symm s)
  have hF : Measurable (Function.uncurry F) :=
    measurable_uncurry_normalized_fullPredecessor_selectedTrace
      dims j A₀ a b r n
  have htri := hF.comp
    (((measurable_snd.comp measurable_fst).prodMk measurable_snd).prodMk
      (measurable_fst.comp measurable_fst))
  have htri' : Measurable (Function.uncurry (fun p :
      ℝ × BlockProductDisintegration.ExteriorSample dims j =>
      fun Gj : BlockProductDisintegration.SelectedSample dims j =>
        F (p.2, Gj) p.1)) := by
    convert htri using 1
    funext p
    rfl
  have hsel := htri'.lintegral_prod_right
    (ν := BlockProductDisintegration.selectedMeasure dims hd j)
  have hsel' : Measurable (Function.uncurry (fun e : ℝ =>
      fun Gext : BlockProductDisintegration.ExteriorSample dims j =>
        ∫⁻ Gj, F (Gext, Gj) e
          ∂BlockProductDisintegration.selectedMeasure dims hd j)) := by
    exact hsel
  have hout := hsel'.lintegral_prod_right
    (ν := BlockProductDisintegration.exteriorMeasure dims hd j)
  convert hout using 1
  funext e
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro Gext
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro Gj
  unfold F
  ac_rfl

/-- The finite block sum commutes with energy integration, after which each
block is put in exterior/selected/energy order. -/
theorem energyOuter_finsetSum_selectedTrace_eq_sampleOuter_sum
    {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i)
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    (a b : ℝ) (r n : ℕ) :
    (∫⁻ e : ℝ in Set.Ioc a b, ∑ j : Fin k,
      ENNReal.ofReal (1 / Real.pi) *
        (∫⁻ Gext, ∫⁻ Gj,
          fullPublicFixedPredecessorWeight A₀ a b r
              ((BlockProductDisintegration.split dims j).symm (Gext, Gj)) *
            publicBlockRegulatedSelectedTrace A₀ j e
              (canonicalWegnerEta n)
              ((BlockProductDisintegration.split dims j).symm (Gext, Gj))
          ∂BlockProductDisintegration.selectedMeasure dims hd j
          ∂BlockProductDisintegration.exteriorMeasure dims hd j)) =
    ∑ j : Fin k,
      (∫⁻ Gext,
        (∫⁻ Gj,
          (∫⁻ e : ℝ in Set.Ioc a b,
            (ENNReal.ofReal (1 / Real.pi) *
              fullPublicFixedPredecessorWeight A₀ a b r
                ((BlockProductDisintegration.split dims j).symm (Gext, Gj))) *
              publicBlockRegulatedSelectedTrace A₀ j e
                (canonicalWegnerEta n)
                ((BlockProductDisintegration.split dims j).symm (Gext, Gj)))
          ∂BlockProductDisintegration.selectedMeasure dims hd j)
        ∂BlockProductDisintegration.exteriorMeasure dims hd j) := by
  rw [MeasureTheory.lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j hj
    exact energyOuter_selectedTrace_eq_sampleOuter dims hd j A₀ a b r n
  · intro j hj
    exact measurable_energyOuter_selectedTrace dims hd j A₀ a b r n

/-- Exact first-reduction and parameter-product identification after the
Tonelli reassociation. -/
theorem sampleOuter_sum_selectedTrace_eq_parameterProduct_sum
    {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i)
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    (a b : ℝ) (r n : ℕ) :
    (∑ j : Fin k,
      (∫⁻ Gext,
        (∫⁻ Gj,
          (∫⁻ e : ℝ in Set.Ioc a b,
            (ENNReal.ofReal (1 / Real.pi) *
              fullPublicFixedPredecessorWeight A₀ a b r
                ((BlockProductDisintegration.split dims j).symm (Gext, Gj))) *
              publicBlockRegulatedSelectedTrace A₀ j e
                (canonicalWegnerEta n)
                ((BlockProductDisintegration.split dims j).symm (Gext, Gj)))
          ∂BlockProductDisintegration.selectedMeasure dims hd j)
        ∂BlockProductDisintegration.exteriorMeasure dims hd j)) =
    ∑ j : Fin k,
      let μp := ((volume.restrict (Set.Ioc a b)).prod volume).prod
        (volume.restrict (Set.Ioi 0))
      ∫⁻ q, ∫⁻ Gext, ∫⁻ Gj,
        ENNReal.ofReal (1 / Real.pi) *
          ENNReal.ofReal (standardCauchyWeight q.1.2) *
          ((eigenCount
            (correctedSelectedAuxiliaryHermitian A₀ j
              (canonicalWegnerEta_pos n)
              ((((Gext, Gj), q.1.1), q.1.2), q.2))
              (Set.Ioo (-q.2) q.2) : ℝ≥0∞) *
            fullPublicFixedPredecessorWeight A₀ a b r
              ((BlockProductDisintegration.split dims j).symm (Gext, Gj))) *
          ENNReal.ofReal
            (poissonRadialWeight (canonicalWegnerEta n) q.2)
        ∂BlockProductDisintegration.selectedMeasure dims hd j
        ∂BlockProductDisintegration.exteriorMeasure dims hd j ∂μp := by
  let W := fullPublicFixedPredecessorWeight A₀ a b r
  rw [sum_iterated_weighted_selectedTrace_eq_auxiliaryCount
    dims hd A₀ (canonicalWegnerEta_pos n)
    (fun j Gext Gj _e =>
      W ((BlockProductDisintegration.split dims j).symm (Gext, Gj)))
    (fun j Gext Gj e =>
      ennreal_descFactorial_ne_top _ _)]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    _ = (∫⁻ Gext,
          (∫⁻ Gj,
            (∫⁻ e : ℝ in Set.Ioc a b, ∫⁻ t : ℝ,
              ∫⁻ xi : ℝ in Set.Ioi 0,
                uniformPerronBridgeKernel A₀ j (canonicalWegnerEta_pos n)
                  a b r ((Gext, Gj), ((e, t), xi)))
            ∂BlockProductDisintegration.selectedMeasure dims hd j)
          ∂BlockProductDisintegration.exteriorMeasure dims hd j) := by
      apply lintegral_congr
      intro Gext
      apply lintegral_congr
      intro Gj
      apply setLIntegral_congr_fun measurableSet_Ioc
      intro e he
      apply lintegral_congr
      intro t
      rw [← MeasureTheory.lintegral_const_mul]
      · apply setLIntegral_congr_fun measurableSet_Ioi
        intro xi hxi
        unfold uniformPerronBridgeKernel
          canonicalSelectedAuxiliaryCountIntegrand W
        ac_rfl
      · have hn : Measurable (fun xi : ℝ =>
            (eigenCount
              (correctedSelectedAuxiliaryHermitian A₀ j
                (canonicalWegnerEta_pos n)
                ((((Gext, Gj), e), t), xi))
              (Set.Ioo (-xi) xi) : ℝ≥0∞)) :=
          (measurable_correctedSelectedAuxiliaryOpenCount dims A₀ j
            (canonicalWegnerEta_pos n)).comp (by fun_prop)
        have hr : Measurable (fun xi : ℝ =>
            ENNReal.ofReal
              (poissonRadialWeight (canonicalWegnerEta n) xi)) := by
          apply ENNReal.measurable_ofReal.comp
          unfold poissonRadialWeight
          fun_prop
        exact measurable_const.mul (hn.mul hr)
    _ = ∫⁻ q, ∫⁻ Gext, ∫⁻ Gj,
        uniformPerronBridgeKernel A₀ j (canonicalWegnerEta_pos n)
          a b r ((Gext, Gj), q)
        ∂BlockProductDisintegration.selectedMeasure dims hd j
        ∂BlockProductDisintegration.exteriorMeasure dims hd j
        ∂(((volume.restrict (Set.Ioc a b)).prod volume).prod
          (volume.restrict (Set.Ioi 0))) :=
      nested_uniformPerronBridgeKernel_eq_parameterProduct
        dims hd j A₀ (canonicalWegnerEta_pos n) a b r
    _ = _ := by
      apply lintegral_congr
      intro q
      apply lintegral_congr
      intro Gext
      apply lintegral_congr
      intro Gj
      unfold uniformPerronBridgeKernel
      rfl

/-- Every weighted Perron approximant is bounded by the sum over blocks of the parameter-product
kernel, uniformly in the Perron index. -/
theorem lintegral_publicBlockWeightedPerronApprox_le_sum_parameterProduct
    {k : ℕ} (dims : Fin k → ℕ) (hd : ∀ i, 0 < dims i)
    (A₀ : HermitianMatrix (BlockGUE.Index dims))
    {a b : ℝ} (hab : a ≤ b) (r n : ℕ) :
    (∫⁻ G, publicBlockWeightedPerronApprox A₀ a b r n G
      ∂BlockGUE.publicBlockProductMeasure dims hd) ≤
    ∑ j : Fin k,
      let μp := ((volume.restrict (Set.Ioc a b)).prod volume).prod
        (volume.restrict (Set.Ioi 0))
      ∫⁻ q, ∫⁻ Gext, ∫⁻ Gj,
        ENNReal.ofReal (1 / Real.pi) *
          ENNReal.ofReal (standardCauchyWeight q.1.2) *
          ((eigenCount
            (correctedSelectedAuxiliaryHermitian A₀ j
              (canonicalWegnerEta_pos n)
              ((((Gext, Gj), q.1.1), q.1.2), q.2))
              (Set.Ioo (-q.2) q.2) : ℝ≥0∞) *
            fullPublicFixedPredecessorWeight A₀ a b r
              ((BlockProductDisintegration.split dims j).symm (Gext, Gj))) *
          ENNReal.ofReal
            (poissonRadialWeight (canonicalWegnerEta n) q.2)
        ∂BlockProductDisintegration.selectedMeasure dims hd j
        ∂BlockProductDisintegration.exteriorMeasure dims hd j ∂μp := by
  calc
    _ ≤ ∫⁻ e : ℝ in Set.Ioc a b, ∑ j : Fin k,
        ENNReal.ofReal (1 / Real.pi) *
          (∫⁻ Gext, ∫⁻ Gj,
            fullPublicFixedPredecessorWeight A₀ a b r
                ((BlockProductDisintegration.split dims j).symm (Gext, Gj)) *
              publicBlockRegulatedSelectedTrace A₀ j e
                (canonicalWegnerEta n)
                ((BlockProductDisintegration.split dims j).symm (Gext, Gj))
            ∂BlockProductDisintegration.selectedMeasure dims hd j
            ∂BlockProductDisintegration.exteriorMeasure dims hd j) :=
      lintegral_publicBlockWeightedPerronApprox_le_energyOuter_sum
        dims hd A₀ hab r n
    _ = ∑ j : Fin k,
        (∫⁻ Gext,
          (∫⁻ Gj,
            (∫⁻ e : ℝ in Set.Ioc a b,
              (ENNReal.ofReal (1 / Real.pi) *
                fullPublicFixedPredecessorWeight A₀ a b r
                  ((BlockProductDisintegration.split dims j).symm (Gext, Gj))) *
                publicBlockRegulatedSelectedTrace A₀ j e
                  (canonicalWegnerEta n)
                  ((BlockProductDisintegration.split dims j).symm (Gext, Gj)))
            ∂BlockProductDisintegration.selectedMeasure dims hd j)
          ∂BlockProductDisintegration.exteriorMeasure dims hd j) :=
      energyOuter_finsetSum_selectedTrace_eq_sampleOuter_sum
        dims hd A₀ a b r n
    _ = _ := sampleOuter_sum_selectedTrace_eq_parameterProduct_sum
      dims hd A₀ a b r n

end PSSSNative.BlockBand.PSSS
