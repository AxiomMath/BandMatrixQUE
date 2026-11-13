module

public import BlockBand.Critical.GlobalSource.ReplacementLindeberg

/-!
# Global Gaussian source, source replacement: the two ends of the telescope

Identification of the all-Gaussian and the all-tag hybrids with the two laws of
`SourceReplacementStatement`.

* `pi_slotMeasures_map_groupSum`: the group sums `M^{-1/2} Σ_i h_{(a,i)}` are i.i.d. standard
  circular vectors (Gaussian stability, `pi_circularVectorLaw_map_scaledSum`);
* `hybridChar_empty`: the all-Gaussian hybrid is `charFun` of the Gaussian probe model
  `profileProbeLaw`/`profileProbeMatrix`;
* `pairMatrix_slotSum_univ`, `integral_slots_blockRestrict`, `hybridChar_univ`: for `L > 0`, the
  all-tag hybrid is `charFun` of `discreteSampledLaw`/`discreteSampledMatrix` (for fixed block
  indices the block restrictions of the circular vectors are the tag Gaussians).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.GlobalSource

open MeasureTheory ProbabilityTheory
open BlockBand.Internal.Contracts.CoareaPalm (circularVectorLaw)
open BlockBand.Internal.Contracts.CriticalEntire (tagGroup)
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open scoped ComplexConjugate NNReal ENNReal Matrix RealInnerProductSpace
open Complex (exp I)

section Gauss
variable {W L J M : ℕ}

/-- The slot vectors of all slots. -/
theorem pi_slotMeasures_map_snd {r : Fin J → Fin L → ℝ} (hr : ∀ a k, 0 ≤ r a k) :
    (Measure.pi (slotMeasures W L r (M := M))).map (fun y s => (y s).2) =
      Measure.pi fun _ : Fin (J * M) => circularVectorLaw (Fin L × Fin W) := by
  have hμ : ∀ s : Fin (J * M), IsProbabilityMeasure (slotMeasures W L r s) := fun s =>
    isProbabilityMeasure_slotLaw (hr _)
  have : ∀ s : Fin (J * M), SigmaFinite ((slotMeasures W L r s).map Prod.snd) := fun s =>
    inferInstance
  rw [Measure.pi_map_pi (fun s => measurable_snd.aemeasurable)]
  congr 1
  funext s
  have := isProbabilityMeasure_discreteBlockLaw (W := W) (hr (tagGroup s))
  simp [slotMeasures, slotLaw, Measure.map_snd_prod]

theorem pi_map_finProdFinEquiv {X : Type*} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] :
    (Measure.pi fun _ : Fin (J * M) => ν).map (fun H p => H (finProdFinEquiv p)) =
      Measure.pi fun _ : Fin J × Fin M => ν := by
  have h := (measurePreserving_piCongrLeft (fun _ : Fin (J * M) => ν) finProdFinEquiv).symm
  have he : ⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin (J * M) => X) finProdFinEquiv).symm =
      fun (H : Fin (J * M) → X) (p : Fin J × Fin M) => H (finProdFinEquiv p) := by
    funext H p
    simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_symm_apply]
  rw [← he]
  exact h.map_eq

theorem pi_map_curry {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν] :
    (Measure.pi fun _ : Fin J × Fin M => ν).map (fun K a i => K (a, i)) =
      Measure.pi fun _ : Fin J => Measure.pi fun _ : Fin M => ν := by
  have h := Measure.infinitePi_map_curry (fun (_ : Fin J) (_ : Fin M) => ν)
  simp only [Measure.infinitePi_eq_pi] at h
  exact h

/-- **Law of the Gaussian group sums**: `(M^{-1/2} Σ_i h_{(a,i)})_a` are i.i.d. with law
`circularVectorLaw`. -/
theorem pi_slotMeasures_map_groupSum {r : Fin J → Fin L → ℝ} (hr : ∀ a k, 0 ≤ r a k)
    (hM : 0 < M) :
    (Measure.pi (slotMeasures W L r (M := M))).map
        (fun y a x => (((Real.sqrt M)⁻¹ : ℝ) : ℂ) * ∑ i, (y (finProdFinEquiv (a, i))).2 x) =
      Measure.pi fun _ : Fin J => circularVectorLaw (Fin L × Fin W) := by
  have m1 : Measurable fun (y : Fin (J * M) → SlotSample W L) s => (y s).2 :=
    Measurable.of_eval fun s => measurable_snd.comp (measurable_pi_apply s)
  have m2 : Measurable fun (H : Fin (J * M) → Fin L × Fin W → ℂ) (p : Fin J × Fin M) =>
      H (finProdFinEquiv p) := Measurable.of_eval fun p => measurable_pi_apply _
  have m3 : Measurable fun (K : Fin J × Fin M → Fin L × Fin W → ℂ) (a : Fin J) (i : Fin M) =>
      K (a, i) := Measurable.of_eval fun a => Measurable.of_eval fun i =>
        measurable_pi_apply _
  have m4 : Measurable fun (K : Fin J → Fin M → Fin L × Fin W → ℂ) (a : Fin J) (x : Fin L × Fin W) =>
      (((Real.sqrt M)⁻¹ : ℝ) : ℂ) * ∑ i, K a i x := by
    refine Measurable.of_eval fun a => Measurable.of_eval fun x => ?_
    exact measurable_const.mul (Finset.measurable_sum _ fun i _ =>
      (measurable_pi_apply x).comp ((measurable_pi_apply i).comp (measurable_pi_apply a)))
  have hcomp : (fun (y : Fin (J * M) → SlotSample W L) (a : Fin J) (x : Fin L × Fin W) =>
      (((Real.sqrt M)⁻¹ : ℝ) : ℂ) * ∑ i, (y (finProdFinEquiv (a, i))).2 x) =
      (fun (K : Fin J → Fin M → Fin L × Fin W → ℂ) a x => (((Real.sqrt M)⁻¹ : ℝ) : ℂ) * ∑ i, K a i x) ∘
        (fun (K : Fin J × Fin M → Fin L × Fin W → ℂ) a i => K (a, i)) ∘
        (fun (H : Fin (J * M) → Fin L × Fin W → ℂ) p => H (finProdFinEquiv p)) ∘
        (fun (y : Fin (J * M) → SlotSample W L) s => (y s).2) := rfl
  rw [hcomp, ← Measure.map_map m4 (m3.comp (m2.comp m1)), ← Measure.map_map m3 (m2.comp m1),
    ← Measure.map_map m2 m1, pi_slotMeasures_map_snd hr, pi_map_finProdFinEquiv, pi_map_curry]
  have hpi := Measure.pi_map_pi (μ := fun _ : Fin J => Measure.pi fun _ : Fin M =>
      circularVectorLaw (Fin L × Fin W))
    (f := fun _ (k : Fin M → Fin L × Fin W → ℂ) (x : Fin L × Fin W) =>
      (((Real.sqrt M)⁻¹ : ℝ) : ℂ) * ∑ i, k i x)
    (fun a => (Measurable.of_eval fun x => measurable_const.mul
      (Finset.measurable_sum _ fun i _ => (measurable_pi_apply x).comp
        (measurable_pi_apply i))).aemeasurable)
  simp only [pi_circularVectorLaw_map_scaledSum hM] at hpi
  exact hpi

theorem measurable_charPair {Ω : Type*} [MeasurableSpace Ω]
    {G : Ω → Matrix (Fin L × Fin W) (Fin L × Fin W) ℂ} (hG : Measurable G)
    (w : Fin J → Fin L × Fin W → ℝ) (u : EuclideanSpace ℝ (Fin J × Fin J × Fin 2)) :
    Measurable fun x : Ω × (Fin J → Fin L × Fin W → ℂ) =>
      exp ((⟪matrixCoord J (pairMatrix (G x.1) (fun a => weightVec (w a) (x.2 a))), u⟫ : ℂ) * I) := by
  have h2 : Continuous fun K : Matrix (Fin J) (Fin J) ℂ =>
      exp ((⟪matrixCoord J K, u⟫ : ℂ) * I) := by
    have := (matrixCoord J).continuous; fun_prop
  have hw : Continuous fun η : Fin J → Fin L × Fin W → ℂ => fun a => weightVec (w a) (η a) := by
    unfold weightVec; fun_prop
  have h1 : Measurable fun x : Ω × (Fin J → Fin L × Fin W → ℂ) =>
      (G x.1, fun a => weightVec (w a) (x.2 a)) :=
    (hG.comp measurable_fst).prodMk (hw.measurable.comp measurable_snd)
  have h1' : Measurable fun x : Ω × (Fin J → Fin L × Fin W → ℂ) =>
      pairMatrix (G x.1) (fun a => weightVec (w a) (x.2 a)) :=
    continuous_pairMatrix.measurable.comp h1
  exact h2.measurable.comp h1'

/-- **The all-Gaussian hybrid is the Gaussian probe model** (`profileProbeLaw`), by Gaussian
stability of the group sums. -/
theorem hybridChar_empty (b E : ℝ) {r : Fin J → Fin L → ℝ} (hr : ∀ a k, 0 ≤ r a k) (hM : 0 < M)
    (u : EuclideanSpace ℝ (Fin J × Fin J × Fin 2)) :
    hybridChar b E W L J M r ∅ u = charFun ((profileProbeLaw W L J b).map
      (fun x => matrixCoord J (profileProbeMatrix b E W L r x))) u := by
  have hP : IsProbabilityMeasure (growthPathLaw W b) := by unfold growthPathLaw; infer_instance
  have hμs : ∀ s : Fin (J * M), IsProbabilityMeasure (slotMeasures W L r s) := fun s =>
    isProbabilityMeasure_slotLaw (hr _)
  set Ψ : (Fin (J * M) → SlotSample W L) → Fin J → Fin L × Fin W → ℂ :=
    fun y a x => (((Real.sqrt M)⁻¹ : ℝ) : ℂ) * ∑ i, (y (finProdFinEquiv (a, i))).2 x
  have hΨ : Measurable Ψ := by
    refine Measurable.of_eval fun a => Measurable.of_eval fun x => ?_
    exact measurable_const.mul (Finset.measurable_sum _ fun i _ =>
      (measurable_pi_apply x).comp (measurable_snd.comp (measurable_pi_apply _)))
  have hslot : ∀ y, slotSum (slotWeight W L r ∅) y =
      fun a => weightVec (gaussWeight W L (r a)) (Ψ y a) := by
    intro y
    funext a x
    unfold slotSum weightVec
    simp only [slotWeight, Finset.notMem_empty, ↓reduceIte, Ψ]
    rw [sum_tagGroup_ite (fun s => (gaussWeight W L (r (tagGroup s)) x : ℂ) * (y s).2 x) a]
    have hg : ∀ i : Fin M, tagGroup (finProdFinEquiv (a, i)) = a := fun i => by simp [tagGroup]
    simp_rw [hg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  set F : GrowthPath W × (Fin J → Fin L × Fin W → ℂ) → ℂ := fun x =>
    exp ((⟪matrixCoord J (pairMatrix (leadG b E W L x.1)
      (fun a => weightVec (gaussWeight W L (r a)) (x.2 a))), u⟫ : ℂ) * I)
  have hF : Measurable F := measurable_charPair (measurable_leadG b E W L) _ u
  have hpp : ∀ x, profileProbeMatrix b E W L r x = pairMatrix (leadG b E W L x.1)
      (fun a => weightVec (gaussWeight W L (r a)) (x.2 a)) := fun x => rfl
  have hmatrix : Measurable fun x : GrowthPath W × (Fin J → Fin L × Fin W → ℂ) =>
      matrixCoord J (profileProbeMatrix b E W L r x) := by
    simp_rw [hpp]
    have hw : Continuous fun η : Fin J → Fin L × Fin W → ℂ =>
        fun a => weightVec (gaussWeight W L (r a)) (η a) := by unfold weightVec; fun_prop
    have h1 : Measurable fun x : GrowthPath W × (Fin J → Fin L × Fin W → ℂ) =>
        pairMatrix (leadG b E W L x.1) (fun a => weightVec (gaussWeight W L (r a)) (x.2 a)) :=
      continuous_pairMatrix.measurable.comp
        (((measurable_leadG b E W L).comp measurable_fst).prodMk (hw.measurable.comp measurable_snd))
    exact (matrixCoord J).continuous.measurable.comp h1
  rw [charFun_apply, integral_map hmatrix.aemeasurable (by fun_prop)]
  unfold hybridChar hybridF
  simp_rw [hslot]
  change ∫ z, F (z.1, Ψ z.2) ∂(growthPathLaw W b).prod (Measure.pi (slotMeasures W L r)) =
    ∫ x, F x ∂profileProbeLaw W L J b
  have hmap : ((growthPathLaw W b).prod (Measure.pi (slotMeasures W L r))).map
      (Prod.map id Ψ) = profileProbeLaw W L J b := by
    rw [← Measure.map_prod_map _ _ measurable_id hΨ, Measure.map_id,
      pi_slotMeasures_map_groupSum hr hM]
    rfl
  rw [← hmap, integral_map (measurable_id.prodMap hΨ).aemeasurable hF.aestronglyMeasurable]
  rfl

end Gauss

section Disc
variable {W L J M : ℕ}

/-- A block of the path for an optional block index (`o = L` sent anywhere, it carries no tag). -/
def blkOf (hL : 0 < L) (o : Fin (L + 1)) : Fin L := ⟨o.val % L, Nat.mod_lt _ hL⟩

theorem optTag_blkOf (hL : 0 < L) (o : Fin (L + 1)) (m : ℝ) (H : Fin L × Fin W → ℂ) :
    optTag W L o m (fun w => H (blkOf hL o, w)) = weightVec (tagWeight W L m o) H := by
  unfold optTag
  split_ifs with h
  · have hb : blkOf hL o = ⟨o.val, h⟩ := Fin.ext (Nat.mod_eq_of_lt h)
    have ho : o = (⟨o.val, h⟩ : Fin L).castSucc := Fin.ext rfl
    rw [hb]
    conv_rhs => rw [ho]
    rw [weightVec_tagWeight_castSucc]
  · funext x
    unfold weightVec tagWeight
    have : x.1.val ≠ o.val := by have := x.1.isLt; omega
    simp [this]

/-- **The all-tag hybrid matrix is the discretely sampled matrix** for the block-restricted
circular vectors. -/
theorem pairMatrix_slotSum_univ (b E : ℝ) (hL : 0 < L) (r : Fin J → Fin L → ℝ) (ω : GrowthPath W)
    (y : Fin (J * M) → SlotSample W L) :
    pairMatrix (leadG b E W L ω) (slotSum (slotWeight W L r Finset.univ) y) =
      discreteSampledMatrix b E W L r
        (fun s => (y s).1, (ω, fun s w => (y s).2 (blkOf hL (y s).1, w))) := by
  set t : ℝ := (Real.sqrt M)⁻¹
  set ξ : Fin (J * M) → Fin L × Fin W → ℂ := fun s =>
    optTag W L (y s).1 (profileMass W L (r (tagGroup s))) (fun w => (y s).2 (blkOf hL (y s).1, w))
  have h1 : ∀ a, slotSum (slotWeight W L r Finset.univ) y a =
      (t : ℂ) • ∑ i : Fin M, ξ (finProdFinEquiv (a, i)) := by
    intro a
    funext x
    unfold slotSum
    simp only [slotWeight, Finset.mem_univ, ↓reduceIte, Pi.smul_apply, Finset.sum_apply,
      smul_eq_mul]
    rw [sum_tagGroup_ite (fun s => (tagWeight W L (profileMass W L (r (tagGroup s))) (y s).1 x : ℂ) *
      (y s).2 x) a]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ξ, optTag_blkOf]
    rfl
  funext a c
  unfold pairMatrix discreteSampledMatrix blockSampledMatrix
  rw [h1, h1, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, star_sum,
    sum_dotProduct, Matrix.mulVec_sum]
  simp_rw [dotProduct_sum]
  have hg : ∀ (a : Fin J) (i : Fin M), tagGroup (finProdFinEquiv (a, i)) = a :=
    fun a i => by simp [tagGroup]
  simp only [ξ, hg, smul_eq_mul, show star (t : ℂ) = (t : ℂ) from Complex.conj_ofReal t,
    leadG]
  rw [← mul_assoc]
  congr 1
  have hM : ((t : ℂ)) * (t : ℂ) = (M : ℂ)⁻¹ := by
    rw [← Complex.ofReal_mul, ← sq]
    simp only [t, inv_pow, Real.sq_sqrt (Nat.cast_nonneg M)]
    push_cast; rfl
  rw [hM]

theorem measurable_blockRestrict (hL : 0 < L) :
    Measurable fun y : Fin (J * M) → SlotSample W L =>
      (fun s => (y s).1, fun s (w : Fin W) => (y s).2 (blkOf hL (y s).1, w)) := by
  refine (Measurable.of_eval fun s => measurable_fst.comp (measurable_pi_apply s)).prodMk ?_
  refine Measurable.of_eval fun s => Measurable.of_eval fun w => ?_
  have h : Measurable fun q : SlotSample W L => q.2 (blkOf hL q.1, w) :=
    measurable_from_prod_countable_right fun o => measurable_pi_apply (blkOf hL o, w)
  exact h.comp (measurable_pi_apply s)

/-- For fixed block indices, restricting each circular vector to its block gives i.i.d. circular
vectors on `ℂ^W` (the tag Gaussians). -/
theorem pi_circularVectorLaw_map_blockRestrict (hL : 0 < L) (κ : Fin (J * M) → Fin (L + 1)) :
    (Measure.pi fun _ : Fin (J * M) => circularVectorLaw (Fin L × Fin W)).map
        (fun H s (w : Fin W) => H s (blkOf hL (κ s), w)) =
      Measure.pi fun _ : Fin (J * M) => circularVectorLaw (Fin W) := by
  have hm : ∀ s : Fin (J * M), Measurable fun (h : Fin L × Fin W → ℂ) (w : Fin W) =>
      h (blkOf hL (κ s), w) := fun s => Measurable.of_eval fun w => measurable_pi_apply _
  have hpi := Measure.pi_map_pi (μ := fun _ : Fin (J * M) => circularVectorLaw (Fin L × Fin W))
    (f := fun s (h : Fin L × Fin W → ℂ) (w : Fin W) => h (blkOf hL (κ s), w))
    (fun s => (hm s).aemeasurable)
  simp only [circularVectorLaw_map_row] at hpi
  exact hpi

theorem integral_slots_blockRestrict {r : Fin J → Fin L → ℝ} (hr : ∀ a k, 0 ≤ r a k)
    (hL : 0 < L) {F : (Fin (J * M) → Fin (L + 1)) × (Fin (J * M) → Fin W → ℂ) → ℂ}
    (hF : Measurable F) (hF1 : ∀ z, ‖F z‖ ≤ 1) :
    ∫ y, F (fun s => (y s).1, fun s w => (y s).2 (blkOf hL (y s).1, w))
        ∂Measure.pi (slotMeasures W L r) =
      ∑ κ, (Measure.pi fun s => discreteBlockLaw W L (r (tagGroup s))).real {κ} •
        ∫ g, F (κ, g) ∂Measure.pi fun _ : Fin (J * M) => circularVectorLaw (Fin W) := by
  have hblk : ∀ s : Fin (J * M), IsProbabilityMeasure (discreteBlockLaw W L (r (tagGroup s))) :=
    fun s => isProbabilityMeasure_discreteBlockLaw (hr _)
  set e := MeasurableEquiv.arrowProdEquivProdArrow (Fin (L + 1)) (Fin L × Fin W → ℂ) (Fin (J * M))
  have hmp : MeasurePreserving e (Measure.pi (slotMeasures W L r))
      ((Measure.pi fun s => discreteBlockLaw W L (r (tagGroup s))).prod
        (Measure.pi fun _ : Fin (J * M) => circularVectorLaw (Fin L × Fin W))) :=
    measurePreserving_arrowProdEquivProdArrow _ _ _ _ _
  set f := fun y : Fin (J * M) → SlotSample W L =>
    F (fun s => (y s).1, fun s w => (y s).2 (blkOf hL (y s).1, w))
  have hf : Measurable f := hF.comp (measurable_blockRestrict hL)
  rw [← (hmp.symm e).integral_comp' f]
  rw [integral_prod (fun p => f (e.symm p))
    (integrable_of_norm_le_one (hf.comp e.symm.measurable) fun z => hF1 _),
    integral_fintype Integrable.of_finite]
  refine Finset.sum_congr rfl fun κ _ => ?_
  congr 1
  have he : ∀ H, f (e.symm (κ, H)) = F (κ, fun s w => H s (blkOf hL (κ s), w)) := fun H => rfl
  simp_rw [he]
  have hΦ : Measurable fun (H : Fin (J * M) → Fin L × Fin W → ℂ) s (w : Fin W) =>
      H s (blkOf hL (κ s), w) := Measurable.of_eval fun s => Measurable.of_eval fun w =>
        (measurable_pi_apply (blkOf hL (κ s), w)).comp (measurable_pi_apply s)
  have hFk : Measurable fun g => F (κ, g) := hF.comp measurable_prodMk_left
  rw [← pi_circularVectorLaw_map_blockRestrict hL κ, integral_map hΦ.aemeasurable
    hFk.aestronglyMeasurable]

/-- **The all-tag hybrid is the discretely sampled model** (`discreteSampledLaw`). -/
theorem hybridChar_univ (b E : ℝ) {r : Fin J → Fin L → ℝ} (hr : ∀ a k, 0 ≤ r a k) (hL : 0 < L)
    (u : EuclideanSpace ℝ (Fin J × Fin J × Fin 2)) :
    hybridChar b E W L J M r Finset.univ u = charFun ((discreteSampledLaw W L J M b r).map
      (fun y => matrixCoord J (discreteSampledMatrix b E W L r y))) u := by
  have hP : IsProbabilityMeasure (growthPathLaw W b) := by unfold growthPathLaw; infer_instance
  have hblk : ∀ s : Fin (J * M), IsProbabilityMeasure (discreteBlockLaw W L (r (tagGroup s))) :=
    fun s => isProbabilityMeasure_discreteBlockLaw (hr _)
  have hμs : ∀ s : Fin (J * M), IsProbabilityMeasure (slotMeasures W L r s) := fun s =>
    isProbabilityMeasure_slotLaw (hr _)
  set D : (Fin (J * M) → Fin (L + 1)) × ProbedPath W (J * M) → ℂ := fun z =>
    exp ((⟪matrixCoord J (discreteSampledMatrix b E W L r z), u⟫ : ℂ) * I)
  have hK : Measurable fun z : (Fin (J * M) → Fin (L + 1)) × ProbedPath W (J * M) =>
      discreteSampledMatrix b E W L r z :=
    measurable_blockSampledMatrix b E W L (fun a => profileMass W L (r a))
  have hc : Continuous fun K : Matrix (Fin J) (Fin J) ℂ => exp ((⟪matrixCoord J K, u⟫ : ℂ) * I) := by
    have := (matrixCoord J).continuous; fun_prop
  have hD : Measurable D := hc.measurable.comp hK
  have hD1 : ∀ z, ‖D z‖ ≤ 1 := fun z => (Complex.norm_exp_ofReal_mul_I _).le
  have hK' : Measurable fun z : (Fin (J * M) → Fin (L + 1)) × ProbedPath W (J * M) =>
      matrixCoord J (discreteSampledMatrix b E W L r z) :=
    (matrixCoord J).continuous.measurable.comp hK
  rw [charFun_apply, integral_map hK'.aemeasurable (by fun_prop)]
  change hybridChar b E W L J M r Finset.univ u = ∫ z, D z ∂discreteSampledLaw W L J M b r
  have hcW : IsProbabilityMeasure (Measure.pi fun _ : Fin (J * M) => circularVectorLaw (Fin W)) :=
    inferInstance
  have hpp : IsProbabilityMeasure ((growthPathLaw W b).prod
      (Measure.pi fun _ : Fin (J * M) => circularVectorLaw (Fin W))) := inferInstance
  unfold discreteSampledLaw
  rw [integral_prod _ (integrable_of_norm_le_one hD hD1), integral_fintype Integrable.of_finite]
  unfold probedPathLaw
  have hφ : ∀ κ, Measurable fun ω : GrowthPath W =>
      ∫ g, D (κ, (ω, g)) ∂Measure.pi fun _ : Fin (J * M) => circularVectorLaw (Fin W) := by
    intro κ
    have h : StronglyMeasurable fun x : GrowthPath W × (Fin (J * M) → Fin W → ℂ) => D (κ, x) :=
      (hD.comp measurable_prodMk_left).stronglyMeasurable
    exact h.integral_prod_right'.measurable
  have hφ1 : ∀ κ ω, ‖∫ g, D (κ, (ω, g)) ∂Measure.pi fun _ : Fin (J * M) =>
      circularVectorLaw (Fin W)‖ ≤ 1 := fun κ ω =>
    (norm_integral_le_of_norm_le_const (C := 1) (ae_of_all _ fun g => hD1 _)).trans (by simp)
  have hR : ∀ κ, ∫ x, D (κ, x) ∂(growthPathLaw W b).prod
      (Measure.pi fun _ : Fin (J * M) => circularVectorLaw (Fin W)) =
      ∫ ω, ∫ g, D (κ, (ω, g)) ∂Measure.pi fun _ : Fin (J * M) => circularVectorLaw (Fin W)
        ∂growthPathLaw W b := fun κ =>
    integral_prod (fun x => D (κ, x)) (integrable_of_norm_le_one
      (hD.comp measurable_prodMk_left) fun x => hD1 _)
  simp_rw [hR]
  unfold hybridChar
  rw [integral_prod _ (integrable_of_norm_le_one (measurable_hybridF (measurable_leadG b E W L) _ u)
    fun z => (norm_hybridF _ _ u z).le)]
  have hin : ∀ ω, ∫ y, hybridF (leadG b E W L) (slotWeight W L r (Finset.univ :
      Finset (Fin (J * M)))) u (ω, y) ∂Measure.pi (slotMeasures W L r (M := M)) =
      ∑ κ, (Measure.pi fun s => discreteBlockLaw W L (r (tagGroup s))).real {κ} •
        ∫ g, D (κ, (ω, g)) ∂Measure.pi fun _ : Fin (J * M) => circularVectorLaw (Fin W) := by
    intro ω
    have h1 : ∀ y, hybridF (leadG b E W L) (slotWeight W L r Finset.univ) u (ω, y) =
        (fun z : (Fin (J * M) → Fin (L + 1)) × (Fin (J * M) → Fin W → ℂ) => D (z.1, (ω, z.2)))
          (fun s => (y s).1, fun s w => (y s).2 (blkOf hL (y s).1, w)) := by
      intro y
      change exp ((⟪matrixCoord J (pairMatrix (leadG b E W L ω)
          (slotSum (slotWeight W L r Finset.univ) y)), u⟫ : ℂ) * I) =
        exp ((⟪matrixCoord J (discreteSampledMatrix b E W L r (fun s => (y s).1,
          (ω, fun s w => (y s).2 (blkOf hL (y s).1, w)))), u⟫ : ℂ) * I)
      rw [pairMatrix_slotSum_univ b E hL r ω y]
    simp_rw [h1]
    exact integral_slots_blockRestrict hr hL
      (hD.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))) fun z => hD1 _
  simp_rw [hin]
  have hI : ∀ κ ∈ (Finset.univ : Finset (Fin (J * M) → Fin (L + 1))), Integrable (fun ω =>
      (Measure.pi fun s => discreteBlockLaw W L (r (tagGroup s))).real {κ} •
        ∫ g, D (κ, (ω, g)) ∂Measure.pi fun _ : Fin (J * M) => circularVectorLaw (Fin W))
      (growthPathLaw W b) := fun κ _ =>
    (integrable_of_norm_le_one (hφ κ) (hφ1 κ)).smul
      ((Measure.pi fun s => discreteBlockLaw W L (r (tagGroup s))).real {κ})
  rw [integral_finsetSum _ hI]
  simp_rw [integral_smul]

end Disc

end BlockBand.Critical.GlobalSource
