module

public import BlockBand.Endpoints.Normalization.LeadProfileCylinder
public import BlockBand.Endpoints.Normalization.LeadProfileRotation
public import BlockBand.Endpoints.Clock.SmallBall
public import BlockBand.Internal.Contracts.ClocksCommonPort
public import BlockBand.Layers.PathGrowth

/-!
# The physical lead-profile theorem: measurability and the profile integrals

We prove the measurability of the matched-lead profile and compute its integrals.
* `measurable_profileOf`, `measurable_leadProfile_joint`: the rotated matched-lead profile is
  jointly measurable in the old path `ω` and the probe `h`.
* `measurable_commonPortProbe_joint`: `(ω, A, B, g) ↦ L(A,B; X(ω)) g` is jointly measurable, with
  `X(ω) = leadSchur e W r ω` (the old self-energy enters the common-port layer matrix
  affinely; Lean's totalized inverse is Borel).
* `integral_profileOf`: for a nonnegative mass vector `m` with total `t = Σ m_x` and every
  continuous `φ`, `∫ φ d(profileOf m) = φ(0)` if `t = 0`, and `Σ_x (m_x / t) φ(pt_x)` otherwise
  (the `δ_0` default of `leadProfile` on the null event `h*Yh = 0`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Model.Construction
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.Critical BlockBand.Internal.Contracts.ClocksCommonPort
open scoped ENNReal NNReal Matrix BoundedContinuousFunction

namespace LeadProfileCommonPort

/-- The atom `(block(x) + J mod n)/n` of the rotated matched-lead profile. -/
def leadPt (n r J : ℕ) (x : Fin r ⊕ Fin 2) : Torus :=
  QuotientAddGroup.mk ((((leadRingBlock r x + J) % n : ℕ) : ℝ) / n)

/-- The finite measure `Σ_x (m_x / Σ m) δ_{pt_x}` of a position-mass vector. -/
def profileMeasure (n r J : ℕ) (m : Fin r ⊕ Fin 2 → ℝ) : Measure Torus :=
  ∑ x : Fin r ⊕ Fin 2, ENNReal.ofReal (m x / ∑ y, m y) • Measure.dirac (leadPt n r J x)

/-- The profile of a position-mass vector, with the `δ_0` default of `leadProfile`. -/
def profileOf (n r J : ℕ) (m : Fin r ⊕ Fin 2 → ℝ) : MassProfile := by
  classical
  exact if hμ : IsProbabilityMeasure (profileMeasure n r J m) then ⟨profileMeasure n r J m, hμ⟩
    else ⟨Measure.dirac 0, inferInstance⟩

theorem leadProfile_eq_profileOf (b e : ℝ) (n W : ℕ) (ω : GrowthPath W)
    (h : Fin 2 × Fin W → ℂ) (J : ℕ) :
    leadProfile b e n W ω h J = profileOf n (n - 3) J (leadPositionMass b e W (n - 3) ω h) :=
  rfl

open Classical in
theorem coe_profileOf (n r J : ℕ) (m : Fin r ⊕ Fin 2 → ℝ) :
    (profileOf n r J m : Measure Torus) =
      if IsProbabilityMeasure (profileMeasure n r J m) then profileMeasure n r J m
      else Measure.dirac 0 := by
  classical
  by_cases hμ : IsProbabilityMeasure (profileMeasure n r J m)
  · simp [profileOf, hμ]
  · simp [profileOf, hμ]

theorem measurable_profileMeasure (n r J : ℕ) : Measurable (profileMeasure n r J) := by
  unfold profileMeasure
  refine Finset.measurable_sum _ fun x _ => ?_
  have h1 : Measurable (fun m : Fin r ⊕ Fin 2 → ℝ => m x / ∑ y, m y) :=
    (measurable_pi_apply x).div (Finset.measurable_sum _ fun y _ => measurable_pi_apply y)
  exact (ENNReal.measurable_ofReal.comp h1).smul_measure _

theorem measurable_profileOf (n r J : ℕ) : Measurable (profileOf n r J) := by
  classical
  have hS : MeasurableSet {m : Fin r ⊕ Fin 2 → ℝ | IsProbabilityMeasure (profileMeasure n r J m)} := by
    have : {m : Fin r ⊕ Fin 2 → ℝ | IsProbabilityMeasure (profileMeasure n r J m)} =
        (fun m => profileMeasure n r J m Set.univ) ⁻¹' {1} := by
      ext m
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
      exact isProbabilityMeasure_iff
    rw [this]
    exact (Measure.measurable_coe MeasurableSet.univ).comp (measurable_profileMeasure n r J)
      (measurableSet_singleton 1)
  have hm : Measurable (fun m : Fin r ⊕ Fin 2 → ℝ =>
      if IsProbabilityMeasure (profileMeasure n r J m) then profileMeasure n r J m
      else Measure.dirac (0 : Torus)) :=
    (measurable_profileMeasure n r J).piecewise hS measurable_const
  have hc : Measurable (fun m => (profileOf n r J m : Measure Torus)) := by
    have he : (fun m => (profileOf n r J m : Measure Torus)) =
        (fun m => if IsProbabilityMeasure (profileMeasure n r J m) then profileMeasure n r J m
          else Measure.dirac (0 : Torus)) := by
      funext m; exact coe_profileOf n r J m
    rw [he]
    exact hm
  exact hc.subtype_mk

/-- Entrywise measurability of a product of measurable matrix-valued maps. -/
theorem measurable_matMul {α : Type*} [MeasurableSpace α] {l m o : Type*} [Fintype m]
    {f : α → Matrix l m ℂ} {g : α → Matrix m o ℂ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun q => f q * g q) := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun k _ =>
    ((measurable_pi_apply k).comp ((measurable_pi_apply i).comp hf)).mul
      ((measurable_pi_apply j).comp ((measurable_pi_apply k).comp hg))

/-- Entrywise measurability of a matrix-vector product of measurable maps. -/
theorem measurable_matMulVec {α : Type*} [MeasurableSpace α] {l m : Type*} [Fintype m]
    {f : α → Matrix l m ℂ} {g : α → m → ℂ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun q => f q *ᵥ g q) := by
  refine measurable_pi_iff.mpr fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.measurable_sum _ fun k _ =>
    ((measurable_pi_apply k).comp ((measurable_pi_apply i).comp hf)).mul
      ((measurable_pi_apply k).comp hg)

/-- The response `U h` is jointly measurable in the path and the probe. -/
theorem measurable_leadResponse_mulVec (b e : ℝ) (W r : ℕ) :
    Measurable (fun q : GrowthPath W × (Fin 2 × Fin W → ℂ) =>
      leadResponse b e W r q.1 *ᵥ q.2) := by
  have hU : Measurable (fun ω : GrowthPath W => leadResponse b e W r ω) := by
    refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun y => ?_
    unfold leadResponse
    exact (measurable_pi_apply (Sum.inr y)).comp ((measurable_pi_apply x).comp
      (BlockBand.Endpoints.Clock.measurable_fullInverse b e W r))
  exact measurable_matMulVec (hU.comp measurable_fst) measurable_snd

theorem measurable_leadPositionMass (b e : ℝ) (W r : ℕ) :
    Measurable (fun q : GrowthPath W × (Fin 2 × Fin W → ℂ) =>
      leadPositionMass b e W r q.1 q.2) := by
  have hψ := measurable_leadResponse_mulVec b e W r
  refine measurable_pi_iff.mpr fun x => ?_
  rcases x with i | j
  · simp only [leadPositionMass]
    exact Finset.measurable_sum _ fun a _ =>
      (((measurable_pi_apply _).comp hψ).norm).pow_const 2
  · simp only [leadPositionMass]
    exact Finset.measurable_sum _ fun a _ =>
      (((measurable_pi_apply _).comp hψ).norm).pow_const 2

/-- The rotated matched-lead profile is jointly measurable in `(ω, h)`. -/
theorem measurable_leadProfile_joint (b e : ℝ) (n W J : ℕ) :
    Measurable (fun q : GrowthPath W × (Fin 2 × Fin W → ℂ) => leadProfile b e n W q.1 q.2 J) :=
  (measurable_profileOf n (n - 3) J).comp (measurable_leadPositionMass b e W (n - 3))

/-- The layer matrix depends affinely on the old self-energy. -/
theorem layerMatrix_eq_sub (e : ℝ) (z : ℂ) {W : ℕ}
    (X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (l : LayerSample W .common) :
    layerMatrix .common e z X l =
      layerMatrix .common e z 0 l - Matrix.fromBlocks X 0 0 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [layerMatrix, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, sub_eq_add_neg, add_assoc]

/-- `(X, A, B) ↦ L(A, B; X)` is jointly measurable. -/
theorem measurable_commonPortL_joint (b e : ℝ) (W : ℕ) :
    Measurable (fun q : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × LayerSample W .common =>
      commonPortL b e q.1 q.2) := by
  have hM : Measurable (fun q : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
      LayerSample W .common => layerMatrix .common e (commonZ b e) q.1 q.2) := by
    have h1 : Measurable (fun q : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
        LayerSample W .common => layerMatrix .common e (commonZ b e) 0 q.2) :=
      (BlockBand.Layers.measurable_layerMatrix .common e (commonZ b e) 0).comp measurable_snd
    refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
    have he : (fun q : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ × LayerSample W .common =>
        layerMatrix .common e (commonZ b e) q.1 q.2 i j) = fun q =>
        layerMatrix .common e (commonZ b e) 0 q.2 i j -
          (Matrix.fromBlocks q.1 0 0 0 : Matrix (LayerSite W .common) (LayerSite W .common) ℂ) i j := by
      funext q; rw [layerMatrix_eq_sub e (commonZ b e) q.1 q.2]; rfl
    rw [he]
    refine ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp h1)).sub ?_
    rcases i with i | i <;> rcases j with j | j
    · exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_fst)
    · exact measurable_const
    · exact measurable_const
    · exact measurable_const
  have hG : Measurable (fun q : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
      LayerSample W .common => commonPortResolvent b e q.1 q.2) :=
    BlockBand.Layers.measurable_matrix_inv.comp hM
  have hblk : Measurable (fun q : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
      LayerSample W .common => (commonPortResolvent b e q.1 q.2).toBlocks₁₂) := by
    refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
    exact (measurable_pi_apply (Sum.inr j)).comp ((measurable_pi_apply (Sum.inl i)).comp hG)
  have hK : Measurable (fun q : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ ×
      LayerSample W .common => matchedLeadK b e q.1) := by
    refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
    unfold matchedLeadK
    simp only [Matrix.sub_apply]
    exact measurable_const.sub ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_fst))
  unfold commonPortL
  exact measurable_matMul hK hblk

/-- The old self-energy `X(ω) = leadSchur e W r ω` is measurable. -/
theorem measurable_leadSchur (e : ℝ) (W r : ℕ) :
    Measurable (fun ω : GrowthPath W => leadSchur e W r ω) := by
  have : SecondCountableTopology (Matrix (Fin W) (Fin W) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin W → Fin W → ℂ))
  exact (BlockBand.Layers.measurable_pathSchur W r e).comp
    (BlockBand.Endpoints.Clock.continuous_pathAt W r).measurable

/-- The transported probe `L g` at `X(ω)` is jointly measurable in `(ω, A, B, g)`. -/
theorem measurable_commonPortProbe_joint (b e : ℝ) (W r : ℕ) :
    Measurable (fun q : GrowthPath W × (LayerSample W .common × (Fin 1 × Fin W → ℂ)) =>
      commonPortProbe b e (leadSchur e W r q.1) q.2) := by
  have hX : Measurable (fun q : GrowthPath W × (LayerSample W .common × (Fin 1 × Fin W → ℂ)) =>
      (leadSchur e W r q.1, q.2.1)) :=
    ((measurable_leadSchur e W r).comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)
  have hL : Measurable (fun q : GrowthPath W × (LayerSample W .common × (Fin 1 × Fin W → ℂ)) =>
      commonPortL b e (leadSchur e W r q.1) q.2.1) := by
    have h0 := (measurable_commonPortL_joint b e W).comp hX
    exact h0
  have hg : Measurable (fun q : GrowthPath W × (LayerSample W .common × (Fin 1 × Fin W → ℂ)) =>
      q.2.2) := measurable_snd.comp measurable_snd
  unfold commonPortProbe
  exact measurable_matMulVec hL hg

/-- **The profile integrals.** For `m ≥ 0` with total `t`, `∫ φ d(profileOf m)` is `φ(0)` if
`t = 0` and `Σ_x (m_x / t) φ(pt_x)` otherwise. -/
theorem integral_profileOf (n r J : ℕ) (m : Fin r ⊕ Fin 2 → ℝ) (hm : ∀ x, 0 ≤ m x)
    (φ : C(Torus, ℝ)) :
    ∫ s, φ s ∂(profileOf n r J m : Measure Torus) =
      if ∑ y, m y = 0 then φ 0 else ∑ x, (m x / ∑ y, m y) * φ (leadPt n r J x) := by
  rw [coe_profileOf]
  by_cases ht : ∑ y, m y = 0
  · rw [ite_eq_left ht]
    have h0 : profileMeasure n r J m = 0 := by
      unfold profileMeasure
      simp [ht]
    have hnp : ¬ IsProbabilityMeasure (profileMeasure n r J m) := by
      rw [h0]; intro h; exact IsProbabilityMeasure.ne_zero (0 : Measure Torus) rfl
    rw [ite_eq_right hnp, integral_dirac]
  · rw [ite_eq_right ht]
    have htpos : 0 < ∑ y, m y :=
      lt_of_le_of_ne (Finset.sum_nonneg fun y _ => hm y) (Ne.symm ht)
    have hprob : IsProbabilityMeasure (profileMeasure n r J m) := by
      rw [isProbabilityMeasure_iff]
      unfold profileMeasure
      rw [Measure.coe_finsetSum, Finset.sum_apply]
      simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
      rw [← ENNReal.ofReal_sum_of_nonneg fun x _ => div_nonneg (hm x) htpos.le,
        ← Finset.sum_div, div_self ht, ENNReal.ofReal_one]
    rw [ite_eq_left hprob]
    unfold profileMeasure
    have hφm : Measurable φ := φ.continuous.measurable
    rw [integral_finsetSum_measure fun x _ => ?_]
    · refine Finset.sum_congr rfl fun x _ => ?_
      rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal
        (div_nonneg (hm x) htpos.le), smul_eq_mul]
    · exact (integrable_dirac' hφm.stronglyMeasurable enorm_lt_top).smul_measure
        ENNReal.ofReal_ne_top

end LeadProfileCommonPort

end BlockBand.Endpoints.Normalization
