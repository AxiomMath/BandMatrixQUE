module

public import BlockBand.DeterminantScore.ScoreMoments
public import BlockBand.DeterminantScore.RbarMomentInvariance
public import BlockBand.DeterminantScore.RbarMomentJensen
public import BlockBand.DeterminantScore.RbarMomentFrame

/-!
# The `‖R̄‖` moment of the physical determinant score

The stabilizer of `K` preserves the conditional law, so `R̄` is normal and diagonal in an
eigenbasis of `K`; choosing a measurable unit eigenvector `w` maximizing `|w*R̄w|`, conditional
Jensen gives `‖R̄‖^r ≤ ⟨|w*Rw|^r⟩_θ`.

`rbarMoment_of_corner (hC : CoareaContract) (hMT : PhysicalMinorTailStatement) :
RbarMomentStatement`: `E♯ 1{E ∈ I}‖R̄‖^ρ ≤ C` for `0 < ρ < 2`, uniformly as in the statement.

Proof. Fix `θ` with `H_R`, `V` Hermitian and `v` unit, `K = outerK U θ`.
* `R̄ = 𝔷⁻¹ S` (`ExactScore.condInverse_eq`) and `S` maps every eigenvector of `K` to a multiple
  of itself (`sectorInvMoment_eigen`, reflections `1 - 2ww*` and GUE unitary invariance); if
  `N_-(H_R - E) > α`, `R̄ = 0`.
* `outerEig U j θ = eigVec j K` is a measurable unit eigenvector of the `j`-th eigenvalue for every
  rank `j` (degenerate spectra included), `R̄` is `θ`-measurable (`measurable_condInverse`), and
  `maxEig` is the eigenvector of the first rank maximizing `|w_j*R̄w_j|` (finite measurable case
  split); `norm_le_of_eigen` gives `‖R̄‖ ≤ |w*R̄w|` with `w = maxEig θ`, and `maxEig` is an
  `IsOuterEigenvector`.
* Weighted Jensen (`jensen_lintegral`, `ρ' > 1`) with weight `sectorWeight` (mass `𝔷`):
  `𝔷 ‖R̄‖^{ρ'} ≤ ∫ sw |w*Rw|^{ρ'}`.
* `ρ' = max ρ (3/2) ∈ (1, 2)`, `‖R̄‖^ρ ≤ 1 + ‖R̄‖^{ρ'}`; restoration `pairExpect_restore_le`,
  pair-law mass `≤ 1`, and `cornerMoment_holds` at `ρ'` with the Householder minor frame
  `minorFrame` give `C = 3(1 + max C₁ 0)`.

Corollary `determinantScore_of_corner (hC) (hMT) (hRow : PairRowMomentStatement) :
DeterminantScoreStatement`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.RbarMoment

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Layers BlockBand.Angular.FiberAngular
open BlockBand.DeterminantScore BlockBand.DeterminantScore.Sector
open BlockBand.DeterminantScore.PhysicalColumn BlockBand.DeterminantScore.MinorTail
open BlockBand.DeterminantScore.MinorTailInverse BlockBand.DeterminantScore.ScoreMoments
open BlockBand.DeterminantScore.ExactScore BlockBand.Angular.DetFactor
open scoped NNReal ENNReal Matrix.Norms.L2Operator

variable {p : Parameters} {i : ZMod p.n}

/-!
## Measurability
-/

theorem sectorWeight_nonneg' (α : Fin p.N) (U : FrameMap p i) (θ : OuterData p i)
    (G' : FrameMatrix p) : 0 ≤ sectorWeight α U θ G' := by
  rw [sectorWeight_eq]; exact secW_nonneg _ _ _

theorem measurable_sectorWeight_real (α : Fin p.N) {U : FrameMap p i} (hU : Measurable U) :
    Measurable fun z : OuterData p i × FrameMatrix p => sectorWeight α U z.1 z.2 := by
  have h := (measurable_sectorWeight α hU).ennreal_toReal
  convert h using 2 with z
  exact (ENNReal.toReal_ofReal (sectorWeight_nonneg' α U z.1 z.2)).symm

theorem measurable_sectorZ (α : Fin p.N) (s : ℝ) {U : FrameMap p i} (hU : Measurable U) :
    Measurable fun θ : OuterData p i => sectorZ α s U θ := by
  have := isProbabilityMeasure_gue (FrameIndex p) (pairTime p s)
  have h : Measurable fun θ : OuterData p i => zNat s U α.val θ :=
    (measurable_secInt hU α.val).lintegral_prod_right'
  unfold sectorZ
  simp_rw [detFactor_eq_zNat]
  exact h.ennreal_toReal

theorem measurable_matInv {κ : Type} [Fintype κ] [DecidableEq κ] :
    Measurable fun M : Matrix κ κ ℂ => M⁻¹ :=
  measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun c => measurable_inv_apply a c

/-- **`θ ↦ R̄(θ)` is Borel.** -/
theorem measurable_condInverse (α : Fin p.N) (s : ℝ) {U : FrameMap p i} (hU : Measurable U) :
    Measurable fun θ : OuterData p i => condInverse α s U θ := by
  have := isProbabilityMeasure_gue (FrameIndex p) (pairTime p s)
  refine measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun c => ?_
  have hf : StronglyMeasurable fun z : OuterData p i × FrameMatrix p =>
      (sectorWeight α U z.1 z.2 : ℂ) * (outerM U z.1 z.2)⁻¹ a c :=
    ((Complex.measurable_ofReal.comp (measurable_sectorWeight_real α hU)).mul
      ((measurable_inv_apply a c).comp (measurable_outerM hU))).stronglyMeasurable
  have hnum := hf.integral_prod_right' (ν := gueMeasure (FrameIndex p) (pairTime p s))
  change Measurable fun θ : OuterData p i =>
    (∫ G', (sectorWeight α U θ G' : ℂ) * (outerM U θ G')⁻¹ a c
      ∂gueMeasure (FrameIndex p) (pairTime p s)) / (sectorZ α s U θ : ℂ)
  exact hnum.measurable.div (Complex.measurable_ofReal.comp (measurable_sectorZ α s hU))

theorem continuous_quadNorm :
    Continuous fun q : FrameMatrix p × (FrameIndex p → ℂ) => ‖star q.2 ⬝ᵥ (q.1 *ᵥ q.2)‖ :=
  (continuous_snd.star.dotProduct (continuous_fst.matrix_mulVec continuous_snd)).norm

theorem measurable_cornerNorm {U : FrameMap p i} (hU : Measurable U)
    {w : OuterData p i → (FrameIndex p → ℂ)} (hw : Measurable w) :
    Measurable fun z : OuterData p i × FrameMatrix p =>
      ‖star (w z.1) ⬝ᵥ ((outerM U z.1 z.2)⁻¹ *ᵥ w z.1)‖ :=
  continuous_quadNorm.measurable.comp
    ((measurable_matInv.comp (measurable_outerM hU)).prodMk (hw.comp measurable_fst))

theorem measurable_ind (κ : ℝ) :
    Measurable fun θ : OuterData p i => (bulkInterval κ).indicator (1 : ℝ → ℝ≥0∞) θ.2.1 :=
  (measurable_one.indicator measurableSet_Icc).comp measurable_snd.fst

theorem measurable_cornerObs (κ r : ℝ) {U : FrameMap p i} (hU : Measurable U)
    {w : OuterData p i → (FrameIndex p → ℂ)} (hw : Measurable w) :
    Measurable fun z : OuterData p i × FrameMatrix p => cornerObs κ r U w z.1 z.2 := by
  unfold cornerObs
  exact ((measurable_ind κ).comp measurable_fst).mul
    (ENNReal.measurable_ofReal.comp ((measurable_cornerNorm hU hw).pow_const r))

/-!
## Measurable eigenvectors of `K` and the maximizing one
-/

/-- The measurable unit eigenvector of rank `j` of `K = outerK U θ`. -/
def outerEig (U : FrameMap p i) (j : Fin (Fintype.card (FrameIndex p))) (θ : OuterData p i) :
    FrameIndex p → ℂ :=
  eigVec j (outerK U θ)

theorem measurable_outerEig {U : FrameMap p i} (hU : Measurable U)
    (j : Fin (Fintype.card (FrameIndex p))) : Measurable (outerEig U j) :=
  (measurable_eigVec j).comp (measurable_outerK hU)

/-- `|w_j*R̄w_j|`. -/
def rbarScore (α : Fin p.N) (s : ℝ) (U : FrameMap p i) (j : Fin (Fintype.card (FrameIndex p)))
    (θ : OuterData p i) : ℝ :=
  ‖star (outerEig U j θ) ⬝ᵥ (condInverse α s U θ *ᵥ outerEig U j θ)‖

theorem measurable_rbarScore (α : Fin p.N) (s : ℝ) {U : FrameMap p i} (hU : Measurable U)
    (j : Fin (Fintype.card (FrameIndex p))) : Measurable (rbarScore α s U j) := by
  have h := (continuous_quadNorm (p := p)).measurable.comp
    ((measurable_condInverse α s hU).prodMk (measurable_outerEig hU j))
  exact h

/-- The region where `j` is the first maximizing rank. -/
def maxRegion (α : Fin p.N) (s : ℝ) (U : FrameMap p i) (j : Fin (Fintype.card (FrameIndex p))) :
    Set (OuterData p i) :=
  {θ | (∀ k, rbarScore α s U k θ ≤ rbarScore α s U j θ) ∧
    ∀ k, k < j → rbarScore α s U k θ < rbarScore α s U j θ}

/-- The maximizing measurable eigenvector `w*(θ)`. -/
def maxEig (α : Fin p.N) (s : ℝ) (U : FrameMap p i) (θ : OuterData p i) : FrameIndex p → ℂ := by
  classical
  exact fun x => ∑ j, if θ ∈ maxRegion α s U j then outerEig U j θ x else 0

theorem measurableSet_maxRegion (α : Fin p.N) (s : ℝ) {U : FrameMap p i} (hU : Measurable U)
    (j : Fin (Fintype.card (FrameIndex p))) : MeasurableSet (maxRegion α s U j) := by
  have h1 : MeasurableSet {θ : OuterData p i |
      ∀ k, rbarScore α s U k θ ≤ rbarScore α s U j θ} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun k =>
      measurableSet_le (measurable_rbarScore α s hU k) (measurable_rbarScore α s hU j)
  have h2 : MeasurableSet {θ : OuterData p i |
      ∀ k, k < j → rbarScore α s U k θ < rbarScore α s U j θ} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      measurableSet_lt (measurable_rbarScore α s hU k) (measurable_rbarScore α s hU j)
  exact h1.inter h2

theorem exists_maxRegion (α : Fin p.N) (s : ℝ) (U : FrameMap p i) (θ : OuterData p i) :
    ∃ j, θ ∈ maxRegion α s U j := by
  classical
  have hne : (Finset.univ : Finset (Fin (Fintype.card (FrameIndex p)))).Nonempty := by
    refine ⟨⟨0, ?_⟩, Finset.mem_univ _⟩
    have := p.W_pos
    simp only [FrameIndex, Fintype.card_fin]
    omega
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_max_image Finset.univ (fun j => rbarScore α s U j θ) hne
  let S := Finset.univ.filter fun j => ∀ k, rbarScore α s U k θ ≤ rbarScore α s U j θ
  have hS : S.Nonempty := ⟨j₀, by simp [S]; exact fun k => hj₀ k (Finset.mem_univ k)⟩
  have hmem := (Finset.mem_filter.mp (Finset.min'_mem S hS)).2
  refine ⟨S.min' hS, hmem, fun k hk => ?_⟩
  by_contra hlt
  have hkS : k ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    intro l
    exact le_trans (hmem l) (not_lt.mp hlt)
  exact (not_le_of_gt hk) (Finset.min'_le S k hkS)

theorem maxRegion_unique (α : Fin p.N) (s : ℝ) (U : FrameMap p i) {θ : OuterData p i}
    {j k : Fin (Fintype.card (FrameIndex p))} (hj : θ ∈ maxRegion α s U j)
    (hk : θ ∈ maxRegion α s U k) : j = k := by
  rcases lt_trichotomy j k with h | h | h
  · exact absurd (hj.1 k) (not_le_of_gt (hk.2 j h))
  · exact h
  · exact absurd (hk.1 j) (not_le_of_gt (hj.2 k h))

theorem maxEig_eq (α : Fin p.N) (s : ℝ) (U : FrameMap p i) {θ : OuterData p i}
    {j : Fin (Fintype.card (FrameIndex p))} (hj : θ ∈ maxRegion α s U j) :
    maxEig α s U θ = outerEig U j θ := by
  classical
  funext x
  unfold maxEig
  rw [Finset.sum_eq_single j]
  · rw [ite_eq_left hj]
  · intro k _ hk
    rw [ite_eq_right]
    exact fun hk' => hk (maxRegion_unique α s U hk' hj)
  · simp

theorem measurable_maxEig (α : Fin p.N) (s : ℝ) {U : FrameMap p i} (hU : Measurable U) :
    Measurable (maxEig α s U) := by
  classical
  refine measurable_pi_iff.mpr fun x => ?_
  unfold maxEig
  exact Finset.measurable_sum _ fun j _ => Measurable.ite (measurableSet_maxRegion α s hU j)
    ((measurable_pi_apply x).comp (measurable_outerEig hU j)) measurable_const

/-- **`w*` is a measurable unit eigenvector field of `K`.** -/
theorem isOuterEigenvector_maxEig (α : Fin p.N) (s : ℝ) {U : FrameMap p i} (hU : Measurable U) :
    IsOuterEigenvector U (maxEig α s U) := by
  refine ⟨measurable_maxEig α s hU, fun θ _ hK => ?_⟩
  obtain ⟨j, hj⟩ := exists_maxRegion α s U θ
  rw [maxEig_eq α s U hj]
  obtain ⟨h1, h2⟩ := eigVec_spec j hK
  exact ⟨h1, _, h2⟩

/-!
## `R̄` is diagonal in an eigenbasis of `K`
-/

theorem condInverse_eq_zero (α : Fin p.N) (s : ℝ) (U : FrameMap p i) {θ : OuterData p i}
    (hN : ¬ nR θ ≤ α.val) : condInverse α s U θ = 0 := by
  ext a c
  have h0 : ∀ G', sectorWeight α U θ G' = 0 := fun G' => by
    unfold sectorWeight
    rw [ite_eq_right (by change ¬ (_ + nR θ = α.val); omega), mul_zero]
  simp [condInverse, sectorAvgMat, h0]

theorem condInverse_eigen (α : Fin p.N) (s : ℝ) {U : FrameMap p i} (hU : IsPairFrame p i U)
    {θ : OuterData p i} (hR : θ.1.1.IsHermitian) (hV : θ.1.2.2.IsHermitian)
    (hv : l2Norm θ.2.2 = 1) :
    ∀ (x : FrameIndex p → ℂ) (μ : ℂ), outerK U θ *ᵥ x = μ • x →
      ∃ c : ℂ, condInverse α s U θ *ᵥ x = c • x := by
  intro x μ hx
  obtain ⟨om, E, v⟩ := θ
  by_cases hN : nR (om, E, v) ≤ α.val
  · rw [condInverse_eq α s hU hR hV E hv hN]
    have hA : ((U v)ᴴ * pairK p i om E * U v).IsHermitian :=
      isHermitian_conjTranspose_mul_mul _ (pairK_isHermitian p i hR hV E)
    obtain ⟨c, hc⟩ := sectorInvMoment_eigen (pairTime p s) hA
      (α.val - negativeCount (om.1 - (E : ℂ) • 1)) x μ hx
    exact ⟨_ * c, by rw [smul_mulVec, hc, smul_smul]⟩
  · exact ⟨0, by rw [condInverse_eq_zero α s U hN, zero_mulVec, zero_smul]⟩

theorem outerK_isHermitian' {U : FrameMap p i} (hU : IsPairFrame p i U) {θ : OuterData p i}
    (hR : θ.1.1.IsHermitian) (hV : θ.1.2.2.IsHermitian) (hv : l2Norm θ.2.2 = 1) :
    (outerK U θ).IsHermitian := by
  rw [← outerKs_eq_outerK hU hv]; exact outerKs_isHermitian U hR hV

/-- **`‖R̄‖ ≤ |w*R̄w|`** for the maximizing eigenvector. -/
theorem norm_condInverse_le (α : Fin p.N) (s : ℝ) {U : FrameMap p i} (hU : IsPairFrame p i U)
    {θ : OuterData p i} (hR : θ.1.1.IsHermitian) (hV : θ.1.2.2.IsHermitian)
    (hv : l2Norm θ.2.2 = 1) :
    ‖condInverse α s U θ‖ ≤
      ‖star (maxEig α s U θ) ⬝ᵥ (condInverse α s U θ *ᵥ maxEig α s U θ)‖ := by
  have hA := outerK_isHermitian' hU hR hV hv
  obtain ⟨j, hj⟩ := exists_maxRegion α s U θ
  rw [maxEig_eq α s U hj]
  exact norm_le_of_eigen hA (condInverse_eigen α s hU hR hV hv) (fun k => outerEig U k θ)
    (fun k => eigVec_spec k hA) (norm_nonneg _) (fun k => hj.1 k)

/-!
## Conditional Jensen at fixed outer data
-/

theorem integrable_sectorInv (α : Fin p.N) (s : ℝ) {U : FrameMap p i} (hU : IsPairFrame p i U)
    {θ : OuterData p i} (hR : θ.1.1.IsHermitian) (hV : θ.1.2.2.IsHermitian)
    (hv : l2Norm θ.2.2 = 1) (a c : FrameIndex p) :
    Integrable (fun G' => (sectorWeight α U θ G' : ℂ) * (outerM U θ G')⁻¹ a c)
      (gueMeasure (FrameIndex p) (pairTime p s)) := by
  obtain ⟨om, E, v⟩ := θ
  by_cases hN : nR (om, E, v) ≤ α.val
  · set N := negativeCount (om.1 - (E : ℂ) • 1)
    set A : Matrix (Fin (2 * p.W - 1)) (Fin (2 * p.W - 1)) ℂ := (U v)ᴴ * pairK p i om E * U v
    have hA : A.IsHermitian := isHermitian_conjTranspose_mul_mul _ (pairK_isHermitian p i hR hV E)
    have hfun : (fun G' => (sectorWeight α U (om, E, v) G' : ℂ) *
        (outerM U (om, E, v) G')⁻¹ a c) = fun G' => sectorInvIntegrand α.val N a c (A + G') := by
      funext G'
      simp only [sectorWeight, outerM, frameM_eq_compress p i hU _ E hv]
      rfl
    have hg : Measurable fun G' : FrameMatrix p => sectorInvIntegrand α.val N a c (A + G') := by
      have h := (measurable_sectorInvIntegrand (κ := FrameIndex p) α.val N a c).comp
        (measurable_const_add A)
      exact h
    rw [hfun, ← map_hermOfCoord_hermGaussian]
    refine (integrable_map_measure (g := fun G' : FrameMatrix p =>
      sectorInvIntegrand α.val N a c (A + G')) hg.aestronglyMeasurable
      continuous_hermOfCoord.measurable.aemeasurable).2 ?_
    refine (integrable_sectorDetSqInv (pairTime p s) hA (α.val - N) a c).congr
      (ae_of_all _ fun x => ?_)
    have him := det_im_eq_zero (hA.add (isHermitian_hermOfCoord x))
    simp only [Function.comp_apply, sectorInvIntegrand, sectorDetSqInv, InSector]
    have hN' : N ≤ α.val := hN
    by_cases hx : negativeCount (A + hermOfCoord x) = α.val - N
    · simp only [hx, Nat.sub_add_cancel hN', ↓reduceIte, mul_one]
      rw [Complex.normSq_eq_conj_mul_self, Complex.conj_eq_iff_im.2 him, pow_two]
    · have hl : ¬ negativeCount (A + hermOfCoord x) + N = α.val := by omega
      simp [hl, hx]
  · have h0 : ∀ G', sectorWeight α U (om, E, v) G' = 0 := fun G' => by
      unfold sectorWeight
      rw [ite_eq_right (by change ¬ (_ + nR (om, E, v) = α.val); omega), mul_zero]
    simp only [h0, Complex.ofReal_zero, zero_mul]
    exact integrable_zero _ _ _

theorem sectorZ_eq (α : Fin p.N) (s : ℝ) {U : FrameMap p i} (hU : IsPairFrame p i U)
    {θ : OuterData p i} (hR : θ.1.1.IsHermitian) (hV : θ.1.2.2.IsHermitian)
    (hv : l2Norm θ.2.2 = 1) :
    (∫⁻ G', ENNReal.ofReal (sectorWeight α U θ G') ∂gueMeasure (FrameIndex p) (pairTime p s)) =
      ENNReal.ofReal (sectorZ α s U θ) := by
  have hd := detFactor_eq_ofReal p i α s hU hR hV θ.2.1 hv
  have hz := detFactor_eq_zNat α s U θ
  unfold sectorZ
  rw [hd, ENNReal.toReal_ofReal (pairAngularDensity_nonneg α s hR hV _ _), ← hd, hz]
  rfl

theorem integrable_sectorWeight (α : Fin p.N) (s : ℝ) {U : FrameMap p i} (hU : IsPairFrame p i U)
    {θ : OuterData p i} (hR : θ.1.1.IsHermitian) (hV : θ.1.2.2.IsHermitian)
    (hv : l2Norm θ.2.2 = 1) :
    Integrable (fun G' => sectorWeight α U θ G') (gueMeasure (FrameIndex p) (pairTime p s)) ∧
      (∫ G', sectorWeight α U θ G' ∂gueMeasure (FrameIndex p) (pairTime p s)) =
        sectorZ α s U θ := by
  have hm : Measurable fun G' : FrameMatrix p => sectorWeight α U θ G' := by
    have h := (measurable_sectorWeight_real α hU.1).comp (measurable_prodMk_left (x := θ))
    exact h
  have hZ := sectorZ_eq α s hU hR hV hv
  have hint : Integrable (fun G' => sectorWeight α U θ G')
      (gueMeasure (FrameIndex p) (pairTime p s)) := by
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    have : ∀ G', ‖sectorWeight α U θ G'‖ₑ = ENNReal.ofReal (sectorWeight α U θ G') := fun G' =>
      Real.enorm_eq_ofReal (sectorWeight_nonneg' α U θ G')
    simp_rw [this, hZ]
    exact ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun G' => sectorWeight_nonneg' α U θ G')
    hm.aestronglyMeasurable, hZ, ENNReal.toReal_ofReal]
  unfold sectorZ
  exact ENNReal.toReal_nonneg

/-- **Conditional Jensen**: `𝔷 ‖R̄‖^ρ ≤ ∫ sw |w*Rw|^ρ` for `ρ > 1`, `w = maxEig θ`. -/
theorem jensen_condInverse (α : Fin p.N) (s : ℝ) {U : FrameMap p i} (hU : IsPairFrame p i U)
    {θ : OuterData p i} (hR : θ.1.1.IsHermitian) (hV : θ.1.2.2.IsHermitian)
    (hv : l2Norm θ.2.2 = 1) {ρ : ℝ} (hρ : 1 < ρ) :
    ENNReal.ofReal (‖condInverse α s U θ‖ ^ ρ) *
        (∫⁻ G', ENNReal.ofReal (sectorWeight α U θ G') ∂gueMeasure (FrameIndex p) (pairTime p s)) ≤
      ∫⁻ G', ENNReal.ofReal (sectorWeight α U θ G') *
        ENNReal.ofReal (‖star (maxEig α s U θ) ⬝ᵥ ((outerM U θ G')⁻¹ *ᵥ maxEig α s U θ)‖ ^ ρ)
        ∂gueMeasure (FrameIndex p) (pairTime p s) := by
  set μ := gueMeasure (FrameIndex p) (pairTime p s)
  set w := maxEig α s U θ
  set g : FrameMatrix p → ℝ := fun G' => sectorWeight α U θ G'
  set X : FrameMatrix p → ℂ := fun G' => star w ⬝ᵥ ((outerM U θ G')⁻¹ *ᵥ w)
  obtain ⟨hgi, hgZ⟩ := integrable_sectorWeight α s hU hR hV hv
  have hI := integrable_sectorInv α s hU hR hV hv
  have hXm : AEStronglyMeasurable X μ := by
    have h0 := (measurable_outerM hU.1).comp (measurable_prodMk_left (x := θ))
    have h : Measurable fun G' : FrameMatrix p => (outerM U θ G')⁻¹ := by
      have h1 := (measurable_matInv (κ := FrameIndex p)).comp h0
      exact h1
    have hc : Continuous fun R : FrameMatrix p => star w ⬝ᵥ (R *ᵥ w) :=
      continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)
    have h2 := hc.measurable.comp h
    exact h2.aestronglyMeasurable
  have hgXe : ∀ G', (g G' : ℂ) * X G' = ∑ a, ∑ c,
      star (w a) * ((sectorWeight α U θ G' : ℂ) * (outerM U θ G')⁻¹ a c) * w c := fun G' => by
    simp only [g, X, dotProduct, mulVec, Pi.star_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring
  have hgX : Integrable (fun G' => (g G' : ℂ) * X G') μ := by
    simp_rw [hgXe]
    exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun c _ =>
      ((hI a c).const_mul _).mul_const _
  have hq : star w ⬝ᵥ (condInverse α s U θ *ᵥ w) =
      (∫ G', (g G' : ℂ) * X G' ∂μ) / ((∫ G', g G' ∂μ : ℝ) : ℂ) := by
    simp_rw [hgXe]
    rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun c _ =>
      ((hI a c).const_mul _).mul_const _, hgZ, Finset.sum_div]
    simp only [dotProduct, mulVec, condInverse, sectorAvgMat, Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum _ fun c _ => ((hI a c).const_mul _).mul_const _, Finset.sum_div]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [integral_mul_const, integral_const_mul, Pi.star_apply]
    ring
  have J := jensen_lintegral (μ := μ) (fun G' => sectorWeight_nonneg' α U θ G') hgi hXm hgX hρ
  rw [← hq, hgZ] at J
  rw [sectorZ_eq α s hU hR hV hv, mul_comm]
  refine le_trans (mul_le_mul_right (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (norm_nonneg _)
    (norm_condInverse_le α s hU hR hV hv) (by linarith))) _) J

/-!
## The `‖R̄‖` moment
-/

theorem pointwise_rbar (α : Fin p.N) (s : ℝ) {U : FrameMap p i} (hU : IsPairFrame p i U)
    {θ : OuterData p i} (hR : θ.1.1.IsHermitian) (hV : θ.1.2.2.IsHermitian)
    (hv : l2Norm θ.2.2 = 1) (κ : ℝ) {ρ ρ' : ℝ} (hρ0 : 0 < ρ) (hρρ' : ρ ≤ ρ') (h1 : 1 < ρ') :
    (∫⁻ G', ENNReal.ofReal (sectorWeight α U θ G') *
        ((bulkInterval κ).indicator 1 θ.2.1 * ENNReal.ofReal (‖condInverse α s U θ‖ ^ ρ))
        ∂gueMeasure (FrameIndex p) (pairTime p s)) ≤
      ∫⁻ G', ENNReal.ofReal (sectorWeight α U θ G') *
        ((bulkInterval κ).indicator 1 θ.2.1 + cornerObs κ ρ' U (maxEig α s U) θ G')
        ∂gueMeasure (FrameIndex p) (pairTime p s) := by
  set μ := gueMeasure (FrameIndex p) (pairTime p s)
  set a : FrameMatrix p → ℝ≥0∞ := fun G' => ENNReal.ofReal (sectorWeight α U θ G')
  set I : ℝ≥0∞ := (bulkInterval κ).indicator (1 : ℝ → ℝ≥0∞) θ.2.1
  set X := ‖condInverse α s U θ‖
  set Q : FrameMatrix p → ℝ≥0∞ := fun G' =>
    ENNReal.ofReal (‖star (maxEig α s U θ) ⬝ᵥ ((outerM U θ G')⁻¹ *ᵥ maxEig α s U θ)‖ ^ ρ')
  have ha : Measurable a := measurable_sectorWeight_G α hU.1 θ
  have hQ : Measurable Q := ENNReal.measurable_ofReal.comp
    (((measurable_cornerNorm hU.1 (measurable_maxEig α s hU.1)).comp
      measurable_prodMk_left).pow_const ρ')
  have hpt : ∀ G', a G' * (I * ENNReal.ofReal (X ^ ρ)) ≤
      a G' * I + I * (a G' * ENNReal.ofReal (X ^ ρ')) := fun G' => by
    have h := rpow_le_one_add (norm_nonneg (condInverse α s U θ)) hρ0.le hρρ'
    calc a G' * (I * ENNReal.ofReal (X ^ ρ)) ≤ a G' * (I * ENNReal.ofReal (1 + X ^ ρ')) := by
          gcongr
      _ = a G' * I + I * (a G' * ENNReal.ofReal (X ^ ρ')) := by
          rw [ENNReal.ofReal_add zero_le_one (Real.rpow_nonneg (norm_nonneg _) _),
            ENNReal.ofReal_one]
          ring
  have hJ := jensen_condInverse α s hU hR hV hv h1
  calc (∫⁻ G', a G' * (I * ENNReal.ofReal (X ^ ρ)) ∂μ)
      ≤ ∫⁻ G', (a G' * I + I * (a G' * ENNReal.ofReal (X ^ ρ'))) ∂μ := lintegral_mono hpt
    _ = (∫⁻ G', a G' * I ∂μ) + I * ((∫⁻ G', a G' ∂μ) * ENNReal.ofReal (X ^ ρ')) := by
        rw [lintegral_add_left (ha.mul_const I), lintegral_const_mul I (ha.mul_const _),
          lintegral_mul_const (ENNReal.ofReal (X ^ ρ')) ha]
    _ ≤ (∫⁻ G', a G' * I ∂μ) + I * ∫⁻ G', a G' * Q G' ∂μ := by
        gcongr
        rw [mul_comm]
        exact hJ
    _ = ∫⁻ G', a G' * (I + cornerObs κ ρ' U (maxEig α s U) θ G') ∂μ := by
        have hIt : I ≠ ⊤ := by simp only [I, Set.indicator]; split_ifs <;> simp
        rw [← lintegral_const_mul' I (fun G' => a G' * Q G') hIt,
          ← lintegral_add_left (ha.mul_const I)]
        refine lintegral_congr fun G' => ?_
        simp only [cornerObs, Q, I]
        ring

/-- **`RbarMomentStatement`** from `CoareaContract` and `PhysicalMinorTailStatement`. -/
theorem rbarMoment_of_corner (hC : CoareaContract) (hMT : PhysicalMinorTailStatement) :
    RbarMomentStatement := by
  intro b T ϑ κ ρ hϑ hκ hρ0 hρ2
  set ρ' : ℝ := max ρ (3 / 2)
  have h1ρ' : 1 < ρ' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hρ'2 : ρ' < 2 := max_lt hρ2 (by norm_num)
  have hρρ' : ρ ≤ ρ' := le_max_left _ _
  obtain ⟨C₁, hC₁⟩ := cornerMoment_holds hC hMT b T ϑ κ ρ' hϑ hκ (by linarith) hρ'2
  refine ⟨3 * (1 + max C₁ 0), ?_⟩
  intro p hb hn model α hα i Pω hPω U hU
  set s := splitS p
  set w := maxEig α s U
  have hw : IsOuterEigenvector U w := isOuterEigenvector_maxEig α s hU.1
  have hWW : 2 * p.W - 2 + 1 = 2 * p.W - 1 := by have := p.W_pos; omega
  have hUw : IsMinorFrame (p := p) (minorFrame hWW) :=
    ⟨measurable_minorFrame hWW, fun x hx => minorFrame_spec hWW hx⟩
  set I : OuterData p i → ℝ≥0∞ := fun θ => (bulkInterval κ).indicator (1 : ℝ → ℝ≥0∞) θ.2.1
  set Φ : OuterData p i → FrameMatrix p → ℝ≥0∞ := fun θ G' => I θ + cornerObs κ ρ' U w θ G'
  have hcm := measurable_cornerObs κ ρ' hU.1 (measurable_maxEig α s hU.1)
  have hΦ : Measurable fun z : OuterData p i × FrameMatrix p => Φ z.1 z.2 :=
    ((measurable_ind κ).comp measurable_fst).add hcm
  have hmain := pairExpect_restore_le hPω hU.1 α α α α
    (fun θ _ => I θ * ENNReal.ofReal (‖condInverse α s U θ‖ ^ ρ)) Φ hΦ
    (fun θ hR hV hv => le_trans (pointwise_rbar α s hU hR hV hv κ hρ0 hρρ' h1ρ')
      (lintegral_mono fun G' => mul_le_mul_left le_add_self _))
  have hI1 : pairExpect α s U Pω (fun θ _ => I θ) ≤ 1 := by
    refine le_trans (pairExpect_mono_ae hPω α U (Ψ := fun θ _ => I θ) (Φ := fun _ _ => 1)
      fun θ _ _ _ _ => Filter.Eventually.of_forall fun G' _ => ?_) (pairExpect_one_le hC hPω hU α)
    simp only [I, Set.indicator]; split_ifs <;> simp
  have hcorner : pairExpect α s U Pω (cornerObs κ ρ' U w) ≤ ENNReal.ofReal (max C₁ 0) :=
    le_trans (hC₁ p hb hn model α hα i Pω hPω U hU w hw (minorFrame hWW) hUw)
      (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hΦb : pairExpect α s U Pω Φ ≤ 1 + ENNReal.ofReal (max C₁ 0) :=
    le_trans (pairExpect_add_le_of_measurable α s hU.1 Pω (fun θ _ => I θ) (cornerObs κ ρ' U w) hcm)
      (add_le_add hI1 hcorner)
  have e : (3 : ℝ≥0∞) * (1 + ENNReal.ofReal (max C₁ 0)) =
      ENNReal.ofReal (3 * (1 + max C₁ 0)) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add zero_le_one (le_max_right _ _),
      ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
  calc _ = pairExpect α s U Pω
        (fun θ _ => I θ * ENNReal.ofReal (‖condInverse α s U θ‖ ^ ρ)) := rfl
    _ ≤ _ := hmain
    _ ≤ (1 + ENNReal.ofReal (max C₁ 0)) + (1 + ENNReal.ofReal (max C₁ 0)) +
        (1 + ENNReal.ofReal (max C₁ 0)) := by gcongr
    _ = _ := by rw [← e]; ring

/-- **The determinant score theorem** from `CoareaContract`, `PhysicalMinorTailStatement` and
`PairRowMomentStatement` (the `‖R̄‖` half given by `rbarMoment_of_corner`). -/
theorem determinantScore_of_corner (hC : CoareaContract) (hMT : PhysicalMinorTailStatement)
    (hRow : PairRowMomentStatement) : DeterminantScoreStatement :=
  determinantScore_of_statements hC (rbarMoment_of_corner hC hMT) hRow

end BlockBand.DeterminantScore.RbarMoment
