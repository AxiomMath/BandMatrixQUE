module

public import BlockBand.Critical.GlobalSource.Rescaling

/-!
# Global Gaussian source: comparison of continuum and discrete block sampling

The hypothesis `GlobalProbeLindebergBound` (continuum-time sampled tags) follows from the
replacement estimate with exact-covariance discrete sampling (`SourceReplacementStatement`), the
Gaussian rescaling of the profiles, and the block-law comparison proved here.

* `sampledProbeMatrix_eq_blockSampledMatrix`, `sampledLaw_map_contBlocks`.
* `tendsto_charFun_sampled_sub_discrete`: discrete versus continuum blocks.
* `globalProbeLindebergBound_of_replacement`: `GlobalProbeLindebergBound` from
  `SourceReplacementStatement`.
* `globalGaussianSource_holds_of_replacement`: the global Gaussian source statement from
  `ComplexSourceLawContract`, `ComplexSourceLimitAlongSequences` and `SourceReplacementStatement`
  (the latter proved from `ComplexSourceLawContract` in `sourceReplacement_holds`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.GlobalSource

open MeasureTheory ProbabilityTheory Filter Topology Complex
open scoped RealInnerProductSpace Matrix
open BlockBand.Internal.Contracts.CriticalEntire BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionLaws

/-- The no-tag index gives the zero tag. -/
theorem optTag_last (W L : ℕ) (m : ℝ) (g : Fin W → ℂ) : optTag W L (Fin.last L) m g = 0 := by
  simp [optTag]

/-- The tag column of a tag born at `t` is the tag at block index `⌊W t⌋` (`blockIndex W L t`). -/
theorem probeColumns_apply_eq_optTag (W L np : ℕ) (t m : Fin np → ℝ) (g : Fin np → Fin W → ℂ)
    (x : Fin L × Fin W) (j : Fin np) :
    probeColumns W L t m g x j = optTag W L (blockIndex W L (t j)) (m j) (g j) x := by
  unfold probeColumns optTag blockIndex
  by_cases h : ⌊(W : ℝ) * t j⌋₊ < L
  · simp only [h, ↓reduceDIte, true_and]
    have hv : (L - 1 - ⌊(W : ℝ) * t j⌋₊) < L := by omega
    simp only [hv, ↓reduceDIte]
    unfold tagVector
    simp only [Fin.ext_iff]
  · simp [h]

/-- Entries of `𝒦 = 𝒥*G𝒥` as bilinear forms of the tags. -/
theorem complexSourceK_apply (b E : ℝ) {np : ℕ} (W L : ℕ) (t m : Fin np → ℝ)
    (x : ProbedPath W np) (j j' : Fin np) :
    complexSourceK b E W L t m x j j' =
      star (optTag W L (blockIndex W L (t j)) (m j) (x.2 j)) ⬝ᵥ
        ((fullInverse b E W L x.1).toBlocks₁₁ *ᵥ
          optTag W L (blockIndex W L (t j')) (m j') (x.2 j')) := by
  simp only [complexSourceK, Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct,
    Matrix.mulVec, ← probeColumns_apply_eq_optTag, Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
  ring

/-- Block indices of the continuum sample; tags of zero-mass groups are dropped (they vanish anyway). -/
def contBlocks (τ : ℝ) {J : ℕ} (Q : Fin J → C(BlockBand.Torus, ℝ)) (M W L : ℕ)
    (t : Fin (J * M) → ℝ) : Fin (J * M) → Fin (L + 1) :=
  fun i => if 0 < probeMass τ (Q (tagGroup i)) then blockIndex W L (t i) else Fin.last L

/-- The continuum-sampled matrix is the grouped tag matrix at the continuum block indices, with masses `m_a`. -/
theorem sampledProbeMatrix_eq_blockSampledMatrix (b E τ : ℝ) {J : ℕ}
    (Q : Fin J → C(BlockBand.Torus, ℝ)) (M W n : ℕ) (y : SampledSample W J M) :
    sampledProbeMatrix b E τ Q M W n y =
      blockSampledMatrix b E W (probePathLength n) (fun a => probeMass τ (Q a))
        (contBlocks τ Q M W (probePathLength n) y.1) y.2 := by
  funext a c
  have hg : ∀ (a : Fin J) (i : Fin M), tagGroup (finProdFinEquiv (a, i)) = a := fun a i => by
    simp [tagGroup]
  simp only [sampledProbeMatrix, groupedSourceMatrix, blockSampledMatrix, complexSourceK_apply,
    tagMasses, contBlocks, hg]
  by_cases ha : 0 < probeMass τ (Q a)
  · by_cases hc : 0 < probeMass τ (Q c)
    · simp [ha, hc]
    · simp [ha, hc, optTag_last]
  · simp [ha, optTag_last]

/-- `optTag` is Borel in the Gaussian. -/
theorem measurable_optTag (W L : ℕ) (o : Fin (L + 1)) (m : ℝ) :
    Measurable fun g : Fin W → ℂ => optTag W L o m g := by
  refine Measurable.of_eval fun y => ?_
  unfold optTag
  split_ifs
  · simp only [tagVector]
    split_ifs
    · exact measurable_const.mul (measurable_pi_apply _)
    · exact measurable_const
  · exact measurable_const

/-- The grouped tag matrix is jointly Borel in the block indices and the probed path. -/
theorem measurable_blockSampledMatrix (b E : ℝ) (W L : ℕ) {J M : ℕ} (mass : Fin J → ℝ) :
    Measurable fun z : (Fin (J * M) → Fin (L + 1)) × ProbedPath W (J * M) =>
      blockSampledMatrix b E W L mass z.1 z.2 := by
  refine measurable_from_prod_countable_right fun κ => ?_
  have hG : Measurable fun x : ProbedPath W (J * M) => (fullInverse b E W L x.1).toBlocks₁₁ := by
    have h : Measurable fun x : ProbedPath W (J * M) => fullInverse b E W L x.1 :=
      (measurable_matrix_inv.comp (measurable_fullPathMatrix b E W L)).comp measurable_fst
    refine Measurable.of_eval fun y => Measurable.of_eval fun y' => ?_
    exact (measurable_pi_apply (Sum.inl y')).comp ((measurable_pi_apply (Sum.inl y)).comp h)
  have hT : ∀ (j : Fin (J * M)) (mm : ℝ), Measurable fun x : ProbedPath W (J * M) =>
      optTag W L (κ j) mm (x.2 j) := fun j mm =>
    (measurable_optTag W L (κ j) mm).comp ((measurable_pi_apply j).comp measurable_snd)
  refine Measurable.of_eval fun a => Measurable.of_eval fun c => ?_
  simp only [blockSampledMatrix, dotProduct, Matrix.mulVec]
  refine measurable_const.mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _
    fun i' _ => Finset.measurable_sum _ fun y _ => Measurable.mul ?_ ?_)
  · exact continuous_star.measurable.comp ((measurable_pi_apply y).comp (hT _ _))
  · exact Finset.measurable_sum _ fun y' _ => ((measurable_pi_apply y').comp
      ((measurable_pi_apply y).comp hG)).mul ((measurable_pi_apply y').comp (hT _ _))

/-- `contBlocks` is Borel. -/
theorem measurable_contBlocks (τ : ℝ) {J : ℕ} (Q : Fin J → C(BlockBand.Torus, ℝ)) (M W L : ℕ) :
    Measurable (contBlocks τ Q M W L) := by
  refine Measurable.of_eval fun i => ?_
  simp only [contBlocks]
  split_ifs
  · exact (measurable_blockIndex W L).comp (measurable_pi_apply i)
  · exact measurable_const

/-- The law of (continuum block indices, probed path) is `Π_i contBlockLaw ⊗ probedPathLaw`. -/
theorem sampledLaw_map_contBlocks {τ : ℝ} (hτ : 0 < τ) {J : ℕ}
    {Q : Fin J → C(BlockBand.Torus, ℝ)} (hQ : ∀ a x, 0 ≤ Q a x) (M W L : ℕ) (b : ℝ) :
    (sampledLaw τ Q M W b).map (Prod.map (contBlocks τ Q M W L) id) =
      (Measure.pi fun i : Fin (J * M) => contBlockLaw τ (Q (tagGroup i)) W L).prod
        (probedPathLaw W (J * M) b) := by
  have := isProbabilityMeasure_sampledBirthLaw hτ hQ M
  have hp := fun a => isProbabilityMeasure_probeBirthLaw hτ (hQ a)
  unfold sampledLaw
  rw [← Measure.map_prod_map _ _ (measurable_contBlocks τ Q M W L) measurable_id, Measure.map_id]
  congr 1
  unfold sampledBirthLaw contBlocks
  have h := Measure.pi_map_pi (μ := fun i : Fin (J * M) => probeBirthLaw τ (Q (tagGroup i)))
    (f := fun i t => if 0 < probeMass τ (Q (tagGroup i)) then blockIndex W L t else Fin.last L)
    (fun i => by
      split_ifs
      · exact (measurable_blockIndex W L).aemeasurable
      · exact measurable_const.aemeasurable)
  refine h.trans ?_
  congr 1
  funext i
  unfold contBlockLaw
  split_ifs
  · rfl
  · rw [Measure.map_const, measure_univ, one_smul]

/-- Characteristic functions of two product laws differing only in the finite factor differ by at most the sum of the coordinate total variations. -/
theorem norm_charFun_prod_sub_le {K Ω : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype K] [MeasurableSpace K] [MeasurableSingletonClass K] [MeasurableSpace Ω]
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
    [MeasurableSpace E'] [BorelSpace E']
    (μ ν : ι → Measure K) [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]
    (P : Measure Ω) [IsProbabilityMeasure P] {Y : (ι → K) × Ω → E'} (hY : Measurable Y) (u : E') :
    ‖charFun (((Measure.pi μ).prod P).map Y) u - charFun (((Measure.pi ν).prod P).map Y) u‖ ≤
      ∑ i, ∑ k, |(μ i).real {k} - (ν i).real {k}| := by
  have hc : Continuous fun z : E' => exp (⟪z, u⟫ * I) := by fun_prop
  have hH : Measurable fun z => exp (⟪Y z, u⟫ * I) := hc.measurable.comp hY
  have hint : ∀ R : Measure ((ι → K) × Ω), IsFiniteMeasure R →
      Integrable (fun z => exp (⟪Y z, u⟫ * I)) R := fun R _ =>
    (integrable_const (1 : ℝ)).mono' hH.aestronglyMeasurable
      (Eventually.of_forall fun z => by rw [norm_exp_ofReal_mul_I])
  rw [charFun_apply, charFun_apply, integral_map hY.aemeasurable hc.aestronglyMeasurable,
    integral_map hY.aemeasurable hc.aestronglyMeasurable,
    integral_prod _ (hint _ inferInstance), integral_prod _ (hint _ inferInstance)]
  refine norm_integral_pi_sub_le μ ν _ fun κ => ?_
  refine (norm_integral_le_of_norm_le_const (C := (1 : ℝ))
    (Eventually.of_forall fun x => ?_)).trans (by simp)
  rw [norm_exp_ofReal_mul_I]

/-- The discrete block law is a probability measure (nonnegative profile). -/
theorem isProbabilityMeasure_discreteBlockLaw {W L : ℕ} {r : Fin L → ℝ} (hr : ∀ k, 0 ≤ r k) :
    IsProbabilityMeasure (discreteBlockLaw W L r) := by
  unfold discreteBlockLaw
  split_ifs with hpm
  · constructor
    rw [Measure.coe_finsetSum, Finset.sum_apply]
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    have hW : (W : ℝ) ≠ 0 := by
      intro h; simp [profileMass, h] at hpm
    have hWpos : (0 : ℝ) < W := lt_of_le_of_ne (Nat.cast_nonneg W) (Ne.symm hW)
    have hden : (0 : ℝ) ≤ (W : ℝ) * profileMass W L r := (mul_pos hWpos hpm).le
    rw [← ENNReal.ofReal_sum_of_nonneg fun k _ => div_nonneg (hr k) hden, ← Finset.sum_div]
    have : (W : ℝ) * profileMass W L r = ∑ k, r k := by
      unfold profileMass; field_simp
    rw [this, div_self (by rw [← this]; exact mul_ne_zero hW hpm.ne'), ENNReal.ofReal_one]
  · infer_instance

/-- The rescaled profile is nonnegative. -/
theorem rescaledProfile_nonneg {τ : ℝ} (hτ : 0 < τ) {Q : C(BlockBand.Torus, ℝ)}
    (hQ : ∀ x, 0 ≤ Q x) (W n : ℕ) (i : Fin (probePathLength n)) :
    0 ≤ rescaledProfile τ Q W n i := by
  unfold rescaledProfile rescaleFactor
  refine mul_nonneg ?_ (hQ _)
  split_ifs
  · exact zero_le_one
  · exact div_nonneg (probeMass_nonneg hτ.le hQ) (mul_nonneg (by positivity)
      (Finset.sum_nonneg fun i _ => hQ _))

/-- **Discrete versus continuum blocks.** Domain: `τ > 0`, nonnegative continuous profiles, any
critical sequence, fixed `M`, any `u`. The characteristic functions of the continuum-sampled
matrix (`sampledProbeMatrixLaw`) and of the discretely sampled matrix of the rescaled profiles
(`discreteSampledLaw`) differ by `o(1)` as `j → ∞`. Proof: both are the same
function of the block indices, the path and the tag Gaussians; masses agree eventually; total
variation of the `J·M` independent block laws `→ 0`. -/
theorem tendsto_charFun_sampled_sub_discrete (b E : ℝ) {τ : ℝ} (hτ : 0 < τ) {J : ℕ}
    {Q : Fin J → C(BlockBand.Torus, ℝ)} (hQ : ∀ a x, 0 ≤ Q a x)
    (s : BlockBand.CriticalSequence τ) (M : ℕ) (u : EuclideanSpace ℝ (Fin J × Fin J × Fin 2)) :
    Tendsto (fun j => ‖charFun ((sampledProbeMatrixLaw b E τ Q M (s.W j) (s.n j)).map
        (matrixCoord J)) u -
      charFun ((discreteSampledLaw (s.W j) (probePathLength (s.n j)) J M b
        (fun a => rescaledProfile τ (Q a) (s.W j) (s.n j))).map
          (fun y => matrixCoord J (discreteSampledMatrix b E (s.W j) (probePathLength (s.n j))
            (fun a => rescaledProfile τ (Q a) (s.W j) (s.n j)) y))) u‖) atTop (𝓝 0) := by
  set e := matrixCoord J
  set TV : ℕ → ℝ := fun j => ∑ i : Fin (J * M), ∑ k,
    |(contBlockLaw τ (Q (tagGroup i)) (s.W j) (probePathLength (s.n j))).real {k} -
      (discreteBlockLaw (s.W j) (probePathLength (s.n j))
        (rescaledProfile τ (Q (tagGroup i)) (s.W j) (s.n j))).real {k}|
  have hTV : Tendsto TV atTop (𝓝 0) := by
    have : ∀ i : Fin (J * M), Tendsto (fun j => ∑ k,
        |(contBlockLaw τ (Q (tagGroup i)) (s.W j) (probePathLength (s.n j))).real {k} -
          (discreteBlockLaw (s.W j) (probePathLength (s.n j))
            (rescaledProfile τ (Q (tagGroup i)) (s.W j) (s.n j))).real {k}|) atTop (𝓝 0) := by
      intro i
      by_cases hm : 0 < probeMass τ (Q (tagGroup i))
      · exact tendsto_tv_contBlockLaw_discreteBlockLaw hτ (hQ _) hm s
      · refine tendsto_const_nhds.congr fun j => ?_
        rw [contBlockLaw_eq_discreteBlockLaw_of_zero hτ (hQ _) hm]
        simp
    simpa using tendsto_finsetSum _ fun i _ => this i
  refine squeeze_zero' (Eventually.of_forall fun j => norm_nonneg _) ?_ hTV
  have hmass := eventually_all.2 fun a => eventually_profileMass_rescaledProfile hτ (hQ a) s
  filter_upwards [hmass] with j hj
  set W := s.W j
  set n := s.n j
  set L := probePathLength n
  set mass : Fin J → ℝ := fun a => probeMass τ (Q a)
  set Y : (Fin (J * M) → Fin (L + 1)) × ProbedPath W (J * M) → EuclideanSpace ℝ
      (Fin J × Fin J × Fin 2) := fun z => e (blockSampledMatrix b E W L mass z.1 z.2)
  have hY : Measurable Y := e.continuous.measurable.comp (measurable_blockSampledMatrix b E W L mass)
  have hc := fun i : Fin (J * M) => isProbabilityMeasure_contBlockLaw hτ (hQ (tagGroup i)) W L
  have hd := fun i : Fin (J * M) => isProbabilityMeasure_discreteBlockLaw (W := W)
    (rescaledProfile_nonneg hτ (hQ (tagGroup i)) W n)
  have h1 : (sampledProbeMatrixLaw b E τ Q M W n).map e =
      ((Measure.pi fun i : Fin (J * M) => contBlockLaw τ (Q (tagGroup i)) W L).prod
        (probedPathLaw W (J * M) b)).map Y := by
    rw [← sampledLaw_map_contBlocks hτ hQ M W L b, Measure.map_map hY
      ((measurable_contBlocks τ Q M W L).prodMap measurable_id)]
    unfold sampledProbeMatrixLaw
    rw [Measure.map_map e.continuous.measurable (measurable_sampledProbeMatrix b E τ Q M W n)]
    congr 1
    funext y
    simp only [Function.comp_apply, Y]
    rw [sampledProbeMatrix_eq_blockSampledMatrix]
    rfl
  have h2 : (discreteSampledLaw W L J M b (fun a => rescaledProfile τ (Q a) W n)).map
      (fun y => e (discreteSampledMatrix b E W L (fun a => rescaledProfile τ (Q a) W n) y)) =
      ((Measure.pi fun i : Fin (J * M) => discreteBlockLaw W L
        (rescaledProfile τ (Q (tagGroup i)) W n)).prod (probedPathLaw W (J * M) b)).map Y := by
    unfold discreteSampledLaw
    congr 1
    funext y
    simp only [Y, discreteSampledMatrix]
    congr 2
    funext a
    exact hj a
  rw [h1, h2]
  exact norm_charFun_prod_sub_le _ _ _ hY u

/-- `|φ_μ - φ_ν| ≤ 2`. -/
theorem norm_charFun_sub_le_two {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    [MeasurableSpace E'] (μ ν : Measure E') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (u : E') : ‖charFun μ u - charFun ν u‖ ≤ 2 := by
  refine (norm_sub_le _ _).trans ?_
  have h1 := norm_charFun_le_one (μ := μ) u
  have h2 := norm_charFun_le_one (μ := ν) u
  linarith

/-- **`GlobalProbeLindebergBound` from the source replacement estimate.** For `0 < b < 1/2`,
`-2 < E < 2`, `τ > 0` and nonnegative continuous profiles, `ComplexSourceLawContract` and
`SourceReplacementStatement` (with `κI = min(2+E, 2-E)`, `T = τ + 1`, `qmax = 2Σ_a‖q_a‖_∞` and the
rescaled profiles) give `ε(M,u) = C(1+‖u‖)³/√M + 1/M`. -/
theorem globalProbeLindebergBound_of_replacement (hCS : ComplexSourceLawContract)
    (hR : SourceReplacementStatement) {b E τ : ℝ} (hb : 0 < b) (hb' : b < 1 / 2)
    (hE : -2 < E ∧ E < 2) (hτ : 0 < τ) {J : ℕ} {Q : Fin J → C(BlockBand.Torus, ℝ)}
    (hQ : ∀ a x, 0 ≤ Q a x) : GlobalProbeLindebergBound b E τ Q := by
  intro s
  set e := matrixCoord J
  set κI : ℝ := min (2 + E) (2 - E)
  have hκI : 0 < κI := lt_min (by linarith [hE.1]) (by linarith [hE.2])
  have hEI : E ∈ BlockBand.Internal.Contracts.Layers.bulkInterval κI := by
    unfold BlockBand.Internal.Contracts.Layers.bulkInterval
    constructor
    · have := min_le_left (2 + E) (2 - E); linarith
    · have := min_le_right (2 + E) (2 - E); linarith
  set qmax : ℝ := 2 * ∑ a, ‖Q a‖
  obtain ⟨C, W₀, hC⟩ := hR b hb hb' κI hκI (τ + 1) qmax J
  refine ⟨fun M u => if M = 0 then 2 else C * (1 + ‖u‖) ^ 3 / Real.sqrt M + 1 / M,
    fun u => ?_, fun M u => ?_⟩
  · have hs : Tendsto (fun M : ℕ => (Real.sqrt M)⁻¹) atTop (𝓝 0) :=
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
    have h := (hs.const_mul (C * (1 + ‖u‖) ^ 3)).add tendsto_one_div_atTop_nhds_zero_nat
    rw [mul_zero, zero_add] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with M hM
    simp only [show M ≠ 0 by omega, ↓reduceIte, div_eq_mul_inv]
  · by_cases hM : M = 0
    · refine Eventually.of_forall fun j => ?_
      simp only [hM, ↓reduceIte]
      have := isProbabilityMeasure_sampledProbeMatrixLaw b E hτ hQ 0 (s.W j) (s.n j)
      exact norm_charFun_sub_le_two _ _ u
    · simp only [hM, ↓reduceIte]
      have hM1 : 1 ≤ M := Nat.one_le_iff_ne_zero.2 hM
      have hMpos : (0 : ℝ) < M := by exact_mod_cast hM1
      have h1 := (tendsto_charFun_rescale hCS hb hb' hE.1 hE.2 hτ hQ s u).eventually
        (gt_mem_nhds (show (0 : ℝ) < 1 / (2 * M) by positivity))
      have h3 := (tendsto_charFun_sampled_sub_discrete b E hτ hQ s M u).eventually
        (gt_mem_nhds (show (0 : ℝ) < 1 / (2 * M) by positivity))
      have hc2 := eventually_all.2 fun a => (tendsto_rescaleFactor hτ (hQ a) s).eventually
        (ge_mem_nhds (show (1 : ℝ) < 2 by norm_num))
      have hW := s.width_tendsto.eventually_ge_atTop W₀
      have hL := (tendsto_probePathLength_div τ s).eventually
        (gt_mem_nhds (show τ < τ + 1 by linarith))
      filter_upwards [h1, h3, hc2, hW, hL] with j hj1 hj3 hjc hjW hjL
      have hWpos : (0 : ℝ) < s.W j := by exact_mod_cast s.W_pos j
      have hLT : (probePathLength (s.n j) : ℝ) ≤ (τ + 1) * s.W j := by
        rw [div_lt_iff₀ hWpos] at hjL; linarith
      have hr : ∀ a k, 0 ≤ rescaledProfile τ (Q a) (s.W j) (s.n j) k ∧
          rescaledProfile τ (Q a) (s.W j) (s.n j) k ≤ qmax := by
        intro a k
        refine ⟨rescaledProfile_nonneg hτ (hQ a) _ _ k, ?_⟩
        have hc0 := rescaledProfile_nonneg hτ (hQ a) (s.W j) (s.n j) k
        unfold rescaledProfile at hc0 ⊢
        have hq : pathProfileValue (s.n j) (Q a) k ≤ ∑ a, ‖Q a‖ :=
          (le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸ ((Q a).norm_coe_le_norm _)) |>.trans
            (Finset.single_le_sum (f := fun a => ‖Q a‖) (fun _ _ => norm_nonneg _)
              (Finset.mem_univ a))
        have hq0 : 0 ≤ pathProfileValue (s.n j) (Q a) k := hQ _ _
        have hcnn : 0 ≤ rescaleFactor τ (Q a) (s.W j) (s.n j) := by
          unfold rescaleFactor
          split_ifs
          · exact zero_le_one
          · exact div_nonneg (probeMass_nonneg hτ.le (hQ a)) (mul_nonneg (by positivity)
              (Finset.sum_nonneg fun i _ => hQ _ _))
        have := hjc a
        calc rescaleFactor τ (Q a) (s.W j) (s.n j) * pathProfileValue (s.n j) (Q a) k
            ≤ 2 * ∑ a, ‖Q a‖ := mul_le_mul this hq hq0 (by norm_num)
          _ = qmax := rfl
      have h2 := hC (s.W j) hjW E hEI (probePathLength (s.n j)) hLT
        (fun a => rescaledProfile τ (Q a) (s.W j) (s.n j)) hr M hM1 u
      set φK := charFun (((globalProbeMatrixLaw b E (s.W j) (s.n j) Q :
        ProbabilityMeasure (Matrix (Fin J) (Fin J) ℂ)) : Measure _).map e) u
      set φG := charFun ((profileProbeLaw (s.W j) (probePathLength (s.n j)) J b).map (fun x =>
        e (profileProbeMatrix b E (s.W j) (probePathLength (s.n j))
          (fun a => rescaledProfile τ (Q a) (s.W j) (s.n j)) x))) u
      set φD := charFun ((discreteSampledLaw (s.W j) (probePathLength (s.n j)) J M b
        (fun a => rescaledProfile τ (Q a) (s.W j) (s.n j))).map
          (fun y => e (discreteSampledMatrix b E (s.W j) (probePathLength (s.n j))
            (fun a => rescaledProfile τ (Q a) (s.W j) (s.n j)) y))) u
      set φS := charFun ((sampledProbeMatrixLaw b E τ Q M (s.W j) (s.n j)).map e) u
      have htri : ‖φK - φS‖ ≤ ‖φK - φG‖ + ‖φG - φD‖ + ‖φS - φD‖ := by
        have := norm_sub_le_norm_sub_add_norm_sub φK φG φS
        have := norm_sub_le_norm_sub_add_norm_sub φG φD φS
        rw [norm_sub_rev φD φS] at this
        linarith
      have hsplit : (1 : ℝ) / M = 1 / (2 * M) + 1 / (2 * M) := by field_simp; ring
      rw [hsplit]
      linarith

/-- `GlobalGaussianSourceStatement` from `ComplexSourceLawContract`,
`ComplexSourceLimitAlongSequences` and `SourceReplacementStatement` (the last is proved from
`ComplexSourceLawContract` by `sourceReplacement_holds`). -/
theorem globalGaussianSource_holds_of_replacement (hCS : ComplexSourceLawContract)
    (hA : ComplexSourceLimitAlongSequences) (hR : SourceReplacementStatement) :
    GlobalGaussianSourceStatement :=
  globalGaussianSource_holds_of_lindeberg hCS hA fun _ _ hb hb' hE τ _ _ hQ =>
    globalProbeLindebergBound_of_replacement hCS hR hb hb' hE τ.2 hQ

end BlockBand.Critical.GlobalSource
