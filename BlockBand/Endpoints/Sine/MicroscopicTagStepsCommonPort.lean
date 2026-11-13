module

public import BlockBand.Endpoints.Sine.MicroscopicTagStepsRegular
public import BlockBand.Endpoints.Sine.MicroscopicTagIntegrals
public import BlockBand.Endpoints.Poisson.SequentialCollarsCertificateLaw
public import BlockBand.Endpoints.Poisson.SequentialCollarsCertificateNetwork

/-!
# Step 4 of the microscopic tag comparison: the common-port part under the prior

In Step 4 of the proof, the remaining positive clocks are exactly `L*Y_jL`, where `Y_j = U*P_jU`
on the `n-1` old and auxiliary positions. The common-port part of the uniform clock-tags
corollary is applied with a zero clock at block `0`, conditionally on the entire old path. The
fixed scalar regularity error has `Eδ = O(W⁻¹)`, and its exceptional probability is smaller than
any power of `W`. So the uniform conditional comparison integrates under the prior, and it
replaces `Lg` by `√γ h`. The scalar `γ` cancels from every ratio.

Laws: the law `mts_portLaw W b = growthPathLaw W b ⊗ layerLaw W b .common ⊗ CN(0, I_W)`
(old path read at length `r = n - 3` by `pathAt`, fresh common-port layer, `g`), and
`probedClockLaw W b = growthPathLaw W b ⊗ CN(0, I_{2W})`. Energy: a deterministic
`e ∈ bulkInterval κ`, uniformly. Inputs: `UniformClockTagsCommonPortContract`,
`MatchedTracesContract.path`, and `hasLaw_pathAt` (the grown path at length `r` has
`pathLaw W r b`).

* `mts_leadClockMatrix`: `Y_y = U*P_yU` (`U = leadResponse`), `h*Y_yh = leadPositionMass … y`
  (`mts_quadForm_leadClockMatrix`), `Y_y ⪰ 0`, `Σ_y Y_y = U*U`.
* `mts_tagClock`: the `n` tag clocks `D_j`, `j : Fin n`, i.e. the `n - 1` positions `y` and a
  zero clock (block `0`), indexed by a bijection `Option (Fin (n-3) ⊕ Fin 2) ≃ Fin n`.
* `mts_tagAverage_eq`: `n⁻¹ Σ_j Φ(n h*D_jh / h*Dh) = leadAveragedTest` (default `0` on the null
  denominator, matching Lean's `x/0 = 0` in `leadAveragedTest`).
* `mts_commonPort_step` (**(e)**): for `ε > 0` there is `W₀` such that for `W ≥ W₀`,
  `4 ≤ n ≤ TW` and `e ∈ bulkInterval κ`,
  `|E_{ported} leadAveragedTest(ω, Lg) - E_{probedClockLaw} leadAveragedTest(ω, h)| ≤ ε`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Model.Construction
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.ClocksCommonPort BlockBand.Internal.Contracts.Critical
open scoped ENNReal NNReal ComplexOrder BoundedContinuousFunction

/-!
## Quadratic forms
-/

theorem mts_quadForm_sum {ι κ : Type*} [Fintype ι] (s : Finset κ) (A : κ → Matrix ι ι ℂ)
    (v : ι → ℂ) : quadForm (∑ j ∈ s, A j) v = ∑ j ∈ s, quadForm (A j) v := by
  unfold quadForm
  rw [Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]

theorem mts_quadForm_smul_real {ι : Type*} [Fintype ι] (c : ℝ) (A : Matrix ι ι ℂ) (v : ι → ℂ) :
    quadForm ((c : ℂ) • A) v = c * quadForm A v := by
  unfold quadForm
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]

theorem mts_quadForm_zero {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    quadForm (0 : Matrix ι ι ℂ) v = 0 := by
  simp [quadForm]

theorem mts_quadForm_conj_diagonal {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (U : Matrix ι κ ℂ) (d : ι → ℝ) (h : κ → ℂ) :
    quadForm (Uᴴ * Matrix.diagonal (fun x => (d x : ℂ)) * U) h =
      ∑ x, d x * ‖(U *ᵥ h) x‖ ^ 2 := by
  unfold quadForm
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.star_mulVec]
  simp only [dotProduct, Matrix.mulVec_diagonal, Complex.re_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im]
  ring

/-!
## The lead clock matrices `Y_y = U*P_yU`
-/

/-- The position (`Fin r ⊕ Fin 2`) of a site of the matched-lead path. -/
def mts_sitePos {W r : ℕ} : FullSite W r → Fin r ⊕ Fin 2
  | Sum.inl x => Sum.inl x.1
  | Sum.inr x => Sum.inr x.1

/-- `Y_y = U*P_yU`, `U = leadResponse` (port columns of the matched-lead inverse), `P_y` the
coordinate projector of position `y`. -/
def mts_leadClockMatrix (b e : ℝ) (W r : ℕ) (ω : GrowthPath W) (y : Fin r ⊕ Fin 2) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  Matrix.conjTranspose (leadResponse b e W r ω) *
    Matrix.diagonal (fun x : FullSite W r => (((if mts_sitePos x = y then 1 else 0 : ℝ)) : ℂ)) *
    leadResponse b e W r ω

theorem mts_quadForm_leadClockMatrix (b e : ℝ) (W r : ℕ) (ω : GrowthPath W)
    (y : Fin r ⊕ Fin 2) (h : Fin 2 × Fin W → ℂ) :
    quadForm (mts_leadClockMatrix b e W r ω y) h = leadPositionMass b e W r ω h y := by
  unfold mts_leadClockMatrix
  rw [mts_quadForm_conj_diagonal]
  rcases y with i | j
  · simp only [leadPositionMass, Fintype.sum_sum_type, Fintype.sum_prod_type, mts_sitePos,
      Sum.inl.injEq, reduceCtorEq, ite_false, zero_mul, Finset.sum_const_zero, add_zero,
      ite_mul, one_mul]
    rw [Finset.sum_eq_single i (fun x _ hx => by simp [hx]) (by simp)]
    simp
  · simp only [leadPositionMass, Fintype.sum_sum_type, Fintype.sum_prod_type, mts_sitePos,
      Sum.inr.injEq, reduceCtorEq, ite_false, zero_mul, Finset.sum_const_zero, zero_add,
      ite_mul, one_mul]
    rw [Finset.sum_eq_single j (fun x _ hx => by simp [hx]) (by simp)]
    simp

theorem mts_leadClockMatrix_posSemidef (b e : ℝ) (W r : ℕ) (ω : GrowthPath W)
    (y : Fin r ⊕ Fin 2) : (mts_leadClockMatrix b e W r ω y).PosSemidef := by
  unfold mts_leadClockMatrix
  refine PosSemidef.conjTranspose_mul_mul_same ?_ _
  rw [posSemidef_diagonal_iff]
  intro x
  split_ifs <;> simp

theorem mts_sum_leadClockMatrix (b e : ℝ) (W r : ℕ) (ω : GrowthPath W) :
    ∑ y, mts_leadClockMatrix b e W r ω y =
      Matrix.conjTranspose (leadResponse b e W r ω) * leadResponse b e W r ω := by
  have hsum : ∑ y, Matrix.diagonal (fun x : FullSite W r =>
      (((if mts_sitePos x = y then 1 else 0 : ℝ)) : ℂ)) = 1 := by
    ext x x'
    rw [Matrix.sum_apply]
    by_cases hxx : x = x'
    · subst hxx
      simp only [diagonal_apply_eq, one_apply_eq]
      rw [Finset.sum_eq_single (mts_sitePos x)]
      · simp
      · intro y _ hy; simp [Ne.symm hy]
      · simp
    · simp [diagonal_apply_ne _ hxx, one_apply_ne hxx]
  unfold mts_leadClockMatrix
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, hsum, Matrix.mul_one]

theorem mts_sum_quadForm_leadClockMatrix (b e : ℝ) (W r : ℕ) (ω : GrowthPath W)
    (h : Fin 2 × Fin W → ℂ) :
    quadForm (∑ y, mts_leadClockMatrix b e W r ω y) h = totalLeadMass b e W r (ω, h) := by
  rw [mts_quadForm_sum]
  unfold totalLeadMass
  exact Finset.sum_congr rfl fun y _ => mts_quadForm_leadClockMatrix b e W r ω y h

/-- If `Re Tr(U*U) = 0` then every lead mass vanishes. -/
theorem mts_leadPositionMass_eq_zero_of_trace (b e : ℝ) (W r : ℕ) (ω : GrowthPath W)
    (htr : ((leadResponse b e W r ω)ᴴ * leadResponse b e W r ω).trace.re = 0)
    (h : Fin 2 × Fin W → ℂ) (y : Fin r ⊕ Fin 2) : leadPositionMass b e W r ω h y = 0 := by
  have hpsd : ((leadResponse b e W r ω)ᴴ * leadResponse b e W r ω).PosSemidef :=
    posSemidef_conjTranspose_mul_self _
  have hnn := hpsd.trace_nonneg
  have htr0 : ((leadResponse b e W r ω)ᴴ * leadResponse b e W r ω).trace = 0 := by
    apply Complex.ext
    · simpa using htr
    · have := (Complex.nonneg_iff.1 hnn).2
      simpa using this.symm
  have hU := trace_conjTranspose_mul_self_eq_zero_iff.1 htr0
  unfold leadPositionMass
  rw [hU]
  rcases y with i | j <;> simp

/-!
## The `n` tag clocks with a zero clock at block `0`
-/

/-- A bijection between the `n` ring tags and `{block 0} ⊔ (n - 1 positions)`. -/
def mts_tagEquiv (n : ℕ) (hn : 3 ≤ n) : Option (Fin (n - 3) ⊕ Fin 2) ≃ Fin n :=
  Fintype.equivFinOfCardEq (by
    simp only [Fintype.card_option, Fintype.card_sum, Fintype.card_fin]
    omega)

/-- The tag clocks `D_j` (`j : Fin n`): `Y_y` on the `n - 1` old and auxiliary positions, `0` at
the removed block. -/
def mts_tagClock (b e : ℝ) (n W : ℕ) (hn : 3 ≤ n) (ω : GrowthPath W) (j : Fin n) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  ((mts_tagEquiv n hn).symm j).elim 0 (mts_leadClockMatrix b e W (n - 3) ω)

theorem mts_sum_tag {α : Type*} [AddCommMonoid α] (b e : ℝ) (n W : ℕ) (hn : 3 ≤ n)
    (ω : GrowthPath W) (F : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ → α) :
    ∑ j, F (mts_tagClock b e n W hn ω j) =
      F 0 + ∑ y, F (mts_leadClockMatrix b e W (n - 3) ω y) := by
  rw [← (mts_tagEquiv n hn).sum_comp, Fintype.sum_option]
  simp [mts_tagClock]

theorem mts_sum_tagClock (b e : ℝ) (n W : ℕ) (hn : 3 ≤ n) (ω : GrowthPath W) :
    ∑ j, mts_tagClock b e n W hn ω j = ∑ y, mts_leadClockMatrix b e W (n - 3) ω y := by
  have := mts_sum_tag b e n W hn ω id
  simpa using this

theorem mts_tagClock_posSemidef (b e : ℝ) (n W : ℕ) (hn : 3 ≤ n) (ω : GrowthPath W)
    (j : Fin n) : (mts_tagClock b e n W hn ω j).PosSemidef := by
  unfold mts_tagClock
  rcases ((mts_tagEquiv n hn).symm j) with _ | y
  · exact PosSemidef.zero
  · exact mts_leadClockMatrix_posSemidef b e W (n - 3) ω y

/-- The ratio of the contract, with default `0`, is `n h*Y_yh / h*Y^{all}h` (Lean's `x/0 = 0`). -/
theorem mts_ratio_eq {W : ℕ} (C D : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (n : ℕ)
    (h : Fin 2 × Fin W → ℂ) :
    ratioHalfLine ((n : ℂ) • C) D (fun _ => 0) h =
      Set.projIci 0 ((n : ℝ) * quadForm C h / quadForm D h) := by
  unfold ratioHalfLine
  have : ((n : ℂ) • C) = ((n : ℝ) : ℂ) • C := by norm_cast
  rw [this, mts_quadForm_smul_real]
  split_ifs with hD
  · rw [hD, div_zero]
  · rfl

/-- `n⁻¹ Σ_j Φ(n h*D_jh / h*Dh) = leadAveragedTest` for every probe vector. -/
theorem mts_tagAverage_eq (b e : ℝ) {n W : ℕ} (hn : 3 ≤ n) (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ)
    (ω : GrowthPath W) (h : Fin 2 × Fin W → ℂ) :
    (n : ℝ)⁻¹ * ∑ j, Φ (ratioHalfLine ((n : ℂ) • mts_tagClock b e n W hn ω j)
        (∑ j, mts_tagClock b e n W hn ω j) (fun _ => 0) h) =
      leadAveragedTest b e n W Φ (ω, h) := by
  rw [mts_sum_tag b e n W hn ω (fun D => Φ (ratioHalfLine ((n : ℂ) • D)
    (∑ j, mts_tagClock b e n W hn ω j) (fun _ => 0) h))]
  unfold leadAveragedTest
  congr 2
  · rw [mts_ratio_eq, mts_quadForm_zero, mul_zero, zero_div]
  · refine Finset.sum_congr rfl fun y _ => ?_
    rw [mts_ratio_eq, mts_sum_tagClock, mts_sum_quadForm_leadClockMatrix,
      mts_quadForm_leadClockMatrix]

/-- On the null event `Re Tr(U*U) = 0` the averaged test does not depend on the probe. -/
theorem mts_leadAveragedTest_of_trace (b e : ℝ) {n W : ℕ} (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ)
    (ω : GrowthPath W)
    (htr : ((leadResponse b e W (n - 3) ω)ᴴ * leadResponse b e W (n - 3) ω).trace.re = 0)
    (h h' : Fin 2 × Fin W → ℂ) :
    leadAveragedTest b e n W Φ (ω, h) = leadAveragedTest b e n W Φ (ω, h') := by
  unfold leadAveragedTest totalLeadMass
  simp only [mts_leadPositionMass_eq_zero_of_trace b e W (n - 3) ω htr]

/-!
## Measurability of the transported probe
-/

theorem mts_measurable_blockDiag {α : Type*} [MeasurableSpace α] {k W : ℕ}
    {A : α → Fin k → Matrix (Fin W) (Fin W) ℂ} (hA : Measurable A) :
    Measurable fun a => BlockBand.Internal.Contracts.Layers.blockDiag (A a) := by
  refine Measurable.of_eval fun x => Measurable.of_eval fun y => ?_
  by_cases h : x.1 = y.1
  · simp only [BlockBand.Internal.Contracts.Layers.blockDiag, h, ite_true]
    exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp
      ((measurable_pi_apply _).comp hA))
  · simp only [BlockBand.Internal.Contracts.Layers.blockDiag, h, ite_false]
    exact measurable_const

theorem mts_measurable_bondMatrix {α : Type*} [MeasurableSpace α] {W : ℕ} (σ : LayerShape)
    {B : α → Fin σ.blocks → Fin σ.ports → Matrix (Fin W) (Fin W) ℂ} (hB : Measurable B) :
    Measurable fun a => bondMatrix σ (B a) := by
  refine Measurable.of_eval fun x => Measurable.of_eval fun y => ?_
  by_cases h : σ.incident x.1 y.1 = true
  · simp only [bondMatrix, h, ite_true]
    exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp
      ((measurable_pi_apply _).comp ((measurable_pi_apply _).comp hB)))
  · simp only [bondMatrix, h]
    exact measurable_const

theorem mts_measurable_commonPortL (b e : ℝ) {W : ℕ} {α : Type*} [MeasurableSpace α]
    {X : α → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {ω : α → LayerSample W .common}
    (hX : Measurable X) (hω : Measurable ω) :
    Measurable (fun a => commonPortL b e (X a) (ω a)) := by
  have hdiag : Measurable (fun a =>
      BlockBand.Internal.Contracts.Layers.blockDiag (ω a).1 - (e : ℂ) • 1 - X a) :=
    measurable_mat_sub (measurable_mat_sub (mts_measurable_blockDiag
      (measurable_fst.comp hω)) measurable_const) hX
  have hbond : Measurable (fun a => bondMatrix .common (ω a).2) :=
    mts_measurable_bondMatrix .common (measurable_snd.comp hω)
  have hM : Measurable (fun a => layerMatrix .common e (commonZ b e) (X a) (ω a)) := by
    unfold layerMatrix
    exact measurable_fromBlocks hdiag hbond (measurable_conjTranspose''.comp hbond)
      measurable_const
  have hinv : Measurable (fun a => (layerMatrix .common e (commonZ b e) (X a) (ω a))⁻¹) :=
    measurable_matrix_inv.comp hM
  have hG : Measurable (fun a => (commonPortResolvent b e (X a) (ω a)).toBlocks₁₂) := by
    refine Measurable.of_eval fun x => Measurable.of_eval fun y => ?_
    exact (measurable_pi_apply (Sum.inr y)).comp ((measurable_pi_apply (Sum.inl x)).comp hinv)
  have hK : Measurable (fun a => matchedLeadK b e (X a)) := by
    unfold matchedLeadK
    exact measurable_mat_sub measurable_const hX
  unfold commonPortL
  exact measurable_mat_mul hK hG

theorem mts_measurable_mulVec {α ι κ : Type*} [MeasurableSpace α] [Fintype κ]
    {M : α → Matrix ι κ ℂ} {v : α → κ → ℂ} (hM : Measurable M) (hv : Measurable v) :
    Measurable fun a => M a *ᵥ v a := by
  refine Measurable.of_eval fun x => ?_
  simp only [mulVec, dotProduct]
  exact Finset.measurable_sum _ fun z _ =>
    ((measurable_pi_apply _).comp ((measurable_pi_apply _).comp hM)).mul
      ((measurable_pi_apply _).comp hv)

theorem mts_measurable_leadSchur (e : ℝ) (W r : ℕ) :
    Measurable (fun ω : GrowthPath W => leadSchur e W r ω) :=
  (measurable_pathSchur e).comp (measurable_pathAt W r)

/-- The ported probe `(ω, (layer, g)) ↦ (ω, L(X(ω)) g)` is measurable. -/
theorem mts_measurable_portProbe (b e : ℝ) (W r : ℕ) :
    Measurable (fun y : GrowthPath W × (LayerSample W .common × (Fin 1 × Fin W → ℂ)) =>
      (y.1, commonPortProbe b e (leadSchur e W r y.1) y.2)) := by
  have h2 : Measurable (fun y : GrowthPath W × (LayerSample W .common × (Fin 1 × Fin W → ℂ)) =>
      commonPortL b e (leadSchur e W r y.1) y.2.1) :=
    mts_measurable_commonPortL b e ((mts_measurable_leadSchur e W r).comp measurable_fst)
      (measurable_fst.comp measurable_snd)
  have h3 : Measurable (fun y : GrowthPath W × (LayerSample W .common × (Fin 1 × Fin W → ℂ)) =>
      y.2.2) := measurable_snd.comp measurable_snd
  refine measurable_fst.prodMk ?_
  unfold commonPortProbe
  exact mts_measurable_mulVec h2 h3

theorem mts_measurable_ratioHalfLine {ι : Type*} [Fintype ι]
    (C D : Matrix ι ι ℂ) : Measurable (fun v : ι → ℂ => ratioHalfLine C D (fun _ => 0) v) := by
  have hq : ∀ A : Matrix ι ι ℂ, Measurable (fun v : ι → ℂ => quadForm A v) := by
    intro A
    have hc : Continuous (fun v : ι → ℂ => (star v ⬝ᵥ (A *ᵥ v)).re) := by fun_prop
    exact hc.measurable
  unfold ratioHalfLine
  refine continuous_projIci_zero.measurable.comp ?_
  exact Measurable.ite (measurableSet_eq_fun (hq D) measurable_const) measurable_const
    ((hq C).div (hq D))

/-!
## The prior bound on the scalar regularity error
-/

/-- Markov's inequality for `δ(X_r) = matchedDistance b e (leadSchur e W r ω)` under the grown
path prior, from the `L^q(pathLaw)` bound (via `hasLaw_pathAt`). -/
theorem mts_lead_tail_le (b e : ℝ) (W r : ℕ) (hr : 1 ≤ r) (δ q : ℝ) (hδ : 0 < δ) (hq : 0 < q)
    {B : ℝ} (hB0 : 0 ≤ B)
    (hB : eLpNorm (fun ps : PathSample W r => matchedDistance b e (pathSchur e ps))
      (ENNReal.ofReal q) (pathLaw W r b) ≤ ENNReal.ofReal B) :
    growthPathLaw W b {ω | δ < matchedDistance b e (leadSchur e W r ω)} ≤
      ENNReal.ofReal ((δ⁻¹ * B) ^ q) := by
  have hX := hasLaw_pathAt W r b hr
  have hdm : Measurable fun ps : PathSample W r => matchedDistance b e (pathSchur e ps) :=
    (measurable_matchedDistance b e).comp (measurable_pathSchur e)
  have hsub : {ω | δ < matchedDistance b e (leadSchur e W r ω)} ⊆
      {ω | ENNReal.ofReal δ ≤ ‖(fun ps : PathSample W r => matchedDistance b e
        (pathSchur e ps)) (pathAt W r ω)‖ₑ} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (hω.le.trans (le_abs_self _))
  refine (measure_mono hsub).trans ?_
  have hq0 : ENNReal.ofReal q ≠ 0 := by simpa using hq
  have hM := meas_ge_le_mul_pow_eLpNorm_enorm (growthPathLaw W b) hq0 ENNReal.ofReal_ne_top
    (f := (fun ps : PathSample W r => matchedDistance b e (pathSchur e ps)) ∘ pathAt W r)
    (ε := ENNReal.ofReal δ) (by simpa using hδ) (by simp)
  refine hM.trans ?_
  have heq : eLpNorm ((fun ps : PathSample W r => matchedDistance b e (pathSchur e ps)) ∘
      pathAt W r) (ENNReal.ofReal q) (growthPathLaw W b) =
      eLpNorm (fun ps : PathSample W r => matchedDistance b e (pathSchur e ps))
        (ENNReal.ofReal q) (pathLaw W r b) := by
    rw [← eLpNorm_map_measure hdm.aestronglyMeasurable hX.aemeasurable, hX.map_eq]
  rw [heq, ENNReal.toReal_ofReal hq.le]
  calc (ENNReal.ofReal δ)⁻¹ ^ q * eLpNorm (fun ps : PathSample W r =>
        matchedDistance b e (pathSchur e ps)) (ENNReal.ofReal q) (pathLaw W r b) ^ q
      ≤ (ENNReal.ofReal δ)⁻¹ ^ q * (ENNReal.ofReal B) ^ q := by
        gcongr
    _ = ENNReal.ofReal ((δ⁻¹ * B) ^ q) := by
        rw [← ENNReal.ofReal_inv_of_pos hδ, ENNReal.ofReal_rpow_of_nonneg (by positivity) hq.le,
          ENNReal.ofReal_rpow_of_nonneg hB0 hq.le, ← ENNReal.ofReal_mul (by positivity),
          Real.mul_rpow (by positivity) hB0]

/-!
## (e) The common-port comparison under the prior
-/

theorem mts_isProbabilityMeasure_commonPortProbeLaw (W : ℕ) (b : ℝ) :
    IsProbabilityMeasure (commonPortProbeLaw W b) := by
  have i1 : ∀ _ : Fin 2, IsProbabilityMeasure (gueMeasure (Fin W)
      (Real.toNNReal ((1 - 2 * b) / W))) := fun _ => passDeriv_isProbabilityMeasure_gue _ _
  have i2 : ∀ _ : Fin 2, ∀ _ : Fin 1, IsProbabilityMeasure
      (ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W))) :=
    fun _ _ => passDeriv_isProbabilityMeasure_ginibre _ _ _
  unfold commonPortProbeLaw layerLaw
  infer_instance

/-- **Step 4, the common-port part, integrated under the prior.** Hypotheses:
`UniformClockTagsCommonPortContract` and `MatchedTracesContract`. Fixed first `b ∈ (0,1/2)`,
`κ > 0`, `T` and `Φ ∈ C_b([0,∞))`. For every `ε > 0` there is `W₀`; for `W ≥ W₀`, every
`4 ≤ n ≤ TW` and deterministic `e ∈ bulkInterval κ`, with `r = n - 3`, `X = leadSchur e W r ω`
the old self-energy and `Lg = commonPortProbe`:
`|E_{ω,layer,g} leadAveragedTest(ω, Lg) - E_{ω,h} leadAveragedTest(ω, h)| ≤ ε`
(the tags are the `n - 1` old and auxiliary positions and a zero clock at block `0`; the
scalar `γ` does not appear since the test is a ratio). -/
theorem mts_commonPort_step (hCP : UniformClockTagsCommonPortContract)
    (hMT : MatchedTracesContract) {b : ℝ} (hb : 0 < b) (hb' : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ)
    (T : ℝ) (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ n : ℕ, 4 ≤ n → (n : ℝ) ≤ T * W → ∀ e ∈ bulkInterval κ,
      |(∫ y, leadAveragedTest b e n W Φ (y.1, commonPortProbe b e (leadSchur e W (n - 3) y.1) y.2)
          ∂mts_portLaw W b) -
        ∫ x, leadAveragedTest b e n W Φ x ∂probedClockLaw W b| ≤ ε := by
  obtain ⟨δ₀, W₁, hδ₀, hW₁⟩ := hCP b hb hb' κ hκ Φ (ε / 2) (by linarith)
  obtain ⟨ε₀, C, hε₀, hMTb⟩ := hMT.path b hb hb' κ T hκ
  set C' := max C 0
  set K : ℝ := (δ₀⁻¹ * (C' * Real.sqrt 2)) ^ (2 : ℝ)
  have hK : 0 ≤ K := Real.rpow_nonneg (by positivity) _
  set M := ‖Φ‖
  refine ⟨max W₁ (max (⌈2 / ε₀⌉₊) (⌈4 * M * K / ε⌉₊ + 1)), ?_⟩
  intro W hW n hn hnT e he
  have hW1 : W₁ ≤ W := (le_max_left _ _).trans hW
  have hWε : 2 / ε₀ ≤ W := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_left _ _).trans ((le_max_right _ _).trans hW))
  have hWK : 4 * M * K / ε + 1 ≤ W := by
    have h2 : ((⌈4 * M * K / ε⌉₊ + 1 : ℕ) : ℝ) ≤ W := by
      exact_mod_cast (le_max_right _ _).trans ((le_max_right _ _).trans hW)
    push_cast at h2
    linarith [Nat.le_ceil (4 * M * K / ε)]
  have hWpos : (0 : ℝ) < W := by
    have : (1 : ℝ) ≤ 4 * M * K / ε + 1 := by
      have : 0 ≤ 4 * M * K / ε := by positivity
      linarith
    linarith
  have hW0 : 0 < W := by exact_mod_cast hWpos
  have hn3 : 3 ≤ n := by omega
  set r := n - 3
  have hr1 : 1 ≤ r := by omega
  have hrT : (r : ℝ) ≤ T * W := by
    have : (r : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 3
    linarith
  -- probability measures
  have hPg := passDeriv_isProbabilityMeasure_growthPathLaw W b
  have hPc := mts_isProbabilityMeasure_commonPortProbeLaw W b
  have hPh := isProbabilityMeasure_probedClockLaw W b
  have hPcv : IsProbabilityMeasure (circularVectorLaw (Fin 2 × Fin W)) := by
    unfold circularVectorLaw; infer_instance
  -- the two integrands and their bounds
  set f : GrowthPath W × (LayerSample W .common × (Fin 1 × Fin W → ℂ)) → ℝ := fun y =>
    leadAveragedTest b e n W Φ (y.1, commonPortProbe b e (leadSchur e W r y.1) y.2)
  set g : GrowthPath W × (Fin 2 × Fin W → ℂ) → ℝ := fun x => leadAveragedTest b e n W Φ x
  have hfm : Measurable f :=
    measurable_leadAveragedTest_of b n W Φ measurable_const (mts_measurable_portProbe b e W r)
  have hgm : Measurable g :=
    measurable_leadAveragedTest_of b n W Φ measurable_const measurable_id
  have hfb : ∀ y, |f y| ≤ M := fun y => abs_leadAveragedTest_le b e hn W Φ _
  have hgb : ∀ x, |g x| ≤ M := fun x => abs_leadAveragedTest_le b e hn W Φ _
  have hfi : Integrable f (mts_portLaw W b) := by
    unfold mts_portLaw
    exact Integrable.of_bound hfm.aestronglyMeasurable M
      (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hfb y)
  have hgi : Integrable g (probedClockLaw W b) := by
    unfold probedClockLaw
    exact Integrable.of_bound hgm.aestronglyMeasurable M
      (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hgb y)
  set A : GrowthPath W → ℝ := fun ω => ∫ x, f (ω, x) ∂commonPortProbeLaw W b
  set B : GrowthPath W → ℝ := fun ω => ∫ h, g (ω, h) ∂circularVectorLaw (Fin 2 × Fin W)
  have hAeq : (∫ y, f y ∂mts_portLaw W b) = ∫ ω, A ω ∂growthPathLaw W b := by
    unfold mts_portLaw; exact integral_prod f hfi
  have hBeq : (∫ x, g x ∂probedClockLaw W b) = ∫ ω, B ω ∂growthPathLaw W b := by
    unfold probedClockLaw; exact integral_prod g hgi
  have hAi : Integrable A (growthPathLaw W b) := by
    unfold mts_portLaw at hfi; exact hfi.integral_prod_left
  have hBi : Integrable B (growthPathLaw W b) := by
    unfold probedClockLaw at hgi; exact hgi.integral_prod_left
  have hAb : ∀ ω, |A ω| ≤ M := by
    intro ω
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (C := M) (ae_of_all _ fun x => ?_)).trans ?_
    · rw [Real.norm_eq_abs]; exact hfb _
    · simp
  have hBb : ∀ ω, |B ω| ≤ M := by
    intro ω
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (C := M) (ae_of_all _ fun x => ?_)).trans ?_
    · rw [Real.norm_eq_abs]; exact hgb _
    · simp
  -- the bad set
  set bad : Set (GrowthPath W) :=
    {ω | ¬ ∀ k, (ω.1 k).IsHermitian} ∪ {ω | δ₀ < matchedDistance b e (leadSchur e W r ω)}
  have hbadm : MeasurableSet bad := by
    refine MeasurableSet.union ?_ ?_
    · have hH : MeasurableSet {ω : GrowthPath W | ∀ k, (ω.1 k).IsHermitian} := by
        have : {ω : GrowthPath W | ∀ k, (ω.1 k).IsHermitian} =
            ⋂ k, {ω | (ω.1 k).IsHermitian} := by
          ext ω; simp
        rw [this]
        exact MeasurableSet.iInter fun k =>
          measurableSet_isHermitian.preimage ((measurable_pi_apply k).comp measurable_fst)
      exact hH.compl
    · exact measurableSet_lt measurable_const
        ((measurable_matchedDistance b e).comp (mts_measurable_leadSchur e W r))
  have hbad1 : growthPathLaw W b {ω | ¬ ∀ k, (ω.1 k).IsHermitian} = 0 := by
    have := ae_growthPath_isHermitian W b
    rwa [ae_iff] at this
  have hbad2 : growthPathLaw W b {ω | δ₀ < matchedDistance b e (leadSchur e W r ω)} ≤
      ENNReal.ofReal (K / W ^ (2 : ℝ)) := by
    have hp2 : (2 : ℝ) ≤ ε₀ * W := by
      rw [div_le_iff₀ hε₀] at hWε; linarith
    have hL := hMTb W hW0 2 le_rfl hp2 r hr1 hrT e he
    have hL' : eLpNorm (fun ps : PathSample W r => matchedDistance b e (pathSchur e ps))
        (ENNReal.ofReal 2) (pathLaw W r b) ≤ ENNReal.ofReal (C' * Real.sqrt 2 / W) := by
      refine hL.trans (ENNReal.ofReal_le_ofReal ?_)
      gcongr
      exact le_max_left _ _
    refine (mts_lead_tail_le b e W r hr1 δ₀ 2 hδ₀ (by norm_num) (by positivity) hL').trans
      (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    unfold K
    rw [mul_div_assoc', div_eq_mul_inv, Real.mul_rpow (by positivity) (by positivity),
      Real.inv_rpow hWpos.le]
    ring_nf
  have hbad : (growthPathLaw W b bad).toReal ≤ K / W ^ (2 : ℝ) := by
    have h := (measure_union_le (μ := growthPathLaw W b) _ _).trans
      (add_le_add (le_of_eq hbad1) hbad2)
    rw [zero_add] at h
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) h
  -- the good-set comparison
  have hgood : ∀ ω, ω ∉ bad → |A ω - B ω| ≤ ε / 2 := by
    intro ω hω
    simp only [bad, Set.mem_union, Set.mem_ofPred_eq, not_or, not_not, not_lt] at hω
    obtain ⟨hH, hδ⟩ := hω
    have hXH : (leadSchur e W r ω).IsHermitian :=
      pathSchur_isHermitian e (pathAt W r ω) (fun i => hH _)
    by_cases htr : ((leadResponse b e W r ω)ᴴ * leadResponse b e W r ω).trace.re = 0
    · have hA : A ω = g (ω, 0) := by
        simp only [A, f]
        rw [show (fun x => leadAveragedTest b e n W Φ (ω, commonPortProbe b e
            (leadSchur e W r ω) x)) = fun _ => g (ω, 0) from funext fun x =>
              mts_leadAveragedTest_of_trace b e Φ ω htr _ _]
        simp
      have hB : B ω = g (ω, 0) := by
        simp only [B]
        rw [show (fun h => g (ω, h)) = fun _ => g (ω, 0) from funext fun h =>
          mts_leadAveragedTest_of_trace b e Φ ω htr _ _]
        simp
      rw [hA, hB, sub_self, abs_zero]; linarith
    · have htr' : 0 < (∑ j, mts_tagClock b e n W hn3 ω j).trace.re := by
        rw [mts_sum_tagClock, mts_sum_leadClockMatrix]
        have hnn := (posSemidef_conjTranspose_mul_self (leadResponse b e W r ω)).trace_nonneg
        exact lt_of_le_of_ne (Complex.nonneg_iff.1 hnn).1 (Ne.symm htr)
      have hC := hW₁ W hW0 hW1 (leadSchur e W r ω) hXH e he hδ n (by omega)
        (mts_tagClock b e n W hn3 ω) (mts_tagClock_posSemidef b e n W hn3 ω) htr'
        (fun _ => 0) measurable_const
      have hint1 : ∀ j, Integrable (fun x => Φ (ratioHalfLine ((n : ℂ) • mts_tagClock b e n W hn3 ω j)
          (∑ j, mts_tagClock b e n W hn3 ω j) (fun _ => 0)
          (commonPortProbe b e (leadSchur e W r ω) x))) (commonPortProbeLaw W b) := by
        intro j
        refine Integrable.of_bound (Φ.continuous.measurable.comp ((mts_measurable_ratioHalfLine _ _).comp
          (measurable_snd.comp ((mts_measurable_portProbe b e W r).comp
            (measurable_const.prodMk measurable_id))))).aestronglyMeasurable M
          (ae_of_all _ fun x => ?_)
        rw [Real.norm_eq_abs]; exact norm_test_le Φ _
      have hint2 : ∀ j, Integrable (fun h => Φ (ratioHalfLine ((n : ℂ) • mts_tagClock b e n W hn3 ω j)
          (∑ j, mts_tagClock b e n W hn3 ω j) (fun _ => 0) h))
          (circularVectorLaw (Fin 2 × Fin W)) := by
        intro j
        refine Integrable.of_bound (Φ.continuous.measurable.comp
          (mts_measurable_ratioHalfLine _ _)).aestronglyMeasurable M (ae_of_all _ fun x => ?_)
        rw [Real.norm_eq_abs]; exact norm_test_le Φ _
      have hA : A ω = (n : ℝ)⁻¹ * ∑ j, ∫ x, Φ (ratioHalfLine ((n : ℂ) •
          mts_tagClock b e n W hn3 ω j) (∑ j, mts_tagClock b e n W hn3 ω j) (fun _ => 0)
          (commonPortProbe b e (leadSchur e W r ω) x)) ∂commonPortProbeLaw W b := by
        rw [← integral_finsetSum _ fun j _ => hint1 j, ← integral_const_mul]
        simp only [A, f]
        exact integral_congr_ae (ae_of_all _ fun x => (mts_tagAverage_eq b e hn3 Φ ω _).symm)
      have hB : B ω = (n : ℝ)⁻¹ * ∑ j, ∫ h, Φ (ratioHalfLine ((n : ℂ) •
          mts_tagClock b e n W hn3 ω j) (∑ j, mts_tagClock b e n W hn3 ω j) (fun _ => 0) h)
          ∂circularVectorLaw (Fin 2 × Fin W) := by
        rw [← integral_finsetSum _ fun j _ => hint2 j, ← integral_const_mul]
        simp only [B, g]
        exact integral_congr_ae (ae_of_all _ fun h => (mts_tagAverage_eq b e hn3 Φ ω _).symm)
      rw [hA, hB]
      exact hC
  -- integrate
  have hpt : ∀ ω, |A ω - B ω| ≤ ε / 2 + 2 * M * bad.indicator 1 ω := by
    intro ω
    by_cases hω : ω ∈ bad
    · rw [Set.indicator_of_mem hω, Pi.one_apply, mul_one]
      have := (abs_sub _ _).trans (add_le_add (hAb ω) (hBb ω))
      linarith
    · rw [Set.indicator_of_notMem hω, mul_zero, add_zero]
      exact hgood ω hω
  have hind : Integrable (bad.indicator (1 : GrowthPath W → ℝ)) (growthPathLaw W b) :=
    (integrable_const (1 : ℝ)).indicator hbadm
  rw [hAeq, hBeq, ← integral_sub hAi hBi]
  calc |∫ ω, (A ω - B ω) ∂growthPathLaw W b|
      ≤ ∫ ω, |A ω - B ω| ∂growthPathLaw W b := abs_integral_le_integral_abs
    _ ≤ ∫ ω, (ε / 2 + 2 * M * bad.indicator 1 ω) ∂growthPathLaw W b :=
        integral_mono (hAi.sub hBi).abs ((integrable_const _).add (hind.const_mul _)) hpt
    _ = ε / 2 + 2 * M * (growthPathLaw W b bad).toReal := by
        rw [integral_add (integrable_const _) (hind.const_mul _), integral_const,
          integral_const_mul, integral_indicator_one hbadm]
        simp [Measure.real]
    _ ≤ ε / 2 + 2 * M * (K / W ^ (2 : ℝ)) := by gcongr
    _ ≤ ε := by
        have hW1' : (1 : ℝ) ≤ W := by
          have : 0 ≤ 4 * M * K / ε := by positivity
          linarith
        have hW2 : (W : ℝ) ≤ W ^ (2 : ℝ) := by
          rw [Real.rpow_two]; nlinarith
        have h1 : K / W ^ (2 : ℝ) ≤ K / W :=
          div_le_div_of_nonneg_left hK hWpos hW2
        have h2 : 2 * M * (K / W) ≤ ε / 2 := by
          rw [mul_div_assoc', div_le_iff₀ hWpos]
          have : 4 * M * K / ε ≤ W := by linarith
          rw [div_le_iff₀ hε] at this
          nlinarith
        have hM0 : 0 ≤ M := norm_nonneg _
        nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * M)]

end BlockBand.Endpoints
