module

public import BlockBand.Critical.MatrixClosing.Stable
public import BlockBand.Critical.EntireLaw.Statements
public import BlockBand.Critical.EntireLaw.Measurability
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Analysis.Matrix.Order

/-!
# The entire law: the closed-source limit

* (i) `continuous_sqrtProbeGram` (Mathlib isometric Hermitian functional calculus),
  `closedPhase` (phase of `closedSourceMatrix K (Re M)`, modulus one), `continuous_closedPhase`,
  the bounded continuous tests `closedPhaseRe`, `closedPhaseIm`, `closedPhase_of_isHermitian`.
* **`tendsto_closedPhase_of_oldData`** (premise `MatrixClosingStatement`): old data
  `(K_n, X_n, F_n)` independent of the collar, `X_n` Hermitian a.s., `F_n` orthonormal a.s.,
  `d(X_n) → 0` in probability, `K_n ⇒ κ`: the phase expectations of
  `closedSourceMatrix K_n (closingMatrix b E 0 X_n F_n ω)` converge to
  `∫κ ∫P exp{-iΣσ_j𝒯(K, C₀)_jj}` (Fubini included).
* Matrix `SecondCountableTopology`/`PolishSpace`/`BorelSpace` instances are `local`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.EntireLaw

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.Critical
open BlockBand.Internal.Contracts.CriticalEntire
open BlockBand.Critical.MatrixClosing
open scoped BoundedContinuousFunction ENNReal

variable {J : ℕ}

/-- Matrices (product topology) are second countable (local). -/
local instance matrix_secondCountableTopology'' (r : ℕ) :
    SecondCountableTopology (Matrix (Fin r) (Fin r) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin r → Fin r → ℂ))

/-- Matrices (product topology) are Polish (local). -/
local instance matrix_polishSpace'' (r : ℕ) : PolishSpace (Matrix (Fin r) (Fin r) ℂ) :=
  inferInstanceAs (PolishSpace (Fin r → Fin r → ℂ))

local instance matrix_borelSpace'' (r : ℕ) : BorelSpace (Matrix (Fin r) (Fin r) ℂ) :=
  BlockBand.Critical.EntireLaw.matrix_borelSpace r

open scoped Matrix.Norms.L2Operator in
theorem continuous_sqrtProbeGram_aux (b E : ℝ) {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Continuous (fun K : Matrix ι ι ℂ => cfc Real.sqrt (probeGram b E K)) :=
  Continuous.cfc_of_mem_nhdsSet (s := Set.univ) Real.sqrt Filter.univ_mem
    (BlockBand.Critical.EntireLaw.continuous_probeGram b E)
    (fun K => (BlockBand.Critical.EntireLaw.probeGram_isHermitian b E K).isSelfAdjoint)
    Real.continuous_sqrt.continuousOn

/-- **(i) `K ↦ B^{1/2} = cfc √(probeGram K)` is continuous** (isometric Hermitian functional
calculus of Mathlib, `Continuous.cfc_of_mem_nhdsSet`; `B` is Hermitian for every `K`). -/
theorem continuous_sqrtProbeGram (b E : ℝ) {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Continuous (fun K : Matrix ι ι ℂ => cfc Real.sqrt (probeGram b E K)) :=
  continuous_sqrtProbeGram_aux b E

/-- `(K, M) ↦ exp{-iΣ_jσ_j𝒯_jj}`, `𝒯 = closedSourceMatrix b E K (Re M)`. -/
def closedPhase (b E : ℝ) (σ : Fin J → ℤˣ) (q : Matrix (Fin J) (Fin J) ℂ × Matrix (Fin J) (Fin J) ℂ) :
    ℂ :=
  closedSourcePhase σ (closedSourceMatrix b E q.1 (BlockBand.Critical.Collar.Kernel.rePart q.2))

theorem norm_closedPhase (b E : ℝ) (σ : Fin J → ℤˣ) (q) : ‖closedPhase (J := J) b E σ q‖ = 1 :=
  norm_closedSourcePhase_of_isHermitian σ
    (closedSourceMatrix_isHermitian b E q.1 (BlockBand.Critical.Collar.Kernel.rePart_isHermitian q.2))

/-- **(i) Joint continuity** of `(K, M) ↦ exp{-iΣσ_j𝒯_jj}(K, Re M)`. -/
theorem continuous_closedPhase (b E : ℝ) (σ : Fin J → ℤˣ) : Continuous (closedPhase (J := J) b E σ) := by
  have hRe : Continuous fun M : Matrix (Fin J) (Fin J) ℂ => BlockBand.Critical.Collar.Kernel.rePart M := by
    unfold BlockBand.Critical.Collar.Kernel.rePart
    exact (continuous_id.add (continuous_id (X := Matrix (Fin J) (Fin J) ℂ)).matrix_conjTranspose).const_smul ((2 : ℂ)⁻¹)
  have hS := (continuous_sqrtProbeGram (ι := Fin J) b E).comp
    (continuous_fst (X := Matrix (Fin J) (Fin J) ℂ) (Y := Matrix (Fin J) (Fin J) ℂ))
  have hT := (BlockBand.Critical.EntireLaw.continuous_closedSourceAlgebra (J := J) b E).comp
    (continuous_fst.prodMk ((hRe.comp continuous_snd).prodMk hS))
  exact (BlockBand.Critical.EntireLaw.continuous_closedSourcePhase σ).comp hT

/-- Real part of `closedPhase` as a bounded continuous joint test. -/
def closedPhaseRe (b E : ℝ) (σ : Fin J → ℤˣ) :
    (Matrix (Fin J) (Fin J) ℂ × Matrix (Fin J) (Fin J) ℂ) →ᵇ ℝ :=
  .mkOfBound ⟨fun q => (closedPhase b E σ q).re,
    Complex.continuous_re.comp (continuous_closedPhase b E σ)⟩ 2 fun q q' => by
    have h1 := Complex.abs_re_le_norm (closedPhase b E σ q)
    have h2 := Complex.abs_re_le_norm (closedPhase b E σ q')
    rw [norm_closedPhase] at h1 h2
    simp only [ContinuousMap.coe_mk, Real.dist_eq]
    linarith [abs_sub (closedPhase b E σ q).re (closedPhase b E σ q').re]

/-- Imaginary part of `closedPhase` as a bounded continuous joint test. -/
def closedPhaseIm (b E : ℝ) (σ : Fin J → ℤˣ) :
    (Matrix (Fin J) (Fin J) ℂ × Matrix (Fin J) (Fin J) ℂ) →ᵇ ℝ :=
  .mkOfBound ⟨fun q => (closedPhase b E σ q).im,
    Complex.continuous_im.comp (continuous_closedPhase b E σ)⟩ 2 fun q q' => by
    have h1 := Complex.abs_im_le_norm (closedPhase b E σ q)
    have h2 := Complex.abs_im_le_norm (closedPhase b E σ q')
    rw [norm_closedPhase] at h1 h2
    simp only [ContinuousMap.coe_mk, Real.dist_eq]
    linarith [abs_sub (closedPhase b E σ q).im (closedPhase b E σ q').im]

theorem integral_closedPhase_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (b E : ℝ) (σ : Fin J → ℤˣ)
    {q : Ω → Matrix (Fin J) (Fin J) ℂ × Matrix (Fin J) (Fin J) ℂ} (hq : AEMeasurable q μ) :
    ∫ ω, closedPhase b E σ (q ω) ∂μ =
      ((∫ ω, closedPhaseRe b E σ (q ω) ∂μ : ℝ) : ℂ) +
        ((∫ ω, closedPhaseIm b E σ (q ω) ∂μ : ℝ) : ℂ) * Complex.I := by
  have hint : Integrable (fun ω => closedPhase b E σ (q ω)) μ :=
    Integrable.of_bound ((continuous_closedPhase b E σ).measurable.comp_aemeasurable hq).aestronglyMeasurable
      1 (Filter.Eventually.of_forall fun ω => (norm_closedPhase b E σ (q ω)).le)
  have hre := integral_re hint
  have him := integral_im hint
  apply Complex.ext
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one, add_zero]
    exact hre.symm
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add]
    rw [add_zero]; exact him.symm

theorem closedPhase_of_isHermitian (b E : ℝ) (σ : Fin J → ℤˣ) (K : Matrix (Fin J) (Fin J) ℂ)
    {M : Matrix (Fin J) (Fin J) ℂ} (hM : M.IsHermitian) :
    closedPhase b E σ (K, M) = closedSourcePhase σ (closedSourceMatrix b E K M) := by
  unfold closedPhase
  congr 2
  unfold BlockBand.Critical.Collar.Kernel.rePart
  rw [hM.eq, ← two_smul ℂ M, smul_smul]
  norm_num

theorem measurable_closingMatrix_prod {W : ℕ} {Ω : Type*} [MeasurableSpace Ω] {r : ℕ} (b e : ℝ)
    {X : Ω → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    {F : Ω → Matrix (Fin 2 × Fin W) (Fin r) ℂ} (hX : Measurable X) (hF : Measurable F) :
    Measurable fun p : Ω × CollarSample W => closingMatrix b e 0 (X p.1) (F p.1) p.2 := by
  have h := (measurable_pi_apply (0 : Fin 1)).comp
    (measurable_shiftedClosing_prod (W := W) b e (fun _ : Fin 1 => (0 : ℝ)) hX hF)
  have heq : ((fun f : Fin 1 → Matrix (Fin r) (Fin r) ℂ => f 0) ∘ fun p : Ω × CollarSample W =>
      shiftedClosing b e (fun _ : Fin 1 => (0 : ℝ)) (X p.1) (F p.1) p.2) =
      fun p : Ω × CollarSample W => closingMatrix b e 0 (X p.1) (F p.1) p.2 := by
    funext p
    simp [shiftedClosing, microShift_zero]
  rwa [heq] at h

theorem measurableSet_isHermitian_of_measurable {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Fintype ι]
    {M : Ω → Matrix ι ι ℂ} (hM : Measurable M) : MeasurableSet {o | (M o).IsHermitian} := by
  have : {o | (M o).IsHermitian} = ⋂ i, ⋂ j, {o | star (M o j i) = M o i j} := by
    ext o
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Matrix.IsHermitian]
    constructor
    · intro h i j; exact congrFun (congrFun h i) j
    · intro h; ext i j; exact h i j
  rw [this]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
  have h1 : Measurable fun o => M o i j := (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hM)
  have h2 : Measurable fun o => star (M o j i) :=
    (continuous_star.measurable).comp ((measurable_pi_apply i).comp ((measurable_pi_apply j).comp hM))
  exact measurableSet_eq_fun h2 h1

/-- **The closed-source limit from old data** (the probabilistic content of the closed-source
limit step once the finite-width closed source matrix is written as
`𝒯_W = closedSourceMatrix(K_W, 𝒞_W)`).
Setting of `MatrixClosingStatement.stable_joint_atZero`: old data `(K_n, X_n, F_n)` on
`(Ωo n, μo n)`, independent of the collar (`μo n ⊗ collarLaw`), `X_n` Hermitian a.s.
(lossless), `F_n` orthonormal frames a.s., `d(X_n) → 0` in probability, and `K_n ⇒ κ` against
bounded continuous tests. Then `E exp{-iΣσ_j(𝒯_W)_jj} → ∫κ ∫P exp{-iΣσ_j𝒯(K, 𝖢_J(0))_jj}`, with
`𝒯_W = closedSourceMatrix b E K_n (closingMatrix b E 0 X_n F_n ω)`. Energy: any `-2 < E < 2`. -/
theorem tendsto_closedPhase_of_oldData (hMC : MatrixClosingStatement) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hE : -2 < E ∧ E < 2) (σ : Fin J → ℤˣ)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {Ξ : Ω' → VaguePointMeasure (ℝ × (Fin J → ℂ))} {C₀ : Ω' → Matrix (Fin J) (Fin J) ℂ}
    (hC₀ : IsCanonicalCauchyAtZero J P' Ξ C₀)
    {Ωo : ℕ → Type*} [∀ n, MeasurableSpace (Ωo n)] (μo : ∀ n, Measure (Ωo n))
    [∀ n, IsProbabilityMeasure (μo n)]
    (W : ℕ → ℕ) (hW : ∀ n, 0 < W n) (hWt : Tendsto W atTop atTop)
    (X : ∀ n, Ωo n → Matrix (Fin 2 × Fin (W n)) (Fin 2 × Fin (W n)) ℂ)
    (hXm : ∀ n, Measurable (X n)) (hXh : ∀ n, ∀ᵐ o ∂μo n, (X n o).IsHermitian)
    (F : ∀ n, Ωo n → Matrix (Fin 2 × Fin (W n)) (Fin J) ℂ) (hFm : ∀ n, Measurable (F n))
    (hFf : ∀ n, ∀ᵐ o ∂μo n, (F n o)ᴴ * F n o = 1)
    (hd : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n => μo n {o | δ < matchedDistance b E (X n o)}) atTop (𝓝 0))
    (K : ∀ n, Ωo n → Matrix (Fin J) (Fin J) ℂ) (hKm : ∀ n, Measurable (K n))
    (κ : Measure (Matrix (Fin J) (Fin J) ℂ)) [IsProbabilityMeasure κ]
    (hK : ∀ φ : Matrix (Fin J) (Fin J) ℂ →ᵇ ℝ,
      Tendsto (fun n => ∫ o, φ (K n o) ∂μo n) atTop (𝓝 (∫ k, φ k ∂κ))) :
    Tendsto (fun n => ∫ p, closedSourcePhase σ (closedSourceMatrix b E (K n p.1)
        (closingMatrix b E 0 (X n p.1) (F n p.1) p.2)) ∂(μo n).prod (collarLaw (W n) b)) atTop
      (𝓝 (∫ k, ∫ ω, closedSourcePhase σ (closedSourceMatrix b E k (C₀ ω)) ∂P' ∂κ)) := by
  have hP' := hC₀.decorated.prob
  set κ0 : ℝ := min (E + 2) (2 - E) with hκ0def
  have hκ0 : 0 < κ0 := lt_min (by linarith [hE.1]) (by linarith [hE.2])
  have he : E ∈ bulkInterval κ0 :=
    ⟨by linarith [min_le_left (E + 2) (2 - E)], by linarith [min_le_right (E + 2) (2 - E)]⟩
  have hre := hMC.stable_joint_atZero hb0 hb hκ0 hC₀ μo W hW hWt (fun _ => E) (fun _ => he) X hXm
    hXh F hFm hFf hd K hKm κ hK (closedPhaseRe b E σ)
  have him := hMC.stable_joint_atZero hb0 hb hκ0 hC₀ μo W hW hWt (fun _ => E) (fun _ => he) X hXm
    hXh F hFm hFf hd K hKm κ hK (closedPhaseIm b E σ)
  have hL : ∀ n, ∫ p, closedSourcePhase σ (closedSourceMatrix b E (K n p.1)
      (closingMatrix b E 0 (X n p.1) (F n p.1) p.2)) ∂(μo n).prod (collarLaw (W n) b) =
      ((∫ p, closedPhaseRe b E σ (K n p.1, closingMatrix b E 0 (X n p.1) (F n p.1) p.2)
          ∂(μo n).prod (collarLaw (W n) b) : ℝ) : ℂ) +
        ((∫ p, closedPhaseIm b E σ (K n p.1, closingMatrix b E 0 (X n p.1) (F n p.1) p.2)
          ∂(μo n).prod (collarLaw (W n) b) : ℝ) : ℂ) * Complex.I := by
    intro n
    have hCm := measurable_closingMatrix_prod (W := W n) b E (hXm n) (hFm n)
    have hae : ∀ᵐ p ∂(μo n).prod (collarLaw (W n) b),
        (closingMatrix b E 0 (X n p.1) (F n p.1) p.2).IsHermitian := by
      rw [Measure.ae_prod_iff_ae_ae (measurableSet_isHermitian_of_measurable hCm)]
      filter_upwards [hXh n] with o ho
      exact ae_closingMatrix_isHermitian hb hκ0 (hW n) he ho (F n o)
    rw [← integral_closedPhase_eq b E σ
      (q := fun p : Ωo n × CollarSample (W n) => (K n p.1, closingMatrix b E 0 (X n p.1) (F n p.1) p.2))
      (((hKm n).comp measurable_fst).prodMk hCm).aemeasurable]
    refine integral_congr_ae ?_
    filter_upwards [hae] with p hp
    exact (closedPhase_of_isHermitian b E σ _ hp).symm
  have hCm₀ := BlockBand.Critical.EntireLaw.measurable_matrix_of_isCanonicalCauchyAtZero hC₀
  have hR : ∫ k, ∫ ω, closedSourcePhase σ (closedSourceMatrix b E k (C₀ ω)) ∂P' ∂κ =
      ((∫ q, closedPhaseRe b E σ (q.1, C₀ q.2) ∂κ.prod P' : ℝ) : ℂ) +
        ((∫ q, closedPhaseIm b E σ (q.1, C₀ q.2) ∂κ.prod P' : ℝ) : ℂ) * Complex.I := by
    have hqm : Measurable fun q : Matrix (Fin J) (Fin J) ℂ × Ω' => (q.1, C₀ q.2) :=
      measurable_fst.prodMk (hCm₀.comp measurable_snd)
    rw [← integral_closedPhase_eq b E σ (μ := κ.prod P') hqm.aemeasurable]
    have hint : Integrable (fun q : Matrix (Fin J) (Fin J) ℂ × Ω' => closedPhase b E σ (q.1, C₀ q.2))
        (κ.prod P') :=
      Integrable.of_bound ((continuous_closedPhase b E σ).measurable.comp hqm).aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun q => (norm_closedPhase b E σ _).le)
    rw [integral_prod _ hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    refine integral_congr_ae ?_
    filter_upwards [BlockBand.Critical.MatrixClosing.ae_isHermitian_of_isCanonicalCauchyAtZero hC₀]
      with ω hω
    exact (closedPhase_of_isHermitian b E σ k hω).symm
  rw [hR]
  refine Tendsto.congr (fun n => (hL n).symm) ?_
  exact ((Complex.continuous_ofReal.tendsto _).comp hre).add
    (((Complex.continuous_ofReal.tendsto _).comp him).mul_const _)

/-- **`d(X_path) → 0` in probability for the old path**: the path clause of `MatchedTracesContract`
at `p = 2` and Chebyshev. Law: `pathLaw W r b`; `-2 < E < 2`, `0 < b < 1/2`, `W_n → ∞`, and lengths
with `1 ≤ r_n ≤ T W_n` eventually. -/
theorem tendsto_pathLaw_matchedDistance (hMT : MatchedTracesContract) {b E : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) (hE : -2 < E ∧ E < 2) {T : ℝ} (W r : ℕ → ℕ) (hWt : Tendsto W atTop atTop)
    (hr : ∀ᶠ n in atTop, 1 ≤ r n ∧ (r n : ℝ) ≤ T * W n) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n => pathLaw (W n) (r n) b
        {π | δ < matchedDistance b E (pathSchur E π)}) atTop (𝓝 0) := by
  set κ0 : ℝ := min (E + 2) (2 - E) with hκ0def
  have hκ0 : 0 < κ0 := lt_min (by linarith [hE.1]) (by linarith [hE.2])
  have he : E ∈ bulkInterval κ0 :=
    ⟨by linarith [min_le_left (E + 2) (2 - E)], by linarith [min_le_right (E + 2) (2 - E)]⟩
  obtain ⟨ε₀, C, hε₀, hP⟩ := hMT.path b hb0 hb κ0 T hκ0
  have hWr : Tendsto (fun n => (W n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hWt
  have hW2 : ∀ᶠ n in atTop, (2 : ℝ) ≤ ε₀ * W n ∧ 0 < W n := by
    have h1 := (hWr.const_mul_atTop hε₀).eventually_ge_atTop 2
    have h2 := hWt.eventually_ge_atTop 1
    filter_upwards [h1, h2] with n h1 h2
    exact ⟨h1, by omega⟩
  set a : ℝ≥0∞ := ENNReal.ofReal δ ^ ((ENNReal.ofReal 2).toReal)
  have ha0 : a ≠ 0 := by
    simp only [a]
    exact (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hδ) ENNReal.ofReal_ne_top).ne'
  have hatop : a ≠ ⊤ := by
    simp only [a]
    exact ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top
  have hbound : ∀ᶠ n in atTop, pathLaw (W n) (r n) b
      {π | δ < matchedDistance b E (pathSchur E π)} ≤
        a⁻¹ * ENNReal.ofReal (C * Real.sqrt 2 / W n) ^ ((ENNReal.ofReal 2).toReal) := by
    filter_upwards [hW2, hr] with n hn hrn
    have hL := hP (W n) hn.2 2 le_rfl hn.1 (r n) hrn.1 hrn.2 E he
    have hM := mul_meas_ge_le_pow_eLpNorm' (pathLaw (W n) (r n) b)
      (p := ENNReal.ofReal 2) (by simp) ENNReal.ofReal_ne_top
      (f := fun π : PathSample (W n) (r n) => matchedDistance b E (pathSchur E π))
      (ENNReal.ofReal δ)
    have hsub : {π : PathSample (W n) (r n) | δ < matchedDistance b E (pathSchur E π)} ⊆
        {π | ENNReal.ofReal δ ≤ ‖matchedDistance b E (pathSchur E π)‖ₑ} := by
      intro π hπ
      simp only [Set.mem_ofPred_eq] at hπ ⊢
      have h0 : 0 ≤ matchedDistance b E (pathSchur E π) := hδ.le.trans hπ.le
      rw [Real.enorm_of_nonneg h0]
      exact ENNReal.ofReal_le_ofReal hπ.le
    rw [← ENNReal.mul_le_iff_le_inv ha0 hatop]
    calc a * pathLaw (W n) (r n) b {π | δ < matchedDistance b E (pathSchur E π)}
        ≤ a * pathLaw (W n) (r n) b {π | ENNReal.ofReal δ ≤
            ‖matchedDistance b E (pathSchur E π)‖ₑ} := by gcongr
      _ ≤ eLpNorm (fun π : PathSample (W n) (r n) => matchedDistance b E (pathSchur E π))
            (ENNReal.ofReal 2) (pathLaw (W n) (r n) b) ^ ((ENNReal.ofReal 2).toReal) := hM
      _ ≤ _ := by gcongr; exact hL
  have hlim : Tendsto (fun n => a⁻¹ * ENNReal.ofReal (C * Real.sqrt 2 / W n) ^
      ((ENNReal.ofReal 2).toReal)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => C * Real.sqrt 2 / (W n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hWr
    have h2 := (ENNReal.tendsto_ofReal h1)
    rw [ENNReal.ofReal_zero] at h2
    have h3 := (ENNReal.continuous_rpow_const (y := (ENNReal.ofReal 2).toReal)).tendsto 0 |>.comp h2
    rw [ENNReal.zero_rpow_of_pos (by simp)] at h3
    have h4 := ENNReal.Tendsto.const_mul h3 (a := a⁻¹) (Or.inr (ENNReal.inv_ne_top.mpr ha0))
    rwa [mul_zero] at h4
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Filter.Eventually.of_forall fun n => zero_le) hbound

/-- **`d(X_path) → 0` for the physical ring**: the old path of the ring (the ring minus the collar
`{n-1, 0, 1}`, `ringPathSample`, with law `pathLaw W (n-3) b` by `map_ringPathSample`) has
`d(X_path) → 0` in probability under the physical law, along every critical sequence and every
choice of realizations (from `MatchedTracesContract`). -/
theorem tendsto_ringPath_matchedDistance (hMT : MatchedTracesContract) {b E : ℝ} (hb : 0 < b)
    (hb' : b < 1 / 2) (hE : -2 < E ∧ E < 2) {τ : ℝ} (s : BlockBand.CriticalSequence τ)
    (R : ∀ j, BlockBand.FiniteRealization (s.parameters b hb hb' j))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun j => ((R j).model.law : Measure (s.parameters b hb hb' j).SiteMatrix)
        {H | δ < matchedDistance b E (pathSchur E (ringPathSample (s.parameters b hb hb' j) H))})
      atTop (𝓝 0) := by
  have hS : ∀ (W r : ℕ), MeasurableSet {π : PathSample W r | δ < matchedDistance b E (pathSchur E π)} :=
    fun W r => measurableSet_lt measurable_const
      (measurable_matchedDistance_comp b E (BlockBand.Layers.measurable_pathSchur W r E))
  have heq : ∀ j, ((R j).model.law : Measure (s.parameters b hb hb' j).SiteMatrix)
      {H | δ < matchedDistance b E (pathSchur E (ringPathSample (s.parameters b hb hb' j) H))} =
      pathLaw (s.W j) (BlockBand.Critical.GlobalSource.probePathLength (s.n j)) b
        {π | δ < matchedDistance b E (pathSchur E π)} := by
    intro j
    have h := map_ringPathSample (R j).model
    have h2 := Measure.map_apply (μ := ((R j).model.law : Measure (s.parameters b hb hb' j).SiteMatrix))
      (measurable_ringPathSample (s.parameters b hb hb' j)) (hS _ _)
    rw [h] at h2
    exact h2.symm
  simp only [heq]
  refine tendsto_pathLaw_matchedDistance hMT hb hb' hE (T := τ + 1) s.W _ s.width_tendsto ?_ hδ
  have hr := (s.ratio_tendsto.eventually (gt_mem_nhds (show τ < τ + 1 by linarith)))
  filter_upwards [hr] with j hj
  have hW : (0 : ℝ) < s.W j := by exact_mod_cast s.W_pos j
  have hn := s.n_ge_four j
  refine ⟨by unfold BlockBand.Critical.GlobalSource.probePathLength; omega, ?_⟩
  rw [div_lt_iff₀ hW] at hj
  unfold BlockBand.Critical.GlobalSource.probePathLength
  have : ((s.n j - 3 : ℕ) : ℝ) ≤ s.n j := by exact_mod_cast Nat.sub_le _ _
  linarith

end BlockBand.Critical.EntireLaw
