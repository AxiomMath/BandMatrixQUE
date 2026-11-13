module

public import BlockBand.Critical.EntireLaw.ProbeScaling
public import BlockBand.Critical.EntireLaw.Tightness
public import BlockBand.Critical.EntireLaw.Determination
public import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# The entire law: tightness from the closing steps

`entireLaw_of_closing` derives `EntireLawContract` from `GlobalGaussianSourceStatement`,
`MatrixClosing.MatrixClosingStatement`, `CollarSourceRemoval` and `ClosedSourceLimitStep`.

Proof of one-probe tightness (`probeTightness_of_closing`, exactly the hypothesis `hX` of
`entireTightness_of_probeTightness`). Fix the profile `Q_a` and put
`X_W = Re(ζ^* R ζ)` (`ringProbeReal`; `= ζ^* R ζ` a.s.).
1. `mixedInverseMoment_probeCone`: at `y = |t| e_a` and `σ = probeSign t` (`-1` for `t ≥ 0`,
   `+1` for `t < 0`) the finite mixed moment is `E e^{itX_W}` (by the finite Gaussian moment
   identity and `ζ(|t|Q) = √|t| ζ(Q)`).
2. `tendsto_charFun_ringProbeReal`: `tendsto_finiteMoment_value` (`J = 1`) gives the
   limit `E exp{-iσ 𝒯^{(|t|Q)}_00}`; by `ProbeScaling` (`κ_{|t|Q} = (|t|•)_# κ_Q`,
   `𝒯(|t|K) = |t|𝒯(K)`, `𝒯_00` real a.s.) it equals `closedProbeCharFun t =
   E exp(i t 𝒯^{(Q)}_00)` (`closedSourceValue_probeCone`).
3. `continuous_closedProbeCharFun` (dominated convergence twice), Mathlib's
   `isTightMeasureSet_of_tendsto_charFun` (Lévy) and boundedness of compact sets.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.EntireLaw

open MeasureTheory Filter Topology Matrix Set Metric
open BlockBand.Critical.Entire
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.CriticalEntire
open BlockBand.Critical.GlobalSource
open scoped ENNReal

/-!
## 1. The limiting characteristic function `t ↦ E exp(i t 𝒯_00)`
-/

/-- `t ↦ ∫ exp(i t Re 𝒯(K, 𝖢_1(0))_00) dP dκ` (the characteristic function of the real a.s.
`𝒯_00`, `J = 1`). -/
def closedProbeCharFun (b E : ℝ) (κ : Measure (Matrix (Fin 1) (Fin 1) ℂ)) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (C : Ω → Matrix (Fin 1) (Fin 1) ℂ) (t : ℝ) : ℂ :=
  ∫ K, ∫ ω, Complex.exp (((t * (closedSourceMatrix b E K (C ω) 0 0).re : ℝ) : ℂ) * Complex.I)
    ∂P ∂κ

theorem measurable_closedProbeIntegrand (b E : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    {C : Ω → Matrix (Fin 1) (Fin 1) ℂ} (hC : Measurable C) (t : ℝ) :
    Measurable fun p : Matrix (Fin 1) (Fin 1) ℂ × Ω =>
      Complex.exp (((t * (closedSourceMatrix b E p.1 (C p.2) 0 0).re : ℝ) : ℂ) * Complex.I) := by
  have hT : Measurable fun p : Matrix (Fin 1) (Fin 1) ℂ × Ω => closedSourceMatrix b E p.1 (C p.2) :=
    (measurable_closedSourceMatrix b E).comp (measurable_fst.prodMk (hC.comp measurable_snd))
  have hT00 : Measurable fun p : Matrix (Fin 1) (Fin 1) ℂ × Ω =>
      closedSourceMatrix b E p.1 (C p.2) 0 0 :=
    (measurable_pi_apply 0).comp ((measurable_pi_apply 0).comp hT)
  exact Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
    (measurable_const.mul (Complex.measurable_re.comp hT00))).mul_const _)

/-- **Continuity of the limiting characteristic function** (dominated convergence, twice; the
integrand has modulus one). -/
theorem continuous_closedProbeCharFun (b E : ℝ) (κ : Measure (Matrix (Fin 1) (Fin 1) ℂ))
    [IsProbabilityMeasure κ] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Ξ : Ω → VaguePointMeasure (ℝ × (Fin 1 → ℂ))} {C : Ω → Matrix (Fin 1) (Fin 1) ℂ}
    (hC : IsCanonicalCauchyAtZero 1 P Ξ C) :
    Continuous (closedProbeCharFun b E κ P C) := by
  have hP : IsProbabilityMeasure P := hC.decorated.prob
  have hCm : Measurable C := measurable_matrix_of_isCanonicalCauchyAtZero hC
  have hnorm : ∀ x : ℝ, ‖Complex.exp ((x : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I
  have hinner : ∀ K : Matrix (Fin 1) (Fin 1) ℂ, Continuous fun t : ℝ =>
      ∫ ω, Complex.exp (((t * (closedSourceMatrix b E K (C ω) 0 0).re : ℝ) : ℂ) * Complex.I) ∂P := by
    intro K
    refine continuous_of_dominated (bound := fun _ => 1) (fun t => ?_)
      (fun t => Eventually.of_forall fun ω => (hnorm _).le) (integrable_const _)
      (Eventually.of_forall fun ω => ?_)
    · exact ((measurable_closedProbeIntegrand b E hCm t).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    · fun_prop
  refine continuous_of_dominated (bound := fun _ => 1) (fun t => ?_)
    (fun t => Eventually.of_forall fun K => ?_) (integrable_const _)
    (Eventually.of_forall hinner)
  · exact ((measurable_closedProbeIntegrand b E hCm t).stronglyMeasurable.integral_prod_right'
      (ν := P)).aestronglyMeasurable
  · refine (norm_integral_le_of_norm_le_const (Eventually.of_forall fun ω => (hnorm _).le)).trans ?_
    simp

/-!
## 2. The finite one-probe variable and its characteristic function
-/

section Finite

variable {p : Parameters}

/-- `ζ^* R ζ` scales linearly with the profiles: `ζ(tQ) = √t ζ(Q)`, `t ≥ 0`. -/
theorem ringSourceMatrix_smul (E : ℝ) {J : ℕ} (Q : Fin J → C(Torus, ℝ)) {t : ℝ} (ht : 0 ≤ t)
    (H : p.SiteMatrix) (g : Fin J → p.Site → ℂ) :
    ringSourceMatrix p E (fun a => t • Q a) H g = t • ringSourceMatrix p E Q H g := by
  have hv : ∀ (Q : C(Torus, ℝ)) (g : p.Site → ℂ),
      ringProbeVector p (t • Q) g = ((Real.sqrt t : ℝ) : ℂ) • ringProbeVector p Q g := by
    intro Q g
    funext x
    simp only [ringProbeVector, ContinuousMap.smul_apply, smul_eq_mul, Pi.smul_apply,
      Real.sqrt_mul ht]
    push_cast
    ring
  ext a c
  simp only [ringSourceMatrix, hv, Matrix.smul_apply]
  rw [Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul,
    Complex.star_def, Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul,
    Real.mul_self_sqrt ht, Complex.real_smul]

/-- The real one-probe variable `X = Re(ζ^* R ζ)` (`J = 1`, profile `Q`); `X = ζ^* R ζ` a.s. -/
def ringProbeReal (p : Parameters) (E : ℝ) (Q : C(Torus, ℝ))
    (x : p.SiteMatrix × (Fin 1 → p.Site → ℂ)) : ℝ :=
  (ringSourceMatrix p E (fun _ : Fin 1 => Q) x.1 x.2 0 0).re

theorem measurable_ringProbeReal (E : ℝ) (Q : C(Torus, ℝ)) :
    Measurable (ringProbeReal p E Q) :=
  Complex.measurable_re.comp ((measurable_pi_apply 0).comp ((measurable_pi_apply 0).comp
    (measurable_ringSourceMatrix (p := p) E fun _ : Fin 1 => Q)))

/-- The sign `σ = -1` for `t ≥ 0`, `σ = 1` for `t < 0` (so that `-σ|t| = t`). -/
def probeSign (t : ℝ) : Fin 1 → ℤˣ := fun _ => if 0 ≤ t then -1 else 1

/-- `exp{-iσ_t 𝒯_00} = exp(i t x)` when `𝒯_00 = |t| x`, `x` real. -/
theorem closedSourcePhase_probeSign (t x : ℝ) {M : Matrix (Fin 1) (Fin 1) ℂ}
    (hM : M 0 0 = ((|t| * x : ℝ) : ℂ)) :
    closedSourcePhase (probeSign t) M = Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) := by
  unfold closedSourcePhase probeSign
  rw [Fin.sum_univ_one, hM]
  congr 1
  split_ifs with ht
  · rw [abs_of_nonneg ht]; push_cast; ring
  · rw [abs_of_neg (not_le.mp ht)]; push_cast; ring

/-- The cone point of one probe `y = |t| e_a`. -/
def probeCone {k : ℕ} (a : Fin (k + 1)) (t : ℝ) : Fin 1 → Fin (k + 1) → ℝ :=
  fun _ => Pi.single a |t|

theorem probeCone_nonneg {k : ℕ} (a : Fin (k + 1)) (t : ℝ) : ∀ j b, 0 ≤ probeCone a t j b := by
  intro j b
  unfold probeCone
  by_cases h : b = a
  · subst h; simp
  · simp [h]

theorem probeProfile_probeCone {k : ℕ} (q : Fin k → C(Torus, ℝ)) (a : Fin (k + 1)) (t : ℝ) :
    probeProfile q (probeCone a t) = fun _ => |t| • fullProfile q a := by
  funext j
  unfold probeProfile probeCone
  rw [Finset.sum_eq_single a (fun b _ hb => by simp [hb]) (by simp)]
  simp

/-- **The finite mixed moment at `y = |t| e_a`, `σ = probeSign t` is the characteristic function
of the one-probe variable** (by `finiteGaussianMomentIdentity`; `H` Hermitian a.s.). -/
theorem mixedInverseMoment_probeCone (R : FiniteRealization p) (E : ℝ) {k : ℕ}
    {q : Fin k → C(Torus, ℝ)} (hq : IsProfileFamily q) (a : Fin (k + 1)) (t : ℝ) :
    mixedInverseMoment (finiteEntireLaw R E (fullProfile q)) (probeCone a t) (probeSign t) =
      charFun ((fullRingProbeLaw R.model 1).map (ringProbeReal p E (fullProfile q a))) t := by
  rw [finiteGaussianMomentIdentity p R E k q hq 1 _ _ (probeCone_nonneg a t),
    charFun_apply_real, integral_map (measurable_ringProbeReal E _).aemeasurable
      (by fun_prop), probeProfile_probeCone]
  have hherm : ∀ᵐ x ∂fullRingProbeLaw R.model 1, x.1.IsHermitian :=
    Measure.quasiMeasurePreserving_fst.ae R.model.isPhysical.1
  refine integral_congr_ae (hherm.mono fun x hx => ?_)
  refine (closedSourcePhase_probeSign t (ringProbeReal p E (fullProfile q a) x) ?_).trans ?_
  · rw [ringSourceMatrix_smul E _ (abs_nonneg t), Matrix.smul_apply, Complex.real_smul]
    have him := ringSourceMatrix_diag_im hx E (fun _ : Fin 1 => fullProfile q a) x.2 0
    conv_lhs => rw [← Complex.re_add_im (ringSourceMatrix p E _ x.1 x.2 0 0), him]
    simp [ringProbeReal]
  · simp only [ringProbeReal]
    push_cast
    ring_nf

end Finite

/-!
## 3. Convergence of the characteristic functions and one-probe tightness
-/

/-- **The limiting value at `y = |t| e_a`, `σ = probeSign t`, is `closedProbeCharFun`** of the
law `κ` of profile `Q_a` (using `κ_{|t|Q} = (|t|•)_# κ_Q`, `𝒯(|t|K) = |t|𝒯(K)`,
`𝒯_00` real a.s.). -/
theorem closedSourceValue_probeCone {b E τ : ℝ} (hτ : 0 ≤ τ) {Q : C(Torus, ℝ)}
    {κ κt : Measure (Matrix (Fin 1) (Fin 1) ℂ)} [IsProbabilityMeasure κ]
    [IsProbabilityMeasure κt] (hκ : IsGlobalProbeCriticalLimit b E τ (fun _ : Fin 1 => Q) κ)
    (t : ℝ) (hκt : IsGlobalProbeCriticalLimit b E τ (fun _ : Fin 1 => |t| • Q) κt)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Ξ : Ω → VaguePointMeasure (ℝ × (Fin 1 → ℂ))} {C : Ω → Matrix (Fin 1) (Fin 1) ℂ}
    (hC : IsCanonicalCauchyAtZero 1 P Ξ C) :
    ∫ K, ∫ ω, closedSourcePhase (probeSign t) (closedSourceMatrix b E K (C ω)) ∂P ∂κt =
      closedProbeCharFun b E κ P C t := by
  have hP : IsProbabilityMeasure P := hC.decorated.prob
  rw [globalProbeLaw_smul_eq_map hτ hκ (abs_nonneg t) hκt,
    integral_map (measurable_const_smul |t|).aemeasurable
      (stronglyMeasurable_closedSourceInner b E (probeSign t) hC).aestronglyMeasurable]
  refine integral_congr_ae (Eventually.of_forall fun K => ?_)
  refine integral_congr_ae ((ae_closedSourceMatrix_diag_im b E hC).mono fun ω hω => ?_)
  refine closedSourcePhase_probeSign t _ ?_
  rw [closedSourceMatrix_smul b E (abs_nonneg t), Matrix.smul_apply, Complex.real_smul]
  conv_lhs => rw [← Complex.re_add_im (closedSourceMatrix b E K (C ω) 0 0), hω K 0]
  simp

/-- **Pointwise convergence of the one-probe characteristic functions** along a critical
sequence (`tendsto_finiteMoment_value` with `J = 1`, `y = |t| e_a`, `σ = ∓1`; uses
`hGS`, `hMC`, `CollarSourceRemoval` and `ClosedSourceLimitStep`). -/
theorem tendsto_charFun_ringProbeReal (hGS : GlobalGaussianSourceStatement)
    (hMC : BlockBand.Critical.MatrixClosing.MatrixClosingStatement) (hO2 : CollarSourceRemoval)
    (hO4 : ClosedSourceLimitStep) {b E : ℝ} (hb : 0 < b) (hb' : b < 1 / 2)
    (hE : -2 < E ∧ E < 2) (τ : PositiveRatio) {k : ℕ} {q : Fin k → C(Torus, ℝ)}
    (hq : IsProfileFamily q) (a : Fin (k + 1)) (s : CriticalSequence τ.1)
    (R : ∀ j, FiniteRealization (s.parameters b hb hb' j))
    {κ : Measure (Matrix (Fin 1) (Fin 1) ℂ)} [IsProbabilityMeasure κ]
    (hκ : IsGlobalProbeCriticalLimit b E τ.1 (fun _ : Fin 1 => fullProfile q a) κ)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (Ξ : Ω → VaguePointMeasure (ℝ × (Fin 1 → ℂ)))
    (C : Ω → Matrix (Fin 1) (Fin 1) ℂ) (hC : IsCanonicalCauchyAtZero 1 P Ξ C) (t : ℝ) :
    Tendsto (fun j => charFun ((fullRingProbeLaw (R j).model 1).map
        (ringProbeReal (s.parameters b hb hb' j) E (fullProfile q a))) t) atTop
      (𝓝 (closedProbeCharFun b E κ P C t)) := by
  have hy := probeCone_nonneg a t
  obtain ⟨κt, hκt, -⟩ := hGS b E hb hb' hE τ 1 (probeProfile q (probeCone a t))
    (probeProfile_nonneg hq hy)
  have hκtP : IsProbabilityMeasure κt := hκt.1.1
  have h := tendsto_finiteMoment_value hMC finiteGaussianMomentIdentity hO2 hO4 hb hb' hE τ hq
    (probeCone a t) (probeSign t) hy s R hκt Ω P Ξ C hC
  have hκt' := hκt.2
  rw [probeProfile_probeCone] at hκt'
  rw [closedSourceValue_probeCone τ.2.le hκ t hκt' hC] at h
  exact h.congr fun j => mixedInverseMoment_probeCone (R j) E hq a t

/-- **One-probe tightness** (the hypothesis `hX` of `entireTightness_of_probeTightness`), from
`GlobalGaussianSourceStatement` (`hGS`), `MatrixClosingStatement` (`hMC`),
`CollarSourceRemoval` and `ClosedSourceLimitStep`: the
characteristic functions of the one-probe variables converge pointwise to the continuous
`closedProbeCharFun` (Lévy, `isTightMeasureSet_of_tendsto_charFun`). -/
theorem probeTightness_of_closing (hGS : GlobalGaussianSourceStatement)
    (hMC : BlockBand.Critical.MatrixClosing.MatrixClosingStatement) (hO2 : CollarSourceRemoval)
    (hO4 : ClosedSourceLimitStep) :
    ∀ (b E : ℝ) (hb : 0 < b) (hb' : b < 1 / 2), -2 < E ∧ E < 2 →
      ∀ (τ : PositiveRatio) (k : ℕ) (q : Fin k → C(Torus, ℝ)), IsProfileFamily q →
      ∀ (s : CriticalSequence τ.1) (R : ∀ j, FiniteRealization (s.parameters b hb hb' j)),
      ∀ a : Fin (k + 1), ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ j,
        (fullRingProbeLaw (R j).model 1).real
          {x | M < ‖ringSourceMatrix (s.parameters b hb hb' j) E
            (fun _ : Fin 1 => fullProfile q a) x.1 x.2 0 0‖} ≤ ε := by
  intro b E hb hb' hE τ k q hq s R a ε hε
  obtain ⟨κ, hκ, -⟩ := hGS b E hb hb' hE τ 1 (fun _ : Fin 1 => fullProfile q a)
    (fun _ => fullProfile_nonneg hq a)
  have hκP : IsProbabilityMeasure κ := hκ.1.1
  obtain ⟨Ω, mΩ, P, Ξ, C, hC⟩ := BlockBand.Critical.DecoratedSine.exists_isCanonicalCauchyAtZero 1
  set μ : ℕ → Measure ℝ := fun j => (fullRingProbeLaw (R j).model 1).map
    (ringProbeReal (s.parameters b hb hb' j) E (fullProfile q a)) with hμ
  have hμP : ∀ j, IsProbabilityMeasure (μ j) := fun j => by
    have : IsProbabilityMeasure (fullRingProbeLaw (R j).model 1) := by
      unfold fullRingProbeLaw; infer_instance
    simp only [hμ]
    infer_instance
  have ht : IsTightMeasureSet (Set.range μ) :=
    isTightMeasureSet_of_tendsto_charFun
      (continuous_closedProbeCharFun b E κ hC).continuousAt
      (tendsto_charFun_ringProbeReal hGS hMC hO2 hO4 hb hb' hE τ hq a s R hκ.2 Ω P Ξ C hC)
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at ht
  obtain ⟨K, hK, hKμ⟩ := ht (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
  obtain ⟨M, hM⟩ := (isBounded_iff_subset_closedBall (0 : ℝ)).mp hK.isBounded
  refine ⟨M, fun j => ?_⟩
  set p := s.parameters b hb hb' j
  have hherm : ∀ᵐ x ∂fullRingProbeLaw (R j).model 1, x.1.IsHermitian :=
    Measure.quasiMeasurePreserving_fst.ae (R j).model.isPhysical.1
  have hsub : {x : p.SiteMatrix × (Fin 1 → p.Site → ℂ) |
      M < ‖ringSourceMatrix p E (fun _ : Fin 1 => fullProfile q a) x.1 x.2 0 0‖} ≤ᵐ[
      fullRingProbeLaw (R j).model 1] ringProbeReal p E (fullProfile q a) ⁻¹' Kᶜ := by
    filter_upwards [hherm] with x hx hxM
    simp only [mem_preimage, mem_compl_iff]
    intro hxK
    have hb := mem_closedBall_zero_iff.mp (hM hxK)
    have him := ringSourceMatrix_diag_im hx E (fun _ : Fin 1 => fullProfile q a) x.2 0
    have hn : ‖ringSourceMatrix p E (fun _ : Fin 1 => fullProfile q a) x.1 x.2 0 0‖ =
        ‖ringProbeReal p E (fullProfile q a) x‖ := by
      conv_lhs => rw [← Complex.re_add_im (ringSourceMatrix p E _ x.1 x.2 0 0), him]
      simp [ringProbeReal]
    change M < ‖ringSourceMatrix p E (fun _ : Fin 1 => fullProfile q a) x.1 x.2 0 0‖ at hxM
    linarith
  have hle : fullRingProbeLaw (R j).model 1 {x : p.SiteMatrix × (Fin 1 → p.Site → ℂ) |
      M < ‖ringSourceMatrix p E (fun _ : Fin 1 => fullProfile q a) x.1 x.2 0 0‖} ≤
      ENNReal.ofReal ε := by
    refine (measure_mono_ae hsub).trans ?_
    rw [← Measure.map_apply (measurable_ringProbeReal E _) hK.isClosed.measurableSet.compl]
    exact hKμ _ ⟨j, rfl⟩
  exact ENNReal.toReal_le_of_le_ofReal hε.le hle

/-- **`EntireTightness` from `hGS`, `hMC`, `CollarSourceRemoval` and `ClosedSourceLimitStep`** (`entireTightness_of_probeTightness` with
`probeTightness_of_closing`). -/
theorem entireTightness_of_closing (hGS : GlobalGaussianSourceStatement)
    (hMC : BlockBand.Critical.MatrixClosing.MatrixClosingStatement) (hO2 : CollarSourceRemoval)
    (hO4 : ClosedSourceLimitStep) : EntireTightness :=
  entireTightness_of_probeTightness (probeTightness_of_closing hGS hMC hO2 hO4)

/-- **The entire law from `GlobalGaussianSourceStatement`, `MatrixClosingStatement`,
`CollarSourceRemoval` and `ClosedSourceLimitStep`** (`entireLaw_of_remaining` with the
tightness hypothesis discharged by `entireTightness_of_closing`). -/
theorem entireLaw_of_closing (hGS : GlobalGaussianSourceStatement)
    (hMC : BlockBand.Critical.MatrixClosing.MatrixClosingStatement) (hO2 : CollarSourceRemoval)
    (hO4 : ClosedSourceLimitStep) : EntireLawContract :=
  entireLaw_of_remaining hGS hMC hO2 hO4 (entireTightness_of_closing hGS hMC hO2 hO4)

end BlockBand.Critical.EntireLaw
