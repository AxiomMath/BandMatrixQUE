module

public import BlockBand.Endpoints.Clock.OpenClockLaw
public import BlockBand.Endpoints.Clock.OpenClockWeak

/-!
# The open-clock law theorem: convergence in law of the open-source Brownian profile `Σ_W`

We prove convergence in law of the finite-dimensional test vectors of the clock profile to those of
the Brownian profile `Σ_τ`.

## Objects

* Finite width: for a test `φ` the profile integral `Σ_W(φ) = W⁻² Σ_k φ(k/W) g* Y_{n;k} g`
  equals `g* Q_n^φ g` (the clock with weight `φ` is linear in the weight,
  `oneEndedQ_sum_smul`), realised on (first `n` one-ended layers) ⊗ `g ~ CN(0, I_W)`;
  `profileVector` collects `Σ_W(φ_i)`, `i < m`.
* Limit: `Σ_τ(φ) = d ∫₀^τ φ(x) e^{√D₀ B_{τ-x} - D₀(τ-x)/2} dx = d ∫₀^τ φ(τ-s) e^{√D₀ B_s - D₀ s/2} ds`
  (the open Brownian measure), i.e. `dStar b * openClockIntegral D₀ φ τ` on the
  constructed Wiener space; `limitProfileVector` collects `Σ_τ(φ_i)`.

## Results (fixed energy; conditional on `DetClockEvolution` and `OpenInputsMoments`)

* `tendsto_profile_fdd`: for every finite family of admissible (continuous, bounded,
  nonnegative) tests `φ_1, …, φ_m` and every bounded continuous `ψ : ℝ^m → ℝ`,
  `E ψ(Σ_W(φ_1), …, Σ_W(φ_m)) → E ψ(Σ_τ(φ_1), …, Σ_τ(φ_m))` — convergence in law of all
  finite-dimensional test vectors of `Σ_W` to those of `Σ_τ`. (Weak convergence as a random finite
  measure on `[0,T]` is related to this formulation by the Kallenberg criterion for nonnegative
  tests; that step is not part of this library.)
* `tendsto_totalMass_law`: the total mass `Σ_W([0,T]) = g* Q_n^1 g` converges in law to
  `openClockLaw b E τ`: `∫ f d(openProbeLaw W b E 1 n_W) → ∫ f d(openClockLaw b E τ)`
  for every bounded continuous `f`.
* `integral_openClockIntegral_le`: first moments of the limit, `E Σ_τ(φ) ≤ d τ sup φ`
  (`E e^{√D B_s - Ds/2} = 1`, Tonelli).
* `limitDensity_pos`, `continuous_limitDensity`: the density of `Σ_τ` is strictly positive and
  continuous for every path.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open MeasureTheory ProbabilityTheory Real Set Filter Topology Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
  BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.SourceProcess OpenClock
open scoped NNReal ENNReal ComplexOrder Matrix BoundedContinuousFunction

namespace OpenClockProfile

variable {W : ℕ}

/-- The clock is linear in its weight: `Y^{Σ lᵢ φᵢ} = Σ lᵢ Y^{φᵢ}`. -/
theorem oneEndedY_sum_smul (b E : ℝ) {m : ℕ} (φ : Fin m → ℝ → ℝ) (l : Fin m → ℝ)
    (D : Matrix (Fin W) (Fin W) ℂ) (j : ℕ) (ω : Fin j → OneEndedLayer W) :
    oneEndedY b E (fun x => ∑ i, l i * φ i x) D j ω =
      ∑ i, ((l i : ℝ) : ℂ) • oneEndedY b E (φ i) D j ω := by
  induction j with
  | zero => simp [oneEndedY]
  | succ j ih =>
    simp only [oneEndedY]
    rw [ih (Fin.init ω)]
    set C := freshC b E (oneEndedX E D j (Fin.init ω)) (ω (Fin.last j))
    set L := freshL b E (oneEndedX E D j (Fin.init ω)) (ω (Fin.last j))
    have h1 : (((∑ i, l i * φ i (((j + 1 : ℕ) : ℝ) / W) : ℝ)) : ℂ) • C =
        ∑ i, ((l i : ℝ) : ℂ) • (((φ i (((j + 1 : ℕ) : ℝ) / W) : ℝ) : ℂ) • C) := by
      push_cast
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul]
    have h2 : Lᴴ * (∑ i, ((l i : ℝ) : ℂ) • oneEndedY b E (φ i) D j (Fin.init ω)) * L =
        ∑ i, ((l i : ℝ) : ℂ) • (Lᴴ * oneEndedY b E (φ i) D j (Fin.init ω) * L) := by
      rw [Matrix.mul_sum, Matrix.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [h1, h2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_add]

theorem oneEndedQ_sum_smul (b E : ℝ) {m : ℕ} (φ : Fin m → ℝ → ℝ) (l : Fin m → ℝ)
    (D : Matrix (Fin W) (Fin W) ℂ) (j : ℕ) (ω : Fin j → OneEndedLayer W) :
    oneEndedQ b E (fun x => ∑ i, l i * φ i x) D j ω =
      ∑ i, ((l i : ℝ) : ℂ) • oneEndedQ b E (φ i) D j ω := by
  unfold oneEndedQ
  rw [oneEndedY_sum_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_comm]

/-- Nonnegative combinations of admissible weights are admissible. -/
theorem isClockWeight_sum {m : ℕ} {φ : Fin m → ℝ → ℝ} (hφ : ∀ i, IsClockWeight (φ i))
    {l : Fin m → ℝ} (hl : ∀ i, 0 ≤ l i) : IsClockWeight (fun x => ∑ i, l i * φ i x) := by
  choose hc h0 K hK using hφ
  refine ⟨continuous_finsetSum _ fun i _ => continuous_const.mul (hc i),
    fun x => Finset.sum_nonneg fun i _ => mul_nonneg (hl i) (h0 i x),
    ∑ i, l i * K i, fun x => Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hK i x) (hl i)⟩

/-- `Σ_W(φ_i) = g* Q_n^{φ_i} g`, `i < m`, on (layers) ⊗ (Gaussian probe). -/
def profileVector (b E : ℝ) {m : ℕ} (φ : Fin m → ℝ → ℝ) (n : ℕ)
    (p : (Fin n → OneEndedLayer W) × (Fin W → ℂ)) : Fin m → ℝ :=
  fun i => quadForm (oneEndedQ b E (φ i) 0 n p.1) p.2

/-- `Σ_τ(φ_i) = d ∫₀^τ φ_i(τ-s) e^{√D₀ B_s - D₀ s/2} ds`, `i < m`. -/
def limitProfileVector (b E : ℝ) {m : ℕ} (φ : Fin m → ℝ → ℝ) (τ : ℝ) (ω : CanonicalWienerPath) :
    Fin m → ℝ :=
  fun i => dStar b * openClockIntegral (transportD0 b E) (φ i) τ ω

theorem measurable_profileVector (b E : ℝ) {m : ℕ} (φ : Fin m → ℝ → ℝ) (n : ℕ) :
    Measurable (profileVector (W := W) b E φ n) :=
  Measurable.of_eval fun i => measurable_probe (W := W) b E (φ i) n

/-- `E Σ_τ(φ) ≤ τ sup φ` before the factor `d`, with integrability. -/
theorem integral_openClockIntegral_le {D : ℝ} (hD : 0 ≤ D) {φ : ℝ → ℝ} (hφc : Continuous φ)
    (hφ0 : ∀ x, 0 ≤ φ x) {K : ℝ} (hK : ∀ x, φ x ≤ K) {τ : ℝ} (hτ : 0 ≤ τ) :
    Integrable (openClockIntegral D φ τ) canonicalWienerLaw ∧
      ∫ ω, openClockIntegral D φ τ ω ∂canonicalWienerLaw ≤ K * τ := by
  set P := canonicalWienerLaw
  have hK0 : 0 ≤ K := (hφ0 0).trans (hK 0)
  set F : CanonicalWienerPath → ℝ → ℝ := fun ω s =>
    φ (τ - s) * exp (Real.sqrt D * ω s.toNNReal - D * s / 2) with hF
  have hFc : Continuous (fun p : CanonicalWienerPath × ℝ => F p.1 p.2) := by
    have hev : Continuous (fun p : CanonicalWienerPath × ℝ => p.1 p.2.toNNReal) :=
      continuous_eval.comp (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))
    exact (hφc.comp (continuous_const.sub continuous_snd)).mul (continuous_exp.comp
      ((continuous_const.mul hev).sub ((continuous_const.mul continuous_snd).div_const _)))
  have hF0 : ∀ ω s, 0 ≤ F ω s := fun ω s => mul_nonneg (hφ0 _) (exp_pos _).le
  -- `E e^{√D B_s - Ds/2} = 1`
  have h0 : ∀ᵐ ω ∂P, ω 0 = 0 := canonicalWiener_isBrownian.toIsPreBrownianReal.eval_zero_ae_eq_zero
  have hmean : ∀ s : ℝ, 0 ≤ s →
      ∫⁻ ω, ENNReal.ofReal (exp (Real.sqrt D * ω s.toNNReal - D * s / 2)) ∂P = 1 := by
    intro s hs
    have hI := integrable_exp_mul_logZ D 0 s.toNNReal 1
    have hE := integral_exp_mul_logZ hD 0 s.toNNReal 1
    have hae : (fun ω => exp (1 * logZ D 0 s.toNNReal ω)) =ᵐ[P]
        fun ω => exp (Real.sqrt D * ω s.toNNReal - D * s / 2) := by
      filter_upwards [h0] with ω hω
      simp [logZ, incr, hω, Real.coe_toNNReal _ hs]
    have hae' : (fun ω => ENNReal.ofReal (exp (1 * logZ D 0 s.toNNReal ω))) =ᵐ[P]
        fun ω => ENNReal.ofReal (exp (Real.sqrt D * ω s.toNNReal - D * s / 2)) :=
      hae.mono fun ω h => by simp only at h ⊢; rw [h]
    rw [← lintegral_congr_ae hae', ← ofReal_integral_eq_lintegral_ofReal hI
        (Filter.Eventually.of_forall fun _ => (exp_pos _).le), hE]
    simp
  have hpt : ∀ ω, ENNReal.ofReal (openClockIntegral D φ τ ω) =
      ∫⁻ s in Ioc 0 τ, ENNReal.ofReal (F ω s) := by
    intro ω
    have hFi : IntegrableOn (fun s => F ω s) (Ioc 0 τ) volume :=
      (hFc.comp (continuous_const.prodMk continuous_id)).integrableOn_Ioc
    show ENNReal.ofReal (∫ s in (0 : ℝ)..τ, F ω s) = _
    rw [intervalIntegral.integral_of_le hτ, ofReal_integral_eq_lintegral_ofReal hFi
      (Filter.Eventually.of_forall fun s => hF0 ω s)]
  have hmeas : Measurable (Function.uncurry fun ω s => ENNReal.ofReal (F ω s)) :=
    ENNReal.measurable_ofReal.comp hFc.measurable
  have hlint : ∫⁻ ω, ENNReal.ofReal (openClockIntegral D φ τ ω) ∂P ≤ ENNReal.ofReal (K * τ) := by
    simp_rw [hpt]
    rw [lintegral_lintegral_swap hmeas.aemeasurable]
    calc ∫⁻ s in Ioc 0 τ, ∫⁻ ω, ENNReal.ofReal (F ω s) ∂P ≤ ∫⁻ _s in Ioc 0 τ, ENNReal.ofReal K := by
          refine setLIntegral_mono measurable_const fun s hs => ?_
          calc ∫⁻ ω, ENNReal.ofReal (F ω s) ∂P
              ≤ ∫⁻ ω, ENNReal.ofReal K * ENNReal.ofReal
                  (exp (Real.sqrt D * ω s.toNNReal - D * s / 2)) ∂P := by
                refine lintegral_mono fun ω => ?_
                rw [← ENNReal.ofReal_mul hK0]
                exact ENNReal.ofReal_le_ofReal
                  (mul_le_mul_of_nonneg_right (hK _) (exp_pos _).le)
            _ = ENNReal.ofReal K := by
                rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hmean s hs.1.le, mul_one]
      _ = ENNReal.ofReal (K * τ) := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_mul hK0]
  have hcont := continuous_openClockIntegral D hφc τ
  have hnn : ∀ ω, 0 ≤ openClockIntegral D φ τ ω := openClockIntegral_nonneg D hφ0 hτ
  have hI : Integrable (openClockIntegral D φ τ) P := by
    refine ⟨hcont.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnn)]
    exact lt_of_le_of_lt hlint ENNReal.ofReal_lt_top
  refine ⟨hI, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnn)
    hcont.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hK0 hτ) hlint

/-- `∫₀^τ (Σ lᵢ φᵢ)(τ-s) M_s ds = Σ lᵢ ∫₀^τ φᵢ(τ-s) M_s ds`. -/
theorem openClockIntegral_sum (D : ℝ) {m : ℕ} {φ : Fin m → ℝ → ℝ} (hφc : ∀ i, Continuous (φ i))
    (l : Fin m → ℝ) (τ : ℝ) (ω : CanonicalWienerPath) :
    openClockIntegral D (fun x => ∑ i, l i * φ i x) τ ω =
      ∑ i, l i * openClockIntegral D (φ i) τ ω := by
  unfold openClockIntegral
  have hev : Continuous (fun s : ℝ => ω s.toNNReal) := ω.continuous.comp continuous_real_toNNReal
  have hint : ∀ i, IntervalIntegrable (fun s => l i * (φ i (τ - s) *
      exp (Real.sqrt D * ω s.toNNReal - D * s / 2))) volume 0 τ := fun i =>
    (continuous_const.mul (((hφc i).comp (continuous_const.sub continuous_id)).mul
      (continuous_exp.comp ((continuous_const.mul hev).sub
        ((continuous_const.mul continuous_id).div_const _))))).intervalIntegrable _ _
  have e : ∑ i, l i * ∫ s in (0 : ℝ)..τ, φ i (τ - s) *
      exp (Real.sqrt D * ω s.toNNReal - D * s / 2) =
      ∑ i, ∫ s in (0 : ℝ)..τ, l i * (φ i (τ - s) * exp (Real.sqrt D * ω s.toNNReal - D * s / 2)) :=
    Finset.sum_congr rfl fun i _ => (intervalIntegral.integral_const_mul _ _).symm
  rw [e, ← intervalIntegral.integral_finsetSum fun i _ => hint i]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [Finset.sum_mul, mul_assoc]

end OpenClockProfile

open OpenClockProfile OpenClockLawProof

/-- **The open-clock law theorem, convergence in law of `Σ_W` (finite-dimensional form, fixed
energy).** Under `DetClockEvolution` and `OpenInputsMoments`: for `0 < b < 1/2`, `-2 < E < 2`,
`T > 0`, `n_W/W → τ > 0` with `n_W ≤ TW`, every finite family of admissible tests `φ_i` and
every bounded continuous `ψ : ℝ^m → ℝ`,
`E ψ(Σ_W(φ_1), …, Σ_W(φ_m)) → E ψ(Σ_τ(φ_1), …, Σ_τ(φ_m))`. -/
theorem tendsto_profile_fdd (hDet : DetClockEvolution) (hOI : OpenInputsMoments) {b : ℝ}
    (hb0 : 0 < b) (hb1 : b < 1 / 2) {E : ℝ} (hE0 : -2 < E) (hE1 : E < 2) {T : ℝ} (hT : 0 < T)
    {n : ℕ → ℕ} {τ : ℝ} (hτ : 0 < τ) (hn : Tendsto (fun W => (n W : ℝ) / W) atTop (𝓝 τ))
    (hnT : ∀ W, (n W : ℝ) ≤ T * W) {m : ℕ} (φ : Fin m → ℝ → ℝ) (hφ : ∀ i, IsClockWeight (φ i))
    (ψ : (Fin m → ℝ) → ℝ) (hψ : Continuous ψ) {M : ℝ} (hM : ∀ x, |ψ x| ≤ M) :
    Tendsto (fun W => ∫ p, ψ (profileVector (W := W) b E φ (n W) p)
        ∂(oneEndedLaw W b (n W)).prod (circularVectorLaw (Fin W))) atTop
      (𝓝 (∫ ω, ψ (limitProfileVector b E φ τ ω) ∂canonicalWienerLaw)) := by
  set D := transportD0 b E
  have hD : 0 ≤ D := (transportD0_pos hb0 hE0 hE1).le
  have hd : 0 ≤ dStar b := dStar_nonneg (by linarith)
  choose hφc hφ0 Kφ hKφ using hφ
  have hKφ0 : ∀ i, 0 ≤ Kφ i := fun i => (hφ0 i 0).trans (hKφ i 0)
  have hmom := fun i => integral_openClockIntegral_le hD (hφc i) (hφ0 i) (hKφ i) hτ.le
  refine tendsto_integral_of_tendsto_laplace (fun W => (Fin (n W) → OneEndedLayer W) × (Fin W → ℂ))
    (fun W => (oneEndedLaw W b (n W)).prod (circularVectorLaw (Fin W)))
    (fun W => profileVector (W := W) b E φ (n W)) (fun W => measurable_profileVector b E φ (n W))
    (fun W p i => CommonPortRatios.quadForm_nonneg_of_posSemidef
      (oneEndedQ_posSemidef b E (hφ0 i) 0 (n W) p.1) p.2)
    canonicalWienerLaw (limitProfileVector b E φ τ)
    (Measurable.of_eval fun i => (continuous_const.mul
      (continuous_openClockIntegral D (hφc i) τ)).measurable)
    (fun ω i => mul_nonneg hd (openClockIntegral_nonneg D (hφ0 i) hτ.le ω))
    (fun i => (hmom i).1.const_mul _) (K := ∑ i, dStar b * (Kφ i * τ)) (fun i => ?_) (fun l hl => ?_)
    ψ hψ hM
  · -- first moments of the limit
    calc ∫ ω, limitProfileVector b E φ τ ω i ∂canonicalWienerLaw
        = dStar b * ∫ ω, openClockIntegral D (φ i) τ ω ∂canonicalWienerLaw := integral_const_mul _ _
      _ ≤ dStar b * (Kφ i * τ) := mul_le_mul_of_nonneg_left (hmom i).2 hd
      _ ≤ ∑ i, dStar b * (Kφ i * τ) :=
          Finset.single_le_sum (f := fun i => dStar b * (Kφ i * τ))
            (fun i _ => mul_nonneg hd (mul_nonneg (hKφ0 i) hτ.le)) (Finset.mem_univ i)
  · -- Laplace transforms
    set ql : ℝ → ℝ := fun x => ∑ i, l i * φ i x with hql
    have hqw : IsClockWeight ql := isClockWeight_sum (fun i => ⟨hφc i, hφ0 i, Kφ i, hKφ i⟩) hl
    have hmain := tendsto_openClockLaplaceW hDet hOI hb0 hb1 hE0 hE1 hT hqw hτ hn hnT one_pos
    have hlhs : ∀ W, ∫ p, exp (-∑ i, l i * profileVector (W := W) b E φ (n W) p i)
        ∂(oneEndedLaw W b (n W)).prod (circularVectorLaw (Fin W)) =
        openClockLaplaceW W b E ql (n W) 1 := by
      intro W
      rw [openClockLaplaceW_eq_lap W b E hqw.2.1 (n W) zero_le_one]
      unfold lap openProbeLaw
      rw [integral_map (measurable_probe (W := W) b E ql (n W)).aemeasurable
        (show Continuous (fun x : ℝ => exp (-(1 * x))) by fun_prop).aestronglyMeasurable]
      refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      simp only [profileVector, one_mul]
      rw [oneEndedQ_sum_smul, CommonPortRatios.quadForm_sum_smul]
    have hrhs : ∫ ω, exp (-∑ i, l i * limitProfileVector b E φ τ ω i) ∂canonicalWienerLaw =
        openClockLaplace D (dStar b) ql τ 1 := by
      rw [openClockLaplace_eq]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      simp only [limitProfileVector, one_mul, hql]
      rw [openClockIntegral_sum D hφc l τ ω, Finset.mul_sum]
      congr 2
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    simp_rw [hlhs, hrhs]
    exact hmain

/-- **Total mass** (the open-clock law theorem with the test `1`, fixed energy): the law of
`Σ_W([0,T]) = g* Q^1_{n_W} g` converges weakly to `openClockLaw b E τ`, the law of
`X_τ = d ∫₀^τ e^{√D₀ B_s - D₀ s/2} ds`. Conditional on `DetClockEvolution` and
`OpenInputsMoments`. -/
theorem tendsto_totalMass_law (hDet : DetClockEvolution) (hOI : OpenInputsMoments) {b : ℝ}
    (hb0 : 0 < b) (hb1 : b < 1 / 2) {E : ℝ} (hE0 : -2 < E) (hE1 : E < 2) {T : ℝ} (hT : 0 < T)
    {n : ℕ → ℕ} {τ : ℝ} (hτ : 0 < τ) (hn : Tendsto (fun W => (n W : ℝ) / W) atTop (𝓝 τ))
    (hnT : ∀ W, (n W : ℝ) ≤ T * W) (f : ℝ →ᵇ ℝ) :
    Tendsto (fun W => ∫ x, f x ∂openProbeLaw W b E (fun _ => 1) (n W)) atTop
      (𝓝 (∫ x, f x ∂openClockLaw b E τ)) := by
  have h1 : IsClockWeight (fun _ : ℝ => (1 : ℝ)) :=
    ⟨continuous_const, fun _ => zero_le_one, 1, fun _ => le_rfl⟩
  have hfd := tendsto_profile_fdd hDet hOI hb0 hb1 hE0 hE1 hT hτ hn hnT (m := 1)
    (fun _ => fun _ => 1) (fun _ => h1) (fun x => f (x 0))
    (f.continuous.comp (continuous_apply 0)) (M := ‖f‖) (fun x => by
      rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm _)
  have hl : ∀ W, ∫ x, f x ∂openProbeLaw W b E (fun _ => 1) (n W) =
      ∫ p, f (profileVector (W := W) b E (fun _ : Fin 1 => fun _ : ℝ => (1 : ℝ)) (n W) p 0)
        ∂(oneEndedLaw W b (n W)).prod (circularVectorLaw (Fin W)) := by
    intro W
    unfold openProbeLaw
    rw [integral_map (measurable_probe (W := W) b E _ (n W)).aemeasurable
      f.continuous.aestronglyMeasurable]
    rfl
  have hr : ∫ x, f x ∂openClockLaw b E τ =
      ∫ ω, f (limitProfileVector b E (fun _ : Fin 1 => fun _ : ℝ => (1 : ℝ)) τ ω 0)
        ∂canonicalWienerLaw := by
    rw [openClockLaw, integral_map (measurable_openClockFunctional b E τ).aemeasurable
      f.continuous.aestronglyMeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [limitProfileVector, openClockIntegral, openClockFunctional, one_mul]
  simp_rw [hl, hr]
  exact hfd

/-- The density `x ↦ d e^{√D₀ B_{τ-x} - D₀(τ-x)/2}` of `Σ_τ` on `[0,τ]`, for a path `ω`. -/
def limitDensity (b E τ : ℝ) (ω : CanonicalWienerPath) (x : ℝ) : ℝ :=
  dStar b * exp (Real.sqrt (transportD0 b E) * ω (τ - x).toNNReal -
    transportD0 b E * (τ - x) / 2)

/-- The limit density is strictly positive (`b < 1`). -/
theorem limitDensity_pos {b : ℝ} (hb : b < 1) (E τ : ℝ) (ω : CanonicalWienerPath) (x : ℝ) :
    0 < limitDensity b E τ ω x :=
  mul_pos (by unfold dStar; exact div_pos one_pos (by linarith)) (exp_pos _)

/-- The limit density is continuous (Brownian paths are continuous). -/
theorem continuous_limitDensity (b E τ : ℝ) (ω : CanonicalWienerPath) :
    Continuous (limitDensity b E τ ω) := by
  unfold limitDensity
  have hev : Continuous (fun x : ℝ => ω (τ - x).toNNReal) :=
    ω.continuous.comp (continuous_real_toNNReal.comp (continuous_const.sub continuous_id))
  exact continuous_const.mul (continuous_exp.comp ((continuous_const.mul hev).sub
    ((continuous_const.mul (continuous_const.sub continuous_id)).div_const _)))

end BlockBand.Endpoints.Clock
