module

public import BlockBand.Endpoints.Response.LifetimeBridgeKernel

/-!
# The lifetime-bridge lemma from its parts

`lifetimeBridge_of_parts : (∀ D₀ > 0, LbkParts D₀) → LifetimeBridgeStatement` assembles the full
statement with the explicit kernel `p = lbkKernel D₀`. `LbkParts D₀` bundles five propositions,
each strictly weaker than the statement:

* `LbkSphereKernelPos` (deterministic; defined in the sibling module `LifetimeBridgeKernel`):
  `pY > 0` on `[0,1]²`.
* `LbkBaseExistence`: the base diffusion exists from every point of the strip.
* `LbkBaseTransitionLaw`: every base diffusion from `z` has one-time law `p_t(z, z') dz'` with the
  explicit `p` (uniqueness of one-time marginals and identification of the heat kernels).
* `LbkHTransformLaw`: the joint law of the extinction time and the finite-dimensional
  marginals of the absorbing `H` transform, in killed-density form.
* `LbkBridgeExistence`: the continuous base bridge (diffusion bridge construction).

The rest is proved here: the transfer of the transition law to the coordinate laws `lawX`, `lawY`
(using the sphere normalisation `∫ pY = 1` and the product structure), positivity of the corner
density, the disintegration (`lbk_disintegrate`: Tonelli, the shift `t = t_k + s`, and division by
`p_t(z, 0) > 0`; after dividing by the corner-lifetime density the result is precisely the base
bridge), and the lifetime law as its `k = 0` case.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
  BlockBand.Internal.Contracts.TransmissionUniform
open scoped ENNReal NNReal

/-!
### Notation for finite strings of transition densities
-/

/-- The last time `t_k` of `0 < t₁ < ⋯ < t_k` (`0` if `k = 0`). -/
def lbkLastTime {k : ℕ} (ts : Fin k → ℝ) : ℝ := (Fin.cons 0 ts : Fin (k + 1) → ℝ) (Fin.last k)

/-- The last point `z_k` of `z₀ = z, z₁, …, z_k` (`z` if `k = 0`). -/
def lbkLastPoint {α : Type*} (z : α) {k : ℕ} (zs : Fin k → α) : α :=
  (Fin.cons z zs : Fin (k + 1) → α) (Fin.last k)

/-- The string of transition densities `p_{t₁}(z, z₁) ⋯ p_{t_k - t_{k-1}}(z_{k-1}, z_k)`
(the numerator of `bridgeFddDensity` without its last factor). -/
def lbkFddProd {α : Type*} (p : ℝ → α → α → ℝ) (z : α) {k : ℕ} (ts : Fin k → ℝ)
    (zs : Fin k → α) : ℝ≥0∞ :=
  ∏ i : Fin k, ENNReal.ofReal
    (p (ts i - (Fin.cons 0 ts : Fin (k + 1) → ℝ) i.castSucc)
      ((Fin.cons z zs : Fin (k + 1) → α) i.castSucc) (zs i))

theorem lbk_bridgeFddDensity_eq {α : Type*} (p : ℝ → α → α → ℝ) (z e : α) (t : ℝ) {k : ℕ}
    (ts : Fin k → ℝ) (zs : Fin k → α) :
    bridgeFddDensity p z e t ts zs =
      lbkFddProd p z ts zs * ENNReal.ofReal (p (t - lbkLastTime ts) (lbkLastPoint z zs) e) /
        ENNReal.ofReal (p t z e) := rfl

/-!
### The parts
-/

/-- **Existence of the base diffusion** from every point of the closed strip: each coordinate
solves an autonomous one-dimensional SDE with Hölder-`1/2` diffusion and Lipschitz drift
(entrance boundaries, no local time). Proved as `lbkBaseExistence_holds`. -/
def LbkBaseExistence (D0 : ℝ) : Prop := ∀ z ∈ baseStrip, HasBaseDiffusion D0 z

/-- The transition law of the base diffusion is the explicit kernel: every base diffusion from
`z ∈ baseStrip` has `P(Z_t ∈ B) = ∫_B p_t(z, ·)` with `p = lbkKernel D0` (the coordinates are the
radial parts of hyperbolic and spherical Brownian motion, independent, with the radial heat
kernels in the coordinates `x`, `y`). This contains uniqueness of the one-time marginals for the
martingale problem (duality with the backward equation, or pathwise uniqueness), independence of
the coordinates, and the identification of McKean's formula and the Legendre series as the heat
kernels of `H²`, `S²`. -/
def LbkBaseTransitionLaw (D0 : ℝ) : Prop :=
  ∀ t : ℝ≥0, 0 < t → ∀ z ∈ baseStrip,
    ∀ (Ω : Type) (m : MeasurableSpace Ω) (𝓖 : Filtration ℝ≥0 m) (P : Measure Ω)
      (Z : ℝ≥0 → Ω → ℝ × ℝ), IsBaseDiffusion P 𝓖 D0 z Z →
      ∀ B : Set (ℝ × ℝ), MeasurableSet B →
        P (Z t ⁻¹' B) = ∫⁻ z' in B, ENNReal.ofReal (lbkKernel D0 t z z')

open scoped Classical in

/-- **The joint law of the `H` transform before and at its lifetime**: for every one-pair
boundary dual (`IsBoundaryDualProcess`, i.e. the absorbing `H` transform) from `z = (x, y)`, all
`0 < t₁ < ⋯ < t_k` and measurable `g, F ≥ 0`,
`E[g(σ₀)F(Z_{t₁..t_k}); t_k < σ₀ < ∞] =
  (D₀/2)(x+y) ∫ F(z₁..z_k) p_{t₁}(z,z₁)⋯p_{t_k-t_{k-1}}(z_{k-1},z_k)
    ∫_0^∞ g(t_k + s) p_s(z_k, 0) ds dz₁⋯dz_k`:
a finite string of killed transition densities `p_t(z,z')H(z')/H(z)` times the remaining
lifetime density `(D₀/2)H(z_k)⁻¹ p_s(z_k, 0)`; the factors `H(z_i)` telescope. It contains the
identification of `IsBoundaryDualProcess` with the Doob `H` transform of the base diffusion, the
Markov property at `t_k`, and the corner lifetime law from interior points. It follows from the
corner heat identity and the Doob killed law by `lbkHTransformLaw_of_doob`.
-/
def LbkHTransformLaw (D0 : ℝ) : Prop :=
  ∀ x y : ℝ, IsDualStart ![x] ![y] →
    ∀ (Ω : Type) (m : MeasurableSpace Ω) (𝓖 : Filtration ℝ≥0 m) (P : Measure Ω)
      (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ), IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y →
      ∀ (k : ℕ) (ts : Fin k → ℝ), StrictMono ts → (∀ i, 0 < ts i) →
        ∀ g : ℝ → ℝ≥0∞, Measurable g → ∀ F : (Fin k → ℝ × ℝ) → ℝ≥0∞, Measurable F →
          ∫⁻ ω, (if dualExtinction N ω < ⊤ ∧ ∀ i, ENNReal.ofReal (ts i) < dualExtinction N ω
              then g (dualExtinction N ω).toReal * F (fun i => dualPoint X Y (ts i) ω)
              else 0) ∂P =
            ENNReal.ofReal (D0 / 2 * (x + y)) *
              ∫⁻ zs, F zs * lbkFddProd (lbkKernel D0) (x, y) ts zs *
                ∫⁻ s in Ioi 0, g (lbkLastTime ts + s) *
                  ENNReal.ofReal (lbkKernel D0 s (lbkLastPoint (x, y) zs) (0, 0))

/-- Existence of the continuous base bridge from `z` to the corner, of every length `t > 0`, for
the explicit kernel (by Kolmogorov extension from the Chapman–Kolmogorov family
`bridgeFddDensity` plus a continuity criterion, or the `h`-transform of the base diffusion by
`p_{t-s}(·, 0)`). -/
def LbkBridgeExistence (D0 : ℝ) : Prop :=
  ∀ x y : ℝ, IsDualStart ![x] ![y] → ∀ t : ℝ, 0 < t →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (Z : ℝ → Ω → ℝ × ℝ),
      IsBaseBridge P (lbkKernel D0) (x, y) t Z

/-- The parts of the lifetime-bridge lemma at diffusivity `D₀`. -/
structure LbkParts (D0 : ℝ) : Prop where
  spherePos : LbkSphereKernelPos D0
  existence : LbkBaseExistence D0
  transition : LbkBaseTransitionLaw D0
  hTransform : LbkHTransformLaw D0
  bridge : LbkBridgeExistence D0

/-!
### Measurability and time bookkeeping
-/

theorem lbk_measurable_cons {α : Type*} [MeasurableSpace α] (z : α) {k : ℕ} (j : Fin (k + 1)) :
    Measurable fun zs : Fin k → α => (Fin.cons z zs : Fin (k + 1) → α) j := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [Fin.cons_zero]
    exact measurable_const
  · simp only [Fin.cons_succ]
    exact measurable_pi_apply i

theorem lbk_fddProd_measurable {p : ℝ → ℝ × ℝ → ℝ × ℝ → ℝ}
    (hp : Measurable fun w : ℝ × (ℝ × ℝ) × (ℝ × ℝ) => p w.1 w.2.1 w.2.2) (z : ℝ × ℝ) {k : ℕ}
    (ts : Fin k → ℝ) : Measurable fun zs : Fin k → ℝ × ℝ => lbkFddProd p z ts zs := by
  unfold lbkFddProd
  refine Finset.measurable_prod _ fun i _ => ?_
  exact (hp.comp ((measurable_const.prodMk ((lbk_measurable_cons z i.castSucc).prodMk
    (measurable_pi_apply i))))).ennreal_ofReal

theorem lbk_lastTime_nonneg {k : ℕ} {ts : Fin k → ℝ} (hpos : ∀ i, 0 < ts i) :
    0 ≤ lbkLastTime ts := by
  cases k with
  | zero => simp [lbkLastTime]
  | succ m =>
    simp only [lbkLastTime, ← Fin.succ_last, Fin.cons_succ]
    exact (hpos _).le

theorem lbk_forall_lt_iff {k : ℕ} {ts : Fin k → ℝ} (hts : StrictMono ts) {t : ℝ} (ht : 0 < t) :
    (∀ i, ts i < t) ↔ lbkLastTime ts < t := by
  cases k with
  | zero => simp [lbkLastTime, ht]
  | succ m =>
    simp only [lbkLastTime, ← Fin.succ_last, Fin.cons_succ]
    exact ⟨fun h => h _, fun h i => lt_of_le_of_lt (hts.monotone (Fin.le_last i)) h⟩

/-!
### The disintegration
-/

/-- The bridge disintegration, abstractly for a jointly measurable kernel `p` with positive corner
values: the "killed densities × remaining lifetime density" form equals
`∫ g(t) c p_t(z, 0) 1{t_k < t} E^{br}_{z,t}[F] dt`. -/
theorem lbk_disintegrate {p : ℝ → ℝ × ℝ → ℝ × ℝ → ℝ}
    (hp : Measurable fun w : ℝ × (ℝ × ℝ) × (ℝ × ℝ) => p w.1 w.2.1 w.2.2)
    {z : ℝ × ℝ} {c : ℝ} (hc : 0 ≤ c) (hcorner : ∀ t : ℝ, 0 < t → 0 < p t z (0, 0))
    {k : ℕ} {ts : Fin k → ℝ} (hts : StrictMono ts) (hpos : ∀ i, 0 < ts i)
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) {F : (Fin k → ℝ × ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ENNReal.ofReal c * ∫⁻ zs, F zs * lbkFddProd p z ts zs *
        ∫⁻ s in Ioi 0, g (lbkLastTime ts + s) * ENNReal.ofReal (p s (lbkLastPoint z zs) (0, 0)) =
      ∫⁻ t in Ioi 0, g t * ENNReal.ofReal (c * p t z (0, 0)) *
        (if ∀ i, ts i < t then ∫⁻ zs, F zs * bridgeFddDensity p z (0, 0) t ts zs else 0) := by
  classical
  set T := lbkLastTime ts with hTdef
  have hT : 0 ≤ T := lbk_lastTime_nonneg hpos
  set Q : ℝ → (Fin k → ℝ × ℝ) → ℝ≥0∞ := fun t zs =>
    F zs * lbkFddProd p z ts zs * ENNReal.ofReal (p (t - T) (lbkLastPoint z zs) (0, 0)) with hQ
  have hlast : Measurable fun zs : Fin k → ℝ × ℝ => lbkLastPoint z zs :=
    lbk_measurable_cons z (Fin.last k)
  have hQm : Measurable (Function.uncurry Q) := by
    refine (hF.comp measurable_snd).mul ((lbk_fddProd_measurable hp z ts).comp measurable_snd)
      |>.mul ?_
    exact (hp.comp ((measurable_fst.sub_const T).prodMk ((hlast.comp measurable_snd).prodMk
      measurable_const))).ennreal_ofReal
  set H : ℝ → (Fin k → ℝ × ℝ) → ℝ≥0∞ := fun t zs => (Ioi T).indicator (fun t => g t * Q t zs) t
    with hH
  have hHm : Measurable (Function.uncurry H) :=
    Measurable.ite (measurableSet_Ioi.preimage measurable_fst) ((hg.comp measurable_fst).mul hQm)
      measurable_const
  -- the integrand on `(0, ∞)`
  have hstep1 : ∀ t ∈ Ioi (0 : ℝ),
      g t * ENNReal.ofReal (c * p t z (0, 0)) *
          (if ∀ i, ts i < t then ∫⁻ zs, F zs * bridgeFddDensity p z (0, 0) t ts zs else 0) =
        ENNReal.ofReal c * ∫⁻ zs, H t zs := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    by_cases hlt : T < t
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ((lbk_forall_lt_iff hts ht').2 hlt))]
      have ha0 : ENNReal.ofReal (p t z (0, 0)) ≠ 0 := by
        rw [ENNReal.ofReal_ne_zero_iff]; exact hcorner t ht'
      have hai : (ENNReal.ofReal (p t z (0, 0)))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 ha0
      have hint : ∫⁻ zs, F zs * bridgeFddDensity p z (0, 0) t ts zs =
          (∫⁻ zs, Q t zs) * (ENNReal.ofReal (p t z (0, 0)))⁻¹ := by
        rw [← lintegral_mul_const' _ _ hai]
        refine lintegral_congr fun zs => ?_
        rw [lbk_bridgeFddDensity_eq, div_eq_mul_inv]
        simp only [hQ]
        ring
      have hH' : ∫⁻ zs, H t zs = g t * ∫⁻ zs, Q t zs := by
        simp only [hH, Set.indicator_of_mem (show t ∈ Ioi T from hlt)]
        exact lintegral_const_mul _ (hQm.comp (measurable_const.prodMk measurable_id))
      rw [hint, hH', ENNReal.ofReal_mul hc]
      calc g t * (ENNReal.ofReal c * ENNReal.ofReal (p t z (0, 0))) *
            ((∫⁻ zs, Q t zs) * (ENNReal.ofReal (p t z (0, 0)))⁻¹)
          = ENNReal.ofReal c * (g t * ∫⁻ zs, Q t zs) *
              (ENNReal.ofReal (p t z (0, 0)) * (ENNReal.ofReal (p t z (0, 0)))⁻¹) := by ring
        _ = _ := by rw [ENNReal.mul_inv_cancel ha0 ENNReal.ofReal_ne_top, mul_one]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => hlt ((lbk_forall_lt_iff hts ht').1 h)))]
      have : ∀ zs, H t zs = 0 := fun zs => by
        simp only [hH]
        exact Set.indicator_of_notMem (show t ∉ Ioi T from hlt) _
      simp [this]
  rw [setLIntegral_congr_fun measurableSet_Ioi hstep1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_lintegral_swap hHm.aemeasurable]
  congr 1
  refine lintegral_congr fun zs => ?_
  -- restrict to `(t_k, ∞)` and shift
  have hsub : ∫⁻ t in Ioi 0, H t zs = ∫⁻ t in Ioi T, g t * Q t zs := by
    simp only [hH]
    rw [lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      Ioi_inter_Ioi, max_eq_left hT]
  have hshift : ∫⁻ t in Ioi T, g t * Q t zs = ∫⁻ s in Ioi 0, g (T + s) * Q (T + s) zs := by
    have := (measurePreserving_add_left volume T).setLIntegral_comp_preimage_emb
      (MeasurableEquiv.addLeft T).measurableEmbedding (fun t => g t * Q t zs) (Ioi T)
    rw [preimage_const_add_Ioi, sub_self] at this
    exact this.symm
  rw [hsub, hshift]
  have hq : ∀ s, g (T + s) * Q (T + s) zs = F zs * lbkFddProd p z ts zs *
      (g (T + s) * ENNReal.ofReal (p s (lbkLastPoint z zs) (0, 0))) := fun s => by
    simp only [hQ, add_sub_cancel_left]
    ring
  simp_rw [hq]
  rw [lintegral_const_mul]
  exact (hg.comp (measurable_const.add measurable_id)).mul
    (hp.comp (f := fun s : ℝ => (s, lbkLastPoint z zs, ((0, 0) : ℝ × ℝ)))
      (measurable_id.prodMk measurable_const)).ennreal_ofReal

/-!
### The assembly
-/

theorem lbk_isDualStart_one {x y : ℝ} (h : IsDualStart ![x] ![y]) :
    0 ≤ x ∧ (0 ≤ y ∧ y ≤ 1) ∧ 0 < x + y := by
  refine ⟨by simpa using h.2.2.1 0, by simpa using h.2.2.2.1 0, by simpa using h.2.2.2.2 0 0⟩

/-- The lifetime-bridge lemma from its parts. The explicit witness is `p = lbkKernel D₀` with
`pX = lbkKernelX D₀`, `pY = lbkKernelY D₀`. -/
theorem lifetimeBridge_of_parts (h : ∀ D0 : ℝ, 0 < D0 → LbkParts D0) :
    LifetimeBridgeStatement := by
  intro D0 hD0
  obtain ⟨hpos, hex, hlaw, hH, hbr⟩ := h D0 hD0
  -- the coordinate normalisations
  have hY1 : ∀ t : ℝ, 0 < t → ∀ y ∈ Icc (0 : ℝ) 1,
      ∫⁻ y', ENNReal.ofReal (lbkKernelY D0 t y y') = 1 :=
    fun t ht y hy => lbk_lintegral_kernelY hD0 hpos ht hy
  have hX1 : ∀ t : ℝ≥0, 0 < t → ∀ z ∈ baseStrip,
      ∫⁻ x', ENNReal.ofReal (lbkKernelX D0 t z.1 x') = 1 := by
    intro t ht z hz
    obtain ⟨Ω, m, 𝓖, P, Z, hZ⟩ := hex z hz
    have h1 := hlaw t ht z hz Ω m 𝓖 P Z hZ univ MeasurableSet.univ
    have := hZ.prob
    rw [preimage_univ, measure_univ, ← univ_prod_univ, lbk_lintegral_prod hD0,
      Measure.restrict_univ, hY1 t (NNReal.coe_pos.2 ht) z.2 hz.2,
      mul_one] at h1
    exact h1.symm
  refine ⟨lbkKernel D0, ⟨hex, fun t _ z _ z' _ => lbk_kernel_nonneg hD0 hpos t z z',
    fun t ht z hz => lbk_kernel_continuousOn hD0 ht hz, hlaw⟩, lbk_kernel_measurable hD0,
    ⟨lbkKernelX D0, lbkKernelY D0, ⟨fun t _ x _ x' _ => lbk_kernelX_nonneg hD0 t x x',
      fun t _ y _ y' _ => lbk_kernelY_nonneg hpos t y y',
      fun t ht x _ => lbk_kernelX_continuousOn hD0 ht x,
      fun t ht y hy => lbk_kernelY_continuousOn hD0 ht hy, ?_, ?_⟩,
      fun _ _ _ _ _ _ => rfl⟩, ?_⟩
  · -- lawX
    intro t ht z hz Ω m 𝓖 P Z hZ A hA
    have h1 := hlaw t ht z hz Ω m 𝓖 P Z hZ (A ×ˢ univ) (hA.prod MeasurableSet.univ)
    rw [lbk_lintegral_prod hD0, Measure.restrict_univ, hY1 t (NNReal.coe_pos.2 ht) z.2 hz.2,
      mul_one] at h1
    rw [← h1]
    congr 1
    ext ω
    simp
  · -- lawY
    intro t ht z hz Ω m 𝓖 P Z hZ A hA
    have h1 := hlaw t ht z hz Ω m 𝓖 P Z hZ (univ ×ˢ A) (MeasurableSet.univ.prod hA)
    rw [lbk_lintegral_prod hD0, Measure.restrict_univ, hX1 t ht z hz, one_mul] at h1
    rw [← h1]
    congr 1
    ext ω
    simp
  · intro x y hxy
    obtain ⟨hx, hy, hs⟩ := lbk_isDualStart_one hxy
    have hz : (x, y) ∈ baseStrip := ⟨hx, hy⟩
    have hcorner : ∀ t : ℝ, 0 < t → 0 < lbkKernel D0 t (x, y) (0, 0) :=
      fun t ht => lbk_kernel_corner_pos hD0 hpos ht hz
    have hc : 0 ≤ D0 / 2 * (x + y) := by positivity
    have hdis : ∀ (Ω : Type) (m : MeasurableSpace Ω) (𝓖 : Filtration ℝ≥0 m) (P : Measure Ω)
        (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ),
        IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y →
        ∀ (k : ℕ) (ts : Fin k → ℝ), StrictMono ts → (∀ i, 0 < ts i) →
          ∀ g : ℝ → ℝ≥0∞, Measurable g → ∀ F : (Fin k → ℝ × ℝ) → ℝ≥0∞, Measurable F →
            ∫⁻ ω, (if dualExtinction N ω < ⊤ ∧ ∀ i, ENNReal.ofReal (ts i) < dualExtinction N ω
                then g (dualExtinction N ω).toReal * F (fun i => dualPoint X Y (ts i) ω)
                else 0) ∂P =
              ∫⁻ t in Ioi 0, g t * ENNReal.ofReal (cornerLifetimeDensity D0 (lbkKernel D0) (x, y) t) *
                (if ∀ i, ts i < t then
                  ∫⁻ zs, F zs * bridgeFddDensity (lbkKernel D0) (x, y) (0, 0) t ts zs
                  else 0) := by
      intro Ω m 𝓖 P N X Y hP k ts hts htp g hg F hF
      rw [hH x y hxy Ω m 𝓖 P N X Y hP k ts hts htp g hg F hF]
      exact lbk_disintegrate (lbk_kernel_measurable hD0) hc hcorner hts htp hg hF
    refine ⟨hcorner, hbr x y hxy, fun Ω m 𝓖 P N X Y hP => ⟨fun g hg => ?_, hdis Ω m 𝓖 P N X Y hP⟩⟩
    -- the lifetime law is the `k = 0` case
    have h0 := hdis Ω m 𝓖 P N X Y hP 0 (fun i => i.elim0) (fun a _ _ => a.elim0)
      (fun i => i.elim0) g hg (fun _ => 1) measurable_const
    have hL : ∀ ω, (if dualExtinction N ω < ⊤ ∧ ∀ i : Fin 0, ENNReal.ofReal ((fun i => i.elim0 :
        Fin 0 → ℝ) i) < dualExtinction N ω then g (dualExtinction N ω).toReal * 1 else 0) =
        (if dualExtinction N ω < ⊤ then g (dualExtinction N ω).toReal else 0) := fun ω => by
      simp
    simp_rw [hL] at h0
    rw [h0]
    refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht' : (0 : ℝ) < t := ht
    have hb : ∀ zs : Fin 0 → ℝ × ℝ,
        bridgeFddDensity (lbkKernel D0) (x, y) (0, 0) t (fun i => i.elim0) zs = 1 := fun zs => by
      rw [lbk_bridgeFddDensity_eq]
      simp only [lbkFddProd, Finset.univ_eq_empty, Finset.prod_empty, one_mul, lbkLastTime,
        lbkLastPoint, Fin.last_zero, Fin.cons_zero, sub_zero]
      exact ENNReal.div_self ((ENNReal.ofReal_ne_zero_iff).2 (hcorner t ht')) ENNReal.ofReal_ne_top
    simp [hb, MeasureTheory.volume_pi]

end BlockBand.Endpoints
