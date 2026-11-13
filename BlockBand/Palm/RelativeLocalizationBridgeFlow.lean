module

public import BlockBand.Palm.RelativeLocalizationBridgeRates

/-!
# Relative localization: `E_aux|𝓜|²` solves the mass equations

Hypotheses: `LinearRotationFlowContract N` and, for the almost-sure forms, `DysonBrownianMotion N`
(non-collision, through `ae_noCollision`). `E_aux` is the expectation over the auxiliary noise.

* `bridgeB2_of_noCollision` / `bridgeB2`: for every short rotation flow `M` started at `s`
  (rates `shortRate`, no damping), `v_k(x) = E_aux Σ_j |M_{s,x}(k,j)|² v₀_j` solves
  `ForwardMassSolution (shortGenerator F a ω ℓ) s u v₀` on every `[s,u] ⊆ [a,c]`;
  `bridgeB2_column_of_noCollision` / `bridgeB2_column`: `x ↦ E_aux |M_{s,x}(j,k)|²` solves it with
  `v₀ = δ_k` (the column form used by `short_column`).
* `bridgeB1_of_noCollision` / `bridgeB1`: for every family `Mf x` of reference rotation flows
  started at `x ∈ [a,c]` (rates `shortRate`, damping `β̂ = refDamping`),
  `P(x)_{kj} = E_aux |(𝓜_{x,c})_{kj}|²` is a `BackwardPropagator (referenceGenerator F a b₀ ω ℓ) a c`.
* `integrable_sq_entry` and `integral_sum_mul_sq`: every squared entry of a rotation flow is
  `E_aux`-integrable on `[s,c]` (so `E_aux Σ_j = Σ_j E_aux`), because `E_aux Σ_j |𝓜_{s,x}(k,j)|²`
  solves the mass equation with `v₀ = 1`, which is positive (`forwardMass_ones_pos`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.RelativeLocalization.StochasticBridge

open MeasureTheory Set BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.TransmissionFlow (IsRotationFlow LinearRotationFlowContract
  massGenerator)
open BlockBand.Internal.Contracts.Transmission (DysonBrownianMotion)
open BlockBand.SourceProcess.FiniteDriverIntegration BlockBand.SourceProcess.Stochastic
open BlockBand.Palm.RelativeLocalization (IsSubGenerator forwardMass_nonneg le_exp_mul_of_deriv_le)
open scoped NNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {N : ℕ}

/-!
## The mass generator
-/

theorem sum_massGenerator_mul (r : ℝ → Fin N → Fin N → ℝ) (κ : ℝ → Fin N → ℝ) (x : ℝ)
    (k : Fin N) (v : Fin N → ℝ) :
    ∑ l, massGenerator r κ x k l * v l =
      (-(∑ m ∈ Finset.univ.erase k, r x k m) - κ x k) * v k +
        ∑ l ∈ Finset.univ.erase k, r x k l * v l := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
  congr 1
  · simp [massGenerator]
  · refine Finset.sum_congr rfl fun l hl => ?_
    simp [massGenerator, (Finset.ne_of_mem_erase hl).symm]

theorem massGenerator_isSubGenerator {r : ℝ → Fin N → Fin N → ℝ} {κ : ℝ → Fin N → ℝ}
    (hr0 : ∀ x k l, 0 ≤ r x k l) (hκ0 : ∀ x k, 0 ≤ κ x k) (s u : ℝ) :
    IsSubGenerator (massGenerator r κ) s u := by
  refine fun x _ => ⟨fun k l hkl => ?_, fun k => ?_⟩
  · simp only [massGenerator, hkl, ite_false]
    exact hr0 x k l
  · have h := sum_massGenerator_mul r κ x k (fun _ => 1)
    simp only [mul_one] at h
    rw [h]
    linarith [hκ0 x k]

/-- The solution with data `1` stays positive (Gronwall from below). -/
theorem forwardMass_ones_pos {r : ℝ → Fin N → Fin N → ℝ} {κ : ℝ → Fin N → ℝ} {s c : ℝ}
    (hr : ContinuousOn r (Icc s c)) (hκ : ContinuousOn κ (Icc s c))
    (hr0 : ∀ x k l, 0 ≤ r x k l) (hκ0 : ∀ x k, 0 ≤ κ x k) {v : ℝ → Fin N → ℝ}
    (hv : ForwardMassSolution (massGenerator r κ) s c (fun _ => 1) v) :
    ∀ x ∈ Icc s c, ∀ k, 0 < v x k := by
  intro x hx k
  have hnn := forwardMass_nonneg (massGenerator_isSubGenerator hr0 hκ0 s c) hv
    (fun _ => zero_le_one)
  have hg : ContinuousOn (fun x => ∑ m ∈ Finset.univ.erase k, r x k m + κ x k) (Icc s c) :=
    (continuousOn_finsetSum _ fun m _ =>
      ((continuous_apply m).comp (continuous_apply k)).comp_continuousOn hr).add
      ((continuous_apply k).comp_continuousOn hκ)
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  have hle := le_exp_mul_of_deriv_le (f := fun x => -v x k)
    (f' := fun x => -∑ l, massGenerator r κ x k l * v x l) (K := -K)
    ((continuous_apply k).comp_continuousOn hv.2.1).neg
    (fun y hy => (hasDerivAt_pi.mp (hv.2.2 y hy) k).neg)
    (fun y hy => by
      have hyI : y ∈ Icc s c := Ioo_subset_Icc_self hy
      rw [sum_massGenerator_mul]
      have h1 : 0 ≤ ∑ l ∈ Finset.univ.erase k, r y k l * v y l :=
        Finset.sum_nonneg fun l _ => mul_nonneg (hr0 _ _ _) (hnn y hyI l)
      have h2 : ∑ m ∈ Finset.univ.erase k, r y k m + κ y k ≤ K :=
        (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hK y hyI)
      have h3 := hnn y hyI k
      nlinarith)
    x hx
  have h0 : v s k = 1 := by rw [hv.1]
  simp only [h0] at hle
  have := Real.exp_pos (-K * (x - s))
  linarith

/-!
## Integrability of the squared entries
-/

theorem stronglyMeasurable_entry {S : Type} [MeasurableSpace S] {μ : Measure S}
    [IsProbabilityMeasure μ] {r : ℝ → Fin N → Fin N → ℝ} {κ : ℝ → Fin N → ℝ} {a c s : ℝ}
    {M : ℝ≥0 → DriverSample S ((Fin N × Fin N) × Fin 2) → Matrix (Fin N) (Fin N) ℂ}
    (hM : IsRotationFlow μ r κ a c s M) (t : ℝ≥0) (k j : Fin N) :
    StronglyMeasurable fun y => ‖M t y k j‖ ^ 2 := by
  have h := (hM.1.adapted t).mono ((driverAugmented (κ := (Fin N × Fin N) × Fin 2) μ).le t)
  have hc : @Continuous (Matrix (Fin N) (Fin N) ℂ) ℂ
      PseudoMetricSpace.toUniformSpace.toTopologicalSpace _ (fun A => A k j) := by
    exact (continuous_apply j).comp (continuous_apply k)
  exact ((continuous_norm.pow 2).comp hc).comp_stronglyMeasurable h

theorem integrable_sq_entry_of_sum {S : Type} [MeasurableSpace S] {μ : Measure S}
    [IsProbabilityMeasure μ] {r : ℝ → Fin N → Fin N → ℝ} {κ : ℝ → Fin N → ℝ} {a c s : ℝ}
    {M : ℝ≥0 → DriverSample S ((Fin N × Fin N) × Fin 2) → Matrix (Fin N) (Fin N) ℂ}
    (hM : IsRotationFlow μ r κ a c s M) (t : ℝ≥0) (k : Fin N)
    (hsum : ∫ y, ∑ j, ‖M t y k j‖ ^ 2 * (1 : ℝ)
      ∂driverLaw (κ := (Fin N × Fin N) × Fin 2) μ ≠ 0) (j : Fin N) :
    Integrable (fun y => ‖M t y k j‖ ^ 2) (driverLaw (κ := (Fin N × Fin N) × Fin 2) μ) := by
  have hI := Integrable.of_integral_ne_zero hsum
  refine hI.mono (stronglyMeasurable_entry hM t k j).aestronglyMeasurable
    (ae_of_all _ fun y => ?_)
  simp only [mul_one, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  exact Finset.single_le_sum (f := fun j => ‖M t y k j‖ ^ 2) (fun _ _ => by positivity)
    (Finset.mem_univ j)

/-- **Integrability.** Every squared entry `|𝓜_{s,x}(k,j)|²` of a rotation flow is
`E_aux`-integrable for `x ∈ [s,c]`. -/
theorem integrable_sq_entry (hRF : LinearRotationFlowContract N) {S : Type} [MeasurableSpace S]
    {μ : Measure S} [IsProbabilityMeasure μ] {r : ℝ → Fin N → Fin N → ℝ} {κ : ℝ → Fin N → ℝ}
    {a c : ℝ} (hac : a ≤ c) (hr : ContinuousOn r (Icc a c)) (hκ : ContinuousOn κ (Icc a c))
    (hrs : ∀ x k l, r x k l = r x l k) (hr0 : ∀ x k l, 0 ≤ r x k l) (hκ0 : ∀ x k, 0 ≤ κ x k)
    {s : ℝ} (hs : s ∈ Icc a c)
    {M : ℝ≥0 → DriverSample S ((Fin N × Fin N) × Fin 2) → Matrix (Fin N) (Fin N) ℂ}
    (hM : IsRotationFlow μ r κ a c s M) {x : ℝ} (hx : x ∈ Icc s c) (k j : Fin N) :
    Integrable (fun y => ‖M (x - s).toNNReal y k j‖ ^ 2)
      (driverLaw (κ := (Fin N × Fin N) × Fin 2) μ) := by
  have hv := (hRF S μ r κ a c hac hr hκ hrs hr0 hκ0).2.2.1 s hs M hM (fun _ => 1)
  rw [← forwardMassSolution_eq] at hv
  have hpos := forwardMass_ones_pos (hr.mono (Icc_subset_Icc_left hs.1))
    (hκ.mono (Icc_subset_Icc_left hs.1)) hr0 hκ0 hv x hx k
  exact integrable_sq_entry_of_sum hM _ k hpos.ne' j

theorem integral_sum_mul_sq (hRF : LinearRotationFlowContract N) {S : Type} [MeasurableSpace S]
    {μ : Measure S} [IsProbabilityMeasure μ] {r : ℝ → Fin N → Fin N → ℝ} {κ : ℝ → Fin N → ℝ}
    {a c : ℝ} (hac : a ≤ c) (hr : ContinuousOn r (Icc a c)) (hκ : ContinuousOn κ (Icc a c))
    (hrs : ∀ x k l, r x k l = r x l k) (hr0 : ∀ x k l, 0 ≤ r x k l) (hκ0 : ∀ x k, 0 ≤ κ x k)
    {s : ℝ} (hs : s ∈ Icc a c)
    {M : ℝ≥0 → DriverSample S ((Fin N × Fin N) × Fin 2) → Matrix (Fin N) (Fin N) ℂ}
    (hM : IsRotationFlow μ r κ a c s M) {x : ℝ} (hx : x ∈ Icc s c) (w : Fin N → ℝ)
    (e : Fin N → Fin N × Fin N) :
    ∫ y, ∑ j, w j * ‖M (x - s).toNNReal y (e j).1 (e j).2‖ ^ 2
        ∂driverLaw (κ := (Fin N × Fin N) × Fin 2) μ =
      ∑ j, w j * ∫ y, ‖M (x - s).toNNReal y (e j).1 (e j).2‖ ^ 2
        ∂driverLaw (κ := (Fin N × Fin N) × Fin 2) μ := by
  rw [integral_finsetSum _ fun j _ =>
    (integrable_sq_entry hRF hac hr hκ hrs hr0 hκ0 hs hM hx (e j).1 (e j).2).const_mul (w j)]
  exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _

/-!
## The short flow
-/

theorem forwardMass_restrict {L : ℝ → Fin N → Fin N → ℝ} {s u c : ℝ} {v₀ : Fin N → ℝ}
    {v : ℝ → Fin N → ℝ} (hv : ForwardMassSolution L s c v₀ v) (huc : u ≤ c) :
    ForwardMassSolution L s u v₀ v :=
  ⟨hv.1, hv.2.1.mono (Icc_subset_Icc_right huc), fun x hx => hv.2.2 x ⟨hx.1, hx.2.trans_le huc⟩⟩

/-- **Short-flow mass identity (pathwise).** On a collision-free path,
`E_aux Σ_j |M_{s,x}(k,j)|² v₀_j` of every short rotation flow started at `s` solves the short mass
equation on `[s,u]`. -/
theorem bridgeB2_of_noCollision (hRF : LinearRotationFlowContract N)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a c : ℝ} (hac : a ≤ c)
    {ω : FlowSample N} (hω : NoCollision F a c ω) (ℓ : ℕ) {S : Type} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] {s u : ℝ} (has : a ≤ s) (hsu : s ≤ u) (huc : u ≤ c)
    {M : ℝ≥0 → DriverSample S ((Fin N × Fin N) × Fin 2) → Matrix (Fin N) (Fin N) ℂ}
    (hM : IsRotationFlow μ (shortRate F a ω ℓ) (fun _ _ => 0) a c s M) (v₀ : Fin N → ℝ) :
    ForwardMassSolution (shortGenerator F a ω ℓ) s u v₀ (fun x k =>
      ∫ y, ∑ j, ‖M (x - s).toNNReal y k j‖ ^ 2 * v₀ j
        ∂driverLaw (κ := (Fin N × Fin N) × Fin 2) μ) := by
  have H := hRF S μ (shortRate F a ω ℓ) (fun _ _ => 0) a c hac (continuousOn_shortRate hF hω ℓ)
    continuousOn_const (shortRate_comm F a ω ℓ) (shortRate_nonneg F a ω ℓ) (fun _ _ => le_rfl)
  rw [shortGenerator_eq_massGenerator]
  exact forwardMass_restrict (H.2.2.1 s ⟨has, hsu.trans huc⟩ M hM v₀) huc

/-- **Short-flow mass identity, column form (pathwise).** `x ↦ E_aux |M_{s,x}(j,k)|²` solves the
short mass equation on `[s,u]` with `v₀ = δ_k`. -/
theorem bridgeB2_column_of_noCollision (hRF : LinearRotationFlowContract N)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a c : ℝ} (hac : a ≤ c)
    {ω : FlowSample N} (hω : NoCollision F a c ω) (ℓ : ℕ) {S : Type} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] {s u : ℝ} (has : a ≤ s) (hsu : s ≤ u) (huc : u ≤ c)
    {M : ℝ≥0 → DriverSample S ((Fin N × Fin N) × Fin 2) → Matrix (Fin N) (Fin N) ℂ}
    (hM : IsRotationFlow μ (shortRate F a ω ℓ) (fun _ _ => 0) a c s M) (k : Fin N) :
    ForwardMassSolution (shortGenerator F a ω ℓ) s u (fun j => if j = k then 1 else 0)
      (fun x j => ∫ y, ‖M (x - s).toNNReal y j k‖ ^ 2
        ∂driverLaw (κ := (Fin N × Fin N) × Fin 2) μ) := by
  have h := bridgeB2_of_noCollision hRF hF hac hω ℓ μ has hsu huc hM
    (fun j => if j = k then 1 else 0)
  have he : (fun x j => ∫ y, ‖M (x - s).toNNReal y j k‖ ^ 2
        ∂driverLaw (κ := (Fin N × Fin N) × Fin 2) μ) =
      fun x j => ∫ y, ∑ i, ‖M (x - s).toNNReal y j i‖ ^ 2 * (if i = k then 1 else 0)
        ∂driverLaw (κ := (Fin N × Fin N) × Fin 2) μ := by
    funext x j
    congr 1
    funext y
    simp
  rw [he]
  exact h

/-- The short-flow mass identity, almost surely. -/
theorem bridgeB2 (hRF : LinearRotationFlowContract N) (hDBM : DysonBrownianMotion N)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a c : ℝ} (ha : 0 < a) (hac : a ≤ c)
    (ℓ : ℕ) :
    ∀ᵐ ω ∂flowLaw N a, ∀ (S : Type) [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
      (s u : ℝ), a ≤ s → s ≤ u → u ≤ c →
      ∀ M : ℝ≥0 → DriverSample S ((Fin N × Fin N) × Fin 2) → Matrix (Fin N) (Fin N) ℂ,
        IsRotationFlow μ (shortRate F a ω ℓ) (fun _ _ => 0) a c s M → ∀ v₀ : Fin N → ℝ,
        ForwardMassSolution (shortGenerator F a ω ℓ) s u v₀ (fun x k =>
          ∫ y, ∑ j, ‖M (x - s).toNNReal y k j‖ ^ 2 * v₀ j
            ∂driverLaw (κ := (Fin N × Fin N) × Fin 2) μ) :=
  (ae_noCollision hDBM hF ha c).mono fun _ hω _ _ μ _ _ _ has hsu huc _ hM v₀ =>
    bridgeB2_of_noCollision hRF hF hac hω ℓ μ has hsu huc hM v₀

/-- The short-flow mass identity, column form, almost surely. -/
theorem bridgeB2_column (hRF : LinearRotationFlowContract N) (hDBM : DysonBrownianMotion N)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a c : ℝ} (ha : 0 < a) (hac : a ≤ c)
    (ℓ : ℕ) :
    ∀ᵐ ω ∂flowLaw N a, ∀ (S : Type) [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
      (s u : ℝ), a ≤ s → s ≤ u → u ≤ c →
      ∀ M : ℝ≥0 → DriverSample S ((Fin N × Fin N) × Fin 2) → Matrix (Fin N) (Fin N) ℂ,
        IsRotationFlow μ (shortRate F a ω ℓ) (fun _ _ => 0) a c s M → ∀ k : Fin N,
        ForwardMassSolution (shortGenerator F a ω ℓ) s u (fun j => if j = k then 1 else 0)
          (fun x j => ∫ y, ‖M (x - s).toNNReal y j k‖ ^ 2
            ∂driverLaw (κ := (Fin N × Fin N) × Fin 2) μ) :=
  (ae_noCollision hDBM hF ha c).mono fun _ hω _ _ μ _ _ _ has hsu huc _ hM k =>
    bridgeB2_column_of_noCollision hRF hF hac hω ℓ μ has hsu huc hM k

/-!
## The reference flow
-/

/-- **Reference-flow mass identity (pathwise).** On a collision-free path, for every family `Mf x`
of reference rotation flows started at `x ∈ [a,c]`, `P(x)_{kj} = E_aux |(𝓜_{x,c})_{kj}|²` is a
backward propagator of the reference generator. -/
theorem bridgeB1_of_noCollision (hRF : LinearRotationFlowContract N)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a c : ℝ} (hac : a ≤ c)
    {ω : FlowSample N} (hω : NoCollision F a c ω) (b₀ : ℝ) (ℓ : ℕ) {S : Type}
    [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    {Mf : ℝ → ℝ≥0 → DriverSample S ((Fin N × Fin N) × Fin 2) → Matrix (Fin N) (Fin N) ℂ}
    (hMf : ∀ x ∈ Icc a c,
      IsRotationFlow μ (shortRate F a ω ℓ) (refDamping F a b₀ ω ℓ) a c x (Mf x)) :
    BackwardPropagator (referenceGenerator F a b₀ ω ℓ) a c (fun x k j =>
      ∫ y, ‖Mf x (c - x).toNNReal y k j‖ ^ 2 ∂driverLaw (κ := (Fin N × Fin N) × Fin 2) μ) := by
  have H := hRF S μ (shortRate F a ω ℓ) (refDamping F a b₀ ω ℓ) a c hac
    (continuousOn_shortRate hF hω ℓ) (continuousOn_refDamping hF hω b₀ ℓ)
    (shortRate_comm F a ω ℓ) (shortRate_nonneg F a ω ℓ) (refDamping_nonneg F a b₀ ω ℓ)
  rw [referenceGenerator_eq_massGenerator]
  exact H.2.2.2 Mf hMf

/-- **Reference-flow mass identity, forward form (pathwise).** The reference flow started at `s` also
solves the forward reference mass equation on `[s,c]`. -/
theorem bridgeB1_forward_of_noCollision (hRF : LinearRotationFlowContract N)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a c : ℝ} (hac : a ≤ c)
    {ω : FlowSample N} (hω : NoCollision F a c ω) (b₀ : ℝ) (ℓ : ℕ) {S : Type}
    [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ] {s : ℝ} (hs : s ∈ Icc a c)
    {M : ℝ≥0 → DriverSample S ((Fin N × Fin N) × Fin 2) → Matrix (Fin N) (Fin N) ℂ}
    (hM : IsRotationFlow μ (shortRate F a ω ℓ) (refDamping F a b₀ ω ℓ) a c s M)
    (v₀ : Fin N → ℝ) :
    ForwardMassSolution (referenceGenerator F a b₀ ω ℓ) s c v₀ (fun x k =>
      ∫ y, ∑ j, ‖M (x - s).toNNReal y k j‖ ^ 2 * v₀ j
        ∂driverLaw (κ := (Fin N × Fin N) × Fin 2) μ) := by
  have H := hRF S μ (shortRate F a ω ℓ) (refDamping F a b₀ ω ℓ) a c hac
    (continuousOn_shortRate hF hω ℓ) (continuousOn_refDamping hF hω b₀ ℓ)
    (shortRate_comm F a ω ℓ) (shortRate_nonneg F a ω ℓ) (refDamping_nonneg F a b₀ ω ℓ)
  rw [referenceGenerator_eq_massGenerator]
  exact H.2.2.1 s hs M hM v₀

/-- The reference-flow mass identity, almost surely. -/
theorem bridgeB1 (hRF : LinearRotationFlowContract N) (hDBM : DysonBrownianMotion N)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a c : ℝ} (ha : 0 < a) (hac : a ≤ c)
    (b₀ : ℝ) (ℓ : ℕ) :
    ∀ᵐ ω ∂flowLaw N a, ∀ (S : Type) [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
      (Mf : ℝ → ℝ≥0 → DriverSample S ((Fin N × Fin N) × Fin 2) → Matrix (Fin N) (Fin N) ℂ),
      (∀ x ∈ Icc a c,
        IsRotationFlow μ (shortRate F a ω ℓ) (refDamping F a b₀ ω ℓ) a c x (Mf x)) →
      BackwardPropagator (referenceGenerator F a b₀ ω ℓ) a c (fun x k j =>
        ∫ y, ‖Mf x (c - x).toNNReal y k j‖ ^ 2 ∂driverLaw (κ := (Fin N × Fin N) × Fin 2) μ) :=
  (ae_noCollision hDBM hF ha c).mono fun _ hω _ _ μ _ _ hMf =>
    bridgeB1_of_noCollision hRF hF hac hω b₀ ℓ μ hMf

/-!
## Existence of the flows (from `LinearRotationFlowContract`)
-/

/-- Short and reference rotation flows exist from every start in `[a,c]` on collision-free
paths. -/
theorem exists_rotationFlows (hRF : LinearRotationFlowContract N)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a c : ℝ} (hac : a ≤ c)
    {ω : FlowSample N} (hω : NoCollision F a c ω) (b₀ : ℝ) (ℓ : ℕ) {S : Type}
    [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ] {s : ℝ} (hs : s ∈ Icc a c) :
    (∃ M, IsRotationFlow μ (shortRate F a ω ℓ) (fun _ _ => 0) a c s M) ∧
      ∃ M, IsRotationFlow μ (shortRate F a ω ℓ) (refDamping F a b₀ ω ℓ) a c s M :=
  ⟨(hRF S μ (shortRate F a ω ℓ) (fun _ _ => 0) a c hac (continuousOn_shortRate hF hω ℓ)
      continuousOn_const (shortRate_comm F a ω ℓ) (shortRate_nonneg F a ω ℓ)
      (fun _ _ => le_rfl)).1 s hs,
    (hRF S μ (shortRate F a ω ℓ) (refDamping F a b₀ ω ℓ) a c hac
      (continuousOn_shortRate hF hω ℓ) (continuousOn_refDamping hF hω b₀ ℓ)
      (shortRate_comm F a ω ℓ) (shortRate_nonneg F a ω ℓ) (refDamping_nonneg F a b₀ ω ℓ)).1 s hs⟩

end BlockBand.Palm.RelativeLocalization.StochasticBridge
