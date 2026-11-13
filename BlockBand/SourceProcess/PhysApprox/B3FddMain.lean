module

public import BlockBand.SourceProcess.PhysApprox.B3FddCoord

/-!
# Finite-dimensional distributions: `TargetCapFddAll` and `TargetCapFdd`

The subsequential cap limit for the complex closed process, through the abstract
`WordLim.exists_limit` (no `T` cap).

* **`targetCapFddAll_holds : TargetCapFddAll`**. Along a tail of `W_n` on which the frame is
  admissible and `P_W(cap) ≥ P(μ(s) ∈ capSet K h)/2` (`CapCond.tendsto_capProb`, non-atomic `h`),
  the conditioned laws `condL` of the births-removed coordinates `fddProc` satisfy the three
  hypotheses of `WordLim.exists_limit` with `t₀ = 0`:
  - measurability (`measurable_fddCoord`);
  - one-time tightness at every `t ≥ 0` (`fdd_tight`: the start bound and chaining);
  - the modulus on every `[0, T']` (`fdd_modulus`: `Modul.modulusS` at the horizon
    `max (max T s) (s + T')`; the Doob argument from time `s` on).
  The candidate is `extPath` plus the limit jumps `gramJ`, `kJ`. `G − J` and `𝒦 − J_𝒦` are
  `extPath`, which is continuous for **every** `ω` (`continuous_extPath`; `0` off `goodSet`).
  At a non-birth time the finite-`W` jumps are eventually the limit jumps
  (`eventually_jumpAll_eq`). The entrance coordinates are tested at time `0` through their real
  part (`readT`, `adjust`), which is the identity at finite `W`.
* `complexCapFdd_of_all : ComplexCapFddAll → ComplexCapFdd` (on `s + u ≤ max(s, T)` the stopped
  length `limLen` is `limLenAll`), hence **`targetCapFdd_holds : TargetCapFdd`**.

Hypotheses used: `TransmissionLawContract` (cap mass), `ComplexClosedSummed` and
`ComplexClosedLindeberg` (modulus and stop tail). `ComplexClosedTight` and
`ComplexKStoppedMomentMax` are not used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.Fdd

open MeasureTheory ProbabilityTheory Filter Topology Matrix Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open BlockBand.SourceProcess.FullSourceGenerator.WordLim
open scoped NNReal ENNReal

variable {np K : ℕ}

/-- `extPath` is continuous on `ℝ≥0` for **every** path (`0` off `goodSet`). -/
theorem continuous_extPath (a : ℕ) (ω : ℕ → ℂ) :
    Continuous fun u : ℝ≥0 => extPath 0 a ω (u : ℝ) := by
  classical
  by_cases hω : ω ∈ goodSet 0
  · exact (continuousOn_extPath hω a).comp_continuous NNReal.continuous_coe fun u => u.2
  · have e : (fun u : ℝ≥0 => extPath 0 a ω (u : ℝ)) = fun _ => 0 := by
      funext u; simp [extPath, hω]
    rw [e]; exact continuous_const

theorem gramEntry_gramOfEntries {c : Type*} (x : Fin 2 × c × c → ℂ) (e : Fin 2 × c × c) :
    gramEntry e (gramOfEntries x) = x e := by
  obtain ⟨σ, k, l⟩ := e
  fin_cases σ <;> simp [gramEntry, gramOfEntries]

/-! ## The limit candidate -/

/-- The limit observable: `extPath` plus the limit jump. -/
def limY (b E s : ℝ) (τ m : Fin np → ℝ) (l : LIdx K np) (u : ℝ≥0) (ω : ℕ → ℂ) : ℂ :=
  extPath 0 (Encodable.encode l) ω u + limJ b E s τ m l u

/-- The limit Gram state. -/
def limG (b E s : ℝ) (τ m : Fin np → ℝ) (u : ℝ≥0) (ω : ℕ → ℂ) :
    GramState (SrcCol K (Fin np)) :=
  gramOfEntries fun e => limY b E s τ m (Sum.inl e : LIdx K np) u ω

/-- The limit `𝒦`. -/
def limK (K : ℕ) (b E s : ℝ) (τ m : Fin np → ℝ) (u : ℝ≥0) (ω : ℕ → ℂ) :
    Matrix (Fin np) (Fin np) ℂ :=
  Matrix.of fun i j => limY b E s τ m (Sum.inr (Sum.inr (i, j)) : LIdx K np) u ω

/-- The limit entrance coordinates. -/
def limT (K : ℕ) (ω : ℕ → ℂ) (k : ℕ) : ℝ :=
  (extPath 0 (Encodable.encode (Sum.inr (Sum.inl k) : LIdx K np)) ω 0).re

theorem limG_sub (b E s : ℝ) (τ m : Fin np → ℝ) (u : ℝ≥0) (ω : ℕ → ℂ) :
    limG (K := K) b E s τ m u ω - gramJ b s τ m u =
      gramOfEntries fun e => extPath 0 (Encodable.encode (Sum.inl e : LIdx K np)) ω u := by
  ext k l
  · simp [limG, limY, limJ, gramOfEntries, gramEntry]
  · simp [limG, limY, limJ, gramOfEntries, gramEntry]

theorem limK_sub (b E s : ℝ) (τ m : Fin np → ℝ) (u : ℝ≥0) (ω : ℕ → ℂ) :
    limK K b E s τ m u ω - kJ E s τ m u = Matrix.of fun i j =>
      extPath 0 (Encodable.encode (Sum.inr (Sum.inr (i, j)) : LIdx K np)) ω u := by
  ext i j
  simp [limK, limY, limJ]

theorem continuous_matrixOf {n : Type*} :
    Continuous fun x : n × n → ℂ => (Matrix.of fun i j => x (i, j) : Matrix n n ℂ) :=
  continuous_matrix fun _ _ => continuous_apply _

/-- **The candidate's regularity.** -/
theorem isCapLimitData_lim (b E s : ℝ) (τ m : Fin np → ℝ) {Q : Measure (ℕ → ℂ)}
    (hQ : IsProbabilityMeasure Q) (hmeas : ∀ a t, 0 ≤ t → Measurable fun ω => extPath 0 a ω t) :
    IsCapLimitData b E s τ m K Q (limT (np := np) K) (limG b E s τ m) (limK K b E s τ m) := by
  have hY : ∀ (l : LIdx K np) (u : ℝ≥0), Measurable (limY b E s τ m l u) := fun l u =>
    (hmeas _ _ u.2).add_const _
  refine ⟨hQ, Measurable.of_eval fun k => Complex.measurable_re.comp (hmeas
      (Encodable.encode (Sum.inr (Sum.inl k) : LIdx K np)) 0 le_rfl),
    fun u => ?_, fun u => ?_, fun ω => ?_, fun ω => ?_⟩
  · have hv : Measurable fun ω => fun e => limY b E s τ m (Sum.inl e : LIdx K np) u ω :=
      Measurable.of_eval fun e => hY _ u
    exact continuous_gramOfEntries.comp_stronglyMeasurable hv.stronglyMeasurable
  · have hv : Measurable fun ω => fun ij : Fin np × Fin np =>
        limY b E s τ m (Sum.inr (Sum.inr ij) : LIdx K np) u ω :=
      Measurable.of_eval fun ij => hY _ u
    exact continuous_matrixOf.comp_stronglyMeasurable hv.stronglyMeasurable
  · simp_rw [limG_sub]
    exact continuous_gramOfEntries.comp (continuous_pi fun e => continuous_extPath _ ω)
  · simp_rw [limK_sub]
    exact continuous_matrix fun i j => continuous_extPath _ ω

/-! ## Reading the observables from the coordinates -/

/-- The test time of a label: `0` for entrance coordinates (constant in time). -/
def readT : LIdx K np → ℝ≥0 → ℝ
  | Sum.inl _ => fun u => u
  | Sum.inr (Sum.inl _) => fun _ => 0
  | Sum.inr (Sum.inr _) => fun u => u

theorem readT_nonneg (l : LIdx K np) (u : ℝ≥0) : 0 ≤ readT l u := by
  rcases l with e | k | ij
  · exact u.2
  · exact le_rfl
  · exact u.2

/-- From a coordinate to an observable: add the limit jump (Gram, `𝒦`), take the real part
(entrance). -/
def adjust (b E s : ℝ) (τ m : Fin np → ℝ) : LIdx K np → ℝ≥0 → ℂ → ℂ
  | Sum.inl e => fun u z => z + limJ (K := K) b E s τ m (Sum.inl e) u
  | Sum.inr (Sum.inl _) => fun _ z => (z.re : ℂ)
  | Sum.inr (Sum.inr ij) => fun u z => z + limJ (K := K) b E s τ m (Sum.inr (Sum.inr ij)) u

theorem continuous_adjust (b E s : ℝ) (τ m : Fin np → ℝ) (l : LIdx K np) (u : ℝ≥0) :
    Continuous (adjust b E s τ m l u) := by
  rcases l with e | k | ij
  · exact continuous_id.add continuous_const
  · exact Complex.continuous_ofReal.comp Complex.continuous_re
  · exact continuous_id.add continuous_const

/-- **Finite `W`**: once the jumps agree, the read coordinate is the observable. -/
theorem adjust_fddCoord {b E s h : ℝ} {τ m : Fin np → ℝ} {W : ℕ}
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} (l : LIdx K np) (u : ℝ≥0)
    (hJ : jumpAll b E s τ m W l u = limJ b E s τ m l u) (y : ProbedPath W np × ℝ) :
    adjust b E s τ m l u (fddCoord b E s h τ m W Vs l (readT l u) y) =
      b3ObsAll b E s h τ m W Vs l u y := by
  rcases l with e | k | ij
  · change fddCoord b E s h τ m W Vs (Sum.inl e) u y + limJ b E s τ m (Sum.inl e) u = _
    rw [fddCoord_eq, hJ, sub_add_cancel]
  · change ((((physTseq b E s W y.1.1 k : ℝ) : ℂ).re : ℝ) : ℂ) = _
    rw [Complex.ofReal_re]; rfl
  · change fddCoord b E s h τ m W Vs (Sum.inr (Sum.inr ij)) u y +
      limJ b E s τ m (Sum.inr (Sum.inr ij)) u = _
    rw [fddCoord_eq, hJ, sub_add_cancel]

/-- **The limit**: the read coordinate is the candidate's observable. -/
theorem adjust_extPath (b E s : ℝ) (τ m : Fin np → ℝ) (l : LIdx K np) (u : ℝ≥0)
    (ω : ℕ → ℂ) :
    adjust b E s τ m l u (extPath 0 (Encodable.encode l) ω (readT l u)) =
      complexObs (limT (np := np) K) (limG b E s τ m) (limK K b E s τ m) l u ω := by
  rcases l with e | k | ij
  · change limY b E s τ m (Sum.inl e) u ω = gramEntry e (limG b E s τ m u ω)
    rw [limG, gramEntry_gramOfEntries]
  · rfl
  · rfl

/-! ## The target -/

/-- **`TargetCapFddAll` holds.** -/
theorem targetCapFddAll_holds : TargetCapFddAll := by
  intro hTL hS _ _ hL b E np τ m T s h K Vs hD Ω mΩ P μ hlim hA hne φ hφ
  obtain ⟨⟨hb0, hb, hE1, hE2, -, -, -, -⟩, hs, hsτ, hh0, -, hVs⟩ := id hD
  have hb1 : b < 1 := by linarith
  have := hlim.prob
  have := CapCond.isFiniteMeasure_entranceLaw P μ s
  set mc := (entranceLaw P μ s (capSet K h)).toReal
  have hmc : 0 < mc := ENNReal.toReal_pos hne (measure_ne_top _ _)
  have hc : 0 < mc / 2 := half_pos hmc
  have hcapE : ∀ᶠ W in atTop,
      ENNReal.ofReal (mc / 2) ≤ growthPathLaw W b (physCapEventC b E s h K W) := by
    filter_upwards [(CapCond.tendsto_capProb hTL hb0 hb hE1 hE2 hlim hs hh0 K (hA K)).eventually
      (lt_mem_nhds (half_lt_self hmc))] with W hW
    exact ENNReal.ofReal_le_of_le_toReal hW.le
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hφ.eventually (hVs.and hcapE))
  set Wn : ℕ → ℕ := fun n => φ (n + N₀)
  have hWn : Tendsto Wn atTop atTop := hφ.comp (tendsto_add_atTop_nat N₀)
  have hgood : ∀ n, IsTimeSFrame b E s h K (Wn n) (Vs (Wn n)) ∧
      ENNReal.ofReal (mc / 2) ≤ growthPathLaw (Wn n) b (physCapEventC b E s h K (Wn n)) :=
    fun n => hN₀ (n + N₀) (Nat.le_add_left _ _)
  have hprob : ∀ n, IsProbabilityMeasure (condL b E s h K (Wn n) np) := fun n =>
    isProbabilityMeasure_condL hb1 hE1 hE2
      (ne_of_gt (lt_of_lt_of_le (ENNReal.ofReal_pos.2 hc) (hgood n).2))
  set X := fddProc b E s h τ m Wn Vs
  have hX : AEMeas 0 (fun n => condL b E s h K (Wn n) np) X := by
    intro n a t ht
    cases hd : Encodable.decode (α := LIdx K np) a with
    | none =>
        rw [show X n a t = 0 from fddProc_none b E s h τ m Wn Vs hd t]
        exact aemeasurable_const
    | some l =>
        rw [show X n a t = _ from fddProc_some b E s h τ m Wn Vs hd t]
        exact (measurable_fddCoord (hgood n).1.1 l ht).aemeasurable
  have hT : OneTimeTight 0 (fun n => condL b E s h K (Wn n) np) X := by
    intro a t ht θ hθ
    cases hd : Encodable.decode (α := LIdx K np) a with
    | none =>
        refine ⟨0, 0, fun n _ => ?_⟩
        rw [show X n a t = 0 from fddProc_none b E s h τ m Wn Vs hd t]
        simp
    | some l =>
        obtain ⟨C, W₀, hW₀⟩ := fdd_tight hS hL hD l ht (mul_pos hc hθ)
        obtain ⟨N, hN⟩ := eventually_atTop.1 (hWn.eventually (eventually_ge_atTop W₀))
        refine ⟨C, N, fun n hn => ?_⟩
        rw [show X n a t = _ from fddProc_some b E s h τ m Wn Vs hd t]
        exact condL_le hb1 hE1 hE2 hc (hgood n).2 (hW₀ _ (hN n hn))
  have hM : Modulus 0 (fun n => condL b E s h K (Wn n) np) X := by
    intro a T' η θ hη hθ
    cases hd : Encodable.decode (α := LIdx K np) a with
    | none =>
        refine ⟨1, one_pos, 0, fun n _ => ?_⟩
        simp only [show ∀ t, X n a t = 0 from fun t => fddProc_none b E s h τ m Wn Vs hd t,
          Pi.zero_apply, sub_self, norm_zero, not_lt.2 hη.le, and_false, exists_false,
          Set.ofPred_false, measure_empty]
        exact zero_le
    | some l =>
        obtain ⟨δ, hδ, W₀, hW₀⟩ := fdd_modulus hS hL hD l T' hη (mul_pos hc hθ)
        obtain ⟨N, hN⟩ := eventually_atTop.1 (hWn.eventually (eventually_ge_atTop W₀))
        refine ⟨δ, hδ, N, fun n hn => ?_⟩
        simp only [show ∀ t, X n a t = _ from fun t => fddProc_some b E s h τ m Wn Vs hd t]
        exact condL_le hb1 hE1 hE2 hc (hgood n).2 (hW₀ _ (hN n hn))
  obtain ⟨ms, hms, Q, hQ, hmeas, -, hfdd⟩ := exists_limit hX hT hM
  refine ⟨fun n => ms n + N₀, fun a b hab => Nat.add_lt_add_right (hms hab) N₀, ℕ → ℂ,
    inferInstance, Q, limT K, limG b E s τ m, limK K b E s τ m,
    isCapLimitData_lim b E s τ m hQ hmeas, ?_⟩
  intro ι _ i u hu ψ
  set e := Fintype.equivFin ι
  set as : Fin (Fintype.card ι) → ℕ := fun j => Encodable.encode (i (e.symm j))
  set τ' : Fin (Fintype.card ι) → ℝ := fun j => readT (i (e.symm j)) (u (e.symm j))
  set Φ : BoundedContinuousFunction (Fin (Fintype.card ι) → ℂ) ℝ :=
    ψ.compContinuous ⟨fun x l => adjust b E s τ m (i l) (u l) (x (e l)),
      continuous_pi fun l => (continuous_adjust b E s τ m (i l) (u l)).comp (continuous_apply _)⟩
  have h1 := hfdd _ as τ' (fun j => readT_nonneg _ _) Φ
  have eR : ∫ ω, Φ (fun j => extPath 0 (as j) ω (τ' j)) ∂Q =
      ∫ ω, ψ (fun l => complexObs (limT (np := np) K) (limG b E s τ m) (limK K b E s τ m) (i l)
        (u l) ω) ∂Q := by
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [Φ, as, τ', BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk,
      Equiv.symm_apply_apply, adjust_extPath]
  rw [eR] at h1
  have hJ : ∀ᶠ n in atTop, ∀ l : ι, ∀ l' : LIdx K np,
      jumpAll b E s τ m (Wn (ms n)) l' (u l) = limJ b E s τ m l' (u l) :=
    (hWn.comp hms.tendsto_atTop).eventually
      (eventually_all.2 fun l => eventually_jumpAll_eq hs.le hsτ (hu l))
  refine h1.congr' (hJ.mono fun n hn => ?_)
  change ∫ y, Φ (fun j => X (ms n) (as j) (τ' j) y) ∂condL b E s h K (Wn (ms n)) np =
    condObsTestAll b E s h τ m (Wn (ms n)) (Vs (Wn (ms n))) i u ψ
  rw [condObsTestAll_eq hb1 hE1 hE2 s h τ m]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [Φ, as, τ', BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk,
    Equiv.symm_apply_apply, X, fddProc_encode]
  congr 1
  funext l
  exact adjust_fddCoord (i l) (u l) (hn l (i l)) y

/-! ## The capped form -/

theorem limLen_eq_all {s T : ℝ} (W : ℕ) {u : ℝ≥0} (hu : s + (u : ℝ) ≤ max s T) :
    limLen s T W u = limLenAll s W u :=
  min_eq_left (Nat.floor_mono (mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg W)))

theorem b3Obs_eq_all (b E s T h : ℝ) (τ m : Fin np → ℝ) (W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (l : LIdx K np) {u : ℝ≥0}
    (hu : s + (u : ℝ) ≤ max s T) :
    b3Obs b E s T h τ m W Vs l u = b3ObsAll b E s h τ m W Vs l u := by
  rcases l with e | k | ij
  · funext y; simp only [b3Obs, b3ObsAll, limLen_eq_all W hu]
  · rfl
  · funext y; simp only [b3Obs, b3ObsAll, limLen_eq_all W hu]

/-- **The all-time form gives the capped form** (restrict `u` to `s + u ≤ max(s, T)`). -/
theorem complexCapFdd_of_all (hAll : ComplexCapFddAll) : ComplexCapFdd := by
  intro b E np τ m T s h K Vs hD Ω mΩ P μ hlim hA hne φ hφ
  obtain ⟨ψ, hψ, Ω', mΩ', Q, tseq, G, Kc, hdat, hfdd⟩ :=
    hAll b E np τ m T s h K Vs hD Ω mΩ P μ hlim hA hne φ hφ
  refine ⟨ψ, hψ, Ω', mΩ', Q, tseq, G, Kc, hdat, fun ι _ i u hu hb ψf => ?_⟩
  have e : ∀ n, condObsTest b E s T h τ m (φ (ψ n)) (Vs (φ (ψ n))) i u ψf =
      condObsTestAll b E s h τ m (φ (ψ n)) (Vs (φ (ψ n))) i u ψf := fun n => by
    unfold condObsTest condObsTestAll
    simp only [b3Obs_eq_all b E s T h τ m _ _ _ (hu _)]
  simp only [e]
  exact hfdd ι i u hb ψf

/-- **`TargetCapFdd` holds** (from `TargetCapFddAll`). -/
theorem targetCapFdd_holds : TargetCapFdd :=
  fun hTL hS hT hK hL => complexCapFdd_of_all (targetCapFddAll_holds hTL hS hT hK hL)

end BlockBand.SourceProcess.PhysApprox.B3.Fdd
