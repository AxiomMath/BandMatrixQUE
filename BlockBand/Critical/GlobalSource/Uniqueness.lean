module

public import BlockBand.Critical.GlobalSource.Statement

/-!
# Global Gaussian source: uniqueness and well-posedness of the limit object

Facts about `IsGlobalProbeLaw` used by any proof of `GlobalGaussianSourceStatement`:

* `isComplexSourceLimit_unique`: the critical limit `IsComplexSourceLimit` determines its law
  (weak limits are unique);
* `isGlobalProbeLaw_unique`: at most one `κ` satisfies `IsGlobalProbeLaw`;
* `exists_isSampledSourceFamily`: from `ComplexSourceLawContract.limit`, a sampled
  finite-source family exists (the existence clause of `IsGlobalProbeLaw`);
* `ae_isAdmissibleBirthTimes`: sampled birth times are almost surely positive, distinct and
  `< τ`;
* `sampledProbeValue_congr`: the `M`-sampled value does not depend on the choice of the sampled
  family (so "for every family" in `IsGlobalProbeLaw` is not stronger than "for one family");
* `isGlobalProbeLaw_of_one_family`: hence convergence for one family suffices;
* `globalGaussianSourceStatement_iff`: the `∃!` of the statement is equivalent to `∃`.

Only `exists_isSampledSourceFamily` uses a hypothesis (`ComplexSourceLawContract`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.GlobalSource

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.CriticalEntire

/-!
## Topological measure instances (local)
-/

/-- Square complex matrices (product topology) have outer approximations of closed sets. -/
theorem matrix_hasOuterApproxClosed (J : ℕ) : HasOuterApproxClosed (Matrix (Fin J) (Fin J) ℂ) :=
  inferInstanceAs (HasOuterApproxClosed (Fin J → Fin J → ℂ))

/-- The source data space has outer approximations of closed sets. -/
theorem sourceData_hasOuterApproxClosed (np : ℕ) : HasOuterApproxClosed (SourceData np) :=
  inferInstanceAs (HasOuterApproxClosed (Fin 4 → Fin np → Fin np → ℂ))

/-- The source data space carries its Borel σ-algebra. -/
theorem sourceData_borelSpace (np : ℕ) : BorelSpace (SourceData np) :=
  inferInstanceAs (BorelSpace (Fin 4 → Fin np → Fin np → ℂ))

attribute [local instance] matrix_hasOuterApproxClosed sourceData_hasOuterApproxClosed
  sourceData_borelSpace

/-!
## Uniqueness of the limit laws
-/

/-- The critical limit determines its law: two probability measures that are weak limits of the same
finite-width source-data laws (`IsComplexSourceLimit`) coincide. -/
theorem isComplexSourceLimit_unique {b E T : ℝ} {np : ℕ} {τ m : Fin np → ℝ}
    {ν ν' : Measure (SourceData np)} (h : IsComplexSourceLimit b E T τ m ν)
    (h' : IsComplexSourceLimit b E T τ m ν') : ν = ν' := by
  have := h.1
  have := h'.1
  exact ext_of_forall_integral_eq_of_IsFiniteMeasure fun Φ =>
    tendsto_nhds_unique (h.2 Φ) (h'.2 Φ)

/-- **Uniqueness of the global source law**: at most one law `κ` of the complex `J×J` matrix
satisfies `IsGlobalProbeLaw`. Measure: Borel probability measures on `Matrix (Fin J) (Fin J) ℂ`
(product topology). No hypothesis on `b, E, τ, Q`. -/
theorem isGlobalProbeLaw_unique {b E τ : ℝ} {J : ℕ} {Q : Fin J → C(Torus, ℝ)}
    {κ κ' : Measure (Matrix (Fin J) (Fin J) ℂ)} (h : IsGlobalProbeLaw b E τ Q κ)
    (h' : IsGlobalProbeLaw b E τ Q κ') : κ = κ' := by
  obtain ⟨hκ, ⟨ν, hν⟩, hlim⟩ := h
  obtain ⟨hκ', -, hlim'⟩ := h'
  have := hκ
  have := hκ'
  exact ext_of_forall_integral_eq_of_IsFiniteMeasure fun Φ =>
    tendsto_nhds_unique (hlim ν hν Φ) (hlim' ν hν Φ)

/-- **The statement's `∃!` is equivalent to `∃`**, by `isGlobalProbeLaw_unique`. -/
theorem globalGaussianSourceStatement_iff :
    GlobalGaussianSourceStatement ↔
      ∀ (b E : ℝ), 0 < b → b < 1 / 2 → -2 < E ∧ E < 2 →
        ∀ (τ : PositiveRatio) (J : ℕ) (Q : Fin J → C(Torus, ℝ)), (∀ a x, 0 ≤ Q a x) →
          ∃ κ : Measure (Matrix (Fin J) (Fin J) ℂ),
            IsGlobalProbeLaw b E τ.1 Q κ ∧ IsGlobalProbeCriticalLimit b E τ.1 Q κ := by
  constructor
  · intro h b E hb hb' hE τ J Q hQ
    exact (h b E hb hb' hE τ J Q hQ).exists
  · intro h b E hb hb' hE τ J Q hQ
    obtain ⟨κ, hκ⟩ := h b E hb hb' hE τ J Q hQ
    exact ⟨κ, hκ, fun κ' hκ' => isGlobalProbeLaw_unique hκ'.1 hκ.1⟩

/-!
## Existence of the sampled source family
-/

/-- Probe masses `m_a = τ ∫_𝕋 q_a` are nonnegative for nonnegative profiles and `τ ≥ 0`. -/
theorem probeMass_nonneg {τ : ℝ} (hτ : 0 ≤ τ) {Q : C(Torus, ℝ)} (hQ : ∀ x, 0 ≤ Q x) :
    0 ≤ probeMass τ Q :=
  mul_nonneg hτ (integral_nonneg hQ)

/-- **Existence of the sampled finite-source family** (the complex finite-source equation run with a
mass-`m_a` Gaussian tag at each sampled time), from `ComplexSourceLawContract.limit` at terminal
time `τ`. Domain: `0 < b < 1/2`, `-2 < E < 2`, `τ ≥ 0`, nonnegative profiles. For non-admissible
times the family is the zero measure; `IsSampledSourceFamily` constrains admissible times only, and
they have full measure (`ae_isAdmissibleBirthTimes`). -/
theorem exists_isSampledSourceFamily (hL5 : ComplexSourceLawContract) {b E τ : ℝ}
    (hb : 0 < b) (hb' : b < 1 / 2) (hE : -2 < E ∧ E < 2) (hτ : 0 ≤ τ) {J : ℕ}
    {Q : Fin J → C(Torus, ℝ)} (hQ : ∀ a x, 0 ≤ Q a x) :
    ∃ ν, IsSampledSourceFamily b E τ Q ν := by
  classical
  refine ⟨fun M t => if h : IsAdmissibleBirthTimes τ t then
      Classical.choose (hL5.limit b hb hb' E hE.1 hE.2 (J * M) t (tagMasses τ Q M) h.1 h.2.1
        (fun i => probeMass_nonneg hτ (hQ _)) τ h.2.2) else 0, ?_⟩
  intro M t ht
  simp only [ht, ↓reduceDIte]
  exact (Classical.choose_spec (hL5.limit b hb hb' E hE.1 hE.2 (J * M) t (tagMasses τ Q M)
    ht.1 ht.2.1 (fun i => probeMass_nonneg hτ (hQ _)) τ ht.2.2)).1

/-!
## Sampled birth times are almost surely admissible
-/

/-- A sampled birth time lies in `(0, τ)` almost surely: the birth law is absolutely continuous
with respect to Lebesgue measure on `[0, τ]`. -/
theorem probeBirthLaw_compl_Ioo (τ : ℝ) (Q : C(Torus, ℝ)) :
    probeBirthLaw τ Q (Set.Ioo 0 τ)ᶜ = 0 := by
  apply withDensity_absolutelyContinuous
  rw [Measure.restrict_apply' measurableSet_Icc]
  refine measure_mono_null (t := ({0, τ} : Set ℝ)) ?_ ((Set.toFinite _).measure_zero _)
  intro x hx
  obtain ⟨hx1, hx2⟩ := hx
  simp only [Set.mem_compl_iff, Set.mem_Ioo, not_and_or, not_lt] at hx1
  simp only [Set.mem_Icc] at hx2
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases hx1 with h | h
  · left; linarith
  · right; linarith

/-- A sampled birth law has no atoms. -/
theorem probeBirthLaw_singleton (τ : ℝ) (Q : C(Torus, ℝ)) (x : ℝ) :
    probeBirthLaw τ Q {x} = 0 := by
  apply withDensity_absolutelyContinuous
  exact Measure.absolutelyContinuous_of_le Measure.restrict_le_self (by simp)

/-- Finitely many independent coordinates with atomless σ-finite laws on `ℝ` are almost surely
distinct. -/
theorem ae_injective_pi {N : ℕ} (μ : Fin N → Measure ℝ) [∀ i, SigmaFinite (μ i)]
    (hμ : ∀ i (x : ℝ), μ i {x} = 0) : ∀ᵐ t ∂Measure.pi μ, Function.Injective t := by
  have key : ∀ i j : Fin N, i ≠ j → ∀ᵐ t ∂Measure.pi μ, t i ≠ t j := by
    intro i j hij
    cases N with
    | zero => exact i.elim0
    | succ n =>
      obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq hij.symm
      have hpres := measurePreserving_piFinSuccAbove μ i
      set S : Set (ℝ × (Fin n → ℝ)) := {p | p.1 = p.2 j'} with hS
      have hSm : MeasurableSet S :=
        measurableSet_eq_fun measurable_fst ((measurable_pi_apply j').comp measurable_snd)
      have hpre : {t : Fin (n + 1) → ℝ | t i = t j} =
          MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i ⁻¹' S := by
        ext t
        simp [hS, MeasurableEquiv.piFinSuccAbove_apply, Fin.removeNth, ← hj']
      rw [ae_iff]
      simp only [ne_eq, not_not]
      rw [hpre, hpres.measure_preimage hSm.nullMeasurableSet,
        Measure.prod_apply_symm hSm]
      have : ∀ y : Fin n → ℝ, μ i ((fun x => (x, y)) ⁻¹' S) = 0 := by
        intro y
        have : (fun x => (x, y)) ⁻¹' S = {y j'} := by
          ext x; simp [hS]
        rw [this, hμ]
      simp [this]
  have hall : ∀ᵐ t ∂Measure.pi μ, ∀ i j : Fin N, i ≠ j → t i ≠ t j := by
    rw [ae_all_iff]; intro i
    rw [ae_all_iff]; intro j
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ h => absurd hij h
    · filter_upwards [key i j hij] with t ht using fun _ => ht
  filter_upwards [hall] with t ht
  intro i j hij
  by_contra h
  exact ht i j h hij

/-- The sampled birth laws are σ-finite (finite). -/
instance probeBirthLaw_sigmaFinite (τ : ℝ) (Q : C(Torus, ℝ)) : SigmaFinite (probeBirthLaw τ Q) := by
  unfold probeBirthLaw
  infer_instance

/-- **Sampled times are almost surely admissible**: under `sampledBirthLaw τ Q M`, the `J·M` times
are a.s. distinct, positive and `< τ`, that is, in the domain of `ComplexSourceLawContract.limit`. -/
theorem ae_isAdmissibleBirthTimes (τ : ℝ) {J : ℕ} (Q : Fin J → C(Torus, ℝ)) (M : ℕ) :
    ∀ᵐ t ∂sampledBirthLaw τ Q M, IsAdmissibleBirthTimes τ t := by
  have hinj := ae_injective_pi (fun i : Fin (J * M) => probeBirthLaw τ (Q (tagGroup i)))
    (fun i x => probeBirthLaw_singleton τ _ x)
  have hcoord : ∀ᵐ t ∂sampledBirthLaw τ Q M, ∀ i, t i ∈ Set.Ioo 0 τ := by
    rw [ae_all_iff]
    intro i
    refine (Measure.tendsto_eval_ae_ae (μ := fun i : Fin (J * M) =>
      probeBirthLaw τ (Q (tagGroup i))) (i := i)).eventually ?_
    rw [ae_iff]
    simpa [Set.compl_def] using probeBirthLaw_compl_Ioo τ (Q (tagGroup i))
  filter_upwards [hinj, hcoord] with t ht1 ht2
  exact ⟨ht1, fun i => (ht2 i).1, fun i => (ht2 i).2⟩

/-- **The sampled value does not depend on the sampled family**: for two families satisfying
`IsSampledSourceFamily`, the `M`-sampled grouped values agree for every bounded continuous test,
because both families coincide at almost every sampled time (`isComplexSourceLimit_unique`,
`ae_isAdmissibleBirthTimes`). -/
theorem sampledProbeValue_congr {b E τ : ℝ} {J : ℕ} {Q : Fin J → C(Torus, ℝ)}
    {ν ν' : ∀ M : ℕ, (Fin (J * M) → ℝ) → Measure (SourceData (J * M))}
    (h : IsSampledSourceFamily b E τ Q ν) (h' : IsSampledSourceFamily b E τ Q ν') (M : ℕ)
    (Φ : BoundedContinuousFunction (Matrix (Fin J) (Fin J) ℂ) ℝ) :
    sampledProbeValue τ Q M (ν M) Φ = sampledProbeValue τ Q M (ν' M) Φ := by
  unfold sampledProbeValue
  refine integral_congr_ae ?_
  filter_upwards [ae_isAdmissibleBirthTimes τ Q M] with t ht
  rw [isComplexSourceLimit_unique (h M t ht) (h' M t ht)]

/-- **One family suffices**: if a probability measure `κ` is the `M → ∞` limit of the sampled values
of one sampled family, then `κ` satisfies `IsGlobalProbeLaw`. -/
theorem isGlobalProbeLaw_of_one_family {b E τ : ℝ} {J : ℕ} {Q : Fin J → C(Torus, ℝ)}
    {κ : Measure (Matrix (Fin J) (Fin J) ℂ)} [IsProbabilityMeasure κ]
    {ν : ∀ M : ℕ, (Fin (J * M) → ℝ) → Measure (SourceData (J * M))}
    (hν : IsSampledSourceFamily b E τ Q ν)
    (hlim : ∀ Φ : BoundedContinuousFunction (Matrix (Fin J) (Fin J) ℂ) ℝ,
      Tendsto (fun M => sampledProbeValue τ Q M (ν M) Φ) atTop (𝓝 (∫ K, Φ K ∂κ))) :
    IsGlobalProbeLaw b E τ Q κ := by
  refine ⟨inferInstance, ⟨ν, hν⟩, fun ν' hν' Φ => ?_⟩
  have : (fun M => sampledProbeValue τ Q M (ν' M) Φ) =
      fun M => sampledProbeValue τ Q M (ν M) Φ :=
    funext fun M => sampledProbeValue_congr hν' hν M Φ
  rw [this]
  exact hlim Φ

/-- The profiles of `probeProfile` (one probe `Σ_a y_a q_a` per factor) are nonnegative for
nonnegative `q` and `y`, so they lie in the domain of `GlobalGaussianSourceStatement` (used for
`EntireLawContract.characterization`). -/
theorem probeProfile_nonneg {k J : ℕ} {q : Fin k → C(Torus, ℝ)} (hq : IsProfileFamily q)
    {y : Fin J → Fin (k + 1) → ℝ} (hy : ∀ j a, 0 ≤ y j a) :
    ∀ j x, 0 ≤ probeProfile q y j x := by
  intro j x
  simp only [probeProfile, ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_nonneg fun a _ => mul_nonneg (hy j a) ?_
  refine Fin.cases ?_ (fun i => ?_) a
  · simp [fullProfile]
  · simpa [fullProfile] using hq i x

end BlockBand.Critical.GlobalSource
