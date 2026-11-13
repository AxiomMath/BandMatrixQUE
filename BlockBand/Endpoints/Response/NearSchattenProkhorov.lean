module

public import BlockBand.Endpoints.Response.NearSchattenExist
public import BlockBand.Endpoints.Response.NearSchattenProkhorovFdd
public import BlockBand.Endpoints.Response.TaggedConvexOrderWitnessStop
public import BlockBand.Endpoints.Response.TaggedConvexOrderMoments
public import BlockBand.Endpoints.Response.NearSchattenUpper

/-!
# Prokhorov realization and existence of critical clock limits

This file proves `NsProkhorovRealization` and, from the tightness clause of
`FullSourceGeneratorContract`, `NsCriticalClockLimitsExist`.

* `nsp_countable_clockWord`: the clock words form a countable type.
* `nsProkhorovRealization_holds : NsProkhorovRealization`: the realization `nsp_realization`
  applied to the index type of ordinary clock words, the sequence `n ↦ growthPathLaw (ψ n) b` and
  the step processes `t ↦ wordValue … ⌊ψ n · t⌋₊`; the hypotheses are read off `NsClockCTight`.
* `nsCriticalClockLimitsExist_of_contracts (hGen) : NsCriticalClockLimitsExist`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Endpoints
open scoped Matrix

/-!
## Finite-width measurability of word values
-/

theorem nsp_measurable_matMul {α : Type*} [MeasurableSpace α] {W : ℕ}
    {f g : α → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a => f a * g a := by
  refine Measurable.of_eval fun x => Measurable.of_eval fun y => ?_
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun z _ =>
    ((measurable_pi_apply z).comp ((measurable_pi_apply x).comp hf)).mul
      ((measurable_pi_apply y).comp ((measurable_pi_apply z).comp hg))

theorem nsp_measurable_intervalSource (b E : ℝ) (W j : ℕ) (q : ℝ → ℝ) :
    Measurable (fun ω : GrowthPath W => intervalSource b E W j q ω) := by
  refine Measurable.of_eval fun x => Measurable.of_eval fun y => ?_
  simp only [intervalSource, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact Finset.measurable_sum _ fun k _ => measurable_const.mul
    ((measurable_pi_apply y).comp ((measurable_pi_apply x).comp
      (ns_measurable_tagResponse b E W j k)))

theorem nsp_measurable_letterMatrix (b E : ℝ) {nT nI : ℕ} (k : Fin nT → ℕ)
    (q : Fin nI → ℝ → ℝ) (W j : ℕ) (a : TraceLetter nT nI) :
    Measurable (fun ω : GrowthPath W => letterMatrix b E k q W j ω a) := by
  cases a with
  | current => exact tcw_measurable_pathCurrent b E W j
  | tag a =>
    exact (continuous_const_smul ((W : ℂ)⁻¹)).measurable.comp
      (ns_measurable_tagResponse b E W j (k a))
  | interval a => exact nsp_measurable_intervalSource b E W j (q a)

theorem nsp_measurable_separatorMatrix (b E : ℝ) (W j : ℕ) (s : Separator) :
    Measurable (fun ω : GrowthPath W => separatorMatrix b E W j ω s) := by
  have hS := tcw_measurable_scattering b E W j
  have hSs : Measurable (fun ω : GrowthPath W => (scatteringMatrix b E W j ω)ᴴ) :=
    continuous_id.matrix_conjTranspose.measurable.comp hS
  cases s with
  | id => exact measurable_const
  | proj => exact measurable_const
  | projS => exact nsp_measurable_matMul measurable_const hS
  | sStarProj => exact nsp_measurable_matMul hSs measurable_const
  | projSProj =>
    exact nsp_measurable_matMul (nsp_measurable_matMul measurable_const hS) measurable_const
  | projSStarProj =>
    exact nsp_measurable_matMul (nsp_measurable_matMul measurable_const hSs) measurable_const

/-- **Finite-width measurability of word values**, for every trace word. -/
theorem nsp_measurable_wordValue (b E : ℝ) {nT nI : ℕ} (k : Fin nT → ℕ)
    (q : Fin nI → ℝ → ℝ) (W j : ℕ) (w : TraceWord nT nI) :
    Measurable (fun ω : GrowthPath W => wordValue b E k q W j ω w) := by
  have hprod : ∀ l : TraceWord nT nI, Measurable (fun ω : GrowthPath W =>
      (l.map fun x => letterMatrix b E k q W j ω x.1 * separatorMatrix b E W j ω x.2).prod) := by
    intro l
    induction l with
    | nil => exact measurable_const
    | cons a l ih =>
      simp only [List.map_cons, List.prod_cons]
      exact nsp_measurable_matMul (nsp_measurable_matMul
        (nsp_measurable_letterMatrix b E k q W j a.1) (nsp_measurable_separatorMatrix b E W j a.2))
        ih
  exact (continuous_id.matrix_trace).measurable.comp (hprod w)

/-!
## Countability of the clock words
-/

theorem nsp_countable_traceLetter (nT nI : ℕ) : Countable (TraceLetter nT nI) := by
  let f : TraceLetter nT nI → Option (Fin nT ⊕ Fin nI) := fun x =>
    match x with
    | .current => none
    | .tag a => some (Sum.inl a)
    | .interval a => some (Sum.inr a)
  refine Function.Injective.countable (f := f) ?_
  intro x y h
  cases x <;> cases y <;> simp_all [f]

theorem nsp_countable_separator : Countable Separator := by
  let f : Separator → ℕ := fun s =>
    match s with
    | .id => 0
    | .proj => 1
    | .projS => 2
    | .sStarProj => 3
    | .projSProj => 4
    | .projSStarProj => 5
  refine Function.Injective.countable (f := f) ?_
  intro x y h
  cases x <;> cases y <;> simp_all [f]

theorem nsp_countable_clockWord : Countable ClockWord := by
  have := nsp_countable_traceLetter 0 1
  have := nsp_countable_separator
  infer_instance

/-!
## The realization
-/

/-- **`NsProkhorovRealization` holds**: the Prokhorov realization of subsequential limits for
the one-source clock family.
-/
theorem nsProkhorovRealization_holds : NsProkhorovRealization := by
  classical
  intro b _ _ E _ _ t₁ R q _ _ hCT ψ hψ
  have := nsp_countable_clockWord
  let X : ∀ n, {w : ClockWord // IsOrdinaryWord w} → ℝ → GrowthPath (ψ n) → ℂ :=
    fun n i t ω => wordValue b E (noTags (ψ n)) (fun _ => q) (ψ n) ⌊(ψ n : ℝ) * t⌋₊ ω i.1
  have : ∀ n, IsProbabilityMeasure (growthPathLaw (ψ n) b) := fun n =>
    tco_isProbabilityMeasure_growthPathLaw _ _
  have hX : ∀ n i t, Measurable (X n i t) := fun n i t =>
    nsp_measurable_wordValue b E _ _ _ _ i.1
  have hT : NspTightAt (t₁ + R) (fun n => growthPathLaw (ψ n) b) X := by
    intro i t ht θ hθ
    obtain ⟨M, W₀, h⟩ := (hCT i.1 i.2 t (t + 1) ht (by linarith)).1 θ hθ
    exact ⟨M, W₀, fun n hn => h (ψ n) (hn.trans (hψ.id_le n))⟩
  have hC : NspModulus (t₁ + R) (fun n => growthPathLaw (ψ n) b) X := by
    intro i T hT η θ hη hθ
    obtain ⟨δ, hδ, W₀, h⟩ := (hCT i.1 i.2 (t₁ + R) T le_rfl hT).2 η θ hη hθ
    exact ⟨δ, hδ, W₀, fun n hn => h (ψ n) (hn.trans (hψ.id_le n))⟩
  obtain ⟨φ, hφ, ν, hν, hmeas, hcont, hfdd⟩ :=
    nsp_realization (Ω := fun n => GrowthPath (ψ n)) hX hT hC
  let Z : ClockWord → ℝ → ({w : ClockWord // IsOrdinaryWord w} × ℕ × ℕ → ℂ) → ℂ :=
    fun w t x => if h : IsOrdinaryWord w then nspZ (t₁ + R) (⟨w, h⟩ : {w // IsOrdinaryWord w}) t x
      else 0
  have hZ : ∀ w (hw : IsOrdinaryWord w) t, Z w t = nspZ (t₁ + R) ⟨w, hw⟩ t := fun w hw t =>
    funext fun x => by simp only [Z, hw, ↓reduceDIte]
  have hfdd' : NsFddAlong b E q (t₁ + R) ν Z (ψ ∘ φ) := by
    intro m ws ts hws Ψ
    have e : (fun x => Ψ (fun l => Z (ws l) (ts l) x)) =
        fun x => Ψ (fun l => nspZ (t₁ + R) (⟨ws l, (hws l).1⟩ : {w // IsOrdinaryWord w})
          (ts l) x) :=
      funext fun x => congrArg Ψ (funext fun l => congrFun (hZ (ws l) (hws l).1 (ts l)) x)
    rw [e]
    exact hfdd m (fun l => ⟨ws l, (hws l).1⟩) ts (fun l => (hws l).2) Ψ
  refine ⟨φ, hφ, _, inferInstance, ν, Z, ⟨hν, fun w hw t _ => ?_, fun w hw => ?_,
    ⟨ψ ∘ φ, hψ.comp hφ, hfdd'⟩⟩, hfdd'⟩
  · rw [hZ w hw t]; exact hmeas _ t
  · filter_upwards [hcont ⟨w, hw⟩] with x hx
    exact hx.congr fun t _ => congrFun (hZ w hw t) x

/-- **`NsCriticalClockLimitsExist`** from the `FullSourceGeneratorContract` alone (its
`tight` clause), the Prokhorov realization and the Hausdorff moment theorem (both proved).
-/
theorem nsCriticalClockLimitsExist_of_contracts (hGen : FullSourceGeneratorContract) :
    NsCriticalClockLimitsExist :=
  nsCriticalClockLimitsExist_holds hGen nsProkhorovRealization_holds

end BlockBand.Endpoints
