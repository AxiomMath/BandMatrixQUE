module

public import BlockBand.SourceProcess.PhysApprox.B3IdentGramGen
public import BlockBand.SourceProcess.PhysApprox.B3FddCoord
public import BlockBand.SourceProcess.PhysApprox.B3FeasBridge
public import BlockBand.SourceProcess.PhysApprox.B3StopTailMain

/-!
# The prelimit generator processes and the local Gram estimate

Measure: `closedLaw b W np` (unconditioned; the cap event is an indicator). Filtration: none is
needed for the statements here.

* `sm_primitive`, `sm_genProc`: a generator process `genProc` of a jointly strongly measurable
  Gram process is jointly strongly measurable (primitives of jointly measurable integrands).
* `exists_uniform_bound`: **the bound `C_H`**, uniform over all feasible paths. It
  depends on the cutoff, `F`, `Λ`, `b, E, s, τ, m` and the horizon only (not on `W`, `R`, `Ω`).
* `cellT s W a t j = max a (min t (j/W − s))`: the grid of `[a, t]` by the cells of the closed
  lengths; `pStopSum`: the tested increments summed over the cells `j` of `[a, t]`, each on the
  alive set `b3Alive … R W j` (cap event and trace `< R` up to `j`, overshoot included);
  `pUnst`: the unstopped tested increment on the cap event.
* `IsGenPair χ b E F Λ`: `(F, Λ)` is `(fun1 χ e, lam1 χ b E e)` or `(fun2 χ e e', lam2 χ b E e e')`.
* **`GramPassLocal`** (the local finite-`W` generator identity), stated as a hypothesis:
  under the hypotheses, for every auxiliary level `R`, `pStopSum → 0` as `W → ∞`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Pass

open MeasureTheory ProbabilityTheory Filter Topology Matrix Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open BlockBand.SourceProcess.PhysApprox.B3.Ident2
open scoped NNReal ENNReal

variable {K np : ℕ}

/-!
## Joint measurability of generator processes
-/

/-- **A primitive of a jointly strongly measurable integrand is jointly strongly measurable.** -/
theorem sm_primitive {Ω : Type*} [MeasurableSpace Ω] {f : ℝ → Ω → ℂ}
    (hf : StronglyMeasurable (Function.uncurry f)) :
    StronglyMeasurable fun p : ℝ≥0 × Ω => ∫ r in Ioc (0 : ℝ) p.1, f r p.2 := by
  set S : Set ((ℝ≥0 × Ω) × ℝ) := {q | q.2 ∈ Ioc (0 : ℝ) q.1.1}
  have hS : MeasurableSet S :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd
        (measurable_coe_nnreal_real.comp (measurable_fst.comp measurable_fst)))
  have hg : StronglyMeasurable (S.indicator fun q => f q.2 q.1.2) :=
    (hf.comp_measurable (measurable_snd.prodMk (measurable_snd.comp measurable_fst))).indicator hS
  have e : (fun p : ℝ≥0 × Ω => ∫ r in Ioc (0 : ℝ) p.1, f r p.2) = fun p =>
      ∫ r, (S.indicator fun q => f q.2 q.1.2) (p, r) := by
    funext p
    rw [← integral_indicator measurableSet_Ioc]
    congr 1
  rw [e]
  exact hg.integral_prod_right'

theorem sm_gramJ (b s : ℝ) (τ m : Fin np → ℝ) :
    StronglyMeasurable fun u : ℝ≥0 => gramJ (K := K) b s τ m u := by
  have h := (stronglyMeasurable_gramJ_comp (K := K) b s τ m).comp_measurable measurable_coe_nnreal_real
  simpa [Function.comp_def, Real.toNNReal_coe] using h

section Meas

variable {Ω : Type*} [MeasurableSpace Ω] {b E s : ℝ} {τ m : Fin np → ℝ}
  {G : ℝ≥0 → Ω → GSt K np} (hG : StronglyMeasurable (Function.uncurry G))
include hG

theorem sm_gY : StronglyMeasurable fun p : ℝ≥0 × Ω => gY b s τ m G p.1 p.2 :=
  hG.sub ((sm_gramJ b s τ m).comp_measurable measurable_fst)

theorem sm_gY_zero : StronglyMeasurable fun p : ℝ≥0 × Ω => gY b s τ m G 0 p.2 :=
  (sm_gY hG).comp_measurable (measurable_const.prodMk measurable_snd)

theorem sm_gY_toNNReal : StronglyMeasurable fun p : ℝ × Ω => gY b s τ m G p.1.toNNReal p.2 :=
  (sm_gY hG).comp_measurable (measurable_real_toNNReal.prodMap measurable_id)

theorem sm_genA {χ : ℝ → ℝ} (hχ : Continuous χ) (e : GIdx K np) :
    StronglyMeasurable fun p : ℝ≥0 × Ω => genA χ b E s τ m G e p.1 p.2 := by
  have hl : Continuous (lamA (K := K) (np := np) χ b E e) :=
    ((continuous_drE b E e).comp (continuous_snd.add continuous_fst)).mul
      ((continuous_cutC hχ).comp continuous_snd)
  exact sm_primitive (f := fun r ω => lamA χ b E e (gramJ b s τ m r.toNNReal,
      gY b s τ m G r.toNNReal ω))
    (hl.comp_stronglyMeasurable (((sm_gramJ b s τ m).comp_measurable
      (measurable_real_toNNReal.comp measurable_fst)).prodMk (sm_gY_toNNReal hG)))

theorem sm_stZ {χ : ℝ → ℝ} (hχ : Continuous χ) :
    StronglyMeasurable fun p : ℝ≥0 × Ω => stZ χ b E s τ m G p.1 p.2 := by
  have hX : StronglyMeasurable fun p : ℝ≥0 × Ω => fun e => genX χ b E s τ m G e p.1 p.2 := by
    refine (measurable_pi_iff.2 fun e => ?_).stronglyMeasurable
    exact ((((ClosedLimit.continuous_gramEntry e).comp_stronglyMeasurable (sm_gY hG)).sub
      ((ClosedLimit.continuous_gramEntry e).comp_stronglyMeasurable (sm_gY_zero hG))).sub
      (sm_genA hG hχ e)).measurable
  exact (sm_gY hG).prodMk (hX.prodMk (sm_gY_zero hG))

/-- **A generator process is jointly strongly measurable.** -/
theorem sm_genProc {χ : ℝ → ℝ} (hχ : Continuous χ) {F : ZSt K np → ℂ}
    {Λ : GSt K np × ZSt K np → ℂ} (hF : Continuous F) (hΛ : Continuous Λ) :
    StronglyMeasurable (Function.uncurry (genProc χ b E s τ m G F Λ)) := by
  refine (hF.comp_stronglyMeasurable (sm_stZ hG hχ)).sub ?_
  exact sm_primitive (f := fun r ω => Λ (gramJ b s τ m r.toNNReal,
      stZ χ b E s τ m G r.toNNReal ω))
    (hΛ.comp_stronglyMeasurable (((sm_gramJ b s τ m).comp_measurable
      (measurable_real_toNNReal.comp measurable_fst)).prodMk
      ((sm_stZ hG hχ).comp_measurable (measurable_real_toNNReal.prodMap measurable_id))))

end Meas

/-!
## The bound uniform over feasible paths
-/

/-- **`C_H`: a generator process is bounded on `[0, T]` along every feasible path, by a constant
depending only on the cutoff, `F`, `Λ` and the parameters** (not on the path or its space). -/
theorem exists_uniform_bound {b E s : ℝ} {τ m : Fin np → ℝ} {χ : ℝ → ℝ} (hχ : Continuous χ)
    {Rχ : ℝ} (hR : ∀ c, Rχ < |c| → χ c = 0 ∧ deriv χ c = 0 ∧ deriv (deriv χ) c = 0)
    {F : ZSt K np → ℂ} {Λ : GSt K np × ZSt K np → ℂ} (hF : Continuous F) (hΛ : Continuous Λ)
    (hFv : ∀ z, F z ≠ 0 → |trRe z.1| ≤ Rχ ∧ |trRe z.2.2| ≤ Rχ)
    (hΛv : ∀ p, Λ p ≠ 0 → |trRe p.2.1| ≤ Rχ ∧ |trRe p.2.2.2| ≤ Rχ) (T : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Ω : Type) (G : ℝ≥0 → Ω → GSt K np) (ω : Ω),
      (∀ u, GramFeasible (srcSignature K (Fin np)) (G u ω)) →
        ∀ v ≤ T, ‖genProc χ b E s τ m G F Λ v ω‖ ≤ C := by
  let S := {g : ℝ≥0 → GSt K np // ∀ u, GramFeasible (srcSignature K (Fin np)) (g u)}
  let _ : MeasurableSpace S := ⊤
  have : MeasurableSingletonClass S := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  obtain ⟨C, hC⟩ := exists_bound_genProc (Q := (Measure.count : Measure S))
    (G := fun u (g : S) => g.1 u) (b := b) (E := E) (s := s) (τ := τ) (m := m)
    (ae_of_all _ fun g u => g.2 u) hχ hR hF hΛ hFv hΛv T
  rw [Measure.ae_count_iff] at hC
  refine ⟨max C 0, le_max_right _ _, fun Ω G ω hω v hv => ?_⟩
  exact (hC ⟨fun u => G u ω, hω⟩ v hv).trans (le_max_left _ _)

/-!
## Generator pairs
-/

/-- `(F, Λ)` is the drift pair `(fun1 χ e, lam1 χ b E e)` or the bracket pair
`(fun2 χ e e', lam2 χ b E e e')`. -/
def IsGenPair (χ : ℝ → ℝ) (b E : ℝ) (F : ZSt K np → ℂ) (Λ : GSt K np × ZSt K np → ℂ) :
    Prop :=
  (∃ e, F = fun1 χ e ∧ Λ = lam1 χ b E e) ∨ ∃ e e', F = fun2 χ e e' ∧ Λ = lam2 χ b E e e'

theorem IsGenPair.data {χ : ℝ → ℝ} {b E : ℝ} (h3 : ContDiff ℝ 3 χ) (hs : HasCompactSupport χ)
    {F : ZSt K np → ℂ} {Λ : GSt K np × ZSt K np → ℂ} (hp : IsGenPair χ b E F Λ) :
    Continuous χ ∧ Continuous F ∧ Continuous Λ ∧ ∃ Rχ : ℝ,
      (∀ c, Rχ < |c| → χ c = 0 ∧ deriv χ c = 0 ∧ deriv (deriv χ) c = 0) ∧
      (∀ z, F z ≠ 0 → |trRe z.1| ≤ Rχ ∧ |trRe z.2.2| ≤ Rχ) ∧
      (∀ p, Λ p ≠ 0 → |trRe p.2.1| ≤ Rχ ∧ |trRe p.2.2.2| ≤ Rχ) := by
  obtain ⟨hc, hd, hdd⟩ := cut_continuity h3
  obtain ⟨R, hR⟩ := exists_cut_radius hs
  rcases hp with ⟨e, rfl, rfl⟩ | ⟨e, e', rfl, rfl⟩
  · exact ⟨hc, continuous_fun1 hc e, continuous_lam1 hc hd hdd b E e, R, hR,
      fun z hz => fun1_ne_zero hR e hz, fun p hp => lam1_ne_zero hR b E e hp⟩
  · exact ⟨hc, continuous_fun2 hc e e', continuous_lam2 hc hd hdd b E e e', R, hR,
      fun z hz => fun2_ne_zero hR e e' hz, fun p hp => lam2_ne_zero hR b E e e' hp⟩

/-!
## The prelimit processes
-/

/-- **The prelimit Gram process**: the closed Gram state at model time `u`. -/
def pG (b E s h : ℝ) (τ m : Fin np → ℝ) (W : ℕ)
    (V : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) :
    ℝ≥0 → ProbedPath W np × ℝ → GSt K np :=
  fun u y => b3ClosedGramAt b E s h τ m W (limLenAll s W u) V y

/-- **The prelimit generator process** (the same `F`, `Λ`, jumps `gramJ`). -/
def pM (χ : ℝ → ℝ) (b E s h : ℝ) (τ m : Fin np → ℝ) (W : ℕ)
    (V : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (F : ZSt K np → ℂ)
    (Λ : GSt K np × ZSt K np → ℂ) : ℝ≥0 → ProbedPath W np × ℝ → ℂ :=
  genProc χ b E s τ m (pG b E s h τ m W V) F Λ

/-- A prelimit cylinder test `φ((obs_{i_l}(u_l))_l)`. -/
def pTest (b E s h : ℝ) (τ m : Fin np → ℝ) (W : ℕ)
    (V : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) {r : ℕ}
    (i : Fin r → LIdx K np) (u : Fin r → ℝ≥0) (φ : BoundedContinuousFunction (Fin r → ℂ) ℝ)
    (y : ProbedPath W np × ℝ) : ℝ :=
  φ fun l => b3ObsAll b E s h τ m W V (i l) (u l) y

/-- The cap event on the closed sample. -/
def capS (b E s h : ℝ) (K W np : ℕ) : Set (ProbedPath W np × ℝ) :=
  {y | y.1.1 ∈ physCapEventC b E s h K W}

/-- The grid of `[a, t]` by the cells of the closed lengths: `max a (min t (j/W − s))`. -/
def cellT (s : ℝ) (W : ℕ) (a t : ℝ≥0) (j : ℕ) : ℝ≥0 :=
  max a (min t ((j : ℝ) / W - s).toNNReal)

/-- **The stopped tested increment**: over the cells `j` of `[a, t]`, the tested increments on
the alive set at `j` (level `R`). -/
def pStopSum (χ : ℝ → ℝ) (b E s h : ℝ) (τ m : Fin np → ℝ) (W : ℕ)
    (V : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (F : ZSt K np → ℂ)
    (Λ : GSt K np × ZSt K np → ℂ) (R : ℝ) {r : ℕ} (i : Fin r → LIdx K np) (u : Fin r → ℝ≥0)
    (φ : BoundedContinuousFunction (Fin r → ℂ) ℝ) (a t : ℝ≥0) : ℂ :=
  ∑ j ∈ Finset.Ico (limLenAll s W a) (limLenAll s W t + 1),
    ∫ y, (b3Alive b E s h τ m R W j V).indicator (fun y => pTest b E s h τ m W V i u φ y •
      (pM χ b E s h τ m W V F Λ (cellT s W a t (j + 1)) y -
        pM χ b E s h τ m W V F Λ (cellT s W a t j) y)) y ∂closedLaw b W np

/-- **The unstopped tested increment** on the cap event. -/
def pUnst (χ : ℝ → ℝ) (b E s h : ℝ) (τ m : Fin np → ℝ) (W : ℕ)
    (V : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (F : ZSt K np → ℂ)
    (Λ : GSt K np × ZSt K np → ℂ) {r : ℕ} (i : Fin r → LIdx K np) (u : Fin r → ℝ≥0)
    (φ : BoundedContinuousFunction (Fin r → ℂ) ℝ) (a t : ℝ≥0) : ℂ :=
  ∫ y, (capS b E s h K W np).indicator (fun y => pTest b E s h τ m W V i u φ y •
    (pM χ b E s h τ m W V F Λ t y - pM χ b E s h τ m W V F Λ a y)) y ∂closedLaw b W np

/-- **`GramPassLocal`** (the local finite-`W` generator
identity at an auxiliary stop `R`; second-order Taylor of the cutoffs, `ComplexClosedSummed` on
`b3Alive`, `ComplexClosedLindeberg` and `ComplexKStoppedMomentMax` for the remainders): for
every generator pair, every level `R`, all off-birth times `a ≤ t` and every cylinder test at
off-birth times `≤ a`, the stopped tested increments tend to `0`. -/
def GramPassLocal : Prop :=
  TransmissionLawContract → ComplexClosedSummed → ComplexClosedTight → ComplexKStoppedMomentMax →
    ComplexClosedLindeberg →
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs →
    ∀ χ : ℝ → ℝ, ContDiff ℝ 3 χ → HasCompactSupport χ →
    ∀ (F : ZSt K np → ℂ) (Λ : GSt K np × ZSt K np → ℂ), IsGenPair χ b E F Λ → ∀ R : ℝ,
    ∀ a t : ℝ≥0, a ≤ t → a ∉ birthTimes s τ → t ∉ birthTimes s τ →
    ∀ (r : ℕ) (i : Fin r → LIdx K np) (u : Fin r → ℝ≥0), (∀ l, u l ≤ a) →
      (∀ l, u l ∉ birthTimes s τ) → ∀ φ : BoundedContinuousFunction (Fin r → ℂ) ℝ,
      Tendsto (fun W => pStopSum χ b E s h τ m W (Vs W) F Λ R i u φ a t) atTop (𝓝 0)

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Pass
