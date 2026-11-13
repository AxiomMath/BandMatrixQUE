module

public import BlockBand.SourceProcess.PhysApprox.IdentK.Passage
public import BlockBand.SourceProcess.PhysApprox.B3MomTight

/-!
# Measurability of the finite-`W` generator process

Measure spaces: the closed sample space `ProbedPath W np × ℝ` with its product Borel structure
(the space of `closedLaw b W np`), and Lebesgue measure on the time interval `(0, t]`.

* `measurable_uncurry_b3ObsAll_of_measurable`: the finite-`W` observables are jointly
  measurable in `(u, y)` for a frame map `Vs` that is merely Borel measurable
  (`measurable_uncurry_b3ObsAll` assumes adaptedness, `Measurable[growthSigma W (closeLen s W)]`;
  here `measurable_b3ClosedGramAt` and `measurable_b3ClosedKAt` replace it).
* `measurable_gL`: the integrand coefficient `gL Λ` is jointly measurable in `(t, x, x₀)`
  (`gramJ`, `kJ` are strongly measurable step functions; `Λ`, `stOf` continuous).
* **`stronglyMeasurable_genObs_b3ObsAll`**: for continuous `F`, `Λ`, the drift-free process
  `genObs (b3ObsAll …) F Λ t` is strongly measurable on the closed sample space (the `F` term by
  continuity; the time integral by `StronglyMeasurable.integral_prod_left`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK.FW

open MeasureTheory ProbabilityTheory Filter Topology Matrix Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open BlockBand.SourceProcess.PhysApprox.B3.Ident2
open BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK.Core
open scoped NNReal ENNReal ComplexConjugate

variable {K np : ℕ}

/-- **The finite-`W` observables are jointly measurable** for a Borel measurable frame map. -/
theorem measurable_uncurry_b3ObsAll_of_measurable {b E s h : ℝ} {τ m : Fin np → ℝ} {W : ℕ}
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} (hV : Measurable Vs)
    (i : B3.LIdx K np) : Measurable (Function.uncurry (b3ObsAll b E s h τ m W Vs i)) := by
  refine measurable_uncurry_of_factor (L := limLenAll s W)
    (Nat.measurable_floor.comp (measurable_const.mul
      (measurable_const.add measurable_coe_nnreal_real))) (fun u => ?_) (fun u v huv => ?_)
  · rcases i with e | k | ij
    · exact (ClosedSumProof.measurable_gramEntry e).comp
        (B3.measurable_b3ClosedGramAt b E s h τ m W _ hV)
    · exact Complex.measurable_ofReal.comp
        ((CapLaw.measurable_physTseq b E s W k).comp (measurable_fst.comp measurable_fst))
    · exact (measurable_pi_apply ij.2).comp
        ((measurable_pi_apply ij.1).comp (B3.measurable_b3ClosedKAt b E s h τ m W _))
  · rcases i with e | k | ij <;> funext y <;> simp only [b3ObsAll, huv]

/-- The coefficient `gL Λ` is jointly measurable. -/
theorem measurable_gL {b E s : ℝ} {τ m : Fin np → ℝ} {Λ : GSt K np × ZK K np → ℂ}
    (hΛ : Continuous Λ) :
    Measurable fun q : ℝ≥0 × (KCo K np → ℂ) × (KCo K np → ℂ) =>
      gL b E s τ m Λ q.1 q.2.1 q.2.2 := by
  have hc : Continuous fun q : (GSt K np × KSt np) × (KCo K np → ℂ) × (KCo K np → ℂ) =>
      Λ (q.1.1, stOf b E s τ m q.1 q.2.1 q.2.2) :=
    hΛ.comp ((continuous_fst.comp continuous_fst).prodMk (continuous_stOf b E s τ m))
  exact (hc.comp_stronglyMeasurable (((stronglyMeasurable_jt (K := K) b E s τ m).comp_measurable
    measurable_fst).prodMk measurable_snd.stronglyMeasurable)).measurable

/-- **The finite-`W` drift-free process is strongly measurable** at every time. -/
theorem stronglyMeasurable_genObs_b3ObsAll {b E s h : ℝ} {np K : ℕ} {τ m : Fin np → ℝ} {W : ℕ}
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} (hV : Measurable Vs)
    {F : ZK K np → ℂ} {Λ : GSt K np × ZK K np → ℂ} (hF : Continuous F) (hΛ : Continuous Λ)
    (t : ℝ≥0) : StronglyMeasurable (genObs b E s τ m (b3ObsAll b E s h τ m W Vs) F Λ t) := by
  have ho : ∀ i, Measurable (Function.uncurry (b3ObsAll b E s h τ m W Vs i)) :=
    measurable_uncurry_b3ObsAll_of_measurable hV
  rw [genObs_eq_mgen]
  have hf : Continuous fun p : (KCo K np → ℂ) × (KCo K np → ℂ) => fF b E s τ m F t p.1 p.2 :=
    hF.comp ((continuous_stOf b E s τ m).comp (continuous_const.prodMk continuous_id))
  have h1 : StronglyMeasurable fun y : ProbedPath W np × ℝ =>
      fF b E s τ m F t (xv cK (b3ObsAll b E s h τ m W Vs) t y)
        (xv cK (b3ObsAll b E s h τ m W Vs) 0 y) :=
    (hf.measurable.comp ((measurable_xv0 ho cK t).prodMk
      (measurable_xv0 ho cK 0))).stronglyMeasurable
  have h2 := StronglyMeasurable.integral_prod_left (μ := volume.restrict (Ioc (0 : ℝ) t))
    (f := fun (r : ℝ) (y : ProbedPath W np × ℝ) =>
      gL b E s τ m Λ r.toNNReal (xv cK (b3ObsAll b E s h τ m W Vs) r.toNNReal y)
        (xv cK (b3ObsAll b E s h τ m W Vs) 0 y))
    (measurable_integrand ho cK (measurable_gL hΛ)).stronglyMeasurable
  exact h1.sub h2

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK.FW
