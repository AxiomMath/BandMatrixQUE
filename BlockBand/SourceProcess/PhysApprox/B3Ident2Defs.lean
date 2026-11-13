module

public import BlockBand.SourceProcess.PhysApprox.B3FddDefs
public import BlockBand.SourceProcess.PhysApprox.B3LimPass
public import BlockBand.SourceProcess.PhysApprox.B3FeasBridge

/-!
# The identification target at all times and its composition

The uncapped fdd limit `IsCapFddLimitAll` is available, so no horizon extension is needed and the
candidate itself is the model.

* **`ComplexCapIdentAll`**, stated as a hypothesis: every continuous candidate that is an uncapped
  conditioned fdd limit is itself an `IsStoppedTestedComplexModel` with entrance
  `μ(s)[|capSet K h]`.
* **`TargetCapIdentAll`**, stated as a hypothesis: the hypotheses of `TargetCapFdd` give
  `ComplexCapIdentAll` (feasibility is not a hypothesis: `complexClosedFeasible_holds`).
* `limLen_eq_limLenAll`, `condObsTest_eq_all`, **`isCapFddLimit_of_all`**: on the capped range
  `s + u ≤ max(s, T)` the capped and uncapped observables agree, so an uncapped limit is a capped
  limit for every `T`.
* **`complexCapSubseq_of_all`**: `ExistsTimeSFrame → ComplexCapFddAll → ComplexCapIdentAll →
  ComplexCapSubseq` (as in `complexCapSubseq_of`; the value is `tendsto_condClosed_of_fdd`).
* **`targetCapCond'_of_all`**: `TargetCapFddAll → TargetCapIdentAll → TargetCapCond'`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open scoped NNReal ENNReal

/-- **`ComplexCapIdentAll` (identification of the uncapped limit points)**: every continuous
candidate that is a conditioned fdd limit at all non-birth times is a stopped tested complex model
with entrance `μ(s)[|capSet K h]`. -/
def ComplexCapIdentAll : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs →
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
    (μ : ℝ → Ω → FiniteMeasure unitInterval), IsTransmissionLimit b E (fun _ => 0) P μ →
    CapCond.NoAtom (entranceLaw P μ s) h → entranceLaw P μ s (capSet K h) ≠ 0 →
    ∀ φ : ℕ → ℕ, Tendsto φ atTop atTop →
    ∀ (Ω' : Type) (_ : MeasurableSpace Ω') (Q : Measure Ω') (tseq : Ω' → ℕ → ℝ)
      (G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin np)))
      (Kc : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ),
      IsCapLimitData b E s τ m K Q tseq G Kc → IsCapFddLimitAll b E s h τ m K Vs φ Q tseq G Kc →
      IsStoppedTestedComplexModel b E s τ m h K ((entranceLaw P μ s)[|capSet K h]) Q tseq G Kc

/-- **Identification of the uncapped limit points from the hypotheses of `TargetCapFdd`.** -/
def TargetCapIdentAll : Prop :=
  TransmissionLawContract → ComplexClosedSummed → ComplexClosedTight → ComplexKStoppedMomentMax →
    ComplexClosedLindeberg → ComplexCapIdentAll

namespace Ident2

theorem limLen_eq_limLenAll {s T : ℝ} {W : ℕ} {u : ℝ≥0} (hu : s + (u : ℝ) ≤ max s T) :
    limLen s T W u = limLenAll s W u :=
  min_eq_left (Nat.floor_le_floor (mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg W)))

theorem ident2_b3Obs_eq_all {b E s T h : ℝ} {np K : ℕ} {τ m : Fin np → ℝ} {W : ℕ}
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} (i : LIdx K np) {u : ℝ≥0}
    (hu : s + (u : ℝ) ≤ max s T) :
    b3Obs b E s T h τ m W Vs i u = b3ObsAll b E s h τ m W Vs i u := by
  rcases i with e | k | ij
  · simp only [b3Obs, b3ObsAll, limLen_eq_limLenAll hu]
  · simp only [b3Obs, b3ObsAll]
  · simp only [b3Obs, b3ObsAll, limLen_eq_limLenAll hu]

theorem condObsTest_eq_all {b E s T h : ℝ} {np K : ℕ} {τ m : Fin np → ℝ} {W : ℕ}
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} {ι : Type} [Fintype ι]
    (i : ι → LIdx K np) {u : ι → ℝ≥0} (hu : ∀ l, s + (u l : ℝ) ≤ max s T)
    (ψ : BoundedContinuousFunction (ι → ℂ) ℝ) :
    condObsTest b E s T h τ m W Vs i u ψ = condObsTestAll b E s h τ m W Vs i u ψ := by
  have e : ∀ y, (fun l => b3Obs b E s T h τ m W Vs (i l) (u l) y) =
      fun l => b3ObsAll b E s h τ m W Vs (i l) (u l) y := fun y =>
    funext fun l => congrFun (ident2_b3Obs_eq_all (i l) (hu l)) y
  simp only [condObsTest, condObsTestAll, e]

/-- **An uncapped conditioned fdd limit is a capped one, for every `T`.** -/
theorem isCapFddLimit_of_all {b E s h : ℝ} {np : ℕ} {τ m : Fin np → ℝ} {K : ℕ}
    {Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} {φ : ℕ → ℕ}
    {Ω' : Type} [MeasurableSpace Ω'] {Q : Measure Ω'} {tseq : Ω' → ℕ → ℝ}
    {G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin np))}
    {Kc : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ}
    (hF : IsCapFddLimitAll b E s h τ m K Vs φ Q tseq G Kc) (T : ℝ) :
    IsCapFddLimit b E s T h τ m K Vs φ Q tseq G Kc := by
  intro ι _ i u hu hτ ψ
  refine (hF ι i u hτ ψ).congr' (Eventually.of_forall fun n => ?_)
  exact (condObsTest_eq_all i hu ψ).symm

end Ident2

open Ident2

/-- **The subsequence form from the uncapped statements** (as in `complexCapSubseq_of`). -/
theorem complexCapSubseq_of_all (hEx : ExistsTimeSFrame) (hFd : ComplexCapFddAll)
    (hId : ComplexCapIdentAll) : ComplexCapSubseq := by
  intro b E np τ m T hD Ω mΩ P μ hlim s hs hτ Φ h hh0 hh1 hA K hne φ hφ
  have hFD := frameDomain_chooseFrame (K := K) hEx hD hs hτ hh0 hh1
  obtain ⟨ψ, hψ, Ω', mΩ', Q, tseq, G, Kc, hdat, hfdd⟩ :=
    hFd b E np τ m T s h K _ hFD Ω mΩ P μ hlim hA hne φ hφ
  have hφψ : Tendsto (fun n => φ (ψ n)) atTop atTop := hφ.comp hψ.tendsto_atTop
  refine ⟨ψ, hψ, Ω', mΩ', Q, tseq, G, Kc,
    hId b E np τ m T s h K _ hFD Ω mΩ P μ hlim hA hne _ hφψ Ω' mΩ' Q tseq G Kc hdat hfdd, ?_⟩
  exact tendsto_condClosed_of_fdd hFD hφψ (isCapFddLimit_of_all hfdd T) Φ

/-- **`TargetCapCond'` from the two uncapped targets** (feasibility by
`complexClosedFeasible_holds`). -/
theorem targetCapCond'_of_all (hFd : TargetCapFddAll) (hId : TargetCapIdentAll) :
    TargetCapCond' :=
  targetCapCond'_of_subseq (fun hTL hEx hS hT hK _ hL _ =>
    complexCapSubseq_of_all hEx (hFd hTL hS hT hK hL) (hId hTL hS hT hK hL))
    complexClosedFeasible_holds

end BlockBand.SourceProcess.PhysApprox.B3
