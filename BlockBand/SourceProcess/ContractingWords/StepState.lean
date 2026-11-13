module

public import BlockBand.SourceProcess.ContractingWords.LayerFresh
public import BlockBand.SourceProcess.ContractingWords.LayerMeas
public import BlockBand.SourceProcess.ContractingWords.PathCond
public import BlockBand.SourceProcess.ContractingWords.AliveLetters
public import BlockBand.SourceProcess.ContractingWords.Moments
public import BlockBand.SourceProcess.FullSourceStops.CurrentPast

/-!
# The path at length `j` as a deterministic old state of the fresh layer

`stateZ ω y`: the one-layer new value at the old state of `ω` at length `j` (letters, `𝕏_j`)
and the fresh sample `y`; `stateΨ x y = stateZ (extPast x) y` on past coordinates.

* `measurable_stateΨ`; `stateZ_extPast`: `stateZ (extPast (pc ω)) = stateZ ω`;
* `ae_step_state`: a.s., for `j ≥ 1`, `k_a < j`: `Z_{j+1} = stateΨ(pc, fs)`,
  `Z_j = coreProd A_j (sepOf 𝕏_j) Zs`;
* `condExp_step`: `E[Z_{j+1} ∣ 𝓕_j] = ∫ stateZ ω y dfresh(y)` a.s. (integrable `Z_{j+1}`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.CompleteSourceGap
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.SourceProcess.FullSourceStops
open scoped ENNReal

variable {W nT nI : ℕ}

/-- The one-layer new value at the old state of `ω` at length `j`. -/
def stateZ (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (W j : ℕ)
    (Zs : List (TraceWord nT nI)) (ω : GrowthPath W) (y : LayerSample W .oneBlockOnePort) : ℂ :=
  newProd (letterMatrix b E k q W j ω) (injCoef q W j) (freshTransport b E (pathXX E W j ω) y)
    (freshD b E (pathXX E W j ω) y) (sepOf b E (freshTwoPortSchur E (pathXX E W j ω) y)) Zs

/-- The same on past coordinates. -/
def stateΨ (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (W j : ℕ)
    (Zs : List (TraceWord nT nI)) (z : PastSample W j × LayerSample W .oneBlockOnePort) : ℂ :=
  stateZ b E k q W j Zs (extPast W j z.1) z.2

theorem measurable_stateΨ (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (j : ℕ)
    (Zs : List (TraceWord nT nI)) : Measurable (stateΨ b E k q W j Zs) := by
  have hx : Measurable fun z : PastSample W j × LayerSample W .oneBlockOnePort =>
      extPast W j z.1 := (measurable_extPast j).comp measurable_fst
  exact measurable_layerZ b E (injCoef q W j)
    (fun ℓ => (measurable_letterMatrix b E k q j ℓ).comp hx)
    ((measurable_pathSchur E j).comp ((measurable_pathAt W j).comp hx)) measurable_snd Zs

theorem stateZ_extPast (b E : ℝ) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) (j : ℕ)
    (Zs : List (TraceWord nT nI)) (ω : GrowthPath W) :
    stateZ b E k q W j Zs (extPast W j (pastCoords W j ω)) = stateZ b E k q W j Zs ω := by
  have h := pathAt_extPast (W := W) j ω
  have hA : letterMatrix b E k q W j (extPast W j (pastCoords W j ω)) =
      letterMatrix b E k q W j ω := funext fun ℓ => letterMatrix_congr b E k q j h ℓ
  have hX : pathXX E W j (extPast W j (pastCoords W j ω)) = pathXX E W j ω :=
    congrArg (pathSchur E) h
  funext y
  unfold stateZ
  rw [hA, hX]

/-- **The path step in state form**, almost surely. -/
theorem ae_step_state {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hW : 1 ≤ W) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ j, 1 ≤ j → (∀ a, k a < j) → ∀ Zs : List (TraceWord nT nI),
      productValue b E k q W (j + 1) ω Zs =
          stateΨ b E k q W j Zs (pastCoords W j ω, freshSample W j ω) ∧
        productValue b E k q W j ω Zs =
          coreProd (letterMatrix b E k q W j ω) (sepOf b E (pathXX E W j ω)) Zs := by
  filter_upwards [ae_productValue_step hb0 hb hE1 hE2 hW k q] with ω h j hj hk Zs
  refine ⟨?_, (h j hj hk Zs).2⟩
  rw [(h j hj hk Zs).1, stateΨ, stateZ_extPast]
  rfl

/-- **The conditional mean of the step.** -/
theorem condExp_step {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (hW : 1 ≤ W) (k : Fin nT → ℕ) (q : Fin nI → ℝ → ℝ) {j : ℕ} (hj : 1 ≤ j) (hk : ∀ a, k a < j)
    (Zs : List (TraceWord nT nI))
    (hint : Integrable (fun ω => productValue b E k q W (j + 1) ω Zs) (growthPathLaw W b)) :
    (growthPathLaw W b)[fun ω => productValue b E k q W (j + 1) ω Zs | growthSigma W j] =ᵐ[
      growthPathLaw W b] fun ω => ∫ y, stateZ b E k q W j Zs ω y ∂freshLaw W b := by
  have hae : (fun ω => productValue b E k q W (j + 1) ω Zs) =ᵐ[growthPathLaw W b]
      fun ω => stateΨ b E k q W j Zs (pastCoords W j ω, freshSample W j ω) := by
    filter_upwards [ae_step_state hb0 hb hE1 hE2 hW k q] with ω h
    exact (h j hj hk Zs).1
  have hint' := hint.congr hae
  refine (condExp_congr_ae hae).trans ((condExp_past_fresh b j (measurable_stateΨ b E k q j Zs)
    hint').trans (Eventually.of_forall fun ω => ?_))
  simp only [stateΨ, stateZ_extPast]

end BlockBand.SourceProcess.ContractingWords
