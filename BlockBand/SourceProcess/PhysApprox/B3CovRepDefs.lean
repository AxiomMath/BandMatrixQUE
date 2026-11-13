module

public import BlockBand.SourceProcess.PhysApprox.B3CovWord
public import BlockBand.SourceProcess.PhysApprox.B3DecayDefs
public import BlockBand.SourceProcess.PhysApprox.B3ClosedFormDefs
public import BlockBand.Transmission.LawClauses.EntryVariance

/-!
# The concrete closed layer error scale `e` and contracting sum `Z`

The hypotheses `CovWordRep`, `ConjWordRep`, `CovErrMoments`, `CovDecayHyp` are stated for two
abstract fields `e, Z : CovField`. They are fixed here.

* **The closed near Schur matrix** is the shared closed input `X_cl = z_b - R_cl⁻¹`
  (`closedNearX`, `b3ClosedX`), with the closed near resolvent `R_cl = ι*ℝ_jC_j(z)ι`
  (`closedNearR`). So `passiveResolvent X_cl = R_cl` when `R_cl` is invertible
  (`passiveResolvent_closedNearX`). This is the input of `δ₀,cl = |W⁻¹ Tr R_cl - a|`.
* **`e = b3CovErr`**: the one-layer error scale `δ₀ + δ₁ + g/W + W⁻¹` at `X_cl` and the stationary
  jet `b3Jet`.
* **`Z = b3CovZ`**: `Σ_{σ,k,l} |Q^σ_{kl}(j)|`, with the closed contracting coordinates
  `Q^σ_{kl} = (V_jᴴΣ_σV_j)_{kl}` (`b3ContrCoord`), `σ` running over the four closed contracting
  separators. This is `contrGram` at the closed frame and the closed separators.
  `CovDecayHyp b3CovZ` follows from `B3ClosedContrDecay` (`covDecayHyp_b3CovZ`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory ProbabilityTheory Filter Topology Matrix Finset
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open BlockBand.SourceProcess.ContractingWords (layerErr)
open BlockBand.Transmission.Bridge
open scoped NNReal ENNReal ComplexConjugate

/-!
## The closed near Schur matrix `closedNearX`
-/

/-- `passiveResolvent X_cl = R_cl` when `R_cl` is invertible. -/
theorem passiveResolvent_closedNearX {b E s h : ℝ} {W j : ℕ} {ω : GrowthPath W} {z : ℂ}
    (hR : IsUnit (closedNearR b E s h W j ω z).det) :
    passiveResolvent b E (closedNearX b E s h W j ω z) = closedNearR b E s h W j ω z := by
  rw [passiveResolvent, closedNearX, sub_sub_cancel]
  exact Matrix.nonsing_inv_nonsing_inv _ hR

/-!
## The stationary jet
-/

/-- The stationary first jet `s_*`, chosen once. -/
def b3Jet (b E : ℝ) : ℂ := Classical.epsilon (IsStationaryJet b E)

theorem b3Jet_spec {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) :
    IsStationaryJet b E (b3Jet b E) :=
  Classical.epsilon_spec
    (BlockBand.Transmission.PassiveCovariance.stationaryJet_exists hb0 hb h1 h2)

/-- Every stationary jet is `b3Jet` (`s_*` is unique). -/
theorem b3Jet_eq {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) {s : ℂ}
    (hs : IsStationaryJet b E s) : b3Jet b E = s :=
  BlockBand.Transmission.LawClauses.stationaryJet_unique hb0 hb h1 h2 (b3Jet_spec hb0 hb h1 h2) hs

/-!
## The two fields
-/

/-- The one-layer error scale `δ₀ + δ₁ + g/W + W⁻¹` of a near Schur matrix `X`, at `b3Jet`. -/
def b3LayerErrX (b E : ℝ) {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  jetDistance0 b E X + jetDistance1 b E (b3Jet b E) X +
    conductanceOf (passiveTransmission b E X) / W + (W : ℝ)⁻¹

/-- **`layerErr` depends on the two-port only through its near Schur matrix.** -/
theorem layerErr_eq_b3LayerErrX {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E)
    (h2 : E < 2) {s : ℂ} (hs : IsStationaryJet b E s) {W : ℕ}
    {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} {X : Matrix (Fin W) (Fin W) ℂ}
    (hX : nearSchur (boundaryZ b E) XX = X) : layerErr b E s XX = b3LayerErrX b E X := by
  rw [layerErr, b3LayerErrX, hX, b3Jet_eq hb0 hb h1 h2 hs]

/-- **The closed layer error scale** `e_j = δ₀(X_cl) + δ₁(X_cl) + g(X_cl)/W + W⁻¹`, at the closed
near Schur matrix of length `j` and phase `z = e^{iθ}`. -/
def b3CovErr : CovField := fun b E _np τ m s h _K W _Vs j y =>
  b3LayerErrX b E (b3ClosedX b E s h τ m W j y)

/-- **The contracting-coordinate sum** `Z_j = Σ_{σ,k,l}|Q^σ_{kl}(j)|` (`b3ContrCoord`). -/
def b3CovZ : CovField := fun b E np τ m s h K W Vs j y =>
  ∑ x : Fin 4 × SrcCol K (Fin np) × SrcCol K (Fin np),
    ‖b3ContrCoord b E s h τ m W j Vs x.1 x.2.1 x.2.2 y‖

theorem b3CovZ_nonneg (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (s h : ℝ) (K W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (j : ℕ)
    (y : ProbedPath W np × ℝ) : 0 ≤ b3CovZ b E np τ m s h K W Vs j y :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem norm_b3CovZ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (s h : ℝ) (K W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (j : ℕ)
    (y : ProbedPath W np × ℝ) :
    ‖b3CovZ b E np τ m s h K W Vs j y‖ = b3CovZ b E np τ m s h K W Vs j y :=
  Real.norm_of_nonneg (b3CovZ_nonneg b E np τ m s h K W Vs j y)

/-- Each closed contracting coordinate is bounded by `Z`. -/
theorem norm_b3ContrCoord_le_b3CovZ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (s h : ℝ) (K W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (j : ℕ) (σ : Fin 4)
    (k l : SrcCol K (Fin np)) (y : ProbedPath W np × ℝ) :
    ‖b3ContrCoord b E s h τ m W j Vs σ k l y‖ ≤ b3CovZ b E np τ m s h K W Vs j y := by
  have hle := Finset.single_le_sum (s := Finset.univ)
    (f := fun x : Fin 4 × SrcCol K (Fin np) × SrcCol K (Fin np) =>
      ‖b3ContrCoord b E s h τ m W j Vs x.1 x.2.1 x.2.2 y‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ (σ, k, l))
  exact hle

theorem measurable_b3CovZ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (s h : ℝ) (K W : ℕ)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} (hV : Measurable Vs)
    (j : ℕ) : Measurable (b3CovZ b E np τ m s h K W Vs j) := by
  unfold b3CovZ
  exact Finset.measurable_sum _ fun x _ =>
    (measurable_b3ContrCoord b E s h τ m W j hV x.1 x.2.1 x.2.2).norm

end BlockBand.SourceProcess.PhysApprox.B3
