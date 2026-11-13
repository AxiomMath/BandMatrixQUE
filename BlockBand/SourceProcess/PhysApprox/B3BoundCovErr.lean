module

public import BlockBand.SourceProcess.PhysApprox.B3CovRepKBound
public import BlockBand.Transmission.PathJet.JetPathStep
public import BlockBand.Transmission.PathScalar.Dissipative

/-!
# The closed layer error scale is bounded on passive `X_cl`

For a passive near Schur matrix `X` (`-Im X ⪰ 0`), `W ≥ 1`, `E ∈ (-2, 2)`, `0 < b < 1/2`, the
one-layer error scale `e = δ₀ + δ₁ + g/W + W⁻¹` (`b3LayerErrX`, at the stationary jet `b3Jet`)
satisfies, deterministically,

  `0 ≤ e ≤ M(b, E) := (η⁻¹ + 1) + jetM b κ_E + 2`,  `κ_E = min(E + 2, 2 - E)`,

* `g/W ≤ 1`: `g = Re Tr(I - S*S) = W - ‖S‖²_HS ≤ W` (`conductanceOf_le_card`, any `X`);
* `W⁻¹ ≤ 1`; `e ≥ 0` from `layerErrX_facts`.

`M` depends only on `(b, E)`: not on `W`, `j`, `R`, the frame or the sample. With
`ae_passive_b3ClosedX`, this gives **`ae_b3CovErr_le`** (a.s., every `W ≥ 1`, every length `j`) and
the form **`covErrBdd_b3CovErr : CovErrBdd b3CovErr`** used by the fixed-`N` restatements.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.Stochastic
open BlockBand.Transmission.Bridge
open scoped ComplexOrder

/-!
## The deterministic bound
-/

/-- **The bound `M(b, E)`** of the closed layer error scale: `(η⁻¹ + 1) + jetM b κ_E + 2`. -/
def b3ErrBound (b E : ℝ) : ℝ :=
  (etaZ b E)⁻¹ + 1 + BlockBand.Transmission.PathJet.jetM b (min (E + 2) (2 - E)) + 2

theorem b3ErrBound_nonneg {b E : ℝ} (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) :
    0 ≤ b3ErrBound b E := by
  obtain ⟨hκ, hE⟩ := cov_bulk h1 h2
  have hη := BlockBand.Transmission.CovarianceBulk.etaZ_pos_bulk hb hκ hE
  unfold b3ErrBound BlockBand.Transmission.PathJet.jetM
  positivity

/-- `g = Re Tr(I - S*S) ≤ W`, for every `X` (`passiveTransmission_eq_one_sub`). -/
theorem conductanceOf_le_card (b E : ℝ) {W : ℕ} (X : Matrix (Fin W) (Fin W) ℂ) :
    conductanceOf (passiveTransmission b E X) ≤ W := by
  have h := trace_re_gram_nonneg (passiveS b E X)
  rw [conductanceOf, passiveTransmission_eq_one_sub, Matrix.trace_sub, Matrix.trace_one,
    Fintype.card_fin, Complex.sub_re, Complex.natCast_re]
  linarith

/-- **`0 ≤ e(X) ≤ M(b, E)` for passive `X`**, `W ≥ 1`. -/
theorem b3LayerErrX_le {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    {W : ℕ} (hW : 1 ≤ W) {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef) :
    0 ≤ b3LayerErrX b E X ∧ b3LayerErrX b E X ≤ b3ErrBound b E := by
  obtain ⟨hκ, hE⟩ := cov_bulk h1 h2
  have hd0 := BlockBand.Transmission.PathScalar.jetDistance0_le_bound hb0 hb h1 h2 hY
  have hd1 : jetDistance1 b E (b3Jet b E) X ≤
      BlockBand.Transmission.PathJet.jetM b (min (E + 2) (2 - E)) := by
    rw [BlockBand.Transmission.PathJet.jetDistance1_eq_crossTr (by linarith) h1 h2 _ hY]
    exact BlockBand.Transmission.PathJet.crossTr_jet_le hb0 hb hκ hE
      (b3Jet_spec hb0 hb h1 h2) hY
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hg : conductanceOf (passiveTransmission b E X) / W ≤ 1 :=
    div_le_one_of_le₀ (conductanceOf_le_card b E X) hW0.le
  have hWi : (W : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hW)
  have hWe := (layerErrX_facts hb hκ hE hW hY).1
  refine ⟨(by positivity : (0 : ℝ) ≤ (W : ℝ)⁻¹).trans hWe, ?_⟩
  unfold b3LayerErrX b3ErrBound
  linarith

/-- **`0 ≤ e_j ≤ M(b, E)` a.s. for the closed layer error scale**, at every `W ≥ 1` and every
length `j` (passivity of `X_cl`, `ae_passive_b3ClosedX`). -/
theorem ae_b3CovErr_le {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2)
    (s h : ℝ) (hh : h ^ 2 < 1) {np K W : ℕ} (τ m : Fin np → ℝ) (hW : 1 ≤ W)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (j : ℕ) :
    ∀ᵐ y ∂closedLaw b W np, 0 ≤ b3CovErr b E np τ m s h K W Vs j y ∧
      b3CovErr b E np τ m s h K W Vs j y ≤ b3ErrBound b E := by
  filter_upwards [ae_passive_b3ClosedX (np := np) hb0 hb hE1 hE2 s h hh τ m hW j] with y hy
  exact b3LayerErrX_le hb0 hb hE1 hE2 hW hy

/-!
## The form `CovErrBdd`
-/

/-- **`0 ≤ e ≤ M` a.e. on the alive set**, with `M ≥ 0` depending only on the frame (chosen
before `R`), eventually in `W`, at every no-birth step. -/
def CovErrBdd (e : CovField) : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∃ M : ℝ, 0 ≤ M ∧ ∀ R : ℝ,
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W,
      ∀ᵐ y ∂closedLaw b W np, y ∈ b3Alive b E s h τ m R W j (Vs W) →
        0 ≤ e b E np τ m s h K W (Vs W) j y ∧ e b E np τ m s h K W (Vs W) j y ≤ M

/-- **`CovErrBdd b3CovErr`**, with `M = b3ErrBound b E`. -/
theorem covErrBdd_b3CovErr : CovErrBdd b3CovErr := by
  intro b E np τ m T s h K Vs hFD
  obtain ⟨hb0, hb, hE1, hE2, -⟩ := hFD.1
  have hh : h ^ 2 < 1 := by nlinarith [hFD.2.2.2.1, hFD.2.2.2.2.1]
  refine ⟨b3ErrBound b E, b3ErrBound_nonneg hb hE1 hE2, fun R => ?_⟩
  filter_upwards [eventually_ge_atTop 1] with W hW1 j _
  filter_upwards [ae_b3CovErr_le hb0 hb hE1 hE2 s h hh τ m hW1 (Vs W) j] with y hy _
  exact hy

/-- `CovErrBdd e` contains `CovErrNonneg e`. -/
theorem covErrNonneg_of_bdd {e : CovField} (hB : CovErrBdd e) : CovErrNonneg e := by
  intro b E np τ m T s h K Vs hFD R
  obtain ⟨M, -, hev⟩ := hB b E np τ m T s h K Vs hFD
  filter_upwards [hev R] with W hW j hj
  filter_upwards [hW j hj] with y hy hyA
  exact (hy hyA).1

end BlockBand.SourceProcess.PhysApprox.B3
