module

public import BlockBand.SourceProcess.PhysApprox.B3MeanFresh
public import BlockBand.SourceProcess.PhysApprox.B3MeanSum

/-!
# The closed one-step `𝒦` mean, `KStopMeanSum`, `GenKMeanForm`, and the maximal correction moment

**The closed input (`ClosedKMeanInput`, stated as a hypothesis).** At every non-birth step `i` at
which the entry `ij` is alive (both tags born), the closed stopped step has the closed exact update
form `Z_i = u*Δ(X, F_i)v` a.e. (`ClosedStepForm`): `F_i` the fresh layer, `u, v` near frames
bounded by a constant `Cf` (on the alive set `‖ι*V_cl e_k‖² ≤ Tr M_cl < R`, and the lossless
closure keeps `‖𝕊_cl‖ ≤ 1`), `X` a passive input; `u, v, X` functions of the past at `i`, the
probes and the phase. The intended witness is `u = 1_{A_i}ι*V_cl e_k`, `v = 1_{A_i}ι*𝕊_cl V_cl e_l`,
`X` the near Schur complement of the closed length-`i` path. The same `X` has the closed jet in
`L⁴`, `∫δ₀(X)⁴ ≤ C/W⁴` (`ClosedJetL4`).

Proved here:
* `b3ClosedKAt_dead`, `kStopStep_dead`: entry `ij` of the closed `𝒦` vanishes at every length up to
  the later of the two births, so the step vanishes there;
* **`kStopMeanForm4_of_closed`**: `GaussianAbsorptionContract + GaussianLpGradient +
  ClosedKMeanInput ⇒ KStopMeanForm4` (Fubini over the fresh layer and `delta_fresh_bounds`);
* **`kStopMeanSum_of_closed`**, **`genKMeanForm_of_closed`**: the targets `KStopMeanSum` and
  `GenKMeanForm` from the same inputs;
* **`complexKCorrMomentMax_of_max`**: `KUnclosedMax + ComplexKStoppedMomentMax ⇒
  ComplexKCorrMomentMax` (`corr = 𝒦 − 𝒦_cl`); with the stopped-moment parts,
  `complexKCorrMomentMax_of_parts`, `complexKCorrMomentMax_of_closed`.

Stated only: **`RieszConjugateL4`** (M. Riesz / Pichorides at `p = 4` on the circle; not in
Mathlib), the analytic input of an alternative argument at each fixed `j`. It bounds
`E_θ|corr_j|⁴` at each fixed `j`; it does not by itself bound `E sup_j`, so it does not replace the
argument above for the maximal form.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.Bridge
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.Closing
open BlockBand.SourceProcess.ClosedPath
open scoped NNReal ENNReal ComplexOrder

variable {W np : ℕ}

/-!
## Entries of unborn tags vanish
-/

theorem probeColumns_dead {n : ℕ} (τ m : Fin np → ℝ) {k : Fin np}
    (hk : n ≤ ⌊(W : ℝ) * τ k⌋₊) (g : Fin np → Fin W → ℂ) (x : Fin n × Fin W) :
    probeColumns W n τ m g x k = 0 := by
  have h : ¬ ⌊(W : ℝ) * τ k⌋₊ < n := not_lt.2 hk
  simp [probeColumns, h]

theorem probeFrame_dead (b E : ℝ) {n : ℕ} (τ m : Fin np → ℝ) {k : Fin np}
    (hk : n ≤ ⌊(W : ℝ) * τ k⌋₊) (x : ProbedPath W np) (z : Fin 2 × Fin W) :
    probeFrame b E W n τ m x z k = 0 := by
  simp [probeFrame, Matrix.mul_apply, probeColumns_dead τ m hk]

/-- **The closed `𝒦` entry `(k, l)` vanishes at every length `n ≤ ⌊Wτ_k⌋` or `n ≤ ⌊Wτ_l⌋`.** -/
theorem b3ClosedKAt_dead (b E s h : ℝ) (τ m : Fin np → ℝ) {n : ℕ} {k l : Fin np}
    (hd : n ≤ ⌊(W : ℝ) * τ k⌋₊ ∨ n ≤ ⌊(W : ℝ) * τ l⌋₊) (y : ProbedPath W np × ℝ) :
    b3ClosedKAt b E s h τ m W n y k l = 0 := by
  rcases hd with hk | hl
  · simp [b3ClosedKAt, complexSourceK, Matrix.mul_apply, Matrix.conjTranspose_apply,
      probeColumns_dead τ m hk, probeFrame_dead b E τ m hk]
  · simp [b3ClosedKAt, complexSourceK, Matrix.mul_apply, probeColumns_dead τ m hl,
      probeFrame_dead b E τ m hl]

/-- **The stopped step of a dead entry vanishes** (`i + 1 ≤` a birth index). -/
theorem kStopStep_dead (b E s h : ℝ) (τ m : Fin np → ℝ) {K : ℕ} (R : ℝ) (i : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (ij : Fin np × Fin np)
    (hd : i + 1 ≤ ⌊(W : ℝ) * τ ij.1⌋₊ ∨ i + 1 ≤ ⌊(W : ℝ) * τ ij.2⌋₊) :
    kStopStep b E s h τ m R W i Vs ij = 0 := by
  funext y
  have h1 := b3ClosedKAt_dead b E s h τ m hd y
  have h0 := b3ClosedKAt_dead b E s h τ m (n := i) (k := ij.1) (l := ij.2)
    (hd.imp (fun h => by omega) (fun h => by omega)) y
  by_cases hy : y ∈ b3Alive b E s h τ m R W i Vs
  · simp only [kStopStep, Set.indicator_of_mem hy, h1, h0, sub_zero, Pi.zero_apply]
  · simp only [kStopStep, Set.indicator_of_notMem hy, Pi.zero_apply]

/-!
## The closed input
-/

/-- The closed exact update form of the stopped step `i` of entry `ij` (on the closed path):
`u, v, X` Borel functions of the past at `i`, the probes and the phase, `‖u‖, ‖v‖ ≤ Cf`, `X`
passive a.e., and `Z_i = u*Δ(X, F_i)v` a.e. -/
def ClosedStepForm (b E s h : ℝ) (τ m : Fin np → ℝ) {K : ℕ} (R : ℝ) (W i : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (ij : Fin np × Fin np)
    (Cf : ℝ) (u v : ProbedPath W np × ℝ → Fin W → ℂ)
    (X : ProbedPath W np × ℝ → Matrix (Fin W) (Fin W) ℂ) : Prop :=
  Measurable u ∧ Measurable v ∧ Measurable X ∧
    (∀ y, u (b3Ext W i y) = u y) ∧ (∀ y, v (b3Ext W i y) = v y) ∧
    (∀ y, X (b3Ext W i y) = X y) ∧ (∀ y, vecNorm (u y) ≤ Cf) ∧ (∀ y, vecNorm (v y) ≤ Cf) ∧
    (∀ᵐ y ∂closedLaw b W np, (passiveY (X y)).PosSemidef) ∧
    kStopStep b E s h τ m R W i Vs ij =ᵐ[closedLaw b W np]
      fun y => bilinear (u y) (freshDelta b E (X y) (freshSample W i y.1.1)) (v y)

/-- The closed `δ₀` jet in `L⁴` (the passive jet moments at the closed input, `p = 4`):
`∫δ₀(X)⁴ ≤ Cj/W⁴`. -/
def ClosedJetL4 (b E : ℝ) (W np : ℕ) (Cj : ℝ)
    (X : ProbedPath W np × ℝ → Matrix (Fin W) (Fin W) ℂ) : Prop :=
  ∫⁻ y, ENNReal.ofReal (jetDistance0 b E (X y)) ^ 4 ∂closedLaw b W np ≤
    ENNReal.ofReal (Cj / (W : ℝ) ^ 4)

/-- **`ClosedKMeanInput`** (on the closed path, at the closed input): for every admissible frame
and trace level, eventually in `W`, at every non-birth step at which the entry is alive, the
closed exact update form holds with an input that has the closed jet in `L⁴`, uniformly. -/
def ClosedKMeanInput : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R : ℝ, ∃ Cf Cj : ℝ, ∀ᶠ W in atTop,
      ∀ ij : Fin np × Fin np, ∀ i ∈ genNoBirthSteps s T τ W,
        ⌊(W : ℝ) * τ ij.1⌋₊ < i + 1 → ⌊(W : ℝ) * τ ij.2⌋₊ < i + 1 →
        ∃ (u v : ProbedPath W np × ℝ → Fin W → ℂ)
          (X : ProbedPath W np × ℝ → Matrix (Fin W) (Fin W) ℂ),
          ClosedStepForm b E s h τ m R W i (Vs W) ij Cf u v X ∧ ClosedJetL4 b E W np Cj X

/-!
## The closed mean
-/

/-- **The `L⁴` mean shape of the closed stopped step** from the closed input. -/
theorem kStopMeanForm4_of_closed (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hC : ClosedKMeanInput) : KStopMeanForm4 := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨hb0, hb, hE1, hE2, -⟩ := hF.1
  obtain ⟨Cm, W₀, hCm, hmean⟩ := ae_norm_condExp_bilinear_fresh_le hGA hLp hb0 hb hE1 hE2
  obtain ⟨Cf, Cj, hev⟩ := hC b E np τ m T s h K Vs hF R
  set C := max (Cm * Cf ^ 2) (max Cj 0) with hCdef
  have hC0 : 0 ≤ C := le_max_of_le_right (le_max_right _ _)
  refine ⟨C, hC0, ?_⟩
  filter_upwards [hev, eventually_ge_atTop W₀] with W hW hW0 i hi ij
  by_cases hlive : ⌊(W : ℝ) * τ ij.1⌋₊ < i + 1 ∧ ⌊(W : ℝ) * τ ij.2⌋₊ < i + 1
  · obtain ⟨u, v, X, ⟨hu, hv, hX, hu', hv', hX', hub, hvb, hXp, hEq⟩, hJ⟩ :=
      hW ij i hi hlive.1 hlive.2
    refine ⟨fun y => ENNReal.ofReal (jetDistance0 b E (X y)), hJ.trans
      (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
        ((le_max_left Cj 0).trans (le_max_right _ _)) (by positivity))), ?_⟩
    have hce : kStopMean b E s h τ m R W i (Vs W) ij =ᵐ[closedLaw b W np]
        (closedLaw b W np)[fun y => bilinear (u y) (freshDelta b E (X y)
          (freshSample W i y.1.1)) (v y) | b3Sigma W i np] := condExp_congr_ae hEq
    filter_upwards [hce, hmean W np hW0 i Cf hu hv hX hu' hv' hX' hub hvb hXp] with y hy1 hy2
    rw [hy1, ← ofReal_norm]
    have hj0 : 0 ≤ jetDistance0 b E (X y) := norm_nonneg _
    calc ENNReal.ofReal ‖(closedLaw b W np)[fun y => bilinear (u y) (freshDelta b E (X y)
          (freshSample W i y.1.1)) (v y) | b3Sigma W i np] y‖ ≤
          ENNReal.ofReal (Cm * Cf ^ 2 * (jetDistance0 b E (X y) + (W : ℝ)⁻¹)) :=
          ENNReal.ofReal_le_ofReal hy2
      _ = ENNReal.ofReal (Cm * Cf ^ 2) *
          (ENNReal.ofReal (jetDistance0 b E (X y)) + ENNReal.ofReal (1 / (W : ℝ))) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add hj0 (by positivity),
            one_div]
      _ ≤ ENNReal.ofReal C *
          (ENNReal.ofReal (jetDistance0 b E (X y)) + ENNReal.ofReal (1 / (W : ℝ))) := by
          gcongr
          exact le_max_left _ _
  · refine ⟨0, by simp, Eventually.of_forall fun y => ?_⟩
    have hd : i + 1 ≤ ⌊(W : ℝ) * τ ij.1⌋₊ ∨ i + 1 ≤ ⌊(W : ℝ) * τ ij.2⌋₊ := by
      rw [not_and_or, not_lt, not_lt] at hlive
      exact hlive
    simp only [kStopMean, kStopStep_dead b E s h τ m R i (Vs W) ij hd, condExp_zero,
      Pi.zero_apply, enorm_zero]
    exact zero_le

/-- **`KStopMeanSum` from the closed input.** -/
theorem kStopMeanSum_of_closed (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hC : ClosedKMeanInput) : KStopMeanSum :=
  kStopMeanSum_of_form4 (kStopMeanForm4_of_closed hGA hLp hC)

/-- **`GenKMeanForm` from the closed input.** -/
theorem genKMeanForm_of_closed (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hC : ClosedKMeanInput) : GenKMeanForm :=
  genKMeanForm_of_form4 (kStopMeanForm4_of_closed hGA hLp hC)

/-!
## The maximal correction moment
-/

/-- **`ComplexKCorrMomentMax` from the maximal unclosed and closed moments** (Minkowski under the
supremum, `corr = 𝒦 − 𝒦_cl`). Converse of `complexKStoppedMomentMax_of_corr`. -/
theorem complexKCorrMomentMax_of_max (hU : KUnclosedMax) (hK : ComplexKStoppedMomentMax) :
    ComplexKCorrMomentMax := by
  intro b E np τ m T s h K Vs hF R
  obtain ⟨C₁, hC₁⟩ := hK b E np τ m T s h K Vs hF R
  obtain ⟨C₀, hC₀⟩ := hU b E np τ m T hF.1 s
  refine ⟨8 * max C₁ 0 + 8 * max C₀ 0, ?_⟩
  filter_upwards [hC₁, hC₀] with W hW1 hW0 ij
  set S := Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊
  have hpt : ∀ y, (⨆ j ∈ S, (b3Alive b E s h τ m R W j (Vs W)).indicator
      (fun y => ‖b3KCorrAt b E s h τ m W (j + 1) y ij.1 ij.2‖ₑ ^ 4) y) ≤
      8 * (⨆ j ∈ S, (b3Alive b E s h τ m R W j (Vs W)).indicator
        (fun y => ‖b3ClosedKAt b E s h τ m W (j + 1) y ij.1 ij.2‖ₑ ^ 4) y) +
      8 * ⨆ j ∈ S, ‖complexSourceK b E W (j + 1) τ m y.1 ij.1 ij.2‖ₑ ^ 4 := by
    intro y
    refine iSup₂_le fun j hj => (indicator_kCorr_le _ b E s h τ m (j + 1) ij.1 ij.2 y).trans ?_
    gcongr
    · exact le_iSup₂ (f := fun j (_ : j ∈ S) => (b3Alive b E s h τ m R W j (Vs W)).indicator
        (fun y => ‖b3ClosedKAt b E s h τ m W (j + 1) y ij.1 ij.2‖ₑ ^ 4) y) j hj
    · exact le_iSup₂ (f := fun j (_ : j ∈ S) =>
        ‖complexSourceK b E W (j + 1) τ m y.1 ij.1 ij.2‖ₑ ^ 4) j hj
  have hg : Measurable fun y : ProbedPath W np × ℝ =>
      8 * ⨆ j ∈ S, ‖complexSourceK b E W (j + 1) τ m y.1 ij.1 ij.2‖ₑ ^ 4 :=
    (Measurable.iSup fun j => Measurable.iSup fun _ =>
      (measurable_enorm_complexSourceK_pow b E (j + 1) τ m ij.1 ij.2).comp
        measurable_fst).const_mul _
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_add_right _ hg, lintegral_const_mul' _ _ (by norm_num),
    lintegral_const_mul' _ _ (by norm_num)]
  have e1 := (hW1 ij).trans (ENNReal.ofReal_le_ofReal (le_max_left C₁ 0))
  have e0 := (hW0 ij).trans (ENNReal.ofReal_le_ofReal (le_max_left C₀ 0))
  calc _ ≤ 8 * ENNReal.ofReal (max C₁ 0) + 8 * ENNReal.ofReal (max C₀ 0) := by gcongr
    _ = ENNReal.ofReal (8 * max C₁ 0 + 8 * max C₀ 0) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
        norm_num

/-- **`ComplexKCorrMomentMax` from the stopped moments and the unclosed per-step estimates.** -/
theorem complexKCorrMomentMax_of_parts (hR : RawTagMoments) (hUS : KUncStepFour)
    (hUE : KUncMeanSum) (hS : KStopStepFour) (hE : KStopMeanSum) (hB : KStopBirthSum) :
    ComplexKCorrMomentMax :=
  complexKCorrMomentMax_of_max (kUnclosedMax_of_parts hR hUS hUE)
    (complexKStoppedMomentMax_of_parts (targetMartMax_holds hS) hE hB)

/-- **`ComplexKCorrMomentMax` with the closed mean from the closed input** and the unclosed means
in `L⁴` mean shape. -/
theorem complexKCorrMomentMax_of_closed (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hR : RawTagMoments) (hUS : KUncStepFour) (hUT : KUncMeanForm4)
    (hS : KStopStepFour) (hC : ClosedKMeanInput) (hB : KStopBirthSum) : ComplexKCorrMomentMax :=
  complexKCorrMomentMax_of_parts hR hUS (kUncMeanSum_of_form4 hUT) hS
    (kStopMeanSum_of_closed hGA hLp hC) hB

/-!
## An alternative argument at fixed `j` (stated only)
-/

/-- **`RieszConjugateL4`: M. Riesz / Pichorides at `p = 4` on the circle** (not in Mathlib):
for `f` analytic on a neighbourhood of the closed unit disk with `f(0) = 0`,
`E_θ|f(e^{iθ})|⁴ ≤ C E_θ|Im f(e^{iθ})|⁴` under the uniform phase. Applied path by path to
`f(z) = corr(z)` (analytic, `corr(0) = 0`, `Im corr = η(M_cl − M)` on `|z| = 1` for diagonal
entries, polarization off the diagonal), it bounds `E_θ|corr_j|⁴` at each fixed `j` by phase
moments of the closed Gram trace. Not used by the theorems above. -/
def RieszConjugateL4 : Prop :=
  ∃ C : ℝ, ∀ f : ℂ → ℂ, AnalyticOnNhd ℂ f (Metric.closedBall 0 1) → f 0 = 0 →
    ∫⁻ θ, ‖f (phase θ)‖ₑ ^ 4 ∂phaseLaw ≤
      ENNReal.ofReal C * ∫⁻ θ, ‖(f (phase θ)).im‖ₑ ^ 4 ∂phaseLaw

end BlockBand.SourceProcess.PhysApprox.B3
