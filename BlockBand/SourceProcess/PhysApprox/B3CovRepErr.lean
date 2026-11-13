module

public import BlockBand.SourceProcess.PhysApprox.B3CovRepDecay

/-!
# `CovErrMoments` for the closed layer error scale, from closed jets

The hypothesis `CovErrMoments e` asks, for every `n ≥ 1`, `‖1_{A_j} e_j^n‖₄ ≤ (C_n/W)^n`. For
the concrete `e = b3CovErr = δ₀(X_cl) + δ₁(X_cl) + g(X_cl)/W + W⁻¹` it is reduced to three
`L^p` statements about the closed near Schur matrix `X_cl = b3ClosedX`:

* `ClosedErrLp e` (any field): `‖1_{A_j} e_j‖_p ≤ C_p/W` for every `p ≥ 1`;
* **`covErrMoments_of_lp : ClosedErrLp e → CovErrMoments e`** (`‖1_A e^n‖₄ = ‖1_A e‖_{4n}^n`);
* the hypotheses `ClosedJet0Lp` (`‖1_{A_j}δ₀(X_cl,j)‖_p ≤ C_p/W`), `ClosedJet1Lp` (the same for
  `δ₁` at the stationary jet) and `ClosedCondLp` (`‖1_{A_j}g(X_cl,j)‖_p ≤ C_p`, the closed
  conductance; heuristically `g_cl ≤ #retained ≤ K` on the cap event);
* **`closedErrLp_of_jets`** (Minkowski): the three hypotheses give `ClosedErrLp b3CovErr`;
  hence **`covErrMoments_b3CovErr`**.

The three hypotheses are required for every `p`, at every no-birth step from `n_s` on.
`ClosedJet0Lp` at `p = 4` is the closed jet bound `ClosedJetL4` at the closed input. A finite
`eLpNorm` bound includes a.e. strong measurability.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3

open MeasureTheory ProbabilityTheory Filter Topology Matrix Finset
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.Layers
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open BlockBand.Transmission.Bridge
open scoped NNReal ENNReal ComplexConjugate

/-!
## From `L^p` bounds to the moments
-/

/-- `‖1_{A_j} e_j‖_p ≤ C_p/W` for every `p ≥ 1`, eventually, at every no-birth step. -/
def ClosedErrLp (e : CovField) : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R p : ℝ, 1 ≤ p → ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W,
      eLpNorm ((b3Alive b E s h τ m R W j (Vs W)).indicator (e b E np τ m s h K W (Vs W) j))
          (ENNReal.ofReal p) (closedLaw b W np) ≤ ENNReal.ofReal (C / W)

/-- **`ClosedErrLp e ⇒ CovErrMoments e`**: `‖1_A e^n‖₄ = ‖1_A e‖_{4n}^n ≤ (C_{4n}/W)^n`. -/
theorem covErrMoments_of_lp {e : CovField} (h : ClosedErrLp e) : CovErrMoments e := by
  intro b E np τ m T s h' K Vs hFD R n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨C, hC, hev⟩ := h b E np τ m T s h' K Vs hFD R (4 * n) (by linarith)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hev] with W hW j hj
  set μ := closedLaw b W np
  set A := b3Alive b E s h' τ m R W j (Vs W)
  set f := A.indicator (e b E np τ m s h' K W (Vs W) j) with hfdef
  have hb : eLpNorm f (ENNReal.ofReal (4 * n)) μ ≤ ENNReal.ofReal (C / W) := hW j hj
  have hfm : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_eLpNorm_ne_top (hb.trans_lt ENNReal.ofReal_lt_top).ne
  rw [← cov_indicator_pow A _ hn, ← hfdef]
  have hfun : (fun y => ‖f y‖ ^ (n : ℝ)) = fun y => ‖f y‖ ^ n :=
    funext fun y => Real.rpow_natCast _ _
  have hcongr : eLpNorm (fun y => f y ^ n) 4 μ = eLpNorm (fun y => ‖f y‖ ^ (n : ℝ)) 4 μ := by
    rw [hfun]
    refine eLpNorm_congr_norm_ae (hfm.pow n) (hfm.norm.pow n) (ae_of_all _ fun y => ?_)
    rw [norm_pow, norm_pow, norm_norm]
  have h4 : (4 : ℝ≥0∞) * ENNReal.ofReal n = ENNReal.ofReal (4 * n) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  have hCW : 0 ≤ C / W := div_nonneg hC (Nat.cast_nonneg W)
  rw [hcongr, eLpNorm_norm_rpow f hfm (by positivity : (0 : ℝ) < n), h4]
  calc eLpNorm f (ENNReal.ofReal (4 * n)) μ ^ (n : ℝ) ≤ ENNReal.ofReal (C / W) ^ (n : ℝ) :=
        ENNReal.rpow_le_rpow hb (by positivity)
    _ = ENNReal.ofReal ((C / W) ^ n) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hCW (by positivity), Real.rpow_natCast]

/-!
## The closed jets
-/

/-- **The closed `δ₀` jet in every `L^p`** (at the closed input):
`‖1_{A_j}δ₀(X_cl,j)‖_p ≤ C_p/W`, eventually, at every no-birth step. -/
def ClosedJet0Lp : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R p : ℝ, 1 ≤ p → ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W,
      eLpNorm ((b3Alive b E s h τ m R W j (Vs W)).indicator
          (fun y => jetDistance0 b E (b3ClosedX b E s h τ m W j y)))
          (ENNReal.ofReal p) (closedLaw b W np) ≤ ENNReal.ofReal (C / W)

/-- **The closed `δ₁` jet in every `L^p`** (at the closed input):
`‖1_{A_j}δ₁(X_cl,j)‖_p ≤ C_p/W` at the stationary jet `b3Jet`. -/
def ClosedJet1Lp : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R p : ℝ, 1 ≤ p → ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W,
      eLpNorm ((b3Alive b E s h τ m R W j (Vs W)).indicator
          (fun y => jetDistance1 b E (b3Jet b E) (b3ClosedX b E s h τ m W j y)))
          (ENNReal.ofReal p) (closedLaw b W np) ≤ ENNReal.ofReal (C / W)

/-- **The closed conductance in every `L^p`** (heuristically `g_cl ≤ #retained ≤ K` on the cap
event): `‖1_{A_j}g(X_cl,j)‖_p ≤ C_p`. -/
def ClosedCondLp : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ R p : ℝ, 1 ≤ p → ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ W in atTop, ∀ j ∈ genNoBirthSteps s T τ W,
      eLpNorm ((b3Alive b E s h τ m R W j (Vs W)).indicator
          (fun y => conductanceOf
            (passiveTransmission b E (b3ClosedX b E s h τ m W j y))))
          (ENNReal.ofReal p) (closedLaw b W np) ≤ ENNReal.ofReal C

/-- The alive set is null-measurable on an admissible frame. -/
theorem nullMeasurableSet_b3Alive {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2)
    (s h : ℝ) {np K : ℕ} (τ m : Fin np → ℝ) (R : ℝ) (W j : ℕ)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} (hV : Measurable Vs) :
    NullMeasurableSet (b3Alive b E s h τ m R W j Vs) (closedLaw b W np) :=
  (measurableSet_b3AliveM b E s h τ m R W j hV).nullMeasurableSet.congr
    (b3Alive_ae_eq hb hE1 hE2 s h τ m R W j Vs).symm

/-- Minkowski for four real functions. -/
theorem eLpNorm_add4_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (f0 f1 f2 f3 : α → ℝ) :
    eLpNorm (f0 + f1 + f2 + f3) p μ ≤
      eLpNorm f0 p μ + eLpNorm f1 p μ + eLpNorm f2 p μ + eLpNorm f3 p μ := by
  have h3 := eLpNorm_add_le (μ := μ) (f := f0 + f1 + f2) (g := f3) hp
  have h2 := eLpNorm_add_le (μ := μ) (f := f0 + f1) (g := f2) hp
  have h1 := eLpNorm_add_le (μ := μ) (f := f0) (g := f1) hp
  calc eLpNorm (f0 + f1 + f2 + f3) p μ ≤ eLpNorm (f0 + f1 + f2) p μ + eLpNorm f3 p μ := h3
    _ ≤ eLpNorm (f0 + f1) p μ + eLpNorm f2 p μ + eLpNorm f3 p μ := by gcongr
    _ ≤ _ := by gcongr

/-- The pointwise split of `1_A e` into its four terms. -/
theorem indicator_b3CovErr_split (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (s h : ℝ) (K W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (j : ℕ)
    (A : Set (ProbedPath W np × ℝ)) :
    A.indicator (b3CovErr b E np τ m s h K W Vs j) =
      A.indicator (fun y => jetDistance0 b E (b3ClosedX b E s h τ m W j y)) +
        A.indicator (fun y => jetDistance1 b E (b3Jet b E)
          (b3ClosedX b E s h τ m W j y)) +
        ((W : ℝ)⁻¹ • A.indicator (fun y => conductanceOf
          (passiveTransmission b E (b3ClosedX b E s h τ m W j y)))) +
        A.indicator (fun _ => (W : ℝ)⁻¹) := by
  funext y
  by_cases hy : y ∈ A
  · rw [Pi.add_apply, Pi.add_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Set.indicator_of_mem hy, Set.indicator_of_mem hy, Set.indicator_of_mem hy,
      Set.indicator_of_mem hy, Set.indicator_of_mem hy]
    simp only [b3CovErr, b3LayerErrX, div_eq_inv_mul]
  · rw [Pi.add_apply, Pi.add_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, Set.indicator_of_notMem hy,
      Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
    ring

theorem cov_err_arith {C0 C1 Cg : ℝ} {W : ℕ} (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hCg : 0 ≤ Cg) :
    ENNReal.ofReal (C0 / W) + ENNReal.ofReal (C1 / W) +
        ENNReal.ofReal (W : ℝ)⁻¹ * ENNReal.ofReal Cg + ENNReal.ofReal (W : ℝ)⁻¹ =
      ENNReal.ofReal ((C0 + C1 + Cg + 1) / W) := by
  have hWi : (0 : ℝ) ≤ (W : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg W)
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  rw [← ENNReal.ofReal_mul hWi, ← ENNReal.ofReal_add (div_nonneg hC0 hW0) (div_nonneg hC1 hW0),
    ← ENNReal.ofReal_add (add_nonneg (div_nonneg hC0 hW0) (div_nonneg hC1 hW0))
      (mul_nonneg hWi hCg),
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg (div_nonneg hC0 hW0) (div_nonneg hC1 hW0))
      (mul_nonneg hWi hCg)) hWi]
  congr 1
  ring

/-- **`ClosedErrLp b3CovErr` from the three closed jet estimates** (Minkowski). -/
theorem closedErrLp_of_jets (h0 : ClosedJet0Lp) (h1 : ClosedJet1Lp) (hg : ClosedCondLp) :
    ClosedErrLp b3CovErr := by
  intro b E np τ m T s h K Vs hFD R p hp
  obtain ⟨hb0, hb, hE1, hE2, -⟩ := hFD.1
  obtain ⟨C0, hC0, hev0⟩ := h0 b E np τ m T s h K Vs hFD R p hp
  obtain ⟨C1, hC1, hev1⟩ := h1 b E np τ m T s h K Vs hFD R p hp
  obtain ⟨Cg, hCg, hevg⟩ := hg b E np τ m T s h K Vs hFD R p hp
  refine ⟨C0 + C1 + Cg + 1, by positivity, ?_⟩
  filter_upwards [hev0, hev1, hevg, hFD.2.2.2.2.2] with W hW0 hW1 hWg hVW j hj
  have hV : Measurable (Vs W) :=
    hVW.1.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  set μ := closedLaw b W np
  set A := b3Alive b E s h τ m R W j (Vs W)
  have hsplit := indicator_b3CovErr_split b E np τ m s h K W (Vs W) j A
  have hconst : eLpNorm (A.indicator (fun _ => (W : ℝ)⁻¹)) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (W : ℝ)⁻¹ := by
    refine (eLpNorm_indicator_le _
      (nullMeasurableSet_b3Alive (by linarith) hE1 hE2 s h τ m R W j hV)).trans (le_of_eq ?_)
    rw [eLpNorm_const _ (ENNReal.ofReal_pos.mpr (by linarith)).ne' (NeZero.ne μ), measure_univ,
      ENNReal.one_rpow, mul_one, Real.enorm_of_nonneg (by positivity)]
  have hg' : eLpNorm ((W : ℝ)⁻¹ • A.indicator (fun y => conductanceOf
      (passiveTransmission b E (b3ClosedX b E s h τ m W j y))))
      (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (W : ℝ)⁻¹ * ENNReal.ofReal Cg := by
    rw [eLpNorm_const_smul, Real.enorm_of_nonneg (by positivity)]
    gcongr
    exact hWg j hj
  rw [hsplit]
  refine (eLpNorm_add4_le hp1 _ _ _ _).trans ?_
  calc _ ≤ ENNReal.ofReal (C0 / W) + ENNReal.ofReal (C1 / W) +
        ENNReal.ofReal (W : ℝ)⁻¹ * ENNReal.ofReal Cg + ENNReal.ofReal (W : ℝ)⁻¹ :=
        add_le_add (add_le_add (add_le_add (hW0 j hj) (hW1 j hj)) hg') hconst
    _ = ENNReal.ofReal ((C0 + C1 + Cg + 1) / W) := cov_err_arith hC0 hC1 hCg

/-- **`CovErrMoments` for the closed layer error scale**, from the three closed jet estimates. -/
theorem covErrMoments_b3CovErr (h0 : ClosedJet0Lp) (h1 : ClosedJet1Lp) (hg : ClosedCondLp) :
    CovErrMoments b3CovErr :=
  covErrMoments_of_lp (closedErrLp_of_jets h0 h1 hg)

end BlockBand.SourceProcess.PhysApprox.B3
