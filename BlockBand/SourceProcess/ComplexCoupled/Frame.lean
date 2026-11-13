module

public import BlockBand.SourceProcess.CoupledFrames.CoupledModel2

/-!
# One born frame with deterministic probe births: hypotheses and Gram model

Setting of `CoupledFrames` with **deterministic** births: ambient space `Amb K R`,
probe columns `π = Fin np`, probe `j` born at the model time `σ_j = τ_j - s > 0` with squared norm
`v_j = d_* m_j`, `eπ = Equiv.refl`. `FrameHyp` collects, for one ambient solution `Y` from the
extended initial frame at cutoff `h`, the birth coefficient vectors `pv` and the shared birth
vectors `w`, the facts produced by the two-frame selection. `gram_model`: the Gram process of
the born frame `X = bornFrame Y` is a born Gram solution with the deterministic birth jumps, equal
a.s. at all times to `bornG`, with initial value `initialGram`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ComplexCoupled
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix Finset
open scoped NNReal ENNReal
open BlockBand.SourceProcess.FiniteDriverIntegration BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.ModelExist
open BlockBand.SourceProcess.BornUnique BlockBand.SourceProcess.CoupledFrames
open BlockBand.SourceProcess.Stochastic.GramUniqueness

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {S : Type} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ] {K R np : ℕ}

/-- The driver space of the ambient construction. -/
abbrev Dr (S : Type) (K R : ℕ) := DriverSample S (SourceNoise (Amb K R))

/-- The deterministic model birth times `σ_j = τ_j - s`. -/
def sigD {Ω : Type*} (s : ℝ) {np : ℕ} (τ : Fin np → ℝ) : Fin np → Ω → ℝ := fun j _ => τ j - s

omit [IsProbabilityMeasure μ] in
theorem measurable_sigD (s : ℝ) {np : ℕ} (τ : Fin np → ℝ) (j : Fin np) :
    Measurable[driverAugmented (κ := SourceNoise (Amb K R)) μ 0] (sigD (Ω := Dr S K R) s τ j) :=
  measurable_const

/-- The `𝓖_θ`-measurability condition on birth coefficients. -/
def BirthMeas (s : ℝ) (τ : Fin np → ℝ) {V : Type*} [TopologicalSpace V]
    (f : Fin np → Dr S K R → V) :
    Prop :=
  ∀ j, StronglyMeasurable[(isStoppingTime_of_meas0 (𝓖 := driverAugmented
    (κ := SourceNoise (Amb K R)) μ) (measurable_sigD (μ := μ) s τ j).real_toNNReal).measurableSpace]
      (f j)

/-- **Hypotheses on one frame** (produced by the two-frame selection). -/
structure FrameHyp (b E s h : ℝ) (τ m : Fin np → ℝ) (μ : Measure S) [IsProbabilityMeasure μ]
    (tq : Dr S K R → ℕ → ℝ) (Y : ℝ≥0 → Dr S K R → Matrix (Amb K R) (ExtCol K R) ℂ)
    (pv : Fin np → Dr S K R → ExtCol K R → ℂ) (w : Fin np → Dr S K R → Amb K R → ℂ) : Prop where
  tq_meas : Measurable[driverAugmented (κ := SourceNoise (Amb K R)) μ 0] tq
  tq_seq : ∀ᵐ x ∂driverLaw (κ := SourceNoise (Amb K R)) μ, IsTransmissionSequence (tq x)
  sol : IsSDESolution μ (sourceDrift (transportD0 b E) (K + R) (ambP K R))
    (sourceDiffusion (transportD0 b E) (ambP K R) (extSig K R)) (fun x => extFrame K R (tq x) h) Y
  pv_meas : BirthMeas (μ := μ) s τ pv
  w_meas : BirthMeas (μ := μ) s τ w
  good : ∀ᵐ x ∂driverLaw (κ := SourceNoise (Amb K R)) μ, ∀ k,
    Y (bτ (Equiv.refl (Fin np)) (sigD s τ) k x) x *ᵥ ba (Equiv.refl (Fin np)) pv k x = w k x
  spec : ∀ᵐ x ∂driverLaw (κ := SourceNoise (Amb K R)) μ,
    ProbeSpec (fun t x => gramPair (ambP K R) (Y t x)) (sigD s τ) (fun j => dStar b * m j) pv x

/-- The born frame of a frame. -/
abbrev bFr (s : ℝ) (τ : Fin np → ℝ) (Y : ℝ≥0 → Dr S K R → Matrix (Amb K R) (ExtCol K R) ℂ)
    (pv : Fin np → Dr S K R → ExtCol K R → ℂ) (w : Fin np → Dr S K R → Amb K R → ℂ) :
    ℝ≥0 → Dr S K R → Matrix (Amb K R) (SrcCol K (Fin np)) ℂ :=
  bornFrame (Equiv.refl (Fin np)) Y (sigD s τ) pv w

/-- The born congruence of a frame. -/
abbrev bL (s : ℝ) (τ : Fin np → ℝ) (pv : Fin np → Dr S K R → ExtCol K R → ℂ) :
    ℝ≥0 → Dr S K R → Matrix (ExtCol K R) (SrcCol K (Fin np)) ℂ :=
  bornL (mθ K (sigD s τ)) (glam K R pv)

variable {b E s h : ℝ} {τ m : Fin np → ℝ} {tq : Dr S K R → ℕ → ℝ}
  {Y : ℝ≥0 → Dr S K R → Matrix (Amb K R) (ExtCol K R) ℂ}
  {pv : Fin np → Dr S K R → ExtCol K R → ℂ} {w : Fin np → Dr S K R → Amb K R → ℂ}

theorem FrameHyp.theta_meas (_ : FrameHyp b E s h τ m μ tq Y pv w) (y : SrcCol K (Fin np)) :
    Measurable[driverAugmented (κ := SourceNoise (Amb K R)) μ 0]
      (mθ K (sigD (Ω := Dr S K R) s τ) y) := by
  rcases y with k | i
  · exact measurable_const
  · exact (measurable_sigD s τ i).real_toNNReal

theorem FrameHyp.glam_meas (H : FrameHyp b E s h τ m μ tq Y pv w) (y : SrcCol K (Fin np)) :
    StronglyMeasurable[(isStoppingTime_of_meas0 (H.theta_meas y)).measurableSpace]
      (glam K R pv y) := by
  rcases y with k | i
  · exact stronglyMeasurable_const
  · exact H.pv_meas i

theorem FrameHyp.eq_mul (H : FrameHyp b E s h τ m μ tq Y pv w) :
    ∀ᵐ x ∂driverLaw (κ := SourceNoise (Amb K R)) μ, ∀ t,
      bFr s τ Y pv w t x = Y t x * bL s τ pv t x :=
  H.good.mono fun _ hx t => bornFrame_eq (Equiv.refl (Fin np)) Y _ pv w hx t

theorem FrameHyp.rep (H : FrameHyp b E s h τ m μ tq Y pv w) :
    ∀ᵐ x ∂driverLaw (κ := SourceNoise (Amb K R)) μ,
      BornRepresents (fun t x => gramPair (ambP K R) (Y t x)) (mθ K (sigD s τ)) (glam K R pv)
        (probeJump (K := K) fun j => dStar b * m j) (sigD s τ) x :=
  H.spec.mono fun x hx => bornRepresents_probe hx fun t =>
    herm_gramPair (isNearProjection_ambP K R).1 (Y t x)

theorem dStar_pos {b : ℝ} (hb1 : b < 1 / 2) : 0 < dStar b := by
  unfold dStar; exact one_div_pos.2 (by linarith)

/-- **The Gram process of the born frame is the born Gram solution.** -/
theorem gram_model (H : FrameHyp b E s h τ m μ tq Y pv w) (hb0 : 0 < b) (hb1 : b < 1 / 2)
    (hE1 : -2 < E) (hE2 : E < 2) (hm : ∀ j, 0 ≤ m j) (hsτ : ∀ j, s < τ j) :
    IsBornGramSolution (driverLaw (κ := SourceNoise (Amb K R)) μ)
      (driverAugmented (κ := SourceNoise (Amb K R)) μ) (transportD0 b E)
      (srcSignature K (Fin np))
      (fun t _ => birthJump (fun j => τ j - s) (fun j => dStar b * m j) (t : ℝ))
      (fun t x => gramPair (ambP K R) (bFr s τ Y pv w t x)) ∧
    (∀ᵐ x ∂driverLaw (κ := SourceNoise (Amb K R)) μ, ∀ t,
      gramPair (ambP K R) (bFr s τ Y pv w t x) =
        bornG (fun t x => gramPair (ambP K R) (Y t x)) (mθ K (sigD s τ)) (glam K R pv) t x) ∧
    ∀ᵐ x ∂driverLaw (κ := SourceNoise (Amb K R)) μ,
      gramPair (ambP K R) (bFr s τ Y pv w 0 x) = initialGram K (Fin np) (tq x) h := by
  have hD0 := transportD0_pos' hb0 hE1 hE2
  have hξm := stronglyMeasurable_extFrame (R := R) H.tq_meas h
  have hξc : ∀ᵐ x ∂driverLaw (κ := SourceNoise (Amb K R)) μ,
      TwoProjection (ambP K R) (extSig K R) (extFrame K R (tq x) h) :=
    H.tq_seq.mono fun x hx => twoProjection_extFrame K R (fun k => hx.2.1 k) h
  have h𝒢 := ambient_isGramMartingaleSolution μ hD0 (isNearProjection_ambP K R)
    (isSignature_extSig K R) hξm hξc H.sol
  have hp : IsStronglyProgressive (driverAugmented (κ := SourceNoise (Amb K R)) μ)
      (fun t x => gramPair (ambP K R) (Y t x)) := fun T =>
    (continuous_gramPair _).comp_stronglyMeasurable (H.sol.1.progressive T)
  have hherm : ∀ x t, (gramPair (ambP K R) (Y t x)).1ᴴ = (gramPair (ambP K R) (Y t x)).1 ∧
      (gramPair (ambP K R) (Y t x)).2ᴴ = (gramPair (ambP K R) (Y t x)).2 := fun x t =>
    herm_gramPair (isNearProjection_ambP K R).1 (Y t x)
  have hj : ∀ f, 0 ≤ ((probeJump (K := K) (fun j => dStar b * m j) f).1.trace).re := fun f => by
    simp [probeJump, mul_nonneg (dStar_pos hb1).le (hm f)]
  have hsol := isBornGramSolution_bornG h𝒢 hp H.theta_meas H.glam_meas
    (fun t x => bornL_sig_probe t x) hj (measurable_sigD s τ) H.rep
  have hXp := isStronglyProgressive_bornFrame (Equiv.refl (Fin np)) H.sol (measurable_sigD s τ)
    H.pv_meas H.w_meas
  have heq : ∀ᵐ x ∂driverLaw (κ := SourceNoise (Amb K R)) μ, ∀ t,
      gramPair (ambP K R) (bFr s τ Y pv w t x) =
        bornG (fun t x => gramPair (ambP K R) (Y t x)) (mθ K (sigD s τ)) (glam K R pv) t x :=
    H.eq_mul.mono fun x hx t => by rw [hx t, CoupledFrames.gramPair_mul]; rfl
  refine ⟨isBornGramSolution_congr hsol (stronglyMeasurable_gram_of_prog hXp) heq, heq, ?_⟩
  filter_upwards [H.sol.2, H.spec, heq] with x hx0 hs he
  rw [he 0]
  refine bornG_zero_probe (by show gramPair _ (Y 0 x) = _; rw [hx0]) hs (hherm x) fun i hz => ?_
  have : τ i - s ≤ 0 := Real.toNNReal_eq_zero.1 hz
  linarith [hsτ i]

end BlockBand.SourceProcess.ComplexCoupled
