module

public import BlockBand.Native.CEH.ETH.ExtractionFixedPoint
public import BlockBand.Native.CEH.Flow.Law
public import BlockBand.Palm.RelativeLocalizationAdapter

/-!
# CEH ETH: law transport for the fixed-point `θ = 1` bound

Law transport and assembly. CEH = Cipolloni–Erdős–Henheik, arXiv:2607.02446v2.

## Main results

* `ZigImChainBound`: the named intermediate statement: the order-one
  bound (4.4) for the positive chain `⟨Im G₁ A° Im G₂ A°*⟩` (the `Im G A Im G` chain of CEH (7.8))
  at fixed deterministic pairs with `θ(z₁, z₂) = 1`, for the sample `F + G_s` of an **arbitrary**
  Hermitian Brownian motion `G` on an arbitrary probability space, uniformly in that space.
  It is never a hypothesis of `externalETH_holds`.
* `externalETH_of_zigImChainBound : ZigImChainBound → Inputs.ExternalETH`, composed with
  `externalETH_of_fixedPointThetaOne`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.ETH

open MeasureTheory Set
open CEHNative.BlockBand CEHNative.BlockBand.External.CEH
open BlockBand.Internal.Contracts.Transmission
open scoped Matrix Matrix.Norms.L2Operator ENNReal NNReal

/-- **The zig bound for the positive imaginary chain on `θ = 1` pairs, on an arbitrary Hermitian
Brownian space** (an intermediate statement, never a hypothesis of `externalETH_holds`).

* *Measure.* `Q`, any probability measure on any `Ω : Type` carrying a filtration `𝓖` for which
  `G` is a Hermitian Brownian motion; the event is
  `N^ε ≤ ‖⟨Im (F + G_s - z₁)⁻¹ A° Im (F + G_s - z₂)⁻¹ A°*⟩‖` (normalized trace, matrix imaginary
  part `(X - Xᴴ)/(2i)`, `A° = cehETHRegularizedObservable s Mf z₁ z₂ J`).
* *Time packaging.* The window variable `s : ℝ` is used as the Brownian time
  `Real.toNNReal s : ℝ≥0`; since `s ≥ sLo > 0`, `(Real.toNNReal s : ℝ) = s`, so `G` is evaluated at
  exactly time `s` (law `GUE_N(s/N)`), and no proof term is carried inside the statement.
* *Window hypotheses and quantifiers.* Exactly those of `FixedPointPositiveChainLawThetaOne`
  (deformation bound `‖F‖ ≤ C N^κ √s`, MDE branch, regular boundary window at `E₀`, real parts
  in `(E₀ - r, E₀ + r)`, heights in `[N^(ε₀-1), N^(ε₁-1)]`, `θ = 1`, `J` Hermitian, `‖J‖ ≤ 1`).
* *Uniformity.* `N₀` depends only on `κ, C, sLo, sHi, r, c, K, ε₀, ε₁, ε, D`; for `N ≥ N₀` the
  bound `N^(-D)` holds uniformly in `s, F, Mf, E₀, z₁, z₂, J` **and** in the Brownian space
  `(Ω, Q, 𝓖, G)`. -/
def ZigImChainBound : Prop :=
  ∀ κ C : ℝ, 0 ≤ κ → 0 < C →
  ∀ sLo sHi : ℝ, 0 < sLo → sLo ≤ sHi →
  ∀ r c K : ℝ, 0 < r → 0 < c → 0 < K →
  ∀ ε₀ ε₁ : ℝ, 0 < ε₀ → ε₀ ≤ ε₁ → ε₁ < 1 →
  ∀ ε D : ℝ, 0 < ε → 0 < D →
  ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ s : ℝ, sLo ≤ s → s ≤ sHi →
    ∀ F : HermitianMatrix (Fin N), LocalETHDeformationBound κ C s F.1 →
    ∀ Mf : ℂ → LocalETHMatrix N, IsLocalETHMDEBranch s F.1 Mf →
    ∀ E₀ : ℝ, LocalETHRegularBoundaryWindow s Mf E₀ r c K →
    ∀ z₁ z₂ : ℂ,
      z₁.re ∈ Ioo (E₀ - r) (E₀ + r) → z₂.re ∈ Ioo (E₀ - r) (E₀ + r) →
      (N : ℝ) ^ (ε₀ - 1) ≤ z₁.im → z₁.im ≤ (N : ℝ) ^ (ε₁ - 1) →
      (N : ℝ) ^ (ε₀ - 1) ≤ z₂.im → z₂.im ≤ (N : ℝ) ^ (ε₁ - 1) →
      regularizationCoefficient (Real.sqrt s : ℂ) (Mf z₁) (Mf z₂)ᴴ = 1 →
    ∀ J : LocalETHMatrix N, J.IsHermitian → ‖J‖ ≤ 1 →
    ∀ {Ω : Type} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
      (𝓖 : MeasureTheory.Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
      (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ), IsHermitianBrownian Q 𝓖 N G →
      Q {ω | (N : ℝ) ^ ε ≤ ‖cehPositiveChain (F.1 + G (Real.toNNReal s) ω) z₁ z₂
          (cehETHRegularizedObservable s Mf z₁ z₂ J)‖} ≤
        ENNReal.ofReal ((N : ℝ) ^ (-D))

/-!
## Measurability of the bad event
-/

theorem measurable_cehHermitianResolvent {N : ℕ} (z : ℂ) :
    Measurable (fun K : Matrix (Fin N) (Fin N) ℂ => cehHermitianResolvent K z) := by
  refine BlockBand.Palm.MomentFlow.measurable_matrix_inv.comp ?_
  apply Measurable.of_eval_matrix
  intro i j
  simp only [Matrix.sub_apply]
  exact (Matrix.measurable_apply (i := i) (j := j)).sub measurable_const

/-- The matrix imaginary part `X ↦ (X - Xᴴ)/(2i)` is continuous. -/
theorem continuous_matrixImaginaryPart {N : ℕ} :
    Continuous (matrixImaginaryPart : LocalETHMatrix N → LocalETHMatrix N) := by
  unfold matrixImaginaryPart
  fun_prop

/-- The chain as a function of the two resolvents is continuous. -/
theorem continuous_cehPositiveChainOfResolvents {N : ℕ} (A : LocalETHMatrix N) :
    Continuous (fun p : LocalETHMatrix N × LocalETHMatrix N =>
      NTrace (matrixImaginaryPart p.1 * A * matrixImaginaryPart p.2 * Aᴴ)) := by
  have h := continuous_matrixImaginaryPart (N := N)
  unfold NTrace
  exact continuous_const.mul
    ((((h.comp continuous_fst |>.matrix_mul continuous_const).matrix_mul
      (h.comp continuous_snd)).matrix_mul continuous_const).matrix_trace)

theorem measurable_cehPositiveChainOfResolvents {N : ℕ} (A : LocalETHMatrix N) :
    Measurable (fun p : LocalETHMatrix N × LocalETHMatrix N =>
      NTrace (matrixImaginaryPart p.1 * A * matrixImaginaryPart p.2 * Aᴴ)) := by
  have : SecondCountableTopology (LocalETHMatrix N) :=
    inferInstanceAs (SecondCountableTopology (Fin N → Fin N → ℂ))
  exact (continuous_cehPositiveChainOfResolvents A).measurable

/-- The positive chain `K ↦ ⟨Im (K - z₁)⁻¹ A Im (K - z₂)⁻¹ Aᴴ⟩` is measurable. -/
theorem measurable_cehPositiveChain {N : ℕ} (z₁ z₂ : ℂ) (A : LocalETHMatrix N) :
    Measurable (fun K : Matrix (Fin N) (Fin N) ℂ => cehPositiveChain K z₁ z₂ A) := by
  have h := (measurable_cehPositiveChainOfResolvents A).comp
    ((measurable_cehHermitianResolvent z₁).prodMk (measurable_cehHermitianResolvent z₂))
  unfold cehPositiveChain
  exact h

/-- The matrix-level threshold set `{K | N^ε ≤ ‖⟨Im G₁(K) A Im G₂(K) Aᴴ⟩‖}`. -/
theorem measurableSet_cehPositiveChain_ge {N : ℕ} (t : ℝ) (z₁ z₂ : ℂ) (A : LocalETHMatrix N) :
    MeasurableSet {K : Matrix (Fin N) (Fin N) ℂ | t ≤ ‖cehPositiveChain K z₁ z₂ A‖} :=
  measurableSet_le measurable_const (measurable_cehPositiveChain z₁ z₂ A).norm

theorem measurableSet_cehFixedPointPositiveChainBad {N : ℕ} (s ε : ℝ)
    (Mf : ℂ → LocalETHMatrix N) (F J : LocalETHMatrix N) (z₁ z₂ : ℂ) :
    MeasurableSet {G : HermitianMatrix (Fin N) |
      CEHFixedPointPositiveChainBad s ε Mf F J z₁ z₂ G} := by
  have h := measurableSet_le measurable_const
    (((measurable_cehPositiveChain z₁ z₂ (cehETHRegularizedObservable s Mf z₁ z₂ J)).comp
      (BlockBand.Native.CEH.Flow.measurable_const_add_matrix F)).comp
        (measurable_subtype_coe (p := fun A : Matrix (Fin N) (Fin N) ℂ => A.IsHermitian))).norm
    (f := fun _ => (N : ℝ) ^ ε)
  unfold CEHFixedPointPositiveChainBad
  exact h

/-!
## Law transport
-/

/-- **Law transport for the fixed-point bad event.** For `N > 0`, `s > 0` and any Hermitian
Brownian motion `G` on `(Ω, Q, 𝓖)`, the `gueLawFamily N (s/N)`-probability (law of `√s W`,
`W ~ GUE_N(1/N)`) of `CEHFixedPointPositiveChainBad` equals the `Q`-probability of the same event
for the sample `F + G_s` (time `Real.toNNReal s = s`). Exact identity of measures. -/
theorem gueLawFamily_fixedPointBad_eq {N : ℕ} (hN : 0 < N) {s : ℝ} (hs : 0 < s) (ε : ℝ)
    (Mf : ℂ → LocalETHMatrix N) (F : HermitianMatrix (Fin N)) (J : LocalETHMatrix N)
    (z₁ z₂ : ℂ) {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {𝓖 : MeasureTheory.Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ} (hG : IsHermitianBrownian Q 𝓖 N G) :
    (gueLawFamily N (s / N) : Measure (HermitianMatrix (Fin N)))
        {W | CEHFixedPointPositiveChainBad s ε Mf F.1 J z₁ z₂ W} =
      Q {ω | (N : ℝ) ^ ε ≤ ‖cehPositiveChain (F.1 + G (Real.toNNReal s) ω) z₁ z₂
          (cehETHRegularizedObservable s Mf z₁ z₂ J)‖} := by
  have hT := measurableSet_cehPositiveChain_ge ((N : ℝ) ^ ε) z₁ z₂
    (cehETHRegularizedObservable s Mf z₁ z₂ J)
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hsq : Real.sqrt ((N : ℝ) * (s / N)) = Real.sqrt (Real.toNNReal s : ℝ) := by
    rw [Real.coe_toNNReal _ hs.le, mul_div_cancel₀ _ hN']
  have hmap : (gueLawFamily N (s / N) : Measure (HermitianMatrix (Fin N))) =
      (BlockBand.Internal.Contracts.Inputs.gueSourceLaw N).map (scaledSource N (s / N)) := rfl
  have hshift := BlockBand.Native.CEH.Flow.hermitianBrownian_shift_measure_eq hG
    (Real.toNNReal s) F.1 hT
  have hpre := Measure.map_apply (μ := BlockBand.Internal.Contracts.Inputs.gueSourceLaw N)
    (measurable_scaledSource N (s / N))
    (measurableSet_cehFixedPointPositiveChainBad s ε Mf F.1 J z₁ z₂)
  rw [hmap, hpre]
  refine Eq.trans ?_ hshift
  refine congrArg _ (Set.ext fun W => ?_)
  show (N : ℝ) ^ ε ≤ ‖cehPositiveChain (F.1 + ((Real.sqrt ((N : ℝ) * (s / N)) : ℝ) : ℂ) • W.1)
      z₁ z₂ (cehETHRegularizedObservable s Mf z₁ z₂ J)‖ ↔
    (N : ℝ) ^ ε ≤ ‖cehPositiveChain (F.1 + ((Real.sqrt (Real.toNNReal s : ℝ) : ℝ) : ℂ) • W.1)
      z₁ z₂ (cehETHRegularizedObservable s Mf z₁ z₂ J)‖
  rw [hsq]

/-!
## Assembly
-/

/-- **The zig bound on an arbitrary Brownian space gives the fixed-point `θ = 1` law for
`gueLawFamily`.** Instantiates `ZigImChainBound` on the concrete Hermitian Brownian space
(`flowBM N` under the probability measure `flowLaw N 0`, filtration `flowFiltration N`,
`flowBM_isHermitianBrownian`) and transports the law by `gueLawFamily_fixedPointBad_eq`. The
cutoff is `max N₀ 1` (the transport uses `N > 0`); `s > 0` follows from `s ≥ sLo > 0`. -/
theorem fixedPointThetaOne_of_zigImChainBound (h : ZigImChainBound) :
    FixedPointPositiveChainLawThetaOne gueLawFamily := by
  intro κ C hκ hC sLo sHi hsLo hsHi r c K hr hc hK ε₀ ε₁ h0 h01 h1 ε D hε hD
  obtain ⟨N₀, hN₀⟩ := h κ C hκ hC sLo sHi hsLo hsHi r c K hr hc hK ε₀ ε₁ h0 h01 h1 ε D hε hD
  refine ⟨max N₀ 1, fun N hN s hs hs' F hF Mf hMf E₀ hreg z₁ z₂ h1r h2r h1l h1u h2l h2u hθ J
    hJ hJn => ?_⟩
  have hN0 : 0 < N := lt_of_lt_of_le Nat.one_pos (le_of_max_le_right hN)
  have hs0 : 0 < s := lt_of_lt_of_le hsLo hs
  have hG := BlockBand.Palm.RelativeLocalization.flowBM_isHermitianBrownian (N := N) 0
  rw [gueLawFamily_fixedPointBad_eq hN0 hs0 ε Mf F J z₁ z₂ hG]
  exact hN₀ N (le_of_max_le_left hN) s hs hs' F hF Mf hMf E₀ hreg z₁ z₂ h1r h2r h1l h1u h2l
    h2u hθ J hJ hJn _ _ _ hG

/-- **Assembly: `ZigImChainBound → Inputs.ExternalETH`**, by
`fixedPointThetaOne_of_zigImChainBound` and `externalETH_of_fixedPointThetaOne`. -/
theorem externalETH_of_zigImChainBound (h : ZigImChainBound) :
    BlockBand.Internal.Contracts.Inputs.ExternalETH :=
  externalETH_of_fixedPointThetaOne (fixedPointThetaOne_of_zigImChainBound h)

end BlockBand.Native.CEH.ETH
