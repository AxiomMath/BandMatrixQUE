module

public import BlockBand.Native.ErdosRiabov.Psi.Cont
public import BlockBand.Native.ErdosRiabov.Psi.Zero
public import BlockBand.SourceProcess.Stochastic.Semimartingale.HittingTime
public import BlockBand.Native.ErdosRiabov.VS.ResolventItoGlue

/-!
# The stopping time `τ` of the zig step

Setting: `p : BlockBand.Parameters`, `N = p.n * p.W`, the VS band process
`H_t = VS.vsBandFin p t = ringMatrixFin p (Y_t - Y_0)` on `RingSample p` with the filtration
`driverAugmented μ` (any probability law `μ` of the unused old state); control data
`P : PsiData N` and thresholds `ψ^iso_k = psiI k`, `ψ^av_k = psiA k` (for the zig step,
`VSData.psiIso`, `VSData.psiAv`).

* `excess P psiI psiA t H = max_{1 ≤ k ≤ K} max(Ψ^iso_{k,t}(H) - ψ^iso_k, Ψ^av_{k,t}(H) - ψ^av_k)`;
  `0 ≤ excess` iff some `Ψ_{k,t} ≥ ψ_k` (`excess_nonneg_iff`); continuous on
  `[0,1] × {Hermitian}` (`continuousOn_excess`).
* `excessProc p P psiI psiA t = excess (t ∧ 1) H_{t ∧ 1}`: the process is constant after time `1`,
  so only `t ∈ [0,1]` is used; it has continuous paths for every sample (`continuous_excessProc`)
  and is `driverAugmented μ`-adapted (`measurable_excessProc`).
* `tau p P psiI psiA = (hitting time of [0,∞) by excessProc) ∧ 1`, built from the raw hitting
  time `Semimartingale.rawHit`: `τ = inf{t ∈ [0,1] : max_k Ψ^av_{k,t}/ψ^av_k ≥ 1 or
  max_k Ψ^iso_{k,t}/ψ^iso_k ≥ 1} ∧ 1` (for positive thresholds `Ψ ≥ ψ` iff
  `Ψ/ψ ≥ 1`). **`tau_isStoppingTime`**: `τ` is a `driverAugmented μ`-stopping time;
  `tau_eq_hitTime`: `τ` equals the first hitting time `∧ 1` on every sample;
  `excess_neg_of_lt_tau`: before `τ` all `Ψ_{k,t} < ψ_k`.
* **`tau_pos`**: `τ > 0` for every sample when all thresholds are positive, because
  `Ψ_{k,0}(H_0 = 0) = 0` (`bigPsiIso_zero`, `bigPsiAv_zero`). **Conditional** on
  `Split.ZeroStatement`, which is an explicit hypothesis of `tau_pos` and of `excessProc_zero`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Psi

open MeasureTheory Filter Topology Set
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Stochastic
open BlockBand.Native.ErdosRiabov.VS
open BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.Semimartingale
open BlockBand.Internal.Contracts.Transmission
open scoped NNReal

variable {N : ℕ}

/-- The hierarchy levels `1 ≤ k ≤ K = 8`. -/
def kRange : Finset ℕ := Finset.Icc 1 vsK

theorem kRange_nonempty : kRange.Nonempty := ⟨1, by simp [kRange, vsK]⟩

namespace PsiData

variable (P : PsiData N)

/-- `max_{1 ≤ k ≤ K} max(Ψ^iso_{k,t}(H) - ψ^iso_k, Ψ^av_{k,t}(H) - ψ^av_k)`. -/
def excess (psiI psiA : ℕ → ℝ) (t : ℝ) (H : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  kRange.sup' kRange_nonempty fun k => max (P.bigPsiIso k t H - psiI k) (P.bigPsiAv k t H - psiA k)

/-- `0 ≤ excess` iff some control quantity reaches its threshold. -/
theorem excess_nonneg_iff (psiI psiA : ℕ → ℝ) (t : ℝ) (H : Matrix (Fin N) (Fin N) ℂ) :
    0 ≤ P.excess psiI psiA t H ↔
      ∃ k ∈ kRange, psiI k ≤ P.bigPsiIso k t H ∨ psiA k ≤ P.bigPsiAv k t H := by
  unfold excess
  rw [Finset.le_sup'_iff]
  simp only [le_max_iff, sub_nonneg]

/-- `excess < 0` iff all control quantities are below their thresholds. -/
theorem excess_neg_iff (psiI psiA : ℕ → ℝ) (t : ℝ) (H : Matrix (Fin N) (Fin N) ℂ) :
    P.excess psiI psiA t H < 0 ↔
      ∀ k ∈ kRange, P.bigPsiIso k t H < psiI k ∧ P.bigPsiAv k t H < psiA k := by
  rw [← not_le, P.excess_nonneg_iff]
  push Not
  rfl

theorem continuousOn_excess (hN : 0 < N) (hW : 0 < P.W) (hz : 0 < P.z.im)
    (hS : StochasticSymm P.S) (psiI psiA : ℕ → ℝ) :
    ContinuousOn (fun q : ℝ × Matrix (Fin N) (Fin N) ℂ => P.excess psiI psiA q.1 q.2)
      (hermDomain N) := by
  unfold excess
  apply ContinuousOn.finset_sup'_apply kRange_nonempty
  intro k _
  exact continuous_max.comp_continuousOn
    (((P.continuousOn_bigPsiIso hN hW hz hS k).sub continuousOn_const).prodMk
      ((P.continuousOn_bigPsiAv hN hW hz hS k).sub continuousOn_const))

end PsiData

variable (p : BlockBand.Parameters)

/-- The excess along the VS band process, stopped at time `1`. -/
def excessProc (P : PsiData (p.n * p.W)) (psiI psiA : ℕ → ℝ) (t : ℝ≥0) (x : RingSample p) :
    ℝ :=
  P.excess psiI psiA (min t 1 : ℝ≥0) (vsBandFin p (min t 1) x)

/-- The stopping time `τ = (first time with some Ψ_{k,t} ≥ ψ_k) ∧ 1`. -/
def tau (P : PsiData (p.n * p.W)) (psiI psiA : ℕ → ℝ) (x : RingSample p) : WithTop ℝ≥0 :=
  min (rawHit (Ici (0 : ℝ)) (excessProc p P psiI psiA) x) ((1 : ℝ≥0) : WithTop ℝ≥0)

variable {p}

/-- The excess as a function of the coordinates `y` (`H = ringMatrixFin p y`). -/
theorem continuousOn_excess_coord {P : PsiData (p.n * p.W)} (hN : 0 < p.n * p.W)
    (hW : 0 < P.W) (hz : 0 < P.z.im) (hS : StochasticSymm P.S) (psiI psiA : ℕ → ℝ) :
    ContinuousOn (fun q : ℝ × (Fin (ringDim p) → ℝ) =>
      P.excess psiI psiA q.1 (ringMatrixFin p q.2)) (Icc 0 1 ×ˢ univ) := by
  have h1 := P.continuousOn_excess hN hW hz hS psiI psiA
  have h2 : Continuous fun q : ℝ × (Fin (ringDim p) → ℝ) => (q.1, ringMatrixFin p q.2) :=
    continuous_fst.prodMk ((continuous_ringMatrixFin (p := p)).comp continuous_snd)
  have h3 : MapsTo (fun q : ℝ × (Fin (ringDim p) → ℝ) => (q.1, ringMatrixFin p q.2))
      (Icc 0 1 ×ˢ univ) (hermDomain (p.n * p.W)) :=
    fun q hq => ⟨hq.1, ringMatrixFin_isHermitian q.2⟩
  have h4 : ContinuousOn ((fun q : ℝ × Matrix (Fin (p.n * p.W)) (Fin (p.n * p.W)) ℂ =>
      P.excess psiI psiA q.1 q.2) ∘
        (fun q : ℝ × (Fin (ringDim p) → ℝ) => (q.1, ringMatrixFin p q.2))) (Icc 0 1 ×ˢ univ) :=
    h1.comp h2.continuousOn h3
  simpa only [Function.comp_def] using h4

theorem coe_min_one_mem (t : ℝ≥0) : ((min t 1 : ℝ≥0) : ℝ) ∈ Icc (0 : ℝ) 1 :=
  ⟨NNReal.coe_nonneg _, by exact_mod_cast min_le_right t 1⟩

/-- **Continuous paths**: `t ↦ excessProc t x` is continuous for every sample. -/
theorem continuous_excessProc {P : PsiData (p.n * p.W)} (hN : 0 < p.n * p.W) (hW : 0 < P.W)
    (hz : 0 < P.z.im) (hS : StochasticSymm P.S) (psiI psiA : ℕ → ℝ) (x : RingSample p) :
    Continuous fun t => excessProc p P psiI psiA t x := by
  have hmin : Continuous fun t : ℝ≥0 => min t 1 := continuous_id.min continuous_const
  have hpath : Continuous fun t : ℝ≥0 =>
      (((min t 1 : ℝ≥0) : ℝ), vsNoise p (min t 1) x) :=
    (NNReal.continuous_coe.comp hmin).prodMk ((continuous_vsNoise p x).comp hmin)
  have heq : (fun t => excessProc p P psiI psiA t x) =
      (fun q : ℝ × (Fin (ringDim p) → ℝ) => P.excess psiI psiA q.1 (ringMatrixFin p q.2)) ∘
        (fun t : ℝ≥0 => (((min t 1 : ℝ≥0) : ℝ), vsNoise p (min t 1) x)) := by
    funext t
    simp only [Function.comp, excessProc, vsBandFin]
  rw [heq]
  exact (continuousOn_excess_coord hN hW hz hS psiI psiA).comp_continuous hpath
    fun t => ⟨coe_min_one_mem t, mem_univ _⟩

/-- **Adapted**: `excessProc t` is `driverAugmented μ t`-measurable. -/
theorem measurable_excessProc (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ]
    {P : PsiData (p.n * p.W)} (hN : 0 < p.n * p.W) (hW : 0 < P.W) (hz : 0 < P.z.im)
    (hS : StochasticSymm P.S) (psiI psiA : ℕ → ℝ) (t : ℝ≥0) :
    Measurable[driverAugmented (κ := Fin (ringDim p)) μ t] (excessProc p P psiI psiA t) := by
  have hc : Continuous fun y : Fin (ringDim p) → ℝ =>
      P.excess psiI psiA ((min t 1 : ℝ≥0) : ℝ) (ringMatrixFin p y) := by
    have h4 : ContinuousOn ((fun q : ℝ × (Fin (ringDim p) → ℝ) =>
        P.excess psiI psiA q.1 (ringMatrixFin p q.2)) ∘
          (fun y : Fin (ringDim p) → ℝ => (((min t 1 : ℝ≥0) : ℝ), y))) univ :=
      (continuousOn_excess_coord hN hW hz hS psiI psiA).comp
        (continuous_const.prodMk continuous_id).continuousOn
        fun y _ => ⟨coe_min_one_mem t, mem_univ _⟩
    exact continuousOn_univ.mp (by simpa only [Function.comp_def] using h4)
  have hY : StronglyMeasurable[driverAugmented (κ := Fin (ringDim p)) μ t]
      (vsNoise p (min t 1)) :=
    ((isContinuousSemimartingale_vsNoise μ).adapted (min t 1)).mono
      ((driverAugmented (κ := Fin (ringDim p)) μ).mono (min_le_left t 1))
  have heq : excessProc p P psiI psiA t =
      (fun y : Fin (ringDim p) → ℝ =>
        P.excess psiI psiA ((min t 1 : ℝ≥0) : ℝ) (ringMatrixFin p y)) ∘ vsNoise p (min t 1) := by
    funext x
    simp only [Function.comp, excessProc, vsBandFin]
  rw [heq]
  exact (hc.comp_stronglyMeasurable hY).measurable

/-- **`τ` is a stopping time**: for `N, W ≥ 1`, `Im z > 0`, a stochastic symmetric
profile and any thresholds, `τ` is a stopping time of `driverAugmented μ`. -/
theorem tau_isStoppingTime (μ : Measure p.SiteMatrix) [IsProbabilityMeasure μ]
    {P : PsiData (p.n * p.W)} (hN : 0 < p.n * p.W) (hW : 0 < P.W) (hz : 0 < P.z.im)
    (hS : StochasticSymm P.S) (psiI psiA : ℕ → ℝ) :
    IsStoppingTime (driverAugmented (κ := Fin (ringDim p)) μ) (tau p P psiI psiA) :=
  (isStoppingTime_rawHit (𝓖 := driverAugmented (κ := Fin (ringDim p)) μ)
    (measurable_excessProc μ hN hW hz hS psiI psiA)).min_const 1

/-- On every sample, `τ` is the first hitting time of `{some Ψ_{k,t} ≥ ψ_k}`, capped at `1`. -/
theorem tau_eq_hitTime {P : PsiData (p.n * p.W)} (hN : 0 < p.n * p.W) (hW : 0 < P.W)
    (hz : 0 < P.z.im) (hS : StochasticSymm P.S) (psiI psiA : ℕ → ℝ) (x : RingSample p) :
    tau p P psiI psiA x =
      min (hitTime (Ici (0 : ℝ)) (excessProc p P psiI psiA) x) ((1 : ℝ≥0) : WithTop ℝ≥0) := by
  unfold tau
  rw [rawHit_eq_hitTime isClosed_Ici (continuous_excessProc hN hW hz hS psiI psiA x)]

/-- Before `τ` (and `t ≤ 1`) every control quantity is below its threshold. -/
theorem excess_neg_of_lt_tau {P : PsiData (p.n * p.W)} (hN : 0 < p.n * p.W) (hW : 0 < P.W)
    (hz : 0 < P.z.im) (hS : StochasticSymm P.S) (psiI psiA : ℕ → ℝ) (x : RingSample p)
    {t : ℝ≥0} (ht : (t : WithTop ℝ≥0) < tau p P psiI psiA x) (ht1 : t ≤ 1) :
    ∀ k ∈ kRange, P.bigPsiIso k t (vsBandFin p t x) < psiI k ∧
      P.bigPsiAv k t (vsBandFin p t x) < psiA k := by
  have hmin : min t 1 = t := min_eq_left ht1
  rw [← P.excess_neg_iff]
  by_contra hc
  rw [not_lt] at hc
  have hmem : excessProc p P psiI psiA t x ∈ Ici (0 : ℝ) := by
    show 0 ≤ P.excess psiI psiA ((min t 1 : ℝ≥0) : ℝ) (vsBandFin p (min t 1) x)
    rw [hmin]
    exact hc
  have hle : hitTime (Ici (0 : ℝ)) (excessProc p P psiI psiA) x ≤ t := iInf₂_le t hmem
  rw [tau_eq_hitTime hN hW hz hS psiI psiA x] at ht
  exact absurd (lt_of_lt_of_le ht ((min_le_left _ _).trans hle)) (lt_irrefl _)

/-- At time `0` the excess is negative when all thresholds are positive (`H_0 = 0`,
`Ψ_{k,0} = 0`). **Conditional** on `Split.ZeroStatement`. -/
theorem excessProc_zero (hZ : Split.ZeroStatement) {P : PsiData (p.n * p.W)}
    {psiI psiA : ℕ → ℝ} (hI : ∀ k ∈ kRange, 0 < psiI k) (hA : ∀ k ∈ kRange, 0 < psiA k)
    (x : RingSample p) : excessProc p P psiI psiA 0 x < 0 := by
  unfold excessProc
  rw [min_eq_left (zero_le_one' ℝ≥0), vsBandFin_zero, NNReal.coe_zero, P.excess_neg_iff]
  intro k hk
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  rw [P.bigPsiIso_zero hZ hk1, P.bigPsiAv_zero hZ hk1]
  exact ⟨hI k hk, hA k hk⟩

/-- **Positivity of `τ`**: `τ > 0` for **every** sample, when all thresholds are
positive (`ψ_k ≥ 1` in the zig step) and `N, W ≥ 1`, `Im z > 0`, `S` stochastic symmetric.
**Conditional** on `Split.ZeroStatement`. -/
theorem tau_pos (hZ : Split.ZeroStatement) {P : PsiData (p.n * p.W)} (hN : 0 < p.n * p.W)
    (hW : 0 < P.W) (hz : 0 < P.z.im) (hS : StochasticSymm P.S) {psiI psiA : ℕ → ℝ}
    (hI : ∀ k ∈ kRange, 0 < psiI k) (hA : ∀ k ∈ kRange, 0 < psiA k) (x : RingSample p) :
    0 < tau p P psiI psiA x := by
  set Y := excessProc p P psiI psiA
  have hc := continuous_excessProc hN hW hz hS psiI psiA x
  have h0 : Y 0 x < 0 := excessProc_zero hZ hI hA x
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ≥0), Y t x < 0 :=
    (hc.tendsto 0).eventually (gt_mem_nhds h0)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  have hlow : ((ε.toNNReal : ℝ≥0) : WithTop ℝ≥0) ≤ hitTime (Ici (0 : ℝ)) Y x := by
    refine le_iInf₂ fun t ht => ?_
    have ht' : 0 ≤ Y t x := ht
    have : ¬ dist t 0 < ε := fun hd => absurd (hball hd) (not_lt.mpr ht')
    rw [not_lt, NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_nonneg (NNReal.coe_nonneg _)]
      at this
    exact WithTop.coe_le_coe.mpr (Real.toNNReal_le_iff_le_coe.mpr this)
  rw [tau_eq_hitTime hN hW hz hS psiI psiA x]
  apply lt_min
  · exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (Real.toNNReal_pos.mpr hε)) hlow
  · exact WithTop.coe_lt_coe.mpr one_pos

end BlockBand.Native.ErdosRiabov.Psi
