module

public import BlockBand.Transmission.Dual.GR4

/-!
# Martingales to the conditional kernel, with an enlarged conditioning variable

`ae_isMPSolutionOn_kernel` disintegrates the joint law of the start `ξ` and the record
`Φ = useq W Z` over the start. To obtain statements *conditional on additional `𝓖₀`-data*
(needed for the atomless lifetime from a random start: the atom may sit at a random time `c`),
this file disintegrates over an arbitrary `𝓖₀`-measurable variable `η : Ω → E`, with the start a
measurable function of it, `ξ = g ∘ η`. The proofs are the same, with `jlaw P ξ` replaced by
`jlaw P η`; the inputs (`exists_mart_cfun`, `ae_martingale_condKernel`, `exists_mart_of_cover`)
are generic in the conditioning variable.
* `ae_mart_kernelC`, `ae_start_kernelC` (the kernel at `e` starts at `g e`);
* **`ae_isMPSolutionOn_kernelC`**: for `law η`-a.e. `e`, every coordinate process `cY n` solves
  the `(b, a)` martingale problem in `W n` under `κ e`, started at `g e`;
* `ae_isStopSeq_kernelC`: the stop-sequence relation passes to `κ e`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualAtomless

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.Semimartingale BlockBand.Transmission.Dual
open BlockBand.Transmission.Dual.G
open scoped NNReal ENNReal

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {W : ℕ → Set (Fin d → ℝ)} {Z : ℕ → Ω → CPath d}
  {E : Type*} [MeasurableSpace E] {η : Ω → E} {g : E → Fin d → ℝ}

/-- **A martingale of the record passes to the kernel** (conditioning on `η`). -/
theorem ae_mart_kernelC (hW : ∀ n, IsOpen (W n))
    (hZa : ∀ n t, StronglyMeasurable[𝓖 t] (zproc Z n t)) (hZ0 : ∀ n x, (Z n x).1 0 = g (η x))
    (hg : Measurable g) (hη : Measurable[𝓖 0] η) {n : ℕ} {V : Set (Fin d → ℝ)}
    (hV : IsInteriorDomain V (W n))
    {G G' : ℝ≥0 → (ℝ≥0 → Fin d → ℝ) → ℝ}
    (hG : ∀ s (y y' : ℝ≥0 → Fin d → ℝ), (∀ u ≤ s, y u = y' u) → G s y = G s y')
    (hG' : IsPathFn (closure V) G')
    (hagree : ∀ s (w : CPath d), (∀ u ≤ s, w.1 u ∈ closure V) → G s w.1 = G' s w.1)
    (hN : ∃ N : ℝ≥0 → Ω → ℝ, Martingale N 𝓖 P ∧ ∀ t, N t =ᵐ[P]
      stoppedProcess (fun t x => G t (Z n x).1) (exitTimeFrom V (zproc Z n)) t) :
    ∀ᵐ e ∂(jlaw P η (useq W Z)).fst,
      Martingale (cfun n V G) (cfilt d) ((jlaw P η (useq W Z)).condKernel e) := by
  have he : cfun n V G = cfun n V G' := cfun_congr hV.1 hagree
  obtain ⟨M, hM, hMe⟩ := exists_mart_cfun (W := W) (ξ := fun x => g (η x)) (hg.comp hη) hZ0
    hV.1 (subset_closure.trans hV.2.2) hG hN
  rw [he] at hMe ⊢
  exact ae_martingale_condKernel (tr := ctrunc) (𝓕 := cfilt d) measurable_ctrunc cfilt_eq hη
    (measurable_useq hW hZa) (measurable_ctrunc_useq hW hZa) (measurable_cfilt_cfun hV.1 hG')
    (fun ŵ _ => (continuous_cfun hG' ŵ).continuousWithinAt) (cfun_bdd hV.1 hG') hM hMe

/-- **The kernel at `e` starts at `g e`.** -/
theorem ae_start_kernelC (hW : ∀ n, IsOpen (W n))
    (hZa : ∀ n t, StronglyMeasurable[𝓖 t] (zproc Z n t)) (hZ0 : ∀ n x, (Z n x).1 0 = g (η x))
    (hg : Measurable g) (hη : Measurable[𝓖 0] η) :
    ∀ᵐ e ∂(jlaw P η (useq W Z)).fst, ∀ n,
      ∀ᵐ ŵ ∂(jlaw P η (useq W Z)).condKernel e, (ŵ n).1 0 = g e := by
  have hηΦ : Measurable fun x => (η x, useq W Z x) :=
    (hη.mono (𝓖.le 0) le_rfl).prodMk (measurable_useq hW hZa)
  refine ae_all_iff.2 fun n => ?_
  have hS : MeasurableSet {p : E × CSeq d | (p.2 n).1 0 = g p.1} :=
    measurableSet_eq_fun ((measurable_cev 0).comp ((measurable_pi_apply n).comp measurable_snd))
      (hg.comp measurable_fst)
  exact ae_ae_condKernel hηΦ hS (ae_of_all _ fun x => (useq_zero hZ0 x n))

variable {b : (Fin d → ℝ) → Fin d → ℝ} {a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ}

/-- **The kernel solves the martingale problem in every `W n`**, for `law η`-a.e. `e`. -/
theorem ae_isMPSolutionOn_kernelC (hW : ∀ n, IsOpen (W n))
    (hZ : ∀ n, IsMPSolutionOn P 𝓖 b a (W n) (zproc Z n)) (hZ0 : ∀ n x, (Z n x).1 0 = g (η x))
    (hg : Measurable g) (hη : Measurable[𝓖 0] η) (hb : ∀ n, ContinuousOn b (W n))
    (ha : ∀ n, ContinuousOn a (W n)) :
    ∀ᵐ e ∂(jlaw P η (useq W Z)).fst, ∀ n,
      IsMPSolutionOn ((jlaw P η (useq W Z)).condKernel e) (cfilt d) b a (W n) (cY n) ∧
      ∀ᵐ ŵ ∂(jlaw P η (useq W Z)).condKernel e, (ŵ n).1 0 = g e := by
  have hZa : ∀ n t, StronglyMeasurable[𝓖 t] (zproc Z n t) := fun n t => (hZ n).adapted t
  have hV := fun n k => isInteriorDomain_exh (W n) k
  have hcb : ∀ n k (i : Fin d), ContinuousOn (fun y => b y i) (closure (exh (W n) k)) :=
    fun n k i => (continuous_apply i).comp_continuousOn ((hb n).mono (hV n k).2.2)
  have hca : ∀ n k (i j : Fin d), ContinuousOn (fun y => a y i j) (closure (exh (W n) k)) :=
    fun n k i j => (continuous_apply j).comp_continuousOn
      ((continuous_apply i).comp_continuousOn ((ha n).mono (hV n k).2.2))
  have hD' := fun n k (i : Fin d) => isPathFn_cdrift (hV n k).2.1 (hcb n k i) i
  have hB' := fun n k (i j : Fin d) =>
    isPathFn_cbrk (hV n k).2.1 (hcb n k i) (hcb n k j) (hca n k i j) i j
  have agD : ∀ n k (i : Fin d) s (w : CPath d), (∀ u ≤ s, w.1 u ∈ closure (exh (W n) k)) →
      cdrift (fun y => b y i) i s w.1 =
        cdrift ((closure (exh (W n) k)).indicator fun y => b y i) i s w.1 :=
    fun n k i s w hw => (cdrift_indicator _ i hw).symm
  have agB : ∀ n k (i j : Fin d) s (w : CPath d), (∀ u ≤ s, w.1 u ∈ closure (exh (W n) k)) →
      cbrk (fun y => b y i) (fun y => b y j) (fun y => a y i j) i j s w.1 =
        cbrk ((closure (exh (W n) k)).indicator fun y => b y i)
          ((closure (exh (W n) k)).indicator fun y => b y j)
          ((closure (exh (W n) k)).indicator fun y => a y i j) i j s w.1 :=
    fun n k i j s w hw => (cbrk_indicator _ _ _ i j hw).symm
  have hD : ∀ n k (i : Fin d), ∀ᵐ e ∂(jlaw P η (useq W Z)).fst,
      Martingale (cfun n (exh (W n) k) (cdrift (fun y => b y i) i)) (cfilt d)
        ((jlaw P η (useq W Z)).condKernel e) := fun n k i =>
    ae_mart_kernelC hW hZa hZ0 hg hη (hV n k) (fun s _ _ h => cdrift_nonant _ i s h) (hD' n k i)
      (agD n k i) ((hZ n).drift _ (hV n k) i)
  have hB : ∀ n k (i j : Fin d), ∀ᵐ e ∂(jlaw P η (useq W Z)).fst,
      Martingale (cfun n (exh (W n) k)
        (cbrk (fun y => b y i) (fun y => b y j) (fun y => a y i j) i j)) (cfilt d)
        ((jlaw P η (useq W Z)).condKernel e) := fun n k i j =>
    ae_mart_kernelC hW hZa hZ0 hg hη (hV n k) (fun s _ _ h => cbrk_nonant _ _ _ i j s h)
      (hB' n k i j) (agB n k i j) ((hZ n).bracket _ (hV n k) i j)
  filter_upwards [ae_all_iff.2 fun n => ae_all_iff.2 fun k => ae_all_iff.2 fun i => hD n k i,
    ae_all_iff.2 fun n => ae_all_iff.2 fun k => ae_all_iff.2 fun i => ae_all_iff.2 fun j =>
      hB n k i j, ae_start_kernelC hW hZa hZ0 hg hη] with e hd hbr hs n
  have hcov : ∀ K, IsCompact K → K ⊆ W n → ∃ k, K ⊆ exh (W n) k :=
    fun K hK hKU => exists_exh_superset (hW n) hK hKU
  refine ⟨⟨fun t => (measurable_cY n t).stronglyMeasurable, ae_of_all _ fun ŵ => (ŵ n).2,
    fun W' hW' i => ?_, fun W' hW' i j => ?_⟩, hs n⟩
  · exact exists_mart_of_cover (hs n) hcov (cdrift_zero _ i)
      (fun k w h0 => continuous_stop_of_agree (isOpen_exh _ k) (hD' n k i) (agD n k i) h0)
      (fun k => hd n k i) hW'
  · exact exists_mart_of_cover (hs n) hcov (cbrk_zero _ _ _ i j)
      (fun k w h0 => continuous_stop_of_agree (isOpen_exh _ k) (hB' n k i j) (agB n k i j) h0)
      (fun k => hbr n k i j) hW'

/-- **The stop-sequence relation passes to the kernel** (conditioning on `η`). -/
theorem ae_isStopSeq_kernelC (hW : ∀ n, IsOpen (W n))
    (hZa : ∀ n t, StronglyMeasurable[𝓖 t] (zproc Z n t)) (hη : Measurable[𝓖 0] η) (t₀ : ℝ≥0)
    (hst : IsStopSeq P W t₀ fun x n => pstop (W n) t₀ (Z n x)) :
    ∀ᵐ e ∂(jlaw P η (useq W Z)).fst,
      IsStopSeq ((jlaw P η (useq W Z)).condKernel e) W t₀ (ctr W t₀) := by
  have hηΦ : Measurable fun x => (η x, useq W Z x) :=
    (hη.mono (𝓖.le 0) le_rfl).prodMk (measurable_useq hW hZa)
  have h : ∀ k n, k ≤ n → ∀ᵐ e ∂(jlaw P η (useq W Z)).fst,
      ∀ᵐ ŵ ∂(jlaw P η (useq W Z)).condKernel e, ctr W t₀ ŵ k = pstop (W k) t₀ (ctr W t₀ ŵ n) := by
    intro k n hkn
    have hS : MeasurableSet {p : E × CSeq d | ctr W t₀ p.2 k =
        pstop (W k) t₀ (ctr W t₀ p.2 n)} :=
      measurableSet_eq_fun ((measurable_pi_apply k).comp ((measurable_ctr hW t₀).comp
        measurable_snd)) ((measurable_pstop (hW k) t₀).comp ((measurable_pi_apply n).comp
          ((measurable_ctr hW t₀).comp measurable_snd)))
    refine ae_ae_condKernel hηΦ hS ?_
    filter_upwards [hst k n hkn] with x hx
    show ctr W t₀ (useq W Z x) k = pstop (W k) t₀ (ctr W t₀ (useq W Z x) n)
    rw [ctr_useq hW t₀ x]; exact hx
  have h' : ∀ᵐ e ∂(jlaw P η (useq W Z)).fst, ∀ k n, k ≤ n →
      ∀ᵐ ŵ ∂(jlaw P η (useq W Z)).condKernel e, ctr W t₀ ŵ k = pstop (W k) t₀ (ctr W t₀ ŵ n) := by
    refine ae_all_iff.2 fun k => ae_all_iff.2 fun n => ?_
    by_cases hkn : k ≤ n
    · filter_upwards [h k n hkn] with e he _ using he
    · exact Eventually.of_forall fun e h => absurd h hkn
  filter_upwards [h'] with e he using he

end BlockBand.Transmission.DualAtomless
