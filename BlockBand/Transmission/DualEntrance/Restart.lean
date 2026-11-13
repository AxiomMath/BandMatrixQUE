module

public import BlockBand.Internal.Contracts.Transmission

/-!
# Restarted supermartingale bound with an occupation term

Setting: an arbitrary filtered probability space `(Ω, Q, 𝓖)` (raw filtration) and a real
continuous semimartingale `Z` (contract `IsContinuousSemimartingale`, in `ℝ¹`) with drift `β`.

**`lintegral_restart_le`.** Let `s ≤ t`, `A ∈ 𝓖_s` with `Z_s ≤ B` on `A`, and `g ≥ 0`. If a.s.
on `A` the process is nonnegative on `[0, t]` and its drift satisfies `β_u ≤ −g_u` for
`u ∈ (s, t]`, then
`∫_A (Z_t + ∫_{(s,t]} g du) dQ ≤ ∫_A Z_s dQ` (lower Lebesgue integrals of `ofReal`).

No measurability of `g` and no integrability of `Z_t` is assumed. Proof: along the localizing
sequence `τ_k`, on `A_k = A ∩ {s ≤ τ_k} ∈ 𝓖_s` one has pathwise
`Z_{t∧τ_k} + ∫_{(s, t∧τ_k]} g ≤ Z_s + N_t − N_s` with `N` the stopped compensated process,
and `∫_{A_k} (N_t − N_s) = 0` (martingale modification). On `A ∩ E_k`,
`E_k = ⋂_{j ≥ k} {t ≤ τ_j}`, the left side is the target integrand; the `E_k` increase to a
full-measure set (`setLIntegral_iUnion_of_directed` needs no measurability).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualEntrance

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.Transmission
open scoped NNReal ENNReal

theorem untopA_min_le (t : ℝ≥0) (τ : WithTop ℝ≥0) : (min (t : WithTop ℝ≥0) τ).untopA ≤ t := by
  cases τ with
  | top => rw [min_eq_left le_top]; exact le_rfl
  | coe a => rw [← WithTop.coe_min]; exact min_le_left t a

theorem le_untopA_min {s t : ℝ≥0} {τ : WithTop ℝ≥0} (hst : s ≤ t) (hs : (s : WithTop ℝ≥0) ≤ τ) :
    s ≤ (min (t : WithTop ℝ≥0) τ).untopA := by
  cases τ with
  | top => rw [min_eq_left le_top]; exact hst
  | coe a => rw [← WithTop.coe_min]; exact le_min hst (WithTop.coe_le_coe.1 hs)

theorem untopA_min_of_le {t : ℝ≥0} {τ : WithTop ℝ≥0} (h : (t : WithTop ℝ≥0) ≤ τ) :
    (min (t : WithTop ℝ≥0) τ).untopA = t := by
  rw [min_eq_left h]; rfl

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-- **Restarted supermartingale bound with an occupation term.** -/
theorem lintegral_restart_le {Z β : ℝ≥0 → Ω → Fin 1 → ℝ}
    {α : ℝ≥0 → Ω → Matrix (Fin 1) (Fin 1) ℝ} (h : IsContinuousSemimartingale Q 𝓖 Z β α)
    {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω} (hA : MeasurableSet[𝓖 s] A) {B : ℝ}
    (hB : ∀ ω ∈ A, Z s ω 0 ≤ B) (g : ℝ≥0 → Ω → ℝ) (hg0 : ∀ u ω, 0 ≤ g u ω)
    (hβ : ∀ᵐ ω ∂Q, ω ∈ A → ∀ u : ℝ≥0, s < u → u ≤ t → β u ω 0 ≤ -g u ω)
    (hZ : ∀ᵐ ω ∂Q, ω ∈ A → ∀ u : ℝ≥0, u ≤ t → 0 ≤ Z u ω 0) :
    ∫⁻ ω in A, (ENNReal.ofReal (Z t ω 0) +
      ∫⁻ u in Ioc (s : ℝ) t, ENNReal.ofReal (g u.toNNReal ω)) ∂Q ≤
      ∫⁻ ω in A, ENNReal.ofReal (Z s ω 0) ∂Q := by
  obtain ⟨τ, hτ, hτlim, hmart⟩ := h.localizing
  have hAm : MeasurableSet A := 𝓖.le s _ hA
  have hZsm : StronglyMeasurable fun ω => Z s ω 0 :=
    (continuous_apply 0).comp_stronglyMeasurable ((h.adapted s).mono (𝓖.le s))
  -- the target integrand and the stopped integrands
  set F : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Z t ω 0) +
    ∫⁻ u in Ioc (s : ℝ) t, ENNReal.ofReal (g u.toNNReal ω) with hF
  let a : ℕ → Ω → ℝ≥0 := fun k ω => (min (t : WithTop ℝ≥0) (τ k ω)).untopA
  let f : ℕ → Ω → ℝ≥0∞ := fun k ω => ENNReal.ofReal (Z (a k ω) ω 0) +
    ∫⁻ u in Ioc (s : ℝ) (a k ω), ENNReal.ofReal (g u.toNNReal ω)
  let Ak : ℕ → Set Ω := fun k => A ∩ {ω | (s : WithTop ℝ≥0) ≤ τ k ω}
  have hAk : ∀ k, MeasurableSet[𝓖 s] (Ak k) := fun k => hA.inter ((hτ k).measurableSet_ge s)
  -- per-`k` bound
  have hk : ∀ k, ∫⁻ ω in Ak k, f k ω ∂Q ≤ ∫⁻ ω in A, ENNReal.ofReal (Z s ω 0) ∂Q := by
    intro k
    obtain ⟨M, hM, hMe⟩ := (hmart k).1 0
    set N := stoppedProcess (smCompensated Z β 0) (τ k) with hNdef
    have hAkm : MeasurableSet (Ak k) := 𝓖.le s _ (hAk k)
    have hNint : ∀ r, Integrable (N r) Q := fun r => (hM.integrable r).congr (hMe r)
    have hZsint : IntegrableOn (fun ω => Z s ω 0) (Ak k) Q := by
      refine Measure.integrableOn_of_bounded (measure_ne_top _ _) hZsm.aestronglyMeasurable
        (M := max B 0) ?_
      refine (ae_restrict_iff' hAkm).2 ?_
      filter_upwards [hZ] with ω hω hωA
      rw [Real.norm_eq_abs, abs_of_nonneg (hω hωA.1 s hst)]
      exact (hB ω hωA.1).trans (le_max_left _ _)
    have hmart0 : ∫ ω in Ak k, (N t ω - N s ω) ∂Q = 0 := by
      rw [integral_sub (hNint t).integrableOn (hNint s).integrableOn,
        ← integral_congr_ae (ae_restrict_of_ae (hMe t)),
        ← integral_congr_ae (ae_restrict_of_ae (hMe s)), hM.setIntegral_eq hst (hAk k), sub_self]
    have hpt : ∀ᵐ ω ∂Q, ω ∈ Ak k → f k ω ≤ ENNReal.ofReal (Z s ω 0 + (N t ω - N s ω)) ∧
        0 ≤ Z s ω 0 + (N t ω - N s ω) := by
      filter_upwards [hβ, hZ, h.integrable] with ω hβω hZω hint hωk
      have hsa : s ≤ a k ω := le_untopA_min hst hωk.2
      have hat : a k ω ≤ t := untopA_min_le t (τ k ω)
      have hNt : N t ω = smCompensated Z β 0 (a k ω) ω := rfl
      have hNs : N s ω = smCompensated Z β 0 s ω := by
        have h2 : (s : WithTop ℝ≥0) ≤ τ k ω := hωk.2
        simp only [hNdef, stoppedProcess, min_eq_left h2]; rfl
      have hI := (hint t).1 0
      have hIa : IntegrableOn (fun u : ℝ => β u.toNNReal ω 0) (Ioc (s : ℝ) (a k ω)) :=
        hI.mono_set (Ioc_subset_Ioc s.coe_nonneg (NNReal.coe_le_coe.2 hat))
      have hsplit : ∫ u in Ioc (0 : ℝ) (a k ω), β u.toNNReal ω 0 =
          (∫ u in Ioc (0 : ℝ) s, β u.toNNReal ω 0) + ∫ u in Ioc (s : ℝ) (a k ω), β u.toNNReal ω 0 := by
        have hU : Ioc (0 : ℝ) s ∪ Ioc (s : ℝ) (a k ω) = Ioc (0 : ℝ) (a k ω) :=
          Ioc_union_Ioc_eq_Ioc s.coe_nonneg (NNReal.coe_le_coe.2 hsa)
        rw [← hU]
        exact setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
          (hI.mono_set (Ioc_subset_Ioc le_rfl (NNReal.coe_le_coe.2 (hsa.trans hat)))) hIa
      have hdom : ∀ u ∈ Ioc (s : ℝ) (a k ω), g u.toNNReal ω ≤ -β u.toNNReal ω 0 := by
        intro u hu
        have hu0 : 0 < u := lt_of_le_of_lt s.coe_nonneg hu.1
        have h1 : s < u.toNNReal := by
          rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hu0.le]; exact hu.1
        have h2 : u.toNNReal ≤ t := by
          rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hu0.le]
          exact hu.2.trans (NNReal.coe_le_coe.2 hat)
        have := hβω hωk.1 u.toNNReal h1 h2
        linarith
      have hneg : 0 ≤ -∫ u in Ioc (s : ℝ) (a k ω), β u.toNNReal ω 0 := by
        rw [← integral_neg]
        exact setIntegral_nonneg measurableSet_Ioc fun u hu => (hg0 _ _).trans (hdom u hu)
      have hgle : ∫⁻ u in Ioc (s : ℝ) (a k ω), ENNReal.ofReal (g u.toNNReal ω) ≤
          ENNReal.ofReal (-∫ u in Ioc (s : ℝ) (a k ω), β u.toNNReal ω 0) := by
        have hIn : IntegrableOn (fun u : ℝ => -β u.toNNReal ω 0) (Ioc (s : ℝ) (a k ω)) := hIa.neg
        rw [← integral_neg, ofReal_integral_eq_lintegral_ofReal hIn
          ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu =>
            (hg0 _ _).trans (hdom u hu)))]
        exact setLIntegral_mono_ae' measurableSet_Ioc (Eventually.of_forall fun u hu =>
          ENNReal.ofReal_le_ofReal (hdom u hu))
      have hid : Z (a k ω) ω 0 - ∫ u in Ioc (s : ℝ) (a k ω), β u.toNNReal ω 0 =
          Z s ω 0 + (N t ω - N s ω) := by
        rw [hNt, hNs]; simp only [smCompensated]; rw [hsplit]; ring
      have hZa := hZω hωk.1 _ hat
      refine ⟨?_, by rw [← hid]; linarith⟩
      calc f k ω ≤ ENNReal.ofReal (Z (a k ω) ω 0) +
            ENNReal.ofReal (-∫ u in Ioc (s : ℝ) (a k ω), β u.toNNReal ω 0) := add_le_add le_rfl hgle
        _ = ENNReal.ofReal (Z (a k ω) ω 0 +
            -∫ u in Ioc (s : ℝ) (a k ω), β u.toNNReal ω 0) := (ENNReal.ofReal_add hZa hneg).symm
        _ = _ := by rw [← sub_eq_add_neg, hid]
    have hNd : IntegrableOn (fun ω => N t ω - N s ω) (Ak k) Q :=
      ((hNint t).sub (hNint s)).integrableOn
    calc ∫⁻ ω in Ak k, f k ω ∂Q
        ≤ ∫⁻ ω in Ak k, ENNReal.ofReal (Z s ω 0 + (N t ω - N s ω)) ∂Q :=
          setLIntegral_mono_ae' hAkm (hpt.mono fun ω h hω => (h hω).1)
      _ = ENNReal.ofReal (∫ ω in Ak k, (Z s ω 0 + (N t ω - N s ω)) ∂Q) :=
          (ofReal_integral_eq_lintegral_ofReal (hZsint.add hNd)
            ((ae_restrict_iff' hAkm).2 (hpt.mono fun ω h hω => (h hω).2))).symm
      _ = ENNReal.ofReal (∫ ω in Ak k, Z s ω 0 ∂Q) := by
          rw [integral_add hZsint hNd, hmart0, add_zero]
      _ = ∫⁻ ω in Ak k, ENNReal.ofReal (Z s ω 0) ∂Q := by
          refine ofReal_integral_eq_lintegral_ofReal hZsint ((ae_restrict_iff' hAkm).2 ?_)
          filter_upwards [hZ] with ω hω hωA using hω hωA.1 s hst
      _ ≤ _ := lintegral_mono_set inter_subset_left
  -- exhaustion
  let E : ℕ → Set Ω := fun k => ⋂ j ≥ k, {ω | (t : WithTop ℝ≥0) ≤ τ j ω}
  have hEm : ∀ k, MeasurableSet (E k) := fun k => MeasurableSet.iInter fun j =>
    MeasurableSet.iInter fun _ => 𝓖.le t _ ((hτ j).measurableSet_ge t)
  have hEmono : Monotone E := fun k l hkl => by
    intro ω hω; simp only [E, mem_iInter] at hω ⊢; exact fun j hj => hω j (hkl.trans hj)
  have hEk : ∀ k, ∫⁻ ω in A ∩ E k, F ω ∂Q ≤ ∫⁻ ω in A, ENNReal.ofReal (Z s ω 0) ∂Q := by
    intro k
    refine le_trans (b := ∫⁻ ω in A ∩ E k, f k ω ∂Q) (le_of_eq ?_)
      ((lintegral_mono_set (s := A ∩ E k) (t := Ak k) ?_).trans (hk k))
    · refine setLIntegral_congr_fun (hAm.inter (hEm k)) fun ω hω => ?_
      have ht : (t : WithTop ℝ≥0) ≤ τ k ω := by
        have := hω.2; simp only [E, mem_iInter] at this; exact this k le_rfl
      simp only [F, f, a, untopA_min_of_le ht]
    · intro ω hω
      have ht : (t : WithTop ℝ≥0) ≤ τ k ω := by
        have := hω.2; simp only [E, mem_iInter] at this; exact this k le_rfl
      exact ⟨hω.1, (WithTop.coe_le_coe.2 hst).trans ht⟩
  have hgood : ∀ᵐ ω ∂Q, ∃ k, ω ∈ E k := by
    filter_upwards [hτlim] with ω hω
    obtain ⟨k, hk⟩ := eventually_atTop.1 ((WithTop.tendsto_nhds_top_iff _).1 hω t)
    exact ⟨k, by simp only [E, mem_iInter]; exact fun j hj => (hk j hj).le⟩
  have hU : A =ᵐ[Q] ⋃ k, A ∩ E k := by
    refine ae_eq_set.2 ⟨measure_mono_null ?_ (ae_iff.1 hgood), ?_⟩
    · rintro ω hω ⟨k, hk⟩; exact hω.2 (mem_iUnion.2 ⟨k, hω.1, hk⟩)
    · rw [sdiff_eq_empty.2 (iUnion_subset fun k => inter_subset_left)]; exact measure_empty
  calc ∫⁻ ω in A, F ω ∂Q = ∫⁻ ω in ⋃ k, A ∩ E k, F ω ∂Q := setLIntegral_congr hU
    _ = ⨆ k, ∫⁻ ω in A ∩ E k, F ω ∂Q :=
        setLIntegral_iUnion_of_directed _ (Monotone.directed_le fun k l hkl =>
          inter_subset_inter_right _ (hEmono hkl))
    _ ≤ _ := iSup_le hEk

end BlockBand.Transmission.DualEntrance
