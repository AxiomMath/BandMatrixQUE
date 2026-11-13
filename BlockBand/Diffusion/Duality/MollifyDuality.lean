module
public import BlockBand.Diffusion.Duality.MollifyPDE
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Space-time duality for `C^{0,2}` solutions

Setting of `IsTestMPSolution.duality`: `(Ω, 𝓖, Q)` a probability space
with a raw filtration; `U ⊆ ℝ^d` open, `b, a` continuous on `U`, `a` symmetric on `U`; `Z` a
solution of the raw test-function martingale problem `IsTestMPSolution Q 𝓖 b a U Z`,
`Z_0 = z ∈ U` a.s.; `O ⊆ U` open; a.s. `Z_r ∈ O` for all `r ∈ (0, t]`.

The joint `C²` hypothesis of `IsTestMPSolution.duality` is weakened to `C^{0,2}`:
`u` has `∂ₜu`, `∂ₓu`, `∂ₓ²u` jointly continuous on `(0, t) × O` (`IsC02On`, no `∂ₜ∂ₓu`, no
`∂ₜ²u`, no joint differentiability), with `∂ₜu + 𝓛u = 0` there (`spGen = 0`). The remaining
hypotheses are those of `IsTestMPSolution.duality`, unchanged: `u` continuous on
`(0, t] × O`, continuous within `(0, t] × O` at `(0, z)`, and bounded by `C` on `(0, t] × O`.

## Main results

* `IsTestMPSolution.duality_C02`: `E[u(t, Z_t)] = u(0, z)`.
* `IsTestMPSolution.duality_setIntegral_C02`: for `s < t` and `A ∈ 𝓖_s`,
  `∫_A u(t, Z_t) dQ = ∫_A u(s, Z_s) dQ`.
* `IsTestMPSolution.condExp_duality_C02`: for `s < t`, `E[u(t, Z_t) | 𝓖_s] = u(s, Z_s)` a.s.

Proof. For `0 < s < t` and `ε_n = s/(n+2)`, the backward mollification
`u_n = tconv (bwdMollifier ε_n) u` is jointly `C²` with `stGen b a u_n = 0` on `(ε_n, t) × O`
(`IsC02On.tconv`), continuous on `(ε_n, t] × O` and bounded by `C`;
`duality_setIntegral_mp` applies to `u_n` on `[s, t]`. As `n → ∞`, `u_n → u` pointwise on
`(0, t] × O` (`tendstoLocallyUniformlyOn_tconv`), and dominated convergence (bound `C`) gives the
identity for `u`. The case `s = 0` follows by letting `s ↓ 0`, using continuity within
`(0, t] × O` at `(0, z)` and path continuity.
-/

namespace BlockBand.Diffusion
open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.SourceProcess.Stochastic
open scoped NNReal ENNReal

variable {d : ℕ}

/-- Dominated convergence on a set, with a constant bound. -/
theorem tendsto_setIntegral_of_abs_le {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    [IsFiniteMeasure Q] {F : ℕ → Ω → ℝ} {f : Ω → ℝ} {C : ℝ}
    (hFm : ∀ n, AEStronglyMeasurable (F n) Q) (hb : ∀ n, ∀ᵐ ω ∂Q, |F n ω| ≤ C)
    (hl : ∀ᵐ ω ∂Q, Tendsto (fun n => F n ω) atTop (𝓝 (f ω))) (A : Set Ω) :
    Tendsto (fun n => ∫ ω in A, F n ω ∂Q) atTop (𝓝 (∫ ω in A, f ω ∂Q)) :=
  tendsto_integral_of_dominated_convergence (fun _ => C) (fun n => (hFm n).restrict)
    (integrable_const C) (fun n => ae_restrict_of_ae ((hb n).mono fun _ h => by
      rwa [Real.norm_eq_abs])) (ae_restrict_of_ae hl)

/-- Pointwise convergence of backward mollifications along `ε_n → 0⁺`. -/
theorem tendsto_tconv_bwdMollifier {E : Type*} [PseudoMetricSpace E] {T₀ T₁ : ℝ} {O : Set E}
    {u : ℝ × E → ℝ} (hu : ContinuousOn u (Ioc T₀ T₁ ×ˢ O)) {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n)
    (hε : Tendsto ε atTop (𝓝 0)) {p : ℝ × E} (hp : p ∈ Ioc T₀ T₁ ×ˢ O) :
    Tendsto (fun n => tconv (bwdMollifier (ε n)) u p) atTop (𝓝 (u p)) := by
  have h := (tendstoLocallyUniformlyOn_tconv (fun _ h => isBwdMollifier_bwdMollifier h) hu
    (φ := bwdMollifier)).tendsto_at hp
  exact h.comp (tendsto_nhdsWithin_iff.2 ⟨hε, Eventually.of_forall hε0⟩)

variable {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {b : (Fin d → ℝ) → Fin d → ℝ} {a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ}
  {U O : Set (Fin d → ℝ)} {Z : ℝ≥0 → Ω → Fin d → ℝ}
  {u ut : ℝ × (Fin d → ℝ) → ℝ} {u1 : ℝ × (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] ℝ}
  {u2 : ℝ × (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] ℝ}

section Headline

variable (hZ : IsTestMPSolution Q 𝓖 b a U Z) (hU : IsOpen U) (hb : ContinuousOn b U)
  (ha : ContinuousOn a U) (hsym : ∀ y ∈ U, ∀ i j, a y i j = a y j i) (hO : IsOpen O)
  (hOU : O ⊆ U) {z : Fin d → ℝ} (hzU : z ∈ U) (hz : ∀ᵐ ω ∂Q, Z 0 ω = z) {t : ℝ≥0}
  (hin : ∀ᵐ ω ∂Q, ∀ r, 0 < r → r ≤ t → Z r ω ∈ O)
  (hd : IsC02On u ut u1 u2 (Ioo 0 (t : ℝ) ×ˢ O))
  (hpde : ∀ p ∈ Ioo 0 (t : ℝ) ×ˢ O, spGen b a ut u1 u2 p = 0)
  (hcont : ContinuousOn u (Ioc 0 (t : ℝ) ×ˢ O))
  (hu0 : ContinuousWithinAt u (Ioc 0 (t : ℝ) ×ˢ O) (0, z))
  {C : ℝ} (hC : ∀ p ∈ Ioc 0 (t : ℝ) ×ˢ O, |u p| ≤ C)

section Pos

include hZ hU hb ha hsym hO hOU hzU hz hin hd hpde hcont hC

/-- Duality from a positive time `s` to `t`, with integrability. -/
theorem IsTestMPSolution.duality_aux_pos_C02 {s : ℝ≥0} (hs0 : 0 < s) (hst : s < t) :
    Integrable (fun ω => u ((t : ℝ), Z t ω)) Q ∧ Integrable (fun ω => u ((s : ℝ), Z s ω)) Q ∧
      ∀ A, MeasurableSet[𝓖 s] A →
        ∫ ω in A, u ((t : ℝ), Z t ω) ∂Q = ∫ ω in A, u ((s : ℝ), Z s ω) ∂Q := by
  have hZ' := hZ.isMPSolutionOn hU hb ha hsym
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs0
  have hstR : (s : ℝ) < t := by exact_mod_cast hst
  set εs : ℕ → ℝ := fun n => (s : ℝ) / ((n : ℝ) + 2) with hεs
  have hn2 : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 2 := fun n => by positivity
  have hε0 : ∀ n, 0 < εs n := fun n => div_pos hsR (hn2 n)
  have hεs' : ∀ n, εs n < s := fun n => by
    simp only [hεs]
    rw [div_lt_iff₀ (hn2 n)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hεlim : Tendsto εs atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  set v : ℕ → ℝ × (Fin d → ℝ) → ℝ := fun n => tconv (bwdMollifier (εs n)) u with hv
  have hφ : ∀ n, IsBwdMollifier (bwdMollifier (εs n)) (εs n) := fun n =>
    isBwdMollifier_bwdMollifier (hε0 n)
  have hsubIoo : ∀ n, Ioo (s : ℝ) t ×ˢ O ⊆ Ioo (0 + εs n) t ×ˢ O := fun n =>
    prod_mono (Ioo_subset_Ioo_left (by linarith [hεs' n])) le_rfl
  have hsubIoc : ∀ n, Ioc (s : ℝ) t ×ˢ O ⊆ Ioc (0 + εs n) t ×ˢ O := fun n =>
    prod_mono (Ioc_subset_Ioc_left (by linarith [hεs' n])) le_rfl
  have hvc : ∀ n, ContinuousOn (v n) (Ioc (0 + εs n) t ×ˢ O) := fun n =>
    continuousOn_tconv (hφ n).continuous (hφ n).support_subset hO hcont
  have hvC : ∀ n, ∀ p ∈ Ioc (0 + εs n) (t : ℝ) ×ˢ O, |v n p| ≤ C := fun n p hp =>
    abs_tconv_le_of_bound (hφ n) hcont hC hp
  have hpath : ∀ᵐ ω ∂Q, (∀ r ≤ t, Z r ω ∈ U) ∧ ∀ r, s < r → r ≤ t → Z r ω ∈ O := by
    filter_upwards [hz, hin] with ω h0 hω
    refine ⟨fun r hr => ?_, fun r hr hrt => hω r (lt_of_le_of_lt zero_le hr) hrt⟩
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ r) with h | h
    · subst h; rw [h0]; exact hzU
    · exact hOU (hω r h hr)
  have hZs : ∀ᵐ ω ∂Q, Z s ω ∈ O := hin.mono fun ω h => h s hs0 hst.le
  have hZt : ∀ᵐ ω ∂Q, Z t ω ∈ O := hin.mono fun ω h => h t (hs0.trans hst) le_rfl
  have hDn : ∀ n, _ := fun n => duality_setIntegral_mp hZ' hU hO hOU hb ha hst
    (u := v n) ((hd.contDiffOn_tconv hO (hφ n)).mono (by simpa using hsubIoo n))
    (fun p hp => hd.stGen_tconv_eq_zero hO hpde (hφ n) (hε0 n).le
      (by simpa using hsubIoo n hp))
    ((hvc n).mono (hsubIoc n))
    (hZs.mono fun ω hω => ((hvc n) _ ⟨⟨by linarith [hεs' n], hst.le⟩, hω⟩).mono (hsubIoc n))
    (fun p hp => hvC n p (hsubIoc n hp)) hpath
  -- limits
  have htR : (0 : ℝ) < t := hsR.trans hstR
  have hlim : ∀ r : ℝ≥0, (s : ℝ) ≤ r → (r : ℝ) ≤ t → ∀ᵐ ω ∂Q,
      Tendsto (fun n => v n ((r : ℝ), Z r ω)) atTop (𝓝 (u ((r : ℝ), Z r ω))) := by
    intro r hr hrt
    filter_upwards [hin] with ω hω
    have hr0 : (0 : ℝ) < r := lt_of_lt_of_le hsR hr
    exact tendsto_tconv_bwdMollifier hcont hε0 hεlim
      ⟨⟨hr0, hrt⟩, hω r (by exact_mod_cast hr0) (by exact_mod_cast hrt)⟩
  have hbnd : ∀ r : ℝ≥0, (s : ℝ) ≤ r → (r : ℝ) ≤ t → ∀ n, ∀ᵐ ω ∂Q,
      |v n ((r : ℝ), Z r ω)| ≤ C := by
    intro r hr hrt n
    filter_upwards [hin] with ω hω
    have hr0 : (0 : ℝ) < r := lt_of_lt_of_le hsR hr
    exact hvC n _ ⟨⟨by linarith [hεs' n], hrt⟩,
      hω r (by exact_mod_cast hr0) (by exact_mod_cast hrt)⟩
  have hTt := tendsto_setIntegral_of_abs_le (fun n => (hDn n).1.aestronglyMeasurable)
    (hbnd t hstR.le le_rfl) (hlim t hstR.le le_rfl)
  have hTs := tendsto_setIntegral_of_abs_le (fun n => (hDn n).2.1.aestronglyMeasurable)
    (hbnd s le_rfl hstR.le) (hlim s le_rfl hstR.le)
  have hint : ∀ r : ℝ≥0, (s : ℝ) ≤ r → (r : ℝ) ≤ t →
      (∀ n, AEStronglyMeasurable (fun ω => v n ((r : ℝ), Z r ω)) Q) →
      Integrable (fun ω => u ((r : ℝ), Z r ω)) Q := by
    intro r hr hrt hm
    have hr0 : (0 : ℝ) < r := lt_of_lt_of_le hsR hr
    refine Integrable.of_bound (aestronglyMeasurable_of_tendsto_ae atTop hm (hlim r hr hrt)) C ?_
    filter_upwards [hin] with ω hω
    rw [Real.norm_eq_abs]
    exact hC _ ⟨⟨hr0, hrt⟩, hω r (by exact_mod_cast hr0) (by exact_mod_cast hrt)⟩
  refine ⟨hint t hstR.le le_rfl fun n => (hDn n).1.aestronglyMeasurable,
    hint s le_rfl hstR.le fun n => (hDn n).2.1.aestronglyMeasurable, fun A hA => ?_⟩
  refine tendsto_nhds_unique (hTt A) ((hTs A).congr fun n => ?_)
  exact ((hDn n).2.2 A hA).symm

end Pos

include hZ hU hb ha hsym hO hOU hzU hz hin hd hpde hcont hu0 hC

/-- Duality from any time `s < t` to `t`, with integrability. -/
theorem IsTestMPSolution.duality_aux_C02 {s : ℝ≥0} (hst : s < t) :
    Integrable (fun ω => u ((t : ℝ), Z t ω)) Q ∧ Integrable (fun ω => u ((s : ℝ), Z s ω)) Q ∧
      ∀ A, MeasurableSet[𝓖 s] A →
        ∫ ω in A, u ((t : ℝ), Z t ω) ∂Q = ∫ ω in A, u ((s : ℝ), Z s ω) ∂Q := by
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with h0 | h0
  swap
  · exact hZ.duality_aux_pos_C02 hU hb ha hsym hO hOU hzU hz hin hd hpde hcont hC h0 hst
  subst h0
  have htR : (0 : ℝ) < t := by exact_mod_cast hst
  have hn2 : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 2 := fun n => by positivity
  set sn : ℕ → ℝ≥0 := fun n => ⟨(t : ℝ) / ((n : ℝ) + 2), (div_pos htR (hn2 n)).le⟩ with hsn
  have hsn0 : ∀ n, 0 < sn n := fun n => by
    rw [← NNReal.coe_pos]; exact div_pos htR (hn2 n)
  have hsnt : ∀ n, sn n < t := fun n => by
    rw [← NNReal.coe_lt_coe]
    change (t : ℝ) / ((n : ℝ) + 2) < t
    rw [div_lt_iff₀ (hn2 n)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hsnR : Tendsto (fun n => (sn n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hsnl : Tendsto sn atTop (𝓝 0) := NNReal.tendsto_coe.1 (by simpa using hsnR)
  have P := fun n => hZ.duality_aux_pos_C02 hU hb ha hsym hO hOU hzU hz hin hd hpde hcont hC
    (hsn0 n) (hsnt n)
  have hi0 : Integrable (fun ω => u (((0 : ℝ≥0) : ℝ), Z 0 ω)) Q :=
    (integrable_const (u (0, z))).congr (hz.mono fun ω hω => by simp [hω])
  refine ⟨(P 0).1, hi0, fun A hA => ?_⟩
  have hbd : ∀ n, ∀ᵐ ω ∂Q, |u ((sn n : ℝ), Z (sn n) ω)| ≤ C := fun n => by
    filter_upwards [hin] with ω hω
    exact hC _ ⟨⟨by exact_mod_cast hsn0 n, by exact_mod_cast (hsnt n).le⟩,
      hω _ (hsn0 n) (hsnt n).le⟩
  have hl : ∀ᵐ ω ∂Q, Tendsto (fun n => u ((sn n : ℝ), Z (sn n) ω)) atTop
      (𝓝 (u (((0 : ℝ≥0) : ℝ), Z 0 ω))) := by
    filter_upwards [hz, hin, hZ.continuous] with ω h0 hω hc
    rw [h0, NNReal.coe_zero]
    have hp : Tendsto (fun n => ((sn n : ℝ), Z (sn n) ω)) atTop
        (𝓝[Ioc 0 (t : ℝ) ×ˢ O] (0, z)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have h2 : Tendsto (fun n => Z (sn n) ω) atTop (𝓝 z) := by
          rw [← h0]; exact (hc.tendsto 0).comp hsnl
        exact hsnR.prodMk_nhds h2
      · exact ⟨⟨by exact_mod_cast hsn0 n, by exact_mod_cast (hsnt n).le⟩,
          hω _ (hsn0 n) (hsnt n).le⟩
    exact hu0.tendsto.comp hp
  have hT := tendsto_setIntegral_of_abs_le (fun n => (P n).2.1.aestronglyMeasurable) hbd hl A
  have heq : ∀ n, ∫ ω in A, u ((sn n : ℝ), Z (sn n) ω) ∂Q = ∫ ω in A, u ((t : ℝ), Z t ω) ∂Q :=
    fun n => ((P n).2.2 A (𝓖.mono zero_le A hA)).symm
  exact tendsto_nhds_unique (hT.congr heq) tendsto_const_nhds |>.symm

/-- **Duality under `C^{0,2}` regularity, conditional form on sets.** For `s < t` and `A ∈ 𝓖_s`,
`∫_A u(t, Z_t) dQ = ∫_A u(s, Z_s) dQ`, for `u` of class `C^{0,2}` solving `∂ₜu + 𝓛u = 0`. -/
theorem IsTestMPSolution.duality_setIntegral_C02 {s : ℝ≥0} (hst : s < t) {A : Set Ω}
    (hA : MeasurableSet[𝓖 s] A) :
    ∫ ω in A, u ((t : ℝ), Z t ω) ∂Q = ∫ ω in A, u ((s : ℝ), Z s ω) ∂Q :=
  (hZ.duality_aux_C02 hU hb ha hsym hO hOU hzU hz hin hd hpde hcont hu0 hC hst).2.2 A hA

/-- **The duality identity under `C^{0,2}` regularity.** `E[u(t, Z_t)] = u(0, z)`. -/
theorem IsTestMPSolution.duality_C02 (ht : 0 < t) : ∫ ω, u ((t : ℝ), Z t ω) ∂Q = u (0, z) := by
  have h := hZ.duality_setIntegral_C02 hU hb ha hsym hO hOU hzU hz hin hd hpde hcont hu0 hC ht
    (MeasurableSet.univ (m := 𝓖 0))
  simp only [Measure.restrict_univ] at h
  rw [h, integral_congr_ae (g := fun _ => u (0, z)) (hz.mono fun ω hω => by simp [hω])]
  simp

/-- **Duality under `C^{0,2}` regularity, conditional expectation form.** For `s < t`,
`E[u(t, Z_t) | 𝓖_s] = u(s, Z_s)` a.s. -/
theorem IsTestMPSolution.condExp_duality_C02 {s : ℝ≥0} (hst : s < t) :
    Q[fun ω => u ((t : ℝ), Z t ω) | 𝓖 s] =ᵐ[Q] fun ω => u ((s : ℝ), Z s ω) := by
  obtain ⟨hψi, hLi, hI⟩ := hZ.duality_aux_C02 hU hb ha hsym hO hOU hzU hz hin hd hpde hcont hu0
    hC hst
  have hgm : AEStronglyMeasurable[𝓖 s] (fun ω => u ((s : ℝ), Z s ω)) Q := by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with h0 | h0
    · subst h0
      refine ⟨fun _ => u (0, z), stronglyMeasurable_const, ?_⟩
      filter_upwards [hz] with ω hω
      simp [hω]
    · have hmeas : Measurable[𝓖 s] (Z s) := hZ.adapted s
      refine aestronglyMeasurable_comp_continuousOn (g := fun x => u ((s : ℝ), x)) hmeas hO ?_
        (hin.mono fun ω hω => hω s h0 hst.le)
      exact hcont.comp (continuous_const.prodMk continuous_id).continuousOn
        fun x hx => ⟨⟨by exact_mod_cast h0, by exact_mod_cast hst.le⟩, hx⟩
  exact (ae_eq_condExp_of_forall_setIntegral_eq (𝓖.le s) hψi (fun A _ _ => hLi.integrableOn)
    (fun A hA _ => (hI A hA).symm) hgm).symm

end Headline

end BlockBand.Diffusion
