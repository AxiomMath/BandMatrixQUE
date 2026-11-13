module

public import BlockBand.Palm.MomentFlow.AvgLine
public import BlockBand.Palm.MomentFlow.TraceSpec
public import BlockBand.Palm.MomentFlow.BridgeIdentity
public import BlockBand.Palm.RelativeLocalizationAdapter

/-!
# The averaged local law as an `𝓛`-measurable eigenvalue-path event

* `measurableSet_forall_mem_le`: a closed condition holding on a separable parameter set `S`
  of functions measurable in `ω` and continuous in the parameter is measurable (countable dense
  subset of `S`).
* `continuousOn_freshDyson_box`: `(σ, x, h) ↦ m_σ(x + ih)` is continuous (Lipschitz) on
  `[c₀ - s₀, c₀] × [E - r₀, E + r₀] × [0, 1]` (`freshDyson_window_lipschitz`).
* **`averaged_measurable`** (hypotheses `ExternalLocalGUE`, `MDEBranchIdentification`,
  `GaussianLpGradient`): same `Cst` as `averaged_uniform`; for `0 ≤ a < c`, `c - a ≤ 1`,
  `[a, c] ⊆ [c₀ - s₀, c₀]`, an `𝓛`-measurable `B`, `P(B) ≤ N^{-D}`, such that for **every**
  `ω ∉ B` (no a.e. qualifier), every `σ ∈ [a, c]`, `|x - E| ≤ r₀/2`, `N^{-1+4ε} ≤ h ≤ 1`:
  `|(1/N) Σ_k h/((λ_k(σ) - x)² + h²) - Im m_σ(x + ih)| ≤ Cst N^ε/(Nh)`.
  `B` is the complement of the eigenvalue-only good event; it is contained in
  `Bad ∪ {ω.1 not Hermitian}` and the second set is null (`ae_fst_isHermitian`).
* `averaged_measurable_kerAt`: a pointwise rewriting lemma: a bound on
  `|(1/N) Σ_k h/((λ_k(σ) - λ_i(σ))² + h²) - Im m_σ(λ_i(σ) + ih)|` (hypothesis `hb`, e.g. from
  `averaged_measurable` at `x = λ_i(σ)`) is restated in the kernel form `Σ_j kerAt (λ(σ)) h i j`.

The event is `𝓛`-measurable outright, so no Markov disintegration (which would be needed if the
good event were not `𝓛`-measurable) is used.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open MeasureTheory Matrix Set Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Internal.Contracts.Inputs BlockBand.External BlockBand.Palm.CoarseRelative
open BlockBand.Palm
open scoped ENNReal

variable {N : ℕ}

/-- Closed conditions holding on a separable parameter set define measurable sets. -/
theorem measurableSet_forall_mem_le {Ω X : Type*} [TopologicalSpace X] {m : MeasurableSpace Ω}
    {S : Set X} [TopologicalSpace.SeparableSpace S] {f : X → Ω → ℝ}
    (hf : ∀ p ∈ S, Measurable[m] (f p)) (hc : ∀ ω, ContinuousOn (fun p => f p ω) S) :
    MeasurableSet[m] {ω | ∀ p ∈ S, f p ω ≤ 0} := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense S
  have e : {ω | ∀ p ∈ S, f p ω ≤ 0} = ⋂ d ∈ D, {ω | f (d : X) ω ≤ 0} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    refine ⟨fun h d _ => h d d.2, fun h p hp => ?_⟩
    have hcl : IsClosed {x : S | f x ω ≤ 0} :=
      isClosed_le ((hc ω).domRestrict) continuous_const
    have hsub : D ⊆ {x : S | f x ω ≤ 0} := fun d hd => h d hd
    have : (⟨p, hp⟩ : S) ∈ closure D := hDd ⟨p, hp⟩
    exact (hcl.closure_subset_iff.2 hsub) this
  rw [e]
  exact MeasurableSet.biInter hDc fun d _ => (hf d d.2) measurableSet_Iic

/-- `(σ, x, h) ↦ m_σ(x + ih)` is Lipschitz, hence continuous, on the regular box. -/
theorem continuousOn_freshDyson_box (hN : 0 < N) {F : Matrix (Fin N) (Fin N) ℂ}
    {A c₀ E r₀ s₀ v₀ : ℝ} (hK : FreshConstants c₀ r₀ s₀ v₀) (hC : FreshClass F A c₀ E r₀ s₀ v₀) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => freshDyson F p.1 ⟨p.2.1, p.2.2⟩)
      (Icc (c₀ - s₀) c₀ ×ˢ (Icc (E - r₀) (E + r₀) ×ˢ Icc 0 1)) := by
  set L := dysonLipConst c₀ s₀ v₀
  have hL : 0 ≤ L := dysonLipConst_nonneg c₀ s₀ v₀
  have hcs : 0 < c₀ - s₀ := by obtain ⟨_, _, _, _, h5, _⟩ := hK; linarith
  set ρ0 := Real.sqrt (c₀ - s₀)
  have hρ0 : 0 < ρ0 := Real.sqrt_pos.2 hcs
  refine (LipschitzOnWith.of_dist_le_mul (K := Real.toNNReal (L * (2 + 1 / ρ0)))
    fun p hp p' hp' => ?_).continuousOn
  obtain ⟨hp1, hp2, hp3⟩ := hp
  obtain ⟨hp1', hp2', hp3'⟩ := hp'
  have hx : |(⟨p.2.1, p.2.2⟩ : ℂ).re - E| ≤ r₀ := abs_le.2 ⟨by simp; linarith [hp2.1],
    by simp; linarith [hp2.2]⟩
  have hx' : |(⟨p'.2.1, p'.2.2⟩ : ℂ).re - E| ≤ r₀ := abs_le.2 ⟨by simp; linarith [hp2'.1],
    by simp; linarith [hp2'.2]⟩
  have h := freshDyson_window_lipschitz hN hK hC hp1 hp1' hx hx' hp3.1 hp3.2 hp3'.1 hp3'.2
  rw [dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
  refine h.trans ?_
  have hf : ∀ u v : ℝ × ℝ, dist u.1 v.1 ≤ dist u v := fun u v => by
    rw [Prod.dist_eq]; exact le_max_left _ _
  have hs2 : ∀ u v : ℝ × ℝ, dist u.2 v.2 ≤ dist u v := fun u v => by
    rw [Prod.dist_eq]; exact le_max_right _ _
  have hf3 : dist p.1 p'.1 ≤ dist p p' := by rw [Prod.dist_eq]; exact le_max_left _ _
  have hs3 : dist p.2 p'.2 ≤ dist p p' := by rw [Prod.dist_eq]; exact le_max_right _ _
  have hd1 : |p.1 - p'.1| ≤ dist p p' := by
    rw [← Real.dist_eq]; exact hf3
  have hd2 : |p.2.1 - p'.2.1| ≤ dist p p' := by
    rw [← Real.dist_eq]; exact (hf p.2 p'.2).trans hs3
  have hd3 : |p.2.2 - p'.2.2| ≤ dist p p' := by
    rw [← Real.dist_eq]; exact (hs2 p.2 p'.2).trans hs3
  have hz : ‖(⟨p.2.1, p.2.2⟩ : ℂ) - ⟨p'.2.1, p'.2.2⟩‖ ≤ 2 * dist p p' := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [Complex.sub_re, Complex.sub_im]
    linarith
  have hs : |p.1 - p'.1| / ρ0 ≤ 1 / ρ0 * dist p p' := by
    rw [div_eq_mul_inv, one_div, mul_comm]
    exact mul_le_mul_of_nonneg_left hd1 (inv_nonneg.2 hρ0.le)
  calc L * (‖(⟨p.2.1, p.2.2⟩ : ℂ) - ⟨p'.2.1, p'.2.2⟩‖ + |p.1 - p'.1| / ρ0)
      ≤ L * (2 * dist p p' + 1 / ρ0 * dist p p') := by gcongr
    _ = L * (2 + 1 / ρ0) * dist p p' := by ring

/-- The eigenvalue form of the averaged-law deviation, minus its bound. -/
def avgDev (F : Matrix (Fin N) (Fin N) ℂ) (a b : ℝ) (p : ℝ × ℝ × ℝ) (ω : FlowSample N) : ℝ :=
  |(N : ℝ)⁻¹ * ∑ k, p.2.2 / ((flowEigenvalue F a ω p.1 k - p.2.1) ^ 2 + p.2.2 ^ 2) -
      (freshDyson F p.1 ⟨p.2.1, p.2.2⟩).im| - b / ((N : ℝ) * p.2.2)

/-- **`𝓛`-measurable form of the averaged local law.** -/
theorem averaged_measurable (hELG : ExternalLocalGUE) (hMDE : MDEBranchIdentification)
    (hLp : GaussianLpGradient) {A c₀ r₀ s₀ v₀ : ℝ} (hK : FreshConstants c₀ r₀ s₀ v₀) {ε : ℝ}
    (hε : 0 < ε) (hε4 : ε < 1 / 4) :
    ∃ Cst : ℝ, 0 ≤ Cst ∧ ∀ D : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c₀ E r₀ s₀ v₀ →
      ∀ a c : ℝ, 0 ≤ a → a < c → c - a ≤ 1 → c₀ - s₀ ≤ a → c ≤ c₀ →
      ∃ B : Set (FlowSample N), MeasurableSet[pathSigma F a a c] B ∧
        flowLaw N a B ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) ∧
        ∀ ω ∉ B, ∀ σ ∈ Icc a c, ∀ x : ℝ, |x - E| ≤ r₀ / 2 →
          ∀ h : ℝ, (N : ℝ) ^ (-(1 - 4 * ε)) ≤ h → h ≤ 1 →
            |(N : ℝ)⁻¹ * ∑ k, h / ((flowEigenvalue F a ω σ k - x) ^ 2 + h ^ 2) -
                (freshDyson F σ ⟨x, h⟩).im| ≤ Cst * (N : ℝ) ^ ε / ((N : ℝ) * h) := by
  obtain ⟨Cst, hCst, hAv⟩ := averaged_uniform hELG hMDE hLp (A := A) hK hε hε4
  refine ⟨Cst, hCst, fun D => ?_⟩
  obtain ⟨N₁, hN₁⟩ := hAv D
  refine ⟨max N₁ 1, fun N hN F E hC a c ha hac hca hac₀ hc => ?_⟩
  have hNpos : 0 < N := lt_of_lt_of_le one_pos (le_of_max_le_right hN)
  have hNp : (0 : ℝ) < N := by exact_mod_cast hNpos
  obtain ⟨Bad, -, hPB, hgood⟩ := hN₁ N (le_of_max_le_left hN) F E hC a (c - a) ha
    (by linarith) hca hac₀ (by linarith)
  have hac' : a + (c - a) = c := by ring
  rw [hac'] at hgood
  set lo : ℝ := (N : ℝ) ^ (-(1 - 4 * ε))
  have hlo : 0 < lo := Real.rpow_pos_of_pos hNp _
  set b : ℝ := Cst * (N : ℝ) ^ ε
  set S : Set (ℝ × ℝ × ℝ) := Icc a c ×ˢ (Icc (E - r₀ / 2) (E + r₀ / 2) ×ˢ Icc lo 1)
  set G : Set (FlowSample N) := {ω | ∀ p ∈ S, avgDev F a b p ω ≤ 0}
  have hr0 : 0 < r₀ := hK.2.2.1
  have hSbox : S ⊆ Icc (c₀ - s₀) c₀ ×ˢ (Icc (E - r₀) (E + r₀) ×ˢ Icc 0 1) := by
    rintro p ⟨h1, h2, h3⟩
    exact ⟨⟨hac₀.trans h1.1, h1.2.trans hc⟩, ⟨by linarith [h2.1], by linarith [h2.2]⟩,
      ⟨hlo.le.trans h3.1, h3.2⟩⟩
  have hGm : MeasurableSet[pathSigma F a a c] G := by
    refine measurableSet_forall_mem_le (fun p hp => ?_) (fun ω => ?_)
    · obtain ⟨h1, -, h3⟩ := hp
      have hlam : ∀ k, Measurable[pathSigma F a a c] fun ω => flowEigenvalue F a ω p.1 k :=
        fun k => measurable_flowEigenvalue_pathSigma F a a c h1 k
      unfold avgDev
      have h1 : ∀ k, Measurable[pathSigma F a a c] fun ω =>
          p.2.2 / ((flowEigenvalue F a ω p.1 k - p.2.1) ^ 2 + p.2.2 ^ 2) :=
        fun k => ((((hlam k).sub_const _).pow_const 2).add_const _).const_div _
      have h2 : Measurable[pathSigma F a a c] fun ω =>
          ∑ k, p.2.2 / ((flowEigenvalue F a ω p.1 k - p.2.1) ^ 2 + p.2.2 ^ 2) :=
        Finset.measurable_sum _ fun k _ => h1 k
      have h3 := ((h2.const_mul ((N : ℝ)⁻¹)).sub_const
        (freshDyson F p.1 ⟨p.2.1, p.2.2⟩).im)
      exact (measurable_abs.comp h3).sub_const _
    · unfold avgDev
      have hpos : ∀ p ∈ S, 0 < p.2.2 := fun p hp => hlo.trans_le hp.2.2.1
      refine ContinuousOn.sub (ContinuousOn.abs (ContinuousOn.sub ?_ ?_)) ?_
      · refine continuousOn_const.mul (continuousOn_finsetSum _ fun k _ => ?_)
        refine ContinuousOn.div (continuous_snd.comp continuous_snd).continuousOn ?_
          (fun p hp => by have := hpos p hp; positivity)
        refine ContinuousOn.add (ContinuousOn.pow (ContinuousOn.sub ?_
          (continuous_fst.comp continuous_snd).continuousOn) 2)
          ((continuous_snd.comp continuous_snd).continuousOn.pow 2)
        exact ((continuous_flowEigenvalue hC.1 a ω k).comp continuous_fst).continuousOn
      · exact Complex.continuous_im.comp_continuousOn
          ((continuousOn_freshDyson_box hNpos hK hC).mono hSbox)
      · refine continuousOn_const.div (continuousOn_const.mul
          (continuous_snd.comp continuous_snd).continuousOn) ?_
        intro p hp; have := hpos p hp; positivity
  refine ⟨Gᶜ, hGm.compl, ?_, ?_⟩
  · have hsub : Gᶜ ⊆ Bad ∪ {ω | ¬ ω.1.IsHermitian} := by
      intro ω hω
      by_contra hcon
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hcon
      apply hω
      intro p hp
      obtain ⟨h1, h2, h3⟩ := hp
      have hx : |p.2.1 - E| ≤ r₀ / 2 := abs_le.2 ⟨by linarith [h2.1], by linarith [h2.2]⟩
      have hb := hgood ω hcon.1 hcon.2 p.1 h1 p.2.1 hx p.2.2 h3.1 h3.2
      have hH := flowMatrix_isHermitian hC.1 a hcon.2 p.1
      have him := normalizedTrace_resolvent_im hH p.2.1 (hlo.trans_le h3.1).ne'
      unfold avgDev
      have : |(N : ℝ)⁻¹ * ∑ k, p.2.2 / ((flowEigenvalue F a ω p.1 k - p.2.1) ^ 2 + p.2.2 ^ 2) -
          (freshDyson F p.1 ⟨p.2.1, p.2.2⟩).im| ≤ b / ((N : ℝ) * p.2.2) := by
        have e1 : (N : ℝ)⁻¹ * ∑ k, p.2.2 / ((flowEigenvalue F a ω p.1 k - p.2.1) ^ 2 +
            p.2.2 ^ 2) = (CEH.normalizedTrace ((flowMatrix F a ω p.1 -
              (⟨p.2.1, p.2.2⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹)).im := him.symm
        rw [e1, ← Complex.sub_im]
        exact (Complex.abs_im_le_norm _).trans hb
      linarith
    have hnull : flowLaw N a {ω | ¬ ω.1.IsHermitian} = 0 :=
      ae_iff.1 (RelativeLocalization.ae_fst_isHermitian a)
    calc flowLaw N a Gᶜ ≤ flowLaw N a (Bad ∪ {ω | ¬ ω.1.IsHermitian}) := measure_mono hsub
      _ ≤ flowLaw N a Bad + flowLaw N a {ω | ¬ ω.1.IsHermitian} := measure_union_le _ _
      _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := by rw [hnull, add_zero]; exact hPB
  · intro ω hω σ hσ x hx h hh hh1
    have hωG : ω ∈ G := not_not.1 hω
    have hp : ((σ, x, h) : ℝ × ℝ × ℝ) ∈ S :=
      ⟨hσ, ⟨by linarith [(abs_le.1 hx).1], by linarith [(abs_le.1 hx).2]⟩, ⟨hh, hh1⟩⟩
    have := hωG _ hp
    unfold avgDev at this
    simp only at this
    have e : b / ((N : ℝ) * h) = Cst * (N : ℝ) ^ ε / ((N : ℝ) * h) := rfl
    linarith

/-- Pointwise rewriting: a bound on the averaged-law deviation at `x = λ_i(σ)` (hypothesis
`hb`) is the same bound in the kernel form `Σ_j kerAt`. No event, no window condition. -/
theorem averaged_measurable_kerAt {F : Matrix (Fin N) (Fin N) ℂ} {a : ℝ} {ω : FlowSample N}
    {σ h b : ℝ} (i : Fin N) (hb : |(N : ℝ)⁻¹ * ∑ k, h / ((flowEigenvalue F a ω σ k -
      flowEigenvalue F a ω σ i) ^ 2 + h ^ 2) -
        (freshDyson F σ ⟨flowEigenvalue F a ω σ i, h⟩).im| ≤ b) :
    |∑ j, kerAt (fun k => flowEigenvalue F a ω σ k) h i j -
        (freshDyson F σ ⟨flowEigenvalue F a ω σ i, h⟩).im| ≤ b := by
  have e : ∑ j, kerAt (fun k => flowEigenvalue F a ω σ k) h i j =
      (N : ℝ)⁻¹ * ∑ k, h / ((flowEigenvalue F a ω σ k - flowEigenvalue F a ω σ i) ^ 2 + h ^ 2) := by
    rw [Finset.mul_sum]; rfl
  rw [e]; exact hb

end BlockBand.Palm.MomentFlow
