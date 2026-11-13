module

public import BlockBand.Center.SmoothConstructionPointwise

/-!
# The deterministic construction of the smooth center, assembled

`ScSmoothConstructionOffPole` is the deterministic construction of the smooth center with the
derivative clause required only off the exterior poles. `scSmoothConstructionOffPole_holds`
proves it with `Φ = scnPhi b ϑ` and one constant for all bulk ranks, and
`smoothCenter_holds_of_offPole` derives `SmoothCenterContract cst0` from it.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

namespace BlockBand.Center

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.QUE BlockBand.QUE.Fourier BlockBand.Model.Construction
open BlockBand.Layers BlockBand.QUE.PairResidual
open scoped ENNReal NNReal ComplexConjugate Matrix.Norms.L2Operator

/-!
## 1. The construction off the exterior poles
-/

/-- **`ScSmoothConstruction` off the exterior poles**: as
`ScSmoothConstruction`, except that the derivative clause
assumes `det(H^{(e)}_R - E) ≠ 0`. Quantifiers, objects and norms as in `ScSmoothConstruction`:
`b, ϑ` first, then `κ' > 0`, `C ≥ 0` and `Φ` with the deterministic fields of
`SmoothCenterContract cst0`; for `p.b = b`, `ϑ`-bulk ranks and Hermitian, ring-banded residuals
with invertible exterior bonds, `|Φ| ≤ C(|ε_{e,e}| + |ε_{e,e+1}|)` at every `E` and, off the
exterior poles, `|∂_{ξ_g}Φ| ≤ C(|∂_{ξ_g}ε_{e,e}| + |∂_{ξ_g}ε_{e,e+1}| + (|ε_{e,e}| +
|ε_{e,e+1}|)|λ_{eg}|)` for `g ≠ e`. -/
def ScSmoothConstructionOffPole : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ ϑ : ℝ, 0 < ϑ → ϑ < 1 / 2 →
    ∃ (κ' C : ℝ), 0 < κ' ∧ 0 ≤ C ∧
    ∃ Φ : ∀ (p : Parameters), Fin p.N → ZMod p.n → p.SiteMatrix → ℝ → ℝ,
      (∀ (p : Parameters) α e (H : p.SiteMatrix) (E : ℝ), |Φ p α e H E| ≤ 1) ∧
      (∀ (p : Parameters) α e, Measurable (fun x : p.SiteMatrix × ℝ => Φ p α e x.1 x.2)) ∧
      (∀ (p : Parameters) α e (H₀ : p.SiteMatrix), H₀.IsHermitian →
        IsRingBanded p H₀ → ExteriorBondsInvertible p e H₀ →
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x : (ZMod p.n → ℝ) × ℝ =>
            Φ p α e (H₀ + ∑ g, (x.1 g : ℂ) • pairProjector p g) x.2)) ∧
      (∀ (p : Parameters) α e (H₀ : p.SiteMatrix) (E : ℝ), E ∉ bulkInterval κ' →
        Φ p α e H₀ E = 0) ∧
      (∀ (p : Parameters), p.b = b → ∀ α, IsBulkRank p ϑ α → ∀ e (H₀ : p.SiteMatrix) (E : ℝ),
        H₀.IsHermitian → IsRingBanded p H₀ → ExteriorBondsInvertible p e H₀ →
        InCenterDomain p e cst0 α H₀ E → Φ p α e H₀ E = dysonCenter p e cst0 α H₀ E) ∧
      (∀ (p : Parameters), p.b = b → ∀ α, IsBulkRank p ϑ α → ∀ e (H₀ : p.SiteMatrix) (E : ℝ),
        H₀.IsHermitian → IsRingBanded p H₀ → ExteriorBondsInvertible p e H₀ →
        |Φ p α e H₀ E| ≤ C * (‖tgtEps p e H₀ E e‖ + ‖tgtEps p e H₀ E (e + 1)‖) ∧
        ((exteriorBlock p e H₀ - (E : ℂ) • 1).det ≠ 0 →
        ∀ g : ZMod p.n, g ≠ e →
          |deriv (fun t : ℝ => Φ p α e (H₀ + (t : ℂ) • pairProjector p g) E) 0| ≤
            C * (‖tgtXiDeriv p (fun H => tgtEps p e H E e) g H₀‖ +
              ‖tgtXiDeriv p (fun H => tgtEps p e H E (e + 1)) g H₀‖ +
              (‖tgtEps p e H₀ E e‖ + ‖tgtEps p e H₀ E (e + 1)‖) * ‖tgtLambda p e g H₀ E‖)))

/-!
## 2. One constant for all bulk ranks
-/

section Uniform

/-- **Rank-uniform constant**: summing the level constants of `scp_level` over the finitely many
levels `k ≤ ctrLevel(ϑ/2)` of `ϑ`-bulk ranks (`κ_α ≥ ϑ/2`). -/
theorem scs_uniform {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2) {ϑ : ℝ} (hϑ : 0 < ϑ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : Parameters), p.b = b → ∀ α : Fin p.N, IsBulkRank p ϑ α →
      ∀ (e : ZMod p.n) (H₀ : p.SiteMatrix) (E : ℝ),
      H₀.IsHermitian → IsRingBanded p H₀ → ExteriorBondsInvertible p e H₀ →
      (exteriorBlock p e H₀ - (E : ℂ) • 1).det ≠ 0 →
      |scnPhi b ϑ p α e H₀ E| ≤ C * (‖tgtEps p e H₀ E e‖ + ‖tgtEps p e H₀ E (e + 1)‖) ∧
      ∀ g : ZMod p.n,
        |deriv (fun t : ℝ => scnPhi b ϑ p α e (H₀ + (t : ℂ) • pairProjector p g) E) 0| ≤
          C * (‖tgtXiDeriv p (fun H => tgtEps p e H E e) g H₀‖ +
            ‖tgtXiDeriv p (fun H => tgtEps p e H E (e + 1)) g H₀‖ +
            (‖tgtEps p e H₀ E e‖ + ‖tgtEps p e H₀ E (e + 1)‖) * ‖tgtLambda p e g H₀ E‖) := by
  choose C hC0 hC using fun k : ℕ => scp_level hb0 hb1 hϑ k
  set K := ctrLevel (ϑ / 2) with hK
  refine ⟨∑ k ∈ Finset.range (K + 1), C k, Finset.sum_nonneg fun k _ => hC0 k, ?_⟩
  intro p hpb α hα e H₀ E hH hb hbd hdet
  set k := ctrLevel (rankMargin p α) with hk
  have hkK : k ≤ K := ctrLevel_mono (by linarith) (ctr_rankMargin_ge hϑ α hα)
  have hCk : C k ≤ ∑ k ∈ Finset.range (K + 1), C k :=
    Finset.single_le_sum (fun j _ => hC0 j) (Finset.mem_range.mpr (by omega))
  obtain ⟨h1, h2⟩ := hC k p hpb α hα hk.symm e H₀ E hH hb hbd hdet
  refine ⟨h1.trans (mul_le_mul_of_nonneg_right hCk (by positivity)), fun g => ?_⟩
  exact (h2 g).trans (mul_le_mul_of_nonneg_right hCk (by positivity))

/-- **`|j^{sm}_e| ≤ C ε_e` at every energy**, also at the exterior poles (by continuity in `E`:
the poles of `E ↦ det(H_R - E)` are isolated, `scn_eventually_det_ne`, and both sides are
continuous in `E` along the line, `scn_phi_contDiff`, `scn_contDiffAt_eps`). -/
theorem scs_abs_phi_le {b ϑ : ℝ} (hϑ : 0 < ϑ) {C : ℝ} (hC0 : 0 ≤ C) {p : Parameters}
    {α : Fin p.N} (hα : IsBulkRank p ϑ α) {e : ZMod p.n} {H₀ : p.SiteMatrix}
    (hH : H₀.IsHermitian) (hb : IsRingBanded p H₀) (hbd : ExteriorBondsInvertible p e H₀)
    (hC : ∀ E : ℝ, (exteriorBlock p e H₀ - (E : ℂ) • 1).det ≠ 0 →
      |scnPhi b ϑ p α e H₀ E| ≤ C * (‖tgtEps p e H₀ E e‖ + ‖tgtEps p e H₀ E (e + 1)‖))
    (E : ℝ) : |scnPhi b ϑ p α e H₀ E| ≤ C * (‖tgtEps p e H₀ E e‖ + ‖tgtEps p e H₀ E (e + 1)‖) := by
  by_cases hdet : (exteriorBlock p e H₀ - (E : ℂ) • 1).det ≠ 0
  · exact hC E hdet
  set κ := rankMargin p α with hκ
  have hκ0 : 0 < κ := scn_rankMargin_pos hϑ hα
  have hκ1 : κ ≤ 1 := scn_rankMargin_le_one α
  obtain ⟨-, -, hm⟩ := scn_mid_bounds hκ0 hκ1
  by_cases hEo : 2 - scnMid κ ≤ |E|
  · rw [scn_phi_zero_of_energy hEo, abs_zero]; positivity
  push Not at hEo
  have hE2 : |E| < 2 := by linarith [ctrTheta_pos (ctrLevel κ)]
  set γ : ℝ → (ZMod p.n → ℝ) × ℝ := fun E' => ((0 : ZMod p.n → ℝ), E') with hγ
  have hγc : Continuous γ := continuous_const.prodMk continuous_id
  have hf : ContinuousAt (fun E' : ℝ => |scnPhi b ϑ p α e H₀ E'|) E := by
    have h := (scn_phi_contDiff (e := e) b ϑ hϑ α hH hb hbd).continuous.comp hγc
    have heq : (fun E' : ℝ => scnPhi b ϑ p α e H₀ E') =
        (fun x : (ZMod p.n → ℝ) × ℝ => scnPhi b ϑ p α e (scnLine H₀ x) x.2) ∘ γ := by
      funext E'; simp only [Function.comp_apply, hγ, scb_line_zero]
    rw [← heq] at h
    exact (continuous_abs.comp h).continuousAt
  have hε : ∀ k : ZMod p.n, ContinuousAt (fun E' : ℝ => ‖tgtEps p e H₀ E' k‖) E := by
    intro k
    have h := (scn_contDiffAt_eps hH hb hbd (x := γ E) hE2 k).continuousAt.comp
      hγc.continuousAt
    have heq : (fun E' : ℝ => tgtEps p e H₀ E' k) =
        (fun y : (ZMod p.n → ℝ) × ℝ => tgtEps p e (scnLine H₀ y) y.2 k) ∘ γ := by
      funext E'; simp only [Function.comp_apply, hγ, scb_line_zero]
    rw [← heq] at h
    exact continuous_norm.continuousAt.comp h
  have hg : ContinuousAt (fun E' : ℝ =>
      C * (‖tgtEps p e H₀ E' e‖ + ‖tgtEps p e H₀ E' (e + 1)‖)) E :=
    continuousAt_const.mul ((hε e).add (hε (e + 1)))
  have hev : ∀ᶠ E' in 𝓝[≠] E, |scnPhi b ϑ p α e H₀ E'| ≤
      C * (‖tgtEps p e H₀ E' e‖ + ‖tgtEps p e H₀ E' (e + 1)‖) := by
    filter_upwards [scn_eventually_det_ne (exteriorBlock p e H₀) E] with E' hE'
    exact hC E' hE'
  exact le_of_tendsto_of_tendsto (hf.tendsto.mono_left nhdsWithin_le_nhds)
    (hg.tendsto.mono_left nhdsWithin_le_nhds) hev

end Uniform

/-!
## 3. The construction
-/

/-- **The smooth center, deterministic part, off the exterior poles**
(`ScSmoothConstructionOffPole`). `κ' = ϑ/4`, `Φ = scnPhi b ϑ` (`j^{sm}_e = χ_E(E)χ(ε_e²)j_e`),
`C` the rank-uniform constant of `scs_uniform`. -/
theorem scSmoothConstructionOffPole_holds : ScSmoothConstructionOffPole := by
  intro b hb0 hb1 ϑ hϑ0 _hϑ1
  obtain ⟨C, hC0, hC⟩ := scs_uniform hb0 hb1 hϑ0
  refine ⟨ϑ / 4, C, by positivity, hC0, scnPhi b ϑ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p α e H E; exact scn_abs_phi_le b ϑ α H E
  · intro p α e; exact scn_measurable_phi b ϑ α
  · intro p α e H₀ hH hb hbd
    exact scn_phi_contDiff b ϑ hϑ0 α hH hb hbd
  · intro p α e H₀ E hE
    by_cases hc : p.b = b ∧ IsBulkRank p ϑ α
    · have hκ := ctr_rankMargin_ge hϑ0 α hc.2
      have hθ := ctrTheta_pos (ctrLevel (rankMargin p α))
      have hmid : ϑ / 4 ≤ scnMid (rankMargin p α) := by unfold scnMid; linarith
      refine scn_phi_zero_of_energy ?_
      unfold bulkInterval at hE
      rw [Set.mem_Icc, not_and_or] at hE
      rcases hE with h | h
      · push Not at h
        rw [abs_of_neg (by linarith)]; linarith
      · push Not at h
        rw [abs_of_pos (by linarith)]; linarith
    · exact scn_phi_of_not fun h => hc ⟨h.1, h.2.1⟩
  · intro p hpb α hα e H₀ E hH _hb _hbd hdom
    exact scn_phi_agree hϑ0 hpb hα hH hdom
  · intro p hpb α hα e H₀ E hH hb hbd
    refine ⟨scs_abs_phi_le hϑ0 hC0 hα hH hb hbd
      (fun E' hE' => (hC p hpb α hα e H₀ E' hH hb hbd hE').1) E, fun hdet g _hg => ?_⟩
    exact (hC p hpb α hα e H₀ E hH hb hbd hdet).2 g

/-!
## 4. `SmoothCenterContract cst0` from the construction
-/

/-- **The smooth center lemma from the off-pole construction** (`SmoothCenterContract cst0`):
the proof of `smoothCenter_holds_of` with `ScSmoothConstructionOffPole` in place of
`ScSmoothConstruction`; the only change is that the derivative clause is used on the
almost-sure event `det(H^{(e)}_R - E) ≠ 0` (`tgt_ae_residual_exterior_det`, deterministic `E`).
Hypotheses: `TaggedTraceStatement`, `ScFixedWidthTaggedMoments` (expected to fail as stated: at
`W = 1` the tail of `λ_{eg}` is `≍ t^{-3}`, so its `L^q` norms are infinite for `q ≥ 3`),
`CenterDomainContract cst0` and `ScSmoothConstructionOffPole`
(`scSmoothConstructionOffPole_holds`). Law, norms and uniformity as in
`smoothCenter_holds_of`. -/
theorem smoothCenter_holds_of_offPole (htt : TaggedTraceStatement)
    (hfw : ScFixedWidthTaggedMoments) (hdom : CenterDomainContract cst0)
    (hcon : ScSmoothConstructionOffPole) :
    SmoothCenterContract cst0 := by
  intro b hb hb' ϑ T hϑ0 hϑ1
  obtain ⟨κ', C, hκ', hC, Φ, hbdd, hmeas, hsm, hsupp, hagree, hpt⟩ := hcon b hb hb' ϑ hϑ0 hϑ1
  obtain ⟨ρ, hρ0, hρ1, htq⟩ := htt.1 b hb hb' κ' T hκ'
  refine ⟨ρ, κ', hρ0, hρ1, hκ', Φ, hbdd, hmeas, hsm, hsupp, hagree, ?_, ?_⟩
  · -- the moment and derivative bounds of the smooth center
    intro q hq
    have hq2 : 1 ≤ 2 * q := by linarith
    obtain ⟨C1, W1, h1⟩ := htq q hq
    obtain ⟨C2, W2, h2⟩ := htq (2 * q) hq2
    set W₁ : ℝ := max (max W1 W2) 1 with hW₁
    obtain ⟨C3, h3⟩ := hfw b hb hb' κ' T hκ' q hq W₁
    obtain ⟨C4, h4⟩ := hfw b hb hb' κ' T hκ' (2 * q) hq2 W₁
    set c1 : ℝ := max C1 0 with hc1
    set c2 : ℝ := max C2 0 with hc2
    set c3 : ℝ := max (max C3 C4) 0 with hc3
    have hc10 : 0 ≤ c1 := le_max_right _ _
    have hc20 : 0 ≤ c2 := le_max_right _ _
    have hc30 : 0 ≤ c3 := le_max_right _ _
    have hW₁1 : 1 ≤ W₁ := le_max_right _ _
    set K1 : ℝ := C * (2 * c1 + 3 * c2 ^ 2) with hK1
    set K2 : ℝ := C * (2 * c3 + 3 * c3 ^ 2) * Real.sqrt W₁ with hK2
    have hK10 : 0 ≤ K1 := by positivity
    have hK20 : 0 ≤ K2 := by positivity
    refine ⟨max (2 * C * c1) W₁ + K1 + K2, ?_⟩
    intro p hpb hnT model S hS α hα e g E
    have hP : IsProbabilityMeasure S.X.P := csm_isProb_ext S.X
    have hG := pc_isCenterSplitting_of_exact S hS e
    have hW1 : (1 : ℝ) ≤ p.W := by exact_mod_cast p.W_pos
    have hW0 : (0 : ℝ) < p.W := by linarith
    have hCq0 : 0 ≤ max (2 * C * c1) W₁ + K1 + K2 := by
      have : 0 ≤ max (2 * C * c1) W₁ := le_trans (by linarith) (le_max_right _ _)
      positivity
    have hden : 0 ≤ ρ ^ edgeDistance p e g + (p.W : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
    by_cases hE : E ∈ bulkInterval κ'
    swap
    · have hz : ∀ H : p.SiteMatrix, Φ p α e H E = 0 := fun H => hsupp p α e H E hE
      refine ⟨?_, fun _ => ?_⟩
      · simp only [hz]
        rw [show (fun _ : S.X.Ω => (0 : ℝ)) = 0 from rfl, eLpNorm_zero]; exact zero_le
      · simp only [hz, deriv_const]
        rw [show (fun _ : S.X.Ω => (0 : ℝ)) = 0 from rfl, eLpNorm_zero]; exact zero_le
    set res : S.X.Ω → p.SiteMatrix := fun ω => S.X.Hm ω - embedPair p e (S.G e ω) with hresdef
    have hres : Measurable res := csm_measurable_res S.X (S.measurable_G e)
    have hgood := sc_ae_good S.X hG
    have hεm : ∀ k, AEStronglyMeasurable (fun ω => tgtEps p e (res ω) E k) S.X.P := fun k =>
      ((tgt_measurable_eps e E k).comp hres).aestronglyMeasurable
    have hΦm : AEStronglyMeasurable (fun ω => Φ p α e (res ω) E) S.X.P :=
      ((hmeas p α e).comp (hres.prodMk measurable_const)).aestronglyMeasurable
    refine ⟨?_, fun hge => ?_⟩
    · -- `‖j^{sm}_e(E)‖_q ≤ C_q/W`
      by_cases hWl : max W1 W2 < (p.W : ℝ)
      · have hb1 := h1 p hpb hnT (lt_of_le_of_lt (le_max_left _ _) hWl) model e S.X (S.G e) hG E hE
        have hk : ∀ k : ZMod p.n, (k = e ∨ k = e + 1) →
            eLpNorm (fun ω => tgtEps p e (res ω) E k) (ENNReal.ofReal q) S.X.P ≤
              ENNReal.ofReal (c1 / p.W) := fun k hk =>
          (hb1.1 k hk).trans (ENNReal.ofReal_le_ofReal
            (div_le_div_of_nonneg_right (le_max_left _ _) hW0.le))
        have hcore := sc_moment_core hΦm (hεm e) (hεm (e + 1)) hq hC (by positivity)
          (by
            filter_upwards [hgood] with ω hω
            exact (hpt p hpb α hα e (res ω) E hω.1 hω.2.1 hω.2.2).1)
          (hk e (Or.inl rfl)) (hk (e + 1) (Or.inr rfl))
        refine hcore.trans (ENNReal.ofReal_le_ofReal ?_)
        rw [show C * (2 * (c1 / p.W)) = (2 * C * c1) / p.W by ring]
        refine div_le_div_of_nonneg_right ?_ hW0.le
        have : 2 * C * c1 ≤ max (2 * C * c1) W₁ := le_max_left _ _
        linarith
      · push Not at hWl
        have hb : eLpNorm (fun ω => Φ p α e (res ω) E) (ENNReal.ofReal q) S.X.P ≤
            ENNReal.ofReal 1 := by
          refine (eLpNorm_le_of_ae_bound (C := 1) hΦm
            (Filter.Eventually.of_forall fun ω => ?_)).trans ?_
          · rw [Real.norm_eq_abs]; exact hbdd p α e _ E
          · simp
        refine hb.trans (ENNReal.ofReal_le_ofReal ?_)
        rw [le_div_iff₀ hW0, one_mul]
        have : W₁ ≤ max (2 * C * c1) W₁ := le_max_right _ _
        have : (p.W : ℝ) ≤ W₁ := hWl.trans (le_max_left _ _)
        linarith
    · -- `‖∂_{ξ_g} j^{sm}_e(E)‖_q ≤ C_q(ρ^{d(e,g)} + W^{-1/2})`
      have hdm : ∀ k, AEStronglyMeasurable (fun ω => tgtXiDeriv p (fun H => tgtEps p e H E k) g
          (res ω)) S.X.P := fun k => sc_aesm_xiDeriv S.X hG hκ' hE g k
      have hlm : AEStronglyMeasurable (fun ω => tgtLambda p e g (res ω) E) S.X.P :=
        ((sc_measurable_lambda e g E).comp hres).aestronglyMeasurable
      have hFm := sc_aesm_derivPhi S.X hG (Φ p α e) (hmeas p α e) (hsm p α e) g E
      have hae : ∀ᵐ ω ∂S.X.P, |deriv (fun t : ℝ =>
          Φ p α e (res ω + (t : ℂ) • pairProjector p g) E) 0| ≤
          C * (‖tgtXiDeriv p (fun H => tgtEps p e H E e) g (res ω)‖ +
            ‖tgtXiDeriv p (fun H => tgtEps p e H E (e + 1)) g (res ω)‖ +
            (‖tgtEps p e (res ω) E e‖ + ‖tgtEps p e (res ω) E (e + 1)‖) *
              ‖tgtLambda p e g (res ω) E‖) := by
        filter_upwards [hgood, tgt_ae_residual_exterior_det S.X hG E] with ω hω hdω
        exact (hpt p hpb α hα e (res ω) E hω.1 hω.2.1 hω.2.2).2 hdω g hge
      by_cases hWl : max W1 W2 < (p.W : ℝ)
      · have hWa : W1 < (p.W : ℝ) := lt_of_le_of_lt (le_max_left _ _) hWl
        have hWb : W2 < (p.W : ℝ) := lt_of_le_of_lt (le_max_right _ _) hWl
        have hb1 := h1 p hpb hnT hWa model e S.X (S.G e) hG E hE
        have hb2 := h2 p hpb hnT hWb model e S.X (S.G e) hG E hE
        set A : ℝ := c1 * (ρ ^ edgeDistance p e g + (p.W : ℝ) ^ (-(1 / 2 : ℝ))) with hA
        have hd : ∀ k : ZMod p.n, (k = e ∨ k = e + 1) →
            eLpNorm (fun ω => tgtXiDeriv p (fun H => tgtEps p e H E k) g (res ω))
              (ENNReal.ofReal q) S.X.P ≤ ENNReal.ofReal A := fun k hk =>
          (hb1.2.2 g hge k hk).trans (ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_right (le_max_left _ _) hden))
        have he : ∀ k : ZMod p.n, (k = e ∨ k = e + 1) →
            eLpNorm (fun ω => tgtEps p e (res ω) E k) (ENNReal.ofReal (2 * q)) S.X.P ≤
              ENNReal.ofReal (c2 / p.W) := fun k hk =>
          (hb2.1 k hk).trans (ENNReal.ofReal_le_ofReal
            (div_le_div_of_nonneg_right (le_max_left _ _) hW0.le))
        have hl : eLpNorm (fun ω => tgtLambda p e g (res ω) E) (ENNReal.ofReal (2 * q)) S.X.P ≤
            ENNReal.ofReal c2 := (hb2.2.1 g hge).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
        have hcore := sc_deriv_core hFm (hdm e) (hdm (e + 1)) (hεm e) (hεm (e + 1)) hlm hq hC
          (by positivity) (by positivity) hc20 hW0 hae (hd e (Or.inl rfl)) (hd (e + 1) (Or.inr rfl))
          (he e (Or.inl rfl)) (he (e + 1) (Or.inr rfl)) hl
        refine hcore.trans (ENNReal.ofReal_le_ofReal ?_)
        have hinv := sc_inv_le_rpow hW1
        have hρd : 0 ≤ ρ ^ edgeDistance p e g := by positivity
        have h1W : 1 / (p.W : ℝ) ≤ ρ ^ edgeDistance p e g + (p.W : ℝ) ^ (-(1 / 2 : ℝ)) := by
          linarith
        have hkey : 2 * A + 2 * p.W * (c2 / p.W) ^ 2 + c2 ^ 2 / (2 * p.W) ≤
            (2 * c1 + 3 * c2 ^ 2) * (ρ ^ edgeDistance p e g + (p.W : ℝ) ^ (-(1 / 2 : ℝ))) := by
          have e1 : 2 * (p.W : ℝ) * (c2 / p.W) ^ 2 = 2 * c2 ^ 2 * (1 / p.W) := by
            field_simp
          have e2 : c2 ^ 2 / (2 * (p.W : ℝ)) ≤ c2 ^ 2 * (1 / p.W) := by
            rw [div_le_iff₀ (by positivity)]
            have : c2 ^ 2 * (1 / (p.W : ℝ)) * (2 * p.W) = 2 * c2 ^ 2 := by field_simp
            nlinarith [sq_nonneg c2]
          rw [e1, hA]
          nlinarith [mul_le_mul_of_nonneg_left h1W (show 0 ≤ c2 ^ 2 by positivity)]
        calc C * (2 * A + 2 * p.W * (c2 / p.W) ^ 2 + c2 ^ 2 / (2 * p.W))
            ≤ C * ((2 * c1 + 3 * c2 ^ 2) *
                (ρ ^ edgeDistance p e g + (p.W : ℝ) ^ (-(1 / 2 : ℝ)))) :=
              mul_le_mul_of_nonneg_left hkey hC
          _ = K1 * (ρ ^ edgeDistance p e g + (p.W : ℝ) ^ (-(1 / 2 : ℝ))) := by rw [hK1]; ring
          _ ≤ (max (2 * C * c1) W₁ + K1 + K2) *
                (ρ ^ edgeDistance p e g + (p.W : ℝ) ^ (-(1 / 2 : ℝ))) := by
              refine mul_le_mul_of_nonneg_right ?_ hden
              have : 0 ≤ max (2 * C * c1) W₁ := le_trans (by linarith) (le_max_right _ _)
              linarith
      · push Not at hWl
        have hWW : (p.W : ℝ) ≤ W₁ := hWl.trans (le_max_left _ _)
        have hb3 := h3 p hpb hnT hWW model e S.X (S.G e) hG E hE
        have hb4 := h4 p hpb hnT hWW model e S.X (S.G e) hG E hE
        have hc3a : C3 ≤ c3 := (le_max_left _ _).trans (le_max_left _ _)
        have hc3b : C4 ≤ c3 := (le_max_right _ _).trans (le_max_left _ _)
        have hcore := sc_deriv_core hFm (hdm e) (hdm (e + 1)) (hεm e) (hεm (e + 1)) hlm hq hC
          hc30 hc30 hc30 (t := 1) one_pos hae
          (((hb3.2 g hge).2 e (Or.inl rfl)).trans (ENNReal.ofReal_le_ofReal hc3a))
          (((hb3.2 g hge).2 (e + 1) (Or.inr rfl)).trans (ENNReal.ofReal_le_ofReal hc3a))
          ((hb4.1 e (Or.inl rfl)).trans (ENNReal.ofReal_le_ofReal hc3b))
          ((hb4.1 (e + 1) (Or.inr rfl)).trans (ENNReal.ofReal_le_ofReal hc3b))
          (((hb4.2 g hge).1).trans (ENNReal.ofReal_le_ofReal hc3b))
        refine hcore.trans (ENNReal.ofReal_le_ofReal ?_)
        have hsq := sc_rpow_half_ge hW1 hWW
        have hrp : 0 ≤ (p.W : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
        have hρd : 0 ≤ ρ ^ edgeDistance p e g := by positivity
        calc C * (2 * c3 + 2 * 1 * c3 ^ 2 + c3 ^ 2 / (2 * 1))
            ≤ C * (2 * c3 + 3 * c3 ^ 2) := by
              refine mul_le_mul_of_nonneg_left ?_ hC; nlinarith [sq_nonneg c3]
          _ ≤ C * (2 * c3 + 3 * c3 ^ 2) * (Real.sqrt W₁ * (p.W : ℝ) ^ (-(1 / 2 : ℝ))) := by
              have h0 : 0 ≤ C * (2 * c3 + 3 * c3 ^ 2) := by positivity
              exact le_mul_of_one_le_right h0 hsq
          _ = K2 * (p.W : ℝ) ^ (-(1 / 2 : ℝ)) := by rw [hK2]; ring
          _ ≤ (max (2 * C * c1) W₁ + K1 + K2) *
                (ρ ^ edgeDistance p e g + (p.W : ℝ) ^ (-(1 / 2 : ℝ))) := by
              have hM0 : 0 ≤ max (2 * C * c1) W₁ := le_trans (by linarith) (le_max_right _ _)
              have k1 : K2 * (p.W : ℝ) ^ (-(1 / 2 : ℝ)) ≤
                  (max (2 * C * c1) W₁ + K1 + K2) * (p.W : ℝ) ^ (-(1 / 2 : ℝ)) :=
                mul_le_mul_of_nonneg_right (by linarith) hrp
              have k2 : (max (2 * C * c1) W₁ + K1 + K2) * (p.W : ℝ) ^ (-(1 / 2 : ℝ)) ≤
                  (max (2 * C * c1) W₁ + K1 + K2) *
                    (ρ ^ edgeDistance p e g + (p.W : ℝ) ^ (-(1 / 2 : ℝ))) :=
                mul_le_mul_of_nonneg_left (by linarith) (by linarith)
              exact k1.trans k2
  · -- replacement: `P♯(j^{sm}_e(λ_α) ≠ j_e(λ_α)) ≤ C_D W^{-D}`
    intro D
    obtain ⟨Cs, Ws, hs⟩ := hdom.small b hb hb' ϑ T hϑ0 hϑ1 (D + 1)
    set W' : ℝ := max Ws 1 with hW'
    have hW'1 : 1 ≤ W' := le_max_right _ _
    refine ⟨max Cs 0 + W' ^ |D|, ?_⟩
    intro p hpb hnT model α hα i X G hG
    have hprob : IsProbabilityMeasure (extendedPairMeasure p α i X.P X.Hm) :=
      extendedPairMeasure_isProbability p model α i X
    have hW1 : (1 : ℝ) ≤ p.W := by exact_mod_cast p.W_pos
    have hW0 : (0 : ℝ) < p.W := by linarith
    set bad := {ω | Φ p α i (X.Hm ω - embedPair p i (G ω)) (physicalOrderedEigenvalue p (X.Hm ω) α) ≠
        dysonCenter p i cst0 α (X.Hm ω - embedPair p i (G ω))
          (physicalOrderedEigenvalue p (X.Hm ω) α)} with hbad
    have hgood : ∀ᵐ ω ∂extendedPairMeasure p α i X.P X.Hm,
        (X.Hm ω - embedPair p i (G ω)).IsHermitian ∧
          IsRingBanded p (X.Hm ω - embedPair p i (G ω)) ∧
          ExteriorBondsInvertible p i (X.Hm ω - embedPair p i (G ω)) := by
      unfold extendedPairMeasure
      exact (withDensity_absolutelyContinuous _ _).ae_le (sc_ae_good X hG)
    have hsub : bad ≤ᵐ[extendedPairMeasure p α i X.P X.Hm]
        {ω | ¬ InCenterDomain p i cst0 α (X.Hm ω - embedPair p i (G ω))
          (physicalOrderedEigenvalue p (X.Hm ω) α)} := by
      filter_upwards [hgood] with ω hω hb
      intro hdomω
      exact hb (hagree p hpb α hα i _ _ hω.1 hω.2.1 hω.2.2 hdomω)
    have hmono := measure_mono_ae hsub
    have hfac : 0 ≤ (max Cs 0 + W' ^ |D|) * (p.W : ℝ) ^ (-D) := by positivity
    by_cases hWl : Ws < (p.W : ℝ)
    · refine hmono.trans ((hs p hpb hnT hWl model α hα i X G hG).trans
        (ENNReal.ofReal_le_ofReal ?_))
      rw [show (1 : ℝ) - (D + 1) = -D by ring]
      have hx : 0 ≤ (p.W : ℝ) ^ (-D) := Real.rpow_nonneg hW0.le _
      have hy : 0 ≤ W' ^ |D| := Real.rpow_nonneg (by linarith) _
      exact mul_le_mul_of_nonneg_right (by linarith [le_max_left Cs 0]) hx
    · push Not at hWl
      refine (prob_le_one).trans ?_
      rw [← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      have hWW : (p.W : ℝ) ≤ W' := hWl.trans (le_max_left _ _)
      have hkey : 1 ≤ W' ^ |D| * (p.W : ℝ) ^ (-D) := by
        rcases le_total 0 D with hD | hD
        · rw [abs_of_nonneg hD, Real.rpow_neg hW0.le, ← div_eq_mul_inv,
            one_le_div (Real.rpow_pos_of_pos hW0 D)]
          exact Real.rpow_le_rpow hW0.le hWW hD
        · have h1 : 1 ≤ W' ^ |D| := Real.one_le_rpow hW'1 (abs_nonneg _)
          have h2 : 1 ≤ (p.W : ℝ) ^ (-D) := Real.one_le_rpow hW1 (by linarith)
          calc (1 : ℝ) = 1 * 1 := by ring
            _ ≤ W' ^ |D| * (p.W : ℝ) ^ (-D) := mul_le_mul h1 h2 zero_le_one (by linarith)
      have : 0 ≤ max Cs 0 * (p.W : ℝ) ^ (-D) :=
        mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hW0.le _)
      calc (1 : ℝ) ≤ W' ^ |D| * (p.W : ℝ) ^ (-D) := hkey
        _ ≤ max Cs 0 * (p.W : ℝ) ^ (-D) + W' ^ |D| * (p.W : ℝ) ^ (-D) := by linarith
        _ = (max Cs 0 + W' ^ |D|) * (p.W : ℝ) ^ (-D) := by ring

end BlockBand.Center
