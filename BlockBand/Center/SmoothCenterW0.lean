module

public import BlockBand.Center.SmoothConstructionAssembly

/-!
# The smooth center with a width threshold

Main theorem `smoothCenterW0_holds_of`: `SmoothCenterW0 cst0` from `TaggedTraceStatement`
and `CenterDomainContract cst0` only. The deterministic construction is
`scSmoothConstructionOffPole_holds`; no fixed-width moment hypothesis is used: for `W` above the
threshold of `TaggedTraceStatement` the bounds come from the tagged trace lemma, and below it
nothing is claimed.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Center

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.QUE BlockBand.QUE.Fourier BlockBand.Model.Construction
open BlockBand.Layers BlockBand.QUE.PairResidual
open scoped ENNReal NNReal

/-!
## 1. The statement with a width threshold
-/

/-- `Layers.SmoothCenterContract cst` with one change: in the
`moment`/`derivative` clause the constant is `∃ Cq W₀ : ℝ` and the bounds are claimed only for
`W₀ < p.W`. All other fields (`bounded`, `measurable`, `smooth`, `support`, `agree`,
`replacement`) are the same, `replacement` keeping its validity for all `W ≥ 1`.

*Law.* `S.X.P` of an exact simultaneous splitting `S` (`S.IsExact`) for `moment`/`derivative`;
the pair law `extendedPairMeasure p α i X.P X.Hm` of any extension with the edge splitting
(`IsCenterSplitting X G`) for `replacement`.
*Domain.* `0 < b < 1/2`, `0 < ϑ < 1/2`, `T` arbitrary; `p.b = b`, `n ≤ TW`; `ϑ`-bulk ranks;
deterministic `E ∈ ℝ`; `g ≠ e` for the derivative.
*Norms.* `eLpNorm` (`L^q`, `q ≥ 1`) of real scalars; `∂_{ξ_g}` is the derivative of `Φ` along
`t ↦ H^{(e)} + t P_{S_g}` at `t = 0`.
*Quantifier order.* `b, ϑ, T`; then `ρ, κ', Φ`; then `q`; then `Cq, W₀`; then `p` (with
`W₀ < W`), the model, `S`, `α`, `e, g, E`. For `replacement`: `D`, then `CD`, then the data.
*Uniformity.* `Cq, W₀` depend on `(b, ϑ, T, q)` only; `CD` on `(b, ϑ, T, D)` only.
*Order of limits.* None (fixed-`p` inequalities with uniform constants). -/
def SmoothCenterW0 (cst : CenterDomainConstants) : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ ϑ T : ℝ, 0 < ϑ → ϑ < 1 / 2 →
    ∃ (ρ κ' : ℝ), 0 ≤ ρ ∧ ρ < 1 ∧ 0 < κ' ∧
    ∃ Φ : ∀ (p : Parameters), Fin p.N → ZMod p.n → p.SiteMatrix → ℝ → ℝ,
      (∀ (p : Parameters) α e (H : p.SiteMatrix) (E : ℝ), |Φ p α e H E| ≤ 1) ∧
      (∀ (p : Parameters) α e, Measurable (fun x : p.SiteMatrix × ℝ => Φ p α e x.1 x.2)) ∧
      (∀ (p : Parameters) α e (H₀ : p.SiteMatrix), H₀.IsHermitian →
        IsRingBanded p H₀ → ExteriorBondsInvertible p e H₀ →
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x : (ZMod p.n → ℝ) × ℝ =>
            Φ p α e (H₀ + ∑ g, (x.1 g : ℂ) • pairProjector p g) x.2)) ∧
      (∀ (p : Parameters) α e (H₀ : p.SiteMatrix) (E : ℝ), E ∉ bulkInterval κ' → Φ p α e H₀ E = 0) ∧
      (∀ (p : Parameters), p.b = b → ∀ α, IsBulkRank p ϑ α → ∀ e (H₀ : p.SiteMatrix) (E : ℝ),
        H₀.IsHermitian → IsRingBanded p H₀ → ExteriorBondsInvertible p e H₀ →
        InCenterDomain p e cst α H₀ E → Φ p α e H₀ E = dysonCenter p e cst α H₀ E) ∧
      (∀ q : ℝ, 1 ≤ q → ∃ Cq W₀ : ℝ, ∀ (p : Parameters), p.b = b → (p.n : ℝ) ≤ T * p.W →
        W₀ < (p.W : ℝ) →
        ∀ (model : p.GaussianRingModel) (S : SimultaneousSplitting p model), S.IsExact →
        ∀ α, IsBulkRank p ϑ α → ∀ (e g : ZMod p.n) (E : ℝ),
          eLpNorm (fun ω => Φ p α e (S.X.Hm ω - embedPair p e (S.G e ω)) E) (ENNReal.ofReal q)
              S.X.P ≤ ENNReal.ofReal (Cq / p.W) ∧
          (g ≠ e → eLpNorm (fun ω => deriv (fun t : ℝ =>
                Φ p α e (S.X.Hm ω - embedPair p e (S.G e ω) + (t : ℂ) • pairProjector p g) E) 0)
              (ENNReal.ofReal q) S.X.P ≤
            ENNReal.ofReal (Cq * (ρ ^ edgeDistance p e g + (p.W : ℝ) ^ (-(1 / 2 : ℝ)))))) ∧
      (∀ D : ℝ, ∃ CD : ℝ, ∀ (p : Parameters), p.b = b → (p.n : ℝ) ≤ T * p.W →
        ∀ (model : p.GaussianRingModel) (α : Fin p.N), IsBulkRank p ϑ α → ∀ (i : ZMod p.n)
          (X : PairExtension p model) (G : X.Ω → PairMatrix p i), IsCenterSplitting X G →
          extendedPairMeasure p α i X.P X.Hm
              {ω | Φ p α i (X.Hm ω - embedPair p i (G ω)) (physicalOrderedEigenvalue p (X.Hm ω) α) ≠
                dysonCenter p i cst α (X.Hm ω - embedPair p i (G ω))
                  (physicalOrderedEigenvalue p (X.Hm ω) α)} ≤
            ENNReal.ofReal (CD * (p.W : ℝ) ^ (-D)))

/-- **The unthresholded smooth center implies the thresholded one** (`SmoothCenterContract cst →
SmoothCenterW0 cst`, any constants `cst`): take `W₀ = 0` (every width satisfies `0 < W`); all
other fields are passed through unchanged. Law, domain, norms, quantifier order and uniformity
as in `SmoothCenterW0`; order of limits: none. Hypothesis: `Layers.SmoothCenterContract cst`.
So `SmoothCenterW0` is weaker. -/
theorem smoothCenterContract_imp_W0 {cst : CenterDomainConstants}
    (h : SmoothCenterContract cst) : SmoothCenterW0 cst := by
  intro b hb hb' ϑ T hϑ0 hϑ1
  obtain ⟨ρ, κ', hρ0, hρ1, hκ', Φ, hbdd, hmeas, hsm, hsupp, hagree, hmom, hrepl⟩ :=
    h b hb hb' ϑ T hϑ0 hϑ1
  refine ⟨ρ, κ', hρ0, hρ1, hκ', Φ, hbdd, hmeas, hsm, hsupp, hagree, ?_, hrepl⟩
  intro q hq
  obtain ⟨Cq, hCq⟩ := hmom q hq
  exact ⟨Cq, 0, fun p hpb hnT _ => hCq p hpb hnT⟩

/-!
## 2. The smooth center above the width threshold
-/

/-- *Statement.* `b ∈ (0,1/2)`, `ϑ ∈ (0,1/2)`, `T` first; then `ρ < 1` (the `ρ` of
`TaggedTraceStatement` at `(b, κ', T)`), `κ' = ϑ/4` and `Φ = scnPhi b ϑ`
(`j^{sm}_e = χ_E(E) χ(ε_e²) j_e`) with the deterministic fields (`bounded`, `measurable`,
`smooth`, `support`, `agree`) of `scSmoothConstructionOffPole_holds`; for each `q ≥ 1` constants
`Cq` and `W₀ = max(W₀^{tt}(q), W₀^{tt}(2q))` (thresholds of `TaggedTraceStatement` at orders
`q, 2q`) with `‖j^{sm}_e(E)‖_q ≤ Cq/W` and, for `g ≠ e`,
`‖∂_{ξ_g} j^{sm}_e(E)‖_q ≤ Cq(ρ^{d(e,g)} + W^{-1/2})` for `W > W₀`; and the replacement bound
`P♯(j^{sm}_e(λ_α) ≠ j_e(λ_α)) ≤ C_D W^{-D}` for all `W ≥ 1`.
*Law.* `S.X.P` of an exact simultaneous splitting (the edge-`e` splitting through
`pc_isCenterSplitting_of_exact`) for the moments; the pair law `extendedPairMeasure` of any
extension with the edge splitting for replacement.
*Domain.* `p.b = b`, `n ≤ TW`, `ϑ`-bulk ranks, deterministic `E` (`E ∉ bulkInterval κ'` is
trivial by `support`), `g ≠ e`.
*Norms.* `eLpNorm` of real scalars; Hölder/AM–GM through `sc_moment_core`, `sc_deriv_core`
(orders `q` and `2q` of the tagged trace lemma).
*Quantifier order / uniformity.* As in `SmoothCenterW0`: `Cq, W₀` after `q`, uniform in `p`
(`p.b = b`, `n ≤ TW`, `W > W₀`), the model, `S`, `α`, `e`, `g`, `E`; `C_D` after `D`, uniform in
the same data and all `W ≥ 1`. *Order of limits.* None.
*Hypotheses.* `TaggedTraceStatement` (at `(b, κ', T)`, orders `q, 2q`, its `W₀`),
`CenterDomainContract cst0` (`small` at order `D + 1`), and the deterministic construction
`scSmoothConstructionOffPole_holds` (derivative clause used on the a.s. event
`det(H^{(e)}_R - E) ≠ 0`, `tgt_ae_residual_exterior_det`). -/
theorem smoothCenterW0_holds_of (htt : TaggedTraceStatement) (hdom : CenterDomainContract cst0) :
    SmoothCenterW0 cst0 := by
  intro b hb hb' ϑ T hϑ0 hϑ1
  obtain ⟨κ', C, hκ', hC, Φ, hbdd, hmeas, hsm, hsupp, hagree, hpt⟩ :=
    scSmoothConstructionOffPole_holds b hb hb' ϑ hϑ0 hϑ1
  obtain ⟨ρ, hρ0, hρ1, htq⟩ := htt.1 b hb hb' κ' T hκ'
  refine ⟨ρ, κ', hρ0, hρ1, hκ', Φ, hbdd, hmeas, hsm, hsupp, hagree, ?_, ?_⟩
  · -- the moment and derivative bounds of the smooth center, for `W > W₀`
    intro q hq
    have hq2 : 1 ≤ 2 * q := by linarith
    obtain ⟨C1, W1, h1⟩ := htq q hq
    obtain ⟨C2, W2, h2⟩ := htq (2 * q) hq2
    set c1 : ℝ := max C1 0 with hc1
    set c2 : ℝ := max C2 0 with hc2
    have hc10 : 0 ≤ c1 := le_max_right _ _
    have hc20 : 0 ≤ c2 := le_max_right _ _
    set K1 : ℝ := C * (2 * c1 + 3 * c2 ^ 2) with hK1
    have hK10 : 0 ≤ K1 := by positivity
    have hC10 : 0 ≤ 2 * C * c1 := by positivity
    refine ⟨2 * C * c1 + K1, max W1 W2, ?_⟩
    intro p hpb hnT hWl model S hS α hα e g E
    have hP : IsProbabilityMeasure S.X.P := csm_isProb_ext S.X
    have hG := pc_isCenterSplitting_of_exact S hS e
    have hW1 : (1 : ℝ) ≤ p.W := by exact_mod_cast p.W_pos
    have hW0 : (0 : ℝ) < p.W := by linarith
    have hden : 0 ≤ ρ ^ edgeDistance p e g + (p.W : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
    have hWa : W1 < (p.W : ℝ) := lt_of_le_of_lt (le_max_left _ _) hWl
    have hWb : W2 < (p.W : ℝ) := lt_of_le_of_lt (le_max_right _ _) hWl
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
    have hb1 := h1 p hpb hnT hWa model e S.X (S.G e) hG E hE
    refine ⟨?_, fun hge => ?_⟩
    · -- `‖j^{sm}_e(E)‖_q ≤ Cq/W`
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
      linarith
    · -- `‖∂_{ξ_g} j^{sm}_e(E)‖_q ≤ Cq(ρ^{d(e,g)} + W^{-1/2})`
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
        _ ≤ (2 * C * c1 + K1) * (ρ ^ edgeDistance p e g + (p.W : ℝ) ^ (-(1 / 2 : ℝ))) := by
            refine mul_le_mul_of_nonneg_right ?_ hden
            linarith
  · -- replacement: `P♯(j^{sm}_e(λ_α) ≠ j_e(λ_α)) ≤ C_D W^{-D}` (all `W ≥ 1`)
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
