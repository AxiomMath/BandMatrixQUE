module

public import BlockBand.Transmission.LawDuality.KillIdPath
public import BlockBand.Transmission.LawDuality.KillIBP

/-!
# The killed dual identity, dual stopped at `τ`

`E[Φ_r K_r − Φ_0 K_0] = E ∫_0^r (K_u G_u + Φ_u K'_u) du`,

with `Φ_s = F_{Z_{s∧τ}}(ν)`, `G_u = 𝒟F(Z_u)1{u<τ}`, `K_s = exp(−∫_0^{s} k R 1{·<τ})`,
`K'_u = −k(u)R_u1{u<τ}K_u` (`ratioStop`, `genStop`, `killFac`, `killDer`), i.e.
`E[F(Z_{r∧τ})K_{r∧τ}] − E F(Z₀) = E∫_0^r 1{u<τ}K_u (𝒟F − kRF)(Z_u)(ν) du`.
It is `integral_killed_eq` with the orthogonality of the full-level martingale increments
(`integral_mul_fullMart_sub_eq_zero`; `K_s` is `𝓖_s`-measurable), the FTC
`killFac_sub_eq`, and the bounds `|G| ≤ Σ_q genMass`, `|K'| ≤ C_k p(M+1)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawDuality

open MeasureTheory ProbabilityTheory Filter Topology Set intervalIntegral
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Transmission.Dual
open BlockBand.SourceProcess.Stochastic.SemimartingaleIto
open scoped NNReal ENNReal

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω}
  {𝓖 : Filtration ℝ≥0 m} {D0 : ℝ} {p : ℕ} {x y : Fin p → ℝ}
  {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}

/-- `K_s` is `𝓖_{s⁺}`-measurable. -/
theorem stronglyMeasurable_killFac (h : IsDualDeletionProcess P 𝓖 D0 x y N X Y)
    (hpath : ∀ ω, IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
    {k : ℝ → ℝ} (hk : Continuous k) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ) (s : ℝ) :
    StronglyMeasurable[𝓖 s.toNNReal] (killFac k N X Y τ s) := by
  have e : killFac k N X Y τ s = fun ω => Real.exp (-∫ v in Ioc (0 : ℝ) (s.toNNReal : ℝ),
      (k (v.toNNReal : ℝ) * dualTotal (N v.toNNReal ω) (X v.toNNReal ω) (Y v.toNNReal ω) *
        stopInd τ v.toNNReal ω)) := funext fun ω => killFac_eq_integral s
  rw [e]
  exact Real.continuous_exp.comp_stronglyMeasurable
    (stronglyMeasurable_integral_of_progressive (isStronglyProgressive_rateInd h hpath hk hτ)
      s.toNNReal).neg

/-- **The killed identity for the dual stopped at `τ`.** -/
theorem integral_killed_dual (h : IsDualDeletionProcess P 𝓖 D0 x y N X Y)
    (hpath : ∀ ω, IsDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
    (hstart : ∀ ω, N 0 ω = p) (ν : FiniteMeasure unitInterval) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime 𝓖 τ) {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hU : StaysIn N X Y τ M ε) {k : ℝ → ℝ} (hk : Continuous k) (hk0 : ∀ v, 0 ≤ k v) {Ck : ℝ}
    (hkC : ∀ v, k v ≤ Ck) {r : ℝ} (hr : 0 ≤ r) :
    ∫ ω, (ratioStop ν N X Y τ r ω * killFac k N X Y τ r ω -
        ratioStop ν N X Y τ 0 ω * killFac k N X Y τ 0 ω) ∂P =
      ∫ ω, (∫ u in (0 : ℝ)..r, (killFac k N X Y τ u ω * genStop D0 ν N X Y τ u ω +
        ratioStop ν N X Y τ u ω * killDer k N X Y τ u ω)) ∂P := by
  have := h.prob
  set Cg := ∑ j ∈ Finset.range p, genMass D0 (j + 1) M ε ν with hCg
  have hCg0 : 0 ≤ Cg := Finset.sum_nonneg fun j _ => genMass_nonneg _ _ _ _ _
  have hCk : 0 ≤ Ck := (hk0 0).trans (hkC 0)
  have hpM : 0 ≤ Ck * (p * (M + 1)) := by positivity
  set C := 1 + Cg + Ck * (p * (M + 1)) with hC
  have hprog := isStronglyProgressive_pathGenInd h hpath hstart ν hτ (D0 := D0)
  refine integral_killed_eq (C := C) hr (fun t => ?_) (fun t => ?_) (fun s t => ?_)
    (ae_of_all _ fun ω => ⟨(continuous_ratioStop (hpath ω) ν).continuousOn,
      (continuous_killFac (hpath ω) hk).continuousOn,
      intervalIntegrable_genStop hpath hstart hM hε hε1 hU D0 ν ω 0 r, ?_,
      fun a b ha hab _ => killFac_sub_eq (hpath ω) hk ha hab, fun u => ⟨?_, ?_, ?_, ?_⟩⟩)
    (fun s t hs hst _ => ?_)
  · exact ((stronglyMeasurable_ratioStop h hpath ν hτ t.toNNReal).mono
      (𝓖.le _)).aestronglyMeasurable
  · exact ((stronglyMeasurable_killFac h hpath hk hτ t).mono (𝓖.le _)).aestronglyMeasurable
  · have e : (fun ω => ∫ u in s..t, genStop D0 ν N X Y τ u ω) = fun ω =>
        (∫ u in Ioc (0 : ℝ) (t.toNNReal : ℝ), pathGen D0 ν N X Y u.toNNReal ω *
          stopInd τ u.toNNReal ω) -
        ∫ u in Ioc (0 : ℝ) (s.toNNReal : ℝ), pathGen D0 ν N X Y u.toNNReal ω *
          stopInd τ u.toNNReal ω := funext fun ω => by
      rw [← integral_interval_sub_left
        (intervalIntegrable_genStop hpath hstart hM hε hε1 hU D0 ν ω 0 t)
        (intervalIntegrable_genStop hpath hstart hM hε hε1 hU D0 ν ω 0 s),
        integral_genStop_eq, integral_genStop_eq]
    rw [e]
    exact (((stronglyMeasurable_integral_of_progressive hprog _).mono (𝓖.le _)).sub
      ((stronglyMeasurable_integral_of_progressive hprog _).mono (𝓖.le _))).aestronglyMeasurable
  · have := (intervalIntegrable_killRate (continuous_killRate (hpath ω) hk) (τ ω) 0 r).neg.mul_continuousOn
      (continuous_killFac (τ := τ) (hpath ω) hk).continuousOn
    exact this
  · have := (pathRatio_mem (hpath ω) ν (stopAt τ u.toNNReal ω))
    rw [ratioStop, abs_of_pos this.1]; linarith [this.2]
  · have := abs_genStop_le hpath hstart hM hε hε1 hU D0 ν ω u
    linarith
  · have := killFac_mem (τ := τ) (hpath ω) hk0 u
    rw [abs_of_pos this.1]; linarith [this.2]
  · have := abs_killDer_le hpath hstart hM hε hU hk0 hkC ω u
    linarith
  · have e : ∀ ω, killFac k N X Y τ s ω * (ratioStop ν N X Y τ t ω - ratioStop ν N X Y τ s ω -
        ∫ u in s..t, genStop D0 ν N X Y τ u ω) = killFac k N X Y τ s ω *
        (fullMart D0 ν N X Y τ t.toNNReal ω - fullMart D0 ν N X Y τ s.toNNReal ω) := fun ω => by
      rw [ratioStop_sub_eq_fullMart hpath hstart hM hε hε1 hU]
    simp_rw [e]
    refine integral_mul_fullMart_sub_eq_zero h hpath hstart ν hτ hM hε hε1 hU
      (Real.toNNReal_le_toNNReal hst) (stronglyMeasurable_killFac h hpath hk hτ s) (CA := 1)
      fun ω => ?_
    have := killFac_mem (τ := τ) (hpath ω) hk0 s
    rw [abs_of_pos this.1]; exact this.2

end BlockBand.Transmission.LawDuality
