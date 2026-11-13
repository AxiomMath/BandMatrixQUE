module

public import BlockBand.Palm.RelativeLocalizationGeneric
public import BlockBand.Palm.RelativeLocalizationStop

/-!
# Relative localization: the per-start bound for every start `s ≥ 0` (hitting-time form)

Clause (b2) of `DysonBrownianMotion` gives the eigenvalue semimartingale only from start times
`s > 0`. This file removes that restriction by restarting at `s + η` with the (adapted) data `v(η)`
and letting `η ↓ 0` (dominated convergence). With a closed set `K̂ ⊆ ℝ × ℝ^N` of
`(centre, eigenvalues)` outside which the domination / short-pair / long-gap conditions hold,
`gen_expectation_avoid` states, for every `s, T ≥ 0`:

`∫ 1{(c₀, λ(s+u)) ∉ K̂ ∀ u ≤ T} e^{-KT} Σ_k φ(λ_k(s+T) - c₀) v_k(T) ≤ ∫ Σ_k φ(λ_k(s) - c₀) v₀_k`,

where `v = genMass Gen F s v₀`. Supporting lemmas: `forwardMass_shift` (time shift),
`forwardMass_congr` (coefficients only matter on the open interval), `genMass_restart`
(the mass restarted at `s + η` from `v(η)` is `v(η + ·)`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.RelativeLocalization

open MeasureTheory ProbabilityTheory Set Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open scoped NNReal

variable {N : ℕ}

theorem forwardMass_congr {L L' : ℝ → Fin N → Fin N → ℝ} {s u : ℝ} {v₀ : Fin N → ℝ}
    {v : ℝ → Fin N → ℝ} (hv : ForwardMassSolution L s u v₀ v)
    (h : ∀ x ∈ Ioo s u, L x = L' x) : ForwardMassSolution L' s u v₀ v :=
  ⟨hv.1, hv.2.1, fun x hx => by rw [← h x hx]; exact hv.2.2 x hx⟩

theorem forwardMass_shift {L : ℝ → Fin N → Fin N → ℝ} {T τ : ℝ} {v₀ : Fin N → ℝ}
    {v : ℝ → Fin N → ℝ} (hv : ForwardMassSolution L 0 T v₀ v) (hτ0 : 0 ≤ τ) :
    ForwardMassSolution (fun x => L (x + τ)) 0 (T - τ) (v τ) (fun x => v (x + τ)) := by
  obtain ⟨h0, hc, hd⟩ := hv
  refine ⟨by simp, ?_, fun x hx => ?_⟩
  · refine hc.comp (continuous_id.add continuous_const).continuousOn fun x hx => ⟨?_, ?_⟩
    · linarith [hx.1]
    · linarith [hx.2]
  · have := hd (x + τ) ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact HasDerivAt.comp_add_const x τ this

/-- The mass restarted at `s + η` with data `v(η)` is `v(η + ·)`. -/
theorem genMass_restart {Gen : (Fin N → ℝ) → Fin N → Fin N → ℝ} (hG : Continuous Gen)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (s η : ℝ≥0)
    (v₀ : FlowSample N → Fin N → ℝ) (ω : FlowSample N) (u : ℝ≥0) :
    genMass Gen F (s + η) (fun ω => genMass Gen F s v₀ η ω) u ω =
      genMass Gen F s v₀ (η + u) ω := by
  have hc := genCoeff_continuous hG hF s
  have hsol := adaptedMass_solution hc v₀ ω (T := ((η + u : ℝ≥0) : ℝ)) (NNReal.coe_nonneg _)
  have hsh := forwardMass_shift hsol (NNReal.coe_nonneg η)
  have hT : ((η + u : ℝ≥0) : ℝ) - η = u := by push_cast; ring
  rw [hT] at hsh
  have hsh' := forwardMass_congr hsh (L' := realCoeff (genCoeff Gen F (s + η)) ω) (fun x hx => by
    simp only [realCoeff, genCoeff]
    congr 2
    rw [Real.toNNReal_add hx.1.le (NNReal.coe_nonneg η), Real.toNNReal_coe, add_assoc,
      add_comm x.toNNReal η])
  have := adaptedMass_eq (genCoeff_continuous hG hF (s + η)) (fun ω => genMass Gen F s v₀ η ω)
    ω hsh' (r := u) ⟨NNReal.coe_nonneg u, le_rfl⟩
  simp only [genMass] at this ⊢
  rw [this]
  congr 1
  push_cast; ring

/-- Process `(centre, λ(s+u))`. -/
def cenLam (F : Matrix (Fin N) (Fin N) ℂ) (s : ℝ≥0) (c₀ : FlowSample N → ℝ) (u : ℝ≥0)
    (ω : FlowSample N) : ℝ × (Fin N → ℝ) :=
  (c₀ ω, flowLam F (s + u) ω)

theorem cenLam_continuous {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (s : ℝ≥0)
    (c₀ : FlowSample N → ℝ) (ω : FlowSample N) : Continuous fun u => cenLam F s c₀ u ω :=
  continuous_const.prodMk ((flowLam_continuous hF ω).comp (continuous_const.add continuous_id))

theorem cenLam_adapted (F : Matrix (Fin N) (Fin N) ℂ) (s : ℝ≥0) {c₀ : FlowSample N → ℝ}
    (hc₀ : Measurable[flowFiltration N s] c₀) (u : ℝ≥0) :
    Measurable[shiftFiltration (flowFiltration N) s u] (cenLam F s c₀ u) :=
  (hc₀.mono ((flowFiltration N).mono (le_add_of_nonneg_right (zero_le (a := u)))) le_rfl).prodMk
    (flowLam_adapted F (s + u))

theorem shift0_eq (s : ℝ≥0) :
    (shiftFiltration (flowFiltration N) s) 0 = flowFiltration N s := by
  show (flowFiltration N) (s + 0) = _
  rw [add_zero]

/-- The pathwise good weighted mass. -/
def goodMass (Gen : (Fin N → ℝ) → Fin N → Fin N → ℝ) (F : Matrix (Fin N) (Fin N) ℂ) (s : ℝ≥0)
    (v₀ : FlowSample N → Fin N → ℝ) (c₀ : FlowSample N → ℝ) (φ : ℝ → ℝ) (u : ℝ≥0)
    (ω : FlowSample N) : ℝ :=
  ∑ k, φ (flowLam F (s + u) ω k - c₀ ω) * genMass Gen F s v₀ u ω k

theorem goodMass_continuous {Gen : (Fin N → ℝ) → Fin N → Fin N → ℝ} (hG : Continuous Gen)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (s : ℝ≥0)
    (v₀ : FlowSample N → Fin N → ℝ) (c₀ : FlowSample N → ℝ) {φ : ℝ → ℝ} (hφ : Continuous φ)
    (ω : FlowSample N) : Continuous fun u => goodMass Gen F s v₀ c₀ φ u ω := by
  refine continuous_finsetSum _ fun k _ => ?_
  exact (hφ.comp (((continuous_apply k).comp ((flowLam_continuous hF ω).comp
    (continuous_const.add continuous_id))).sub continuous_const)).mul
    ((continuous_apply k).comp (adaptedMass_continuous (genCoeff_continuous hG hF s) v₀ ω))

theorem goodMass_measurable {Gen : (Fin N → ℝ) → Fin N → Fin N → ℝ} (hG : Continuous Gen)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (s : ℝ≥0)
    {v₀ : FlowSample N → Fin N → ℝ} (hv₀ : Measurable[flowFiltration N s] v₀)
    {c₀ : FlowSample N → ℝ} (hc₀ : Measurable[flowFiltration N s] c₀) {φ : ℝ → ℝ}
    (hφ : Continuous φ) (u : ℝ≥0) : Measurable (goodMass Gen F s v₀ c₀ φ u) := by
  have hv : Measurable (fun ω => genMass Gen F s v₀ u ω) :=
    (adaptedMass_measurable (shiftFiltration (flowFiltration N) s) (genCoeff_adapted hG F s)
      (genCoeff_continuous hG hF s) (by rw [shift0_eq]; exact hv₀) u).mono
      ((flowFiltration N).le _) le_rfl
  have hl : Measurable (flowLam F (s + u)) :=
    (flowLam_adapted F (s + u)).mono ((flowFiltration N).le _) le_rfl
  have hc : Measurable c₀ := hc₀.mono ((flowFiltration N).le _) le_rfl
  refine Finset.measurable_sum _ fun k _ => ?_
  exact (hφ.measurable.comp (((measurable_pi_apply k).comp hl).sub hc)).mul
    ((measurable_pi_apply k).comp hv)

theorem goodMass_le {Gen : (Fin N → ℝ) → Fin N → Fin N → ℝ} (hG : Continuous Gen)
    (hGs : IsSubGenField Gen) {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (s : ℝ≥0)
    {v₀ : FlowSample N → Fin N → ℝ} (hv₀ : ∀ ω k, 0 ≤ v₀ ω k ∧ v₀ ω k ≤ 1)
    (c₀ : FlowSample N → ℝ) {φ : ℝ → ℝ} {M : ℝ} (hφ0 : ∀ z, 0 ≤ φ z) (hφM : ∀ z, φ z ≤ M)
    (u : ℝ≥0) (ω : FlowSample N) :
    0 ≤ goodMass Gen F s v₀ c₀ φ u ω ∧ goodMass Gen F s v₀ c₀ φ u ω ≤ M * N := by
  have hM0 : 0 ≤ M := (hφ0 0).trans (hφM 0)
  have hv := genMass_mem_unit hG hGs hF s hv₀ u ω
  refine ⟨Finset.sum_nonneg fun k _ => mul_nonneg (hφ0 _) (hv k).1, ?_⟩
  calc _ ≤ ∑ _k : Fin N, M := Finset.sum_le_sum fun k _ => by
        calc _ ≤ M * 1 := mul_le_mul (hφM _) (hv k).2 (hv k).1 hM0
          _ = M := mul_one M
    _ = M * N := by simp [mul_comm]

/-- Avoidance event `{(c₀, λ(s+u)) ∉ K̂ for all u ≤ T}`. -/
def avoidSet (F : Matrix (Fin N) (Fin N) ℂ) (s : ℝ≥0) (c₀ : FlowSample N → ℝ)
    (Kh : Set (ℝ × (Fin N → ℝ))) (T : ℝ≥0) : Set (FlowSample N) :=
  {ω | ∀ u : ℝ≥0, u ≤ T → cenLam F s c₀ u ω ∉ Kh}

theorem measurableSet_avoidSet {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (s : ℝ≥0)
    {c₀ : FlowSample N → ℝ} (hc₀ : Measurable[flowFiltration N s] c₀)
    {Kh : Set (ℝ × (Fin N → ℝ))} (hKh : IsClosed Kh) (T : ℝ≥0) :
    MeasurableSet (avoidSet F s c₀ Kh T) := by
  have hAv_eq : avoidSet F s c₀ Kh T = {ω | hitTime (cenLam F s c₀) Kh ω ≤ T}ᶜ := by
    ext ω
    simp only [avoidSet, Set.mem_ofPred_eq, Set.mem_compl_iff,
      hitTime_le_iff (cenLam_continuous hF s c₀ ω) hKh, not_exists, not_and]
  have hst : IsStoppingTime (shiftFiltration (flowFiltration N) s) (hitTime (cenLam F s c₀) Kh) :=
    isStoppingTime_hitTime _ _ (cenLam_adapted F s hc₀) (cenLam_continuous hF s c₀) hKh
  rw [hAv_eq]; exact ((shiftFiltration (flowFiltration N) s).le T _ (hst T)).compl

/-- The tilted state process is progressive, so its stopped values are measurable. -/
theorem stopped_tilted_integrable {Gen : (Fin N → ℝ) → Fin N → Fin N → ℝ} (hG : Continuous Gen)
    (hGs : IsSubGenField Gen) {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (a : ℝ)
    (s : ℝ≥0) {v₀ : FlowSample N → Fin N → ℝ}
    (hv₀m : Measurable[shiftFiltration (flowFiltration N) s 0] v₀)
    (hv₀ : ∀ ω k, 0 ≤ v₀ ω k ∧ v₀ ω k ≤ 1)
    {c₀ : FlowSample N → ℝ} (hc₀ : Measurable[shiftFiltration (flowFiltration N) s 0] c₀)
    {φ : ℝ → ℝ} (hφc : Continuous φ) {M K : ℝ} (hφ0 : ∀ z, 0 ≤ φ z) (hφM : ∀ z, φ z ≤ M)
    (hK0 : 0 ≤ K) (ρ : FlowSample N → WithTop ℝ≥0)
    (hρ : IsStoppingTime (shiftFiltration (flowFiltration N) s) ρ) (T : ℝ≥0) :
    Integrable (stoppedProcess (fun (u : ℝ≥0) ω => tiltedMass K φ
        ((u : ℝ), sumVec (lamShift F s c₀ u ω) (genMass Gen F s v₀ u ω))) ρ T) (flowLaw N a) := by
  set X : ℝ≥0 → FlowSample N → ℝ := fun u ω => tiltedMass K φ
      ((u : ℝ), sumVec (lamShift F s c₀ u ω) (genMass Gen F s v₀ u ω)) with hX
  have hcomp : Continuous (tiltedMass (N := N) K φ) := by
    unfold tiltedMass
    exact ((continuous_fst.const_smul K).neg.rexp).mul (continuous_finsetSum _ fun k _ =>
      (hφc.comp ((continuous_apply (lamIdx k)).comp continuous_snd)).mul
        ((continuous_apply (massIdx k)).comp continuous_snd))
  have hYc : ∀ ω, Continuous fun u : ℝ≥0 =>
      sumVec (lamShift F s c₀ u ω) (genMass Gen F s v₀ u ω) := fun ω =>
    continuous_sumVec.comp ((continuous_pi fun k => ((continuous_apply k).comp
      ((flowLam_continuous hF ω).comp (continuous_const.add continuous_id))).sub
      continuous_const).prodMk (adaptedMass_continuous (genCoeff_continuous hG hF s) v₀ ω))
  have hYa : ∀ u, Measurable[shiftFiltration (flowFiltration N) s u]
      (fun ω => sumVec (lamShift F s c₀ u ω) (genMass Gen F s v₀ u ω)) := by
    intro u
    have h1 : Measurable[shiftFiltration (flowFiltration N) s u] (lamShift F s c₀ u) := by
      refine @measurable_pi_iff (FlowSample N) (Fin N) (fun _ => ℝ)
        (shiftFiltration (flowFiltration N) s u) _ _ |>.mpr fun k => ?_
      exact ((measurable_pi_apply k).comp (flowLam_adapted F (s + u))).sub
        (hc₀.mono ((shiftFiltration (flowFiltration N) s).mono (zero_le (a := u))) le_rfl)
    have h2 := adaptedMass_measurable (shiftFiltration (flowFiltration N) s)
      (genCoeff_adapted hG F s) (genCoeff_continuous hG hF s) hv₀m u
    exact continuous_sumVec.measurable.comp (h1.prodMk h2)
  have hXa : ∀ u, StronglyMeasurable[shiftFiltration (flowFiltration N) s u] (X u) := fun u =>
    (hcomp.measurable.comp (measurable_const.prodMk (hYa u))).stronglyMeasurable
  have hXc : ∀ ω, Continuous fun u => X u ω := fun ω =>
    hcomp.comp (NNReal.continuous_coe.prodMk (hYc ω))
  have hprog := StronglyAdapted.isStronglyProgressive_of_continuous hXa hXc
  have hm := hprog.stronglyMeasurable_stoppedProcess hρ T
  have hbd : ∀ u ω, ‖X u ω‖ ≤ M * N := by
    intro u ω
    have hv := genMass_mem_unit hG hGs hF s hv₀ u ω
    have hM0 : 0 ≤ M := (hφ0 0).trans (hφM 0)
    have hexp : Real.exp (-(K * u)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by have := NNReal.coe_nonneg u; nlinarith)
    have hsum0 : 0 ≤ ∑ k, φ (lamShift F s c₀ u ω k) * genMass Gen F s v₀ u ω k :=
      Finset.sum_nonneg fun k _ => mul_nonneg (hφ0 _) (hv k).1
    have hsum1 : ∑ k, φ (lamShift F s c₀ u ω k) * genMass Gen F s v₀ u ω k ≤ M * N := by
      calc _ ≤ ∑ _k : Fin N, M := Finset.sum_le_sum fun k _ => by
            calc _ ≤ M * 1 := mul_le_mul (hφM _) (hv k).2 (hv k).1 hM0
              _ = M := mul_one M
        _ = M * N := by simp [mul_comm]
    simp only [hX, tiltedMass, sumVec_lamIdx, sumVec_massIdx]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hsum0)]
    calc _ ≤ 1 * (M * N) := mul_le_mul hexp hsum1 hsum0 zero_le_one
      _ = M * N := one_mul _
  exact Integrable.of_bound hm.aestronglyMeasurable (M * N)
    (Eventually.of_forall fun ω => hbd _ ω)

theorem tendsto_eta (T : ℝ≥0) :
    Tendsto (fun n : ℕ => T / ((n : ℝ≥0) + 2)) atTop (𝓝 0) := by
  rw [← NNReal.tendsto_coe]
  simp only [NNReal.coe_div, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_ofNat,
    NNReal.coe_zero]
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (T : ℝ)
  rw [mul_zero] at h
  refine squeeze_zero (fun n => by positivity) (fun n => ?_) h
  rw [mul_one_div]
  exact div_le_div_of_nonneg_left (NNReal.coe_nonneg T) (by positivity) (by linarith)

/-- **Per-start bound, every `s ≥ 0`, hitting-time form.** -/
theorem gen_expectation_avoid (hIto : SemimartingaleItoFormula (N + N))
    (hStop : StoppedSemimartingale 1) (hDBM : DysonBrownianMotion N)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (a : ℝ) (s : ℝ≥0)
    {Gen : (Fin N → ℝ) → Fin N → Fin N → ℝ} (hG : Continuous Gen) (hGs : IsSubGenField Gen)
    {v₀ : FlowSample N → Fin N → ℝ} (hv₀m : Measurable[flowFiltration N s] v₀)
    (hv₀ : ∀ ω k, 0 ≤ v₀ ω k ∧ v₀ ω k ≤ 1)
    {c₀ : FlowSample N → ℝ} (hc₀ : Measurable[flowFiltration N s] c₀)
    {φ φ1 φ2 : ℝ → ℝ} (hφ : ∀ z, HasDerivAt φ (φ1 z) z) (hφ1 : ∀ z, HasDerivAt φ1 (φ2 z) z)
    (hφc : ContDiff ℝ 2 φ) {A B Kc G c₁ M K : ℝ} (hφ0 : ∀ z, 0 ≤ φ z) (hφM : ∀ z, φ z ≤ M)
    (hA : ∀ z, |φ1 z| ≤ A * φ z) (hA0 : 0 ≤ A) (hB : ∀ z, |φ2 z| ≤ B * φ z) (hB0 : 0 ≤ B)
    (hKc0 : 0 ≤ Kc) (hcomp : ∀ x z, |z - x| ≤ G → φ z ≤ Kc * φ x) (hc₁ : 0 < c₁)
    (hK0 : 0 ≤ K) {ℓ : ℕ}
    (hK : 2 * ℓ * B * Kc / N + 2 * A * (1 + Real.log N) / c₁ + B / (2 * N) ≤ K)
    {Kh : Set (ℝ × (Fin N → ℝ))} (hKh : IsClosed Kh)
    (hcond : ∀ (c : ℝ) (lam : Fin N → ℝ), (c, lam) ∉ Kh →
      (∀ v : Fin N → ℝ, (∀ k, 0 ≤ v k) → ∀ k,
        ∑ l, Gen lam k l * v l ≤ ∑ l, shortGen N lam ℓ k l * v l) ∧
      (∀ k l : Fin N, l ≠ k → labelDist k l < ℓ →
        |(lam l - c) - (lam k - c)| ≤ G ∨ (φ1 (lam k - c) = 0 ∧ φ (lam l - c) = φ (lam k - c))) ∧
      (∀ k l : Fin N, l ≠ k → ℓ ≤ labelDist k l → c₁ * labelDist k l / N ≤ |lam k - lam l|))
    (T : ℝ≥0) :
    Real.exp (-(K * T)) *
        ∫ ω, (avoidSet F s c₀ Kh T).indicator (goodMass Gen F s v₀ c₀ φ T) ω ∂flowLaw N a ≤
      ∫ ω, goodMass Gen F s v₀ c₀ φ 0 ω ∂flowLaw N a := by
  set μ := flowLaw N a
  have hφcont : Continuous φ := hφc.continuous
  have hbd := goodMass_le hG hGs hF s hv₀ c₀ hφ0 hφM
  have hAvm := measurableSet_avoidSet hF s hc₀ hKh T
  have hint : ∀ u, Integrable (goodMass Gen F s v₀ c₀ φ u) μ := fun u =>
    Integrable.of_bound (goodMass_measurable hG hF s hv₀m hc₀ hφcont u).aestronglyMeasurable
      (M * N) (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hbd u ω).1]; exact (hbd u ω).2)
  set I := ∫ ω, (avoidSet F s c₀ Kh T).indicator (goodMass Gen F s v₀ c₀ φ T) ω ∂μ with hI
  have hI0 : 0 ≤ I := integral_nonneg fun ω => by
    simp only [Set.indicator]; split_ifs
    · exact (hbd T ω).1
    · exact le_rfl
  rcases eq_or_ne T 0 with hT0 | hT0
  · subst hT0
    simp only [NNReal.coe_zero, mul_zero, neg_zero, Real.exp_zero, one_mul]
    refine integral_mono ((hint 0).indicator hAvm) (hint 0) fun ω => ?_
    simp only [Set.indicator]; split_ifs
    · exact le_rfl
    · exact (hbd 0 ω).1
  have hTpos : 0 < T := pos_iff_ne_zero.mpr hT0
  set η : ℕ → ℝ≥0 := fun n => T / ((n : ℝ≥0) + 2) with hη
  have hηpos : ∀ n, 0 < η n := fun n => div_pos hTpos (by positivity)
  have hηle : ∀ n, η n ≤ T := fun n => by
    simp only [hη]
    exact div_le_self (zero_le (a := T)) (by
      have : (1 : ℝ≥0) ≤ (n : ℝ≥0) + 2 := by
        have := zero_le (a := (n : ℝ≥0)); exact le_trans (by norm_num) (le_add_of_nonneg_left this)
      exact this)
  have hstep : ∀ n, Real.exp (-(K * (T - η n : ℝ≥0))) * I ≤
      ∫ ω, goodMass Gen F s v₀ c₀ φ (η n) ω ∂μ := by
    intro n
    set s' := s + η n with hs'
    set w₀ : FlowSample N → Fin N → ℝ := fun ω => genMass Gen F s v₀ (η n) ω with hw₀
    have hv₀m' : Measurable[shiftFiltration (flowFiltration N) s 0] v₀ := by
      rw [shift0_eq]; exact hv₀m
    have hw₀m : Measurable[shiftFiltration (flowFiltration N) s' 0] w₀ := by
      have := adaptedMass_measurable (shiftFiltration (flowFiltration N) s)
        (genCoeff_adapted hG F s) (genCoeff_continuous hG hF s) hv₀m' (η n)
      rw [shift0_eq]; exact this
    have hw₀ : ∀ ω k, 0 ≤ w₀ ω k ∧ w₀ ω k ≤ 1 := fun ω k =>
      genMass_mem_unit hG hGs hF s hv₀ _ ω k
    have hc₀s : Measurable[flowFiltration N s'] c₀ :=
      hc₀.mono ((flowFiltration N).mono (le_add_of_nonneg_right (zero_le (a := η n)))) le_rfl
    have hc₀' : Measurable[shiftFiltration (flowFiltration N) s' 0] c₀ := by
      rw [shift0_eq]; exact hc₀s
    set ρ := hitTime (cenLam F s' c₀) Kh with hρ
    have hρst : IsStoppingTime (shiftFiltration (flowFiltration N) s') ρ :=
      isStoppingTime_hitTime _ _ (cenLam_adapted F s' hc₀s) (cenLam_continuous hF s' c₀) hKh
    have hmain := gen_expectation_le hIto hStop hDBM hF a s'
      (add_pos_of_nonneg_of_pos (zero_le (a := s)) (hηpos n))
      hG hGs hw₀m hw₀ hc₀' hφ hφ1 hφc hφ0 hφM hA hA0 hB hB0 hKc0 hcomp hc₁ hK0 hK ρ hρst
      (fun ω u hu => by
        have hnot := notMem_of_lt_hitTime hu
        obtain ⟨h1, h2, h3⟩ := hcond _ _ hnot
        exact ⟨h1, fun k l hlk hd => by simpa [lamShift, cenLam] using h2 k l hlk hd, h3⟩)
      (T - η n)
    have hrest : ∀ u ω, genMass Gen F s' w₀ u ω = genMass Gen F s v₀ (η n + u) ω :=
      fun u ω => genMass_restart hG hF s (η n) v₀ ω u
    have hTη : η n + (T - η n) = T := add_tsub_cancel_of_le (hηle n)
    have hsT : s' + (T - η n) = s + T := by rw [hs', add_assoc, hTη]
    have hsi := stopped_tilted_integrable hG hGs hF a s' hw₀m hw₀ hc₀' hφcont hφ0 hφM hK0 ρ hρst
      (T - η n)
    calc Real.exp (-(K * (T - η n : ℝ≥0))) * I
        = ∫ ω, (avoidSet F s c₀ Kh T).indicator
            (fun ω => Real.exp (-(K * (T - η n : ℝ≥0))) * goodMass Gen F s v₀ c₀ φ T ω) ω ∂μ := by
          rw [hI, ← integral_const_mul]
          congr 1; funext ω
          simp only [Set.indicator]; split_ifs <;> simp
      _ ≤ _ := integral_mono ((hint T).const_mul _ |>.indicator hAvm) hsi fun ω => by
          simp only [Set.indicator]
          split_ifs with hω
          · have hρT : ((T - η n : ℝ≥0) : WithTop ℝ≥0) ≤ ρ ω := by
              by_contra hlt
              push Not at hlt
              obtain ⟨r, hr, hrK⟩ := (hitTime_le_iff (cenLam_continuous hF s' c₀ ω) hKh _).mp
                hlt.le
              refine hω (η n + r) (by
                calc η n + r ≤ η n + (T - η n) := add_le_add (le_refl _) hr
                  _ = T := hTη) ?_
              simpa [cenLam, hs', add_assoc] using hrK
            simp only [stoppedProcess, min_eq_left hρT]
            change _ ≤ tiltedMass K φ (((T - η n : ℝ≥0) : ℝ), sumVec (lamShift F s' c₀ (T - η n) ω)
              (genMass Gen F s' w₀ (T - η n) ω))
            simp only [tiltedMass, sumVec_lamIdx, sumVec_massIdx, lamShift, hrest, hTη, hsT,
              goodMass]
            exact le_rfl
          · simp only [stoppedProcess, tiltedMass, sumVec_lamIdx, sumVec_massIdx]
            refine mul_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun k _ =>
              mul_nonneg (hφ0 _) (genMass_mem_unit hG hGs hF s' hw₀ _ ω k).1)
      _ ≤ _ := hmain
      _ = ∫ ω, goodMass Gen F s v₀ c₀ φ (η n) ω ∂μ := by
          refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
          simp only [tiltedMass, sumVec_lamIdx, sumVec_massIdx, lamShift, hrest]
          simp only [mul_zero, neg_zero, Real.exp_zero, one_mul, add_zero, hs',
            goodMass]
  -- `η ↓ 0`
  have hlimL : Tendsto (fun n => Real.exp (-(K * (T - η n : ℝ≥0))) * I) atTop
      (𝓝 (Real.exp (-(K * T)) * I)) := by
    have h1 : Tendsto (fun n => T - η n) atTop (𝓝 (T - 0)) :=
      tendsto_const_nhds.sub (tendsto_eta T)
    rw [tsub_zero] at h1
    have h2 := (NNReal.continuous_coe.tendsto T).comp h1
    exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).tendsto _
      |>.comp h2).mul_const I
  have hlimR : Tendsto (fun n => ∫ ω, goodMass Gen F s v₀ c₀ φ (η n) ω ∂μ) atTop
      (𝓝 (∫ ω, goodMass Gen F s v₀ c₀ φ 0 ω ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => M * N)
      (fun n => (hint (η n)).aestronglyMeasurable) (integrable_const _)
      (fun n => Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hbd _ ω).1]; exact (hbd _ ω).2)
      (Eventually.of_forall fun ω => ?_)
    exact ((goodMass_continuous hG hF s v₀ c₀ hφcont ω).tendsto 0).comp (tendsto_eta T)
  exact le_of_tendsto_of_tendsto' hlimL hlimR hstep

end BlockBand.Palm.RelativeLocalization
