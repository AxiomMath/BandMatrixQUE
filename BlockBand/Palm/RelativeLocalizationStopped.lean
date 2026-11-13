module

public import BlockBand.Palm.RelativeLocalizationFlowMass
public import BlockBand.Palm.RelativeLocalizationExpectation
public import BlockBand.Palm.RelativeLocalizationODE

/-!
# Relative localization: stopped Itô formula and the tilted Gronwall inequality in mean

If the long-gap clauses and a uniform gap `g` hold before a stopping time `ρ`, the Itô formula for
the stopped tilted weighted mass `e^{-Ku} Σ_k φ(λ_k) v_k` and the nonpositivity of its drift show
that its mean at time `T ∧ ρ` is at most its mean at time `0` (`flow_tilted_expectation_le`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.RelativeLocalization

open MeasureTheory ProbabilityTheory Set Filter
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open scoped NNReal

variable {N : ℕ}

theorem sumVec_lamIdx (x y : Fin N → ℝ) (k : Fin N) : sumVec x y (lamIdx k) = x k := by
  simp only [sumVec, lamIdx, Equiv.symm_apply_apply, Sum.elim_inl]

theorem sumVec_massIdx (x y : Fin N → ℝ) (k : Fin N) : sumVec x y (massIdx k) = y k := by
  simp only [sumVec, massIdx, Equiv.symm_apply_apply, Sum.elim_inr]

theorem truncRate_nonneg (g x : ℝ) : 0 ≤ truncRate N g x := by
  unfold truncRate
  have : 0 ≤ max (x ^ 2) (g ^ 2) := le_max_of_le_left (sq_nonneg x)
  positivity

theorem truncShortGen_rowSum (lam : Fin N → ℝ) (ℓ : ℕ) (g : ℝ) (k : Fin N) :
    ∑ l, truncShortGen N lam ℓ g k l = 0 := by
  classical
  have h : ∀ l, truncShortGen N lam ℓ g k l =
      (if l ≠ k ∧ labelDist k l < ℓ then truncRate N g (lam k - lam l) else 0) -
        (if l = k then ∑ m ∈ Finset.univ.filter (fun m => m ≠ k ∧ labelDist k m < ℓ),
          truncRate N g (lam k - lam m) else 0) := by
    intro l
    unfold truncShortGen
    by_cases hl : l = k
    · subst hl; simp
    · have h' : k ≠ l := fun e => hl e.symm
      simp only [h', hl, ite_false, ne_eq, not_false_eq_true, true_and, sub_zero]
  rw [Finset.sum_congr rfl fun l _ => h l, Finset.sum_sub_distrib, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true, ← Finset.sum_filter, sub_self]

theorem truncRefGen_isSubGenerator (lam : ℝ → Fin N → ℝ) (ℓ : ℕ) (b₀ g s u : ℝ) :
    IsSubGenerator (fun x => truncRefGen N (lam x) ℓ b₀ g) s u := by
  classical
  intro x _
  refine ⟨fun k l hkl => ?_, fun k => ?_⟩
  · simp only [truncRefGen, truncShortGen, hkl, ite_false, sub_zero]
    split_ifs
    · exact truncRate_nonneg _ _
    · exact le_rfl
  · have : ∑ l, truncRefGen N (lam x) ℓ b₀ g k l =
        ∑ l, truncShortGen N (lam x) ℓ g k l -
          max (truncLongCoup N (lam x) ℓ g k) (b₀ * N / ℓ) := by
      simp only [truncRefGen, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ,
        ite_true]
    rw [this, truncShortGen_rowSum]
    have : 0 ≤ truncLongCoup N (lam x) ℓ g k := by
      unfold truncLongCoup; exact Finset.sum_nonneg fun m _ => truncRate_nonneg _ _
    linarith [le_max_left (truncLongCoup N (lam x) ℓ g k) (b₀ * N / ℓ)]

theorem refGen_le_short (lam : Fin N → ℝ) (ℓ : ℕ) (b₀ : ℝ) {v : Fin N → ℝ}
    (hv : ∀ k, 0 ≤ v k) (k : Fin N) :
    ∑ l, refGen N lam ℓ b₀ k l * v l ≤ ∑ l, shortGen N lam ℓ k l * v l := by
  have : ∑ l, refGen N lam ℓ b₀ k l * v l =
      ∑ l, shortGen N lam ℓ k l * v l - max (longCoup N lam ℓ k) (b₀ * N / ℓ) * v k := by
    simp only [refGen, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
  rw [this]
  have := mul_nonneg (le_max_of_le_left (longCoup_nonneg lam ℓ k) :
    0 ≤ max (longCoup N lam ℓ k) (b₀ * N / ℓ)) (hv k)
  linarith

/-- The flow mass stays in `[0,1]` for every sample (data in `[0,1]`). -/
theorem flowMass_mem_unit {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (s : ℝ≥0)
    (ℓ : ℕ) (b₀ : ℝ) {g : ℝ} (hg : 0 < g) {v₀ : FlowSample N → Fin N → ℝ}
    (hv₀ : ∀ ω k, 0 ≤ v₀ ω k ∧ v₀ ω k ≤ 1) (u : ℝ≥0) (ω : FlowSample N) (k : Fin N) :
    0 ≤ flowMass F s ℓ b₀ g v₀ u ω k ∧ flowMass F s ℓ b₀ g v₀ u ω k ≤ 1 := by
  have hc := flowCoeff_continuous hF s ℓ b₀ hg
  have hsol := adaptedMass_solution hc v₀ ω (NNReal.coe_nonneg u)
  have hsub : IsSubGenerator (realCoeff (flowCoeff F s ℓ b₀ g) ω) 0 u :=
    truncRefGen_isSubGenerator (fun x => flowLam F (s + x.toNNReal) ω) ℓ b₀ g 0 u
  have hmem : (u : ℝ) ∈ Icc 0 (u : ℝ) := ⟨NNReal.coe_nonneg u, le_rfl⟩
  exact ⟨forwardMass_nonneg hsub hsol (fun k => (hv₀ ω k).1) u hmem k,
    forwardMass_le_const hsub hsol zero_le_one (fun k => (hv₀ ω k).2) u hmem k⟩

/-- Stopped Itô formula and the tilted Gronwall inequality in mean. -/
theorem flow_tilted_expectation_le (hIto : SemimartingaleItoFormula (N + N))
    (hStop : StoppedSemimartingale 1) (hDBM : DysonBrownianMotion N)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (a : ℝ) (s : ℝ≥0) (hs : 0 < s)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (b₀ : ℝ) {g : ℝ} (hg : 0 < g) {v₀ : FlowSample N → Fin N → ℝ}
    (hv₀m : Measurable[shiftFiltration (flowFiltration N) s 0] v₀)
    (hv₀ : ∀ ω k, 0 ≤ v₀ ω k ∧ v₀ ω k ≤ 1)
    {ν E d R r₀ c₁ C₁ K : ℝ} (hν : 0 ≤ ν) (hd : 0 < d) (hR : 0 < R) (hρ : d + 2 * R ≤ r₀ / 8)
    (hc₁ : 0 < c₁) (hK0 : 0 ≤ K)
    (hK : 2 * ℓ * (ν * (weightConst / R + weightConst / d) + ν ^ 2 * weightConst ^ 2) *
            Real.exp (ν * weightConst * (C₁ * ℓ / N)) / N +
          2 * (ν * weightConst) * (1 + Real.log N) / c₁ +
          (ν * (weightConst / R + weightConst / d) + ν ^ 2 * weightConst ^ 2) / (2 * N) ≤ K)
    (ρ : FlowSample N → WithTop ℝ≥0) (hρst : IsStoppingTime (shiftFiltration (flowFiltration N) s) ρ)
    (hgood : ∀ ω (u : ℝ≥0), (u : WithTop ℝ≥0) < ρ ω →
      (∀ i j : Fin N, ℓ ≤ labelDist i j →
        c₁ * labelDist i j / N ≤ |flowLam F (s + u) ω i - flowLam F (s + u) ω j|) ∧
      (∀ i j : Fin N, labelDist i j < ℓ →
        min |flowLam F (s + u) ω i - E| |flowLam F (s + u) ω j - E| ≤ r₀ / 8 →
        |flowLam F (s + u) ω i - flowLam F (s + u) ω j| ≤ C₁ * ℓ / N) ∧
      (∀ i j : Fin N, i ≠ j → g ≤ |flowLam F (s + u) ω i - flowLam F (s + u) ω j|))
    (T : ℝ≥0) :
    ∫ ω, stoppedProcess (fun (u : ℝ≥0) ω => tiltedMass K (rlPhi ν E d R)
        ((u : ℝ), sumVec (flowLam F (s + u) ω) (flowMass F s ℓ b₀ g v₀ u ω))) ρ T ω
        ∂flowLaw N a ≤
      ∫ ω, tiltedMass K (rlPhi ν E d R)
        (0, sumVec (flowLam F s ω) (flowMass F s ℓ b₀ g v₀ 0 ω)) ∂flowLaw N a := by
  set Y : ℝ≥0 → FlowSample N → Fin (N + N) → ℝ :=
    fun u ω => sumVec (flowLam F (s + u) ω) (flowMass F s ℓ b₀ g v₀ u ω) with hYdef
  set B : ℝ≥0 → FlowSample N → Fin (N + N) → ℝ :=
    fun u ω => sumVec (fun k => dysonDrift N (flowLam F (s + u) ω) k)
      (matAct (flowCoeff F s ℓ b₀ g u ω) (flowMass F s ℓ b₀ g v₀ u ω)) with hBdef
  set Φ := tiltedMass (N := N) K (rlPhi ν E d R) with hΦ
  have hY := flow_state_semimartingale hDBM hF a s hs ℓ b₀ hg hv₀m
  have hΦc : ContDiff ℝ 2 Φ := tiltedMass_contDiff (rlPhi_contDiff hd hR)
  have hI := hIto (FlowSample N) (flowLaw N a) (shiftFiltration (flowFiltration N) s) Y B
    (fun _ _ => lamCov N) hY Set.univ isOpen_univ (Eventually.of_forall fun _ _ => trivial) Φ
    (hΦc.continuous.measurable) hΦc.contDiffOn
  have hS := hStop (FlowSample N) (flowLaw N a) (shiftFiltration (flowFiltration N) s) _ _ _ hI
    ρ hρst
  -- bounds
  have hbd : ∀ (u : ℝ≥0) ω, |Φ ((u : ℝ), Y u ω)| ≤ N := by
    intro u ω
    have hv := flowMass_mem_unit hF s ℓ b₀ hg hv₀ u ω
    have hexp : Real.exp (-(K * u)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by have := NNReal.coe_nonneg u; nlinarith)
    have hsum0 : 0 ≤ ∑ k, rlPhi ν E d R (Y u ω (lamIdx k)) * Y u ω (massIdx k) :=
      Finset.sum_nonneg fun k _ => mul_nonneg (rlPhi_pos _).le (by
        rw [hYdef]; simp only [sumVec_massIdx]; exact (hv k).1)
    have hsum1 : ∑ k, rlPhi ν E d R (Y u ω (lamIdx k)) * Y u ω (massIdx k) ≤ N := by
      calc _ ≤ ∑ _k : Fin N, (1 : ℝ) := Finset.sum_le_sum fun k _ => by
            rw [hYdef]; simp only [sumVec_massIdx]
            calc _ ≤ 1 * 1 := mul_le_mul (rlPhi_le_one hν hR _) (hv k).2 (hv k).1 zero_le_one
              _ = 1 := one_mul 1
        _ = N := by simp
    simp only [hΦ, tiltedMass]
    rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hsum0)]
    calc _ ≤ 1 * (N : ℝ) := mul_le_mul hexp hsum1 hsum0 zero_le_one
      _ = N := one_mul _
  -- the drift integrals are nonpositive
  have hdrift : ∀ ω (u : ℝ≥0), (u : WithTop ℝ≥0) < ρ ω →
      itoDrift Φ (Y u ω) u (B u ω) (lamCov N) ≤ 0 := by
    intro ω u hu
    obtain ⟨h1, h2, h3⟩ := hgood ω u hu
    have hv := flowMass_mem_unit hF s ℓ b₀ hg hv₀ u ω
    have hlam : (fun m => Y u ω (lamIdx m)) = flowLam F (s + u) ω := by
      funext m; rw [hYdef]; simp only [sumVec_lamIdx]
    have hmass : (fun m => Y u ω (massIdx m)) = flowMass F s ℓ b₀ g v₀ u ω := by
      funext m; rw [hYdef]; simp only [sumVec_massIdx]
    have hL : flowCoeff F s ℓ b₀ g u ω = refGen N (flowLam F (s + u) ω) ℓ b₀ :=
      truncRefGen_eq hℓ hg.le h3
    refine itoDrift_rlPhi_nonpos hν hd hR hρ hc₁ ℓ (Y u ω) u
      (refGen N (flowLam F (s + u) ω) ℓ b₀) (fun k => ?_) (fun k => ?_) ?_ ?_ hK (B u ω)
      (fun k => ?_) (fun k => ?_)
    · rw [hYdef]; simp only [sumVec_massIdx]; exact (hv k).1
    · have := refGen_le_short (flowLam F (s + u) ω) ℓ b₀ (v := flowMass F s ℓ b₀ g v₀ u ω)
        (fun k => (hv k).1) k
      simpa only [hYdef, sumVec_massIdx, sumVec_lamIdx] using this
    · intro i j hij; simpa only [hYdef, sumVec_lamIdx] using h1 i j hij
    · intro i j hij hm
      simp only [hYdef, sumVec_lamIdx] at hm ⊢
      exact h2 i j hij hm
    · simp only [hBdef, hYdef, sumVec_lamIdx]
    · simp only [hBdef, hYdef, sumVec_massIdx, hL, matAct]
  have hβ : ∀ᵐ ω ∂flowLaw N a, ∀ r : ℝ≥0, ∫ x in Set.Ioc (0 : ℝ) r,
      switchAfter ρ (fun t ω (_ : Fin 1) => itoDrift Φ (Y t ω) t (B t ω) (lamCov N))
        x.toNNReal ω 0 ≤ 0 := by
    refine Eventually.of_forall fun ω r => setIntegral_nonpos_of_ae_restrict ?_
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [Measure.ae_ne volume (((ρ ω).untopA : ℝ≥0) : ℝ)] with x hx hxI
    have hx0 : 0 < x := hxI.1
    simp only [switchAfter, Pi.zero_apply]
    split_ifs with hle
    · refine hdrift ω x.toNNReal (lt_of_le_of_ne hle fun heq => hx ?_)
      cases hρω : ρ ω with
      | top => rw [hρω] at heq; exact absurd heq WithTop.coe_ne_top
      | coe p =>
        rw [hρω] at heq
        have := WithTop.coe_injective heq
        change x = ((p : ℝ≥0) : ℝ)
        rw [← this, Real.coe_toNNReal _ hx0.le]
    · exact le_rfl
  have hfin := integral_le_of_drift_nonpos (flowLaw N a) (shiftFiltration (flowFiltration N) s)
    _ _ _ hS (C := N) (fun t ω => hbd _ ω) hβ T
  have e0 : ∀ ω, stoppedProcess (fun (t : ℝ≥0) ω (_ : Fin 1) => Φ ((t : ℝ), Y t ω)) ρ 0 ω 0 =
      Φ (0, sumVec (flowLam F s ω) (flowMass F s ℓ b₀ g v₀ 0 ω)) := by
    intro ω
    have hm : min ((0 : ℝ≥0) : WithTop ℝ≥0) (ρ ω) = ((0 : ℝ≥0) : WithTop ℝ≥0) :=
      min_eq_left (by rw [WithTop.coe_zero]; exact zero_le (a := ρ ω))
    simp only [stoppedProcess]
    rw [hm]
    have hu : ((((0 : ℝ≥0) : WithTop ℝ≥0)).untopA : ℝ≥0) = 0 := rfl
    rw [hu]
    simp only [hYdef, add_zero, NNReal.coe_zero]
  calc ∫ ω, stoppedProcess (fun (u : ℝ≥0) ω => Φ ((u : ℝ), Y u ω)) ρ T ω ∂flowLaw N a
      = ∫ ω, stoppedProcess (fun (t : ℝ≥0) ω (_ : Fin 1) => Φ ((t : ℝ), Y t ω)) ρ T ω 0
          ∂flowLaw N a := rfl
    _ ≤ ∫ ω, stoppedProcess (fun (t : ℝ≥0) ω (_ : Fin 1) => Φ ((t : ℝ), Y t ω)) ρ 0 ω 0
          ∂flowLaw N a := hfin
    _ = _ := integral_congr_ae (Eventually.of_forall e0)

end BlockBand.Palm.RelativeLocalization
