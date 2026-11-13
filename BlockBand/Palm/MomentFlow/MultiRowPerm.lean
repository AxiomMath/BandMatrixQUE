module

public import BlockBand.Palm.MomentFlow.MultiFlowGen
public import BlockBand.Palm.MomentFlow.MultiMatch
public import BlockBand.Palm.MomentFlow.MultiShort

/-!
# `r`-particle finite speed in the matching distance, quantitative form

`multi_match_row_quant`: for flow times `a < s ≤ u`, `ξ₀` in the `r`-sector with a labelling `x`,
the far set `{ζ : occDist ξ₀ ζ > r R}` (`occDist`), the matching weight
`W = permW φ λ c` with one centre `c_m = λ_{x_m}(s)` per particle (`φ = rlPhi ν 0 d R₀`), and any
sample set `G` on which (when every particle of `ξ₀` is in the bulk at time `s`) the initial matrix
is Hermitian, the gap clauses and gaps `> g` hold on `[s,u]`, every far configuration has
`W(λ(s)) ≤ δ₀` and `W(λ(u))(ξ₀) ≥ w`:

`P(bulk ∧ ∃ Φ solving 𝓢 on [s,u], Φ(s) = 1_far, e < Φ(u, ξ₀)) ≤ P(Gᶜ) + M δ₀ e^{K(u-s)}/(w e)`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open MeasureTheory ProbabilityTheory Set Filter Finset
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Palm.RelativeLocalization
open scoped NNReal

variable {N : ℕ}

/-- The summed drift inequality in enumeration coordinates. -/
theorem perm_Q_le (lam : Fin N → ℝ) (ℓ r : ℕ) (c : Fin r → ℝ) (vv : Fin (sectorCard N r) → ℝ)
    (hvv : ∀ q, 0 ≤ vv q)
    {φ φ1 φ2 : ℝ → ℝ} (hφ : ∀ z, HasDerivAt φ (φ1 z) z) (hφ1 : ∀ z, HasDerivAt φ1 (φ2 z) z)
    {A B Kc G c₁ : ℝ} (hφ0 : ∀ z, 0 ≤ φ z) (hA : ∀ z, |φ1 z| ≤ A * φ z) (hA0 : 0 ≤ A)
    (hB : ∀ z, |φ2 z| ≤ B * φ z) (hB0 : 0 ≤ B) (hKc0 : 0 ≤ Kc)
    (hcomp : ∀ x z, |z - x| ≤ G → φ z ≤ Kc * φ x) (hc₁ : 0 < c₁)
    (hshort : ∀ m k l, l ≠ k → labelDist k l < ℓ →
      |lam l - lam k| ≤ G ∨ (φ1 (lam k - c m) = 0 ∧ φ (lam l - c m) = φ (lam k - c m)))
    (hlong : ∀ k l, l ≠ k → ℓ ≤ labelDist k l → c₁ * labelDist k l / N ≤ |lam k - lam l|) :
    ∑ q, permW φ lam c (sectorEnum N r q) *
          ∑ q', cfgMat (cfgRate N lam ℓ 0) r q q' * vv q' +
        ∑ q, vv q * ∑ i, (dysonDrift N lam i *
          (cfgFact (sectorEnum N r q) * ∑ y ∈ labs r (sectorEnum N r q), permD1 φ φ1 lam c y i) +
          cfgFact (sectorEnum N r q) * ∑ y ∈ labs r (sectorEnum N r q),
            permD2 φ φ1 φ2 lam c y i / (2 * N)) ≤
      (r * (2 * ℓ * B * Kc / N + 2 * A * (1 + Real.log N) / c₁ + B / (2 * N)) +
          r ^ 2 * (A ^ 2 * (Kc ^ 2 + 1)) / (2 * N)) *
        ∑ q, permW φ lam c (sectorEnum N r q) * vv q := by
  have hact : ∀ q, ∑ q', cfgMat (cfgRate N lam ℓ 0) r q q' * vv q' =
      momentGenerator (cfgRate N lam ℓ 0) (cfgExt r vv) (sectorEnum N r q) := by
    intro q
    rw [← cfgMat_act]
    exact Finset.sum_congr rfl fun q' _ => by rw [cfgExt_enum]
  have hv : ∀ ξ ∈ sector N r, 0 ≤ cfgExt r vv ξ := fun ξ hξ => by
    rw [cfgExt_of_mem vv hξ]; exact hvv _
  have h := perm_drift_le (r := r) lam ℓ c hφ hφ1 hφ0 hA hA0 hB hB0 hKc0 hcomp hc₁ hshort hlong
    (cfgExt r vv) hv
  set T : Occ N → ℝ := fun ξ => ∑ i, (dysonDrift N lam i *
      (cfgFact ξ * ∑ y ∈ labs r ξ, permD1 φ φ1 lam c y i) +
      cfgFact ξ * ∑ y ∈ labs r ξ, permD2 φ φ1 φ2 lam c y i / (2 * N)) with hT
  have e1 : ∑ q, permW φ lam c (sectorEnum N r q) *
        ∑ q', cfgMat (cfgRate N lam ℓ 0) r q q' * vv q' =
      ∑ ξ ∈ sector N r, permW φ lam c ξ * momentGenerator (cfgRate N lam ℓ 0) (cfgExt r vv) ξ :=
    (Finset.sum_congr rfl fun q _ => by rw [hact]).trans (sum_sectorEnum r (fun ξ =>
      permW φ lam c ξ * momentGenerator (cfgRate N lam ℓ 0) (cfgExt r vv) ξ))
  have e2 : ∑ q, vv q * T (sectorEnum N r q) = ∑ ξ ∈ sector N r, cfgExt r vv ξ * T ξ :=
    (Finset.sum_congr rfl fun q _ => by rw [cfgExt_enum]).trans
      (sum_sectorEnum r (fun ξ => cfgExt r vv ξ * T ξ))
  have e3 : ∑ q, permW φ lam c (sectorEnum N r q) * vv q =
      ∑ ξ ∈ sector N r, permW φ lam c ξ * cfgExt r vv ξ :=
    (Finset.sum_congr rfl fun q _ => by rw [cfgExt_enum]).trans (sum_sectorEnum r (fun ξ =>
      permW φ lam c ξ * cfgExt r vv ξ))
  rw [e1, e3]
  exact e2 ▸ h

/-- **`r`-particle finite speed in the matching distance, quantitative form.** -/
theorem multi_match_row_quant (r : ℕ) (hIto : SemimartingaleItoFormula (N + (r + sectorCard N r)))
    (hStop : StoppedSemimartingale 1) (hDBM : DysonBrownianMotion N) (hN : 0 < N)
    {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) {a s u : ℝ} (has : a < s) (hsu : s ≤ u)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {ξ₀ : Occ N} (hξ₀ : ξ₀ ∈ sector N r) {x : Fin r → Fin N}
    (hx : x ∈ labs r ξ₀) (R : ℝ)
    {E r₀ ν d R₀ c₁ C₁ g K δ₀ w e : ℝ} (hν : 0 ≤ ν) (hd : 0 < d) (hR₀ : 0 < R₀)
    (hρ : d + 2 * R₀ ≤ r₀ / 16) (hc₁ : 0 < c₁) (hC₁ : 0 < C₁) (hg : 0 < g) (hK0 : 0 ≤ K)
    (hK : r * (2 * ℓ * (ν * (weightConst / R₀ + weightConst / d) + ν ^ 2 * weightConst ^ 2) *
            Real.exp (ν * weightConst * (2 * C₁ * ℓ / N)) / N +
          2 * (ν * weightConst) * (1 + Real.log N) / (c₁ / 2) +
          (ν * (weightConst / R₀ + weightConst / d) + ν ^ 2 * weightConst ^ 2) / (2 * N)) +
        r ^ 2 * ((ν * weightConst) ^ 2 *
          (Real.exp (ν * weightConst * (2 * C₁ * ℓ / N)) ^ 2 + 1)) / (2 * N) ≤ K)
    (hδ₀ : 0 ≤ δ₀) (hw : 0 < w) (he : 0 < e) (G : Set (FlowSample N))
    (hG : ∀ ω ∈ G, (∀ k : Fin N, 0 < ξ₀ k → |flowEigenvalue F a ω s k - E| ≤ r₀ / 16) →
      ω.1.IsHermitian ∧
      (∀ σ ∈ Icc s u,
        (∀ i j : Fin N, ℓ ≤ labelDist i j →
          c₁ * labelDist i j / N ≤ |flowEigenvalue F a ω σ i - flowEigenvalue F a ω σ j|) ∧
        (∀ i j : Fin N, labelDist i j < ℓ →
          min |flowEigenvalue F a ω σ i - E| |flowEigenvalue F a ω σ j - E| ≤ r₀ / 8 →
          |flowEigenvalue F a ω σ i - flowEigenvalue F a ω σ j| ≤ C₁ * ℓ / N) ∧
        (∀ i j : Fin N, i ≠ j → g < |flowEigenvalue F a ω σ i - flowEigenvalue F a ω σ j|)) ∧
      (∀ ζ ∈ sector N r, (r : ℝ) * R < (occDist ξ₀ ζ : ℝ) →
        permW (rlPhi ν 0 d R₀) (flowEigenvalue F a ω s)
          (fun m => flowEigenvalue F a ω s (x m)) ζ ≤ δ₀) ∧
      w ≤ permW (rlPhi ν 0 d R₀) (flowEigenvalue F a ω u)
          (fun m => flowEigenvalue F a ω s (x m)) ξ₀) :
    flowLaw N a {ω | (∀ k : Fin N, 0 < ξ₀ k → |flowEigenvalue F a ω s k - E| ≤ r₀ / 16) ∧
        ∃ Φ : ℝ → Occ N → ℝ, IsMomentFlowSolution (shortFlowRate F a ω ℓ) r s u Φ ∧
          (∀ ζ ∈ sector N r, Φ s ζ = if (r : ℝ) * R < (occDist ξ₀ ζ : ℝ) then 1 else 0) ∧
          e < Φ u ξ₀} ≤
      flowLaw N a Gᶜ +
        ENNReal.ofReal (sectorCard N r * δ₀ / (Real.exp (-(K * (u - s))) * w * e)) := by
  classical
  set μ := flowLaw N a with hμ
  have hr₀ : 0 ≤ r₀ := by linarith
  set sL : ℝ≥0 := Real.toNNReal (s - a) with hsLdef
  set T : ℝ≥0 := Real.toNNReal (u - s) with hTdef
  have hsL : (sL : ℝ) = s - a := Real.coe_toNNReal _ (by linarith)
  have hsLpos : 0 < sL := Real.toNNReal_pos.mpr (by linarith)
  have hT : (T : ℝ) = u - s := Real.coe_toNNReal _ (by linarith)
  set φ := rlPhi ν 0 d R₀ with hφdef
  have hφc : Continuous φ := (rlPhi_contDiff hd hR₀).continuous
  have hφ0 : ∀ z, 0 ≤ φ z := fun z => (rlPhi_pos z).le
  have hφle : ∀ z, φ z ≤ 1 := rlPhi_le_one hν hR₀
  obtain ⟨c₀, hc₀def⟩ : ∃ c₀ : FlowSample N → Fin r → ℝ,
      c₀ = fun ω m => clampC E r₀ (flowLam F sL ω (x m)) := ⟨_, rfl⟩
  set σe := sectorEnum N r with hσe
  set farD : Occ N → Prop := fun ζ => (r : ℝ) * R < (occDist ξ₀ ζ : ℝ) with hfarD
  obtain ⟨fI, hfIdef⟩ : ∃ fI : Occ N → ℝ, fI = fun ζ => if farD ζ then 1 else 0 := ⟨_, rfl⟩
  obtain ⟨wt, hwt⟩ : ∃ wt : Fin (sectorCard N r) → (Fin N → ℝ) → (Fin r → ℝ) → ℝ,
      wt = fun q lam c => permW φ lam c (σe q) := ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ A : Set (FlowSample N), A = {ω | ∀ q, farD (σe q) →
    wt q (flowLam F (sL + 0) ω) (c₀ ω) ≤ δ₀} := ⟨_, rfl⟩
  obtain ⟨v₀, hv₀def⟩ : ∃ v₀ : FlowSample N → Fin (sectorCard N r) → ℝ,
      v₀ = fun ω q => A.indicator (fun _ => fI (σe q)) ω := ⟨_, rfl⟩
  set ρ := flowStop F sL ℓ E r₀ c₁ C₁ g with hρdef
  set Kc := Real.exp (ν * weightConst * (2 * C₁ * ℓ / N)) with hKc
  -- measurability at the start
  have hlam0 : Measurable[shiftFiltration (flowFiltration N) sL 0] (flowLam F (sL + 0)) :=
    flowLam_adapted F (sL + 0)
  have hle0 : flowFiltration N sL ≤ shiftFiltration (flowFiltration N) sL 0 :=
    (flowFiltration N).mono (le_of_eq (add_zero sL).symm)
  have hc₀m : Measurable[shiftFiltration (flowFiltration N) sL 0] c₀ := by
    rw [hc₀def]
    refine @measurable_pi_iff (FlowSample N) (Fin r) (fun _ => ℝ)
      (shiftFiltration (flowFiltration N) sL 0) _ _ |>.mpr fun m => ?_
    exact ((continuous_clampC E r₀).measurable.comp
      ((measurable_pi_apply (x m)).comp (flowLam_adapted F sL))).mono hle0 le_rfl
  have hwcd : ∀ q, ContDiff ℝ 2 (fun z : (Fin N → ℝ) × (Fin r → ℝ) => wt q z.1 z.2) :=
    fun q => by rw [hwt]; exact permW_contDiff (rlPhi_contDiff hd hR₀) (σe q)
  have hwc : ∀ q, Continuous (fun z : (Fin N → ℝ) × (Fin r → ℝ) => wt q z.1 z.2) :=
    fun q => (hwcd q).continuous
  have hAm : MeasurableSet[shiftFiltration (flowFiltration N) sL 0] A := by
    have : A = ⋂ q, {ω | farD (σe q) → wt q (flowLam F (sL + 0) ω) (c₀ ω) ≤ δ₀} := by
      rw [hAdef]; ext ω; simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    rw [this]
    refine MeasurableSet.iInter fun q => ?_
    by_cases hq : farD (σe q)
    · simp only [hq, true_imp_iff]
      have hmq : Measurable[shiftFiltration (flowFiltration N) sL 0]
          (fun ω => wt q (flowLam F (sL + 0) ω) (c₀ ω)) :=
        (hwc q).measurable.comp (hlam0.prodMk hc₀m)
      exact measurableSet_le hmq measurable_const
    · simp only [hq, false_imp_iff, Set.ofPred_true]; exact MeasurableSet.univ
  have hv₀m : Measurable[shiftFiltration (flowFiltration N) sL 0] v₀ := by
    refine @measurable_pi_iff (FlowSample N) (Fin (sectorCard N r)) (fun _ => ℝ)
      (shiftFiltration (flowFiltration N) sL 0) _ _ |>.mpr fun q => ?_
    rw [hv₀def]
    exact Measurable.indicator measurable_const hAm
  have hfI : ∀ ζ, 0 ≤ fI ζ ∧ fI ζ ≤ 1 := fun ζ => by rw [hfIdef]; dsimp only; split_ifs <;> norm_num
  have hv₀ : ∀ ω q, 0 ≤ v₀ ω q ∧ v₀ ω q ≤ 1 := by
    intro ω q
    rw [hv₀def]
    simp only [Set.indicator]
    split_ifs
    · exact hfI _
    · norm_num
  -- the weight bound and the drift hypothesis
  set Wm : ℝ := ∑ q, cfgFact (σe q) * ((labs r (σe q)).card : ℝ) with hWm
  have hw0 : ∀ q lam c, 0 ≤ wt q lam c := fun q lam c => by
    rw [hwt]; exact mul_nonneg (cfgFact_pos _).le (Finset.sum_nonneg fun y _ => pW_nonneg hφ0 lam c y)
  have hwM : ∀ q lam c, wt q lam c ≤ Wm := by
    intro q lam c
    have h1 : wt q lam c ≤ cfgFact (σe q) * ((labs r (σe q)).card : ℝ) := by
      rw [hwt]; simp only [permW]
      refine mul_le_mul_of_nonneg_left ?_ (cfgFact_pos _).le
      calc ∑ y ∈ labs r (σe q), pW φ lam c y ≤ ∑ _y ∈ labs r (σe q), (1 : ℝ) :=
            Finset.sum_le_sum fun y _ => Finset.prod_le_one₀ (fun m _ => hφ0 _)
              (fun m _ => hφle _)
        _ = _ := by simp
    refine h1.trans ?_
    exact Finset.single_le_sum (f := fun q => cfgFact (σe q) * ((labs r (σe q)).card : ℝ))
      (fun q _ => mul_nonneg (cfgFact_pos _).le (Nat.cast_nonneg _)) (Finset.mem_univ q)
  have hWm0 : 0 ≤ Wm := Finset.sum_nonneg fun q _ => mul_nonneg (cfgFact_pos _).le
    (Nat.cast_nonneg _)
  have hcomp : ∀ x' z, |z - x'| ≤ 2 * C₁ * ℓ / N → φ z ≤ Kc * φ x' := by
    intro x' z hxz
    refine (rlPhi_le_exp_mul hν hd hR₀ x' z).trans
      (mul_le_mul_of_nonneg_right ?_ (rlPhi_pos x').le)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hxz
      (mul_nonneg hν weightConst_pos.le))
  have hgood : ∀ ω (xx : ℝ≥0), (xx : WithTop ℝ≥0) < ρ ω → ∀ vv : Fin (sectorCard N r) → ℝ,
      (∀ q, 0 ≤ vv q) →
      ∑ q, wt q (flowLam F (sL + xx) ω) (c₀ ω) *
          ∑ q', mfCoeff F sL ℓ g r xx ω q q' * vv q' +
        ∑ q, vv q * ∑ i, (dysonDrift N (flowLam F (sL + xx) ω) i *
          (cfgFact (σe q) * ∑ y ∈ labs r (σe q),
            permD1 φ (rlPhi1 ν 0 d R₀) (flowLam F (sL + xx) ω) (c₀ ω) y i) +
          cfgFact (σe q) * ∑ y ∈ labs r (σe q), permD2 φ (rlPhi1 ν 0 d R₀) (rlPhi2 ν 0 d R₀)
            (flowLam F (sL + xx) ω) (c₀ ω) y i / (2 * N)) ≤
      K * ∑ q, wt q (flowLam F (sL + xx) ω) (c₀ ω) * vv q := by
    intro ω xx hxx vv hvv
    obtain ⟨h1, h2, h3⟩ := good_before_flowStop hxx
    have hrate : cfgRate N (flowLam F (sL + xx) ω) ℓ g = cfgRate N (flowLam F (sL + xx) ω) ℓ 0 :=
      cfgRate_eq_zero_gap hg.le h3
    have hsh : ∀ m k l, l ≠ k → labelDist k l < ℓ →
        |flowLam F (sL + xx) ω l - flowLam F (sL + xx) ω k| ≤ 2 * C₁ * ℓ / N ∨
          (rlPhi1 ν 0 d R₀ (flowLam F (sL + xx) ω k - c₀ ω m) = 0 ∧
            φ (flowLam F (sL + xx) ω l - c₀ ω m) = φ (flowLam F (sL + xx) ω k - c₀ ω m)) := by
      intro m k l hlk hd'
      have hcl : |c₀ ω m - E| ≤ r₀ / 16 := by
        rw [hc₀def]; exact abs_clampC_sub_le hr₀ _
      have hh := rlPhi_short_close_or_flat (ν := ν) (E := 0) (d := d) (R := R₀) (r₀ := r₀ / 2)
        (G := 2 * C₁ * ℓ / N) hR₀ (by linarith)
        (fun l => flowLam F (sL + xx) ω l - c₀ ω m) ℓ (fun i j hij hm => by
          have hdiff : (flowLam F (sL + xx) ω i - c₀ ω m) - (flowLam F (sL + xx) ω j - c₀ ω m) =
              flowLam F (sL + xx) ω i - flowLam F (sL + xx) ω j := by ring
          rw [hdiff]
          refine h2 i j hij ?_
          simp only [sub_zero] at hm
          rcases min_le_iff.1 hm with hm | hm
          · refine (min_le_left _ _).trans ?_
            calc |flowLam F (sL + xx) ω i - E|
                ≤ |flowLam F (sL + xx) ω i - c₀ ω m| + |c₀ ω m - E| := abs_sub_le _ _ _
              _ ≤ r₀ / 2 / 8 + r₀ / 16 := add_le_add hm hcl
              _ = r₀ / 8 := by ring
          · refine (min_le_right _ _).trans ?_
            calc |flowLam F (sL + xx) ω j - E|
                ≤ |flowLam F (sL + xx) ω j - c₀ ω m| + |c₀ ω m - E| := abs_sub_le _ _ _
              _ ≤ r₀ / 2 / 8 + r₀ / 16 := add_le_add hm hcl
              _ = r₀ / 8 := by ring) k l hlk hd'
      rcases hh with hh | hh
      · left; simpa only [sub_sub_sub_cancel_right] using hh
      · exact Or.inr hh
    have hQ := perm_Q_le (flowLam F (sL + xx) ω) ℓ r (c₀ ω) vv hvv
      (rlPhi_hasDerivAt hd hR₀) (rlPhi1_hasDerivAt hd hR₀) hφ0 (abs_rlPhi1_le hν hd hR₀)
      (mul_nonneg hν weightConst_pos.le) (abs_rlPhi2_le hν hd hR₀)
      (by have := weightConst_pos; positivity) (Real.exp_pos _).le hcomp (half_pos hc₁) hsh
      (fun k l _ hkl => h1 k l hkl)
    rw [hwt]; simp only [mfCoeff, hrate]
    exact hQ.trans (mul_le_mul_of_nonneg_right hK (Finset.sum_nonneg fun q _ =>
      mul_nonneg (mul_nonneg (cfgFact_pos _).le
        (Finset.sum_nonneg fun y _ => pW_nonneg hφ0 _ _ y)) (hvv q)))
  have hd1 : ∀ q lam c i, HasDerivAt
      (fun s : ℝ => wt q (fun m => lam m + if m = i then s else 0) c)
      (cfgFact (σe q) * ∑ y ∈ labs r (σe q), permD1 φ (rlPhi1 ν 0 d R₀) lam c y i) 0 :=
    fun q lam c i => by
      rw [hwt]; exact hasDerivAt_permW_line (rlPhi_hasDerivAt hd hR₀) lam c (σe q) i
  have hd2 : ∀ q lam c i, HasDerivAt
      (fun s : ℝ => cfgFact (σe q) * ∑ y ∈ labs r (σe q),
        permD1 φ (rlPhi1 ν 0 d R₀) (fun m => lam m + if m = i then s else 0) c y i)
      (cfgFact (σe q) * ∑ y ∈ labs r (σe q),
        permD2 φ (rlPhi1 ν 0 d R₀) (rlPhi2 ν 0 d R₀) lam c y i) 0 :=
    fun q lam c i => hasDerivAt_permWD1_line (rlPhi_hasDerivAt hd hR₀)
      (rlPhi1_hasDerivAt hd hR₀) lam c (σe q) i
  have hgood' : ∀ ω (xx : ℝ≥0), (xx : WithTop ℝ≥0) < ρ ω → ∀ vv : Fin (sectorCard N r) → ℝ,
      (∀ q, 0 ≤ vv q) →
      ∑ q, wt q (flowLam F (sL + xx) ω) (c₀ ω) *
          ∑ q', mfCoeff F sL ℓ g r xx ω q q' * vv q' +
        ∑ q, vv q * ∑ i, (dysonDrift N (flowLam F (sL + xx) ω) i *
          (cfgFact (σe q) * ∑ y ∈ labs r (σe q),
            permD1 φ (rlPhi1 ν 0 d R₀) (flowLam F (sL + xx) ω) (c₀ ω) y i) +
          (cfgFact (σe q) * ∑ y ∈ labs r (σe q), permD2 φ (rlPhi1 ν 0 d R₀) (rlPhi2 ν 0 d R₀)
            (flowLam F (sL + xx) ω) (c₀ ω) y i) / (2 * N)) ≤
      K * ∑ q, wt q (flowLam F (sL + xx) ω) (c₀ ω) * vv q := by
    intro ω xx hxx vv hvv
    have := hgood ω xx hxx vv hvv
    simp only [Finset.sum_div, mul_div_assoc] at this ⊢
    exact this
  have hexp := gen_mf_expectation_le r hIto hStop hDBM hN hF a sL hsLpos ℓ hg hv₀m hv₀ hc₀m
    (w := wt) hwcd hd1 hd2 hWm0 hw0 hwM
    hK0 ρ (isStoppingTime_flowStop hF sL ℓ E r₀ c₁ C₁ g) hgood' T
  -- the stopped value
  set X : FlowSample N → ℝ := stoppedProcess (fun (xx : ℝ≥0) ω => gTilted K wt
      ((xx : ℝ), gState F sL ℓ g r c₀ v₀ xx ω)) ρ T with hXdef
  have hmass0 : ∀ ω, mfMass F sL ℓ g r v₀ 0 ω = v₀ ω := fun ω =>
    (adaptedMass_solution (mfCoeff_continuous hN hF sL ℓ hg r) v₀ ω le_rfl).1
  have hinit_pt : ∀ ω, gTilted K wt (0, gState F sL ℓ g r c₀ v₀ 0 ω) ≤ sectorCard N r * δ₀ := by
    intro ω
    rw [gState, gTilted_sumVec, hmass0]
    simp only [mul_zero, neg_zero, Real.exp_zero, one_mul]
    calc ∑ q, wt q (flowLam F (sL + 0) ω) (c₀ ω) * v₀ ω q ≤ ∑ _q : Fin (sectorCard N r), δ₀ :=
          Finset.sum_le_sum fun q _ => by
            rw [hv₀def]
            simp only [Set.indicator]
            split_ifs with hωA
            · rw [hfIdef]
              dsimp only
              split_ifs with hq
              · rw [mul_one]; rw [hAdef] at hωA; exact hωA q hq
              · rw [mul_zero]; exact hδ₀
            · rw [mul_zero]; exact hδ₀
      _ = sectorCard N r * δ₀ := by simp
  have hinit : ∫ ω, gTilted K wt (0, gState F sL ℓ g r c₀ v₀ 0 ω) ∂μ ≤ sectorCard N r * δ₀ := by
    by_cases hi : Integrable (fun ω => gTilted K wt (0, gState F sL ℓ g r c₀ v₀ 0 ω)) μ
    · calc _ ≤ ∫ _ω, (sectorCard N r * δ₀ : ℝ) ∂μ := integral_mono hi (integrable_const _) hinit_pt
        _ = sectorCard N r * δ₀ := by simp
    · rw [integral_undef hi]; positivity
  have hXint_le : ∫ ω, X ω ∂μ ≤ sectorCard N r * δ₀ := hexp.trans hinit
  -- integrability of the stopped value
  have hYc : ∀ ω, Continuous fun xx : ℝ≥0 => gState F sL ℓ g r c₀ v₀ xx ω := fun ω =>
    continuous_sumVec.comp (((flowLam_continuous hF ω).comp
      (continuous_const.add continuous_id)).prodMk (continuous_sumVec.comp
        (continuous_const.prodMk (adaptedMass_continuous (mfCoeff_continuous hN hF sL ℓ hg r)
          v₀ ω))))
  have hYa : ∀ xx, Measurable[shiftFiltration (flowFiltration N) sL xx]
      (fun ω => gState F sL ℓ g r c₀ v₀ xx ω) := by
    intro xx
    have h1 := flowLam_adapted F (sL + xx)
    have h2 := adaptedMass_measurable (shiftFiltration (flowFiltration N) sL)
      (mfCoeff_adapted hN F sL ℓ hg r) (mfCoeff_continuous hN hF sL ℓ hg r) hv₀m xx
    have h3 : Measurable[shiftFiltration (flowFiltration N) sL xx] c₀ :=
      hc₀m.mono ((shiftFiltration (flowFiltration N) sL).mono (zero_le (a := xx))) le_rfl
    exact continuous_sumVec.measurable.comp (h1.prodMk
      (continuous_sumVec.measurable.comp (h3.prodMk h2)))
  have hΦcont : Continuous (gTilted (N := N) (r := r) (M := sectorCard N r) K wt) :=
    (gTilted_contDiff hwcd).continuous
  have hpt0 : ∀ (xx : ℝ≥0) ω, 0 ≤ gTilted K wt ((xx : ℝ), gState F sL ℓ g r c₀ v₀ xx ω) := by
    intro xx ω
    rw [gState, gTilted_sumVec]
    exact mul_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun q _ => mul_nonneg (hw0 _ _ _)
      (mfMass_mem_unit hN hF sL ℓ hg r hv₀ xx ω q).1)
  have hptbd : ∀ (xx : ℝ≥0) ω, gTilted K wt ((xx : ℝ), gState F sL ℓ g r c₀ v₀ xx ω) ≤
      sectorCard N r * Wm := by
    intro xx ω
    rw [gState, gTilted_sumVec]
    have hexp1 : Real.exp (-(K * xx)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by have := NNReal.coe_nonneg xx; nlinarith)
    have hs0 : 0 ≤ ∑ q, wt q (flowLam F (sL + xx) ω) (c₀ ω) * mfMass F sL ℓ g r v₀ xx ω q :=
      Finset.sum_nonneg fun q _ => mul_nonneg (hw0 _ _ _)
        (mfMass_mem_unit hN hF sL ℓ hg r hv₀ xx ω q).1
    have hs1 : ∑ q, wt q (flowLam F (sL + xx) ω) (c₀ ω) * mfMass F sL ℓ g r v₀ xx ω q ≤
        sectorCard N r * Wm := by
      calc _ ≤ ∑ _q : Fin (sectorCard N r), Wm := Finset.sum_le_sum fun q _ => by
            have hm := mfMass_mem_unit hN hF sL ℓ hg r hv₀ xx ω q
            calc _ ≤ Wm * 1 := mul_le_mul (hwM _ _ _) hm.2 hm.1 hWm0
              _ = Wm := mul_one _
        _ = _ := by simp
    calc _ ≤ 1 * ((sectorCard N r : ℝ) * Wm) := mul_le_mul hexp1 hs1 hs0 zero_le_one
      _ = _ := one_mul _
  have hXa : ∀ xx, StronglyMeasurable[shiftFiltration (flowFiltration N) sL xx]
      (fun ω => gTilted K wt ((xx : ℝ), gState F sL ℓ g r c₀ v₀ xx ω)) := fun xx =>
    (hΦcont.measurable.comp (measurable_const.prodMk (hYa xx))).stronglyMeasurable
  have hXc : ∀ ω, Continuous fun xx : ℝ≥0 =>
      gTilted K wt ((xx : ℝ), gState F sL ℓ g r c₀ v₀ xx ω) := fun ω =>
    hΦcont.comp (NNReal.continuous_coe.prodMk (hYc ω))
  have hprog := StronglyAdapted.isStronglyProgressive_of_continuous hXa hXc
  have hm := hprog.stronglyMeasurable_stoppedProcess
    (isStoppingTime_flowStop hF sL ℓ E r₀ c₁ C₁ g) T
  have hX0 : ∀ ω, 0 ≤ X ω := fun ω => by simp only [hXdef, stoppedProcess]; exact hpt0 _ ω
  have hXint : Integrable X μ :=
    Integrable.of_bound hm.aestronglyMeasurable ((sectorCard N r) * Wm)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hX0 ω)]
        simp only [hXdef, stoppedProcess]; exact hptbd _ ω)
  -- Markov
  set θ := Real.exp (-(K * (u - s))) * w * e with hθ
  have hθpos : 0 < θ := by positivity
  have hmk := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall hX0) hXint θ
  have hmeas : μ {ω | θ ≤ X ω} ≤ ENNReal.ofReal (sectorCard N r * δ₀ / θ) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [le_div_iff₀ hθpos]
    have : θ * μ.real {ω | θ ≤ X ω} ≤ sectorCard N r * δ₀ := hmk.trans hXint_le
    rw [measureReal_def] at this
    linarith
  -- containment
  have hsub : {ω | (∀ k : Fin N, 0 < ξ₀ k → |flowEigenvalue F a ω s k - E| ≤ r₀ / 16) ∧
        ∃ Φ : ℝ → Occ N → ℝ, IsMomentFlowSolution (shortFlowRate F a ω ℓ) r s u Φ ∧
          (∀ ζ ∈ sector N r, Φ s ζ = if (r : ℝ) * R < (occDist ξ₀ ζ : ℝ) then 1 else 0) ∧
          e < Φ u ξ₀} ⊆ Gᶜ ∪ {ω | θ ≤ X ω} := by
    rintro ω ⟨hbulk, Φ, hΦ, hΦ0, hΦu⟩
    by_cases hωG : ω ∈ G
    swap
    · exact Or.inl hωG
    right
    obtain ⟨hH, hcl, hfarW, hwW⟩ := hG ω hωG hbulk
    have hlamS : flowLam F sL ω = flowEigenvalue F a ω s := flowLam_eq_eig F a hH has.le
    have hocc : ∀ m, 0 < ξ₀ (x m) := by
      intro m
      rw [← mem_labs.1 hx, ← card_filter_eq_occOf]
      exact Finset.card_pos.2 ⟨m, by simp⟩
    have hc0 : c₀ ω = fun m => flowEigenvalue F a ω s (x m) := by
      funext m
      rw [hc₀def]; simp only [hlamS]
      exact clampC_eq (hbulk _ (hocc m))
    have hlam_t : ∀ xx : ℝ≥0, flowLam F (sL + xx) ω = flowEigenvalue F a ω (s + xx) := by
      intro xx
      rw [flowLam_add_eq_eig F a hH, NNReal.coe_add, hsL]
      congr 1; ring
    have hωA : ω ∈ A := by
      rw [hAdef]
      intro q hq
      rw [hwt]
      dsimp only
      rw [hlam_t 0, hc0]
      simp only [NNReal.coe_zero, add_zero]
      exact hfarW (σe q) (sectorEnum_mem r q) hq
    have hρT : ¬ ρ ω ≤ T := by
      have hiff := hitTime_le_iff (X := fun xx ω => flowLam F (sL + xx) ω)
        (K := stopSet N ℓ E r₀ c₁ C₁ g) (ω := ω)
        ((flowLam_continuous hF ω).comp (continuous_const.add continuous_id))
        ((isClosed_failSet N ℓ E r₀ c₁ C₁).union (isClosed_gapSet N g)) T
      rw [hρdef, flowStop, hiff]
      rintro ⟨xx, hxT, hxs⟩
      simp only [stopSet, Set.mem_union] at hxs
      have hxT' : (xx : ℝ) ≤ u - s := by rw [← hT]; exact_mod_cast hxT
      have hσ : s + (xx : ℝ) ∈ Icc s u := ⟨by linarith [xx.2], by linarith⟩
      obtain ⟨h1, h2, h3⟩ := hcl _ hσ
      simp only [hlam_t xx] at hxs
      rcases hxs with hxs | hxs
      · exact not_mem_failSet_of_clauses hℓ hc₁ hC₁ hN h1 h2 hxs
      · obtain ⟨i, j, hij, hle⟩ := hxs
        exact absurd hle (not_le.mpr (h3 i j hij))
    have hTρ : (T : WithTop ℝ≥0) ≤ ρ ω := (lt_of_not_ge hρT).le
    have hXω : X ω = gTilted K wt ((T : ℝ), gState F sL ℓ g r c₀ v₀ T ω) := by
      simp only [hXdef, stoppedProcess, min_eq_left hTρ]
      rfl
    set Lc := mfCoeff F sL ℓ g r with hLc
    have hsol := adaptedMass_solution (mfCoeff_continuous hN hF sL ℓ hg r) v₀ ω
      (T := u - s) (by linarith)
    have hsh := forwardMass_shift_to hsol s
    have hsu' : s + (u - s) = u := by ring
    rw [hsu'] at hsh
    have hmf := isMomentFlowSolution_of_forwardMass
      (c := fun σ => cfgRate N (flowLam F (sL + Real.toNNReal (σ - s)) ω) ℓ g) hsh
    have hmf' : IsMomentFlowSolution (shortFlowRate F a ω ℓ) r s u
        (fun σ => cfgExt r (adaptedMass Lc v₀ (σ - s) ω)) := by
      refine hmf.congr_rate fun σ hσ i j hij => ?_
      have hσs : ((Real.toNNReal (σ - s) : ℝ≥0) : ℝ) = σ - s :=
        Real.coe_toNNReal _ (by linarith [hσ.1])
      have hl : flowLam F (sL + Real.toNNReal (σ - s)) ω = flowEigenvalue F a ω σ := by
        rw [hlam_t, hσs]; congr 1; ring
      show cfgRate N (flowLam F (sL + Real.toNNReal (σ - s)) ω) ℓ g i j = _
      rw [hl, shortFlowRate_eq_cfgRate F a ω ℓ σ hij]
      have hgap := (hcl σ ⟨hσ.1.le, hσ.2.le⟩).2.2
      rw [cfgRate_eq_zero_gap hg.le fun i j h => (hgap i j h).le]
    have h0 : ∀ ζ ∈ sector N r, Φ s ζ = cfgExt r (adaptedMass Lc v₀ (s - s) ω) ζ := by
      intro ζ hζ
      rw [sub_self, hΦ0 ζ hζ, cfgExt_of_mem _ hζ]
      have : adaptedMass Lc v₀ 0 ω = v₀ ω := hsol.1
      rw [this]
      rw [hv₀def]
      simp only [Set.indicator_of_mem hωA, sectorEnum_index hζ, hσe, hfIdef, hfarD]
    have heq := hΦ.eq_of_initial_eq (fun x _ i j _ => shortFlowRate_nonneg F a ω ℓ x i j) hmf'
      h0 u ⟨hsu, le_rfl⟩ ξ₀ hξ₀
    have hΦval : Φ u ξ₀ = mfMass F sL ℓ g r v₀ T ω (sectorIndex hξ₀) := by
      rw [heq, cfgExt_of_mem _ hξ₀]
      simp only [mfMass, hT, hLc]
    have hWξ : w ≤ wt (sectorIndex hξ₀) (flowLam F (sL + T) ω) (c₀ ω) := by
      rw [hwt]
      dsimp only
      rw [hσe, sectorEnum_index hξ₀, hlam_t T, hT, hc0]
      have : s + (u - s) = u := by ring
      rw [this]; exact hwW
    show θ ≤ X ω
    rw [hXω, gState, gTilted_sumVec]
    have hterm : wt (sectorIndex hξ₀) (flowLam F (sL + T) ω) (c₀ ω) *
        mfMass F sL ℓ g r v₀ T ω (sectorIndex hξ₀) ≤
        ∑ q, wt q (flowLam F (sL + T) ω) (c₀ ω) * mfMass F sL ℓ g r v₀ T ω q :=
      Finset.single_le_sum (f := fun q => wt q (flowLam F (sL + T) ω) (c₀ ω) *
          mfMass F sL ℓ g r v₀ T ω q)
        (fun q _ => mul_nonneg (hw0 _ _ _)
          (mfMass_mem_unit hN hF sL ℓ hg r hv₀ T ω q).1) (Finset.mem_univ _)
    rw [← hΦval] at hterm
    rw [hT]
    calc θ = Real.exp (-(K * (u - s))) * (w * e) := by rw [hθ]; ring
      _ ≤ Real.exp (-(K * (u - s))) *
          (wt (sectorIndex hξ₀) (flowLam F (sL + T) ω) (c₀ ω) * Φ u ξ₀) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
          exact mul_le_mul hWξ hΦu.le he.le (hw.le.trans hWξ)
      _ ≤ _ := mul_le_mul_of_nonneg_left hterm (Real.exp_pos _).le
  calc μ _ ≤ μ (Gᶜ ∪ {ω | θ ≤ X ω}) := measure_mono hsub
    _ ≤ μ Gᶜ + μ {ω | θ ≤ X ω} := measure_union_le _ _
    _ ≤ μ Gᶜ + ENNReal.ofReal (sectorCard N r * δ₀ / θ) := add_le_add le_rfl hmeas

end BlockBand.Palm.MomentFlow
