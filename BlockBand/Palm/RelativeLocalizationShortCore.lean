module

public import BlockBand.Palm.RelativeLocalizationClauses

/-!
# Relative localization: the short-flow cores (row and column), one deterministic `(s,u,k)`

* `row_core` : the outer `flowLaw N a`-measure of `{centre in the bulk ∧ some solution of the
  short-generator mass equation from `1{|j-k| > R}` has `v_u(k) > th`}` is at most the measure
  of the failure of `goodClauses` on `[a, cT]` plus `e^{K(u-s)} N e^{-ν min(R/(CN) - h - d, R_c)}
  / (th e^{-2νD₀})`;
* `col_core` : the same for `Σ_{|j-k|>R} v_u(j)` from `δ_k`, with the bound
  `e^{K(u-s)} / (th e^{ν min(R/(CN) - h - 2D₀ - d, R_c)})`.

Moving centre: `rowCentre = clamp_{[E ± r₀/16]} λ_k(s)` (start-measurable; equal to `λ_k(s)` on
the bulk event). Proof: `gen_expectation_avoid` for every gap level `1/(n+1)`, Markov, and
`tendsto_gapEvent`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Palm.RelativeLocalization

open MeasureTheory ProbabilityTheory Set Filter Topology Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open scoped NNReal ENNReal

variable {N : ℕ}

/-- Clamped moving centre. -/
def clampCentre (E r : ℝ) (x : ℝ) : ℝ := max (E - r) (min (E + r) x)

theorem clampCentre_eq {E r x : ℝ} (hx : |x - E| ≤ r) : clampCentre E r x = x := by
  rw [abs_le] at hx
  unfold clampCentre
  rw [min_eq_right (by linarith), max_eq_right (by linarith)]

theorem abs_clampCentre_le {E r : ℝ} (hr : 0 ≤ r) (x : ℝ) : |clampCentre E r x - E| ≤ r := by
  unfold clampCentre
  rw [abs_le]; constructor
  · have := le_max_left (E - r) (min (E + r) x); linarith
  · have h1 : min (E + r) x ≤ E + r := min_le_left _ _
    have : max (E - r) (min (E + r) x) ≤ E + r := max_le (by linarith) h1
    linarith

theorem continuous_clampCentre (E r : ℝ) : Continuous (clampCentre E r) := by
  unfold clampCentre; fun_prop

/-- The row weight constants. -/
def rowKappa (N ℓ : ℕ) (ν d Rc c₁ C₁ : ℝ) : ℝ :=
  2 * ℓ * (|ν| * (weightConst / Rc + weightConst / d) + ν ^ 2 * weightConst ^ 2) *
      Real.exp (|ν| * weightConst * (2 * C₁ * ℓ / N)) / N +
    2 * (|ν| * weightConst) * (1 + Real.log N) / (c₁ / 2) +
    (|ν| * (weightConst / Rc + weightConst / d) + ν ^ 2 * weightConst ^ 2) / (2 * N)

theorem rowKappa_neg (N ℓ : ℕ) (ν d Rc c₁ C₁ : ℝ) :
    rowKappa N ℓ (-ν) d Rc c₁ C₁ = rowKappa N ℓ ν d Rc c₁ C₁ := by
  simp [rowKappa, abs_neg]

end BlockBand.Palm.RelativeLocalization

namespace BlockBand.Palm.RelativeLocalization

open MeasureTheory ProbabilityTheory Set Filter Topology Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open scoped NNReal ENNReal

variable {N : ℕ}

theorem flowLam_shift_eq (F : Matrix (Fin N) (Fin N) ℂ) {a s : ℝ} (has : a ≤ s)
    {ω : FlowSample N} (hω : ω.1.IsHermitian) (r : ℝ≥0) :
    flowLam F (Real.toNNReal (s - a) + r) ω = flowEigenvalue F a ω (s + r) := by
  rw [flowLam_eq_flowEigenvalue F a hω]
  funext k
  congr 1
  push_cast
  rw [Real.coe_toNNReal _ (by linarith)]
  ring

/-- Row data `1_A 1{R < |j-k|}`. -/
def rowData (A : Set (FlowSample N)) (R : ℝ) (k : Fin N) (ω : FlowSample N) : Fin N → ℝ :=
  fun j => A.indicator (fun _ => (1 : ℝ)) ω * (if R < (labelDist k j : ℝ) then 1 else 0)

theorem rowData_mem (A : Set (FlowSample N)) (R : ℝ) (k : Fin N) (ω : FlowSample N) (j : Fin N) :
    0 ≤ rowData A R k ω j ∧ rowData A R k ω j ≤ 1 := by
  unfold rowData
  by_cases hω : ω ∈ A <;> by_cases hj : R < (labelDist k j : ℝ) <;> simp [hω, hj]

end BlockBand.Palm.RelativeLocalization

namespace BlockBand.Palm.RelativeLocalization

open MeasureTheory ProbabilityTheory Set Filter Topology Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open scoped NNReal ENNReal

variable {N : ℕ}

/-- Row centre and far-label event (measurable at the start). -/
def rowCentre (F : Matrix (Fin N) (Fin N) ℂ) (s' : ℝ≥0) (E r₀ : ℝ) (k : Fin N)
    (ω : FlowSample N) : ℝ :=
  clampCentre E (r₀ / 16) (flowLam F s' ω k)

def rowA (F : Matrix (Fin N) (Fin N) ℂ) (s' : ℝ≥0) (E r₀ R δ : ℝ) (k : Fin N) :
    Set (FlowSample N) :=
  {ω | ∀ j : Fin N, R < (labelDist k j : ℝ) → δ ≤ |flowLam F s' ω j - rowCentre F s' E r₀ k ω|}

theorem rowCentre_measurable (F : Matrix (Fin N) (Fin N) ℂ) (s' : ℝ≥0) (E r₀ : ℝ) (k : Fin N) :
    Measurable[flowFiltration N s'] (rowCentre F s' E r₀ k) :=
  (continuous_clampCentre E _).measurable.comp ((measurable_pi_apply k).comp (flowLam_adapted F s'))

theorem rowA_measurable (F : Matrix (Fin N) (Fin N) ℂ) (s' : ℝ≥0) (E r₀ R δ : ℝ) (k : Fin N) :
    MeasurableSet[flowFiltration N s'] (rowA F s' E r₀ R δ k) := by
  have : rowA F s' E r₀ R δ k = ⋂ j : Fin N, {ω | R < (labelDist k j : ℝ) →
      δ ≤ |flowLam F s' ω j - rowCentre F s' E r₀ k ω|} := by
    ext ω; simp [rowA]
  rw [this]
  refine MeasurableSet.iInter fun j => ?_
  by_cases hj : R < (labelDist k j : ℝ)
  · simp only [hj, true_implies]
    have hm : Measurable[flowFiltration N s']
        (fun ω => |flowLam F s' ω j - rowCentre F s' E r₀ k ω|) :=
      continuous_abs.measurable.comp (((measurable_pi_apply j).comp (flowLam_adapted F s')).sub
        (rowCentre_measurable F s' E r₀ k))
    exact hm measurableSet_Ici
  · simp only [hj, false_implies, Set.ofPred_true]
    exact @MeasurableSet.univ _ (flowFiltration N s')

theorem rowData_measurable {A : Set (FlowSample N)} {s' : ℝ≥0}
    (hA : MeasurableSet[flowFiltration N s'] A) (R : ℝ) (k : Fin N) :
    Measurable[flowFiltration N s'] (rowData A R k) := by
  refine @measurable_pi_iff (FlowSample N) (Fin N) (fun _ => ℝ) (flowFiltration N s') _ _ |>.mpr
    fun j => ?_
  exact (measurable_const.indicator hA).mul_const _

end BlockBand.Palm.RelativeLocalization

namespace BlockBand.Palm.RelativeLocalization

open MeasureTheory ProbabilityTheory Set Filter Topology Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open scoped NNReal ENNReal

variable {N : ℕ}

/-- **Row core** (one deterministic `(s, u, k)`; clauses as the good set). -/
theorem row_core (hIto : SemimartingaleItoFormula (N + N)) (hStop : StoppedSemimartingale 1)
    (hDBM : DysonBrownianMotion N) {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    {a cT : ℝ} (ha : 0 < a) {E r₀ : ℝ} (hr₀ : 0 < r₀) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    {c₁ C₁ C b₀ h D₀ : ℝ} (hc₁ : 0 < c₁) (hC₁ : 0 < C₁) (hC : 0 < C)
    {s u : ℝ} (has : a ≤ s) (hsu : s ≤ u) (hucT : u ≤ cT) (k : Fin N) {R : ℝ}
    {ν d Rc K th : ℝ} (hν : 0 ≤ ν) (hd : 0 < d) (hRc : 0 < Rc) (hρ : d + 2 * Rc ≤ r₀ / 32)
    (hK0 : 0 ≤ K) (hK : rowKappa N ℓ ν d Rc c₁ C₁ ≤ K) (hth : 0 < th) :
    flowLaw N a {ω | |flowEigenvalue F a ω s k - E| ≤ r₀ / 16 ∧
        ∃ v, ForwardMassSolution (shortGenerator F a ω ℓ) s u
          (fun j => if R < (labelDist k j : ℝ) then 1 else 0) v ∧ th < v u k} ≤
      flowLaw N a {ω | ¬ ∀ σ ∈ Set.Icc a cT, goodClauses F a ω E r₀ c₁ C₁ C b₀ ℓ h D₀ σ} +
      ENNReal.ofReal (Real.exp (K * (u - s)) *
          (N * Real.exp (-(ν * min (R / (C * N) - h - d) Rc))) /
        (th * Real.exp (-(ν * (2 * D₀))))) := by
  classical
  set μ := flowLaw N a
  set s' := Real.toNNReal (s - a) with hs'
  set T := Real.toNNReal (u - s) with hT
  set T' := Real.toNNReal (cT - a) with hT'
  have hTr : (T : ℝ) = u - s := Real.coe_toNNReal _ (by linarith)
  set δ := R / (C * N) - h with hδ
  set cc := rowCentre F s' E r₀ k with hcc
  set A := rowA F s' E r₀ R δ k with hA
  set v₀ := rowData A R k with hv₀
  set φ := rlPhi ν 0 d Rc with hφ
  set G : ℝ := 2 * C₁ * ℓ / N with hG
  set IM := (N : ℝ) * Real.exp (-(ν * min (δ - d) Rc)) with hIM
  set g : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hgdef
  have hgpos : ∀ n, 0 < g n := fun n => by simp only [hgdef]; positivity
  set Gen : ℕ → (Fin N → ℝ) → Fin N → Fin N → ℝ := fun n lam => truncShortGen N lam ℓ (g n)
  set Kh : ℕ → Set (ℝ × (Fin N → ℝ)) := fun n => centreSet N ℓ E r₀ c₁ C₁ (g n)
  set X : ℕ → FlowSample N → ℝ := fun n =>
    (avoidSet F s' cc (Kh n) T).indicator (goodMass (Gen n) F s' v₀ cc φ T)
  have hAm := rowA_measurable F s' E r₀ R δ k
  have hv₀m : Measurable[flowFiltration N s'] v₀ := rowData_measurable hAm R k
  have hv₀b : ∀ ω j, 0 ≤ v₀ ω j ∧ v₀ ω j ≤ 1 := rowData_mem A R k
  have hccm : Measurable[flowFiltration N s'] cc := rowCentre_measurable F s' E r₀ k
  have hGc : ∀ n, Continuous (Gen n) := fun n => truncShortGen_continuous ℓ (hgpos n)
  have hGs : ∀ n, IsSubGenField (Gen n) := fun n => truncShortGen_isSubGenField ℓ (g n)
  have hφ0 : ∀ z, 0 ≤ φ z := fun z => (rlPhi_pos z).le
  have hφ1 : ∀ z, φ z ≤ 1 := rlPhi_le_one hν hRc
  -- the per-start bound
  have hexp : ∀ n, Real.exp (-(K * T)) * ∫ ω, X n ω ∂μ ≤
      ∫ ω, goodMass (Gen n) F s' v₀ cc φ 0 ω ∂μ := by
    intro n
    exact gen_expectation_avoid hIto hStop hDBM hF a s' (hGc n) (hGs n) hv₀m hv₀b hccm
      (rlPhi_hasDerivAt hd hRc) (rlPhi1_hasDerivAt hd hRc) (rlPhi_contDiff hd hRc) hφ0 hφ1
      (abs_rlPhi1_le_abs hd hRc) (mul_nonneg (abs_nonneg _) weightConst_pos.le)
      (abs_rlPhi2_le_abs hd hRc)
      (add_nonneg (mul_nonneg (abs_nonneg _) (add_nonneg (div_nonneg weightConst_pos.le hRc.le)
        (div_nonneg weightConst_pos.le hd.le))) (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
      (Real.exp_pos _).le
      (fun x z hxz => (rlPhi_le_exp_mul_abs hd hRc x z).trans
        (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left hxz (mul_nonneg (abs_nonneg _) weightConst_pos.le)))
          (rlPhi_pos x).le))
      (half_pos hc₁) hK0 hK (isClosed_centreSet N ℓ E r₀ c₁ C₁ (g n))
      (fun c lam hcl => hcond_centreSet (Gen := Gen n)
        (fun lam hgap v hv k => truncShortGen_dom (hgpos n).le lam hgap v hv k) hRc hρ c lam hcl) T
  -- the initial mass
  have hinit : ∀ n ω, goodMass (Gen n) F s' v₀ cc φ 0 ω ≤ IM := by
    intro n ω
    have h0 : genMass (Gen n) F s' v₀ 0 ω = v₀ ω :=
      (adaptedMass_solution (genCoeff_continuous (hGc n) hF s') v₀ ω le_rfl).1
    simp only [goodMass, h0, add_zero]
    by_cases hωA : ω ∈ A
    · have := initial_mass_le (ν := ν) (E := 0) (d := d) (R := Rc) (δ := δ) hν hRc
        (fun j => flowLam F s' ω j - cc ω) (fun j => R < (labelDist k j : ℝ))
        (fun j hj => by simpa using hωA j hj)
      simpa [hv₀, rowData, hωA] using this
    · simp only [hv₀, rowData, Set.indicator_of_notMem hωA, zero_mul, mul_zero,
        Finset.sum_const_zero]
      positivity
  have hbdd : ∀ n, ∀ u' ω, 0 ≤ goodMass (Gen n) F s' v₀ cc φ u' ω ∧
      goodMass (Gen n) F s' v₀ cc φ u' ω ≤ 1 * N := fun n =>
    goodMass_le (hGc n) (hGs n) hF s' hv₀b cc hφ0 hφ1
  have hXm : ∀ n, Measurable (X n) := fun n =>
    (goodMass_measurable (hGc n) hF s' hv₀m hccm (rlPhi_contDiff hd hRc).continuous T).indicator
      (measurableSet_avoidSet hF s' hccm (isClosed_centreSet N ℓ E r₀ c₁ C₁ (g n)) T)
  have hX0 : ∀ n ω, 0 ≤ X n ω := fun n ω => by
    simp only [X, Set.indicator]; split_ifs
    · exact (hbdd n T ω).1
    · exact le_rfl
  have hXi : ∀ n, Integrable (X n) μ := fun n =>
    Integrable.of_bound (hXm n).aestronglyMeasurable (1 * N) (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hX0 n ω)]
      simp only [X, Set.indicator]; split_ifs
      · exact (hbdd n T ω).2
      · positivity)
  have hXe : ∀ n, ∫ ω, X n ω ∂μ ≤ Real.exp (K * (u - s)) * IM := by
    intro n
    have h1 := hexp n
    have h2 : ∫ ω, goodMass (Gen n) F s' v₀ cc φ 0 ω ∂μ ≤ IM := by
      calc _ ≤ ∫ _ω, IM ∂μ := integral_mono_of_nonneg (Eventually.of_forall fun ω => (hbdd n 0 ω).1)
            (integrable_const _) (Eventually.of_forall (hinit n))
        _ = IM := by simp
    rw [hTr] at h1
    have he : Real.exp (-(K * (u - s))) * Real.exp (K * (u - s)) = 1 := by
      rw [← Real.exp_add]; simp
    calc ∫ ω, X n ω ∂μ = Real.exp (K * (u - s)) * (Real.exp (-(K * (u - s))) * ∫ ω, X n ω ∂μ) := by
          rw [← mul_assoc, mul_comm (Real.exp (K * (u - s))), he, one_mul]
      _ ≤ Real.exp (K * (u - s)) * IM :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (Real.exp_pos _).le
  -- the inclusion
  set Nul : Set (FlowSample N) := {ω | ¬ ω.1.IsHermitian}
  have hNul : μ Nul = 0 := ae_iff.mp (ae_fst_isHermitian (N := N) a)
  refine markov_limit μ _ _ Nul (fun n => gapEvent F T' (g n)) X
    (mul_pos hth (Real.exp_pos _)) hNul (tendsto_gapEvent hDBM hF ha T') hXm hX0 hXi hXe
    (fun n ω hω => ?_)
  obtain ⟨hcen, v, hv, hvk⟩ := hω
  by_contra hcon
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not, not_lt, Nul] at hcon
  obtain ⟨⟨⟨hgood, hH⟩, hgap⟩, hXle⟩ := hcon
  have hN : 0 < N := Fin.pos k
  -- eigenvalues along the shifted flow
  have hlam : ∀ r : ℝ≥0, flowLam F (s' + r) ω = flowEigenvalue F a ω (s + r) :=
    flowLam_shift_eq F has hH
  have hlam0 : flowLam F s' ω = flowEigenvalue F a ω s := by simpa using hlam 0
  have hcceq : rowCentre F s' E r₀ k ω = flowEigenvalue F a ω s k := by
    simp only [rowCentre, hlam0]; exact clampCentre_eq hcen
  have hgs : goodClauses F a ω E r₀ c₁ C₁ C b₀ ℓ h D₀ s := hgood s ⟨has, hsu.trans hucT⟩
  have hgu : goodClauses F a ω E r₀ c₁ C₁ C b₀ ℓ h D₀ u := hgood u ⟨has.trans hsu, hucT⟩
  -- the far event holds
  have hωA : ω ∈ A := by
    intro j hj
    show δ ≤ |flowLam F s' ω j - rowCentre F s' E r₀ k ω|
    rw [hcceq, hlam0]
    exact far_from_label (flowEigenvalue F a ω s) (flowEigenvalue_monotone' hF a hH s) hC
      hgs.2.2.1 hj
  -- gaps along the window
  have hgaps : ∀ r : ℝ≥0, r ≤ T' → ∀ i j : Fin N, i ≠ j →
      g n < |flowLam F r ω i - flowLam F r ω j| := by
    intro r hr i j hij
    by_contra hlt; push Not at hlt
    exact hgap ⟨r, hr, i, j, hij, hlt⟩
  -- avoidance
  have hav : ω ∈ avoidSet F s' cc (Kh n) T := by
    intro r hr hK'
    simp only [cenLam, Kh, centreSet, Set.mem_ofPred_eq, Set.mem_union] at hK'
    have hrT : (s + r : ℝ) ≤ cT := by
      have : (r : ℝ) ≤ u - s := by rw [← hTr]; exact_mod_cast hr
      linarith
    rcases hK' with (hf | hgp) | hcE
    · rw [hlam r] at hf
      exact clauses_not_fail hℓ hc₁ hC₁ hN (hgood (s + r) ⟨by
        have := NNReal.coe_nonneg r; linarith, hrT⟩) hf
    · obtain ⟨i, j, hij, hle⟩ := hgp
      have hr' : s' + r ≤ T' := by
        rw [hs', hT', ← NNReal.coe_le_coe]; push_cast
        rw [Real.coe_toNNReal _ (by linarith), Real.coe_toNNReal _ (by linarith)]; linarith
      have := hgaps (s' + r) hr' i j hij
      have := hgpos n
      linarith
    · have := abs_clampCentre_le (E := E) (by positivity : 0 ≤ r₀ / 16) (flowLam F s' ω k)
      simp only [hcc, rowCentre] at hcE
      linarith
  -- identification of the arbitrary solution
  have hdata : v₀ ω = fun j => if R < (labelDist k j : ℝ) then 1 else 0 := by
    funext j; simp [hv₀, rowData, Set.indicator_of_mem hωA]
  have hid : genMass (Gen n) F s' v₀ T ω = v u := by
    have := genMass_eq_solution (hGc n) hF has (ω := ω) (L := shortGenerator F a ω ℓ)
      (v₀ := v₀) (fun σ hσ => by
        have hσa : a ≤ σ := has.trans hσ.1.le
        refine shortGenerator_eq_trunc hσa hH (hgpos n).le fun i j hij => (hgaps _ ?_ i j hij).le
        rw [hT', ← NNReal.coe_le_coe, Real.coe_toNNReal _ (by linarith),
          Real.coe_toNNReal _ (by linarith)]
        linarith [hσ.2])
      (by rw [hdata]; exact hv) (r := u - s) ⟨by linarith, le_rfl⟩
    rw [show u - s + s = u by ring] at this
    exact this
  -- terminal bound
  have hvnn : ∀ j, 0 ≤ genMass (Gen n) F s' v₀ T ω j := fun j =>
    (genMass_mem_unit (hGc n) (hGs n) hF s' hv₀b T ω j).1
  have hterm := terminal_le (ν := ν) (E := 0) (d := d) (R := Rc) hν hd hRc
    (fun j => flowLam F (s' + T) ω j - cc ω) (genMass (Gen n) F s' v₀ T ω) hvnn k
  have hdisp : |flowLam F (s' + T) ω k - cc ω - 0| ≤ 2 * D₀ := by
    show |flowLam F (s' + T) ω k - rowCentre F s' E r₀ k ω - 0| ≤ 2 * D₀
    rw [hlam T, hcceq, sub_zero, hTr, show s + (u - s) = u by ring]
    have h1 := disp_le hF hH hgu k
    have h2 := disp_le hF hH hgs k
    calc |flowEigenvalue F a ω u k - flowEigenvalue F a ω s k|
        ≤ |flowEigenvalue F a ω u k - flowEigenvalue F a ω a k| +
          |flowEigenvalue F a ω a k - flowEigenvalue F a ω s k| := abs_sub_le _ _ _
      _ ≤ D₀ + D₀ := add_le_add h1 (by rw [abs_sub_comm]; exact h2)
      _ = 2 * D₀ := by ring
  have hXω : X n ω = goodMass (Gen n) F s' v₀ cc φ T ω := by
    simp only [X, Set.indicator_of_mem hav]
  have hgm : goodMass (Gen n) F s' v₀ cc φ T ω =
      ∑ j, rlPhi ν 0 d Rc (flowLam F (s' + T) ω j - cc ω) * genMass (Gen n) F s' v₀ T ω j := rfl
  rw [congrFun hid k] at hterm
  have hstep : v u k ≤ Real.exp (ν * (2 * D₀)) * X n ω := by
    rw [hXω, hgm]
    refine hterm.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hdisp hν)) ?_)
    exact Finset.sum_nonneg fun j _ => mul_nonneg (rlPhi_pos _).le (hvnn j)
  have : th * Real.exp (-(ν * (2 * D₀))) < X n ω := by
    have he : Real.exp (-(ν * (2 * D₀))) * Real.exp (ν * (2 * D₀)) = 1 := by
      rw [← Real.exp_add]; simp
    have hpos := Real.exp_pos (-(ν * (2 * D₀)))
    calc th * Real.exp (-(ν * (2 * D₀))) < v u k * Real.exp (-(ν * (2 * D₀))) :=
          mul_lt_mul_of_pos_right hvk hpos
      _ ≤ Real.exp (ν * (2 * D₀)) * X n ω * Real.exp (-(ν * (2 * D₀))) :=
          mul_le_mul_of_nonneg_right hstep hpos.le
      _ = X n ω := by rw [mul_comm (Real.exp _) (X n ω), mul_assoc, mul_comm (Real.exp _), he,
            mul_one]
  linarith

end BlockBand.Palm.RelativeLocalization

namespace BlockBand.Palm.RelativeLocalization
open MeasureTheory ProbabilityTheory Set Filter Topology Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open scoped NNReal ENNReal
variable {N : ℕ}

/-- **Column core** (increasing weight `rlPhi (-ν)`, data `δ_k`). -/
theorem col_core (hIto : SemimartingaleItoFormula (N + N)) (hStop : StoppedSemimartingale 1)
    (hDBM : DysonBrownianMotion N) {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian)
    {a cT : ℝ} (ha : 0 < a) {E r₀ : ℝ} (hr₀ : 0 < r₀) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    {c₁ C₁ C b₀ h D₀ : ℝ} (hc₁ : 0 < c₁) (hC₁ : 0 < C₁) (hC : 0 < C)
    {s u : ℝ} (has : a ≤ s) (hsu : s ≤ u) (hucT : u ≤ cT) (k : Fin N) {R : ℝ}
    {ν d Rc K th : ℝ} (hν : 0 ≤ ν) (hd : 0 < d) (hRc : 0 < Rc) (hρ : d + 2 * Rc ≤ r₀ / 32)
    (hK0 : 0 ≤ K) (hK : rowKappa N ℓ ν d Rc c₁ C₁ ≤ K) (hth : 0 < th) :
    flowLaw N a {ω | |flowEigenvalue F a ω s k - E| ≤ r₀ / 16 ∧
        ∃ v, ForwardMassSolution (shortGenerator F a ω ℓ) s u
          (fun j => if j = k then 1 else 0) v ∧
          th < ∑ j : Fin N, (if R < (labelDist k j : ℝ) then 1 else 0) * v u j} ≤
      flowLaw N a {ω | ¬ ∀ σ ∈ Set.Icc a cT, goodClauses F a ω E r₀ c₁ C₁ C b₀ ℓ h D₀ σ} +
      ENNReal.ofReal (Real.exp (K * (u - s)) * 1 /
        (th * Real.exp (ν * min (R / (C * N) - h - 2 * D₀ - d) Rc))) := by
  classical
  set μ := flowLaw N a
  set s' := Real.toNNReal (s - a) with hs'
  set T := Real.toNNReal (u - s) with hT
  set T' := Real.toNNReal (cT - a) with hT'
  have hTr : (T : ℝ) = u - s := Real.coe_toNNReal _ (by linarith)
  set δ := R / (C * N) - h - 2 * D₀ with hδ
  set cc := rowCentre F s' E r₀ k with hcc
  set A := {ω : FlowSample N | |flowLam F s' ω k - E| ≤ r₀ / 16} with hA
  set v₀ : FlowSample N → Fin N → ℝ :=
    fun ω j => A.indicator (fun _ => (1 : ℝ)) ω * (if j = k then 1 else 0) with hv₀
  set φ := rlPhi (-ν) 0 d Rc with hφ
  set G : ℝ := 2 * C₁ * ℓ / N with hG
  set g : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hgdef
  have hgpos : ∀ n, 0 < g n := fun n => by simp only [hgdef]; positivity
  set Gen : ℕ → (Fin N → ℝ) → Fin N → Fin N → ℝ := fun n lam => truncShortGen N lam ℓ (g n)
  set Kh : ℕ → Set (ℝ × (Fin N → ℝ)) := fun n => centreSet N ℓ E r₀ c₁ C₁ (g n)
  set X : ℕ → FlowSample N → ℝ := fun n =>
    (avoidSet F s' cc (Kh n) T).indicator (goodMass (Gen n) F s' v₀ cc φ T)
  have hAm : MeasurableSet[flowFiltration N s'] A := by
    have hm : Measurable[flowFiltration N s'] (fun ω => |flowLam F s' ω k - E|) :=
      continuous_abs.measurable.comp (((measurable_pi_apply k).comp (flowLam_adapted F s')).sub
        measurable_const)
    exact hm measurableSet_Iic
  have hv₀m : Measurable[flowFiltration N s'] v₀ :=
    @measurable_pi_iff (FlowSample N) (Fin N) (fun _ => ℝ) (flowFiltration N s') _ _ |>.mpr
      fun j => (measurable_const.indicator hAm).mul_const _
  have hv₀b : ∀ ω j, 0 ≤ v₀ ω j ∧ v₀ ω j ≤ 1 := by
    intro ω j
    simp only [hv₀]
    by_cases hω : ω ∈ A <;> by_cases hj : j = k <;> simp [hω, hj]
  have hccm : Measurable[flowFiltration N s'] cc := rowCentre_measurable F s' E r₀ k
  have hGc : ∀ n, Continuous (Gen n) := fun n => truncShortGen_continuous ℓ (hgpos n)
  have hGs : ∀ n, IsSubGenField (Gen n) := fun n => truncShortGen_isSubGenField ℓ (g n)
  have hφ0 : ∀ z, 0 ≤ φ z := fun z => (rlPhi_pos z).le
  have hφ1 : ∀ z, φ z ≤ Real.exp (2 * ν * Rc) := rlPhi_neg_le hν hRc
  -- the per-start bound
  have hexp : ∀ n, Real.exp (-(K * T)) * ∫ ω, X n ω ∂μ ≤
      ∫ ω, goodMass (Gen n) F s' v₀ cc φ 0 ω ∂μ := by
    intro n
    exact gen_expectation_avoid hIto hStop hDBM hF a s' (hGc n) (hGs n) hv₀m hv₀b hccm
      (rlPhi_hasDerivAt hd hRc) (rlPhi1_hasDerivAt hd hRc) (rlPhi_contDiff hd hRc) hφ0 hφ1
      (abs_rlPhi1_le_abs hd hRc) (mul_nonneg (abs_nonneg _) weightConst_pos.le)
      (abs_rlPhi2_le_abs hd hRc)
      (add_nonneg (mul_nonneg (abs_nonneg _) (add_nonneg (div_nonneg weightConst_pos.le hRc.le)
        (div_nonneg weightConst_pos.le hd.le))) (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
      (Real.exp_pos _).le
      (fun x z hxz => (rlPhi_le_exp_mul_abs hd hRc x z).trans
        (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left hxz (mul_nonneg (abs_nonneg _) weightConst_pos.le)))
          (rlPhi_pos x).le))
      (half_pos hc₁) hK0 (by have := hK; rw [← rowKappa_neg] at this; exact this) (isClosed_centreSet N ℓ E r₀ c₁ C₁ (g n))
      (fun c lam hcl => hcond_centreSet (Gen := Gen n)
        (fun lam hgap v hv k => truncShortGen_dom (hgpos n).le lam hgap v hv k) hRc hρ c lam hcl) T
  -- the initial mass
  have hinit : ∀ n ω, goodMass (Gen n) F s' v₀ cc φ 0 ω ≤ 1 := by
    intro n ω
    have h0 : genMass (Gen n) F s' v₀ 0 ω = v₀ ω :=
      (adaptedMass_solution (genCoeff_continuous (hGc n) hF s') v₀ ω le_rfl).1
    simp only [goodMass, h0, add_zero]
    by_cases hωA : ω ∈ A
    · have hc : rowCentre F s' E r₀ k ω = flowLam F s' ω k := clampCentre_eq hωA
      simp only [hv₀, Set.indicator_of_mem hωA, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true, hcc, hc, sub_self]
      rw [hφ, rlPhi_at_centre hd hRc]
    · simp only [hv₀, Set.indicator_of_notMem hωA, zero_mul, mul_zero, Finset.sum_const_zero]
      norm_num
  have hbdd : ∀ n, ∀ u' ω, 0 ≤ goodMass (Gen n) F s' v₀ cc φ u' ω ∧
      goodMass (Gen n) F s' v₀ cc φ u' ω ≤ Real.exp (2 * ν * Rc) * N := fun n =>
    goodMass_le (hGc n) (hGs n) hF s' hv₀b cc hφ0 hφ1
  have hXm : ∀ n, Measurable (X n) := fun n =>
    (goodMass_measurable (hGc n) hF s' hv₀m hccm (rlPhi_contDiff (ν := -ν) hd hRc).continuous T).indicator
      (measurableSet_avoidSet hF s' hccm (isClosed_centreSet N ℓ E r₀ c₁ C₁ (g n)) T)
  have hX0 : ∀ n ω, 0 ≤ X n ω := fun n ω => by
    simp only [X, Set.indicator]; split_ifs
    · exact (hbdd n T ω).1
    · exact le_rfl
  have hXi : ∀ n, Integrable (X n) μ := fun n =>
    Integrable.of_bound (hXm n).aestronglyMeasurable (Real.exp (2 * ν * Rc) * N) (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hX0 n ω)]
      simp only [X, Set.indicator]; split_ifs
      · exact (hbdd n T ω).2
      · positivity)
  have hXe : ∀ n, ∫ ω, X n ω ∂μ ≤ Real.exp (K * (u - s)) * 1 := by
    intro n
    have h1 := hexp n
    have h2 : ∫ ω, goodMass (Gen n) F s' v₀ cc φ 0 ω ∂μ ≤ 1 := by
      calc _ ≤ ∫ _ω, (1 : ℝ) ∂μ := integral_mono_of_nonneg (Eventually.of_forall fun ω => (hbdd n 0 ω).1)
            (integrable_const _) (Eventually.of_forall (hinit n))
        _ = 1 := by simp
    rw [hTr] at h1
    have he : Real.exp (-(K * (u - s))) * Real.exp (K * (u - s)) = 1 := by
      rw [← Real.exp_add]; simp
    calc ∫ ω, X n ω ∂μ = Real.exp (K * (u - s)) * (Real.exp (-(K * (u - s))) * ∫ ω, X n ω ∂μ) := by
          rw [← mul_assoc, mul_comm (Real.exp (K * (u - s))), he, one_mul]
      _ ≤ Real.exp (K * (u - s)) * 1 :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (Real.exp_pos _).le
  -- the inclusion
  set Nul : Set (FlowSample N) := {ω | ¬ ω.1.IsHermitian}
  have hNul : μ Nul = 0 := ae_iff.mp (ae_fst_isHermitian (N := N) a)
  refine markov_limit μ _ _ Nul (fun n => gapEvent F T' (g n)) X
    (mul_pos hth (Real.exp_pos _)) hNul (tendsto_gapEvent hDBM hF ha T') hXm hX0 hXi hXe
    (fun n ω hω => ?_)
  obtain ⟨hcen, v, hv, hvk⟩ := hω
  by_contra hcon
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not, not_lt, Nul] at hcon
  obtain ⟨⟨⟨hgood, hH⟩, hgap⟩, hXle⟩ := hcon
  have hN : 0 < N := Fin.pos k
  -- eigenvalues along the shifted flow
  have hlam : ∀ r : ℝ≥0, flowLam F (s' + r) ω = flowEigenvalue F a ω (s + r) :=
    flowLam_shift_eq F has hH
  have hlam0 : flowLam F s' ω = flowEigenvalue F a ω s := by simpa using hlam 0
  have hcceq : rowCentre F s' E r₀ k ω = flowEigenvalue F a ω s k := by
    simp only [rowCentre, hlam0]; exact clampCentre_eq hcen
  have hgs : goodClauses F a ω E r₀ c₁ C₁ C b₀ ℓ h D₀ s := hgood s ⟨has, hsu.trans hucT⟩
  have hgu : goodClauses F a ω E r₀ c₁ C₁ C b₀ ℓ h D₀ u := hgood u ⟨has.trans hsu, hucT⟩
  -- gaps along the window
  have hgaps : ∀ r : ℝ≥0, r ≤ T' → ∀ i j : Fin N, i ≠ j →
      g n < |flowLam F r ω i - flowLam F r ω j| := by
    intro r hr i j hij
    by_contra hlt; push Not at hlt
    exact hgap ⟨r, hr, i, j, hij, hlt⟩
  have hωA : ω ∈ A := by
    show |flowLam F s' ω k - E| ≤ r₀ / 16
    rw [hlam0]; exact hcen
  -- avoidance
  have hav : ω ∈ avoidSet F s' cc (Kh n) T := by
    intro r hr hK'
    simp only [cenLam, Kh, centreSet, Set.mem_ofPred_eq, Set.mem_union] at hK'
    have hrT : (s + r : ℝ) ≤ cT := by
      have : (r : ℝ) ≤ u - s := by rw [← hTr]; exact_mod_cast hr
      linarith
    rcases hK' with (hf | hgp) | hcE
    · rw [hlam r] at hf
      exact clauses_not_fail hℓ hc₁ hC₁ hN (hgood (s + r) ⟨by
        have := NNReal.coe_nonneg r; linarith, hrT⟩) hf
    · obtain ⟨i, j, hij, hle⟩ := hgp
      have hr' : s' + r ≤ T' := by
        rw [hs', hT', ← NNReal.coe_le_coe]; push_cast
        rw [Real.coe_toNNReal _ (by linarith), Real.coe_toNNReal _ (by linarith)]; linarith
      have := hgaps (s' + r) hr' i j hij
      linarith
    · have := abs_clampCentre_le (E := E) (by positivity : 0 ≤ r₀ / 16) (flowLam F s' ω k)
      simp only [hcc, rowCentre] at hcE
      linarith
  -- identification
  have hdata : v₀ ω = fun j => if j = k then 1 else 0 := by
    funext j; simp [hv₀, Set.indicator_of_mem hωA]
  have hid : genMass (Gen n) F s' v₀ T ω = v u := by
    have := genMass_eq_solution (hGc n) hF has (ω := ω) (L := shortGenerator F a ω ℓ)
      (v₀ := v₀) (fun σ hσ => by
        have hσa : a ≤ σ := has.trans hσ.1.le
        refine shortGenerator_eq_trunc hσa hH (hgpos n).le fun i j hij => (hgaps _ ?_ i j hij).le
        rw [hT', ← NNReal.coe_le_coe, Real.coe_toNNReal _ (by linarith),
          Real.coe_toNNReal _ (by linarith)]
        linarith [hσ.2])
      (by rw [hdata]; exact hv) (r := u - s) ⟨by linarith, le_rfl⟩
    rw [show u - s + s = u by ring] at this
    exact this
  have hvnn : ∀ j, 0 ≤ genMass (Gen n) F s' v₀ T ω j := fun j =>
    (genMass_mem_unit (hGc n) (hGs n) hF s' hv₀b T ω j).1
  -- the centre moves by at most `2 D₀`
  have hdisp : |flowLam F (s' + T) ω k - rowCentre F s' E r₀ k ω| ≤ 2 * D₀ := by
    rw [hlam T, hcceq, hTr, show s + (u - s) = u by ring]
    have h1 := disp_le hF hH hgu k
    have h2 := disp_le hF hH hgs k
    calc |flowEigenvalue F a ω u k - flowEigenvalue F a ω s k|
        ≤ |flowEigenvalue F a ω u k - flowEigenvalue F a ω a k| +
          |flowEigenvalue F a ω a k - flowEigenvalue F a ω s k| := abs_sub_le _ _ _
      _ ≤ D₀ + D₀ := add_le_add h1 (by rw [abs_sub_comm]; exact h2)
      _ = 2 * D₀ := by ring
  -- far labels at time `u` have large weight
  set m := min (δ - d) Rc with hm
  have hfar : ∀ j : Fin N, R < (labelDist k j : ℝ) →
      genMass (Gen n) F s' v₀ T ω j ≤
        Real.exp (-(ν * m)) * (φ (flowLam F (s' + T) ω j - cc ω) *
          genMass (Gen n) F s' v₀ T ω j) := by
    intro j hj
    have hcnt := far_from_label (flowLam F (s' + T) ω) (by
      rw [hlam T]; exact flowEigenvalue_monotone' hF a hH _) hC (by
      rw [hlam T, hTr, show s + (u - s) = u by ring]; exact hgu.2.2.1) hj
    have hdj : δ ≤ |flowLam F (s' + T) ω j - cc ω - 0| := by
      have : |flowLam F (s' + T) ω j - flowLam F (s' + T) ω k| ≤
          |flowLam F (s' + T) ω j - cc ω| + |flowLam F (s' + T) ω k - cc ω| := by
        calc _ = |(flowLam F (s' + T) ω j - cc ω) - (flowLam F (s' + T) ω k - cc ω)| := by
              ring_nf
          _ ≤ _ := abs_sub _ _
      rw [sub_zero, hδ]
      simp only [hcc] at this ⊢
      linarith
    have hw := exp_le_rlPhi_neg (E := 0) (d := d) (R := Rc) hν hRc (flowLam F (s' + T) ω j - cc ω)
    have hmin : m ≤ min (|flowLam F (s' + T) ω j - cc ω - 0| - d) Rc :=
      min_le_min_right _ (by linarith)
    have h1 : Real.exp (ν * m) ≤ φ (flowLam F (s' + T) ω j - cc ω) :=
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hmin hν)).trans hw
    have he : Real.exp (-(ν * m)) * Real.exp (ν * m) = 1 := by rw [← Real.exp_add]; simp
    calc genMass (Gen n) F s' v₀ T ω j
        = Real.exp (-(ν * m)) * (Real.exp (ν * m) * genMass (Gen n) F s' v₀ T ω j) := by
          rw [← mul_assoc, he, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (hvnn j))
          (Real.exp_pos _).le
  have hXω : X n ω = goodMass (Gen n) F s' v₀ cc φ T ω := by
    simp only [X, Set.indicator_of_mem hav]
  have hsum : ∑ j : Fin N, (if R < (labelDist k j : ℝ) then 1 else 0) * v u j ≤
      Real.exp (-(ν * m)) * X n ω := by
    rw [hXω, ← hid]
    simp only [goodMass, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    split_ifs with hj
    · rw [one_mul]; exact hfar j hj
    · rw [zero_mul]
      exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (rlPhi_pos _).le (hvnn j))
  have : th * Real.exp (ν * m) < X n ω := by
    have he : Real.exp (ν * m) * Real.exp (-(ν * m)) = 1 := by rw [← Real.exp_add]; simp
    have hpos := Real.exp_pos (ν * m)
    calc th * Real.exp (ν * m) < (∑ j : Fin N, (if R < (labelDist k j : ℝ) then 1 else 0) * v u j) *
          Real.exp (ν * m) := mul_lt_mul_of_pos_right hvk hpos
      _ ≤ Real.exp (-(ν * m)) * X n ω * Real.exp (ν * m) := mul_le_mul_of_nonneg_right hsum hpos.le
      _ = X n ω := by rw [mul_comm (Real.exp _) (X n ω), mul_assoc, mul_comm (Real.exp _), he,
            mul_one]
  linarith

end BlockBand.Palm.RelativeLocalization
