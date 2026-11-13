module

public import BlockBand.Endpoints.Response.NearSchattenFinite
public import BlockBand.Endpoints.Response.TaggedConvexOrderStoppedNuc

/-!
# Deterministic inputs of the stopped energy inequality

* Measurability of word values: `nss_measurable_polyValue`, `ω ↦ polyValue Φ` is measurable
  for every trace polynomial `Φ` of the one-source family, and the one-source stop is adapted
  (`nss_measurableSet_alive_growthSigma`).
* The generator mass: `nss_abs_genExpr_le`, with `𝕊` unitary,
  `|𝒢_ε| ≤ (D/2) M_ε (g Tr A + (Tr A)²)`, `M_ε = max(pε^{p-1}, p(1-p)ε^{p-2})`; in particular
  `-𝒢_ε ≤ C_ε(g Tr A + (Tr A)²)`.
* The reverse bridge: `nss_polyGen_le_genExpr`, on the stop, after the injection,
  `Re 𝒜Φ_π ≤ 𝒢_ε + (D/2)δ(K²/2 + K²)`; with `nss_genExpr_nonpos` (`𝒢_ε ≤ 0`) this bounds the
  truncation `(-Re 𝒜Φ_π)⁺ ≤ -Re 𝒜Φ_π + cδ`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Matrix Filter Topology Set Finset
open scoped ENNReal ComplexOrder
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
  BlockBand.Internal.Contracts.Endpoints

variable {W : ℕ}

/-!
## Measurability
-/

theorem nss_measurable_intervalSource (b E : ℝ) (W j : ℕ) (q : ℝ → ℝ) :
    Measurable (fun ω : GrowthPath W => intervalSource b E W j q ω) := by
  unfold intervalSource
  refine Measurable.of_eval_matrix _ fun x y => ?_
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact Finset.measurable_sum _ fun k _ =>
    measurable_const.mul (tco_measurable_tagResponse b E W j k).eval_matrix

theorem nss_measurable_traceLoad (b E : ℝ) (κ : Fin 0 → ℕ) (q : ℝ → ℝ) (W j : ℕ) :
    Measurable (fun ω : GrowthPath W => traceLoad b E κ (fun _ : Fin 1 => q) W j ω) := by
  simp_rw [nsf_traceLoad_eq]
  exact (Complex.measurable_re.comp ((continuous_id.matrix_trace).measurable.comp
    (nss_measurable_intervalSource b E W j q))).add
    (tcx_measurable_nuclearNorm_pathCurrent b E W j)

theorem nss_alive_eq_iInter (b E : ℝ) (κ : Fin 0 → ℕ) (q : ℝ → ℝ) (K ε : ℝ) (W l : ℕ) :
    alive b E κ (fun _ : Fin 1 => q) K ε W l = ⋂ i ∈ Finset.range (l + 1),
      {ω | ¬ (ε * W ≤ i ∧ K < traceLoad b E κ (fun _ : Fin 1 => q) W i ω)} := by
  ext ω
  simp only [tcw_mem_alive_iff, Set.mem_iInter, Finset.mem_range, Set.mem_ofPred_eq]
  exact ⟨fun h i hi => h i (by omega), fun h i hi => h i (by omega)⟩

theorem nss_measurableSet_alive (b E : ℝ) (κ : Fin 0 → ℕ) (q : ℝ → ℝ) (K ε : ℝ) (W l : ℕ) :
    MeasurableSet (alive b E κ (fun _ : Fin 1 => q) K ε W l) := by
  rw [nss_alive_eq_iInter]
  refine Finset.measurableSet_biInter _ fun i _ => ?_
  by_cases hi : ε * W ≤ i
  · simp only [hi, true_and]
    exact (measurableSet_lt measurable_const (nss_measurable_traceLoad b E κ q W i)).compl
  · simp [hi]

theorem nss_intervalSource_ext {b E : ℝ} {W i l : ℕ} (hi : i ≤ l) (q : ℝ → ℝ)
    (ω : GrowthPath W) :
    intervalSource b E W i q (tcx_ext W l (tcx_proj W l ω)) = intervalSource b E W i q ω := by
  unfold intervalSource
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [tcx_tagResponse_ext hi]

theorem nss_traceLoad_ext {b E : ℝ} (κ : Fin 0 → ℕ) (q : ℝ → ℝ) {W i l : ℕ} (hi : i ≤ l)
    (ω : GrowthPath W) :
    traceLoad b E κ (fun _ : Fin 1 => q) W i (tcx_ext W l (tcx_proj W l ω)) =
      traceLoad b E κ (fun _ : Fin 1 => q) W i ω := by
  rw [nsf_traceLoad_eq, nsf_traceLoad_eq, tcx_pathCurrent_ext hi, nss_intervalSource_ext hi]

/-- Adaptedness of the one-source stop: `{l < σ_K} ∈ growthSigma W l`. -/
theorem nss_measurableSet_alive_growthSigma (b E : ℝ) (κ : Fin 0 → ℕ) (q : ℝ → ℝ) (K ε : ℝ)
    (W l : ℕ) : MeasurableSet[growthSigma W l] (alive b E κ (fun _ : Fin 1 => q) K ε W l) := by
  refine tcx_measurableSet_growthSigma_of_invariant (nss_measurableSet_alive b E κ q K ε W l)
    fun ω => ?_
  simp only [tcw_mem_alive_iff]
  refine forall_congr' fun i => forall_congr' fun hi => ?_
  rw [nss_traceLoad_ext κ q hi]

theorem nss_measurable_letterMatrix (b E : ℝ) (κ : Fin 0 → ℕ) (qf : Fin 1 → ℝ → ℝ) (W j : ℕ)
    (x : TraceLetter 0 1) :
    Measurable (fun ω : GrowthPath W => letterMatrix b E κ qf W j ω x) := by
  cases x with
  | current => exact tcw_measurable_pathCurrent b E W j
  | tag a => exact a.elim0
  | interval a => exact nss_measurable_intervalSource b E W j (qf a)

theorem nss_measurable_separatorMatrix (b E : ℝ) (W j : ℕ) (s : Separator) :
    Measurable (fun ω : GrowthPath W => separatorMatrix b E W j ω s) := by
  have hS := tcw_measurable_scattering b E W j
  cases s
  · exact measurable_const
  · exact measurable_const
  · exact (continuous_const.matrix_mul continuous_id).measurable.comp hS
  · exact (continuous_id.matrix_conjTranspose.matrix_mul continuous_const).measurable.comp hS
  · exact ((continuous_const.matrix_mul continuous_id).matrix_mul
      continuous_const).measurable.comp hS
  · exact ((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul
      continuous_const).measurable.comp hS

theorem nss_measurable_wordValue (b E : ℝ) (κ : Fin 0 → ℕ) (qf : Fin 1 → ℝ → ℝ) (W j : ℕ)
    (w : TraceWord 0 1) : Measurable (fun ω : GrowthPath W => wordValue b E κ qf W j ω w) := by
  have hmul : ∀ f g : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ,
      Measurable f → Measurable g → Measurable (fun ω => f ω * g ω) := fun f g hf hg => by
    refine Measurable.of_eval_matrix _ fun x y => ?_
    simp only [Matrix.mul_apply]
    exact Finset.measurable_sum _ fun k _ => hf.eval_matrix.mul hg.eval_matrix
  have hL : ∀ L : TraceWord 0 1, Measurable (fun ω : GrowthPath W => (L.map fun x =>
      letterMatrix b E κ qf W j ω x.1 * separatorMatrix b E W j ω x.2).prod) := by
    intro L
    induction L with
    | nil => simp
    | cons x L ih =>
      simp only [List.map_cons, List.prod_cons]
      exact hmul _ _ (hmul _ _ (nss_measurable_letterMatrix b E κ qf W j x.1)
        (nss_measurable_separatorMatrix b E W j x.2)) ih
  exact (continuous_id.matrix_trace).measurable.comp (hL w)

/-- `ω ↦ polyValue Φ` is measurable (one-source family). -/
theorem nss_measurable_polyValue (b E : ℝ) (κ : Fin 0 → ℕ) (qf : Fin 1 → ℝ → ℝ) (W j : ℕ)
    (Φ : TracePoly 0 1) : Measurable (fun ω : GrowthPath W => polyValue b E κ qf W j ω Φ) := by
  unfold polyValue
  simp_rw [MvPolynomial.eval_eq]
  exact Finset.measurable_sum _ fun d _ => measurable_const.mul
    (Finset.measurable_prod _ fun w _ => (nss_measurable_wordValue b E κ qf W j w).pow_const _)

/-!
## The size of the regularized generator
-/

/-- `M_ε = max(pε^{p-1}, p(1-p)ε^{p-2})`. -/
def nssGenConst (p ε : ℝ) : ℝ := max (p * ε ^ (p - 1)) (p * (1 - p) * ε ^ (p - 2))

theorem nss_abs_deriv_le {p ε x : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 < ε) (hx : 0 ≤ x) :
    |nsgDeriv p ε x| ≤ p * ε ^ (p - 1) := by
  unfold nsgDeriv
  have h0 : 0 ≤ (x + ε) ^ (p - 1) := Real.rpow_nonneg (by linarith) _
  have h1 : (x + ε) ^ (p - 1) ≤ ε ^ (p - 1) :=
    Real.rpow_le_rpow_of_nonpos hε (by linarith) (by linarith)
  rw [abs_of_nonneg (mul_nonneg hp0 h0)]
  exact mul_le_mul_of_nonneg_left h1 hp0

theorem nss_abs_deriv2_le {p ε x : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 < ε) (hx : 0 ≤ x) :
    |nsgDeriv2 p ε x| ≤ p * (1 - p) * ε ^ (p - 2) := by
  unfold nsgDeriv2
  have h0 : 0 ≤ (x + ε) ^ (p - 2) := Real.rpow_nonneg (by linarith) _
  have h1 : (x + ε) ^ (p - 2) ≤ ε ^ (p - 2) :=
    Real.rpow_le_rpow_of_nonpos hε (by linarith) (by linarith)
  have hc : 0 ≤ p * (1 - p) := mul_nonneg hp0 (by linarith)
  rw [show p * (p - 1) * (x + ε) ^ (p - 2) = -(p * (1 - p) * (x + ε) ^ (p - 2)) by ring,
    abs_neg, abs_of_nonneg (mul_nonneg hc h0)]
  exact mul_le_mul_of_nonneg_left h1 hc

/-- `|DD f_ε'(x, y)| ≤ p(1-p)ε^{p-2}` for `x, y ≥ 0`. -/
theorem nss_abs_divDiff_le {p ε x y : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 < ε) (hx : 0 ≤ x)
    (hy : 0 ≤ y) : |nsgDivDiff p ε x y| ≤ p * (1 - p) * ε ^ (p - 2) := by
  unfold nsgDivDiff
  split_ifs with hxy
  · exact nss_abs_deriv2_le hp0 hp1 hε hx
  · have hne : 0 < |x - y| := abs_pos.2 (sub_ne_zero.2 hxy)
    rw [abs_div, div_le_iff₀ hne]
    exact nsf_abs_sub_le_of_deriv (L := max x y) (g := nsgDeriv p ε) (g' := nsgDeriv2 p ε)
      (fun z hz => nsg_hasDerivAt_deriv (by linarith [hz.1]))
      (fun z hz => nss_abs_deriv2_le hp0 hp1 hε hz.1) ⟨hx, le_max_left _ _⟩
      ⟨hy, le_max_right _ _⟩

theorem nss_nsfSpecGen_zero {ι : Type*} [Fintype ι] (D g : ℝ) (lam s : ι → ℝ) :
    nsfSpecGen D g (fun _ => 0) (fun _ => 0) lam s = 0 := by
  unfold nsfSpecGen nsfDivDiff
  simp

/-- The size of the regularized trace generator: with `𝕊` unitary,
`|𝒢_ε| ≤ (D/2) M_ε (g Tr A + (Tr A)²)`. -/
theorem nss_abs_genExpr_le {b E p ε : ℝ} (hb : 0 < b) (hE : -2 < E) (hE' : E < 2) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (hε : 0 < ε) {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) {j : ℕ} {ω : GrowthPath W}
    (hS : (scatteringMatrix b E W j ω)ᴴ * scatteringMatrix b E W j ω = 1) :
    |nsgGenExpr b E p ε q W j ω| ≤ transportD0 b E / 2 * nssGenConst p ε *
      (nsgConductance (scatteringMatrix b E W j ω) * (nearClock b E W j q ω).trace.re +
        (nearClock b E W j q ω).trace.re ^ 2) := by
  have hpsd := ns_nearClock_posSemidef b E W j q hq ω
  obtain ⟨hV, -⟩ := nsf_eigenframe hpsd.1
  rw [nsf_nsgGenExpr_eq]
  unfold nsfGenExpr
  rw [dite_eq_left hpsd.1]
  set lam := hpsd.1.eigenvalues
  have hsum : ∑ i, lam i = (nearClock b E W j q ω).trace.re := by
    rw [hpsd.1.trace_eq_sum_eigenvalues, Complex.re_sum]; simp [lam]
  have hlam : ∀ i, lam i ∈ Icc 0 ((nearClock b E W j q ω).trace.re) :=
    fun i => ⟨hpsd.eigenvalues_nonneg i, nsf_eigenvalue_le_trace hpsd i⟩
  have hD := (ns_transportD0_pos hb hE hE').le
  have hcmp := nsf_specGen_sub_le (L := (nearClock b E W j q ω).trace.re) (δ := nssGenConst p ε)
    (e₁ := fun _ => 0) (e₂ := fun _ => 0) hD (nsg_conductance_nonneg hS) hlam
    (fun i => nsg_frameDiag_nonneg _ _ i) (fun i => nsg_frameDiag_le_one hS hV i)
    (fun x hx => by
      rw [sub_zero]; exact (nss_abs_deriv_le hp0 hp1 hε hx.1).trans (le_max_left _ _))
    (fun x hx y hy => by
      have : nsfDivDiff (fun _ : ℝ => (0 : ℝ)) (fun _ => 0) x y = 0 := by
        unfold nsfDivDiff; simp
      rw [this, sub_zero, ← nsf_nsgDivDiff_eq]
      exact (nss_abs_divDiff_le hp0 hp1 hε hx.1 hy.1).trans (le_max_right _ _))
  rw [nss_nsfSpecGen_zero, sub_zero, hsum] at hcmp
  exact hcmp.trans_eq (by ring)

/-- `𝒢_ε ≤ 0` at a path with unitary `𝕊`. -/
theorem nss_genExpr_nonpos {b E p ε : ℝ} (hb : 0 < b) (hE : -2 < E) (hE' : E < 2) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (hε : 0 < ε) {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) {j : ℕ} {ω : GrowthPath W}
    (hS : (scatteringMatrix b E W j ω)ᴴ * scatteringMatrix b E W j ω = 1) :
    nsgGenExpr b E p ε q W j ω ≤ 0 := by
  refine (nsg_genExpr_le hb hE hE' hp0 hp1 hε hq hS).trans ?_
  have hr : 0 ≤ nsDecayRate b E p := by
    unfold nsDecayRate
    have := (ns_transportD0_pos hb hE hE').le
    have : 0 ≤ 1 - p := by linarith
    positivity
  have hc : 0 ≤ nsClockSum (nsDissKernel p ε) (nearClock b E W j q ω) :=
    ns_clockSum_nonneg (fun x _ => by
      unfold nsDissKernel
      exact mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (by positivity) _))
      (ns_nearClock_posSemidef b E W j q hq ω)
  nlinarith

/-- `|𝒢_ε| ≤ C_ε K²` on the stop (`C_ε = (D/2) M_ε (1/2 + 1)`). -/
theorem nss_abs_genExpr_le_alive {b E p ε : ℝ} (hb : 0 < b) (hE : -2 < E) (hE' : E < 2)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hε : 0 < ε) {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) {K ε' : ℝ}
    {j : ℕ} {ω : GrowthPath W} (κ : Fin 0 → ℕ)
    (halive : ω ∈ alive b E κ (fun _ : Fin 1 => q) K ε' W j) (hj : ε' * W ≤ j)
    (hS : (scatteringMatrix b E W j ω)ᴴ * scatteringMatrix b E W j ω = 1) :
    |nsgGenExpr b E p ε q W j ω| ≤
      transportD0 b E / 2 * nssGenConst p ε * (K / 2 * K + K ^ 2) := by
  obtain ⟨-, hg, -, hA⟩ := nsf_alive_bounds κ hq halive hj hS
  have hA0 := (trace_nearClock_le b E W j q hq ω).1
  have hg0 := nsg_conductance_nonneg hS
  have hM : 0 ≤ nssGenConst p ε :=
    (mul_nonneg hp0 (Real.rpow_nonneg hε.le _)).trans (le_max_left _ _)
  have hD := (ns_transportD0_pos hb hE hE').le
  refine (nss_abs_genExpr_le hb hE hE' hp0 hp1 hε hq hS).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hK0 : 0 ≤ K := hA0.trans hA
  gcongr

/-!
## The reverse bridge on the stop
-/

/-- Two-sided bridge on the stop: `|Re 𝒜Φ_π - 𝒢_ε| ≤ (D/2)δ(K²/2 + K²)` (under the hypotheses of
`nsf_neg_genExpr_le_poly`). -/
theorem nss_abs_polyGen_sub_genExpr_le {b E p ε : ℝ} (hb : 0 < b) (hE : -2 < E) (hE' : E < 2)
    {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) {K ε' δ : ℝ} {a : ℕ → ℝ} {N : ℕ}
    (h1 : ∀ x ∈ Icc 0 (K + 1), |nsfPolyD1 a N x - nsgDeriv p ε x| ≤ δ)
    (h2 : ∀ x ∈ Icc 0 (K + 1), ∀ y ∈ Icc 0 (K + 1),
      |nsfDivDiff (nsfPolyD1 a N) (nsfPolyD2 a N) x y - nsgDivDiff p ε x y| ≤ δ)
    {j : ℕ} {ω : GrowthPath W} (κ : Fin 0 → ℕ)
    (halive : ω ∈ alive b E κ (fun _ : Fin 1 => q) K ε' W j) (hj : ε' * W ≤ j)
    (hS : (scatteringMatrix b E W j ω)ᴴ * scatteringMatrix b E W j ω = 1) {t : ℝ}
    (hqt : q t = 0) :
    |(polyValue b E κ (fun _ => q) W j ω
          (wordGenerator b E (fun _ => q) t (nsfClockPoly a N))).re -
        nsgGenExpr b E p ε q W j ω| ≤
      transportD0 b E / 2 * δ * (K / 2 * K + K ^ 2) := by
  have hpsd := ns_nearClock_posSemidef b E W j q hq ω
  obtain ⟨hV, -⟩ := nsf_eigenframe hpsd.1
  obtain ⟨-, hg, -, hA⟩ := nsf_alive_bounds κ hq halive hj hS
  rw [nsf_polyValue_wordGenerator_path b E hq W j ω κ a N hqt, Complex.ofReal_re,
    nsf_nsgGenExpr_eq]
  unfold nsfGenExpr
  rw [dite_eq_left hpsd.1, dite_eq_left hpsd.1]
  set lam := hpsd.1.eigenvalues
  have hsum : ∑ i, lam i = (nearClock b E W j q ω).trace.re := by
    rw [hpsd.1.trace_eq_sum_eigenvalues, Complex.re_sum]; simp [lam]
  have hlam : ∀ i, lam i ∈ Icc 0 (K + 1) :=
    fun i => ⟨hpsd.eigenvalues_nonneg i, (nsf_eigenvalue_le_trace hpsd i).trans (by linarith)⟩
  have hg0 := nsg_conductance_nonneg hS
  have hD := (ns_transportD0_pos hb hE hE').le
  have hδ : 0 ≤ δ := (abs_nonneg _).trans (h1 0 ⟨le_rfl, by linarith [hlam]⟩)
  have hcmp := nsf_specGen_sub_le (L := K + 1) (d₂ := nsfPolyD2 a N) (e₂ := nsgDeriv2 p ε)
    hD hg0 hlam
    (fun i => nsg_frameDiag_nonneg _ _ i) (fun i => nsg_frameDiag_le_one hS hV i) h1
    (fun x hx y hy => h2 x hx y hy)
  have hS0 : 0 ≤ ∑ i, lam i := Finset.sum_nonneg fun i _ => (hlam i).1
  have hbd : transportD0 b E / 2 * δ * (nsgConductance (scatteringMatrix b E W j ω) *
      ∑ i, lam i + (∑ i, lam i) ^ 2) ≤ transportD0 b E / 2 * δ * (K / 2 * K + K ^ 2) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [hsum] at hS0 ⊢
    have hK0 : 0 ≤ K := hS0.trans hA
    gcongr
  exact hcmp.trans hbd

/-- The reverse bridge on the stop: `Re 𝒜Φ_π ≤ 𝒢_ε + (D/2)δ(K²/2 + K²)`. -/
theorem nss_polyGen_le_genExpr {b E p ε : ℝ} (hb : 0 < b) (hE : -2 < E) (hE' : E < 2)
    {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) {K ε' δ : ℝ} {a : ℕ → ℝ} {N : ℕ}
    (h1 : ∀ x ∈ Icc 0 (K + 1), |nsfPolyD1 a N x - nsgDeriv p ε x| ≤ δ)
    (h2 : ∀ x ∈ Icc 0 (K + 1), ∀ y ∈ Icc 0 (K + 1),
      |nsfDivDiff (nsfPolyD1 a N) (nsfPolyD2 a N) x y - nsgDivDiff p ε x y| ≤ δ)
    {j : ℕ} {ω : GrowthPath W} (κ : Fin 0 → ℕ)
    (halive : ω ∈ alive b E κ (fun _ : Fin 1 => q) K ε' W j) (hj : ε' * W ≤ j)
    (hS : (scatteringMatrix b E W j ω)ᴴ * scatteringMatrix b E W j ω = 1) {t : ℝ}
    (hqt : q t = 0) :
    (polyValue b E κ (fun _ => q) W j ω
        (wordGenerator b E (fun _ => q) t (nsfClockPoly a N))).re ≤
      nsgGenExpr b E p ε q W j ω + transportD0 b E / 2 * δ * (K / 2 * K + K ^ 2) := by
  have := (abs_le.1 (nss_abs_polyGen_sub_genExpr_le hb hE hE' hq h1 h2 κ halive hj hS hqt)).2
  linarith

end BlockBand.Endpoints
