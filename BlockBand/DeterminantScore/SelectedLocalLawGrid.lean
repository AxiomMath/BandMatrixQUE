module

public import BlockBand.DeterminantScore.SelectedLocalLaw
public import BlockBand.DeterminantScore.SelectedResolventTrace
public import BlockBand.LocalWindow.ProofPartOneGrid

/-!
# The complex-trace local law on an energy grid, conditional on the exterior

* `hatK ε₀ ω e = F̂(e) - e` (truncated residual at a grid energy).
* `norm_chi_le_blockMax`: for Hermitian `K`, the one-trace certificate `χ(K, s, 0, ā(E))` is
  bounded by the block certificate `max_k |W⁻¹ Tr P_k (K - s a)⁻¹ - a|` (generalizes
  `SelectedResolvent.norm_chi_le_certErr`); `norm_chi_hatK_le`: `‖χ(K̂_e)‖ ≤ certErrHat(e)`.
* `PairRegularBody`: the conclusion of `SelectedResolvent.pair_regular` for fixed constants;
  `pairDyson_near`: under it, `‖m_K(z) - μ‖ ≤ L(‖z‖ + χ₀)`, `Im m_K(z) ≥ 3V/4`, root equation.
* `TraceGood`, `TraceBadEvent`: the good exterior states at a grid energy `e` (Hermitian `V`,
  `s^{-1/2}‖K̂_e‖ ≤ C d^A`, `‖χ(K̂_e)‖ ≤ χ₀`) and the grid failure event
  `d^δ/η + dρ < ‖Tr (K̂_e + G - iη)⁻¹ - d ā(e)‖` (with the deterministic centre `ā(e)`, so that
  the event is Borel; `ρ = L(η + χ₀)`).
* **`splitLaw_traceBad_le`**: `splitLaw(TraceBadEvent) ≤ |Es| d^{-D}` (conditional Fubini
  `ProofPartOne.prod_inter_le_of_section` and `SelectedLocalLaw.gue_trace_bad_le` on each good
  section).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.SelectedLocalLaw

open MeasureTheory Matrix BlockBand.Palm
open BlockBand.Model.Construction
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.Layers
open BlockBand.LocalWindow BlockBand.LocalWindow.LawBridge BlockBand.LocalWindow.ProofCount
open BlockBand.LocalWindow.ProofCertificate BlockBand.LocalWindow.ProofPartOne
open BlockBand.DeterminantScore.SelectedResolvent
open scoped ENNReal NNReal Matrix.Norms.L2Operator ComplexConjugate

variable {p : Parameters} {i : ZMod p.n}

/-- `K̂_e = F̂(e) - e`: the truncated residual of the split state `ω` at the grid energy `e`. -/
def hatK (ε₀ : ℝ) (om : SplitState p i) (e : ℝ) : PairMatrix p i :=
  truncF ε₀ om.1 om.2.1 om.2.2 e - (e : ℂ) • 1

theorem isHermitian_hatK (ε₀ : ℝ) (om : SplitState p i) (hV : om.2.2.IsHermitian) (e : ℝ) :
    (hatK ε₀ om e).IsHermitian :=
  (isHermitian_truncF ε₀ om.1 om.2.1 hV e).sub (by
    rw [IsHermitian, conjTranspose_smul, conjTranspose_one, Complex.star_def,
      Complex.conj_ofReal])

/-!
## The one-trace certificate of a pair matrix
-/

/-- **`χ ≤` block certificate**: for Hermitian `K`, the one-trace certificate
`χ = ⟨(K - s ā)⁻¹⟩ - ā` (`s = splitS p`, `a = matchedA E`) is bounded by
`max_{k = i, i+1} |W⁻¹ Tr P_k (K - s a)⁻¹ - a|`. -/
theorem norm_chi_le_blockMax {K : PairMatrix p i} (hK : K.IsHermitian) (E : ℝ) :
    ‖certificateChi K (splitS p) 0 (conj (matchedA E))‖ ≤
      max ‖pairBlockTrace p i ((K - ((splitS p : ℂ) * matchedA E) • 1)⁻¹) i - matchedA E‖
        ‖pairBlockTrace p i ((K - ((splitS p : ℂ) * matchedA E) • 1)⁻¹) (i + 1) -
          matchedA E‖ := by
  set a := matchedA E
  set R := (K - ((splitS p : ℂ) * a) • (1 : PairMatrix p i))⁻¹ with hRdef
  have hR : (K - (((0 : ℝ) : ℂ) + (splitS p : ℂ) * conj a) • (1 : PairMatrix p i))⁻¹ = Rᴴ := by
    rw [hRdef, conjTranspose_nonsing_inv]
    congr 1
    rw [conjTranspose_sub, hK.eq, conjTranspose_smul, conjTranspose_one]
    congr 2
    simp [Complex.conj_ofReal]
  have hcard : (Fintype.card (PairSite p i) : ℂ) = 2 * p.W := by
    rw [BlockBand.Angular.FiberAngular.card_pairSite]; push_cast; ring
  have hW : (p.W : ℂ) ≠ 0 := by exact_mod_cast p.W_pos.ne'
  have hchi : certificateChi K (splitS p) 0 (conj a) =
      conj (((pairBlockTrace p i R i - a) + (pairBlockTrace p i R (i + 1) - a)) / 2) := by
    unfold certificateChi certificateMatrixTrace certificateMatrixResolvent
    rw [hR, trace_conjTranspose, trace_eq_pairBlockTrace, hcard]
    rw [map_div₀, map_add, map_sub, map_sub]
    simp only [star_mul', Complex.star_def, map_natCast]
    field_simp
    simp [map_ofNat]
    ring
  rw [hchi, Complex.norm_conj, norm_div, Complex.norm_two]
  have h1 := norm_add_le (pairBlockTrace p i R i - a) (pairBlockTrace p i R (i + 1) - a)
  have h2 := le_max_left ‖pairBlockTrace p i R i - a‖ ‖pairBlockTrace p i R (i + 1) - a‖
  have h3 := le_max_right ‖pairBlockTrace p i R i - a‖ ‖pairBlockTrace p i R (i + 1) - a‖
  linarith

/-- `‖χ(K̂_e, s, 0, ā(e))‖ ≤ certErrHat(e)` for Hermitian `V`. -/
theorem norm_chi_hatK_le (ε₀ : ℝ) (om : SplitState p i) (hV : om.2.2.IsHermitian) (e : ℝ) :
    ‖certificateChi (hatK ε₀ om e) (splitS p) 0 (conj (matchedA e))‖ ≤ certErrHat ε₀ p i om e :=
  norm_chi_le_blockMax (isHermitian_hatK ε₀ om hV e) e

/-!
## The regularity package as a predicate
-/

/-- The conclusion of `SelectedResolvent.pair_regular` for fixed constants `(c, V, ε₁, δ, L)`. -/
def PairRegularBody (c V ε₁ δ L : ℝ) : Prop :=
  ∀ (p : Parameters) (i : ZMod p.n) (K : PairMatrix p i), K.IsHermitian →
    ∀ μ : ℂ, V ≤ μ.im → ‖μ‖ ≤ 1 → ‖certificateChi K c 0 μ‖ ≤ ε₁ →
      (∀ z : ℂ, 0 ≤ z.im → ‖z‖ ≤ δ →
        3 * V / 4 ≤ (pairDyson p i K c z).im ∧ ‖pairDyson p i K c z‖ ≤ 2 ∧
          pairDyson p i K c z = certificateMatrixTrace K (z + c * pairDyson p i K c z)) ∧
      (∀ z₁ z₂ : ℂ, 0 ≤ z₁.im → 0 ≤ z₂.im → ‖z₁‖ ≤ δ → ‖z₂‖ ≤ δ →
        ‖pairDyson p i K c z₁ - pairDyson p i K c z₂‖ ≤ L * ‖z₁ - z₂‖) ∧
      ‖pairDyson p i K c 0 - μ‖ ≤ L * ‖certificateChi K c 0 μ‖

/-- `pair_regular` in predicate form. -/
theorem pairRegularBody_exists {c V : ℝ} (hc : 0 < c) (hc1 : c < 1) (hV : 0 < V) :
    ∃ ε₁ δ L : ℝ, 0 < ε₁ ∧ 0 < δ ∧ 0 < L ∧ PairRegularBody c V ε₁ δ L :=
  pair_regular hc hc1 hV

/-- **The Dyson root near the reference**: under `PairRegularBody`, for Hermitian `K`, a
reference `μ` (`V ≤ Im μ`, `‖μ‖ ≤ 1`) with `‖χ(K, c, 0, μ)‖ ≤ χ₀ ≤ ε₁` and `Im z ≥ 0`,
`‖z‖ ≤ δ`: `m = pairDyson K c z` is a root with `Im m ≥ 3V/4` and `‖m - μ‖ ≤ L(‖z‖ + χ₀)`. -/
theorem pairDyson_near {c V ε₁ δ L : ℝ} (hreg : PairRegularBody c V ε₁ δ L) (hL : 0 ≤ L)
    (hδ : 0 ≤ δ) {K : PairMatrix p i} (hK : K.IsHermitian) {μ : ℂ} (hVμ : V ≤ μ.im)
    (hμ : ‖μ‖ ≤ 1) {χ₀ : ℝ} (hchi : ‖certificateChi K c 0 μ‖ ≤ χ₀) (hχ₀ : χ₀ ≤ ε₁)
    {z : ℂ} (hz : 0 ≤ z.im) (hzδ : ‖z‖ ≤ δ) :
    3 * V / 4 ≤ (pairDyson p i K c z).im ∧
      pairDyson p i K c z = certificateMatrixTrace K (z + c * pairDyson p i K c z) ∧
      ‖pairDyson p i K c z - μ‖ ≤ L * (‖z‖ + χ₀) := by
  obtain ⟨hpt, hlip, hm0⟩ := hreg p i K hK μ hVμ hμ (hchi.trans hχ₀)
  obtain ⟨him, -, hroot⟩ := hpt z hz hzδ
  refine ⟨him, hroot, ?_⟩
  have h1 := hlip z 0 hz (by simp) hzδ (by simpa using hδ)
  rw [sub_zero] at h1
  calc ‖pairDyson p i K c z - μ‖
      ≤ ‖pairDyson p i K c z - pairDyson p i K c 0‖ + ‖pairDyson p i K c 0 - μ‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ L * ‖z‖ + L * χ₀ := add_le_add h1 (hm0.trans (mul_le_mul_of_nonneg_left hchi hL))
    _ = L * (‖z‖ + χ₀) := by ring

/-!
## The grid events
-/

variable (p i)

/-- The good exterior states at a grid energy `e`: `V` Hermitian,
`s^{-1/2}‖K̂_e‖ ≤ C d^A`, `‖χ(K̂_e, s, 0, ā(e))‖ ≤ χ₀`. -/
def TraceGood (ε₀ A C χ₀ e : ℝ) : Set (SplitState p i) :=
  {om | om.2.2.IsHermitian ∧
    (Real.sqrt (splitS p))⁻¹ * ‖hatK ε₀ om e‖ ≤ C * ((2 * p.W : ℕ) : ℝ) ^ A ∧
    ‖certificateChi (hatK ε₀ om e) (splitS p) 0 (conj (matchedA e))‖ ≤ χ₀}

/-- The **complex-trace local-law failure event on a grid**: some grid
energy `e ∈ Es` with a good exterior at which
`d^δ/η + dρ < ‖Tr (K̂_e + G - iη)⁻¹ - d ā(e)‖`. -/
def TraceBadEvent (ε₀ A C χ₀ δ η ρ : ℝ) (Es : Finset ℝ) : Set (SplitState p i × PairMatrix p i) :=
  {x | ∃ e ∈ Es, x.1 ∈ TraceGood p i ε₀ A C χ₀ e ∧
    ((2 * p.W : ℕ) : ℝ) ^ δ / η + ((2 * p.W : ℕ) : ℝ) * ρ <
      ‖((hatK ε₀ x.1 e + x.2 - (((0 : ℝ) : ℂ) + Complex.I * η) • (1 : PairMatrix p i))⁻¹).trace -
        ((2 * p.W : ℕ) : ℂ) * conj (matchedA e)‖}

theorem measurable_hatK_resolvent {ε₀ : ℝ} (hε₀ : 0 < ε₀) (e : ℝ) (z : ℂ) :
    Measurable (fun x : SplitState p i × PairMatrix p i =>
      ((hatK ε₀ x.1 e + x.2 - z • (1 : PairMatrix p i))⁻¹).trace) := by
  have h1 : Measurable (fun x : SplitState p i × PairMatrix p i =>
      truncF ε₀ x.1.1 x.1.2.1 x.1.2.2 e) := (measurable_truncF hε₀ e).comp measurable_fst
  have h2 : Measurable (fun x : SplitState p i × PairMatrix p i =>
      hatK ε₀ x.1 e + x.2 - z • (1 : PairMatrix p i)) := by
    refine measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun b => ?_
    simp only [hatK, Matrix.sub_apply, Matrix.add_apply]
    exact ((((measurable_pi_apply b).comp ((measurable_pi_apply a).comp h1)).sub
      measurable_const).add
      ((measurable_pi_apply b).comp ((measurable_pi_apply a).comp measurable_snd))).sub
      measurable_const
  exact continuous_id.matrix_trace.measurable.comp (measurable_inv_matrix.comp h2)

variable {p i}

/-- **The complex-trace local law on a grid, conditional on the exterior** (conditional Fubini under `splitLaw = Pω ⊗ GUE_d(s/d)`). Fixed `0 < b < 1/2`
(`c = min(1 - 2b, b)`), `V > 0`, constants `ε₁, δ_P, L` of `PairRegularBody c V`, a bulk margin
`κ` with `V ≤ √κ/2`, and `A, C`, `ε, δ, D > 0`; then `N₀`; for every `p` with `p.b = b`, model,
pair, splitting law with `d = 2W ≥ N₀`, `ε₀ > 0`, grid `Es ⊆ bulkInterval κ`, `0 < η ≤ δ_P`,
`0 ≤ χ₀ ≤ ε₁` with `d^ε ≤ d η (3V/4)/π` and `η ≤ √s d^{A + 1/ε}`:
`splitLaw(TraceBadEvent (ρ = L(η + χ₀))) ≤ |Es| d^{-D}`. -/
theorem splitLaw_traceBad_le (hBridge : PairGUELawBridgeStatement) (hELG : ExternalLocalGUE)
    (hMDE : MDEBranchIdentification) {b V ε₁ δP L κ : ℝ}
    (hreg : PairRegularBody (min (1 - 2 * b) b) V ε₁ δP L) (hV0 : 0 < V) (hL : 0 ≤ L) (hκ : 0 < κ)
    (hVκ : V ≤ Real.sqrt κ / 2)
    (A C ε δ D : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hD : 0 < D) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ (p : Parameters), p.b = b → ∀ (model : p.GaussianRingModel)
      (i : ZMod p.n) (Pω : Measure (SplitState p i)), IsPairSplitting p i model (splitS p) Pω →
      N₀ ≤ 2 * p.W → ∀ ε₀ : ℝ, 0 < ε₀ → ∀ (Es : Finset ℝ), (∀ e ∈ Es, e ∈ bulkInterval κ) →
        ∀ η χ₀ : ℝ, 0 < η → η ≤ δP → 0 ≤ χ₀ → χ₀ ≤ ε₁ →
        ((2 * p.W : ℕ) : ℝ) ^ ε ≤ ((2 * p.W : ℕ) : ℝ) * η * (3 * V / 4 / Real.pi) →
        η ≤ Real.sqrt (splitS p) * ((2 * p.W : ℕ) : ℝ) ^ (A + 1 / ε) →
        splitLaw p i Pω (TraceBadEvent p i ε₀ A C χ₀ δ η (L * (η + χ₀)) Es) ≤
          Es.card * ENNReal.ofReal (((2 * p.W : ℕ) : ℝ) ^ (-D)) := by
  obtain ⟨N₀, hN₀, h⟩ := gue_trace_bad_le hBridge hELG hMDE A C ε δ D hε hδ hD
  refine ⟨N₀, hN₀, fun p hpb model i Pω hPω hN ε₀ hε₀ Es hEs η χ₀ hη hηδ hχ0 hχ₁ hdom hz => ?_⟩
  set a : ℝ≥0∞ := ENNReal.ofReal (((2 * p.W : ℕ) : ℝ) ^ (-D))
  set dR : ℝ := ((2 * p.W : ℕ) : ℝ) with hdR
  have hd : 0 < dR := by
    have := p.W_pos
    rw [hdR]; exact_mod_cast (by omega : 0 < 2 * p.W)
  have hs := BlockBand.Angular.PairCoareaBridge.splitS_pos p
  have hsp : splitS p = min (1 - 2 * b) b := splitS_eq hpb
  set z : ℂ := ((0 : ℝ) : ℂ) + Complex.I * η with hzdef
  have hzim : z.im = η := by simp [z]
  have hznorm : ‖z‖ = η := by
    simp only [z, Complex.ofReal_zero, zero_add, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη]
  set S : Finset ℝ → ℝ → Set (SplitState p i × PairMatrix p i) := fun _ e =>
    {x | dR ^ δ / η + dR * (L * (η + χ₀)) <
      ‖((hatK ε₀ x.1 e + x.2 - z • (1 : PairMatrix p i))⁻¹).trace -
        ((2 * p.W : ℕ) : ℂ) * conj (matchedA e)‖}
  have hsub : TraceBadEvent p i ε₀ A C χ₀ δ η (L * (η + χ₀)) Es ⊆ ⋃ e ∈ Es,
      {x | x ∈ S Es e ∧ x.1 ∈ TraceGood p i ε₀ A C χ₀ e} := by
    rintro x ⟨e, he, hg, hb⟩
    refine Set.mem_biUnion he ⟨?_, hg⟩
    exact hb
  have hone : ∀ e ∈ Es, splitLaw p i Pω {x | x ∈ S Es e ∧ x.1 ∈ TraceGood p i ε₀ A C χ₀ e} ≤
      a := by
    intro e he
    have hS : MeasurableSet (S Es e) :=
      measurableSet_lt measurable_const
        (((measurable_hatK_resolvent p i hε₀ e z).sub measurable_const).norm)
    have := prod_inter_le_of_section Pω (gueMeasure (PairSite p i) (pairTime p (splitS p))) hS
      (Good := TraceGood p i ε₀ A C χ₀ e) (a := a) (fun om hom => by
        obtain ⟨hV, hn, hchi⟩ := hom
        have hK := isHermitian_hatK ε₀ om hV e
        obtain ⟨hVμ0, hμ1⟩ := conj_matchedA_bounds hκ (hEs e he)
        have hVμ : V ≤ (conj (matchedA e)).im := hVκ.trans hVμ0
        rw [hsp] at hchi
        obtain ⟨him, hroot, hnear⟩ := pairDyson_near hreg hL ((hη.le).trans hηδ) hK hVμ hμ1
          hchi hχ₁ (by rw [hzim]; exact hη.le) (by rw [hznorm]; exact hηδ)
        rw [hznorm] at hnear
        set m := pairDyson p i (hatK ε₀ om e) (min (1 - 2 * b) b) z
        have hm : 0 < m.im := lt_of_lt_of_le (by positivity) him
        have hdom' : dR ^ ε ≤ dR * η * (m.im / Real.pi) :=
          hdom.trans (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right him Real.pi_pos.le)
            (mul_pos hd hη).le)
        have hz' : ‖((0 : ℝ) : ℂ) + Complex.I * η‖ ≤
            Real.sqrt (splitS p) * dR ^ (A + 1 / ε) := by
          rw [← hzdef, hznorm]; exact hz
        rw [← hsp] at hroot
        have hbad := h p i hN (splitS p) hs (hatK ε₀ om e) hK hn 0 η hη m hm
          (by rw [← hzdef]; convert hroot using 3) hdom' hz'
        refine (measure_mono fun G hG => ?_).trans hbad
        simp only [S, Set.mem_preimage, Set.mem_ofPred_eq] at hG ⊢
        rw [← hzdef]
        have htri : ‖((hatK ε₀ om e + G - z • (1 : PairMatrix p i))⁻¹).trace -
            ((2 * p.W : ℕ) : ℂ) * conj (matchedA e)‖ ≤
            ‖((hatK ε₀ om e + G - z • (1 : PairMatrix p i))⁻¹).trace - ((2 * p.W : ℕ) : ℂ) * m‖ +
              dR * (L * (η + χ₀)) := by
          have e1 : ((hatK ε₀ om e + G - z • (1 : PairMatrix p i))⁻¹).trace -
              ((2 * p.W : ℕ) : ℂ) * conj (matchedA e) =
              (((hatK ε₀ om e + G - z • (1 : PairMatrix p i))⁻¹).trace -
                ((2 * p.W : ℕ) : ℂ) * m) + ((2 * p.W : ℕ) : ℂ) * (m - conj (matchedA e)) := by
            ring
          rw [e1]
          refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
          rw [norm_mul, Complex.norm_natCast]
          exact mul_le_mul_of_nonneg_left hnear hd.le
        linarith)
    rwa [measure_univ_of_isPairSplitting p i hPω, mul_one] at this
  calc splitLaw p i Pω (TraceBadEvent p i ε₀ A C χ₀ δ η (L * (η + χ₀)) Es)
      ≤ ∑ e ∈ Es, splitLaw p i Pω {x | x ∈ S Es e ∧ x.1 ∈ TraceGood p i ε₀ A C χ₀ e} :=
        (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
    _ ≤ ∑ _e ∈ Es, a := Finset.sum_le_sum hone
    _ = Es.card * a := by rw [Finset.sum_const, nsmul_eq_mul]

end BlockBand.DeterminantScore.SelectedLocalLaw
