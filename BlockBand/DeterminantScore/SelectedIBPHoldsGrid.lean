module

public import BlockBand.DeterminantScore.SelectedIBPHoldsMoment
public import BlockBand.DeterminantScore.SelectedLocalLawPoint

/-!
# The `Tr G R_η` tail on an energy grid, conditional on the exterior, and its transfer

* `norm_trace_mul_sub_rankOne`: `|Tr G(K - z)⁻¹ - Tr G(K' - z)⁻¹| ≤ ‖G‖ · 2/|Im z|` if
  `K - K' = a bᵀ` (the resolvent difference is rank one with operator norm `≤ 2/|Im z|`).
* `norm_trace_mul_sub_op`: `≤ |ι| ‖G‖ r/|Im z|²` if `‖(K' - z) - (K - z)‖ ≤ r`.
* **`traceG_transfer`**: off the crowding event, at a nonpole `E` and any `e`,
  `|Tr G R_η(K₀(E)) - Tr G R_η(K̂_e)| ≤ c_G (2/η) + 2W c_G (c²/ε₀² + 1)|E - e|/η²`.
* `IBPBadEvent`: some grid energy `e` with a good exterior (`TraceGood`) at which
  `B < |Tr G R_η(K̂_e) + s d ā(e)²|` (deterministic centre `ā(e) = conj (matchedA e)`).
* **`splitLaw_ibpBad_le`**: `splitLaw(IBPBadEvent) ≤ |Es| (C₀ √n M/u)ⁿ` (conditional Fubini
  `ProofPartOne.prod_inter_le_of_section`; on each good section the local law
  `SelectedLocalLaw.gue_trace_bad_le` at loss `d^{1/10}`, failure power `n + 3`, and
  `SelectedIBPHolds.section_tail`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.SelectedIBPHolds

open MeasureTheory ProbabilityTheory Matrix BlockBand.Palm
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.Layers
open BlockBand.LocalWindow BlockBand.LocalWindow.LawBridge BlockBand.LocalWindow.ProofCount
open BlockBand.LocalWindow.ProofCertificate BlockBand.LocalWindow.ProofPartOne
open BlockBand.DeterminantScore.SelectedResolvent BlockBand.DeterminantScore.SelectedLocalLaw
open BlockBand.DeterminantScore.SelectedIBP BlockBand.DeterminantScore.MinorTailInverse
open scoped ENNReal NNReal ComplexConjugate Matrix.Norms.L2Operator

local notation "T" => Matrix.toEuclideanLin (𝕜 := ℂ)

section Trace

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Rank-one change of `Tr G R`** (the resolvent changes by rank one with
operator, hence trace, norm `≤ 2/|Im z|`): for Hermitian `K, K'` with `K - K' = a bᵀ`,
`Im z ≠ 0` and `‖G v‖ ≤ c_G ‖v‖`, `|Tr G(K - z)⁻¹ - Tr G(K' - z)⁻¹| ≤ c_G · 2/|Im z|`. -/
theorem norm_trace_mul_sub_rankOne {K K' : Matrix ι ι ℂ} (hK : K.IsHermitian)
    (hK' : K'.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (a b : ι → ℂ) (hD : K - K' = vecMulVec a b)
    (G : Matrix ι ι ℂ) {cG : ℝ} (hcG : 0 ≤ cG) (hG : ∀ v, ‖T G v‖ ≤ cG * ‖v‖) :
    ‖(G * (K - z • (1 : Matrix ι ι ℂ))⁻¹).trace - (G * (K' - z • (1 : Matrix ι ι ℂ))⁻¹).trace‖ ≤
      cG * (2 * |z.im|⁻¹) := by
  set R := (K - z • (1 : Matrix ι ι ℂ))⁻¹
  set R' := (K' - z • (1 : Matrix ι ι ℂ))⁻¹
  have hu : IsUnit (K - z • (1 : Matrix ι ι ℂ)).det :=
    isUnit_iff_ne_zero.mpr (det_sub_smul_ne_zero hK hz)
  have hu' : IsUnit (K' - z • (1 : Matrix ι ι ℂ)).det :=
    isUnit_iff_ne_zero.mpr (det_sub_smul_ne_zero hK' hz)
  have hdiff : R - R' = vecMulVec (-(R *ᵥ a)) (b ᵥ* R') := by
    have e1 : R * (K' - z • (1 : Matrix ι ι ℂ)) * R' = R := by
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu', Matrix.mul_one]
    have e2 : R * (K - z • (1 : Matrix ι ι ℂ)) * R' = R' := by
      rw [Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
    have : R - R' = -(R * (K - K') * R') := by
      calc R - R' = R * (K' - z • (1 : Matrix ι ι ℂ)) * R' -
            R * (K - z • (1 : Matrix ι ι ℂ)) * R' := by rw [e1, e2]
        _ = -(R * (K - K') * R') := by
            simp only [Matrix.mul_sub, Matrix.sub_mul]; abel
    rw [this, hD, mul_vecMulVec_mul, neg_vecMulVec]
  have hbound : ∀ v, ‖T (G * (R - R')) v‖ ≤ cG * (2 * |z.im|⁻¹) * ‖v‖ := by
    intro v
    rw [← toE_toE]
    refine (hG _).trans ?_
    have : ‖T (R - R') v‖ ≤ 2 * |z.im|⁻¹ * ‖v‖ := by
      rw [map_sub, LinearMap.sub_apply]
      calc ‖T R v - T R' v‖ ≤ ‖T R v‖ + ‖T R' v‖ := norm_sub_le _ _
        _ ≤ |z.im|⁻¹ * ‖v‖ + |z.im|⁻¹ * ‖v‖ :=
            add_le_add (norm_resolvent_le hK hz v) (norm_resolvent_le hK' hz v)
        _ = 2 * |z.im|⁻¹ * ‖v‖ := by ring
    calc cG * ‖T (R - R') v‖ ≤ cG * (2 * |z.im|⁻¹ * ‖v‖) := mul_le_mul_of_nonneg_left this hcG
      _ = cG * (2 * |z.im|⁻¹) * ‖v‖ := by ring
  have htr : (G * R).trace - (G * R').trace = ∑ x, (1 : ℂ) * (G * (R - R')) x x := by
    rw [← trace_sub, ← Matrix.mul_sub]; simp [Matrix.trace]
  rw [htr]
  rw [hdiff, mul_vecMulVec] at hbound ⊢
  exact norm_weightedTrace_vecMulVec_le _ _ (fun _ => 1) (fun _ => by simp) (by positivity) hbound

/-- **Operator change of `Tr G R`**: for Hermitian `K, K'`, `Im z ≠ 0`, an operator bound `r` on
`(K' - z) - (K - z)` and `‖G v‖ ≤ c_G ‖v‖`:
`|Tr G(K - z)⁻¹ - Tr G(K' - z)⁻¹| ≤ |ι| c_G r/|Im z|²`. -/
theorem norm_trace_mul_sub_op {K K' : Matrix ι ι ℂ} (hK : K.IsHermitian)
    (hK' : K'.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) {r : ℝ} (hr : 0 ≤ r)
    (hd : ∀ v, ‖T ((K' - z • 1) - (K - z • 1)) v‖ ≤ r * ‖v‖) (G : Matrix ι ι ℂ) {cG : ℝ}
    (hcG : 0 ≤ cG) (hG : ∀ v, ‖T G v‖ ≤ cG * ‖v‖) :
    ‖(G * (K - z • (1 : Matrix ι ι ℂ))⁻¹).trace - (G * (K' - z • (1 : Matrix ι ι ℂ))⁻¹).trace‖ ≤
      Fintype.card ι * (cG * (|z.im|⁻¹ * r * |z.im|⁻¹)) := by
  have hop := toE_resolvent_sub_le hK hK' hz hz hr hd
  have hb : ∀ v, ‖T (G * ((K - z • (1 : Matrix ι ι ℂ))⁻¹ - (K' - z • (1 : Matrix ι ι ℂ))⁻¹)) v‖ ≤
      cG * (|z.im|⁻¹ * r * |z.im|⁻¹) * ‖v‖ := by
    intro v
    rw [← toE_toE]
    refine (hG _).trans ?_
    calc cG * ‖T ((K - z • (1 : Matrix ι ι ℂ))⁻¹ - (K' - z • (1 : Matrix ι ι ℂ))⁻¹) v‖
        ≤ cG * (|z.im|⁻¹ * r * |z.im|⁻¹ * ‖v‖) := mul_le_mul_of_nonneg_left (hop v) hcG
      _ = cG * (|z.im|⁻¹ * r * |z.im|⁻¹) * ‖v‖ := by ring
  rw [← trace_sub, ← Matrix.mul_sub]
  unfold Matrix.trace
  refine ((norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => norm_diag_le hb x)).trans
    (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Trace

section Pair

variable {p : Parameters} {i : ZMod p.n}

/-- **Grid-to-selected transfer of `Tr G R_η`**. Let `H_R, V, G`
be Hermitian, `‖C‖, ‖C*‖ ≤ c`, `‖G‖ ≤ c_G`, `ε₀ > 0`, `E` a nonpole energy with at most one
eigenvalue of `H_R` within `ε₀`, `e` any energy and `η > 0`. Then
`|Tr G R_η(K₀(E)) - Tr G R_η(K̂_e)| ≤ c_G (2/η) + 2W c_G ((c²/ε₀² + 1)|E - e|)/η²`. -/
theorem traceG_transfer (om : SplitState p i) (G : PairMatrix p i) (hH : om.1.IsHermitian)
    (hV : om.2.2.IsHermitian) (hG : G.IsHermitian) {ε₀ c cG : ℝ} (hε₀ : 0 < ε₀) (hc : 0 ≤ c)
    (hcG : 0 ≤ cG) (hC : ∀ v, ‖T om.2.1 v‖ ≤ c * ‖v‖) (hC' : ∀ w, ‖T om.2.1ᴴ w‖ ≤ c * ‖w‖)
    (hGn : ∀ v, ‖T G v‖ ≤ cG * ‖v‖) {E e η : ℝ}
    (hdet : (om.1 - (E : ℂ) • (1 : Matrix (ExteriorSite p i) (ExteriorSite p i) ℂ)).det ≠ 0)
    (hnear : (nearSet ε₀ hH E).card ≤ 1) (hη : 0 < η) :
    ‖(G * res (schurK0 p i om E) η G).trace - (G * res (hatK ε₀ om e) η G).trace‖ ≤
      cG * (2 / η) + 2 * p.W * (cG * ((c ^ 2 / ε₀ ^ 2 + 1) * |E - e|)) / η ^ 2 := by
  set z : ℂ := (η : ℂ) * Complex.I with hzdef
  have hzim : z.im = η := im_eta_I η
  have hz : z.im ≠ 0 := by rw [hzim]; exact hη.ne'
  have hA : (schurK0 p i om E + G).IsHermitian :=
    (WeightedTrace.schurK0_isHermitian hH hV E).add hG
  have hM : (hatK ε₀ om E + G).IsHermitian := (isHermitian_hatK ε₀ om hV E).add hG
  have hM' : (hatK ε₀ om e + G).IsHermitian := (isHermitian_hatK ε₀ om hV e).add hG
  obtain ⟨a, b, hab⟩ := physicalCoareaF_sub_truncF_rankOne hH om.2.1 om.2.2 hdet hnear
  have hD : schurK0 p i om E + G - (hatK ε₀ om E + G) = vecMulVec a b := by
    rw [← hab]; unfold schurK0 hatK; abel
  have h1 := norm_trace_mul_sub_rankOne hA hM hz a b hD G hcG hGn
  set r := (c ^ 2 / ε₀ ^ 2 + 1) * |E - e| with hr
  have hr0 : 0 ≤ r := by positivity
  have hdiff : ∀ v, ‖T ((hatK ε₀ om e + G - z • 1) - (hatK ε₀ om E + G - z • 1)) v‖ ≤
      r * ‖v‖ := by
    intro v
    have heq : (hatK ε₀ om e + G - z • (1 : PairMatrix p i)) - (hatK ε₀ om E + G - z • 1) =
        (truncF ε₀ om.1 om.2.1 om.2.2 e - truncF ε₀ om.1 om.2.1 om.2.2 E) -
          ((e - E : ℝ) : ℂ) • 1 := by
      unfold hatK; rw [Complex.ofReal_sub, sub_smul]; abel
    rw [heq, map_sub, LinearMap.sub_apply]
    have k1 := norm_truncF_sub_le hH om.2.1 om.2.2 hε₀ hc hC hC' e E v
    have k2 := norm_toE_smul_one (ι := PairSite p i) ((e - E : ℝ) : ℂ) v
    rw [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm] at k2
    rw [abs_sub_comm] at k1
    calc _ ≤ ‖T (truncF ε₀ om.1 om.2.1 om.2.2 e - truncF ε₀ om.1 om.2.1 om.2.2 E) v‖ +
            ‖T (((e - E : ℝ) : ℂ) • (1 : PairMatrix p i)) v‖ := norm_sub_le _ _
      _ ≤ c ^ 2 * (|E - e| / ε₀ ^ 2) * ‖v‖ + |E - e| * ‖v‖ := by rw [k2]; gcongr
      _ = r * ‖v‖ := by rw [hr]; field_simp
  have h2 := norm_trace_mul_sub_op hM hM' hz hr0 hdiff G hcG hGn
  have hcard : (Fintype.card (PairSite p i) : ℝ) = 2 * p.W := by
    exact_mod_cast BlockBand.Angular.FiberAngular.card_pairSite p i
  rw [hcard, hzim, abs_of_pos hη] at h2
  rw [hzim, abs_of_pos hη] at h1
  unfold res
  rw [← hzdef]
  set X := (G * (schurK0 p i om E + G - z • (1 : PairMatrix p i))⁻¹).trace
  set Y := (G * (hatK ε₀ om E + G - z • (1 : PairMatrix p i))⁻¹).trace
  set Z := (G * (hatK ε₀ om e + G - z • (1 : PairMatrix p i))⁻¹).trace
  have heq : X - Z = (X - Y) + (Y - Z) := by ring
  rw [heq]
  refine (norm_add_le _ _).trans ?_
  have e1 : cG * (2 * η⁻¹) = cG * (2 / η) := by ring
  have e2 : 2 * (p.W : ℝ) * (cG * (η⁻¹ * r * η⁻¹)) = 2 * p.W * (cG * r) / η ^ 2 := by
    field_simp
  linarith

end Pair

/-!
## The grid events
-/

variable (p : Parameters) (i : ZMod p.n)

/-- The **`Tr G R_η` tail event on a grid**: some grid energy `e ∈ Es` with a
good exterior (`SelectedLocalLaw.TraceGood`) at which `B < |Tr G R_η(K̂_e) + s d ā(e)²|`
(`d = 2W`, deterministic centre `ā(e) = conj (matchedA e)`, so that the event is Borel). -/
def IBPBadEvent (ε₀ A C χ₀ η B : ℝ) (Es : Finset ℝ) : Set (SplitState p i × PairMatrix p i) :=
  {x | ∃ e ∈ Es, x.1 ∈ TraceGood p i ε₀ A C χ₀ e ∧
    B < ‖(x.2 * res (hatK ε₀ x.1 e) η x.2).trace +
      (splitS p : ℂ) * ((2 * p.W : ℕ) : ℂ) * conj (matchedA e) ^ 2‖}

theorem measurable_traceG_hatK {ε₀ : ℝ} (hε₀ : 0 < ε₀) (e η : ℝ) :
    Measurable (fun x : SplitState p i × PairMatrix p i =>
      (x.2 * res (hatK ε₀ x.1 e) η x.2).trace) := by
  have h1 : Measurable (fun x : SplitState p i × PairMatrix p i =>
      truncF ε₀ x.1.1 x.1.2.1 x.1.2.2 e) := (measurable_truncF hε₀ e).comp measurable_fst
  have h2 : Measurable (fun x : SplitState p i × PairMatrix p i =>
      hatK ε₀ x.1 e + x.2 - ((η : ℂ) * Complex.I) • (1 : PairMatrix p i)) := by
    refine measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun b => ?_
    simp only [hatK, Matrix.sub_apply, Matrix.add_apply]
    exact ((((measurable_pi_apply b).comp ((measurable_pi_apply a).comp h1)).sub
      measurable_const).add
      ((measurable_pi_apply b).comp ((measurable_pi_apply a).comp measurable_snd))).sub
      measurable_const
  have h3 : Measurable (fun x : SplitState p i × PairMatrix p i => res (hatK ε₀ x.1 e) η x.2) :=
    measurable_inv_matrix.comp h2
  have h4 : Measurable (fun x : SplitState p i × PairMatrix p i =>
      x.2 * res (hatK ε₀ x.1 e) η x.2) :=
    (continuous_fst.matrix_mul continuous_snd).measurable.comp (measurable_snd.prodMk h3)
  exact continuous_id.matrix_trace.measurable.comp h4

variable {p i}

/-- **The `Tr G R_η` tail on a grid, conditional on the exterior**. Fixed
`0 < b < 1/2` (`c = min(1 - 2b, b)`), `V > 0`, constants `ε₁, δ_P, L` of `PairRegularBody c V`, a
bulk margin `κ` with `V ≤ √κ/2`, `A, C` and `n ≥ 1`; then `N₀` and an absolute `C₀ > 0`; for every
`p` with `p.b = b`, model, pair, splitting law with `d = 2W ≥ N₀`, `ε₀ > 0`, grid
`Es ⊆ bulkInterval κ`, `0 < η ≤ min(δ_P, 1)`, `0 ≤ χ₀ ≤ ε₁` with the local-law domain conditions
`d^{1/5} ≤ d η (3V/4)/π`, `η ≤ √s d^{A + 5}`, `d^{1/10}/η ≤ d`, `1 ≤ d η`, and `a > 0` with
`3 ≤ a² η³`, `u > 0`, `B ≥ u + (5 d^{1/10}/η + 5) + 3 d L(η + χ₀)`:
`splitLaw(IBPBadEvent) ≤ |Es| (C₀ √n M/u)ⁿ`, `M = a (yConst n + yConst (2n) + 1)^{1/n}`. -/
theorem splitLaw_ibpBad_le (hBridge : PairGUELawBridgeStatement) (hELG : ExternalLocalGUE)
    (hMDE : MDEBranchIdentification) (hLp : GaussianLpGradient) {b V ε₁ δP L κ : ℝ}
    (hreg : PairRegularBody (min (1 - 2 * b) b) V ε₁ δP L) (hV0 : 0 < V) (hL : 0 ≤ L)
    (hκ : 0 < κ) (hVκ : V ≤ Real.sqrt κ / 2) (A C : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∃ N₀ : ℕ, ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (p : Parameters), p.b = b →
      ∀ (model : p.GaussianRingModel) (i : ZMod p.n) (Pω : Measure (SplitState p i)),
      IsPairSplitting p i model (splitS p) Pω → N₀ ≤ 2 * p.W → ∀ ε₀ : ℝ, 0 < ε₀ →
      ∀ (Es : Finset ℝ), (∀ e ∈ Es, e ∈ bulkInterval κ) →
        ∀ η χ₀ : ℝ, 0 < η → η ≤ δP → η ≤ 1 → 0 ≤ χ₀ → χ₀ ≤ ε₁ →
        ((2 * p.W : ℕ) : ℝ) ^ (1 / 5 : ℝ) ≤ ((2 * p.W : ℕ) : ℝ) * η * (3 * V / 4 / Real.pi) →
        η ≤ Real.sqrt (splitS p) * ((2 * p.W : ℕ) : ℝ) ^ (A + 1 / (1 / 5 : ℝ)) →
        ((2 * p.W : ℕ) : ℝ) ^ (1 / 10 : ℝ) / η ≤ ((2 * p.W : ℕ) : ℝ) →
        1 ≤ ((2 * p.W : ℕ) : ℝ) * η →
        ∀ a u B : ℝ, 0 < a → 3 ≤ a ^ 2 * η ^ 3 → 0 < u →
        u + (5 * ((2 * p.W : ℕ) : ℝ) ^ (1 / 10 : ℝ) / η + 5) +
          3 * ((2 * p.W : ℕ) : ℝ) * (L * (η + χ₀)) ≤ B →
        splitLaw p i Pω (IBPBadEvent p i ε₀ A C χ₀ η B Es) ≤
          Es.card * ENNReal.ofReal ((C₀ * Real.sqrt n *
            (a * (yConst n + yConst (2 * n) + 1) ^ ((n : ℝ)⁻¹)) / u) ^ (n : ℝ)) := by
  obtain ⟨N₀, -, hloc⟩ := gue_trace_bad_le hBridge hELG hMDE A C (1 / 5) (1 / 10) ((n : ℝ) + 3)
    (by norm_num) (by norm_num) (by positivity)
  obtain ⟨C₀, hC₀, htail⟩ := section_tail hLp
  refine ⟨N₀, C₀, hC₀, fun p hpb model i Pω hPω hN ε₀ hε₀ Es hEs η χ₀ hη hηδ hη1 hχ0 hχ₁ hdom
    hz hℓ hdη a u B ha ha3 hu hB => ?_⟩
  set bnd : ℝ≥0∞ := ENNReal.ofReal ((C₀ * Real.sqrt n *
    (a * (yConst n + yConst (2 * n) + 1) ^ ((n : ℝ)⁻¹)) / u) ^ (n : ℝ)) with hbnd
  set dR : ℝ := ((2 * p.W : ℕ) : ℝ) with hdR
  have hW1 : (1 : ℝ) ≤ p.W := by exact_mod_cast p.W_pos
  have hd1 : 1 ≤ dR := by rw [hdR]; push_cast; linarith
  have hd0 : 0 < dR := by linarith
  have hs := BlockBand.Angular.PairCoareaBridge.splitS_pos p
  have hsp : splitS p = min (1 - 2 * b) b := splitS_eq hpb
  have hs1 : splitS p ≤ 1 := by
    have := p.b_lt_half
    rw [hsp]; exact (min_le_right _ _).trans (by rw [← hpb]; linarith)
  have hcardN : Fintype.card (PairSite p i) = 2 * p.W :=
    BlockBand.Angular.FiberAngular.card_pairSite p i
  set z : ℂ := ((0 : ℝ) : ℂ) + Complex.I * η with hzdef
  have hzim : z.im = η := by simp [z]
  have hznorm : ‖z‖ = η := by
    simp only [z, Complex.ofReal_zero, zero_add, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη]
  have hzeq : ((η : ℂ) * Complex.I) = z := by rw [hzdef]; push_cast; ring
  -- the time and the failure exponent
  set t := pairTime p (splitS p) with htdef
  have ht : (t : ℝ) = splitS p / (2 * (p.W : ℝ)) := by
    rw [htdef, pairTime, Real.coe_toNNReal _ (by positivity)]
  have htd : (t : ℝ) * (Fintype.card (PairSite p i) : ℝ) ≤ 1 := by
    rw [hcardN, ht]; push_cast
    rw [div_mul_cancel₀ _ (by positivity)]; exact hs1
  set β : ℝ := dR ^ (-((n : ℝ) + 3)) with hβdef
  have hβ0 : 0 ≤ β := Real.rpow_nonneg hd0.le _
  have hinv : dR⁻¹ ≤ η := by
    calc dR⁻¹ ≤ dR⁻¹ * (dR * η) := le_mul_of_one_le_right (inv_nonneg.2 hd0.le) hdη
      _ = η := by field_simp
  have hinv1 : dR⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hd1
  have hinv0 : 0 ≤ dR⁻¹ := inv_nonneg.2 hd0.le
  have hβeq : β = (dR⁻¹) ^ (n + 3) := by
    rw [hβdef, Real.rpow_neg hd0.le, show ((n : ℝ) + 3) = ((n + 3 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast, inv_pow]
  have hβ1 : β ≤ η ^ n := by
    rw [hβeq]
    exact (pow_le_pow_of_le_one hinv0 hinv1 (by omega)).trans (pow_le_pow_left₀ hinv0 hinv n)
  have hβ2 : (Fintype.card (PairSite p i) : ℝ) * β ≤ η ^ 2 := by
    rw [hcardN, ← hdR, hβeq]
    have e : dR * dR⁻¹ ^ (n + 3) = dR⁻¹ ^ (n + 2) := by
      rw [pow_succ _ (n + 2), ← mul_assoc, mul_comm dR, mul_assoc, mul_inv_cancel₀ hd0.ne',
        mul_one]
    rw [e]
    exact (pow_le_pow_of_le_one hinv0 hinv1 (by omega)).trans (pow_le_pow_left₀ hinv0 hinv 2)
  -- the sections
  set S : ℝ → Set (SplitState p i × PairMatrix p i) := fun e =>
    {x | B < ‖(x.2 * res (hatK ε₀ x.1 e) η x.2).trace +
      (splitS p : ℂ) * ((2 * p.W : ℕ) : ℂ) * conj (matchedA e) ^ 2‖}
  have hsub : IBPBadEvent p i ε₀ A C χ₀ η B Es ⊆ ⋃ e ∈ Es,
      {x | x ∈ S e ∧ x.1 ∈ TraceGood p i ε₀ A C χ₀ e} := by
    rintro x ⟨e, he, hg, hb⟩
    exact Set.mem_biUnion he ⟨hb, hg⟩
  have hone : ∀ e ∈ Es, splitLaw p i Pω {x | x ∈ S e ∧ x.1 ∈ TraceGood p i ε₀ A C χ₀ e} ≤
      bnd := by
    intro e he
    have hS : MeasurableSet (S e) :=
      measurableSet_lt measurable_const
        (((measurable_traceG_hatK p i hε₀ e η).add measurable_const).norm)
    have := prod_inter_le_of_section Pω (gueMeasure (PairSite p i) t) hS
      (Good := TraceGood p i ε₀ A C χ₀ e) (a := bnd) (fun om hom => by
        obtain ⟨hV, hnrm, hchi⟩ := hom
        have hK := isHermitian_hatK ε₀ om hV e
        obtain ⟨hVμ0, hμ1⟩ := conj_matchedA_bounds hκ (hEs e he)
        have hVμ : V ≤ (conj (matchedA e)).im := hVκ.trans hVμ0
        rw [hsp] at hchi
        have hzim0 : 0 ≤ z.im := by rw [hzim]; exact hη.le
        have hzδ : ‖z‖ ≤ δP := by rw [hznorm]; exact hηδ
        obtain ⟨him, hroot, hnear⟩ := pairDyson_near hreg hL ((hη.le).trans hηδ) hK hVμ hμ1
          hchi hχ₁ hzim0 hzδ
        have hm2 := ((hreg p i _ hK _ hVμ hμ1 (hchi.trans hχ₁)).1 z hzim0 hzδ).2.1
        rw [hznorm] at hnear
        set m := pairDyson p i (hatK ε₀ om e) (min (1 - 2 * b) b) z
        have hm : 0 < m.im := lt_of_lt_of_le (by positivity) him
        have hdom' : dR ^ (1 / 5 : ℝ) ≤ dR * η * (m.im / Real.pi) :=
          hdom.trans (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right him Real.pi_pos.le)
            (mul_pos hd0 hη).le)
        have hz' : ‖((0 : ℝ) : ℂ) + Complex.I * η‖ ≤
            Real.sqrt (splitS p) * dR ^ (A + 1 / (1 / 5 : ℝ)) := by
          rw [← hzdef, hznorm]; exact hz
        rw [← hsp] at hroot
        have hbad := hloc p i hN (splitS p) hs (hatK ε₀ om e) hK hnrm 0 η hη m hm
          (by rw [← hzdef]; convert hroot using 3) hdom' hz'
        have hBad : gueMeasure (PairSite p i) t (resBad (hatK ε₀ om e) η (dR ^ (1 / 10 : ℝ)) m) ≤
            ENNReal.ofReal β := by
          refine (measure_mono fun G hG => ?_).trans hbad
          simp only [resBad, Set.mem_ofPred_eq] at hG ⊢
          rw [res, hzeq, hcardN] at hG
          exact hG
        -- the centre
        set q : ℂ := (splitS p : ℂ) * ((2 * p.W : ℕ) : ℂ) * conj (matchedA e) ^ 2 with hq
        have hσ : ‖(t : ℂ) * ((Fintype.card (PairSite p i) : ℂ) * m) ^ 2 - q‖ ≤
            3 * dR * (L * (η + χ₀)) := by
          have htC : (t : ℂ) = ((splitS p / (2 * (p.W : ℝ)) : ℝ) : ℂ) := by
            rw [← ht]
          have e1 : (t : ℂ) * ((Fintype.card (PairSite p i) : ℂ) * m) ^ 2 - q =
              (splitS p : ℂ) * ((2 * p.W : ℕ) : ℂ) *
                ((m - conj (matchedA e)) * (m + conj (matchedA e))) := by
            rw [htC, hcardN, hq]
            have hW0 : (p.W : ℂ) ≠ 0 := by exact_mod_cast p.W_pos.ne'
            push_cast
            field_simp
            ring
          rw [e1, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos hs, Complex.norm_natCast]
          have h3 : ‖m + conj (matchedA e)‖ ≤ 3 := by
            refine (norm_add_le _ _).trans ?_
            linarith
          have hLn : 0 ≤ L * (η + χ₀) := by positivity
          calc splitS p * dR * (‖m - conj (matchedA e)‖ * ‖m + conj (matchedA e)‖)
              ≤ 1 * dR * (L * (η + χ₀) * 3) := by
                gcongr
            _ = 3 * dR * (L * (η + χ₀)) := by ring
        have hℓ0 : 0 ≤ dR ^ (1 / 10 : ℝ) := Real.rpow_nonneg hd0.le _
        have hd1' : 1 ≤ (Fintype.card (PairSite p i) : ℝ) := by rw [hcardN]; exact hd1
        have hℓ' : dR ^ (1 / 10 : ℝ) / η ≤ (Fintype.card (PairSite p i) : ℝ) := by
          rw [hcardN]; exact hℓ
        have hB' : u + (5 * dR ^ (1 / 10 : ℝ) / η + 5) + 3 * dR * (L * (η + χ₀)) ≤ B := hB
        exact htail n hn (PairSite p i) (hatK ε₀ om e) hK η hη hη1 t hd1' htd m hm2
          (dR ^ (1 / 10 : ℝ)) hℓ0 hℓ' β hβ0 hBad hβ1 hβ2 a ha ha3 u _ B q hu hσ hB')
    rwa [measure_univ_of_isPairSplitting p i hPω, mul_one] at this
  calc splitLaw p i Pω (IBPBadEvent p i ε₀ A C χ₀ η B Es)
      ≤ ∑ e ∈ Es, splitLaw p i Pω {x | x ∈ S e ∧ x.1 ∈ TraceGood p i ε₀ A C χ₀ e} :=
        (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
    _ ≤ ∑ _e ∈ Es, bnd := Finset.sum_le_sum hone
    _ = Es.card * bnd := by rw [Finset.sum_const, nsmul_eq_mul]

end BlockBand.DeterminantScore.SelectedIBPHolds
