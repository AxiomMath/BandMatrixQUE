module

public import BlockBand.Center.SmoothCenterW0
public import BlockBand.Center.CenterSplitting
public import BlockBand.Center.CenterCyclic

/-!
# The physical center bound through the thresholded smooth center

`physicalCenter_holds_of_W0` proves the physical center bound for `pairCenterFamily0` from the
rank location bound, the thresholded smooth center `SmoothCenterW0 cst0`, the energy primitive
and the divergence isometry; the simultaneous splitting and the cyclic invariance are
constructed in the proof.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Center

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.QUE BlockBand.QUE.Fourier BlockBand.Model.Construction
open BlockBand.QUE.PairResidual
open scoped ENNReal NNReal Interval

/-- **The physical center bound** (`PhysicalCenterContract`), through the thresholded smooth
center `SmoothCenterW0 cst0`.

*Law.* The exact pair law (`extendedPairMeasure`, density
`(n/2)(p_{αi} + p_{α,i+1})`) on the witness extension of `pairCenterFamily0`, whose center is the
Dyson center `j_i(λ_α)` built from `H - G_i` (`pairCenterFamily0_isDyson`),
transported to the exact simultaneous splitting of `pcSplittingExists_holds`.
*Domain.* `0 < b < 1/2`, `θ > 0` (`ϑ = min(θ, 1/4)`; `θ ≤ 0` would include edge ranks and is
not claimed), `T` arbitrary.
*Norms.* Real second moment of the center under the pair law; internally `L⁴` moments of the
smooth center and of its shift derivatives, `L⁴` rank location, `L²` divergence.
*Quantifier order / uniformity.* `b, θ, T` first; then `B` and `W₀` (from `ρ`, the constant `C₄`
and threshold `W₀` of `SmoothCenterW0` at `q = 4`, `C₂` of the replacement field at `D = 2`, the
rank-location constant at `q = 4` and `s(b)`), then `n, W`, the model, `α`, `i`.
*Order of limits.* None (fixed-`(n, W)` inequality with uniform constants).
*Hypotheses.* `RankLocationContract` (`location`, physical law, `q = 4`);
`SmoothCenterW0 cst0` (fields `bounded`, `measurable`, `smooth`, `moment` /
`derivative` at `q = 4` for `W > W₀`, `replacement` at `D = 2`);
`PcEnergyPrimitive` and `PcDivergenceIsometry` (proved as `pcEnergyPrimitive_holds` and
`pcDivergenceIsometry_holds`).
*Used.* `pcSplittingExists_holds`, `pcCenterCyclic_holds` and `pc_divergence_le`. -/
theorem physicalCenter_holds_of_W0 (hrank : RankLocationContract)
    (hsmooth : SmoothCenterW0 cst0) (henergy : PcEnergyPrimitive)
    (hiso : PcDivergenceIsometry) :
    ∀ (b θ T : ℝ) (hb : 0 < b) (hb' : b < 1 / 2), 0 < θ →
      PhysicalCenterContract b θ T hb hb' pairCenterFamily0 := by
  intro b θ T hb hb' hθ
  set ϑ : ℝ := min θ (1 / 4) with hϑdef
  have hϑ0 : 0 < ϑ := lt_min hθ (by norm_num)
  have hϑ1 : ϑ < 1 / 2 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  obtain ⟨ρ, κ', hρ0, hρ1, _hκ', Φ, hbdd, hmeas, hsm, _hsupp, _hagree, hmom, hrepl⟩ :=
    hsmooth b hb hb' ϑ T hϑ0 hϑ1
  obtain ⟨C4, W4, hC4⟩ := hmom 4 (by norm_num)
  obtain ⟨CD, hCD⟩ := hrepl 2
  obtain ⟨CL, hCL⟩ := hrank.location b hb hb' T ϑ hϑ0 hϑ1 4 (by norm_num)
  set c4 : ℝ := max C4 0 with hc4
  set cd : ℝ := max CD 0 with hcd
  set cl : ℝ := max CL 0 with hcl
  set T' : ℝ := max T 0 with hT'
  set V : ℝ := (4 * c4 ^ 4 / min (1 - 2 * b) b + 2 * (4 * c4 ^ 4) * (2 / (1 - ρ ^ 2))) +
    2 * (4 * c4 ^ 4) * T' with hVdef
  have hc40 : 0 ≤ c4 := le_max_right _ _
  have hcd0 : 0 ≤ cd := le_max_right _ _
  have hcl0 : 0 ≤ cl := le_max_right _ _
  have hT'0 : 0 ≤ T' := le_max_right _ _
  have hsb : 0 < min (1 - 2 * b) b := lt_min (by linarith) hb
  have hρ2 : 0 < 1 - ρ ^ 2 := by nlinarith
  have hV0 : 0 ≤ V := by positivity
  refine ⟨Real.pi * (cl + 1) * Real.sqrt V + cd * Real.sqrt T', W4, by positivity, ?_⟩
  intro n W hn hW hnT hW4 p model α hα i
  have hpb : p.b = b := rfl
  have hsplitS : splitS p = min (1 - 2 * b) b := rfl
  have hnTp : (p.n : ℝ) ≤ T * p.W := hnT
  have hW4p : W4 < (p.W : ℝ) := hW4
  clear_value p
  have hαϑ : IsBulkRank p ϑ α := pc_bulk_mono (min_le_left _ _) hα
  obtain ⟨S, hS⟩ := pcSplittingExists_holds p model
  have hP : IsProbabilityMeasure S.X.P := csm_isProb_ext S.X
  have hWpos : (0 : ℝ) < p.W := pc_W_pos
  have hnpos : (0 : ℝ) < p.n := by exact_mod_cast p.n_pos
  have hnT' : (p.n : ℝ) ≤ T' * p.W :=
    hnTp.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hWpos.le)
  set φ : ZMod p.n → p.SiteMatrix → ℝ → ℝ := Φ p α with hφdef
  -- moment data with nonnegative constants (for `W > W₄`)
  have hmom' : ∀ (e g : ZMod p.n) (E : ℝ),
      eLpNorm (fun ω => φ e (S.X.Hm ω - embedPair p e (S.G e ω)) E) (ENNReal.ofReal 4) S.X.P ≤
          ENNReal.ofReal (c4 / p.W) ∧
        (g ≠ e → eLpNorm (fun ω => deriv (fun t : ℝ =>
            φ e (S.X.Hm ω - embedPair p e (S.G e ω) + (t : ℂ) • pairProjector p g) E) 0)
            (ENNReal.ofReal 4) S.X.P ≤
          ENNReal.ofReal (c4 * (ρ ^ edgeDistance p e g + (p.W : ℝ) ^ (-(1 / 2 : ℝ))))) := by
    intro e g E
    obtain ⟨h1, h2⟩ := hC4 p hpb hnTp hW4p model S hS α hαϑ e g E
    refine ⟨h1.trans (ENNReal.ofReal_le_ofReal ?_), fun hge => (h2 hge).trans
      (ENNReal.ofReal_le_ofReal ?_)⟩
    · exact div_le_div_of_nonneg_right (le_max_left _ _) hWpos.le
    · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  -- the divergence bound
  have hdiv : ∀ E : ℝ, Integrable (fun ω => (((2 * (p.W : ℝ)) ^ 2 / splitS p) *
        ∑ g, S.ξ g ω * φ g (S.X.Hm ω - embedPair p g (S.G g ω)) E ^ 2) ^ 2) S.X.P ∧
      (∫ ω, (((2 * (p.W : ℝ)) ^ 2 / splitS p) *
        ∑ g, S.ξ g ω * φ g (S.X.Hm ω - embedPair p g (S.G g ω)) E ^ 2) ^ 2 ∂S.X.P) ≤
        V * p.n / (p.W : ℝ) ^ 2 := by
    intro E
    have h := pc_divergence_le hiso S hS φ (hbdd p α) (hmeas p α) (hsm p α) hc40 hρ0 hρ1 hnT'
      hmom' E
    rw [hsplitS] at h
    rw [hsplitS]
    exact h
  -- the random-energy bound
  set σi : ℝ := (2 * (p.W : ℝ)) ^ 2 / splitS p with hσi
  set D : S.X.Ω × ℝ → ℝ := fun z =>
    σi * ∑ g, S.ξ g z.1 * φ g (S.X.Hm z.1 - embedPair p g (S.G g z.1)) z.2 ^ 2 with hDdef
  have hDm : Measurable D := by
    refine measurable_const.mul (Finset.measurable_sum _ fun g _ => ?_)
    refine ((S.measurable_ξ g).comp measurable_fst).mul ?_
    exact ((hmeas p α g).comp (((pc_measurable_res S g).comp measurable_fst).prodMk
      measurable_snd)).pow_const 2
  set e₀ : ℝ := classicalLocation p α with he₀
  set Λ : S.X.Ω → ℝ := fun ω => physicalOrderedEigenvalue p (S.X.Hm ω) α with hΛdef
  have hΛm : Measurable Λ := (measurable_physicalOrderedEigenvalue p α).comp S.X.measurable_Hm
  set M : ℝ := (cl + 1) / (p.n * Real.sqrt p.W) with hMdef
  have hM : 0 < M := by positivity
  set K : ℝ := Real.sqrt (V * p.n) / p.W with hKdef
  have hK : 0 ≤ K := by positivity
  have hterm : ∫⁻ x, ‖Λ x - e₀‖ₑ ^ 4 ∂S.X.P ≤ ENNReal.ofReal (M ^ 4) := by
    have hloc := hCL p hpb hnTp model MassLaw.physical α hαϑ
    have hmeasH : Measurable (fun H : p.SiteMatrix => physicalOrderedEigenvalue p H α - e₀) :=
      (measurable_physicalOrderedEigenvalue p α).sub measurable_const
    have heq : eLpNorm (fun x => Λ x - e₀) (ENNReal.ofReal 4) S.X.P =
        eLpNorm (fun H : p.SiteMatrix => physicalOrderedEigenvalue p H α - e₀) (ENNReal.ofReal 4)
          (model.law : Measure p.SiteMatrix) := by
      rw [← S.X.map_eq, eLpNorm_map_measure (by rw [S.X.map_eq]; exact hmeasH.aestronglyMeasurable)
        S.X.measurable_Hm.aemeasurable]
      rfl
    have hbound : eLpNorm (fun x => Λ x - e₀) (ENNReal.ofReal ((4 : ℕ) : ℝ)) S.X.P ≤
        ENNReal.ofReal M := by
      rw [show ((4 : ℕ) : ℝ) = 4 by norm_num, heq]
      refine hloc.trans (ENNReal.ofReal_le_ofReal ?_)
      exact div_le_div_of_nonneg_right ((le_max_left _ _).trans (by linarith)) (by positivity)
    exact pc_lintegral_pow_le_of_eLpNorm (hΛm.sub measurable_const).aestronglyMeasurable
      (by norm_num) hM.le hbound
  have hDk : ∀ E, ∫⁻ x, ‖D (x, E)‖ₑ ^ 2 ∂S.X.P ≤ ENNReal.ofReal (K ^ 2) := by
    intro E
    obtain ⟨hi, hb2⟩ := hdiv E
    refine pc_lintegral_sq_le_of_integral (f := fun x => D (x, E)) hi (hb2.trans (le_of_eq ?_))
    rw [hKdef, div_pow, Real.sq_sqrt (by positivity)]
  have hre := pc_terminal_energy_le S.X.P D hDm Λ hΛm e₀ M K hM hK hterm hDk
  -- the cyclic sum, the energy primitive and replacement
  have hsum := pc_energy_sum henergy S hS α φ (hbdd p α) (hmeas p α) e₀
  set LHS : ZMod p.n → ℝ := fun g => ∫ ω, (pairCenterFamily0 p model α g).center ω ^ 2
    ∂extendedPairMeasure p α g (pairCenterFamily0 p model α g).X.P
      (pairCenterFamily0 p model α g).X.Hm with hLHS
  have hrep : ∀ g, LHS g ≤ (∫ ω, φ g (S.X.Hm ω - embedPair p g (S.G g ω))
      (physicalOrderedEigenvalue p (S.X.Hm ω) α) ^ 2 ∂extendedPairMeasure p α g S.X.P S.X.Hm) +
        cd / (p.W : ℝ) ^ 2 := by
    intro g
    refine (pc_replace_le α g (φ g) (hmeas p α g) (hbdd p α g) (CD * (p.W : ℝ) ^ (-(2 : ℝ)))
      (fun X G hG => hCD p hpb hnTp model α hαϑ g X G hG) S hS).trans ?_
    gcongr
    rw [Real.rpow_neg hWpos.le, Real.rpow_two, ← div_eq_mul_inv]
    exact max_le (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)) (by positivity)
  have hcycl : ∀ g, LHS g = LHS i := fun g => pcCenterCyclic_holds p model α g i
  have hnL : (p.n : ℝ) * LHS i ≤ (p.n : ℝ) / 2 * |∫ x, (∫ E in e₀..Λ x, D (x, E)) ∂S.X.P| +
      (p.n : ℝ) * (cd / (p.W : ℝ) ^ 2) := by
    have h1 : (p.n : ℝ) * LHS i = ∑ g, LHS g := by
      rw [Finset.sum_congr rfl fun g _ => hcycl g, Finset.sum_const, Finset.card_univ, ZMod.card,
        nsmul_eq_mul]
    rw [h1]
    calc ∑ g, LHS g ≤ ∑ g, ((∫ ω, φ g (S.X.Hm ω - embedPair p g (S.G g ω))
          (physicalOrderedEigenvalue p (S.X.Hm ω) α) ^ 2 ∂extendedPairMeasure p α g S.X.P S.X.Hm) +
            cd / (p.W : ℝ) ^ 2) := Finset.sum_le_sum fun g _ => hrep g
      _ = (p.n : ℝ) / 2 * (∫ x, (∫ E in e₀..Λ x, D (x, E)) ∂S.X.P) +
            (p.n : ℝ) * (cd / (p.W : ℝ) ^ 2) := by
          rw [Finset.sum_add_distrib, hsum, Finset.sum_const, Finset.card_univ, ZMod.card,
            nsmul_eq_mul]
      _ ≤ _ := by
          gcongr
          exact le_abs_self _
  have hfinal : LHS i ≤ Real.pi * M * K + cd / (p.W : ℝ) ^ 2 := by
    have h2 : (p.n : ℝ) * LHS i ≤ (p.n : ℝ) * (Real.pi * M * K + cd / (p.W : ℝ) ^ 2) := by
      refine hnL.trans ?_
      have := mul_le_mul_of_nonneg_left hre (show (0 : ℝ) ≤ p.n / 2 by positivity)
      nlinarith
    exact le_of_mul_le_mul_left h2 hnpos
  refine hfinal.trans ?_
  have halg := pc_final_algebra (n := (p.n : ℝ)) (W := (p.W : ℝ)) (cl := cl) (cd := cd) (V := V)
    (T' := T') hnpos hWpos hcl0 hcd0 hV0 hT'0 hnT'
  refine le_trans (le_of_eq ?_) halg
  rw [hMdef, hKdef]

end BlockBand.Center
