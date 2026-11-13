module

public import BlockBand.DeterminantScore.MinorTailRow

/-!
# The physical minor tail under the pair law

`tail_holds (hC : CoareaContract) (hNS : NegativeSpreadStatement)`: the `tail` field of
`PhysicalMinorTailStatement`: for `b, κ`, every `c > 0`, `q > 0` there is `C` with
`P♯(𝒢_α, V_B ≤ A) ≤ C((A + W)/W²)^{q/(q+1)}` for every `A ≥ 0`, `n ≥ 4`, `W`, model, rank,
pair, splitting law, pair frame, measurable unit eigenvector `w(θ)` of `K` and minor frame. The
constant is `C = 3(2 + 2/s_b + C_q⁺ c^{-q})`, `s_b = min(1 - 2b, b)`, `C_q⁺ = max(C_q, 0)` with
`C_q` the constant of the `inverse_moment` field of `NegativeSpreadStatement` at exponent `q`.
`physicalMinorTail_of_inverseSpread`: `PhysicalMinorTailStatement` from `CoareaContract`,
`NegativeSpreadStatement` and the second clause (`inverse_spread`).

Proof of the first clause, at fixed outer data `θ` with Hermitian blocks and unit `v` (almost sure
under the pair law), with the splitting parameter `a > 0`:
* `1{𝒢, V_B ≤ A} ≤ a⁻¹ 1{V_B ≤ A} U + a^q 1_𝒢 U^{-q}` on `{det M ≠ 0}` (`one_le_split`,
  `invSq_pos`), the elementary (Young) form of Hölder's inequality;
* `gue_tail` (from the sibling module on the row tail): `E_{G'}[det² 1{sector α} 1{V_B ≤ A} U] ≤ (2A + t⁻¹) Σ 𝔷_ℓ`
  (the signed row spread, three restored sectors);
* `inner_neg`: on `𝒢_α`, `⟨U⟩_θ ≥ cW² > 0`, so the sector is attained, `det² U` is integrable and
  `E_{G'}[det² 1{sector α} U^{-q}] = 𝔷_α E_{sector}U^{-q} ≤ 𝔷_α C_q (cW²)^{-q}`
  (`inverse_moment` of `NegativeSpreadStatement`, transported to `G_{d-1}(t)` coordinates);
* `PhysicalColumn.pairExpect_le` (cited): the three restored pair laws have mass `≤ 1`; `t⁻¹ = 2W/s_b`;
  `a = W²((A+W)/W²)^{1/(q+1)}` (`tail_constant`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.MinorTail

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Layers BlockBand.Angular.FiberAngular
open BlockBand.DeterminantScore BlockBand.DeterminantScore.Sector
open BlockBand.DeterminantScore.PhysicalColumn BlockBand.DeterminantScore.NegativeSpread
open scoped NNReal ENNReal

/-!
## Sector weights in `G_m(t)` coordinates
-/

section SectorCoord

variable {m : ℕ}

theorem sectorDetSq_re_eq {K : Matrix (Fin m) (Fin m) ℂ} (hK : K.IsHermitian) {n α : ℕ}
    (hn : n ≤ α) (x : HermCoord m → ℝ) :
    (sectorDetSq K (α - n) x).re = secW n α (K + hermOfCoord x) := by
  have him := BlockBand.Angular.DetFactor.det_im_eq_zero (hK.add (isHermitian_hermOfCoord x))
  unfold sectorDetSq secW InSector
  by_cases h : negativeCount (K + hermOfCoord x) = α - n
  · have h' : negativeCount (K + hermOfCoord x) + n = α := by omega
    have h'' : α - n + n = α := by omega
    simp only [h, ↓reduceIte, h'', mul_one, Complex.normSq_apply, sq, Complex.mul_re, him]
    ring
  · have h' : ¬ negativeCount (K + hermOfCoord x) + n = α := by omega
    simp [h, h']

/-- Transfer of a sector-weighted `GUE` integral to `G_m(t)` coordinates. -/
theorem lintegral_secW_eq {K : Matrix (Fin m) (Fin m) ℂ} (hK : K.IsHermitian) {n α : ℕ}
    (hn : n ≤ α) (t : ℝ≥0) {g : Matrix (Fin m) (Fin m) ℂ → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ G, ENNReal.ofReal (secW n α (K + G)) * g (K + G) ∂gueMeasure (Fin m) t) =
      ∫⁻ x, ENNReal.ofReal (sectorDetSq K (α - n) x).re * g (K + hermOfCoord x)
        ∂hermGaussian m t := by
  have hm : Measurable fun G : Matrix (Fin m) (Fin m) ℂ =>
      ENNReal.ofReal (secW n α (K + G)) * g (K + G) :=
    (ENNReal.measurable_ofReal.comp ((measurable_secW n α).comp (measurable_const_add K))).mul
      (hg.comp (measurable_const_add K))
  rw [← map_hermOfCoord_hermGaussian, lintegral_map hm continuous_hermOfCoord.measurable]
  refine lintegral_congr fun x => ?_
  rw [sectorDetSq_re_eq hK hn]

theorem ae_isHermitian_gue (t : ℝ≥0) : ∀ᵐ G ∂gueMeasure (Fin m) t, G.IsHermitian := by
  have hS : MeasurableSet {G : Matrix (Fin m) (Fin m) ℂ | G.IsHermitian} :=
    (isClosed_eq (continuous_id.matrix_conjTranspose) continuous_id).measurableSet
  rw [← map_hermOfCoord_hermGaussian, ae_map_iff continuous_hermOfCoord.measurable.aemeasurable hS]
  exact ae_of_all _ fun x => isHermitian_hermOfCoord x

end SectorCoord

variable {p : Parameters} {i : ZMod p.n}

theorem detFactor_eq_zNat (α : Fin p.N) (s : ℝ) (U : FrameMap p i) (θ : OuterData p i) :
    detFactor p i α s U θ.1 θ.2.1 θ.2.2 = zNat s U α.val θ := by
  unfold detFactor zNat
  refine lintegral_congr fun G' => ?_
  change _ = ENNReal.ofReal (Complex.normSq (frameM p i U θ.1 θ.2.1 θ.2.2 G').det *
    (if negativeCount (frameM p i U θ.1 θ.2.1 θ.2.2 G') +
      negativeCount (θ.1.1 - (θ.2.1 : ℂ) • 1) = α.val then 1 else 0))
  split_ifs <;> simp

/-- **Fixed-`θ` inverse spread on the good event** (the negative spread bound integrated at fixed
outer data): if `⟨U⟩_θ ≥ L > 0`, then `E_{G'}[det² 1{sector α} U^{-q}] ≤ C_q L^{-q} 𝔷_α(θ)`. -/
theorem inner_neg {q C : ℝ}
    (hCq : ∀ (m : ℕ) (t : ℝ≥0) (K : Matrix (Fin m) (Fin m) ℂ) (ℓ : ℕ), 0 < t →
      K.IsHermitian → 0 < (sectorMass m t K ℓ).re →
        (∫⁻ x, ENNReal.ofReal ((sectorInvSq K x)⁻¹ ^ q) ∂sectorLaw m t K ℓ) ≤
          ENNReal.ofReal C * ((∫⁻ x, ENNReal.ofReal (sectorInvSq K x) ∂sectorLaw m t K ℓ) ^ q)⁻¹)
    (hq : 0 < q) (α : Fin p.N) (s : ℝ) (U : FrameMap p i) {θ : OuterData p i}
    (hR : θ.1.1.IsHermitian) (hV : θ.1.2.2.IsHermitian) (ht : 0 < pairTime p s) {L : ℝ}
    (hL : 0 < L) (hgood : L ≤ sectorAvg α s U (invSqTrace U θ) θ) :
    (∫⁻ G', ENNReal.ofReal (sectorWeight α U θ G') *
        ENNReal.ofReal ((invSqTrace U θ G')⁻¹ ^ q) ∂gueMeasure (FrameIndex p) (pairTime p s)) ≤
      ENNReal.ofReal C * (ENNReal.ofReal L ^ q)⁻¹ * zNat s U α.val θ := by
  set K := outerKs U θ
  have hK : K.IsHermitian := outerKs_isHermitian U hR hV
  set n := nR θ
  set t := pairTime p s
  have hM : ∀ G', outerM U θ G' = K + G' := outerM_eq U θ
  -- if the exterior already has more than `α` negative eigenvalues, the sector is empty
  by_cases hn : n ≤ α.val
  swap
  · refine le_trans (le_of_eq ?_) zero_le
    refine lintegral_eq_zero_of_ae_eq_zero (Filter.Eventually.of_forall fun G' => ?_)
    have : ¬ negativeCount (outerM U θ G') + n = α.val := by omega
    simp [sectorWeight_eq, secW, this, n]
  set ℓ := α.val - n
  set Z := (sectorMass _ t K ℓ).re
  have hZnat : zNat s U α.val θ = ENNReal.ofReal Z := by
    unfold zNat
    have h := lintegral_secW_eq hK hn t (g := fun _ => 1) measurable_const
    simp only [mul_one] at h
    simp_rw [hM]
    rw [h, lintegral_sectorDetSq hK]
  have hsZ : sectorZ α s U θ = max Z 0 := by
    unfold sectorZ
    rw [detFactor_eq_zNat, hZnat, ENNReal.toReal_ofReal']
  -- the good event forces an attained sector and an integrable `det² U`
  set I := ∫ G', sectorWeight α U θ G' * invSqTrace U θ G' ∂gueMeasure (FrameIndex p) t
  have havg : sectorAvg α s U (invSqTrace U θ) θ = I / max Z 0 := by
    unfold sectorAvg; rw [hsZ]
  have hZpos : 0 < Z := by
    by_contra h
    rw [havg, max_eq_right (not_lt.mp h), div_zero] at hgood
    linarith
  have hI : 0 < I := by
    rw [havg, max_eq_left hZpos.le] at hgood
    by_contra h
    have : I / Z ≤ 0 := div_nonpos_of_nonpos_of_nonneg (not_lt.mp h) hZpos.le
    linarith
  have hint : Integrable (fun G' => sectorWeight α U θ G' * invSqTrace U θ G')
      (gueMeasure (FrameIndex p) t) := by
    by_contra h
    have : I = 0 := integral_undef h
    linarith
  have hfin := frameIndex_neZero p
  have hUm : Measurable fun X : FrameMatrix p => ENNReal.ofReal (invSq X) :=
    ENNReal.measurable_ofReal.comp measurable_invSq
  have hUqm : Measurable fun X : FrameMatrix p => ENNReal.ofReal ((invSq X)⁻¹ ^ q) :=
    ENNReal.measurable_ofReal.comp (measurable_invSq.inv.pow_const q)
  have hswU0 : ∀ᵐ G' ∂gueMeasure (FrameIndex p) t,
      0 ≤ sectorWeight α U θ G' * invSqTrace U θ G' := by
    filter_upwards [ae_isHermitian_gue t] with G' hG'
    refine mul_nonneg (secW_nonneg _ _ _) ?_
    unfold invSqTrace
    rw [hM]; exact invSq_nonneg (hK.add hG')
  have hIl : ENNReal.ofReal I = ∫⁻ x, ENNReal.ofReal (sectorDetSq K ℓ x).re *
      ENNReal.ofReal (invSq (K + hermOfCoord x)) ∂hermGaussian _ t := by
    rw [ofReal_integral_eq_lintegral_ofReal hint hswU0, ← lintegral_secW_eq hK hn t hUm]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_isHermitian_gue t] with G' hG'
    rw [← ENNReal.ofReal_mul (secW_nonneg _ _ _), sectorWeight_eq]
    unfold invSqTrace
    rw [hM]
    rfl
  have hZpos' : 0 < (sectorMass (2 * p.W - 1) t K ℓ).re := hZpos
  have hEU : ENNReal.ofReal L ≤ ∫⁻ x, ENNReal.ofReal (sectorInvSq K x) ∂sectorLaw _ t K ℓ := by
    have hm : Measurable fun x : HermCoord (2 * p.W - 1) → ℝ => ENNReal.ofReal (sectorInvSq K x) :=
      hUm.comp (continuous_const.add continuous_hermOfCoord).measurable
    rw [lintegral_sectorLaw hK hZpos' hm]
    have e : (∫⁻ x, ENNReal.ofReal (sectorDetSq K ℓ x).re * ENNReal.ofReal (sectorInvSq K x)
        ∂hermGaussian _ t) = ENNReal.ofReal I := hIl.symm
    rw [e, ← ENNReal.ofReal_inv_of_pos hZpos, ← ENNReal.ofReal_mul (inv_nonneg.mpr hZpos.le)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [havg, max_eq_left hZpos.le] at hgood
    rw [inv_mul_eq_div]; exact hgood
  have hmq : Measurable fun x : HermCoord (2 * p.W - 1) → ℝ =>
      ENNReal.ofReal ((sectorInvSq K x)⁻¹ ^ q) :=
    hUqm.comp (continuous_const.add continuous_hermOfCoord).measurable
  have hB := hCq _ t K ℓ ht hK hZpos'
  have hLHS : (∫⁻ G', ENNReal.ofReal (sectorWeight α U θ G') *
      ENNReal.ofReal ((invSqTrace U θ G')⁻¹ ^ q) ∂gueMeasure (FrameIndex p) t) =
      ENNReal.ofReal Z * ∫⁻ x, ENNReal.ofReal ((sectorInvSq K x)⁻¹ ^ q) ∂sectorLaw _ t K ℓ := by
    rw [lintegral_sectorLaw hK hZpos' hmq, ← mul_assoc,
      ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr hZpos).ne' ENNReal.ofReal_ne_top, one_mul]
    have h := lintegral_secW_eq hK hn t hUqm
    refine Eq.trans ?_ h
    refine lintegral_congr fun G' => ?_
    rw [sectorWeight_eq]
    unfold invSqTrace
    rw [hM]
    rfl
  rw [hLHS, hZnat, mul_comm _ (ENNReal.ofReal Z)]
  refine mul_le_mul_right (hB.trans (mul_le_mul_right ?_ _)) _
  exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow hEU hq.le)

theorem invSq_pos {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {M : Matrix ι ι ℂ}
    (hM : M.IsHermitian) (hdet : M.det ≠ 0) : 0 < invSq M := by
  set R := M⁻¹ with hRdef
  have hR : R.IsHermitian := hM.inv
  have e : invSq M = ∑ a, ∑ b, Complex.normSq (R a b) := by
    unfold invSq
    simp only [trace, diag, mul_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have hab : R b a = star (R a b) := (hR.apply b a).symm
    change (R a b * R b a).re = _
    rw [hab, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
  rw [e]
  by_contra hle
  have h0 : ∀ a b, R a b = 0 := by
    intro a b
    have hs := Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Finset.sum_nonneg fun b _ =>
      Complex.normSq_nonneg (R a b)) |>.mp (le_antisymm (not_lt.mp hle)
        (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => Complex.normSq_nonneg _)) a
      (Finset.mem_univ a)
    have hs2 := (Finset.sum_eq_zero_iff_of_nonneg fun b _ => Complex.normSq_nonneg (R a b)).mp hs b
      (Finset.mem_univ b)
    exact Complex.normSq_eq_zero.mp hs2
  have hR0 : R = 0 := by ext a b; exact h0 a b
  have h1 : M * R = 1 := mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hdet)
  rw [hR0, Matrix.mul_zero] at h1
  obtain ⟨a⟩ := ‹Nonempty ι›
  have := congrFun (congrFun h1 a) a
  simp at this

/-- Real form of the elementary split `1 ≤ U/a + a^q U^{-q}` for `U, a > 0`. -/
theorem one_le_split {U a q : ℝ} (hU : 0 < U) (ha : 0 < a) (hq : 0 < q) :
    1 ≤ a⁻¹ * U + a ^ q * U⁻¹ ^ q := by
  have h1 : 0 ≤ a⁻¹ * U := by positivity
  have h2 : 0 ≤ a ^ q * U⁻¹ ^ q := by positivity
  by_cases h : a ≤ U
  · have : 1 ≤ a⁻¹ * U := by rw [inv_mul_eq_div, one_le_div ha]; exact h
    linarith
  · have hlt : U < a := lt_of_not_ge h
    have e : a ^ q * U⁻¹ ^ q = (a / U) ^ q := by
      rw [div_eq_mul_inv, Real.mul_rpow ha.le (inv_nonneg.mpr hU.le)]
    have : 1 ≤ (a / U) ^ q := Real.one_le_rpow (by rw [one_le_div hU]; exact hlt.le) hq.le
    linarith

theorem outerKs_eq_outerK {U : FrameMap p i} (hU : IsPairFrame p i U) {θ : OuterData p i}
    (hv : l2Norm θ.2.2 = 1) : outerKs U θ = outerK U θ := by
  unfold outerKs outerK outerK0
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    (hU.2 θ.2.2 hv).1]

/-- **Fixed-`θ` tail bound** (the integrand of the minor tail bound at fixed outer data),
for every splitting parameter `a > 0`:
`E_{G'}[det² 1{sector α} 1{𝒢_α, V_B ≤ A}]
   ≤ (a⁻¹(2A + t⁻¹) + a^q C_q (cW²)^{-q}) Σ_{ℓ = α-1}^{α+1} 𝔷_ℓ(θ)`. -/
theorem inner_tail {q C : ℝ}
    (hCq : ∀ (m : ℕ) (t : ℝ≥0) (K : Matrix (Fin m) (Fin m) ℂ) (ℓ : ℕ), 0 < t →
      K.IsHermitian → 0 < (sectorMass m t K ℓ).re →
        (∫⁻ x, ENNReal.ofReal ((sectorInvSq K x)⁻¹ ^ q) ∂sectorLaw m t K ℓ) ≤
          ENNReal.ofReal C * ((∫⁻ x, ENNReal.ofReal (sectorInvSq K x) ∂sectorLaw m t K ℓ) ^ q)⁻¹)
    (hC : 0 ≤ C) (hq : 0 < q) (α : Fin p.N) (s : ℝ) {U : FrameMap p i} (hU : IsPairFrame p i U)
    {θ : OuterData p i} (hR : θ.1.1.IsHermitian) (hV : θ.1.2.2.IsHermitian) (hv : l2Norm θ.2.2 = 1)
    {w : OuterData p i → (FrameIndex p → ℂ)} (hw : IsOuterEigenvector U w)
    {Uw : (FrameIndex p → ℂ) → Matrix (FrameIndex p) (MinorIndex p) ℂ} (hUw : IsMinorFrame Uw)
    (ht : 0 < pairTime p s) (κ c : ℝ) (hc : 0 < c) {A a : ℝ} (hA : 0 ≤ A) (ha : 0 < a) :
    (∫⁻ G', ENNReal.ofReal (sectorWeight α U θ G') *
        ind (fun x : OuterData p i × FrameMatrix p =>
          SpreadGood α s U κ c x.1 ∧ minorV U w Uw x.1 x.2 ≤ A) (θ, G')
        ∂gueMeasure (FrameIndex p) (pairTime p s)) ≤
      ENNReal.ofReal (a⁻¹ * (2 * A + ((pairTime p s : ℝ))⁻¹) +
          a ^ q * (C * ((c * (p.W : ℝ) ^ 2) ^ q)⁻¹)) *
        (zNat s U (α.val - 1) θ + zNat s U α.val θ + zNat s U (α.val + 1) θ) := by
  set t := pairTime p s
  set K := outerKs U θ
  have hK : K.IsHermitian := outerKs_isHermitian U hR hV
  set n := nR θ
  have hM : ∀ G', outerM U θ G' = K + G' := outerM_eq U θ
  set L := c * (p.W : ℝ) ^ 2
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hL : 0 < L := by positivity
  set Z3 := zNat s U (α.val - 1) θ + zNat s U α.val θ + zNat s U (α.val + 1) θ
  by_cases hG : SpreadGood α s U κ c θ
  swap
  · refine le_trans (le_of_eq ?_) zero_le
    refine lintegral_eq_zero_of_ae_eq_zero (Filter.Eventually.of_forall fun G' => ?_)
    simp [ind, hG]
  -- the eigenvector and the minor frame
  have hKH : (outerK U θ).IsHermitian := by
    rw [← outerKs_eq_outerK hU hv]; exact hK
  obtain ⟨hw1, μ, hμ⟩ := hw.2 θ hv hKH
  set V := Uw (w θ)
  obtain ⟨hVV, hVw⟩ := hUw.2 (w θ) hw1
  have hKw : K *ᵥ w θ = ((μ : ℝ) : ℂ) • w θ := by
    change outerKs U θ *ᵥ w θ = _
    rw [outerKs_eq_outerK hU hv]; exact hμ
  have hmk : 2 * p.W - 1 = (2 * p.W - 2) + 1 := by have := p.W_pos; omega
  have hfin := frameIndex_neZero p
  have hTail := gue_tail hmk hK ht hw1 hKw hVV hVw n α.val A
  have hNeg := inner_neg hCq hq α s U hR hV ht hL hG.2
  have hmT : Measurable fun G' : FrameMatrix p => tailW V n α.val A (K + G') :=
    (measurable_tailW V n α.val A).comp (measurable_const_add K)
  -- pointwise split
  have hpt : ∀ᵐ G' ∂gueMeasure (FrameIndex p) t,
      ENNReal.ofReal (sectorWeight α U θ G') *
        ind (fun x : OuterData p i × FrameMatrix p =>
          SpreadGood α s U κ c x.1 ∧ minorV U w Uw x.1 x.2 ≤ A) (θ, G') ≤
      ENNReal.ofReal a⁻¹ * tailW V n α.val A (K + G') +
        ENNReal.ofReal (a ^ q) * (ENNReal.ofReal (sectorWeight α U θ G') *
          ENNReal.ofReal ((invSqTrace U θ G')⁻¹ ^ q)) := by
    filter_upwards [ae_isHermitian_gue t] with G' hG'
    by_cases hA' : minorV U w Uw θ G' ≤ A
    swap
    · simp [ind, hA']
    have hind : ind (fun x : OuterData p i × FrameMatrix p =>
        SpreadGood α s U κ c x.1 ∧ minorV U w Uw x.1 x.2 ≤ A) (θ, G') = 1 := by
      simp [ind, hG, hA']
    have hmv : invSq (Vᴴ * (K + G') * V) ≤ A := by
      have : minorV U w Uw θ G' = invSq (Vᴴ * (K + G') * V) := by
        unfold minorV minorB invSq; rw [hM]
      rw [← this]; exact hA'
    have htw : tailW V n α.val A (K + G') =
        ENNReal.ofReal (sectorWeight α U θ G') * ENNReal.ofReal (invSq (K + G')) := by
      unfold tailW; rw [sectorWeight_eq, hM]; simp only [hmv, ↓reduceIte]; rfl
    have hUq : invSqTrace U θ G' = invSq (K + G') := by unfold invSqTrace invSq; rw [hM]
    rw [hind, mul_one, htw, hUq]
    set sw := sectorWeight α U θ G'
    have hsw0 : 0 ≤ sw := secW_nonneg _ _ _
    by_cases hsw : sw = 0
    · rw [hsw, ENNReal.ofReal_zero]; exact zero_le
    have hdet : (K + G').det ≠ 0 := by
      intro h0
      apply hsw
      simp only [sw, sectorWeight_eq, hM, secW, h0, map_zero, zero_mul]
    have hUpos := invSq_pos (hK.add hG') hdet
    have key := one_le_split hUpos ha hq
    rw [← ENNReal.ofReal_mul hsw0, ← ENNReal.ofReal_mul hsw0,
      ← ENNReal.ofReal_mul (inv_nonneg.mpr ha.le), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith [mul_le_mul_of_nonneg_left key hsw0]
  have hzS : ∀ ℓ, (∫⁻ G', ENNReal.ofReal (secW n ℓ (K + G')) ∂gueMeasure (FrameIndex p) t) =
      zNat s U ℓ θ := by
    intro ℓ; unfold zNat; simp_rw [hM]; rfl
  rw [hzS, hzS, hzS] at hTail
  calc _ ≤ ∫⁻ G', (ENNReal.ofReal a⁻¹ * tailW V n α.val A (K + G') +
        ENNReal.ofReal (a ^ q) * (ENNReal.ofReal (sectorWeight α U θ G') *
          ENNReal.ofReal ((invSqTrace U θ G')⁻¹ ^ q))) ∂gueMeasure (FrameIndex p) t :=
        lintegral_mono_ae hpt
    _ = ENNReal.ofReal a⁻¹ * (∫⁻ G', tailW V n α.val A (K + G') ∂gueMeasure (FrameIndex p) t) +
        ENNReal.ofReal (a ^ q) * ∫⁻ G', ENNReal.ofReal (sectorWeight α U θ G') *
          ENNReal.ofReal ((invSqTrace U θ G')⁻¹ ^ q) ∂gueMeasure (FrameIndex p) t := by
        rw [lintegral_add_left (hmT.const_mul _), lintegral_const_mul _ hmT,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal a⁻¹ * (ENNReal.ofReal (2 * A + (t : ℝ)⁻¹) * Z3) +
        ENNReal.ofReal (a ^ q) * (ENNReal.ofReal C * (ENNReal.ofReal L ^ q)⁻¹ *
          zNat s U α.val θ) := by
        gcongr
    _ ≤ ENNReal.ofReal a⁻¹ * (ENNReal.ofReal (2 * A + (t : ℝ)⁻¹) * Z3) +
        ENNReal.ofReal (a ^ q) * (ENNReal.ofReal C * (ENNReal.ofReal L ^ q)⁻¹ * Z3) := by
        gcongr
        exact le_add_right (le_add_left le_rfl)
    _ = _ := by
        have hX : 0 ≤ 2 * A + (t : ℝ)⁻¹ := by positivity
        rw [ENNReal.ofReal_rpow_of_pos hL, ← ENNReal.ofReal_inv_of_pos (by positivity),
          ← ENNReal.ofReal_mul hC, ← mul_assoc, ← mul_assoc,
          ← ENNReal.ofReal_mul (inv_nonneg.mpr ha.le), ← ENNReal.ofReal_mul (by positivity),
          ← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]

/-!
## The tail clause
-/

/-- The optimization of the splitting parameter: `a = W² r^{1/(q+1)}`, `r = (A+W)/W²`. -/
theorem tail_constant {A W sb c q C' : ℝ} (hA : 0 ≤ A) (hW : 0 < W) (hsb : 0 < sb) (hc : 0 < c)
    (hq : 0 < q) :
    (W ^ 2 * ((A + W) / W ^ 2) ^ (1 / (q + 1)))⁻¹ * (2 * A + 2 * W / sb) +
        (W ^ 2 * ((A + W) / W ^ 2) ^ (1 / (q + 1))) ^ q * (C' * ((c * W ^ 2) ^ q)⁻¹) ≤
      (2 + 2 / sb + C' * (c ^ q)⁻¹) * ((A + W) / W ^ 2) ^ (q / (q + 1)) := by
  set r := (A + W) / W ^ 2 with hr
  have hW2 : 0 < W ^ 2 := by positivity
  have hrpos : 0 < r := by positivity
  set e := 1 / (q + 1)
  have hq1 : 0 < q + 1 := by linarith
  have hexp : q / (q + 1) = 1 - e := by simp only [e]; field_simp; ring
  have hre : 0 < r ^ e := Real.rpow_pos_of_pos hrpos e
  have hrq : r ^ (q / (q + 1)) = r / r ^ e := by
    rw [hexp, Real.rpow_sub hrpos, Real.rpow_one]
  have hrq' : (r ^ e) ^ q = r ^ (q / (q + 1)) := by
    rw [← Real.rpow_mul hrpos.le]; congr 1; simp only [e]; field_simp
  have hX : 2 * A + 2 * W / sb ≤ (2 + 2 / sb) * (A + W) := by
    have h1 : 0 ≤ 2 * W := by positivity
    have h2 : 0 ≤ 2 * A / sb := by positivity
    have e1 : (2 + 2 / sb) * (A + W) = 2 * A + 2 * W + 2 * A / sb + 2 * W / sb := by ring
    rw [e1]; linarith
  have hAW : A + W = r * W ^ 2 := by simp only [r]; field_simp
  have t1 : (W ^ 2 * r ^ e)⁻¹ * (2 * A + 2 * W / sb) ≤ (2 + 2 / sb) * r ^ (q / (q + 1)) := by
    calc (W ^ 2 * r ^ e)⁻¹ * (2 * A + 2 * W / sb)
        ≤ (W ^ 2 * r ^ e)⁻¹ * ((2 + 2 / sb) * (A + W)) :=
          mul_le_mul_of_nonneg_left hX (by positivity)
      _ = (2 + 2 / sb) * r ^ (q / (q + 1)) := by
          rw [hrq, hAW]; field_simp
  have t2 : (W ^ 2 * r ^ e) ^ q * (C' * ((c * W ^ 2) ^ q)⁻¹) =
      C' * (c ^ q)⁻¹ * r ^ (q / (q + 1)) := by
    rw [Real.mul_rpow hW2.le hre.le, hrq', Real.mul_rpow hc.le hW2.le]
    have : 0 < (W ^ 2) ^ q := Real.rpow_pos_of_pos hW2 q
    have : 0 < c ^ q := Real.rpow_pos_of_pos hc q
    field_simp
  rw [t2, add_mul]
  linarith

theorem inv_pairTime_eq (p : Parameters) :
    ((pairTime p (splitS p) : ℝ))⁻¹ = 2 * (p.W : ℝ) / splitS p := by
  have hs := BlockBand.Angular.PairCoareaBridge.splitS_pos p
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  unfold pairTime
  rw [Real.coe_toNNReal _ (by positivity)]
  field_simp

/-- **The physical minor tail, first clause**, under `CoareaContract` and
`NegativeSpreadStatement` (only its `inverse_moment` field). -/
theorem tail_holds (hC : CoareaContract) (hNS : NegativeSpreadStatement) :
    ∀ b κ c q : ℝ, 0 < κ → 0 < c → 0 < q → ∃ C : ℝ, ∀ p : Parameters, p.b = b →
    ∀ (model : p.GaussianRingModel) (α : Fin p.N) (i : ZMod p.n)
      (Pω : Measure (SplitState p i)), IsPairSplitting p i model (splitS p) Pω →
    ∀ U : FrameMap p i, IsPairFrame p i U →
    ∀ w : OuterData p i → (FrameIndex p → ℂ), IsOuterEigenvector U w →
    ∀ Uw : (FrameIndex p → ℂ) → Matrix (FrameIndex p) (MinorIndex p) ℂ, IsMinorFrame Uw →
    ∀ A : ℝ, 0 ≤ A →
      pairExpect α (splitS p) U Pω (fun θ G' =>
          ind (fun x : OuterData p i × FrameMatrix p =>
            SpreadGood α (splitS p) U κ c x.1 ∧ minorV U w Uw x.1 x.2 ≤ A) (θ, G')) ≤
        ENNReal.ofReal (C * ((A + p.W) / (p.W : ℝ) ^ 2) ^ (q / (q + 1))) := by
  intro b κ c q _ hc hq
  obtain ⟨Cq, hCq⟩ := hNS.inverse_moment q hq
  set C' := max Cq 0
  have hC' : 0 ≤ C' := le_max_right _ _
  have hCq' : ∀ (m : ℕ) (t : ℝ≥0) (K : Matrix (Fin m) (Fin m) ℂ) (ℓ : ℕ), 0 < t →
      K.IsHermitian → 0 < (sectorMass m t K ℓ).re →
        (∫⁻ x, ENNReal.ofReal ((sectorInvSq K x)⁻¹ ^ q) ∂sectorLaw m t K ℓ) ≤
          ENNReal.ofReal C' * ((∫⁻ x, ENNReal.ofReal (sectorInvSq K x) ∂sectorLaw m t K ℓ) ^ q)⁻¹ :=
    fun m t K ℓ ht hK hZ => (hCq m t K ℓ ht hK hZ).trans
      (mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_max_left _ _)) _)
  set sb := min (1 - 2 * b) b
  refine ⟨3 * (2 + 2 / sb + C' * (c ^ q)⁻¹), ?_⟩
  intro p hb model α i Pω hPω U hU w hw Uw hUw A hA
  have hs : splitS p = sb := by unfold splitS Parameters.c; rw [hb]
  have hsp := BlockBand.Angular.PairCoareaBridge.splitS_pos p
  have hsb : 0 < sb := hs ▸ hsp
  have ht := pairTime_splitS_pos p
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  set r := ((A + p.W) / (p.W : ℝ) ^ 2)
  set a := (p.W : ℝ) ^ 2 * r ^ (1 / (q + 1))
  have ha : 0 < a := by positivity
  have hB := pairExpect_le hC hPω hU α _ _ (fun θ hR hV hv =>
    inner_tail hCq' hC' hq α (splitS p) hU hR hV hv hw hUw ht κ c hc hA ha)
  refine hB.trans ?_
  rw [three_mul_ofReal]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  rw [inv_pairTime_eq, hs]
  exact tail_constant hA hW hsb hc hq

/-- `PhysicalMinorTailStatement` from its second clause (the inverse spread bound `hI`), which is
a hypothesis here; the first clause is `tail_holds`. -/
theorem physicalMinorTail_of_inverseSpread (hC : CoareaContract) (hNS : NegativeSpreadStatement)
    (hI : ∀ b T ϑ κ r : ℝ, 0 < ϑ → 0 < κ → 0 < r → r < 2 → ∃ C : ℝ,
      ∀ p : Parameters, p.b = b → (p.n : ℝ) ≤ T * (p.W : ℝ) →
      ∀ (model : p.GaussianRingModel) (α : Fin p.N), IsBulkRank p ϑ α →
      ∀ (i : ZMod p.n) (Pω : Measure (SplitState p i)), IsPairSplitting p i model (splitS p) Pω →
      ∀ U : FrameMap p i, IsPairFrame p i U →
      ∀ w : OuterData p i → (FrameIndex p → ℂ), IsOuterEigenvector U w →
      ∀ Uw : (FrameIndex p → ℂ) → Matrix (FrameIndex p) (MinorIndex p) ℂ, IsMinorFrame Uw →
        pairExpect α (splitS p) U Pω (fun θ G' =>
            (bulkInterval κ).indicator 1 θ.2.1 *
              ENNReal.ofReal (minorQSq (splitS p) U w Uw θ G' ^ (-(r / 2)))) ≤
          ENNReal.ofReal C) :
    PhysicalMinorTailStatement :=
  ⟨tail_holds hC hNS, hI⟩

end BlockBand.DeterminantScore.MinorTail
