module

public import BlockBand.DeterminantScore.MinorTailInverseBad

/-!
# The inverse spread `E♯ 1{E ∈ I} q_B^{-r} ≤ C_r` and the physical minor tail

`inverseSpread_holds (hC : CoareaContract) (hNS : NegativeSpreadStatement)
(hLW : PhysicalLocalWindowStatement) (hRL : PhysicalRealLoopStatement)`: the `inverse_spread`
field of `PhysicalMinorTailStatement`: for `b, T, ϑ, κ` and `0 < r < 2` there is `C` with
`E♯ 1{E ∈ I} q_B^{-r} ≤ C` for `4 ≤ n ≤ TW`, `ϑ`-bulk ranks, every model, pair, splitting law,
pair frame, measurable unit eigenvector `w(θ)` of `K` and minor frame.

`physicalMinorTail_holds`: `PhysicalMinorTailStatement`, from `inverseSpread_holds` and
`MinorTail.physicalMinorTail_of_inverseSpread` (first clause `MinorTail.tail_holds`).

Proof of the second clause (by the spread good event, Hölder bounds the bad contribution to
`E♯Y^r` by `CW^{ξr/2-(1-r/2)/50}`, and `ξ` is chosen small), with `θ' = r/2`, `q = 2r/(2-r)` (so
`r < 2q/(q+1)`), `ξ = (1-θ')/(50θ')` and `λ = W^{-ξ}`: pointwise on the support,
`1{E ∈ I} q_B^{-r} ≤ 1_{𝒢_α} q_B^{-r} + (1-θ')λ^{-θ'/(1-θ')} 1{E ∈ I, ¬𝒢_α} + θ'λ q_B^{-2}`
(Young's inequality in its weighted AM-GM form `young_split`); then
* `1_{𝒢_α} q_B^{-r}`: `MinorTailInverse.inner_good` at fixed `θ` and the three restored pair laws
  (`pairExpect_add_le`), at most `3(1 + rK''/(2q/(q+1) - r))`;
* `1{E ∈ I, ¬𝒢_α}`: `PhysicalRealLoopStatement.good`, `P♯ ≤ C W^{-1/50}`, and
  `λ^{-θ'/(1-θ')} = W^{1/50}`;
* `q_B^{-2}`: `MinorTailInverse.badMoment_holds`, `E♯ q_B^{-2} ≤ C_ξ W^ξ`, and `λ W^ξ = 1`.

Hypotheses: `CoareaContract`; `NegativeSpreadStatement` (`inverse_moment`, at exponent `q`);
`PhysicalLocalWindowStatement` (part (i), through `badMoment_holds`); `PhysicalRealLoopStatement`
(only `good`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.MinorTailInverse

open MeasureTheory ProbabilityTheory Matrix Set
open BlockBand.Model.Construction BlockBand.Coarea
open BlockBand.Internal.Contracts BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Layers BlockBand.Angular.FiberAngular
open BlockBand.DeterminantScore BlockBand.DeterminantScore.Sector
open BlockBand.DeterminantScore.PhysicalColumn BlockBand.DeterminantScore.MinorTail
open BlockBand.LocalWindow
open scoped NNReal ENNReal

variable {p : Parameters} {i : ZMod p.n}

/-- **Young's inequality** (weighted AM-GM): for `X, λ > 0`, `0 < θ < 1`,
`X^{-θ} ≤ θλX⁻¹ + (1-θ)λ^{-θ/(1-θ)}`. -/
theorem young_split {X lam θ : ℝ} (hX : 0 < X) (hlam : 0 < lam) (hθ : 0 < θ) (hθ1 : θ < 1) :
    X ^ (-θ) ≤ θ * (lam * X⁻¹) + (1 - θ) * lam ^ (-(θ / (1 - θ))) := by
  have h1θ : 0 < 1 - θ := by linarith
  have h := Real.geom_mean_le_arith_mean2_weighted hθ.le h1θ.le
    (mul_nonneg hlam.le (inv_nonneg.mpr hX.le)) (Real.rpow_nonneg hlam.le (-(θ / (1 - θ))))
    (by ring)
  have e : (lam * X⁻¹) ^ θ * (lam ^ (-(θ / (1 - θ)))) ^ (1 - θ) = X ^ (-θ) := by
    rw [Real.mul_rpow hlam.le (inv_nonneg.mpr hX.le), ← Real.rpow_mul hlam.le,
      Real.inv_rpow hX.le, ← Real.rpow_neg hX.le]
    have : -(θ / (1 - θ)) * (1 - θ) = -θ := by field_simp
    rw [this, mul_comm, ← mul_assoc, ← Real.rpow_add hlam]
    simp
  rw [e] at h
  exact h

theorem goodConst_nonneg {s C c q r : ℝ} (hs : 0 < s) (hC : 0 ≤ C) (hc : 0 < c)
    (hr : 0 < r) (hrq : r < 2 * (q / (q + 1))) : 0 ≤ goodConst s C c q r := by
  have hK : 0 ≤ levelConst s C c q := by
    have : 0 ≤ C * (c ^ q)⁻¹ := mul_nonneg hC (inv_nonneg.mpr (Real.rpow_nonneg hc.le _))
    unfold levelConst
    have : 0 ≤ (4 / s ^ 2 + 2 / s) ^ (q / (q + 1)) := Real.rpow_nonneg (by positivity) _
    positivity
  have hgap : 0 < 2 * (q / (q + 1)) - r := by linarith
  unfold goodConst
  positivity

/-- **The physical minor tail, second clause** (the inverse spread bound). -/
theorem inverseSpread_holds (hC : CoareaContract) (hNS : NegativeSpreadStatement)
    (hLW : PhysicalLocalWindowStatement) (hRL : PhysicalRealLoopStatement) :
    ∀ b T ϑ κ r : ℝ, 0 < ϑ → 0 < κ → 0 < r → r < 2 → ∃ C : ℝ,
      ∀ p : Parameters, p.b = b → (p.n : ℝ) ≤ T * (p.W : ℝ) →
      ∀ (model : p.GaussianRingModel) (α : Fin p.N), IsBulkRank p ϑ α →
      ∀ (i : ZMod p.n) (Pω : Measure (SplitState p i)), IsPairSplitting p i model (splitS p) Pω →
      ∀ U : FrameMap p i, IsPairFrame p i U →
      ∀ w : OuterData p i → (FrameIndex p → ℂ), IsOuterEigenvector U w →
      ∀ Uw : (FrameIndex p → ℂ) → Matrix (FrameIndex p) (MinorIndex p) ℂ, IsMinorFrame Uw →
        pairExpect α (splitS p) U Pω (fun θ G' =>
            (bulkInterval κ).indicator 1 θ.2.1 *
              ENNReal.ofReal (minorQSq (splitS p) U w Uw θ G' ^ (-(r / 2)))) ≤
          ENNReal.ofReal C := by
  intro b T ϑ κ r hϑ hκ hr hr2
  -- the exponents
  set θ' := r / 2 with hθ'
  have hθ0 : 0 < θ' := by positivity
  have hθ1 : θ' < 1 := by rw [hθ']; linarith
  set q := 2 * r / (2 - r) with hqdef
  have h2r : 0 < 2 - r := by linarith
  have hq : 0 < q := by positivity
  have hrq : r < 2 * (q / (q + 1)) := by
    have e : q / (q + 1) = 2 * r / (r + 2) := by
      rw [hqdef]; field_simp; ring
    rw [e, show 2 * (2 * r / (r + 2)) = 4 * r / (r + 2) by ring, lt_div_iff₀ (by linarith)]
    nlinarith
  set ξ := (1 - θ') / (50 * θ') with hξdef
  have hξ : 0 < ξ := by apply div_pos <;> linarith
  -- the inputs
  obtain ⟨c, hc, hgood⟩ := hRL.good b κ hκ
  obtain ⟨CP, hCP⟩ := hgood T ϑ hϑ
  obtain ⟨Cξ, hCξ⟩ := badMoment_holds hC hLW b T ϑ ξ hϑ hξ
  obtain ⟨Cq, hCq⟩ := hNS.inverse_moment q hq
  set C' := max Cq 0
  have hC' : 0 ≤ C' := le_max_right _ _
  have hCq' : ∀ (m : ℕ) (t : ℝ≥0) (K : Matrix (Fin m) (Fin m) ℂ) (ℓ : ℕ), 0 < t →
      K.IsHermitian → 0 < (sectorMass m t K ℓ).re →
        (∫⁻ x, ENNReal.ofReal ((sectorInvSq K x)⁻¹ ^ q) ∂sectorLaw m t K ℓ) ≤
          ENNReal.ofReal C' * ((∫⁻ x, ENNReal.ofReal (sectorInvSq K x) ∂sectorLaw m t K ℓ) ^ q)⁻¹ :=
    fun m t K ℓ ht hK hZ => (hCq m t K ℓ ht hK hZ).trans
      (mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_max_left _ _)) _)
  set sb := min (1 - 2 * b) b with hsb
  set G := goodConst sb C' c q r with hGdef
  set CP' := max CP 0
  set Cξ' := max Cξ 0
  refine ⟨3 * G + (1 - θ') * CP' + θ' * Cξ', ?_⟩
  intro p hb hn model α hα i Pω hPω U hU w hw Uw hUw
  have hs : splitS p = sb := by unfold splitS Parameters.c; rw [hb]
  have hsp := BlockBand.Angular.PairCoareaBridge.splitS_pos p
  have hsb0 : 0 < sb := hs ▸ hsp
  have hG0 : 0 ≤ G := goodConst_nonneg hsb0 hC' hc hr hrq
  have ht := pairTime_splitS_pos p
  have hW1 : (1 : ℝ) ≤ p.W := by exact_mod_cast p.W_pos
  have hW : (0 : ℝ) < p.W := by linarith
  set s := splitS p with hsdef
  set lam := (p.W : ℝ) ^ (-ξ) with hlam
  have hlam0 : 0 < lam := Real.rpow_pos_of_pos hW _
  set c₁ := θ' * lam with hc₁
  set c₂ := (1 - θ') * lam ^ (-(θ' / (1 - θ'))) with hc₂
  have hc₁0 : 0 ≤ c₁ := by positivity
  have hc₂0 : 0 ≤ c₂ := mul_nonneg (by linarith) (Real.rpow_nonneg hlam0.le _)
  -- the three pieces
  set Ψ₁ : OuterData p i → FrameMatrix p → ℝ≥0∞ := fun θ G' =>
    ind (fun θ'' => SpreadGood α s U κ c θ'') θ *
      ENNReal.ofReal (minorQSq s U w Uw θ G' ^ (-(r / 2))) with hΨ₁
  set Ψa : OuterData p i → FrameMatrix p → ℝ≥0∞ := fun θ _ =>
    ENNReal.ofReal c₂ * ind (fun θ'' => θ''.2.1 ∈ bulkInterval κ ∧ ¬ SpreadGood α s U κ c θ'') θ
    with hΨa
  set Ψb : OuterData p i → FrameMatrix p → ℝ≥0∞ := fun θ G' =>
    ENNReal.ofReal c₁ * ENNReal.ofReal (minorQSq s U w Uw θ G')⁻¹ with hΨb
  have hmono : pairExpect α s U Pω (fun θ G' =>
      (bulkInterval κ).indicator 1 θ.2.1 *
        ENNReal.ofReal (minorQSq s U w Uw θ G' ^ (-(r / 2)))) ≤
      pairExpect α s U Pω (fun θ G' => Ψ₁ θ G' + (Ψa θ G' + Ψb θ G')) := by
    refine pairExpect_mono_ae hPω α U fun θ hR hV hv _ => ?_
    filter_upwards [ae_isHermitian_gue (pairTime p s)] with G' hG' _
    obtain ⟨hXt, -, -⟩ := minorQSq_ge s U hR hV w Uw hG'
    have hXpos : 0 < minorQSq s U w Uw θ G' := lt_of_lt_of_le (by exact_mod_cast ht) hXt
    simp only [hΨ₁, hΨa, hΨb]
    by_cases hE : θ.2.1 ∈ bulkInterval κ
    swap
    · rw [indicator_of_notMem hE, zero_mul]; exact zero_le
    rw [indicator_of_mem hE, Pi.one_apply, one_mul]
    by_cases hg : SpreadGood α s U κ c θ
    · have : ind (fun θ'' => SpreadGood α s U κ c θ'') θ = 1 := by simp [ind, hg]
      rw [this, one_mul]
      exact le_self_add
    · have h0 : ind (fun θ'' => SpreadGood α s U κ c θ'') θ = 0 := by simp [ind, hg]
      have h1 : ind (fun θ'' => θ''.2.1 ∈ bulkInterval κ ∧ ¬ SpreadGood α s U κ c θ'') θ = 1 := by
        simp [ind, hg, hE]
      rw [h0, zero_mul, zero_add, h1, mul_one, ← ENNReal.ofReal_mul hc₁0,
        ← ENNReal.ofReal_add hc₂0 (mul_nonneg hc₁0 (inv_nonneg.mpr hXpos.le))]
      refine ENNReal.ofReal_le_ofReal ?_
      have := young_split hXpos hlam0 hθ0 hθ1
      rw [hc₁, hc₂]
      rw [show -(r / 2) = -θ' from rfl]
      linarith
  have hΨ₂m : ∀ θ, Measurable ((fun θ G' => Ψa θ G' + Ψb θ G') θ) := fun θ =>
    measurable_const.add (measurable_const.mul
      (ENNReal.measurable_ofReal.comp (measurable_minorQSq_G s U w Uw θ).inv))
  have hstep1 := pairExpect_add_le hC hPω hU α Ψ₁ (fun θ G' => Ψa θ G' + Ψb θ G')
    (ENNReal.ofReal G) hΨ₂m (fun θ hR hV hv => by
      rw [hGdef, ← hs]
      exact inner_good hCq' hC' hq hr hrq α hU hR hV hv hw hUw κ c hc)
  have hbm : Measurable fun z : OuterData p i × FrameMatrix p => Ψb z.1 z.2 :=
    measurable_const.mul (ENNReal.measurable_ofReal.comp
      (measurable_minorQSq s hU.1 hw.1 hUw.1).inv)
  have hstep2 := pairExpect_add_le_of_measurable α s hU.1 Pω Ψa Ψb hbm
  have hPa : pairExpect α s U Pω Ψa ≤ ENNReal.ofReal c₂ * ENNReal.ofReal (CP' * (p.W : ℝ) ^ (-(1 / 50 : ℝ))) := by
    simp only [hΨa]
    rw [pairExpect_const_mul α s U Pω ENNReal.ofReal_ne_top]
    gcongr
    refine (hCP p hb hn model α hα i Pω hPω U hU).trans (ENNReal.ofReal_le_ofReal ?_)
    gcongr
    exact le_max_left _ _
  have hPb : pairExpect α s U Pω Ψb ≤ ENNReal.ofReal c₁ * ENNReal.ofReal (Cξ' * (p.W : ℝ) ^ ξ) := by
    simp only [hΨb]
    rw [pairExpect_const_mul α s U Pω ENNReal.ofReal_ne_top]
    gcongr
    refine (hCξ p hb hn model α hα i Pω hPω U hU w hw Uw hUw).trans (ENNReal.ofReal_le_ofReal ?_)
    gcongr
    exact le_max_left _ _
  -- the powers of `W`
  have hpow2 : c₂ * (CP' * (p.W : ℝ) ^ (-(1 / 50 : ℝ))) = (1 - θ') * CP' := by
    have e : lam ^ (-(θ' / (1 - θ'))) = (p.W : ℝ) ^ (1 / 50 : ℝ) := by
      rw [hlam, ← Real.rpow_mul hW.le]
      congr 1
      rw [hξdef]
      have : (1 - θ') ≠ 0 := by linarith
      field_simp
    rw [hc₂, e]
    have : (p.W : ℝ) ^ (1 / 50 : ℝ) * (p.W : ℝ) ^ (-(1 / 50 : ℝ)) = 1 := by
      rw [← Real.rpow_add hW]; norm_num
    calc (1 - θ') * (p.W : ℝ) ^ (1 / 50 : ℝ) * (CP' * (p.W : ℝ) ^ (-(1 / 50 : ℝ)))
        = (1 - θ') * CP' * ((p.W : ℝ) ^ (1 / 50 : ℝ) * (p.W : ℝ) ^ (-(1 / 50 : ℝ))) := by ring
      _ = (1 - θ') * CP' := by rw [this, mul_one]
  have hpowb : c₁ * (Cξ' * (p.W : ℝ) ^ ξ) = θ' * Cξ' := by
    have : lam * (p.W : ℝ) ^ ξ = 1 := by
      rw [hlam, ← Real.rpow_add hW]; norm_num
    calc c₁ * (Cξ' * (p.W : ℝ) ^ ξ) = θ' * Cξ' * (lam * (p.W : ℝ) ^ ξ) := by rw [hc₁]; ring
      _ = θ' * Cξ' := by rw [this, mul_one]
  have hCP0 : 0 ≤ CP' := le_max_right _ _
  have hCξ0 : 0 ≤ Cξ' := le_max_right _ _
  calc _ ≤ _ := hmono
    _ ≤ 3 * ENNReal.ofReal G + pairExpect α s U Pω (fun θ G' => Ψa θ G' + Ψb θ G') := hstep1
    _ ≤ 3 * ENNReal.ofReal G + (pairExpect α s U Pω Ψa + pairExpect α s U Pω Ψb) := by
        gcongr
    _ ≤ 3 * ENNReal.ofReal G +
        (ENNReal.ofReal c₂ * ENNReal.ofReal (CP' * (p.W : ℝ) ^ (-(1 / 50 : ℝ))) +
          ENNReal.ofReal c₁ * ENNReal.ofReal (Cξ' * (p.W : ℝ) ^ ξ)) := by
        gcongr
    _ = ENNReal.ofReal (3 * G + (1 - θ') * CP' + θ' * Cξ') := by
        have ha : 0 ≤ (1 - θ') * CP' := mul_nonneg (by linarith) hCP0
        have hb' : 0 ≤ θ' * Cξ' := mul_nonneg hθ0.le hCξ0
        rw [← ENNReal.ofReal_mul hc₂0, ← ENNReal.ofReal_mul hc₁0, hpow2, hpowb, three_mul_ofReal,
          ← ENNReal.ofReal_add ha hb', ← ENNReal.ofReal_add (by positivity) (add_nonneg ha hb')]
        congr 1
        ring

/-- **The physical minor tail** (`PhysicalMinorTailStatement`), both clauses, under
`CoareaContract`, `NegativeSpreadStatement`, `PhysicalLocalWindowStatement` and
`PhysicalRealLoopStatement`. -/
theorem physicalMinorTail_holds (hC : CoareaContract) (hNS : NegativeSpreadStatement)
    (hLW : PhysicalLocalWindowStatement) (hRL : PhysicalRealLoopStatement) :
    PhysicalMinorTailStatement :=
  physicalMinorTail_of_inverseSpread hC hNS (inverseSpread_holds hC hNS hLW hRL)

end BlockBand.DeterminantScore.MinorTailInverse
