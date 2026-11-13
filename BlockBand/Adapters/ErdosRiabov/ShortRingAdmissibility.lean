module

public import BlockBand.Adapters.ErdosRiabov.Clause167
public import BlockBand.Adapters.ErdosRiabov.Clause45

/-!
# Short-ring Erdős–Riabov admissibility with the polynomial control

The polynomial control `Υ_η(x,y) = (ℓη)⁻¹ (1 + d(x,y)/ℓ)^{-D}` is admissible in the sense of
Erdős–Riabov Definition 2.4 for the short-ring variance profile, with constants depending
only on the fixed parameters (`shortRingAdmissibility_holds`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Adapters.ErdosRiabov

open BlockBand.External
open scoped BigOperators

/-- Points of the spectral domain have `|Im z| > 0`. -/
theorem spectralDomain_abs_im_pos {q : ErdosRiabov.ModelParameters} {N : ℕ} (hN : 0 < N) {z : ℂ}
    (hz : ErdosRiabov.SpectralDomain q N z) : 0 < |z.im| :=
  lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast hN) _) hz.1

/-- The reference record at bond `b` (only `b` enters the constants). -/
def refParams (b : ℝ) (hb0 : 0 < b) (hb : b < 1 / 2) : CyclicModel.Params :=
  cyclicModelParams b 4 1 hb0 hb le_rfl one_pos

/-- The admissibility constant `C₁(b, κ, C₀, D)`. -/
def admissibilityConstant (b : ℝ) (hb0 : 0 < b) (hb : b < 1 / 2) (κ C₀ D : ℝ) : ℝ :=
  max 1 (max
    (CyclicModel.GaussianRing.ERGeneralVectorMDEThetaDomain.thetaDomainControlConstant
        (refParams b hb0 hb) C₀ *
      (1 + D / CyclicModel.GaussianRing.ERGeneralVectorMDEThetaDomain.thetaDomainDecay C₀) ^ D)
  (max (CyclicModel.GaussianRing.ERGeneralVectorMDEXiKappa.xiKappaControlConstant κ b *
      (1 + D / CyclicModel.GaussianRing.ERGeneralVectorMDEXiKappa.xiKappaRate κ b) ^ D)
  (max (CyclicModel.GaussianRing.ERClause6DomainControl.clause6DomainConstant
        (refParams b hb0 hb) κ C₀ *
      (1 + D / CyclicModel.GaussianRing.ERClause6DomainControl.clause6DomainDecay
        (refParams b hb0 hb) κ C₀) ^ D)
  (max (CyclicModel.GaussianRing.ERClause7DomainControl.clause67DomainConstant
        (refParams b hb0 hb) κ C₀)
  (max ((3 / 2 : ℝ) ^ D) (max (2 * (Real.sqrt C₀ + 1))
  (max (constC C₀ D) (constW C₀ D))))))))

/-- The polynomial-control form of
`Internal.Contracts.Inputs.ShortRingAdmissibility`.
Deterministic (no law).
Order: fix
`0 < b < 1/2`, `δ₀, κ > 0`, `C₀ ≥ 1`, `D ≥ 6`; then `C₁ = admissibilityConstant b κ C₀ D`,
`c₂ = 1`, `D' = (1+2C₀)(D+1)/2`; then for every native `ErdosRiabov.ModelParameters` with
`δ₀, κ, C₀` and `C1 ≥ C₁, c2 ≥ c₂, DPrime ≥ D'`, every `m ≥ 4` and `W ≥ 1`, the polynomial
control `(ℓη)⁻¹(1 + d/ℓ)^{-D}` on `Fin (mW)` (row-major, periodic distance,
`ℓ = min (W/√η) (mW)`) is an `ErdosRiabov.AdmissibleControl` of `S = C ⊗ J_W`: all seven
clauses of ER Definition 2.4, uniformly in `m, W`, heights, spectral parameters and sites.
No contract.
-/
theorem shortRingAdmissibility_holds : Internal.Contracts.Inputs.ShortRingAdmissibility := by
  intro b hb0 hb δ₀ κ C₀ _hδ₀ hκ hC₀ D hD
  set K := admissibilityConstant b hb0 hb κ C₀ D with hK
  refine ⟨K, 1, floorExponent C₀ D, le_max_left _ _, one_pos,
    floorExponent_pos hC₀ (by linarith), ?_⟩
  intro q _hqδ hqκ hqC hC1 _hc2 hD' m W hm hW
  have hc2 : (1 : ℝ) ≤ q.c2 := _hc2
  set P := cyclicModelParams b m W hb0 hb hm hW with hP
  have hPb : P.b = (refParams b hb0 hb).b := rfl
  have hN : 0 < m * W := Nat.mul_pos (by omega) hW
  have hN4 : 4 ≤ m * W := le_trans hm (Nat.le_mul_of_pos_right m hW)
  have hWN : W ≤ m * W := Nat.le_mul_of_pos_left W (by omega)
  have hD0 : (0 : ℝ) < D := by linarith
  have hK1 : (1 : ℝ) ≤ q.C1 := le_trans (le_max_left _ _) hC1
  -- each constant below `q.C1`
  have kθ : CyclicModel.GaussianRing.ERGeneralVectorMDEThetaDomain.thetaDomainControlConstant P q.C0 *
      (1 + D / CyclicModel.GaussianRing.ERGeneralVectorMDEThetaDomain.thetaDomainDecay q.C0) ^ D ≤
        q.C1 := by
    rw [hqC, thetaDomainControlConstant_congr P (refParams b hb0 hb) hPb]
    exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC1
  have kξ : CyclicModel.GaussianRing.ERGeneralVectorMDEXiKappa.xiKappaControlConstant q.kappa P.b *
      (1 + D / CyclicModel.GaussianRing.ERGeneralVectorMDEXiKappa.xiKappaRate q.kappa P.b) ^ D ≤
        q.C1 := by
    rw [hqκ]
    refine le_trans ?_ hC1
    exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  have k6 : CyclicModel.GaussianRing.ERClause6DomainControl.clause6DomainConstant P q.kappa q.C0 *
      (1 + D / CyclicModel.GaussianRing.ERClause6DomainControl.clause6DomainDecay P q.kappa
        q.C0) ^ D ≤ q.C1 := by
    rw [hqκ, hqC, clause6DomainConstant_congr P (refParams b hb0 hb) hPb,
      clause6DomainDecay_congr P (refParams b hb0 hb) hPb]
    refine le_trans ?_ hC1
    refine le_trans ?_ (le_max_right _ _)
    refine le_trans ?_ (le_max_right _ _)
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have k7 : CyclicModel.GaussianRing.ERClause7DomainControl.clause67DomainConstant P q.kappa q.C0 ≤
      q.C1 := by
    rw [hqκ, hqC, clause67DomainConstant_congr P (refParams b hb0 hb) hPb]
    refine le_trans ?_ hC1
    refine le_trans ?_ (le_max_right _ _)
    refine le_trans ?_ (le_max_right _ _)
    refine le_trans ?_ (le_max_right _ _)
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have ktail : max ((3 / 2 : ℝ) ^ D) (max (2 * (Real.sqrt C₀ + 1))
      (max (constC C₀ D) (constW C₀ D))) ≤ q.C1 := by
    refine le_trans ?_ hC1
    refine le_trans ?_ (le_max_right _ _)
    refine le_trans ?_ (le_max_right _ _)
    refine le_trans ?_ (le_max_right _ _)
    refine le_trans ?_ (le_max_right _ _)
    exact le_max_right _ _
  have k32 : (3 / 2 : ℝ) ^ D ≤ q.C1 := le_trans (le_max_left _ _) ktail
  have kR : 2 * (Real.sqrt q.C0 + 1) ≤ q.C1 := by
    rw [hqC]; exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ktail
  have kC : constC q.C0 D ≤ q.C1 := by
    rw [hqC]
    exact le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
      ktail
  have kW : constW q.C0 D ≤ q.C1 := by
    rw [hqC]
    exact le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
      ktail
  have kD' : floorExponent q.C0 D ≤ q.DPrime := by rw [hqC]; exact hD'
  have hq1 : 1 ≤ q.C0 := q.C0_ge_one
  -- heights
  have hpos : ∀ η, ErdosRiabov.ControlHeight q (m * W) η → 0 < η := fun η hη =>
    lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast hN) _) hη.1
  have hΥ0 : ∀ η, 0 < η → ∀ x y,
      0 ≤ Internal.Contracts.Inputs.polynomialControl (m * W) W D η x y := fun η hη x y =>
    (polynomialControl_pos hN hW D hη x y).le
  refine
    { entrywisePositive := ?_
      symmetric := ?_
      clause1 := ?_
      clause2 := ?_
      clause3 := ?_
      clause4 := ?_
      clause5 := ?_
      clause6 := ?_
      clause7 := ?_ }
  · intro η hη x y
    exact polynomialControl_pos hN hW D (hpos η hη) x y
  · intro η _ x y
    exact polynomialControl_symm _ _ D η x y
  · intro z₁ z₂ h₁ h₂ hs x y
    have hη : 0 < min |z₁.im| |z₂.im| :=
      lt_min (spectralDomain_abs_im_pos hN h₁)
        (spectralDomain_abs_im_pos hN h₂)
    exact ⟨(clause1_theta q P hD0 h₁ h₂ x y).trans
        (mul_le_mul_of_nonneg_right kθ (hΥ0 _ hη x y)),
      (clause1_xi q P hD0 h₁ h₂ hs x y).trans
        (mul_le_mul_of_nonneg_right kξ (hΥ0 _ one_pos x y))⟩
  · intro η hη
    have hη0 := hpos η hη
    have hl := loc_pos hN hW hη0
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x y
      refine (polynomialControl_le_max hN hW hD0.le hη0 x y).trans ?_
      rw [div_eq_mul_inv]
      have : 0 < (ErdosRiabov.localizationLength (m * W) W η * η)⁻¹ := by positivity
      exact le_mul_of_one_le_left this.le hK1
    · intro x
      refine (polynomialControl_rowSum_le hN hW (by linarith) hq1 hη0 hη.2 x).trans ?_
      exact div_le_div_of_nonneg_right kR hη0.le
    · intro x y
      exact rpow_floor_le_polynomialControl hN4 hW hD0.le hq1 hη0 hη.2 kD' x y
    · intro hsmall x y
      obtain ⟨hlo, hhi⟩ := polynomialControl_deloc hN hW hD0.le hη0 hsmall x y
      have hNη : 0 < 1 / (((m * W : ℕ) : ℝ) * η) := by
        have : (0 : ℝ) < ((m * W : ℕ) : ℝ) := by exact_mod_cast hN
        positivity
      have h32 : (0 : ℝ) < (3 / 2 : ℝ) ^ D := by positivity
      refine ⟨le_trans ?_ hlo, hhi.trans ?_⟩
      · apply mul_le_mul_of_nonneg_right _ hNη.le
        rw [one_div]
        exact inv_anti₀ h32 k32
      · exact le_mul_of_one_le_left hNη.le hK1
  · intro η₁ η₂ h₁ _ hle x y
    refine (polynomialControl_anti hN hW hD0.le (hpos η₁ h₁) hle x y).trans ?_
    exact le_mul_of_one_le_left (hΥ0 η₁ (hpos η₁ h₁) x y) hK1
  · intro η₁ η₂ h₁ h₂ hle x y
    have hη₂ := hpos η₂ h₂
    refine ⟨fun a => ?_, ?_⟩
    · refine (clause4_pointwise hN hW hD0.le (hpos η₁ h₁) hle x y a).trans ?_
      have hl := loc_pos hN hW hη₂
      rw [div_eq_mul_inv]
      apply mul_le_mul_of_nonneg_right _ (hΥ0 η₁ (hpos η₁ h₁) x y)
      have : 0 < (ErdosRiabov.localizationLength (m * W) W η₂ * η₂)⁻¹ := by positivity
      exact le_mul_of_one_le_left this.le hK1
    · refine (clause4_sqrt hN hW hD q.C0_ge_one (hpos η₁ h₁) hle h₂.2 x y).trans ?_
      exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right kC hη₂.le)
        (Real.sqrt_nonneg _)
  · intro η₁ η₂ h₁ h₂ hle ηi hi x y
    have hη₂ := hpos η₂ h₂
    refine (clause5_bound hN hW hWN hD q.C0_ge_one (hpos η₁ h₁) hle h₂.2 ηi hi x y).trans ?_
    have hl₁ := loc_pos hN hW (hpos η₁ h₁)
    have hl₂ := loc_pos hN hW hη₂
    have hrest : 0 ≤ (ErdosRiabov.localizationLength (m * W) W η₂ /
          ErdosRiabov.localizationLength (m * W) W η₁) *
        Real.sqrt ((ErdosRiabov.localizationLength (m * W) W η₂ * η₂) /
          (ErdosRiabov.localizationLength (m * W) W ηi * ηi)) *
        Real.sqrt (ErdosRiabov.localizationLength (m * W) W η₁ * η₁ *
          Internal.Contracts.Inputs.polynomialControl (m * W) W D η₁ x y) := by positivity
    have hc := div_le_div_of_nonneg_right kW hη₂.le
    calc _ = constW q.C0 D / η₂ * ((ErdosRiabov.localizationLength (m * W) W η₂ /
          ErdosRiabov.localizationLength (m * W) W η₁) *
        Real.sqrt ((ErdosRiabov.localizationLength (m * W) W η₂ * η₂) /
          (ErdosRiabov.localizationLength (m * W) W ηi * ηi)) *
        Real.sqrt (ErdosRiabov.localizationLength (m * W) W η₁ * η₁ *
          Internal.Contracts.Inputs.polynomialControl (m * W) W D η₁ x y)) := by ring
      _ ≤ q.C1 / η₂ * ((ErdosRiabov.localizationLength (m * W) W η₂ /
          ErdosRiabov.localizationLength (m * W) W η₁) *
        Real.sqrt ((ErdosRiabov.localizationLength (m * W) W η₂ * η₂) /
          (ErdosRiabov.localizationLength (m * W) W ηi * ηi)) *
        Real.sqrt (ErdosRiabov.localizationLength (m * W) W η₁ * η₁ *
          Internal.Contracts.Inputs.polynomialControl (m * W) W D η₁ x y)) :=
          mul_le_mul_of_nonneg_right hc hrest
      _ = _ := by ring
  · intro z₁ z₂ h₁ h₂ hs η hthr a b' c
    have hη : 0 < min |z₁.im| |z₂.im| :=
      lt_min (spectralDomain_abs_im_pos hN h₁)
        (spectralDomain_abs_im_pos hN h₂)
    have hthr' : ((W : ℝ) / ((m * W : ℕ) : ℝ)) ^ 2 ≤ min |z₁.im| |z₂.im| :=
      le_trans (le_mul_of_one_le_left (sq_nonneg _) hc2) hthr
    refine (clause6_poly q P hD0 h₁ h₂ hs hthr' a b' c).trans ?_
    have hl := loc_pos hN hW hη
    have hrest : 0 ≤ (min ((ErdosRiabov.cyclicDistance (m * W) b' c : ℝ) + W)
            (ErdosRiabov.localizationLength (m * W) W (min |z₁.im| |z₂.im|)) /
          ErdosRiabov.localizationLength (m * W) W (min |z₁.im| |z₂.im|)) *
        (Internal.Contracts.Inputs.polynomialControl (m * W) W D (min |z₁.im| |z₂.im|) a b' +
          Internal.Contracts.Inputs.polynomialControl (m * W) W D (min |z₁.im| |z₂.im|) a c) := by
      have := hΥ0 _ hη a b'
      have := hΥ0 _ hη a c
      exact mul_nonneg (div_nonneg (le_min (by positivity) hl.le) hl.le) (by positivity)
    rw [mul_assoc _ _ (_ + _), mul_assoc q.C1]
    exact mul_le_mul_of_nonneg_right k6 hrest
  · intro z₁ z₂ h₁ h₂ hs a b'
    refine (clause7_poly q P h₁ h₂ hs a b').trans ?_
    have : (0 : ℝ) < (W : ℝ) ^ 2 := by positivity
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right k7 (Nat.cast_nonneg _)) this.le

end BlockBand.Adapters.ErdosRiabov
