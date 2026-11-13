module

public import BlockBand.Transmission.PathScalar.AbsorbedRecursion
public import BlockBand.Transmission.PathScalar.Assembly

/-!
# The absorbed fixed-moment clause from the passive one-port step

Proof (near-end growth, not the centre growth of the paper): fix `r`, `ε`; the profile
`absProfile W r ε` grows the path `1, …, r` with each block keeping its absorption
(`nearSchur_absorbed_eq`). Each step is a passive one-port step at the absorbed input
`X_j - iε'_j` (`ae_absorbed_step`), and the abstract stopped recursion
(`eLpNorm_delta_le`, domain `d₀/2`) gives `‖δ_r‖_p ≤ C/W`; the exit event is paid by Markov at
`q = p + 1` and the union bound over `r ≤ TW`, with the deterministic bound `δ_r ≤ η_κ⁻¹ + 1`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PathScalar

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.Bridge BlockBand.Transmission.PassiveCovariance
open scoped ENNReal NNReal Matrix ComplexOrder

variable {W : ℕ}

/-- **The start bound** (proved by `absorbedStartBound_holds`): the first length of the absorbed
near-end growth has `‖δ₀(X_1)‖_q ≤ C/W`, uniformly over profiles `0 ≤ κ ≤ K`. -/
def AbsorbedStartBound : Prop :=
  ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ' K q : ℝ, 0 < κ' → 0 ≤ K → 1 ≤ q →
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ E ∈ bulkInterval κ',
      ∀ κ : ℝ → ℝ, (∀ s, 0 ≤ κ s ∧ κ s ≤ K) →
        eLpNorm (absorbedDelta b E κ W 1) (ENNReal.ofReal q) (growthPathLaw W b) ≤
          ENNReal.ofReal (C / W)

/-- The exit-event arithmetic: `(A + rB)/W^q ≤ (A + T₊B) W^{-p}` for `q = p + 1`, `r ≤ TW`. -/
theorem bad_arith {A B T p : ℝ} {r : ℕ} {x : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hx : 1 ≤ x)
    (hr : (r : ℝ) ≤ T * x) :
    A * x⁻¹ ^ (p + 1) + r * (B * x⁻¹ ^ (p + 1)) ≤ (A + max T 0 * B) * x⁻¹ ^ p := by
  have hx0 : 0 < x := by linarith
  have hi : x⁻¹ ^ (p + 1) = x⁻¹ ^ p * x⁻¹ := by
    rw [Real.rpow_add (inv_pos.2 hx0), Real.rpow_one]
  have hxp : 0 ≤ x⁻¹ ^ p := Real.rpow_nonneg (inv_nonneg.2 hx0.le) _
  have hr' : (r : ℝ) * x⁻¹ ≤ max T 0 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hx0]
    exact hr.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hx0.le)
  have hxi : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hx
  rw [hi]
  have h1 : A * (x⁻¹ ^ p * x⁻¹) ≤ A * x⁻¹ ^ p := by
    have := mul_le_mul_of_nonneg_left hxi hxp
    nlinarith
  have h2 : (r : ℝ) * (B * (x⁻¹ ^ p * x⁻¹)) ≤ max T 0 * B * x⁻¹ ^ p := by
    have : (r : ℝ) * (B * (x⁻¹ ^ p * x⁻¹)) = B * x⁻¹ ^ p * ((r : ℝ) * x⁻¹) := by ring
    rw [this]
    have := mul_le_mul_of_nonneg_left hr' (mul_nonneg hB hxp)
    linarith
  nlinarith

/-- The final real arithmetic of the absorbed clause. -/
theorem absorbed_final_arith {S1 c₀ Cp ρ Z M x : ℝ} (hx : 1 ≤ x) (hc₀ : 0 ≤ c₀)
    (hρ1 : ρ < 1) :
    S1 / x + (c₀ / x ^ 2 + Cp / x) / (1 - ρ) + Z * x⁻¹ * M ≤
      (S1 + (c₀ + Cp) / (1 - ρ) + Z * M) / x := by
  have hx0 : 0 < x := by linarith
  have h1ρ : 0 < 1 - ρ := by linarith
  have hc : c₀ / x ^ 2 ≤ c₀ / x := by
    apply div_le_div_of_nonneg_left hc₀ hx0; nlinarith
  have : (c₀ / x ^ 2 + Cp / x) / (1 - ρ) ≤ ((c₀ + Cp) / (1 - ρ)) / x := by
    rw [div_div, mul_comm, ← div_div]
    apply div_le_div_of_nonneg_right _ h1ρ.le
    rw [add_div]; linarith
  calc S1 / x + (c₀ / x ^ 2 + Cp / x) / (1 - ρ) + Z * x⁻¹ * M
      ≤ S1 / x + ((c₀ + Cp) / (1 - ρ)) / x + Z * M / x := by
        rw [show Z * x⁻¹ * M = Z * M / x by field_simp]; linarith
    _ = (S1 + (c₀ + Cp) / (1 - ρ) + Z * M) / x := by ring

/-- **The absorbed fixed-moment clause** (`PassiveInitialScalarContract.absorbedMoment`) from the
passive one-port mean and fluctuation steps and the start bound. -/
theorem absorbedMoment_of_steps (hMean : PassiveMeanStep) (hFl : PassiveFluctuationStep)
    (hStart : AbsorbedStartBound) : AbsorbedMomentClause := by
  intro b hb hb' κ' T K p hκ' hK hp
  obtain ⟨d₀, ρ, Cm, Wm, hd₀, hρ0, hρ1, hCm, hmean⟩ := hMean b hb hb' κ' hκ'
  obtain ⟨Cp, Wp, hCp, hflp⟩ := hFl b hb hb' κ' hκ' p hp
  obtain ⟨Cq, Wq, hCq, hflq⟩ := hFl b hb hb' κ' hκ' (p + 1) (by linarith)
  obtain ⟨S1, Ws1, hS1, hst1⟩ := hStart b hb hb' κ' K p hκ' hK hp
  obtain ⟨S2, Ws2, hS2, hst2⟩ := hStart b hb hb' κ' K (p + 1) hκ' hK (by linarith)
  have hηl := etaLow_pos (by linarith : b < 1) hκ'
  have h1ρ : 0 < 1 - ρ := by linarith
  set ηl := etaLow b κ' with hηl_def
  set c₀ := Cm + K / ηl ^ 2 with hc₀
  have hc₀0 : 0 ≤ c₀ := by positivity
  set d := d₀ / 2 with hd
  set t := (1 - ρ) * d / 2 with ht
  have hd0 : 0 < d := by positivity
  have ht0 : 0 < t := by positivity
  set A := (d / 2)⁻¹ ^ (p + 1) * S2 ^ (p + 1) with hA
  set B := t⁻¹ ^ (p + 1) * Cq ^ (p + 1) with hB
  have hA0 : 0 ≤ A := mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hS2 _)
  have hB0 : 0 ≤ B := mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hCq _)
  set M := ηl⁻¹ + 1 with hM
  have hM0 : 0 ≤ M := by positivity
  set Z := (A + max T 0 * B) ^ p⁻¹ with hZ
  have hZ0 : 0 ≤ Z := Real.rpow_nonneg (by positivity) _
  refine ⟨S1 + (c₀ + Cp) / (1 - ρ) + Z * M,
    max (max (max Wm Wp) (max Wq (max Ws1 Ws2)))
      (max 1 (max ⌈K / (ηl ^ 2 * (d₀ / 2))⌉₊ ⌈c₀ / ((1 - ρ) * d / 2)⌉₊)), ?_⟩
  intro W hW E hE r hr hrT ε hε
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hWm, hWp⟩, hWq, hWs1, hWs2⟩, hW1, hWK', hWc'⟩ := hW
  have hW0 : 0 < W := by omega
  have hx : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hx0 : (0 : ℝ) < W := by linarith
  have hWW : (W : ℝ) ≤ (W : ℝ) ^ 2 := by nlinarith
  have hWK : K / (ηl ^ 2 * (W : ℝ) ^ 2) ≤ d₀ / 2 := by
    have hc := Nat.le_ceil (K / (ηl ^ 2 * (d₀ / 2)))
    have hc' : ((⌈K / (ηl ^ 2 * (d₀ / 2))⌉₊ : ℕ) : ℝ) ≤ W := by exact_mod_cast hWK'
    have h1 : K / (ηl ^ 2 * (d₀ / 2)) ≤ (W : ℝ) ^ 2 := by linarith
    rw [div_le_iff₀ (by positivity)] at h1
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hcW : c₀ / (W : ℝ) ^ 2 ≤ (1 - ρ) * d / 2 := by
    have hc := Nat.le_ceil (c₀ / ((1 - ρ) * d / 2))
    have hc' : ((⌈c₀ / ((1 - ρ) * d / 2)⌉₊ : ℕ) : ℝ) ≤ W := by exact_mod_cast hWc'
    have h1 : c₀ / ((1 - ρ) * d / 2) ≤ (W : ℝ) ^ 2 := by linarith
    rw [div_le_iff₀ (by positivity)] at h1
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨h1, h2⟩ := bulk_bounds hκ' hE
  set κ := absProfile W r ε with hκ
  have hκ0 : ∀ s, 0 ≤ κ s := absProfile_nonneg fun i => (hε i).1
  have hκK : ∀ s, 0 ≤ κ s ∧ κ s ≤ K := fun s => ⟨hκ0 s, absProfile_le hW0 hK (fun i => (hε i).2) s⟩
  have hκm : ∀ (m : ℕ) (i : Fin m), layerAbsorption W κ m i ≤ K / (W : ℝ) ^ 2 :=
    fun m i => (layerAbsorption_absProfile_mem hW0 hK hε m i).2
  have hobj : (fun ω => jetDistance0 b E (nearSchur (boundaryZ b E)
      (absorbedPathSchur E ε (pathAt W r ω)))) = absorbedDelta b E κ W r := by
    funext ω; rw [absorbedDelta, nearSchur_absorbed_eq b E hW0 ε ω]
  rw [hobj]
  have hstep := ae_absorbed_step hb hb' hκ' hρ0 hρ1 hK hmean hWm hW1 hWK hE hκ0 hκm
  have hstep' : ∀ᵐ ω ∂growthPathLaw W b, ∀ j, 1 ≤ j → j < r →
      absorbedDelta b E κ W j ω ≤ d → absorbedDelta b E κ W (j + 1) ω ≤
        ρ * absorbedDelta b E κ W j ω + c₀ / (W : ℝ) ^ 2 + stepFluct b E κ W (j + 1 - 1) ω :=
    hstep.mono fun ω h j hj _ hdj => by simpa using h j hj hdj
  have hξ : ∀ j, 2 ≤ j → j ≤ r → eLpNorm (stepFluct b E κ W (j - 1)) (ENNReal.ofReal p)
      (growthPathLaw W b) ≤ ENNReal.ofReal (Cp / W) := fun j _ _ =>
    eLpNorm_stepFluct_le (by linarith) h1 h2 (by linarith) hκ0 (j - 1)
      fun X hX => hflp W hWp E hE X hX
  have key := eLpNorm_delta_le (δ := fun j => absorbedDelta b E κ W j)
    (ξ := fun j => stepFluct b E κ W (j - 1)) (d := d) (t := t) (ρ := ρ) (c := c₀ / (W : ℝ) ^ 2)
    (n := r) (growthPathLaw W b) hp hρ0 hρ1 hd0 (by positivity) (by linarith) (by positivity)
    (by positivity) (fun j ω => absorbedDelta_nonneg b E κ j ω)
    (fun j ω => stepFluct_nonneg b E κ (j - 1) ω) (fun j => measurable_absorbedDelta b E κ j)
    (fun j => measurable_stepFluct b E κ (j - 1)) hstep' (hst1 W hWs1 E hE κ hκK) hξ hr le_rfl
    (ae_absorbed_bound hb hb' hκ' hE hκ0 r)
  have hbad := measure_bad_le (δ := fun j => absorbedDelta b E κ W j)
    (ξ := fun j => stepFluct b E κ W (j - 1)) (d := d) (t := t) (growthPathLaw W b) r
  have hm1 : growthPathLaw W b {ω | d / 2 < absorbedDelta b E κ W 1 ω} ≤
      ENNReal.ofReal ((d / 2)⁻¹ ^ (p + 1) * (S2 / W) ^ (p + 1)) :=
    markov_ofReal _ (absorbedDelta_nonneg b E κ 1) (by linarith) (by positivity) (by positivity)
      (hst2 W hWs2 E hE κ hκK)
  have hm2 : ∀ j ∈ Finset.Icc 2 r, growthPathLaw W b {ω | t < stepFluct b E κ W (j - 1) ω} ≤
      ENNReal.ofReal (t⁻¹ ^ (p + 1) * (Cq / W) ^ (p + 1)) := fun j _ =>
    markov_ofReal _ (stepFluct_nonneg b E κ (j - 1)) (by linarith) ht0 (by positivity)
      (eLpNorm_stepFluct_le (by linarith) h1 h2 (by linarith) hκ0 (j - 1)
        fun X hX => hflq W hWq E hE X hX)
  have hc2 : 0 ≤ t⁻¹ ^ (p + 1) * (Cq / W) ^ (p + 1) :=
    mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _)
  have hsum : ∑ j ∈ Finset.Icc 2 r, growthPathLaw W b {ω | t < stepFluct b E κ W (j - 1) ω} ≤
      ENNReal.ofReal (r * (t⁻¹ ^ (p + 1) * (Cq / W) ^ (p + 1))) := by
    refine (Finset.sum_le_sum hm2).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ hc2)
    rw [Nat.card_Icc]; exact_mod_cast (by omega : r + 1 - 2 ≤ r)
  have hWi : (0 : ℝ) ≤ (W : ℝ)⁻¹ := by positivity
  have hdiv : ∀ y : ℝ, 0 ≤ y → (y / W) ^ (p + 1) = y ^ (p + 1) * (W : ℝ)⁻¹ ^ (p + 1) :=
    fun y hy => by rw [div_eq_mul_inv, Real.mul_rpow hy hWi]
  have hXbad : growthPathLaw W b (goodEvent (fun j => absorbedDelta b E κ W j)
      (fun j => stepFluct b E κ W (j - 1)) d t r)ᶜ ≤
        ENNReal.ofReal ((A + max T 0 * B) * (W : ℝ)⁻¹ ^ p) := by
    refine hbad.trans ((add_le_add hm1 hsum).trans ?_)
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := bad_arith (A := A) (B := B) (T := T) (p := p) (r := r) hA0 hB0 hx hrT
    rw [hdiv S2 hS2, hdiv Cq hCq]
    calc (d / 2)⁻¹ ^ (p + 1) * (S2 ^ (p + 1) * (W : ℝ)⁻¹ ^ (p + 1)) +
          r * (t⁻¹ ^ (p + 1) * (Cq ^ (p + 1) * (W : ℝ)⁻¹ ^ (p + 1)))
        = A * (W : ℝ)⁻¹ ^ (p + 1) + r * (B * (W : ℝ)⁻¹ ^ (p + 1)) := by
          simp only [hA, hB]; ring
      _ ≤ _ := this
  have hp0 : (0 : ℝ) < p := by linarith
  have hpow : growthPathLaw W b (goodEvent (fun j => absorbedDelta b E κ W j)
      (fun j => stepFluct b E κ W (j - 1)) d t r)ᶜ ^ (ENNReal.ofReal p).toReal⁻¹ ≤
        ENNReal.ofReal (Z * (W : ℝ)⁻¹) := by
    rw [ENNReal.toReal_ofReal hp0.le]
    refine (ENNReal.rpow_le_rpow hXbad (inv_nonneg.2 hp0.le)).trans ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (inv_nonneg.2 hp0.le),
      Real.mul_rpow (by positivity) (Real.rpow_nonneg hWi _),
      Real.rpow_rpow_inv hWi hp0.ne']
  refine key.trans ?_
  calc ENNReal.ofReal (S1 / W + (c₀ / (W : ℝ) ^ 2 + Cp / W) / (1 - ρ)) +
        growthPathLaw W b (goodEvent (fun j => absorbedDelta b E κ W j)
          (fun j => stepFluct b E κ W (j - 1)) d t r)ᶜ ^ (ENNReal.ofReal p).toReal⁻¹ *
            ENNReal.ofReal M
      ≤ ENNReal.ofReal (S1 / W + (c₀ / (W : ℝ) ^ 2 + Cp / W) / (1 - ρ)) +
          ENNReal.ofReal (Z * (W : ℝ)⁻¹) * ENNReal.ofReal M := by gcongr
    _ = ENNReal.ofReal (S1 / W + (c₀ / (W : ℝ) ^ 2 + Cp / W) / (1 - ρ) +
          Z * (W : ℝ)⁻¹ * M) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
    _ ≤ ENNReal.ofReal ((S1 + (c₀ + Cp) / (1 - ρ) + Z * M) / W) :=
        ENNReal.ofReal_le_ofReal (absorbed_final_arith hx hc₀0 hρ1)

end BlockBand.Transmission.PathScalar
