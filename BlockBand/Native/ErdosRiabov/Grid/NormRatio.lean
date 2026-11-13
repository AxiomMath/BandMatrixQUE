module

public import BlockBand.Native.ErdosRiabov.Psi.Cont

set_option autoImplicit false

/-!
# Multiplicative continuity of the scales and size functions in the height

Instead of additive Lipschitz constants, the scales are compared multiplicatively: if two heights
satisfy `η ≤ q η'` and `η' ≤ q η` (`q ≥ 1`), then
* `loc_le_mul`: `ℓ(η) ≤ q^{1/2} ℓ(η')`, `ℓ = localizationLength N W`;
* `lEtaH_le_mul`: `ℓ(η)η ≤ q^{3/2} ℓ(η')η'`;
* `polynomialControl_le_mul`: `Υ_η(x,y) ≤ q^{3/2 + D/2} Υ_{η'}(x,y)` (`D ≥ 0`).

From these, the module `Grid.PsiRatio` proves `PsiData.heights_le_mul` (for `t, s ∈ [0,1]`,
`η_t ≤ (1 + |t - s|/Im z) η_s`, using `Im m ≤ 1`) and `PsiData.sIso_le_mul`,
`PsiData.sAv_le_mul`, `PsiData.norm_le_mul`: the size functions and the normalizations
`(ℓη)^{α} s` of `Ψ` change by at most `q^{E}` between two times, with `E = normExp k D` (for
exponents `0 ≤ α ≤ 1`).
-/

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Grid

open Set
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Internal.Contracts.Inputs (polynomialControl)

/-!
### Comparison of powers
-/

theorem rpow_le_mul_rpow {a b F e : ℝ} (ha : 0 ≤ a) (hF : 0 ≤ F) (hb : 0 ≤ b) (h : a ≤ F * b)
    (he : 0 ≤ e) : a ^ e ≤ F ^ e * b ^ e := by
  rw [← Real.mul_rpow hF hb]
  exact Real.rpow_le_rpow ha h he

theorem rpow_neg_le_mul_rpow_neg {a b F e : ℝ} (ha : 0 < a) (hF : 0 < F) (hb : 0 < b)
    (h : b ≤ F * a) (he : 0 ≤ e) : a ^ (-e) ≤ F ^ e * b ^ (-e) := by
  have h1 : (F * a) ^ (-e) ≤ b ^ (-e) := Real.rpow_le_rpow_of_nonpos hb h (by linarith)
  rw [Real.mul_rpow hF.le ha.le, Real.rpow_neg hF.le] at h1
  have hFe : 0 < F ^ e := Real.rpow_pos_of_pos hF e
  calc a ^ (-e) = F ^ e * ((F ^ e)⁻¹ * a ^ (-e)) := by field_simp
    _ ≤ F ^ e * b ^ (-e) := by gcongr

theorem rpow_mono_exp {q a b : ℝ} (hq : 1 ≤ q) (hab : a ≤ b) : q ^ a ≤ q ^ b :=
  Real.rpow_le_rpow_of_exponent_le hq hab

/-!
### Localization length, `ℓη` and the control
-/

variable {N W : ℕ}

theorem loc_le_mul {η η' q : ℝ} (hη : 0 < η) (hη' : 0 < η') (hq : 1 ≤ q) (h : η' ≤ q * η) :
    localizationLength N W η ≤ q ^ (1 / 2 : ℝ) * localizationLength N W η' := by
  unfold localizationLength
  have hsq : Real.sqrt q = q ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow q
  have hs1 : 1 ≤ Real.sqrt q := Real.one_le_sqrt.mpr hq
  have hsη : Real.sqrt η' ≤ Real.sqrt q * Real.sqrt η := by
    rw [← Real.sqrt_mul (by linarith)]
    exact Real.sqrt_le_sqrt h
  have hpos : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  have hpos' : 0 < Real.sqrt η' := Real.sqrt_pos.mpr hη'
  have hW : (0 : ℝ) ≤ W := Nat.cast_nonneg _
  have h1 : (W : ℝ) / Real.sqrt η ≤ Real.sqrt q * ((W : ℝ) / Real.sqrt η') := by
    rw [div_le_iff₀ hpos, mul_comm, ← mul_assoc]
    rw [mul_div_assoc', le_div_iff₀ hpos']
    nlinarith [mul_le_mul_of_nonneg_left hsη hW]
  rw [← hsq]
  calc min ((W : ℝ) / Real.sqrt η) (N : ℝ) ≤ min (Real.sqrt q * ((W : ℝ) / Real.sqrt η'))
        (Real.sqrt q * N) := min_le_min h1 (le_mul_of_one_le_left (Nat.cast_nonneg _) hs1)
    _ = Real.sqrt q * min ((W : ℝ) / Real.sqrt η') (N : ℝ) :=
        (mul_min_of_nonneg _ _ (Real.sqrt_nonneg q)).symm

theorem lEtaH_le_mul {η η' q : ℝ} (hη : 0 < η) (hη' : 0 < η') (hq : 1 ≤ q) (h : η ≤ q * η')
    (h' : η' ≤ q * η) :
    localizationLength N W η * η ≤ q ^ (3 / 2 : ℝ) * (localizationLength N W η' * η') := by
  have h1 := loc_le_mul (N := N) (W := W) hη hη' hq h'
  have hl0 : 0 ≤ localizationLength N W η' := by
    unfold localizationLength
    exact le_min (by positivity) (Nat.cast_nonneg _)
  have hq0 : 0 < q := by linarith
  have e : q ^ (3 / 2 : ℝ) = q ^ (1 / 2 : ℝ) * q := by
    rw [← Real.rpow_add_one hq0.ne']
    norm_num
  rw [e]
  have hl : 0 ≤ localizationLength N W η := by
    unfold localizationLength
    exact le_min (by positivity) (Nat.cast_nonneg _)
  calc localizationLength N W η * η ≤ (q ^ (1 / 2 : ℝ) * localizationLength N W η') * (q * η') :=
        mul_le_mul h1 h hη.le (by positivity)
    _ = q ^ (1 / 2 : ℝ) * q * (localizationLength N W η' * η') := by ring

/-- **The control is multiplicatively continuous in the height.** -/
theorem polynomialControl_le_mul (hN : 0 < N) (hW : 0 < W) {D : ℝ} (hD : 0 ≤ D) {η η' q : ℝ}
    (hη : 0 < η) (hη' : 0 < η') (hq : 1 ≤ q) (h : η ≤ q * η') (h' : η' ≤ q * η)
    (x y : Fin N) :
    polynomialControl N W D η x y ≤ q ^ (3 / 2 + D / 2 : ℝ) * polynomialControl N W D η' x y := by
  unfold polynomialControl
  set ℓ := localizationLength N W η
  set ℓ' := localizationLength N W η'
  have hl : 0 < ℓ := Adapters.ErdosRiabov.loc_pos hN hW hη
  have hl' : 0 < ℓ' := Adapters.ErdosRiabov.loc_pos hN hW hη'
  have hq0 : 0 < q := by linarith
  set d : ℝ := (cyclicDistance N x y : ℝ)
  have hd : 0 ≤ d := Nat.cast_nonneg _
  -- the prefactor
  have hA : (ℓ * η)⁻¹ ≤ q ^ (3 / 2 : ℝ) * (ℓ' * η')⁻¹ := by
    have h2 := lEtaH_le_mul (N := N) (W := W) hη' hη hq h' h
    have hp : 0 < ℓ * η := mul_pos hl hη
    have hp' : 0 < ℓ' * η' := mul_pos hl' hη'
    have := rpow_neg_le_mul_rpow_neg hp (Real.rpow_pos_of_pos hq0 (3 / 2)) hp' h2 zero_le_one
    simpa [Real.rpow_neg_one, Real.rpow_one] using this
  -- the decay factor
  have hB : (1 + d / ℓ) ^ (-D) ≤ q ^ (D / 2) * (1 + d / ℓ') ^ (-D) := by
    have hloc := loc_le_mul (N := N) (W := W) hη hη' hq h'
    have hsq1 : 1 ≤ q ^ (1 / 2 : ℝ) := Real.one_le_rpow hq (by norm_num)
    have hx : 0 < 1 + d / ℓ := by positivity
    have hx' : 0 < 1 + d / ℓ' := by positivity
    have hcmp : 1 + d / ℓ' ≤ q ^ (1 / 2 : ℝ) * (1 + d / ℓ) := by
      have h3 : d / ℓ' ≤ q ^ (1 / 2 : ℝ) * (d / ℓ) := by
        have hr : 1 ≤ q ^ (1 / 2 : ℝ) * ℓ' / ℓ := by
          rw [le_div_iff₀ hl]
          linarith [hloc]
        calc d / ℓ' = d / ℓ' * 1 := (mul_one _).symm
          _ ≤ d / ℓ' * (q ^ (1 / 2 : ℝ) * ℓ' / ℓ) := by gcongr
          _ = q ^ (1 / 2 : ℝ) * (d / ℓ) := by field_simp
      nlinarith
    have := rpow_neg_le_mul_rpow_neg hx (Real.rpow_pos_of_pos hq0 _) hx' hcmp hD
    rwa [← Real.rpow_mul hq0.le, show (1 / 2 : ℝ) * D = D / 2 by ring] at this
  have hsplit : q ^ (3 / 2 + D / 2 : ℝ) = q ^ (3 / 2 : ℝ) * q ^ (D / 2) :=
    Real.rpow_add hq0 _ _
  rw [hsplit]
  have hB0 : 0 ≤ (1 + d / ℓ) ^ (-D) := Real.rpow_nonneg (by positivity) _
  calc (ℓ * η)⁻¹ * (1 + d / ℓ) ^ (-D)
      ≤ (q ^ (3 / 2 : ℝ) * (ℓ' * η')⁻¹) * (q ^ (D / 2) * (1 + d / ℓ') ^ (-D)) :=
        mul_le_mul hA hB hB0 (by positivity)
    _ = q ^ (3 / 2 : ℝ) * q ^ (D / 2) * ((ℓ' * η')⁻¹ * (1 + d / ℓ') ^ (-D)) := by ring

/-!
### Products and square roots
-/

theorem sqrt_prod_le_mul {ι : Type} (s : Finset ι) (f g : ι → ℝ) {F : ℝ} (hF : 0 ≤ F)
    (hf : ∀ i ∈ s, 0 ≤ f i) (h : ∀ i ∈ s, f i ≤ F * g i) :
    Real.sqrt (∏ i ∈ s, f i) ≤ F ^ ((s.card : ℝ) / 2) * Real.sqrt (∏ i ∈ s, g i) := by
  have hp : ∏ i ∈ s, f i ≤ ∏ i ∈ s, (F * g i) := Finset.prod_le_prod₀ hf h
  rw [Finset.prod_mul_distrib, Finset.prod_const] at hp
  calc Real.sqrt (∏ i ∈ s, f i) ≤ Real.sqrt (F ^ s.card * ∏ i ∈ s, g i) := Real.sqrt_le_sqrt hp
    _ = Real.sqrt (F ^ s.card) * Real.sqrt (∏ i ∈ s, g i) :=
        Real.sqrt_mul (pow_nonneg hF _) _
    _ = F ^ ((s.card : ℝ) / 2) * Real.sqrt (∏ i ∈ s, g i) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hF]
        congr 2
        ring

end BlockBand.Native.ErdosRiabov.Grid
