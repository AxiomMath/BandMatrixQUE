module

public import BlockBand.Adapters.ErdosRiabov.Clause23

/-!
# Polynomial control at arbitrary heights

Comparison of the localization length and of the polynomial control `Υ_h` at two heights, a
lower bound below a ceiling, and exact proportionality in the delocalized regime (parts (a)–(d)
of the polynomial control lemma).

For `0 < h ≤ h'`:
* `loc_le_sqrt_ratio_mul`, `loc_mul_le_ratio_mul` ((a)): `ℓ(h) ≤ √(h'/h) ℓ(h')`,
  `f(h') ≤ (h'/h) f(h)` (the other halves are `loc_antitone`, `loc_mul_mono`);
* `polynomialControl_mono` ((b)): `Υ_{h'} ≤ Υ_h` (a restatement of
  `polynomialControl_anti`);
* `polynomialControl_reverse` ((b)): `Υ_h ≤ (h'/h)^{1+D/2} Υ_{h'}`;
* `polynomialControl_lower` ((c), ceiling `H ≥ 1` in place of `C₀ + 1`, `r = √H`,
  `W ≤ N`, `h ≤ H`): `W/r ≤ ℓ(h)`, `f(h) ≤ W r` and `Υ_h ≥ (W r)⁻¹ (1 + r d/W)^{-D}`;
* `polynomialControl_deloc_prop` ((d)): if `ℓ(h) = ℓ(h') = N` then
  `Υ_{h'} = (h/h') Υ_h` (any `h, h' > 0`); `polynomialControl_deloc_prop_of_le` gives it for
  `h, h' ≤ (W/N)²`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Kernel

open BlockBand.External BlockBand.Internal.Contracts.Inputs BlockBand.Adapters.ErdosRiabov

/-!
## Localization length (a)
-/

/-- `ℓ(h) ≤ √(h'/h) ℓ(h')` for `0 < h ≤ h'`. -/
theorem loc_le_sqrt_ratio_mul (N W : ℕ) {h h' : ℝ} (hh : 0 < h) (hhh : h ≤ h') :
    ErdosRiabov.localizationLength N W h ≤
      Real.sqrt (h' / h) * ErdosRiabov.localizationLength N W h' := by
  have hh' : 0 < h' := hh.trans_le hhh
  have hs : 0 < Real.sqrt h := Real.sqrt_pos.2 hh
  have hs' : 0 < Real.sqrt h' := Real.sqrt_pos.2 hh'
  have hr1 : 1 ≤ Real.sqrt (h' / h) := Real.one_le_sqrt.mpr ((one_le_div hh).2 hhh)
  unfold ErdosRiabov.localizationLength
  rw [mul_min_of_nonneg _ _ (Real.sqrt_nonneg _)]
  have heq : Real.sqrt (h' / h) * ((W : ℝ) / Real.sqrt h') = (W : ℝ) / Real.sqrt h := by
    rw [Real.sqrt_div' _ hh.le]
    field_simp
  rw [heq]
  exact min_le_min le_rfl (le_mul_of_one_le_left (Nat.cast_nonneg _) hr1)

/-- `f(h') ≤ (h'/h) f(h)` for `0 < h ≤ h'`, `f(h) = ℓ(h) h`. -/
theorem loc_mul_le_ratio_mul (N W : ℕ) {h h' : ℝ} (hh : 0 < h) (hhh : h ≤ h') :
    ErdosRiabov.localizationLength N W h' * h' ≤
      h' / h * (ErdosRiabov.localizationLength N W h * h) := by
  have hh' : 0 < h' := hh.trans_le hhh
  have hs : 0 < Real.sqrt h := Real.sqrt_pos.2 hh
  have hsh : Real.sqrt h ≤ Real.sqrt h' := Real.sqrt_le_sqrt hhh
  rw [loc_mul_eq N W hh', loc_mul_eq N W hh, mul_min_of_nonneg _ _ (by positivity)]
  have h2 : h' / h * ((N : ℝ) * h) = (N : ℝ) * h' := by field_simp
  rw [h2]
  refine le_min (min_le_left _ _ |>.trans ?_) (min_le_right _ _)
  -- `W √h' ≤ (h'/h) W √h`, i.e. `√h √h' ≤ h' = √h'²`
  have hsq : Real.sqrt h' * Real.sqrt h' = h' := Real.mul_self_sqrt hh'.le
  have hsq' : Real.sqrt h * Real.sqrt h = h := Real.mul_self_sqrt hh.le
  have key : Real.sqrt h' ≤ h' / h * Real.sqrt h := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hh]
    have hp := mul_nonneg (mul_nonneg (Real.sqrt_nonneg h) (Real.sqrt_nonneg h'))
      (sub_nonneg.2 hsh)
    nlinarith [Real.sqrt_nonneg h']
  calc (W : ℝ) * Real.sqrt h' ≤ (W : ℝ) * (h' / h * Real.sqrt h) :=
        mul_le_mul_of_nonneg_left key (Nat.cast_nonneg _)
    _ = h' / h * ((W : ℝ) * Real.sqrt h) := by ring

/-!
## Monotonicity and reverse comparison (b)
-/

/-- **Monotonicity** (b): `Υ_{h'} ≤ Υ_h` for `0 < h ≤ h'` (restatement of
`polynomialControl_anti`). -/
theorem polynomialControl_mono {N W : ℕ} (hN : 0 < N) (hW : 0 < W) {D : ℝ} (hD : 0 ≤ D)
    {h h' : ℝ} (hh : 0 < h) (hhh : h ≤ h') (x y : Fin N) :
    polynomialControl N W D h' x y ≤ polynomialControl N W D h x y :=
  polynomialControl_anti hN hW hD hh hhh x y

/-- **Reverse comparison** (b): `Υ_h ≤ (h'/h)^{1+D/2} Υ_{h'}` for `0 < h ≤ h'`. -/
theorem polynomialControl_reverse {N W : ℕ} (hN : 0 < N) (hW : 0 < W) {D : ℝ} (hD : 0 ≤ D)
    {h h' : ℝ} (hh : 0 < h) (hhh : h ≤ h') (x y : Fin N) :
    polynomialControl N W D h x y ≤
      (h' / h) ^ (1 + D / 2) * polynomialControl N W D h' x y := by
  have hh' : 0 < h' := hh.trans_le hhh
  rw [polynomialControl_eq hN hW D hh, polynomialControl_eq hN hW D hh']
  set L := ErdosRiabov.localizationLength N W h with hLdef
  set L' := ErdosRiabov.localizationLength N W h' with hL'def
  set d : ℝ := (ErdosRiabov.cyclicDistance N x y : ℝ) with hddef
  set q := h' / h with hqdef
  have hL : 0 < L := loc_pos hN hW hh
  have hL' : 0 < L' := loc_pos hN hW hh'
  have hd : 0 ≤ d := Nat.cast_nonneg _
  have hq : 0 < q := div_pos hh' hh
  have hq1 : 1 ≤ q := (one_le_div hh).2 hhh
  have hF : 0 < L * h := mul_pos hL hh
  have hF' : 0 < L' * h' := mul_pos hL' hh'
  have hLL : L ≤ Real.sqrt q * L' := loc_le_sqrt_ratio_mul N W hh hhh
  have hFF : L' * h' ≤ q * (L * h) := loc_mul_le_ratio_mul N W hh hhh
  have hr1 : 1 ≤ Real.sqrt q := Real.one_le_sqrt.mpr hq1
  -- step 1: `f(h)⁻¹ ≤ q f(h')⁻¹`
  have step1 : (L * h)⁻¹ ≤ q * (L' * h')⁻¹ := by
    calc (L * h)⁻¹ = q * (q * (L * h))⁻¹ := by field_simp
      _ ≤ q * (L' * h')⁻¹ := mul_le_mul_of_nonneg_left (inv_anti₀ hF' hFF) hq.le
  -- step 2: `F_D(L,d) ≤ q^{D/2} F_D(L',d)`
  have hbase : 1 + d / L' ≤ Real.sqrt q * (1 + d / L) := by
    have hdl : d / L' ≤ Real.sqrt q * (d / L) := by
      rw [mul_div_assoc', div_le_div_iff₀ hL' hL]
      nlinarith
    nlinarith [div_nonneg hd hL.le]
  have hu : 0 < (1 + d / L) ^ D := Real.rpow_pos_of_pos (by positivity) _
  have hv : 0 < (1 + d / L') ^ D := Real.rpow_pos_of_pos (by positivity) _
  have hc : 0 < q ^ (D / 2) := Real.rpow_pos_of_pos hq _
  have hvu : (1 + d / L') ^ D ≤ q ^ (D / 2) * (1 + d / L) ^ D := by
    calc (1 + d / L') ^ D ≤ (Real.sqrt q * (1 + d / L)) ^ D :=
          Real.rpow_le_rpow (by positivity) hbase hD
      _ = Real.sqrt q ^ D * (1 + d / L) ^ D :=
          Real.mul_rpow (Real.sqrt_nonneg _) (by positivity)
      _ = q ^ (D / 2) * (1 + d / L) ^ D := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hq.le]
          congr 2
          ring
  have step2 : decayF D L d ≤ q ^ (D / 2) * decayF D L' d := by
    unfold decayF
    calc ((1 + d / L) ^ D)⁻¹ = (q ^ (D / 2) * (1 + d / L) ^ D)⁻¹ * q ^ (D / 2) := by
          field_simp
      _ ≤ ((1 + d / L') ^ D)⁻¹ * q ^ (D / 2) :=
          mul_le_mul_of_nonneg_right (inv_anti₀ hv hvu) hc.le
      _ = q ^ (D / 2) * ((1 + d / L') ^ D)⁻¹ := mul_comm _ _
  have hsplit : q ^ (1 + D / 2) = q * q ^ (D / 2) := by
    rw [Real.rpow_add hq, Real.rpow_one]
  rw [hsplit]
  calc (L * h)⁻¹ * decayF D L d ≤ (q * (L' * h')⁻¹) * (q ^ (D / 2) * decayF D L' d) :=
        mul_le_mul step1 step2 (decayF_pos hL hd).le (by positivity)
    _ = q * q ^ (D / 2) * ((L' * h')⁻¹ * decayF D L' d) := by ring

/-!
## Lower bound below a ceiling (c)
-/

/-- `W/√H ≤ ℓ(h)` and `ℓ(h) h ≤ W √H` for `0 < h ≤ H`, `H ≥ 1`, `W ≤ N`. -/
theorem loc_bounds_of_le {N W : ℕ} (hWN : W ≤ N) {H h : ℝ} (hH : 1 ≤ H)
    (hh : 0 < h) (hhH : h ≤ H) :
    (W : ℝ) / Real.sqrt H ≤ ErdosRiabov.localizationLength N W h ∧
      ErdosRiabov.localizationLength N W h * h ≤ (W : ℝ) * Real.sqrt H := by
  have hsH : 0 < Real.sqrt H := Real.sqrt_pos.2 (by linarith)
  constructor
  · rw [div_le_iff₀ hsH, mul_comm]
    exact W_le_sqrt_mul_loc hWN hH hh hhH
  · rw [loc_mul_eq N W hh]
    exact (min_le_left _ _).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hhH) (Nat.cast_nonneg _))

/-- **Lower bound** (c), with the ceiling `H` in place of `C₀ + 1` and `r = √H`: for `0 < h ≤ H`,
`H ≥ 1`, `1 ≤ W ≤ N`, `D ≥ 0`,
`Υ_h(x,y) ≥ (W r)⁻¹ (1 + r d(x,y)/W)^{-D}`. -/
theorem polynomialControl_lower {N W : ℕ} (hWN : W ≤ N) (hW : 0 < W) {D : ℝ} (hD : 0 ≤ D)
    {H h : ℝ} (hH : 1 ≤ H) (hh : 0 < h) (hhH : h ≤ H) (x y : Fin N) :
    ((W : ℝ) * Real.sqrt H)⁻¹ *
        (1 + Real.sqrt H * (ErdosRiabov.cyclicDistance N x y : ℝ) / W) ^ (-D) ≤
      polynomialControl N W D h x y := by
  have hN : 0 < N := lt_of_lt_of_le hW hWN
  obtain ⟨hl, hf⟩ := loc_bounds_of_le hWN hH hh hhH
  have hsH : 0 < Real.sqrt H := Real.sqrt_pos.2 (by linarith)
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hL := loc_pos hN hW hh
  set L := ErdosRiabov.localizationLength N W h
  set d : ℝ := (ErdosRiabov.cyclicDistance N x y : ℝ)
  have hd : 0 ≤ d := Nat.cast_nonneg _
  unfold polynomialControl
  have hbase : 1 + d / L ≤ 1 + Real.sqrt H * d / W := by
    have hWL : (W : ℝ) ≤ Real.sqrt H * L := by
      rw [div_le_iff₀ hsH] at hl
      linarith
    have : d / L ≤ Real.sqrt H * d / W := by
      rw [div_le_div_iff₀ hL hWr]
      nlinarith
    linarith
  rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
  apply mul_le_mul (inv_anti₀ (mul_pos hL hh) hf)
    (inv_anti₀ (Real.rpow_pos_of_pos (by positivity) _)
      (Real.rpow_le_rpow (by positivity) hbase hD))
    (inv_nonneg.mpr (Real.rpow_nonneg (by positivity) _)) (by positivity)

/-!
## Exact proportionality at `ℓ = N` (d)
-/

/-- **Delocalized proportionality** (d): if
`ℓ(h) = ℓ(h') = N` then `Υ_{h'} = (h/h') Υ_h` entrywise (`h, h' > 0`). -/
theorem polynomialControl_deloc_prop {N W : ℕ} (D : ℝ) {h h' : ℝ} (hh : 0 < h) (hh' : 0 < h')
    (hl : ErdosRiabov.localizationLength N W h = N)
    (hl' : ErdosRiabov.localizationLength N W h' = N) (x y : Fin N) :
    polynomialControl N W D h' x y = h / h' * polynomialControl N W D h x y := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Fin.pos x
  unfold polynomialControl
  rw [hl, hl']
  field_simp

/-- `polynomialControl_deloc_prop` for heights `h, h' ≤ (W/N)²` (then `ℓ = N`). -/
theorem polynomialControl_deloc_prop_of_le {N W : ℕ} (D : ℝ) {h h' : ℝ} (hh : 0 < h)
    (hh' : 0 < h') (hsmall : h ≤ ((W : ℝ) / (N : ℝ)) ^ 2)
    (hsmall' : h' ≤ ((W : ℝ) / (N : ℝ)) ^ 2) (x y : Fin N) :
    polynomialControl N W D h' x y = h / h' * polynomialControl N W D h x y :=
  polynomialControl_deloc_prop D hh hh' (loc_eq_N (Fin.pos x) hh hsmall)
    (loc_eq_N (Fin.pos x) hh' hsmall') x y

end BlockBand.Native.ErdosRiabov.Kernel
