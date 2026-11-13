module

public import BlockBand.Native.CEH.ETH.ZigClosureBounds

/-!
# CEH ETH: the path-core hypotheses on the good event, and the one-path bound

On the event where both single-resolvent tubes and all martingale controls hold, the processes of
`zcl_Data.proc` satisfy every pathwise hypothesis of the path core, so the endpoint bound on `Z_s`
holds on that event.

* `zcl_Data.TubeGood d ζ ω`: the tubes (`zgl_TubeGood`, exponent `ζ`) at `(z₁, m₁)` and
  `(z₂, m₂)` hold for all `σ ≤ s` (good event of `zgl_flowTube_two`);
* `zcl_Data.TailGood d p ω`: all the martingale controls of `ztl_goodEvent_levels` hold, with the
  levels `zpc_aX/aY/aZ` and budgets `zpc_bX/bY/bZ` of the path core, for `ℓ ≤ p.Lg`;
* `zcl_Data.hyp`: on `TubeGood ∩ TailGood`, with `p.Tz = N^ζ`, `p.Cm ≥ 0` and the Lemma 5.6
  bound `‖⟨M^A_σ⟩‖ ≤ p.Cm √chainP` (`hMA`), **every field of `zpc_Hyp d.geom p (d.proc ω)`**;
  the tube fields `W₁_le`, `W₂_le`, `imR₁_le`, `imR₂_le` (first and third conjuncts of the tube),
  `TI_le₁`, `TI_le₂` (`zgl_norm_imaginaryPart_mul_flow_le`), the martingale fields
  from `TailGood`, the others from `ZigClosureRegular`, `ZigClosureConst`, `ZigClosureBounds`;
* `zcl_Data.endpoint_le`: with `p = zpc_parRpow N ξ ζ Lmax Cm Lg` and the window-form numeric
  hypotheses of `zpc_closure_rpow`, `Z_s ≤ N^{ξ/2} ρ₁ρ₂ s₂(s)²` (`Z_s ≥ 0`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.ETH

open MeasureTheory Matrix Set
open CEHNative.BlockBand CEHNative.BlockBand.External.CEH
open BlockBand.Native.CEH.Flow BlockBand.Native.CEH.Zig BlockBand.Native.CEH.LocalLaw
open BlockBand.External.CEH (normalizedTrace)
open scoped NNReal ENNReal ComplexConjugate

variable {Ω : Type} {N : ℕ}

namespace zcl_Data

/-- The two tubes along the whole flow. -/
def TubeGood (d : zcl_Data Ω N) (ζ : ℝ) (ω : Ω) : Prop :=
  ∀ σ : ℝ≥0, σ ≤ d.s → zgl_TubeGood N ζ d.F d.G d.z₁ d.m₁ d.s σ ω ∧
    zgl_TubeGood N ζ d.F d.G d.z₂ d.m₂ d.s σ ω

/-- All the martingale controls of `ztl_goodEvent_levels` with the levels of the path core. -/
def TailGood (d : zcl_Data Ω N) (p : zpc_Par) (ω : Ω) : Prop :=
  (∀ c₁ c₂ q : Bool, ∀ ℓ ≤ p.Lg, ∀ t ∈ Set.Icc 0 (d.s : ℝ),
      (∫ r in Set.Ioc 0 t, ztl_brkX d.F d.G (ztl_cz c₁ d.z₁) (ztl_cz c₁ d.m₁) (ztl_cz c₂ d.z₂)
        (ztl_cz c₂ d.m₂) d.s (ztl_evK q (ztl_avgK N)) d.A ω r) ≤ zpc_bX d.geom p ℓ →
      |ztl_mX d.F d.G (ztl_cz c₁ d.z₁) (ztl_cz c₁ d.m₁) (ztl_cz c₂ d.z₂) (ztl_cz c₂ d.m₂) d.s
        (ztl_evK q (ztl_avgK N)) d.A ω t| < zpc_aX d.geom p ℓ) ∧
    (∀ c₁ c₂ q : Bool, ∀ ℓ ≤ p.Lg, ∀ t ∈ Set.Icc 0 (d.s : ℝ),
      (∫ r in Set.Ioc 0 t, ztl_brkX d.F d.G (ztl_cz c₁ d.z₁) (ztl_cz c₁ d.m₁) (ztl_cz c₂ d.z₂)
        (ztl_cz c₂ d.m₂) d.s (ztl_evK q (ztl_avgK N)) 1 ω r) ≤ zpc_bY d.geom ℓ →
      |ztl_mX d.F d.G (ztl_cz c₁ d.z₁) (ztl_cz c₁ d.m₁) (ztl_cz c₂ d.z₂) (ztl_cz c₂ d.m₂) d.s
        (ztl_evK q (ztl_avgK N)) 1 ω t| < zpc_aY d.geom p ℓ) ∧
    (∀ ℓ ≤ p.Lg, ∀ t ∈ Set.Icc 0 (d.s : ℝ),
      (∫ r in Set.Ioc 0 t, ztl_brkZ d.F d.G d.z₁ d.m₁ d.z₂ d.m₂ d.s d.A ω r) ≤ zpc_bZ d.geom p →
      |ztl_mZ d.F d.G d.z₁ d.m₁ d.z₂ d.m₂ d.s d.A ω t| < zpc_aZ d.geom p)

variable {d : zcl_Data Ω N} (hd : d.Valid) {ω : Ω}
include hd

/-!
## The tube fields
-/

section Tube

variable {ζ : ℝ} (hT : d.TubeGood ζ ω)
include hT

theorem W₁_le {p : zpc_Par} (hTz : p.Tz = (N : ℝ) ^ ζ) :
    ∀ r ∈ Icc 0 d.geom.s, ‖(d.proc ω).W₁ r‖ ≤ p.Tz / (d.geom.N * d.geom.e₁ r) := by
  intro r hr
  have h := ((hT r.toNNReal (toNNReal_le_of_mem hr)).1).1
  rw [Real.coe_toNNReal _ hr.1, abs_of_pos hd.z₁_pos, abs_of_pos hd.m₁_pos] at h
  rw [hTz]
  exact h

theorem W₂_le {p : zpc_Par} (hTz : p.Tz = (N : ℝ) ^ ζ) :
    ∀ r ∈ Icc 0 d.geom.s, ‖(d.proc ω).W₂ r‖ ≤ p.Tz / (d.geom.N * d.geom.e₂ r) := by
  intro r hr
  have h := ((hT r.toNNReal (toNNReal_le_of_mem hr)).2).1
  rw [Real.coe_toNNReal _ hr.1, abs_of_pos hd.z₂_pos, abs_of_pos hd.m₂_pos] at h
  rw [hTz]
  exact h

theorem imR₁_le : ∀ r ∈ Icc 0 d.geom.s, (d.proc ω).imR₁ r ≤ 3 / 2 * d.geom.c₁ := by
  intro r hr
  have h := ((hT r.toNNReal (toNNReal_le_of_mem hr)).1).2.2
  rw [abs_of_pos hd.m₁_pos] at h
  exact h

theorem imR₂_le : ∀ r ∈ Icc 0 d.geom.s, (d.proc ω).imR₂ r ≤ 3 / 2 * d.geom.c₂ := by
  intro r hr
  have h := ((hT r.toNNReal (toNNReal_le_of_mem hr)).2).2.2
  rw [abs_of_pos hd.m₂_pos] at h
  exact h

theorem TI_min : ∀ r ∈ Icc 0 d.geom.s, (d.proc ω).TI r ≤
    3 / 2 * min (d.geom.c₁ / d.geom.e₂ r) (d.geom.c₂ / d.geom.e₁ r) := by
  intro r hr
  have hσ := toNNReal_le_of_mem hr
  have h := zgl_norm_imaginaryPart_mul_flow_le (hd.herm r.toNNReal ω) hd.z₁_pos.ne' hd.hm₁
    hd.z₂_pos.ne' hd.hm₂ hσ ((hT _ hσ).1.2.2) ((hT _ hσ).2.2.2)
  rw [Real.coe_toNNReal _ hr.1, abs_of_pos hd.z₁_pos, abs_of_pos hd.m₁_pos,
    abs_of_pos hd.z₂_pos, abs_of_pos hd.m₂_pos] at h
  exact h

theorem TI_le₁ : ∀ r ∈ Icc 0 d.geom.s, (d.proc ω).TI r ≤ 3 / 2 * (d.geom.c₁ / d.geom.e₂ r) :=
  fun r hr => (TI_min hd hT r hr).trans
    (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num))

theorem TI_le₂ : ∀ r ∈ Icc 0 d.geom.s, (d.proc ω).TI r ≤ 3 / 2 * (d.geom.c₂ / d.geom.e₁ r) :=
  fun r hr => (TI_min hd hT r hr).trans
    (mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num))

end Tube

/-!
## All the hypotheses of the path core
-/

/-- **Every field of `zpc_Hyp`** on the good event `TubeGood ∩ TailGood`. -/
theorem hyp {ζ : ℝ} {p : zpc_Par} (hTz : p.Tz = (N : ℝ) ^ ζ) (hCm : 0 ≤ p.Cm)
    (hMA : ∀ k : Bool × Bool, ∀ r ∈ Icc 0 (d.s : ℝ), ‖d.μA k r‖ ≤
      p.Cm * Real.sqrt (NTrace (matrixImaginaryPart d.M₁ * d.A * matrixImaginaryPart d.M₂ *
        d.Aᴴ)).re)
    (hT : d.TubeGood ζ ω) (hM : d.TailGood p ω) : zpc_Hyp d.geom p (d.proc ω) where
  contX := contX hd ω
  contY := contY hd ω
  contZ := contZ hd ω
  contCfX := contCfX hd ω
  contCfY := contCfY hd ω
  intDX := intDX hd ω
  intDY := intDY hd ω
  intDZ := intDZ hd ω
  X0 := X0 hd ω
  Y0 := Y0 hd ω
  Z0 := hd.Z0 ω
  decX := decX hd ω
  decY := decY hd ω
  decZ := decZ ω
  cfX_le := cfX_le hd ω
  cfY_le := cfY_le hd ω
  driftX := driftX hd ω
  driftY := driftY hd ω
  driftZ := driftZ hd ω
  MA_le := MA_le hd ω hCm hMA
  cross_le := cross_le hd ω
  QX₁_le := QX₁_le hd ω
  QX₂_le := QX₂_le hd ω
  QY₁_le := QY₁_le hd ω
  QY₂_le := QY₂_le hd ω
  V₁_le := V₁_le hd ω
  V₂_le := V₂_le hd ω
  W₁_le := W₁_le hd hT hTz
  W₂_le := W₂_le hd hT hTz
  imR₁_le := imR₁_le hd hT
  imR₂_le := imR₂_le hd hT
  TI_le₁ := TI_le₁ hd hT
  TI_le₂ := TI_le₂ hd hT
  brkXre_nonneg := brkXre_nonneg ω
  brkXre_le := brkXre_le hd ω
  brkXim_nonneg := brkXim_nonneg ω
  brkXim_le := brkXim_le hd ω
  brkYre_nonneg := brkYre_nonneg ω
  brkYre_le := brkYre_le hd ω
  brkYim_nonneg := brkYim_nonneg ω
  brkYim_le := brkYim_le hd ω
  brkZ_nonneg := brkZ_nonneg ω
  brkZ_le := brkZ_le hd ω
  martXre k ℓ hℓ t ht hb := hM.1 k.1 k.2 true ℓ hℓ t ht hb
  martXim k ℓ hℓ t ht hb := hM.1 k.1 k.2 false ℓ hℓ t ht hb
  martYre k ℓ hℓ t ht hb := hM.2.1 k.1 k.2 true ℓ hℓ t ht hb
  martYim k ℓ hℓ t ht hb := hM.2.1 k.1 k.2 false ℓ hℓ t ht hb
  martZ t ht hb := hM.2.2 0 (Nat.zero_le _) t ht hb

/-- **The one-path bound at the endpoint** (`zpc_closure_rpow`): with
`p = zpc_parRpow N ξ ζ Lmax Cm Lg`, on `TubeGood ∩ TailGood` and under the numeric hypotheses
in window form, `Z_s ≤ N^{ξ/2} ρ₁ρ₂ s₂(s)²`. -/
theorem endpoint_le {ξ ζ ne Lmax Cm : ℝ} {Lg : ℕ} (hne : 0 < ne)
    (h₁ : ne ≤ d.geom.N * d.geom.ρ₁ * d.geom.η₁) (h₂ : ne ≤ d.geom.N * d.geom.ρ₂ * d.geom.η₂)
    (hCm : 0 ≤ Cm) (hgrid : d.geom.P 0 ≤ 2 ^ Lg * d.geom.P d.geom.s)
    (hlog : Real.log (d.geom.P 0 / d.geom.P d.geom.s) ≤ Lmax)
    (hY : (1 + Lmax) * (4 * Real.sqrt 3 * d.geom.N ^ (ξ / 4) +
      (d.geom.N ^ (2 * ξ)) ^ 2 / (3 * (Real.pi * ne)) + 3 * d.geom.N ^ ζ) <
        d.geom.N ^ (2 * ξ))
    (hX : (1 + Lmax / 2) * (2 * d.geom.N ^ (ξ / 4) *
      Real.sqrt (4 * d.geom.N ^ ξ / (Real.pi * ne)) +
      Cm * d.geom.N ^ (2 * ξ) / Real.sqrt (d.geom.N * (d.geom.ρ₁ * d.geom.ρ₂)) +
      d.geom.N ^ (2 * ξ) * d.geom.N ^ (2 * ξ) / (2 * (Real.pi * ne)) +
      2 * d.geom.N ^ ζ * Real.sqrt (3 / 2 * d.geom.N ^ ξ) / Real.sqrt (Real.pi * ne)) <
        d.geom.N ^ (2 * ξ))
    (hZ : Real.pi ^ 2 + d.geom.N ^ (ξ / 4) * d.geom.N ^ ξ * Real.sqrt (4 / (Real.pi * ne)) +
      6 * d.geom.N ^ ζ * d.geom.N ^ ξ / (Real.pi * ne) +
      8 * d.geom.s * Cm ^ 2 * Real.pi ^ 2 +
      8 * (d.geom.N ^ (2 * ξ)) ^ 2 / (Real.pi * ne) ≤ d.geom.N ^ (ξ / 2))
    (hβ : d.geom.N ^ (ξ / 2) < d.geom.N ^ ξ)
    (hMA : ∀ k : Bool × Bool, ∀ r ∈ Icc 0 (d.s : ℝ), ‖d.μA k r‖ ≤
      Cm * Real.sqrt (NTrace (matrixImaginaryPart d.M₁ * d.A * matrixImaginaryPart d.M₂ *
        d.Aᴴ)).re)
    (hT : d.TubeGood ζ ω) (hM : d.TailGood (zpc_parRpow d.geom.N ξ ζ Lmax Cm Lg) ω) :
    d.Zp ω d.s ≤ (N : ℝ) ^ (ξ / 2) *
      (cehDensityOf d.M₁ * cehDensityOf d.M₂ * sTwoAt d.s d.M₁ d.M₂ d.A ^ 2) := by
  have h := (zpc_closure_rpow (D := d.proc ω) hd.geom_valid hne h₁ h₂ hCm hgrid hlog hY hX hZ hβ
    (hyp hd rfl hCm hMA hT hM)).2
  exact (le_abs_self _).trans h

end zcl_Data

end BlockBand.Native.CEH.ETH
