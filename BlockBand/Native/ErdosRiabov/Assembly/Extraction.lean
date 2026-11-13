module

public import BlockBand.Native.ErdosRiabov.Assembly.Zig
public import BlockBand.Adapters.ErdosRiabov.Clause23

/-!
# Extraction at the terminal time

Step (6) of the proof of the short-ring local law. Deterministic; no law.

At `t = 1`, `k = 1` and the pattern `σ = (+)` (`fun _ => false`): `α₁ = 0`, `z_1 = z`
(`vsTraj z 1 = z`), `η_1 = Im z`, `s^iso_{1,1}(a, x', b) = Υ_η(a,b)^{1/2}` and
`M^{(1)}_{[1,1]} = m(z)`. Hence (`isoRatio_one_one`) the isotropic ratio is exactly the
quantity `|G_ab(z) - m δ_ab| / Υ_η(a,b)^{1/2}`, `G = (H - z)⁻¹`,
`Υ_η = polynomialControl N W D η`.

* **`extraction`**: if `Υ_η(a,b) > 0` and `X Υ_η(a,b)^{1/2} < |G_ab(z) - m δ_ab|` then
  `X < Ψ^iso_{1,1}(H)`; `extraction_subset`: the same as an inclusion of events.
* `extraction_zig`: the form for `zigPsiData p D z` with `Im z > 0` (positivity of `Υ` is
  `Adapters.ErdosRiabov.polynomialControl_pos`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Assembly

open BlockBand.External.ErdosRiabov (semicircleM)
open BlockBand.Internal.Contracts.Inputs (polynomialControl)
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Psi

variable {N : ℕ}

/-- The pattern `σ = (+)` of length `1`. -/
def plusPattern : Fin 1 → Bool := fun _ => false

/-- `M^{(t)}_{[1,1]} = m(z)` for the pattern `(+)` (every time `t`, every site). -/
theorem mChain_plus (P : PsiData N) (x : Fin 1 → Fin N) (t : ℝ) (a : Fin N) :
    P.mChain plusPattern x t a = semicircleM P.z := by
  simp [PsiData.mChain, Split.chainM, Split.chainTilde_eq, patM, plusPattern, VS.patConj]

/-- The chain of length `1` with the isotropic slot is the resolvent at `z_1 = z`. -/
theorem gChain_plus_one (P : PsiData N) (x : Fin 1 → Fin N) (H : Matrix (Fin N) (Fin N) ℂ) :
    gChain (patZ P.z plusPattern 1) (isoSlots P.S x) H =
      (H - P.z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ := by
  simp [gChain, Chains.slotProd, Chains.slotList, isoSlots, patZ, plusPattern, VS.patConj,
    vsTraj]

/-- `s^iso_{1,1}(a, x', b) = Υ_η(a,b)^{1/2}`, `η = Im z`. -/
theorem sIso_one_one (P : PsiData N) (a b : Fin N) (x : Fin 1 → Fin N) :
    P.sIso a b x 1 = Real.sqrt (polynomialControl N P.W P.D P.z.im a b) := by
  simp [PsiData.sIso, PsiData.ups, isoPoint, vsHeight]

/-- **The terminal isotropic ratio is the local-law quantity**: for `σ = (+)`, `k = 1`, `t = 1`
and any `x'`, `isoRatio = |G_ab(z) - m δ_ab| / Υ_η(a,b)^{1/2}`. -/
theorem isoRatio_one_one (P : PsiData N) (a b : Fin N) (x : Fin 1 → Fin N)
    (H : Matrix (Fin N) (Fin N) ℂ) :
    P.isoRatio (plusPattern, a, b, x) 1 H =
      ‖(H - P.z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ a b -
          (if a = b then semicircleM P.z else 0)‖ /
        Real.sqrt (polynomialControl N P.W P.D P.z.im a b) := by
  have hα : Expo.lossAlpha 1 = 0 := by simp [Expo.lossAlpha]
  simp only [PsiData.isoRatio, PsiData.isoErr, gChain_plus_one, mChain_plus, sIso_one_one, hα,
    Real.rpow_zero, one_mul]

/-- **Extraction**: if `Υ_η(a,b) > 0` (`η = Im z`) and `X Υ_η(a,b)^{1/2} < |G_ab(z) - m δ_ab|`,
then `X < Ψ^iso_{1,1}(H)`. -/
theorem extraction (P : PsiData N) {a b : Fin N}
    (hpos : 0 < polynomialControl N P.W P.D P.z.im a b) {X : ℝ}
    {H : Matrix (Fin N) (Fin N) ℂ}
    (h : X * Real.sqrt (polynomialControl N P.W P.D P.z.im a b) <
      ‖(H - P.z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ a b -
        (if a = b then semicircleM P.z else 0)‖) :
    X < P.bigPsiIso 1 1 H := by
  have hs : 0 < Real.sqrt (polynomialControl N P.W P.D P.z.im a b) := Real.sqrt_pos.2 hpos
  have hr : X < P.isoRatio (plusPattern, a, b, fun _ => a) 1 H := by
    rw [isoRatio_one_one, lt_div_iff₀ hs]
    exact h
  exact hr.trans_le (P.isoRatio_le_bigPsiIso _ 1 H)

/-- **Extraction, event form**: `{|G_ab(z) - m δ_ab| > X Υ_η(a,b)^{1/2}} ⊆ {Ψ^iso_{1,1} > X}`
when `Υ_η(a,b) > 0`. -/
theorem extraction_subset (P : PsiData N) {a b : Fin N}
    (hpos : 0 < polynomialControl N P.W P.D P.z.im a b) (X : ℝ) :
    {H : Matrix (Fin N) (Fin N) ℂ | X * Real.sqrt (polynomialControl N P.W P.D P.z.im a b) <
        ‖(H - P.z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ a b -
          (if a = b then semicircleM P.z else 0)‖} ⊆
      {H | X < P.bigPsiIso 1 1 H} :=
  fun _ h => extraction P hpos h

/-- **Extraction for the zig data**: on the ring `p` with `Im z > 0`,
`X Υ_η(a,b)^{1/2} < |G_ab(z) - m δ_ab|` implies `X < Ψ^iso_{1,1}(H)` for `zigPsiData p D z`. -/
theorem extraction_zig (p : BlockBand.Parameters) (D : ℝ) {z : ℂ} (hz : 0 < z.im)
    {a b : Fin (p.n * p.W)} {X : ℝ} {H : Matrix (Fin (p.n * p.W)) (Fin (p.n * p.W)) ℂ}
    (h : X * Real.sqrt (polynomialControl (p.n * p.W) p.W D z.im a b) <
      ‖(H - z • (1 : Matrix (Fin (p.n * p.W)) (Fin (p.n * p.W)) ℂ))⁻¹ a b -
        (if a = b then semicircleM z else 0)‖) :
    X < (zigPsiData p D z).bigPsiIso 1 1 H :=
  extraction (zigPsiData p D z)
    (Adapters.ErdosRiabov.polynomialControl_pos p.N_pos p.W_pos D hz a b) h

end BlockBand.Native.ErdosRiabov.Assembly
