module

public import BlockBand.Native.ErdosRiabov.Prop.Bridge

/-!
# `propOp` forms of the propagator bounds for the `M`-bounds

Deterministic: no measure occurs.

* `mb_goodProps_av_any_apply`: the signed (`propOp`) form of `Propagator.goodProps_av_any` (the
  averaged bound at any non-saturated position): if `|g| ≤ φ s^av_{k,s}` then
  `|U g(x)| ≤ C_P^k φ (L_t/L_s) s^av_{k,t}(x)`;
* `mb_evol_goodProps_iso_apply`, `mb_evol_goodProps_av_apply`: the `propOp` forms of
  `Propagator.evol_goodProps_iso` / `evol_goodProps_av` (Evol's Duhamel propagators);
* `mb_vsTensorProp_muIso_one`: for `k = 1` the isotropic Duhamel propagator is the identity.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.MBound

open BlockBand.Native.ErdosRiabov.Kernel BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Psi BlockBand.Native.ErdosRiabov.Evol
open BlockBand.Native.ErdosRiabov.Propagator
open BlockBand.Internal.Contracts.Inputs (shortRingProfile)

section Psi

variable (d : VSData) {m W : ℕ} (hm : 4 ≤ m) (hW : 0 < W) (P : PsiData (m * W))
  (hPW : P.W = W) (hPD : P.D = d.D) (hz : BulkDomain (m * W) d.delta0 d.kappa d.C0 P.z)
  {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t ≤ 1)
include hm hW hPW hPD hz hs0 hst ht1

/-- **Averaged propagator bound, any position, `propOp` form**: for chain length `k = n+2`,
factors `c` with a non-saturated factor `c j`, and `|g(y)| ≤ φ s^av_{k,s}(y)`:
`|U g(x)| ≤ C_P^k φ (L_t/L_s) s^av_{k,t}(x)`, `U = goodProp S P.z c s t`. -/
theorem mb_goodProps_av_any_apply {n : ℕ} (c : Fin (n + 2) → PropFactor) (j : Fin (n + 2))
    (hj : c j ≠ .sat) {φ : ℝ} (hφ : 0 ≤ φ) (g : (Fin (n + 2) → Fin (m * W)) → ℂ)
    (hg : ∀ y, ‖g y‖ ≤ φ * P.sAv y s) (x : Fin (n + 2) → Fin (m * W)) :
    ‖propOp (goodProp (shortRingProfile d.b m W) P.z c s t) g x‖ ≤
      kernelActionConst d ^ (n + 2) * φ * (P.lEta t / P.lEta s) * P.sAv x t := by
  rw [propOp_apply]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ y, ‖goodProp (shortRingProfile d.b m W) P.z c s t x y * g y‖
      ≤ ∑ y, ‖goodProp (shortRingProfile d.b m W) P.z c s t x y‖ * (φ * P.sAv y s) :=
        Finset.sum_le_sum fun y _ => by
          rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hg y) (norm_nonneg _)
    _ = φ * ∑ y, ‖goodProp (shortRingProfile d.b m W) P.z c s t x y‖ * P.sAv y s := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring
    _ ≤ φ * (kernelActionConst d ^ (n + 2) * (P.lEta t / P.lEta s) * P.sAv x t) :=
        mul_le_mul_of_nonneg_left (goodProps_av_any d hm hW P hPW hPD hz hs0 hst ht1 c j hj x)
          hφ
    _ = _ := by ring

end Psi

section Evol

variable {p : BlockBand.Parameters} (d : VSData) (P : PsiData (p.n * p.W)) (hb : d.b = p.b)
  (hPS : P.S = shortRingProfile p.b p.n p.W) (hPW : P.W = p.W) (hPD : P.D = d.D)
  (hz : BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 P.z) {s t : ℝ} (hs0 : 0 ≤ s)
  (hst : s ≤ t) (ht1 : t ≤ 1)
include hb hPS hPW hPD hz hs0 hst ht1

/-- **Isotropic propagator bound for Evol's propagator, `propOp` form** (chain length `k = n+2`): if
`|f(y)| ≤ φ s^iso_{k,s}(a,y,b)` then `|U f(x)| ≤ C_P^{k-1} φ √(L_t/L_s) s^iso_{k,t}(a,x,b)`,
`U = vsTensorProp P.S (muIso P σ) (muNext P σ) s t`. -/
theorem mb_evol_goodProps_iso_apply {n : ℕ} (σ : Fin (n + 2) → Bool) (a b : Fin (p.n * p.W))
    {φ : ℝ} (hφ : 0 ≤ φ) (f : (Fin (n + 2) → Fin (p.n * p.W)) → ℂ)
    (hf : ∀ y, ‖f y‖ ≤ φ * P.sIso a b y s) (x : Fin (n + 2) → Fin (p.n * p.W)) :
    ‖propOp (vsTensorProp P.S (muIso P σ) (muNext P σ) s t) f x‖ ≤
      kernelActionConst d ^ (n + 1) * φ * Real.sqrt (P.lEta t / P.lEta s) * P.sIso a b x t := by
  rw [vsTensorProp_muIso_eq_goodProp, evol_PS_eq d P hb hPS]
  exact goodProps_iso_apply d p.n_ge_four p.W_pos P hPW hPD hz hs0 hst ht1 _
    (propFactorIso_last σ) a b hφ f hf x

/-- **Averaged propagator bound for Evol's propagator, `propOp` form** (chain length `k = n+2`, a pattern with a
non-saturated factor): if `|g(y)| ≤ φ s^av_{k,s}(y)` then
`|U g(x)| ≤ C_P^k φ (L_t/L_s) s^av_{k,t}(x)`, `U = vsTensorProp P.S (muAv P σ) (muNext P σ) s t`. -/
theorem mb_evol_goodProps_av_apply {n : ℕ} (σ : Fin (n + 2) → Bool) (hσ : HasDesatFactor σ)
    {φ : ℝ} (hφ : 0 ≤ φ) (g : (Fin (n + 2) → Fin (p.n * p.W)) → ℂ)
    (hg : ∀ y, ‖g y‖ ≤ φ * P.sAv y s) (x : Fin (n + 2) → Fin (p.n * p.W)) :
    ‖propOp (vsTensorProp P.S (muAv P σ) (muNext P σ) s t) g x‖ ≤
      kernelActionConst d ^ (n + 2) * φ * (P.lEta t / P.lEta s) * P.sAv x t := by
  obtain ⟨j, hj⟩ := hσ
  rw [vsTensorProp_muAv_eq_goodProp, evol_PS_eq d P hb hPS]
  exact mb_goodProps_av_any_apply d p.n_ge_four p.W_pos P hPW hPD hz hs0 hst ht1 _ j
    ((propFactorOf_ne_sat_iff σ j).mpr hj) hφ g hg x

end Evol

/-- **Iso, `k = 1`**: the isotropic Duhamel propagator of a one-letter
pattern is the identity, `vsTensorProp S (muIso P σ) (muNext P σ) s t = 1` (its only weight is
`0`). -/
theorem mb_vsTensorProp_muIso_one {p : BlockBand.Parameters} (P : PsiData (p.n * p.W))
    (σ : Fin 1 → Bool) (s t : ℝ) : vsTensorProp P.S (muIso P σ) (muNext P σ) s t = 1 := by
  have h : ∀ j : Fin 1, muIso P σ j = 0 := fun j => by
    unfold muIso
    rw [ite_eq_right (by have := j.isLt; omega)]
  unfold vsTensorProp
  simp only [h, vsPropagator_zero_left]
  exact tensorMat_one

end BlockBand.Native.ErdosRiabov.MBound
