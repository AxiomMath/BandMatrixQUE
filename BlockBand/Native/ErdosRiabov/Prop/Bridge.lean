module

public import BlockBand.Native.ErdosRiabov.Prop.RegProps
public import BlockBand.Native.ErdosRiabov.Evol.Duhamel

/-!
# Bridge: Evol's Duhamel propagators are `goodProp`

Interface between the Duhamel forms of the Evol flow and the propagator estimates.
Deterministic: no measure occurs.

* `patNext σ j`: the cyclically next pattern bit (`σ_{j+1}`, `σ_k := σ_0`), and
  `propFactorOf σ j`: `sat` if `σ_j ≠ σ_{j+1}`, `desat` if both are `false`, `desatConj` if both
  are `true`; `propFactorIso σ j`: the same, but `ident` in the last slot.
* `vsTensorProp_muAv_eq_goodProp`, `vsTensorProp_muIso_eq_goodProp`: Evol's propagators
  `vsTensorProp S (muAv P σ) (muNext P σ)` and `vsTensorProp S (muIso P σ) (muNext P σ)` equal
  `goodProp S P.z (propFactorOf σ)` and `goodProp S P.z (propFactorIso σ)` (any `S`).
* `HasDesatFactor σ` (`∃ j, σ_j = σ_{j+1}`) and `propFactorOf_ne_sat_iff`.
* Ring parameters: Evol uses `p : BlockBand.Parameters` (`N = p.n p.W`, `P.S =
  shortRingProfile p.b p.n p.W`); the propagator bounds use VS data `d` with `m = p.n`, `W = p.W`
  and `d.b = p.b` (`hb`); `m ≥ 4`, `W ≥ 1` come from `p.n_ge_four`, `p.W_pos`.
* Corollaries for the Evol propagators: `evol_goodProps_iso`, `evol_goodProps_av`,
  `evol_goodProps_av_one`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Propagator

open BlockBand.External.ErdosRiabov (semicircleM)
open BlockBand.Native.ErdosRiabov.Kernel BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Psi BlockBand.Native.ErdosRiabov.Evol
open BlockBand.Internal.Contracts.Inputs (shortRingProfile)
open scoped ComplexConjugate

variable {k : ℕ}

/-- The cyclically next pattern bit `σ_{j+1}` (`σ_k := σ_0`). -/
def patNext (σ : Fin k → Bool) (j : Fin k) : Bool :=
  if h : j.val + 1 < k then σ ⟨j.val + 1, h⟩ else σ ⟨0, by omega⟩

/-- The factor of a pair of pattern bits. -/
def propFactorOfBits : Bool → Bool → PropFactor
  | false, false => .desat
  | true, true => .desatConj
  | _, _ => .sat

/-- The factor of slot `j` of the averaged Duhamel propagator of pattern `σ`. -/
def propFactorOf (σ : Fin k → Bool) (j : Fin k) : PropFactor := propFactorOfBits (σ j) (patNext σ j)

/-- The factor of slot `j` of the isotropic Duhamel propagator (`ident` in the last slot). -/
def propFactorIso (σ : Fin k → Bool) (j : Fin k) : PropFactor :=
  if j.val + 1 < k then propFactorOf σ j else .ident

/-- The pattern has a non-saturated (`Q̂`/`conj Q̂`) factor: `σ_j = σ_{j+1}` for some `j`. -/
def HasDesatFactor (σ : Fin k → Bool) : Prop := ∃ j, σ j = patNext σ j

theorem propFactorOfBits_ne_sat_iff (a b : Bool) : propFactorOfBits a b ≠ .sat ↔ a = b := by
  cases a <;> cases b <;> simp [propFactorOfBits]

theorem propFactorOf_ne_sat_iff (σ : Fin k → Bool) (j : Fin k) :
    propFactorOf σ j ≠ .sat ↔ σ j = patNext σ j :=
  propFactorOfBits_ne_sat_iff _ _

/-- `vsPropagator S 0 μ' = I`. -/
theorem vsPropagator_zero_left {N : ℕ} (S : Matrix (Fin N) (Fin N) ℝ) (μ' : ℂ) (s t : ℝ) :
    vsPropagator S 0 μ' s t = 1 := by
  unfold vsPropagator vsY
  simp

private theorem vsPropagator_bits {N : ℕ} (S : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (a b : Bool)
    (s t : ℝ) :
    vsPropagator S (VS.patConj a (semicircleM z)) (VS.patConj b (semicircleM z)) s t =
      goodPropFactor S z (propFactorOfBits a b) s t := by
  cases a <;> cases b <;>
    simp [VS.patConj, propFactorOfBits, goodPropFactor, PropFactor.mu1, PropFactor.mu2,
      vsPropagator_swap]

variable {p : BlockBand.Parameters}

theorem muAv_apply (P : PsiData (p.n * p.W)) (σ : Fin k → Bool) (j : Fin k) :
    muAv P σ j = VS.patConj (σ j) (semicircleM P.z) := by
  unfold muAv patM
  rw [dite_eq_left ⟨by omega, by omega⟩]
  simp only [Nat.add_sub_cancel, Fin.eta]

theorem muNext_apply (P : PsiData (p.n * p.W)) (σ : Fin k → Bool) (j : Fin k) :
    muNext P σ j = VS.patConj (patNext σ j) (semicircleM P.z) := by
  unfold muNext nextIdx patM patNext
  by_cases h : j.val + 1 < k
  · rw [ite_eq_left h, dite_eq_left ⟨by omega, by omega⟩, dite_eq_left h]
    simp only [show j.val + 2 - 1 = j.val + 1 by omega]
  · rw [ite_eq_right h, dite_eq_left ⟨le_rfl, by omega⟩, dite_eq_right h]

private theorem vsTensorProp_eq_goodProp_of {N : ℕ} (S : Matrix (Fin N) (Fin N) ℝ) (z : ℂ)
    (μ μ' : Fin k → ℂ) (c : Fin k → PropFactor) (s t : ℝ)
    (h : ∀ j, vsPropagator S (μ j) (μ' j) s t = goodPropFactor S z (c j) s t) :
    vsTensorProp S μ μ' s t = goodProp S z c s t := by
  unfold vsTensorProp goodProp
  congr 1
  funext j
  exact h j

/-- **Bridge (av)**: Evol's averaged Duhamel propagator is `goodProp` of `propFactorOf σ`. -/
theorem vsTensorProp_muAv_eq_goodProp (P : PsiData (p.n * p.W))
    (S : Matrix (Fin (p.n * p.W)) (Fin (p.n * p.W)) ℝ) (σ : Fin k → Bool) (s t : ℝ) :
    vsTensorProp S (muAv P σ) (muNext P σ) s t = goodProp S P.z (propFactorOf σ) s t :=
  vsTensorProp_eq_goodProp_of S P.z _ _ _ s t fun j => by
    rw [muAv_apply, muNext_apply, vsPropagator_bits]
    rfl

/-- **Bridge (iso)**: Evol's isotropic Duhamel propagator is `goodProp` of `propFactorIso σ`. -/
theorem vsTensorProp_muIso_eq_goodProp (P : PsiData (p.n * p.W))
    (S : Matrix (Fin (p.n * p.W)) (Fin (p.n * p.W)) ℝ) (σ : Fin k → Bool) (s t : ℝ) :
    vsTensorProp S (muIso P σ) (muNext P σ) s t = goodProp S P.z (propFactorIso σ) s t :=
  vsTensorProp_eq_goodProp_of S P.z _ _ _ s t fun j => by
    unfold propFactorIso
    by_cases h : j.val + 1 < k
    · have hm : muIso P σ j = muAv P σ j := by unfold muIso muAv; rw [ite_eq_left h]
      rw [hm, muAv_apply, muNext_apply, vsPropagator_bits, ite_eq_left h]
      rfl
    · have hm : muIso P σ j = 0 := by unfold muIso; rw [ite_eq_right h]
      rw [hm, vsPropagator_zero_left, ite_eq_right h]
      simp [goodPropFactor, PropFactor.mu1, PropFactor.mu2, vsPropagator_zero]

theorem propFactorIso_last {n : ℕ} (σ : Fin (n + 2) → Bool) :
    propFactorIso σ (Fin.last (n + 1)) = .ident := by
  unfold propFactorIso
  rw [ite_eq_right (by simp)]

/-! ## Corollaries for the Evol propagators -/

section Evol

variable (d : VSData) (P : PsiData (p.n * p.W)) (hb : d.b = p.b)
  (hPS : P.S = shortRingProfile p.b p.n p.W) (hPW : P.W = p.W) (hPD : P.D = d.D)
  (hz : BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 P.z) {s t : ℝ} (hs0 : 0 ≤ s)
  (hst : s ≤ t) (ht1 : t ≤ 1)
include hb hPS hPW hPD hz hs0 hst ht1

omit hPW hPD hz hs0 hst ht1 in
theorem evol_PS_eq : P.S = shortRingProfile d.b p.n p.W := by rw [hPS, hb]

/-- **Isotropic propagator bound for Evol's propagator** (chain length `k = n+2`, `ψ` pattern `σ`):
`Σ_y |U(x,y)| s^iso_{k,s}(a,y,b) ≤ C_P^{k-1} √(L_t/L_s) s^iso_{k,t}(a,x,b)`,
`U = vsTensorProp P.S (muIso P σ) (muNext P σ) s t`. -/
theorem evol_goodProps_iso {n : ℕ} (σ : Fin (n + 2) → Bool) (a b : Fin (p.n * p.W))
    (x : Fin (n + 2) → Fin (p.n * p.W)) :
    ∑ y, ‖vsTensorProp P.S (muIso P σ) (muNext P σ) s t x y‖ * P.sIso a b y s ≤
      kernelActionConst d ^ (n + 1) * Real.sqrt (P.lEta t / P.lEta s) * P.sIso a b x t := by
  rw [vsTensorProp_muIso_eq_goodProp, evol_PS_eq d P hb hPS]
  exact goodProps_iso d p.n_ge_four p.W_pos P hPW hPD hz hs0 hst ht1 _ (propFactorIso_last σ) a b x

/-- **Averaged propagator bound for Evol's propagator** (chain length `k = n+2`): if the pattern has a
non-saturated factor (`HasDesatFactor σ`),
`Σ_y |U(x,y)| s^av_{k,s}(y) ≤ C_P^k (L_t/L_s) s^av_{k,t}(x)`,
`U = vsTensorProp P.S (muAv P σ) (muNext P σ) s t`. -/
theorem evol_goodProps_av {n : ℕ} (σ : Fin (n + 2) → Bool) (hσ : HasDesatFactor σ)
    (x : Fin (n + 2) → Fin (p.n * p.W)) :
    ∑ y, ‖vsTensorProp P.S (muAv P σ) (muNext P σ) s t x y‖ * P.sAv y s ≤
      kernelActionConst d ^ (n + 2) * (P.lEta t / P.lEta s) * P.sAv x t := by
  obtain ⟨j, hj⟩ := hσ
  rw [vsTensorProp_muAv_eq_goodProp, evol_PS_eq d P hb hPS]
  exact goodProps_av_any d p.n_ge_four p.W_pos P hPW hPD hz hs0 hst ht1 _ j
    ((propFactorOf_ne_sat_iff σ j).mpr hj) x

omit hPD in

/-- **Averaged propagator bound, `k = 1`, for Evol's propagator** (every one-letter pattern is non-saturated):
`Σ_y |U(x,y)| s^av_{1,s}(y) ≤ (1 + C_K C₁''/c_m) (L_t/L_s) s^av_{1,t}(x)`. -/
theorem evol_goodProps_av_one (σ : Fin 1 → Bool) (x : Fin 1 → Fin (p.n * p.W)) :
    ∑ y, ‖vsTensorProp P.S (muAv P σ) (muNext P σ) s t x y‖ * P.sAv y s ≤
      (1 + vsCK d * d.C1pp / d.cm) * (P.lEta t / P.lEta s) * P.sAv x t := by
  rw [vsTensorProp_muAv_eq_goodProp, evol_PS_eq d P hb hPS]
  refine goodProps_av_one d p.n_ge_four p.W_pos P hPW hz hs0 hst ht1 _ ?_ x
  rw [propFactorOf_ne_sat_iff]
  simp [patNext]

end Evol

end BlockBand.Native.ErdosRiabov.Propagator
