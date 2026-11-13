module

public import BlockBand.Native.ErdosRiabov.SatLin.Reduce
public import BlockBand.Native.ErdosRiabov.Circ.RemEvent

/-!
# The saturated linear term as a sum of one-slot actions, and the slot rotation

* `propOp_vsTensorGen_const`: for constant weights,
  `T̂^{⊕k}_s[f](x) = Σ_j T̂^{(j)}_s[f](x)` (`circSlot`).
* `trace_slotProd_rotate`: `Tr ∏_l M_{l+1} B_{l+1} = Tr ∏_l M_l B_l` (cyclicity).
* `avErr_rotate`, `avErr_rotate_pow`: `𝒳^σ_t(x) = 𝒳^{σ∘rot^r}_t(x∘rot^r)` for `k = n+2`
  (trace cyclicity and `Discharge.mbAvM_rotate_uncond`; unconditional).
* **`circSlot_avErr_rotTo`**: `T̂^{(j)}[𝒳^σ](x) = T̂^{(k)}[𝒳^{σ'}](mbRotTo j x)`,
  `σ' = σ ∘ rot^{j+1}` (the slot `j` moved to the last slot).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.SatLin

open Set Function
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Propagator
open BlockBand.Native.ErdosRiabov.Circ
open BlockBand.Native.ErdosRiabov.MBound (mbRotTo mbRotTo_last mbRotTo_update)
open scoped ComplexConjugate

variable {N : ℕ}

/-- **The generator with constant weights is the sum of the one-slot actions.** -/
theorem propOp_vsTensorGen_const {k : ℕ} (S : Matrix (Fin N) (Fin N) ℝ) (μ μ' : ℂ) (s : ℝ)
    (f : (Fin k → Fin N) → ℂ) (x : Fin k → Fin N) :
    propOp (vsTensorGen S (fun _ => μ) (fun _ => μ') s) f x =
      ∑ j, circSlot j (vsKernel S μ μ' s) f x := by
  rw [propOp_vsTensorGen_apply]
  rfl

/-- **Trace cyclicity of a slot product.** -/
theorem trace_slotProd_rotate {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (B M : Fin (n + 1) → Matrix ι ι ℂ) :
    Matrix.trace (Chains.slotProd (fun j => B (finRotate (n + 1) j))
        (fun j => M (finRotate (n + 1) j))) =
      Matrix.trace (Chains.slotProd B M) := by
  unfold Chains.slotProd Chains.slotList
  rw [List.ofFn_succ', List.ofFn_succ, List.concat_eq_append, List.prod_append, List.prod_cons,
    List.prod_cons, List.prod_nil, mul_one]
  simp only [finRotate_apply, Fin.coeSucc_eq_succ, Fin.last_add_one]
  rw [Matrix.trace_mul_comm]

variable (P : PsiData N)

/-- **One-step rotation of `𝒳`** (`k = n+2`, unconditional). -/
theorem avErr_rotate (hS : Split.ProfileHyp P.S) (hz : P.z.im ≠ 0) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) {n : ℕ} (σ : Fin (n + 2) → Bool) (x : Fin (n + 2) → Fin N)
    (H : Matrix (Fin N) (Fin N) ℂ) :
    P.avErr σ x t H =
      P.avErr (fun r => σ (finRotate (n + 2) r)) (fun r => x (finRotate (n + 2) r)) t H := by
  have hM := Discharge.mbAvM_rotate_uncond P hS hz ht σ x
  change Matrix.trace (gChain (patZ P.z σ t) (avSlots P.S x) H) - Evol.avM P σ x t =
    Matrix.trace (gChain (patZ P.z (fun r => σ (finRotate (n + 2) r)) t)
      (avSlots P.S (fun r => x (finRotate (n + 2) r))) H) -
        Evol.avM P (fun r => σ (finRotate (n + 2) r)) (fun r => x (finRotate (n + 2) r)) t
  rw [← hM]
  congr 1
  unfold gChain
  exact (trace_slotProd_rotate (n := n + 1) (avSlots P.S x)
    (fun j => (H - patZ P.z σ t j • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹)).symm

/-- **Rotation of `𝒳` by `rot^r`** (`k = n+2`, unconditional). -/
theorem avErr_rotate_pow (hS : Split.ProfileHyp P.S) (hz : P.z.im ≠ 0) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) {n : ℕ} (r : ℕ) (σ : Fin (n + 2) → Bool) (x : Fin (n + 2) → Fin N)
    (H : Matrix (Fin N) (Fin N) ℂ) :
    P.avErr σ x t H = P.avErr (fun i => σ ((finRotate (n + 2) ^ r) i))
      (fun i => x ((finRotate (n + 2) ^ r) i)) t H := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [ih, avErr_rotate P hS hz ht]
    simp only [pow_succ, Equiv.Perm.mul_apply]

/-- **The slot `j` moved to the last slot** (`k = n+2`, unconditional):
`T̂^{(j)}[𝒳^σ_t](x) = T̂^{(k)}[𝒳^{σ'}_t](mbRotTo j x)`, `σ' = σ ∘ rot^{j+1}`. -/
theorem circSlot_avErr_rotTo (hS : Split.ProfileHyp P.S) (hz : P.z.im ≠ 0) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) {n : ℕ} (K : Matrix (Fin N) (Fin N) ℂ) (σ : Fin (n + 2) → Bool)
    (j : Fin (n + 2)) (H : Matrix (Fin N) (Fin N) ℂ) (x : Fin (n + 2) → Fin N) :
    circSlot j K (fun y => P.avErr σ y t H) x =
      circSlot (Fin.last (n + 1)) K
        (fun y => P.avErr (fun i => σ ((finRotate (n + 2) ^ ((j : ℕ) + 1)) i)) y t H)
        (mbRotTo j x) := by
  rw [circSlot_apply, circSlot_apply, mbRotTo_last]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  rw [avErr_rotate_pow P hS hz ht ((j : ℕ) + 1), ← mbRotTo_update]
  rfl

end BlockBand.Native.ErdosRiabov.SatLin
