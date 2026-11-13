module

public import BlockBand.Native.ErdosRiabov.Circ.BoundBase

/-!
# The long linear term: `T̂^{(k-2)} T̂^{(k)} = Θ̊^{(k-2)} Θ̊^{(k)} + 𝓡₁ + 𝓡₂ - 𝓡₃`

The two-slot kernel action on long chains splits into the doubly regularized action and three
remainders.

Chains of length `k = n+4`, 0-based sites; `T̂ = T̂_s = vsKernel S m m̄ s`; ER's `x_{k-3}, x_{k-2},
x_{k-1}, x_k` are the coordinates `⟨n⟩, ⟨n+1⟩, ⟨n+2⟩, Fin.last (n+3)`. With `𝒯_j` the partial trace
over coordinate `j`:
* `circRemOne`   `𝓡₁(x) = T̂(x_{k-1}, x_k) 𝒯_k[T̂^{(k-2)} f](x)`,
* `circRemTwo`   `𝓡₂(x) = T̂(x_{k-2}, x_{k-3}) 𝒯_{k-2}[T̂^{(k)} f](x)`,
* `circRemThree` `𝓡₃(x) = T̂(x_{k-1}, x_k) T̂(x_{k-2}, x_{k-3}) 𝒯_{k-2,k}[f](x)`.
* **`circ_twoSlot_decomp`**: for stochastic symmetric `S`, `Im z ≠ 0`, `s ∈ [0,1]`:
  `T̂^{(k-2)}_s T̂^{(k)}_s f = Θ̊^{(k-2)}_s Θ̊^{(k)}_s f + 𝓡₁ + 𝓡₂ - 𝓡₃` (`Θ̊ = ringOp`, anchors
  `x_{k-3}`, `x_{k-1}`). The symmetry `T̂(x_k, x_{k-1}) = T̂(x_{k-1}, x_k)` is used for `𝓡₁`, `𝓡₃`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Circ

open Set Function
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Propagator
open scoped ComplexConjugate

variable {N : ℕ}

section Defs

variable (S : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (s : ℝ) {n : ℕ}

/-- `𝓡₁(x) = T̂_s(x_{k-1}, x_k) 𝒯_k[T̂^{(k-2)}_s f](x)` (first line of the Erdős–Riabov
remainder). -/
def circRemOne (f : CircFun N (n + 2 + 2)) : CircFun N (n + 2 + 2) := fun x =>
  vsKernel S (semicircleM z) (conj (semicircleM z)) s (x ⟨n + 2, by omega⟩)
      (x (Fin.last (n + 2 + 1))) *
    ∑ b, circSlot ⟨n + 1, by omega⟩ (vsKernel S (semicircleM z) (conj (semicircleM z)) s) f
      (update x (Fin.last (n + 2 + 1)) b)

/-- `𝓡₂(x) = T̂_s(x_{k-2}, x_{k-3}) 𝒯_{k-2}[T̂^{(k)}_s f](x)` (second line). -/
def circRemTwo (f : CircFun N (n + 2 + 2)) : CircFun N (n + 2 + 2) := fun x =>
  vsKernel S (semicircleM z) (conj (semicircleM z)) s (x ⟨n + 1, by omega⟩) (x ⟨n, by omega⟩) *
    ∑ b, circSlot (Fin.last (n + 2 + 1)) (vsKernel S (semicircleM z) (conj (semicircleM z)) s) f
      (update x ⟨n + 1, by omega⟩ b)

/-- `𝓡₃(x) = T̂_s(x_{k-1}, x_k) T̂_s(x_{k-2}, x_{k-3}) 𝒯_{k-2,k}[f](x)` (third line). -/
def circRemThree (f : CircFun N (n + 2 + 2)) : CircFun N (n + 2 + 2) := fun x =>
  vsKernel S (semicircleM z) (conj (semicircleM z)) s (x ⟨n + 2, by omega⟩)
      (x (Fin.last (n + 2 + 1))) *
    vsKernel S (semicircleM z) (conj (semicircleM z)) s (x ⟨n + 1, by omega⟩) (x ⟨n, by omega⟩) *
      ∑ b, ∑ c, f (update (update x ⟨n + 1, by omega⟩ b) (Fin.last (n + 2 + 1)) c)

end Defs

theorem circ_ringOp_add (S : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (t : ℝ) {k : ℕ} (j a : Fin k)
    (f g : CircFun N k) : ringOp S z t j a (f + g) = ringOp S z t j a f + ringOp S z t j a g := by
  funext x
  simp only [ringOp, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- **ER **:
`T̂^{(k-2)}_s T̂^{(k)}_s f = Θ̊^{(k-2)}_s Θ̊^{(k)}_s f + 𝓡₁ + 𝓡₂ - 𝓡₃`
for stochastic symmetric `S`, `Im z ≠ 0`, `s ∈ [0,1]`, `k = n+4`.
-/
theorem circ_twoSlot_decomp {S : Matrix (Fin N) (Fin N) ℝ} (hS : StochasticSymm S) {z : ℂ}
    (hz : z.im ≠ 0) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {n : ℕ} (f : CircFun N (n + 2 + 2)) :
    circSlot ⟨n + 1, by omega⟩ (vsKernel S (semicircleM z) (conj (semicircleM z)) s)
        (circSlot (Fin.last (n + 2 + 1)) (vsKernel S (semicircleM z) (conj (semicircleM z)) s)
          f) =
      ringOp S z s ⟨n + 1, by omega⟩ ⟨n, by omega⟩
          (ringOp S z s (Fin.last (n + 2 + 1)) ⟨n + 2, by omega⟩ f) +
        circRemOne S z s f + circRemTwo S z s f - circRemThree S z s f := by
  set T := vsKernel S (semicircleM z) (conj (semicircleM z)) s with hT
  have hsym := circ_kernel_symm hS hz hs (S := S)
  have hne1 : (⟨n, by omega⟩ : Fin (n + 2 + 2)) ≠ ⟨n + 1, by omega⟩ := by
    simp only [ne_eq, Fin.ext_iff]; omega
  have hne2 : (⟨n + 2, by omega⟩ : Fin (n + 2 + 2)) ≠ Fin.last (n + 2 + 1) := by
    simp only [ne_eq, Fin.ext_iff, Fin.val_last]; omega
  have hl1 : (Fin.last (n + 2 + 1) : Fin (n + 2 + 2)) ≠ ⟨n + 1, by omega⟩ := by
    simp only [ne_eq, Fin.ext_iff, Fin.val_last]; omega
  have hl0 : (Fin.last (n + 2 + 1) : Fin (n + 2 + 2)) ≠ ⟨n, by omega⟩ := by
    simp only [ne_eq, Fin.ext_iff, Fin.val_last]; omega
  have hl2 : (⟨n + 2, by omega⟩ : Fin (n + 2 + 2)) ≠ ⟨n + 1, by omega⟩ := by
    simp only [ne_eq, Fin.ext_iff]; omega
  set E2 : CircFun N (n + 2 + 2) := fun x =>
    T (x (Fin.last (n + 2 + 1))) (x ⟨n + 2, by omega⟩) * ∑ b, f (update x (Fin.last (n + 2 + 1)) b)
    with hE2
  have h2 := circSlot_eq_ringOp_add S z s hne2 f
  have hR2 : ringOp S z s (Fin.last (n + 2 + 1)) ⟨n + 2, by omega⟩ f =
      circSlot (Fin.last (n + 2 + 1)) T f - E2 := by
    rw [h2]
    funext x
    simp only [Pi.add_apply, Pi.sub_apply, E2, hT]
    ring
  have h1a := circSlot_eq_ringOp_add S z s hne1
    (ringOp S z s (Fin.last (n + 2 + 1)) ⟨n + 2, by omega⟩ f)
  have h1b := circSlot_eq_ringOp_add S z s hne1 E2
  -- `T̂^{(k-2)} E2 = 𝓡₁` (disjoint coordinates)
  have hc1 : circSlot ⟨n + 1, by omega⟩ T E2 = circRemOne S z s f := by
    funext x
    simp only [circSlot_apply, circRemOne, E2, hT, update_of_ne hl1, update_of_ne hl1.symm,
      update_of_ne hl2]
    rw [hsym (x (Fin.last (n + 2 + 1))) (x ⟨n + 2, by omega⟩)]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    rw [update_comm hl1.symm]
    ring
  -- `E1[T̂^{(k)} f] = 𝓡₂`, `E1[E2] = 𝓡₃`
  have hc2 : (fun x => T (x ⟨n + 1, by omega⟩) (x ⟨n, by omega⟩) *
      ∑ b, circSlot (Fin.last (n + 2 + 1)) T f (update x ⟨n + 1, by omega⟩ b)) =
        circRemTwo S z s f := rfl
  have hc3 : (fun x => T (x ⟨n + 1, by omega⟩) (x ⟨n, by omega⟩) *
      ∑ b, E2 (update x ⟨n + 1, by omega⟩ b)) = circRemThree S z s f := by
    funext x
    simp only [circRemThree, E2, hT, update_of_ne hl1, update_of_ne hl2]
    rw [hsym (x (Fin.last (n + 2 + 1))) (x ⟨n + 2, by omega⟩), Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [show circSlot (Fin.last (n + 2 + 1)) T f =
      ringOp S z s (Fin.last (n + 2 + 1)) ⟨n + 2, by omega⟩ f + E2 by rw [hR2]; abel, map_add,
    h1a, ← hc1, h1b]
  funext x
  have e2 : ∀ y, ringOp S z s (Fin.last (n + 2 + 1)) ⟨n + 2, by omega⟩ f y =
      circSlot (Fin.last (n + 2 + 1)) T f y - E2 y := fun y => congrFun hR2 y
  have hx2 := congrFun hc2 x
  have hx3 := congrFun hc3 x
  simp only [Pi.add_apply, Pi.sub_apply] at hx2 hx3 ⊢
  simp only [e2, Finset.sum_sub_distrib, mul_sub] at hx2 hx3 ⊢
  rw [← hx2, ← hx3]
  ring

end BlockBand.Native.ErdosRiabov.Circ
