module

public import BlockBand.Native.ErdosRiabov.SatLin.Slots
public import BlockBand.Native.ErdosRiabov.LLGrid.Lip

/-!
# The saturated linear term at nearby times (deterministic)

Setting: `P : PsiData N`, `N ≥ 1`, `z ∈ 𝒟`, `S` stochastic symmetric, `T̂_t = vsKernel S m m̄ t`,
`r = (Im z)⁻¹`, times in `[0,1]`. The kernel bounds, the one-slot difference bound and the crude
bound on `𝒳` are `LLGrid.kernel_rowSum_le`, `LLGrid.kernel_sub_le`,
`LLGrid.norm_circSlot_sub_le`, `LLGrid.norm_avErr_le`, `LLGrid.vsHeight_le_im_add_one`.

* `linQ σ s H u = η_s |T̂^{⊕k}_s[𝒳_s(H)](u)|`; `linQ_le_sum`: `linQ ≤ Σ_j η_s |T̂^{(j)}_s[𝒳_s](u)|`;
* **`linQ_le_near`**: for Hermitian `H, H'` with `|(H - H')_{ab}| ≤ δ` and `|𝒳_t(H)| ≤ M`,
  `linQ_t(H) ≤ (1 + |t-s|/Im z) linQ_s(H') + (Im z + 1) k (N |t-s| r² M + r N errLip(δ,|t-s|,B))`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.SatLin

open Set Function
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Propagator
open BlockBand.Native.ErdosRiabov.Circ
open scoped ComplexConjugate Matrix.Norms.L2Operator

variable {N : ℕ}

/-!
### The saturated linear functional
-/

/-- **The saturated linear functional** `η_s |T̂^{⊕k}_s[𝒳_s(H)](u)|` (the body of
`MI.SatLinBound`). -/
def linQ (P : PsiData N) {k : ℕ} (σ : Fin k → Bool) (s : ℝ) (H : Matrix (Fin N) (Fin N) ℂ)
    (u : Fin k → Fin N) : ℝ :=
  vsHeight P.z s *
    ‖propOp (vsTensorGen P.S (fun _ => semicircleM P.z) (fun _ => conj (semicircleM P.z)) s)
      (fun y => P.avErr σ y s H) u‖

/-- `linQ ≤ Σ_j η_s |T̂^{(j)}_s[𝒳_s](u)|`. -/
theorem linQ_le_sum (P : PsiData N) {k : ℕ} (σ : Fin k → Bool) {s : ℝ}
    (hη : 0 ≤ vsHeight P.z s) (H : Matrix (Fin N) (Fin N) ℂ) (u : Fin k → Fin N) :
    linQ P σ s H u ≤ ∑ j, vsHeight P.z s *
      ‖circSlot j (vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s)
        (fun y => P.avErr σ y s H) u‖ := by
  unfold linQ
  rw [propOp_vsTensorGen_const, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) hη

/-- **Two-time comparison of the saturated linear functional.** For `s, t ∈ [0,1]`, Hermitian
`H, H'` with `|(H - H')_{ab}| ≤ δ`, `|𝒳_t(H)| ≤ M` and `B` as in
`Grid.PsiData.norm_avErr_sub_le` (`r = (Im z)⁻¹`):
`linQ_t(H) ≤ (1 + |t-s|/Im z) linQ_s(H') + (Im z + 1) k (N |t-s| r² M + r N errLip(δ,|t-s|,B))`.
-/
theorem linQ_le_near (P : PsiData N) (hN : 0 < N) {δ₀ κ C₀ : ℝ}
    (hz : BulkDomain N δ₀ κ C₀ P.z) (hS : StochasticSymm P.S) {k : ℕ}
    (σ : Fin k → Bool) {H H' : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    (hH' : H'.IsHermitian) {δ : ℝ} (hδ : ∀ a b, ‖(H - H') a b‖ ≤ δ) {B : ℝ} (hB2 : 2 ≤ B)
    (hBL : ((k - 1 : ℕ) : ℝ) * (1 - ‖semicircleM P.z‖ ^ 2)⁻¹ ≤ B) {t s : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) {M : ℝ}
    (hM : ∀ y, ‖P.avErr σ y t H‖ ≤ M) (u : Fin k → Fin N) :
    linQ P σ t H u ≤ (1 + |t - s| / P.z.im) * linQ P σ s H' u +
      (P.z.im + 1) * (k * (N * (|t - s| * P.z.im⁻¹ ^ 2) * M +
        P.z.im⁻¹ * (N * (Grid.PsiData.errLip P) k δ |t - s| B))) := by
  have hzi := hz.im_pos hN
  set K := vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z))
  set f : (Fin k → Fin N) → ℂ := fun y => P.avErr σ y t H
  set g : (Fin k → Fin N) → ℂ := fun y => P.avErr σ y s H'
  have he0 : 0 ≤ (N : ℝ) * (Grid.PsiData.errLip P) k δ |t - s| B :=
    mul_nonneg (Nat.cast_nonneg _) ((Grid.PsiData.errLip_nonneg P) k
      ((norm_nonneg _).trans (hδ ⟨0, hN⟩ ⟨0, hN⟩)) (abs_nonneg _) (by linarith))
  have hfg : ∀ y, ‖f y - g y‖ ≤ N * (Grid.PsiData.errLip P) k δ |t - s| B := fun y =>
    (Grid.PsiData.norm_avErr_sub_le P) hzi hS σ y hH hH' hδ hB2 hBL ht hs
  have hslot : ∀ j : Fin k, ‖circSlot j (K t) f u - circSlot j (K s) g u‖ ≤
      N * (|t - s| * P.z.im⁻¹ ^ 2) * M +
        P.z.im⁻¹ * (N * (Grid.PsiData.errLip P) k δ |t - s| B) := fun j =>
    LLGrid.norm_circSlot_sub_le j
      (fun a c => LLGrid.kernel_sub_le hS hN hz hs.1 hs.2 ht.1 ht.2 a c)
      (fun a => LLGrid.kernel_rowSum_le hS hN hz hs.1 hs.2 a) hM hfg he0 u
  have hdiff : ‖propOp (vsTensorGen P.S (fun _ => semicircleM P.z)
        (fun _ => conj (semicircleM P.z)) t) f u -
      propOp (vsTensorGen P.S (fun _ => semicircleM P.z)
        (fun _ => conj (semicircleM P.z)) s) g u‖ ≤
      k * (N * (|t - s| * P.z.im⁻¹ ^ 2) * M +
        P.z.im⁻¹ * (N * (Grid.PsiData.errLip P) k δ |t - s| B)) := by
    rw [propOp_vsTensorGen_const, propOp_vsTensorGen_const, ← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun j _ => hslot j).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hηt := LLGrid.vsHeight_le_im_add_one hzi ht.1
  have hηt0 : 0 ≤ vsHeight P.z t := (vsHeight_pos hzi ht.2).le
  have hηs0 : 0 ≤ vsHeight P.z s := (vsHeight_pos hzi hs.2).le
  have hq := (Grid.PsiData.heights_le_mul P) hzi (t := t) hs.2
  have hE0 : 0 ≤ k * (N * (|t - s| * P.z.im⁻¹ ^ 2) * M +
      P.z.im⁻¹ * (N * (Grid.PsiData.errLip P) k δ |t - s| B)) :=
    (norm_nonneg _).trans hdiff
  have htri := norm_le_insert' (propOp (vsTensorGen P.S (fun _ => semicircleM P.z)
        (fun _ => conj (semicircleM P.z)) t) f u)
    (propOp (vsTensorGen P.S (fun _ => semicircleM P.z) (fun _ => conj (semicircleM P.z)) s) g u)
  unfold linQ
  set A := ‖propOp (vsTensorGen P.S (fun _ => semicircleM P.z)
    (fun _ => conj (semicircleM P.z)) s) g u‖
  have hA0 : 0 ≤ A := norm_nonneg _
  calc vsHeight P.z t * ‖propOp (vsTensorGen P.S (fun _ => semicircleM P.z)
        (fun _ => conj (semicircleM P.z)) t) f u‖
      ≤ vsHeight P.z t * A + vsHeight P.z t * k * (N * (|t - s| * P.z.im⁻¹ ^ 2) * M +
          P.z.im⁻¹ * (N * (Grid.PsiData.errLip P) k δ |t - s| B)) := by
        rw [mul_assoc, ← mul_add]
        refine mul_le_mul_of_nonneg_left ?_ hηt0
        linarith
    _ ≤ (1 + |t - s| / P.z.im) * (vsHeight P.z s * A) + (P.z.im + 1) * (k * (N *
          (|t - s| * P.z.im⁻¹ ^ 2) * M + P.z.im⁻¹ * (N * (Grid.PsiData.errLip P) k δ |t - s| B)))
        := by
        have h1 : vsHeight P.z t * A ≤ (1 + |t - s| / P.z.im) * vsHeight P.z s * A :=
          mul_le_mul_of_nonneg_right hq hA0
        have h2 := mul_le_mul_of_nonneg_right hηt hE0
        nlinarith

end BlockBand.Native.ErdosRiabov.SatLin
