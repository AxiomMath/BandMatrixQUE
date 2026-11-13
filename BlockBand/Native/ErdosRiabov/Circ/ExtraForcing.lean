module

public import BlockBand.Native.ErdosRiabov.Circ.CircEvol
public import BlockBand.Native.ErdosRiabov.Evol.RegWard
public import BlockBand.Native.ErdosRiabov.Contr.MoreSplit

/-!
# The extra forcing of regularized chains (short chains)

A deterministic bound on the extra forcing of short regularized chains in terms of the averaged
control quantity.

Setting: VS data `d`, `m ≥ 4`, `W ≥ 1`, `P : PsiData (mW)` with
`P.W = W`, `P.D = d.D`, `P.S = shortRingProfile d.b m W`, `P.z ∈ 𝒟`; `η_s = vsHeight P.z s`,
`L_s = P.lEta s`, `C_K = vsCK d`, `Ψ^av_{k,s}(H) = P.bigPsiAv k s H`, `β_k = lossBeta k`.

* `circ_norm_avErr_le`: `|𝒳^k_s(x)| ≤ Ψ^av_{k,s} L_s^{β_k} s^av_{k,s}(x)` (the definition of
  `Ψ`, positive denominators).
* `circ_traceLast_le`: for `k = n+2` and `σ_k ≠ σ_1`, the closing partial trace satisfies
  `|𝒯_k[𝒳^k](x)| ≤ η_s⁻¹ Ψ^av_{k-1,s} L_s^{β_{k-1}} s^av_{k-1,s}(x')` (Ward identity).
* **`extraForcing_two`** (short chains, `k = 2`, saturated pattern):
  `η_s |F̃_s[𝒳^2_s](x)| ≤ 2 C_K Ψ^av_{1,s} L_s^{β_1} s^av_{2,s}(x)`, i.e.
  `η|F̃|/(L^{β_2} s^av_2) ≤ 2 C_K ψ_1` on `{Ψ^av_1 ≤ ψ_1}` (`β_1 = β_2`).

The long chains (`k ∈ {4,6,8}`, `extraForcingLong`) are not covered here: the pair
`(x_{k-3}, x_{k-2})` term needs the Ward reduction at the internal slot `k-2`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Circ

open Set Function
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Propagator
open BlockBand.Native.ErdosRiabov.Evol
open BlockBand.Native.ErdosRiabov.Contr
open BlockBand.Internal.Contracts.Inputs (shortRingProfile polynomialControl)
open scoped ComplexConjugate

variable {N : ℕ}

/-- `|𝒳^k_t(x)| ≤ Ψ^av_{k,t}(H) L_t^{β_k} s^av_{k,t}(x)` when `L_t > 0` and `s^av_{k,t}(x) > 0`. -/
theorem circ_norm_avErr_le (P : PsiData N) {k : ℕ} (σ : Fin k → Bool) (x : Fin k → Fin N)
    {t : ℝ} (H : Matrix (Fin N) (Fin N) ℂ) (hL : 0 < P.lEta t) (hs : 0 < P.sAv x t) :
    ‖P.avErr σ x t H‖ ≤ P.bigPsiAv k t H * (P.lEta t ^ Expo.lossBeta k * P.sAv x t) := by
  have hden : 0 < P.lEta t ^ Expo.lossBeta k * P.sAv x t :=
    mul_pos (Real.rpow_pos_of_pos hL _) hs
  have h := P.avRatio_le_bigPsiAv (σ, x) t H
  unfold PsiData.avRatio at h
  exact (div_le_iff₀ hden).mp h

theorem circ_sAv_one (P : PsiData N) (x : Fin 1 → Fin N) (t : ℝ) : P.sAv x t = (P.lEta t)⁻¹ := by
  simp [PsiData.sAv]

/-- **Closing partial trace via Ward**: for `k = n+2`, `σ_k ≠ σ_1`, `s ∈ [0,1]`, Hermitian
`H`, with `L_s > 0` and `s^av_{k-1}` positive at the two reduced site vectors:
`|𝒯_k[𝒳^k_s](x)| ≤ η_s⁻¹ Ψ^av_{k-1,s} L_s^{β_{k-1}} s^av_{k-1,s}(x')`. **Conditional on
`Split.CyclicStatement` and `Split.WardStatement`.** -/
theorem circ_traceLast_le (hC : Split.CyclicStatement) (hWd : Split.WardStatement)
    (P : PsiData N) (hS : StochasticSymm P.S) (hz : 0 < P.z.im) {n : ℕ}
    (σ : Fin (n + 2) → Bool) (hσ : σ (Fin.last (n + 1)) ≠ σ 0) (x : Fin (n + 2) → Fin N)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {H : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    (hL : 0 < P.lEta s) (hsa : 0 < P.sAv (wardSites x) s) :
    ‖∑ b, P.avErr σ (update x (Fin.last (n + 1)) b) s H‖ ≤
      (vsHeight P.z s)⁻¹ * (P.bigPsiAv (n + 1) s H *
        (P.lEta s ^ Expo.lossBeta (n + 1) * P.sAv (wardSites x) s)) := by
  have hη := vsHeight_pos hz hs.2
  refine (wardReduction_norm hC hWd P hS hz σ hσ x hs hH).trans ?_
  have h1 := circ_norm_avErr_le P (wardPatLast σ) (wardSites x) H hL hsa
  have h2 := circ_norm_avErr_le P (wardPatHead σ) (wardSites x) H hL hsa
  calc (2 * vsHeight P.z s)⁻¹ * (‖P.avErr (wardPatLast σ) (wardSites x) s H‖ +
        ‖P.avErr (wardPatHead σ) (wardSites x) s H‖)
      ≤ (2 * vsHeight P.z s)⁻¹ * (2 * (P.bigPsiAv (n + 1) s H *
          (P.lEta s ^ Expo.lossBeta (n + 1) * P.sAv (wardSites x) s))) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by field_simp

theorem circ_last_ne_zero {n : ℕ} (σ : Fin (n + 2) → Bool) (hσ : ¬ HasDesatFactor σ) :
    σ (Fin.last (n + 1)) ≠ σ 0 := by
  intro h
  refine hσ ⟨Fin.last (n + 1), ?_⟩
  unfold patNext
  rw [dite_eq_right (by simp)]
  exact h

/-- **The extra forcing of short chains (`k = 2`)**, under the hypotheses
`Split.CyclicStatement` and `Split.WardStatement` (`hC`, `hWd`; proved as
`MTerms.cyclic_holds`, `MTerms.ward_holds`). For a saturated pattern `σ` of length `2`,
`s ∈ [0,1]`, Hermitian `H` and sites `x`:
`η_s |F̃_s[𝒳^2_s](x)| ≤ 2 C_K Ψ^av_{1,s}(H) L_s^{β_1} s^av_{2,s}(x)`, `F̃ = extraForcingShort`.
-/
theorem extraForcing_two (hC : Split.CyclicStatement) (hWd : Split.WardStatement)
    (d : VSData) {m W : ℕ} (hm : 4 ≤ m) (hW : 0 < W) (P : PsiData (m * W)) (hPW : P.W = W)
    (hPD : P.D = d.D) (hPS : P.S = shortRingProfile d.b m W)
    (hz : BulkDomain (m * W) d.delta0 d.kappa d.C0 P.z) (σ : Fin 2 → Bool)
    (hσ : ¬ HasDesatFactor σ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    {H : Matrix (Fin (m * W)) (Fin (m * W)) ℂ} (hH : H.IsHermitian) (x : Fin 2 → Fin (m * W)) :
    vsHeight P.z s * ‖extraForcingShort (n := 0) P.S P.z s (fun y => P.avErr σ y s H) x‖ ≤
      2 * vsCK d * P.bigPsiAv 1 s H * P.lEta s ^ Expo.lossBeta 1 * P.sAv x s := by
  have hN : 0 < m * W := Nat.mul_pos (by omega) hW
  have hin := contrVSInputs_of d hm hW P hPW hPD hz hs.1 hs.2
  have hS : StochasticSymm P.S := hPS ▸ shortRingProfile_stochasticSymm d.b_pos d.b_lt_half
    (by omega : 3 ≤ m) hW
  have hzi : 0 < P.z.im := hz.im_pos hN
  have hη := hin.height_pos
  have hL := hin.lEta_pos
  have hσ' := circ_last_ne_zero σ hσ
  have hPsi := P.bigPsiAv_nonneg (k := 1) s H
  have hsa : ∀ y : Fin 2 → Fin (m * W), 0 < P.sAv (wardSites y) s := fun y => by
    rw [circ_sAv_one]
    exact inv_pos.mpr hL
  have hT : ∀ y : Fin 2 → Fin (m * W),
      ‖∑ b, P.avErr σ (update y (Fin.last 1) b) s H‖ ≤
        (vsHeight P.z s)⁻¹ * (P.bigPsiAv 1 s H * (P.lEta s ^ Expo.lossBeta 1 * (P.lEta s)⁻¹)) :=
    fun y => by
      have h := circ_traceLast_le hC hWd P hS hzi σ hσ' y hs hH hL (hsa y)
      rwa [circ_sAv_one] at h
  have hK : ‖vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s (x 0) (x 1)‖ ≤
      vsCK d * P.ups s (x 0) (x 1) := by
    have h := (lemmaK_K1_single d.b_pos d.b_lt_half d.delta0_pos d.kappa_pos d.C0_ge_one
      d.D_ge_six hm hW hz hs.1 hs.2).1 (x 0) (x 1)
    rw [hPS]
    simpa only [PsiData.ups, hPW, hPD, vsCK] using h
  have hsAv : P.sAv x s = (P.lEta s)⁻¹ * P.ups s (x 0) (x 1) := by
    have h01 : finRotate 2 0 = 1 := by decide
    have h10 : finRotate 2 1 = 0 := by decide
    simp only [PsiData.sAv, show (2 : ℕ) ≠ 1 by norm_num, ite_false, Fin.prod_univ_two, h01, h10]
    rw [hin.symm (x 1) (x 0), Real.sqrt_mul_self (hin.nonneg _ _)]
    norm_num [Real.rpow_neg_one]
  have hE : extraForcingShort (n := 0) P.S P.z s (fun y => P.avErr σ y s H) x =
      vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s (x 0) (x 1) *
        (∑ b, P.avErr σ (update (update x 0 (x 1)) (Fin.last 1) b) s H +
          ∑ b, P.avErr σ (update x (Fin.last 1) b) s H) := rfl
  rw [hE, norm_mul, hsAv]
  have hsum := (norm_add_le _ _).trans (add_le_add (hT (update x 0 (x 1))) (hT x))
  have hU := hin.nonneg (x 0) (x 1)
  have hCK := vsCK_pos d
  calc vsHeight P.z s * (‖vsKernel P.S (semicircleM P.z) (conj (semicircleM P.z)) s (x 0) (x 1)‖ *
        ‖∑ b, P.avErr σ (update (update x 0 (x 1)) (Fin.last 1) b) s H +
          ∑ b, P.avErr σ (update x (Fin.last 1) b) s H‖)
      ≤ vsHeight P.z s * (vsCK d * P.ups s (x 0) (x 1) *
          (2 * ((vsHeight P.z s)⁻¹ *
            (P.bigPsiAv 1 s H * (P.lEta s ^ Expo.lossBeta 1 * (P.lEta s)⁻¹))))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul hK (by linarith) (norm_nonneg _)
          (by positivity)) hη.le
    _ = _ := by field_simp

end BlockBand.Native.ErdosRiabov.Circ
