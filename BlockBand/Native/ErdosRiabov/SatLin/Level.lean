module

public import BlockBand.Native.ErdosRiabov.SatLin.Side

/-!
# The levels of the saturated linear term against `φ^{av}_{k,T}` (term matching)

Deterministic. `φ = Expo.phiAv N ξ L_T Y_T k` at the zig data, `ℓ = logL N`.

* term matching in `Flow.Expo.avTerms`: `one_le_phiAv` (`ψ_{k,0} = 1`),
  `thrAv_one_le_phiAv_two` (`ψ^av_1 X^{-β_2}`, `β_2 = 0`), `thrIso_succ_le_phiAv`
  (`ψ_{k+1}`, `4 ≤ k ≤ 7`), and `thrAv_le_thrIso` (`ψ^av_{k-1}, ψ^av_{k-2} ≤ ψ_{k+1}`,
  `4 ≤ k ≤ 7`: the gainless remainder of `Circ.circ_LL_pointwise` is dominated for `k = 4, 6`);
* **`bShort_le`**: `bShort ≤ A ℓ^{757} ρ φ_2` for `ρ ≥ 1` (`A = A(d)`);
* **`bLong_le`**: `bLong ≤ A ℓ^{757} ρ² φ_k` for `ρ ≥ 1`, `B₂ ≤ ρ² φ_k` (`A = A(d)`);
* in the sibling module `Bridge`, from these bounds: `llLevelP7_le` (`k = 4, 6`): `LLGrid.llLevelP7 d p z n ε T ≤ A ℓ^{757} N^{ε/2} φ_k`.

The gainless terms `ψ^av_{k-1} X⁰`, `ψ^av_{k-2} X⁰` of `LLGrid.llLevelP7` (from
`Circ.circ_LL_pointwise` and `Circ.circ_integrand_long`) are **not** dominated by `φ^{av}_8`:
for `k = 8`, `avTerms 8` has no `X⁰` term `≥ ψ^av_7 N^{-ε'}` (its `X⁰` terms are `1`, `ψ_5` and
the `Y`-term), so `llLevelP7_le` is stated for `k = 4, 6` only.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.SatLin

open Set Function
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Flow.Expo
open BlockBand.Native.ErdosRiabov.Flow.Expo.Mono
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Propagator
open BlockBand.Native.ErdosRiabov.Forcing
open BlockBand.Native.ErdosRiabov.QV
open BlockBand.Native.ErdosRiabov.MI (intF eMI logL aInt aLam aZ cAvZ)
open BlockBand.Native.ErdosRiabov.Assembly (zigPsiData)
open BlockBand.Native.ErdosRiabov.Apriori (aprPsiI aprPsiA aprLamM)
open scoped NNReal

/-!
### Term matching
-/

section Terms

variable {N ξ X Y : ℝ} (hN : 0 < N) (hX : 0 < X) (hY : 0 < Y)
include hN hX hY

/-- A term of `avTerms k` is at most `φ^{av}_k`. -/
theorem term_le_phiAv {k : ℕ} {T : Term} (hT : T ∈ avTerms k) :
    T.value N ξ X Y ≤ phiAv N ξ X Y k := by
  unfold phiAv
  refine List.single_le_sum (fun y hy => ?_) _ (List.mem_map_of_mem hT)
  obtain ⟨T', _, rfl⟩ := List.mem_map.mp hy
  exact Term.value_nonneg' hN hX hY T'

/-- `1 ≤ φ^{av}_k` (the term `ψ_{k,0} = 1`). -/
theorem one_le_phiAv (k : ℕ) : 1 ≤ phiAv N ξ X Y k := by
  have h := term_le_phiAv hN hX hY (ξ := ξ) (k := k) (T := Term.mono Mono.one)
    (by unfold avTerms; simp)
  have e : (Term.mono Mono.one).value N ξ X Y = 1 := by
    simp [Term.value, Mono.value, Mono.one, Mono.gval]
  rwa [e] at h

/-- `ψ^av_1 ≤ φ^{av}_2` (the term `ψ^av_1 X^{-β_2}`, `β_2 = 0`). -/
theorem thrAv_one_le_phiAv_two : thrAv N ξ 1 ≤ phiAv N ξ X Y 2 := by
  have h := term_le_phiAv hN hX hY (ξ := ξ) (k := 2) (T := Term.mono (pA 1 * betaM 2))
    (by unfold avTerms; simp)
  have vb := value_basic N ξ X Y (k := 2) (by norm_num) 1 0
  rw [Term.value, Mono.value_mul hN hX hY, vb.2.1, vb.2.2.2.1, lossBeta_one_two.2, neg_zero,
    Real.rpow_zero, mul_one] at h
  exact h

/-- `ψ_{k+1} ≤ φ^{av}_k` for `4 ≤ k ≤ 7`. -/
theorem thrIso_succ_le_phiAv {k : ℕ} (hk4 : 4 ≤ k) (hk7 : k ≤ 7) :
    thrIso N ξ (k + 1) ≤ phiAv N ξ X Y k := by
  have h := term_le_phiAv hN hX hY (ξ := ξ) (k := k) (T := Term.mono (pI (k + 1)))
    (by unfold avTerms; simp [show ¬ k ≤ 3 by omega, hk7])
  rwa [Term.value, (value_basic N ξ X Y (k := 0) (by norm_num) (k + 1) 0).1] at h

omit hN hX hY in
/-- `ψ^av_j ≤ ψ_{k+1}` for `j + 1 ≤ k` (`N ≥ 1`, `ξ ≥ 0`). -/
theorem thrAv_le_thrIso {j k : ℕ} (hN1 : 1 ≤ N) (hξ : 0 ≤ ξ) (hjk : j + 1 ≤ k) :
    thrAv N ξ j ≤ thrIso N ξ (k + 1) := by
  unfold thrAv thrIso
  refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
  have : ((j : ℝ) + 3 / 2) ≤ ((k + 1 : ℕ) : ℝ) := by
    have : ((j + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hjk
    push_cast at this ⊢
    linarith
  nlinarith [mul_le_mul_of_nonneg_right this (show (0 : ℝ) ≤ ξ / 640 by positivity)]

omit hX hY in
theorem thrAv_nonneg (j : ℕ) : 0 ≤ thrAv N ξ j := Real.rpow_nonneg hN.le _

end Terms

/-!
### The polylog bounds of the levels
-/

section Bounds

variable (d : VSData) {p : BlockBand.Parameters} {z : ℂ}
  (hz : BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 z)

/-- The control parameter `φ^{av}_{k,T}` at the zig data. -/
def phiT (d : VSData) (p : BlockBand.Parameters) (z : ℂ) (T : ℝ) (k : ℕ) : ℝ :=
  phiAv ((p.n * p.W : ℕ) : ℝ) d.xi ((zigPsiData p d.D z).lEta T)
    (yScale (zigPsiData p d.D z) T) k

include hz in
/-- The scalars at the zig data: `0 < N`, `0 < L_T`, `0 < Y_T`, `1 ≤ ℓ`. -/
theorem zig_scalars {T : ℝ} (hT1 : T ≤ 1) :
    (0 : ℝ) < ((p.n * p.W : ℕ) : ℝ) ∧ 0 < (zigPsiData p d.D z).lEta T ∧
      0 < yScale (zigPsiData p d.D z) T ∧ 1 ≤ logL (p.n * p.W) := by
  have hN := MI.mi_N_pos p
  have hzi := hz.im_pos hN
  have hL := (zigPsiData p d.D z).lEta_pos hN p.W_pos hzi hT1
  refine ⟨by exact_mod_cast hN, hL, ?_, MI.mi_logL_one⟩
  unfold yScale
  have hη := vsHeight_pos hzi hT1
  have : (0 : ℝ) < ((p.n * p.W : ℕ) : ℝ) := by exact_mod_cast hN
  positivity

include hz in
/-- The basic `φ` facts at the zig data: `Φ^{av,f}_k ≤ φ_k`, `φ^{qv}_k ≤ φ_k`, `1 ≤ φ_k`. -/
theorem phiT_facts {T : ℝ} (hT1 : T ≤ 1) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ 8) :
    phiAvF (aprPsiI d (p.n * p.W)) (aprPsiA d (p.n * p.W)) ((zigPsiData p d.D z).lEta T)
        (yScale (zigPsiData p d.D z) T) k ≤ phiT d p z T k ∧
      qvPhiAv (aprPsiI d (p.n * p.W)) (aprPsiA d (p.n * p.W)) k
        ((zigPsiData p d.D z).lEta T) ≤ phiT d p z T k ∧ 1 ≤ phiT d p z T k := by
  obtain ⟨hN, hX, hY, -⟩ := zig_scalars d hz hT1
  obtain ⟨e1, e2⟩ := MI.aprPsi_eq d (p.n * p.W)
  rw [e1, e2]
  exact ⟨phiAvF_le_phiAv hN hX hY hk1 hk, MI.qvPhiAv_le_phiAv hN hX hY hk1 hk,
    one_le_phiAv hN hX hY k⟩

include hz in
/-- `C_av iF(γ) ≤ A ℓ^{757}` (`A = (3k²+k+1) c_av A_Z(k)² A_I(γ)`), `γ ≥ 0`, `k ≤ 8`. -/
theorem avConst_intF_le {T : ℝ} (hT1 : T ≤ 1) {k : ℕ} (hk : k ≤ 8) {γ : ℝ} (hγ : 0 ≤ γ) :
    avConst d (fun _ => aprLamM d (p.n * p.W)) (eMI d (p.n * p.W) k) k *
        intF d (zigPsiData p d.D z) γ T ≤
      ((3 * k * k + k + 1 : ℕ) : ℝ) * cAvZ d * 1 * aZ d k ^ 2 * aInt d γ *
        logL (p.n * p.W) ^ 757 := by
  obtain ⟨hΛ0, he0, hZ⟩ := MI.z_le d (p := p) hk
  have hℓ := MI.mi_logL_one (p := p)
  have h := MI.fbound_gen (m := ((3 * k * k + k + 1 : ℕ) : ℝ)) (K := 1) (K' := 1) hℓ
    (Nat.cast_nonneg _) (MI.cAv_nonneg d hΛ0 he0) (MI.cAvZ_nonneg d) (MI.cAv_le d hΛ0 he0)
    (by linarith) hZ zero_le_one le_rfl (MI.intF_nonneg d (zigPsiData p d.D z) rfl hz hT1 hγ)
    (MI.aInt_nonneg d hγ)
    (MI.intF_le_logL d (zigPsiData p d.D z) rfl hz hT1 hγ)
  unfold avConst
  refine (le_of_eq (by ring)).trans h

include hz in
/-- `√(𝔠 Λ³ iF(γ)) ≤ (1 + 𝔠 A_Λ³ A_I(γ)) ℓ^{757}`, `γ ≥ 0`. -/
theorem sqrt_qv_le {T : ℝ} (hT1 : T ≤ 1) {γ : ℝ} (hγ : 0 ≤ γ) :
    Real.sqrt (qvC d * aprLamM d (p.n * p.W) ^ 3 * intF d (zigPsiData p d.D z) γ T) ≤
      (1 + qvC d * aLam d ^ 3 * aInt d γ) * logL (p.n * p.W) ^ 757 := by
  obtain ⟨hΛ0, -, -⟩ := MI.z_le d (p := p) (k := 0) (by norm_num)
  have hℓ := MI.mi_logL_one (p := p)
  have h := MI.mbound_gen (m := 1) (K := 1) (K' := 1) hℓ zero_le_one zero_le_one le_rfl
    (qvC_pos d).le hΛ0 (MI.aprLamM_le_logL d (MI.mi_N_two p))
    (MI.intF_nonneg d (zigPsiData p d.D z) rfl hz hT1 hγ)
    (MI.intF_le_logL d (zigPsiData p d.D z) rfl hz hT1 hγ)
  simpa using h

/-!
### The level of the short slot
-/

/-- The constant of `bShort_le`. -/
def aShort (d : VSData) : ℝ :=
  onestepConst d * kernelActionConst d ^ 2 *
      (((3 * 2 * 2 + 2 + 1 : ℕ) : ℝ) * cAvZ d * 1 * aZ d 2 ^ 2 * aInt d 0) +
    onestepConst d * kernelActionConst d ^ 2 * (2 * vsCK d) * aInt d 0 + vsCK d +
    4 * ((1 + qvC d * aLam d ^ 3 * aInt d 0) * (onestepConst d * kernelActionConst d ^ 2))

theorem cR_pos (d : VSData) : 0 < onestepConst d * kernelActionConst d ^ 2 := by
  have := QV.qv_onestepConst_pos d; have := kernelActionConst_ge_one d; positivity

theorem aShort_nonneg (d : VSData) : 0 ≤ aShort d := by
  have := cR_pos d; have := MI.cAvZ_nonneg d; have := MI.aInt_nonneg d (γ := 0) le_rfl
  have := (vsCK_pos d).le; have := MI.aLam_nonneg d; have := (qvC_pos d).le
  unfold aShort; positivity

include hz in
/-- **The short level against `φ^{av}_{2,T}`**: `bShort ≤ aShort ℓ^{757} ρ φ_2` for `ρ ≥ 1`. -/
theorem bShort_le {T : ℝ} (hT1 : T ≤ 1) {ρ : ℝ} (hρ : 1 ≤ ρ) :
    bShort d (zigPsiData p d.D z) T ρ ≤
      aShort d * logL (p.n * p.W) ^ 757 * ρ * phiT d p z T 2 := by
  obtain ⟨hN, hX, hY, hℓ⟩ := zig_scalars d hz hT1
  obtain ⟨hΦ, hq, hφ1⟩ := phiT_facts d hz hT1 (k := 2) (by norm_num) (by norm_num)
  have hψ1 : aprPsiA d (p.n * p.W) 1 ≤ phiT d p z T 2 := by
    rw [(MI.aprPsi_eq d (p.n * p.W)).2]
    exact thrAv_one_le_phiAv_two hN hX hY
  set ℓ7 := logL (p.n * p.W) ^ 757
  set φ := phiT d p z T 2
  set cR := onestepConst d * kernelActionConst d ^ 2
  set C := avConst d (fun _ => aprLamM d (p.n * p.W)) (eMI d (p.n * p.W) 2) 2
  set Φ := phiAvF (aprPsiI d (p.n * p.W)) (aprPsiA d (p.n * p.W))
    ((zigPsiData p d.D z).lEta T) (yScale (zigPsiData p d.D z) T) 2
  set I0 := intF d (zigPsiData p d.D z) 0 T
  set sq := Real.sqrt (qvC d * aprLamM d (p.n * p.W) ^ 3 * I0)
  set φq := qvPhiAv (aprPsiI d (p.n * p.W)) (aprPsiA d (p.n * p.W)) 2
    ((zigPsiData p d.D z).lEta T)
  set a1 := ((3 * 2 * 2 + 2 + 1 : ℕ) : ℝ) * cAvZ d * 1 * aZ d 2 ^ 2 * aInt d 0
  set a2 := 1 + qvC d * aLam d ^ 3 * aInt d 0
  have hℓ7 : 1 ≤ ℓ7 := one_le_pow₀ hℓ
  have hl1 : logL (p.n * p.W) ≤ ℓ7 := by
    simpa using pow_le_pow_right₀ hℓ (show 1 ≤ 757 by norm_num)
  have hcR := cR_pos d
  have hCK := (vsCK_pos d).le
  have hA0 := MI.aInt_nonneg d (γ := 0) le_rfl
  have ha1 : 0 ≤ a1 := by have := MI.cAvZ_nonneg d; positivity
  have ha2 : 0 ≤ a2 := by have := MI.aLam_nonneg d; have := (qvC_pos d).le; positivity
  have hpsi := MI.mi_psi_ge d p
  have hpsi0 : ∀ n, 0 ≤ aprPsiI d (p.n * p.W) n ∧ 0 ≤ aprPsiA d (p.n * p.W) n := fun n =>
    ⟨by linarith [(hpsi n).1], by linarith [(hpsi n).2]⟩
  have hC0 : 0 ≤ C := MI.avConst_nonneg d (by linarith [MI.aprLamM_one_le d (MI.mi_N_pos p)])
    (MI.eMI_nonneg d (MI.mi_N_pos p) 2) 2
  have hΦ0 : 0 ≤ Φ := phiAvF_nonneg hpsi0 hX.le hY.le 2
  have hI00 : 0 ≤ I0 := MI.intF_nonneg d (zigPsiData p d.D z) rfl hz hT1 le_rfl
  have hψ0 : 0 ≤ aprPsiA d (p.n * p.W) 1 := (hpsi0 1).2
  have hsq0 : 0 ≤ sq := Real.sqrt_nonneg _
  have hφq0 : 0 ≤ φq := (qvPhiAv_pos (fun j => (hpsi j).1) (fun j => (hpsi0 j).2) 2 hX).le
  have hφ0 : 0 ≤ φ := by linarith
  have hCI : C * I0 ≤ a1 * ℓ7 := avConst_intF_le d hz hT1 (k := 2) (by norm_num) le_rfl
  have hI0 : I0 ≤ aInt d 0 * ℓ7 :=
    (MI.intF_le_logL d (zigPsiData p d.D z) rfl hz hT1 le_rfl).trans
      (mul_le_mul_of_nonneg_left hl1 hA0)
  have hsq : sq ≤ a2 * ℓ7 := sqrt_qv_le d hz hT1 le_rfl
  -- the three terms
  have t1 : cR * (C * Φ + 2 * vsCK d * aprPsiA d (p.n * p.W) 1) * I0 ≤
      (cR * a1 + cR * (2 * vsCK d) * aInt d 0) * ℓ7 * φ := by
    have e1 : cR * (C * Φ + 2 * vsCK d * aprPsiA d (p.n * p.W) 1) * I0 =
        cR * (C * I0) * Φ + cR * (2 * vsCK d) * aprPsiA d (p.n * p.W) 1 * I0 := by ring
    have h1 : cR * (C * I0) * Φ ≤ cR * (a1 * ℓ7) * φ :=
      mul_le_mul (mul_le_mul_of_nonneg_left hCI hcR.le) hΦ hΦ0
        (mul_nonneg hcR.le (mul_nonneg ha1 (by linarith)))
    have h2 : cR * (2 * vsCK d) * aprPsiA d (p.n * p.W) 1 * I0 ≤
        cR * (2 * vsCK d) * φ * (aInt d 0 * ℓ7) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hψ1 (by positivity)) hI0 hI00
        (mul_nonneg (by positivity) hφ0)
    rw [e1]
    nlinarith
  have t2 : vsCK d * aprPsiA d (p.n * p.W) 1 ≤ vsCK d * ℓ7 * φ := by
    have h1 := mul_le_mul_of_nonneg_left hψ1 hCK
    have h2 := mul_le_mul_of_nonneg_left hℓ7 (mul_nonneg hCK hφ0)
    linarith
  have t3 : 2 * ρ * (2 * sq * φq * cR) ≤ 4 * (a2 * cR) * ℓ7 * ρ * φ := by
    have h1 : sq * φq ≤ (a2 * ℓ7) * φ := mul_le_mul hsq hq hφq0 (mul_nonneg ha2 (by linarith))
    have h2 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 4 * ρ * cR by positivity)
    nlinarith
  have hρ0 : 0 ≤ ρ := by linarith
  have hX1 : 0 ≤ (cR * a1 + cR * (2 * vsCK d) * aInt d 0) * ℓ7 * φ := by positivity
  have hX2 : 0 ≤ vsCK d * ℓ7 * φ := by positivity
  have eb : bShort d (zigPsiData p d.D z) T ρ =
      cR * (C * Φ + 2 * vsCK d * aprPsiA d (p.n * p.W) 1) * I0 +
        vsCK d * aprPsiA d (p.n * p.W) 1 + 2 * ρ * (2 * sq * φq * cR) := rfl
  have ea : aShort d = cR * a1 + cR * (2 * vsCK d) * aInt d 0 + vsCK d + 4 * (a2 * cR) := rfl
  rw [eb, ea]
  have hρ1 := mul_le_mul_of_nonneg_left hρ hX1
  have hρ2 := mul_le_mul_of_nonneg_left hρ hX2
  nlinarith

/-!
### The level of the long slot
-/

/-- The constant of `bLong_le` (`k = n+4`, `β = β_k`). -/
def aLong (d : VSData) (n : ℕ) : ℝ :=
  vsCK d * d.Cwc * kernelActionConst d ^ (n + 4) *
      (((3 * (n + 4) * (n + 4) + (n + 4) + 1 : ℕ) : ℝ) * cAvZ d * 1 * aZ d (n + 4) ^ 2 *
        aInt d (1 - Expo.lossBeta (n + 4))) +
    kernelActionConst d ^ (n + 4) * kernelActionConst d * aInt d (1 - Expo.lossBeta (n + 4)) +
    16 * ((1 + qvC d * aLam d ^ 3 * aInt d (2 - 2 * Expo.lossBeta (n + 4))) *
      (vsCK d * d.Cwc * kernelActionConst d ^ (n + 4)))

include hz in
/-- **The long level against `φ^{av}_{k,T}`** (`k = n+4`): for `ρ ≥ 1`, `B₂ ≤ ρ² φ_k`,
`bLong ≤ aLong ℓ^{757} ρ² φ_k`. -/
theorem bLong_le {T : ℝ} (hT1 : T ≤ 1) {n : ℕ} (hn : n + 4 ≤ 8) {ρ B₂ : ℝ} (hρ : 1 ≤ ρ)
    (hB₂ : B₂ ≤ ρ ^ 2 * phiT d p z T (n + 4)) :
    0 ≤ aLong d n ∧ bLong d (zigPsiData p d.D z) n B₂ T ρ ≤
      aLong d n * logL (p.n * p.W) ^ 757 * ρ ^ 2 * phiT d p z T (n + 4) := by
  obtain ⟨hN, hX, hY, hℓ⟩ := zig_scalars d hz hT1
  obtain ⟨hΦ, hq, hφ1⟩ := phiT_facts d hz hT1 (k := n + 4) (by omega) hn
  set β := Expo.lossBeta (n + 4)
  have hγ1 : 0 ≤ 1 - β := by linarith [qv_beta_le_one (k := n + 4) hn]
  have hγ2 : 0 ≤ 2 - 2 * β := by linarith [qv_beta_le_one (k := n + 4) hn]
  set ℓ7 := logL (p.n * p.W) ^ 757
  set φ := phiT d p z T (n + 4)
  set cW := vsCK d * d.Cwc * kernelActionConst d ^ (n + 4)
  set CP := kernelActionConst d ^ (n + 4) * kernelActionConst d
  set C := avConst d (fun _ => aprLamM d (p.n * p.W)) (eMI d (p.n * p.W) (n + 4)) (n + 4)
  set Φ := phiAvF (aprPsiI d (p.n * p.W)) (aprPsiA d (p.n * p.W))
    ((zigPsiData p d.D z).lEta T) (yScale (zigPsiData p d.D z) T) (n + 4)
  set I1 := intF d (zigPsiData p d.D z) (1 - β) T
  set sq := Real.sqrt (qvC d * aprLamM d (p.n * p.W) ^ 3 * intF d (zigPsiData p d.D z)
    (2 - 2 * β) T)
  set φq := qvPhiAv (aprPsiI d (p.n * p.W)) (aprPsiA d (p.n * p.W)) (n + 4)
    ((zigPsiData p d.D z).lEta T)
  set a1 := ((3 * (n + 4) * (n + 4) + (n + 4) + 1 : ℕ) : ℝ) * cAvZ d * 1 * aZ d (n + 4) ^ 2 *
    aInt d (1 - β)
  set a2 := 1 + qvC d * aLam d ^ 3 * aInt d (2 - 2 * β)
  have hℓ7 : 1 ≤ ℓ7 := one_le_pow₀ hℓ
  have hl1 : logL (p.n * p.W) ≤ ℓ7 := by
    simpa using pow_le_pow_right₀ hℓ (show 1 ≤ 757 by norm_num)
  have hCP1 := kernelActionConst_ge_one d
  have hcW : 0 ≤ cW := by
    have := (vsCK_pos d).le; have := le_trans zero_le_one d.one_le_Cwc; positivity
  have hCP : 0 ≤ CP := by positivity
  have hA1 := MI.aInt_nonneg d hγ1
  have ha1 : 0 ≤ a1 := by have := MI.cAvZ_nonneg d; positivity
  have ha2 : 0 ≤ a2 := by
    have := MI.aLam_nonneg d; have := (qvC_pos d).le; have := MI.aInt_nonneg d hγ2; positivity
  have hpsi := MI.mi_psi_ge d p
  have hpsi0 : ∀ n, 0 ≤ aprPsiI d (p.n * p.W) n ∧ 0 ≤ aprPsiA d (p.n * p.W) n := fun n =>
    ⟨by linarith [(hpsi n).1], by linarith [(hpsi n).2]⟩
  have hΦ0 : 0 ≤ Φ := phiAvF_nonneg hpsi0 hX.le hY.le _
  have hI10 : 0 ≤ I1 := MI.intF_nonneg d (zigPsiData p d.D z) rfl hz hT1 hγ1
  have hsq0 : 0 ≤ sq := Real.sqrt_nonneg _
  have hφq0 : 0 ≤ φq := (qvPhiAv_pos (fun j => (hpsi j).1) (fun j => (hpsi0 j).2) _ hX).le
  have hφ0 : 0 ≤ φ := by linarith
  have hρ0 : 0 ≤ ρ := by linarith
  have hρ2 : ρ ≤ ρ ^ 2 := by nlinarith
  have hρ21 : 1 ≤ ρ ^ 2 := by nlinarith
  have hCI : C * I1 ≤ a1 * ℓ7 := avConst_intF_le d hz hT1 hn hγ1
  have hI1 : I1 ≤ aInt d (1 - β) * ℓ7 :=
    (MI.intF_le_logL d (zigPsiData p d.D z) rfl hz hT1 hγ1).trans
      (mul_le_mul_of_nonneg_left hl1 hA1)
  have hsq : sq ≤ a2 * ℓ7 := sqrt_qv_le d hz hT1 hγ2
  have hn8 : (n : ℝ) + 4 ≤ 8 := by
    have : ((n + 4 : ℕ) : ℝ) ≤ 8 := by exact_mod_cast hn
    push_cast at this; linarith
  have t1 : cW * (C * Φ) * I1 ≤ cW * a1 * ℓ7 * φ := by
    have h1 : (C * I1) * Φ ≤ (a1 * ℓ7) * φ :=
      mul_le_mul hCI hΦ hΦ0 (mul_nonneg ha1 (by linarith))
    have := mul_le_mul_of_nonneg_left h1 hcW
    linarith
  have t2 : CP * B₂ * I1 ≤ CP * aInt d (1 - β) * ℓ7 * ρ ^ 2 * φ := by
    have h1 : B₂ * I1 ≤ (ρ ^ 2 * φ) * (aInt d (1 - β) * ℓ7) :=
      mul_le_mul hB₂ hI1 hI10 (by positivity)
    have := mul_le_mul_of_nonneg_left h1 hCP
    linarith
  have t3 : 2 * ρ * (((n : ℝ) + 4) * sq * φq * cW) ≤ 16 * (a2 * cW) * ℓ7 * ρ ^ 2 * φ := by
    have h1 : sq * φq ≤ (a2 * ℓ7) * φ := mul_le_mul hsq hq hφq0 (mul_nonneg ha2 (by linarith))
    have h2 : ((n : ℝ) + 4) * (sq * φq) ≤ 8 * ((a2 * ℓ7) * φ) :=
      mul_le_mul hn8 h1 (mul_nonneg hsq0 hφq0) (by norm_num)
    have h3 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 2 * ρ * cW by positivity)
    have h4 : 16 * (a2 * cW) * ℓ7 * ρ * φ ≤ 16 * (a2 * cW) * ℓ7 * ρ ^ 2 * φ := by
      have := mul_le_mul_of_nonneg_left hρ2
        (show 0 ≤ 16 * (a2 * cW) * ℓ7 * φ by have := hℓ7; positivity)
      linarith
    linarith
  have hX1 : 0 ≤ cW * a1 * ℓ7 * φ := by positivity
  have eb : bLong d (zigPsiData p d.D z) n B₂ T ρ =
      cW * (C * Φ) * I1 + CP * B₂ * I1 + 2 * ρ * (((n : ℝ) + 4) * sq * φq * cW) := by
    unfold bLong bOne; ring
  have ea : aLong d n = cW * a1 + CP * aInt d (1 - β) + 16 * (a2 * cW) := rfl
  refine ⟨by rw [ea]; positivity, ?_⟩
  rw [eb, ea]
  have hρ1 := mul_le_mul_of_nonneg_left hρ21 hX1
  linarith

end Bounds

end BlockBand.Native.ErdosRiabov.SatLin
