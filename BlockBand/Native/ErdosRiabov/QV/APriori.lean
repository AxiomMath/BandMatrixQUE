module

public import BlockBand.Native.ErdosRiabov.QV.Word
public import BlockBand.Native.ErdosRiabov.Prop.Single
public import BlockBand.Native.ErdosRiabov.Evol.TermListPair

/-!
# Quadratic variation: the a priori hypothesis `APriori` and its word form

* `APriori P psiI psiA LamM s H` is the a priori hypothesis `AP(s, H; Λ)` of the
  quadratic-variation estimates: for every `1 ≤ k ≤ 8`, pattern and sites,
  `|𝒴^k| ≤ ψ_k L^{α_k} s^iso`, `|𝒳^k| ≤ ψ^av_k L^{β_k} s^av`, `|M_aa| ≤ Λ_M √L s^iso(a,·,a)` and
  `|Tr M S^{x_k}| ≤ Λ_M L s^av`. **Naming:** `LamM` is the `M`-bound constant `Λ_M`
  (`= C (log N)^{C'}`), not `Λ = c_m⁻¹ log((C₀+1)N)` (written `Λ_N`).
  `APriori` is a hypothesis of every quadratic-variation estimate (it is discharged by
  `Apriori.qvAPriori_of_le_tau`).
* Word form (`APriori.word_*`): the same bounds for the words `qvW`, with the list sizes
  `qvIsoSq`, `qvAvSq`.
* Sandwich identities: `(Y S^q Yᴴ)_aa = Σ_e S_qe |Y_ae|²`, `(Yᴴ S^d Y)_bb = Σ_c S_dc |Y_cb|²`,
  `Tr[Y S^q Yᴴ S^b] = Σ_a S_ba Σ_e S_qe |Y_ae|²`, `(Y S^q X)_cb = Σ_e Y_ce S_qe X_eb`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.QV

open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Internal.Contracts.Inputs (polynomialControl shortRingProfile)
open Matrix
open scoped ComplexConjugate

variable {N : ℕ}

/-!
## Sandwich identities
-/

section Sandwich

variable (S : Matrix (Fin N) (Fin N) ℝ)

theorem qv_mul_obs_apply (Y X : Matrix (Fin N) (Fin N) ℂ) (q c b : Fin N) :
    (Y * obsMat S q * X) c b = ∑ e, Y c e * (S q e : ℂ) * X e b := by
  rw [Matrix.mul_apply]
  simp only [obsMat, Matrix.mul_diagonal, Split.rowObs]

theorem qv_sandwich_right (Y : Matrix (Fin N) (Fin N) ℂ) (q a : Fin N) :
    (Y * obsMat S q * Yᴴ) a a = ∑ e, (S q e : ℂ) * ((‖Y a e‖ ^ 2 : ℝ) : ℂ) := by
  rw [qv_mul_obs_apply]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Matrix.conjTranspose_apply, Complex.ofReal_pow, ← Complex.mul_conj']
  simp only [RCLike.star_def]
  ring

theorem qv_sandwich_left (Y : Matrix (Fin N) (Fin N) ℂ) (d b : Fin N) :
    (Yᴴ * obsMat S d * Y) b b = ∑ c, (S d c : ℂ) * ((‖Y c b‖ ^ 2 : ℝ) : ℂ) := by
  rw [qv_mul_obs_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.conjTranspose_apply, Complex.ofReal_pow, ← Complex.mul_conj']
  simp only [RCLike.star_def]
  ring

theorem qv_trace_sandwich (Y : Matrix (Fin N) (Fin N) ℂ) (q b : Fin N) :
    Matrix.trace (Y * obsMat S q * Yᴴ * obsMat S b) =
      ∑ a, (S b a : ℂ) * ∑ e, (S q e : ℂ) * ((‖Y a e‖ ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.trace]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.diag_apply, show obsMat S b = diagonal (Split.rowObs S b) from rfl,
    Matrix.mul_diagonal, qv_sandwich_right]
  simp only [Split.rowObs]
  ring

end Sandwich

/-!
## The a priori hypothesis
-/

/-- **The a priori hypothesis `AP(s, H; Λ_M)`**, with the
thresholds `psiI k = ψ_k`, `psiA k = ψ^av_k` and the `M`-bound constant `LamM`. -/
structure APriori (P : PsiData N) (psiI psiA : ℕ → ℝ) (LamM s : ℝ)
    (H : Matrix (Fin N) (Fin N) ℂ) : Prop where
  iso : ∀ (k : ℕ), 1 ≤ k → k ≤ 8 → ∀ (σ : Fin k → Bool) (a b : Fin N) (x : Fin k → Fin N),
    ‖P.isoErr σ a b x s H‖ ≤ psiI k * P.lEta s ^ Expo.lossAlpha k * P.sIso a b x s
  av : ∀ (k : ℕ), 1 ≤ k → k ≤ 8 → ∀ (σ : Fin k → Bool) (x : Fin k → Fin N),
    ‖P.avErr σ x s H‖ ≤ psiA k * P.lEta s ^ Expo.lossBeta k * P.sAv x s
  mIso : ∀ (k : ℕ), 1 ≤ k → k ≤ 8 → ∀ (σ : Fin k → Bool) (a : Fin N) (x : Fin k → Fin N),
    ‖P.mChain σ x s a‖ ≤ LamM * Real.sqrt (P.lEta s) * P.sIso a a x s
  mAv : ∀ (k : ℕ), 1 ≤ k → k ≤ 8 → ∀ (σ : Fin k → Bool) (x : Fin k → Fin N),
    ‖∑ a, P.mChain σ x s a * obsSeq P.S x k a‖ ≤ LamM * P.lEta s * P.sAv x s

namespace APriori

variable {P : PsiData N} {psiI psiA : ℕ → ℝ} {LamM s : ℝ} {H : Matrix (Fin N) (Fin N) ℂ}
  (hA : APriori P psiI psiA LamM s H) (hU : ∀ x y, 0 ≤ P.ups s x y) (hL : 0 < P.lEta s)
include hA hU hL

/-- `G - M` bound for a word. -/
theorem word_iso_err (β₀ : Bool) (r : List (Fin N × Bool)) (hk : r.length + 1 ≤ 8)
    (a b : Fin N) :
    ‖qvW P s H β₀ r a b - (if a = b then P.mChain (qvSig β₀ r) (qvSites r a) s a else 0)‖ ≤
      psiI (r.length + 1) * P.lEta s ^ Expo.lossAlpha (r.length + 1) *
        Real.sqrt (qvIsoSq P s a (r.map Prod.fst) b) := by
  have h := hA.iso (r.length + 1) (by omega) hk (qvSig β₀ r) a b (qvSites r a)
  rw [PsiData.isoErr, gChain_iso_qvW, sIso_qvSites P hU hL] at h
  exact h

/-- **Word form of (APG), isotropic**: for `k = |r|+1 ≤ 8`,
`|W_ab| ≤ Λ_M (δ_ab √L + ψ_k L^{α_k}) s(a, r.map fst, b)`.
-/
theorem word_iso (hLam : 1 ≤ LamM) (β₀ : Bool)
    (r : List (Fin N × Bool)) (hpsi : 0 ≤ psiI (r.length + 1)) (hk : r.length + 1 ≤ 8)
    (a b : Fin N) :
    ‖qvW P s H β₀ r a b‖ ≤ LamM * ((if a = b then Real.sqrt (P.lEta s) else 0) +
      psiI (r.length + 1) * P.lEta s ^ Expo.lossAlpha (r.length + 1)) *
        Real.sqrt (qvIsoSq P s a (r.map Prod.fst) b) := by
  have h1 := hA.word_iso_err hU hL β₀ r hk a b
  set q := Real.sqrt (qvIsoSq P s a (r.map Prod.fst) b)
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hT : 0 ≤ psiI (r.length + 1) * P.lEta s ^ Expo.lossAlpha (r.length + 1) * q :=
    mul_nonneg (mul_nonneg hpsi (Real.rpow_nonneg hL.le _)) hq
  have hM : ‖(if a = b then P.mChain (qvSig β₀ r) (qvSites r a) s a else 0)‖ ≤
      LamM * (if a = b then Real.sqrt (P.lEta s) else 0) * q := by
    split_ifs with hab
    · subst hab
      have h2 := hA.mIso (r.length + 1) (by omega) hk (qvSig β₀ r) a (qvSites r a)
      rwa [sIso_qvSites P hU hL] at h2
    · simp
  calc ‖qvW P s H β₀ r a b‖
      ≤ ‖qvW P s H β₀ r a b - (if a = b then P.mChain (qvSig β₀ r) (qvSites r a) s a else 0)‖ +
          ‖(if a = b then P.mChain (qvSig β₀ r) (qvSites r a) s a else 0)‖ := by
        have := norm_add_le (qvW P s H β₀ r a b -
          (if a = b then P.mChain (qvSig β₀ r) (qvSites r a) s a else 0))
          (if a = b then P.mChain (qvSig β₀ r) (qvSites r a) s a else 0)
        rwa [sub_add_cancel] at this
    _ ≤ psiI (r.length + 1) * P.lEta s ^ Expo.lossAlpha (r.length + 1) * q +
          LamM * (if a = b then Real.sqrt (P.lEta s) else 0) * q := add_le_add h1 hM
    _ ≤ LamM * (psiI (r.length + 1) * P.lEta s ^ Expo.lossAlpha (r.length + 1) * q) +
          LamM * (if a = b then Real.sqrt (P.lEta s) else 0) * q := by
        have := le_mul_of_one_le_left hT hLam
        linarith
    _ = _ := by ring

/-- Squared word form:
`|W_ab|² ≤ 2Λ_M² (δ_ab L + ψ_k² (L^{α_k})²) s(a, ·, b)²`.
-/
theorem word_iso_sq (hLam : 1 ≤ LamM) (β₀ : Bool)
    (r : List (Fin N × Bool)) (hpsi : 0 ≤ psiI (r.length + 1)) (hk : r.length + 1 ≤ 8)
    (a b : Fin N) :
    ‖qvW P s H β₀ r a b‖ ^ 2 ≤ 2 * LamM ^ 2 * ((if a = b then P.lEta s else 0) +
      psiI (r.length + 1) ^ 2 * (P.lEta s ^ Expo.lossAlpha (r.length + 1)) ^ 2) *
        qvIsoSq P s a (r.map Prod.fst) b := by
  have h := hA.word_iso hU hL hLam β₀ r hpsi hk a b
  have hq := qvIsoSq_nonneg P s hU hL a (r.map Prod.fst) b
  set q := qvIsoSq P s a (r.map Prod.fst) b
  set x := (if a = b then Real.sqrt (P.lEta s) else 0)
  set y := psiI (r.length + 1) * P.lEta s ^ Expo.lossAlpha (r.length + 1)
  have hx : 0 ≤ x := by unfold x; split_ifs <;> simp [Real.sqrt_nonneg]
  have hy : 0 ≤ y := mul_nonneg hpsi (Real.rpow_nonneg hL.le _)
  have hx2 : x ^ 2 = (if a = b then P.lEta s else 0) := by
    unfold x; split_ifs <;> simp [Real.sq_sqrt hL.le]
  have h0 : 0 ≤ LamM * (x + y) * Real.sqrt q :=
    mul_nonneg (mul_nonneg (by linarith) (add_nonneg hx hy)) (Real.sqrt_nonneg _)
  calc ‖qvW P s H β₀ r a b‖ ^ 2 ≤ (LamM * (x + y) * Real.sqrt q) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = LamM ^ 2 * (x + y) ^ 2 * q := by rw [mul_pow, mul_pow, Real.sq_sqrt hq]
    _ ≤ LamM ^ 2 * (2 * (x ^ 2 + y ^ 2)) * q := by
        gcongr
        nlinarith [sq_nonneg (x - y)]
    _ = _ := by rw [hx2]; unfold y; ring

/-- **Word form of (APG), averaged**: for `k = |r|+1 ≤ 8`,
`|Tr[W(β₀,r) S^c]| ≤ Λ_M (L + ψ^av_k L^{β_k}) s^av(c:: r.map fst)`.
-/
theorem word_av (hLam : 1 ≤ LamM) (β₀ : Bool)
    (r : List (Fin N × Bool)) (hpsi : 0 ≤ psiA (r.length + 1)) (hk : r.length + 1 ≤ 8) (c : Fin N) :
    ‖Matrix.trace (qvW P s H β₀ r * obsMat P.S c)‖ ≤
      LamM * (P.lEta s + psiA (r.length + 1) * P.lEta s ^ Expo.lossBeta (r.length + 1)) *
        Real.sqrt (qvAvSq P s c (r.map Prod.fst)) := by
  have h1 := hA.av (r.length + 1) (by omega) hk (qvSig β₀ r) (qvSites r c)
  have h2 := hA.mAv (r.length + 1) (by omega) hk (qvSig β₀ r) (qvSites r c)
  rw [PsiData.avErr, gChain_av_qvW, sAv_qvSites P hU hL] at h1
  rw [sAv_qvSites P hU hL] at h2
  set q := Real.sqrt (qvAvSq P s c (r.map Prod.fst))
  set M := ∑ a, P.mChain (qvSig β₀ r) (qvSites r c) s a * obsSeq P.S (qvSites r c)
    (r.length + 1) a
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hT : 0 ≤ psiA (r.length + 1) * P.lEta s ^ Expo.lossBeta (r.length + 1) * q :=
    mul_nonneg (mul_nonneg hpsi (Real.rpow_nonneg hL.le _)) hq
  calc ‖Matrix.trace (qvW P s H β₀ r * obsMat P.S c)‖
      ≤ ‖Matrix.trace (qvW P s H β₀ r * obsMat P.S c) - M‖ + ‖M‖ := by
        have := norm_add_le (Matrix.trace (qvW P s H β₀ r * obsMat P.S c) - M) M
        rwa [sub_add_cancel] at this
    _ ≤ psiA (r.length + 1) * P.lEta s ^ Expo.lossBeta (r.length + 1) * q +
          LamM * P.lEta s * q := add_le_add h1 h2
    _ ≤ LamM * (psiA (r.length + 1) * P.lEta s ^ Expo.lossBeta (r.length + 1) * q) +
          LamM * P.lEta s * q := by
        have := le_mul_of_one_le_left hT hLam
        linarith
    _ = _ := by ring

end APriori

/-!
## The `M`-term of the two-chain and the stability operator
-/

/-- **The `M`-term of the two-chain**, under the hypothesis `Split.ExplicitShortStatement`
(proved as `MTerms.explicitShort_holds`): for a profile with `StochasticSymm`, `Im z ≠ 0` and
`s ∈ [0,1]`, the `M`-term of the two-chain `G_β S^c G_{β'}` is
`m_β m_β' Σ_d stabOp_s(m_β m_β')(a,d) S_cd`. -/
theorem qv_mChain_two (hES : Split.ExplicitShortStatement) (P : PsiData N)
    (hS : StochasticSymm P.S) (hz : P.z.im ≠ 0) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (β β' : Bool) (c e a : Fin N) :
    P.mChain (qvSig β [(c, β')]) (qvSites [(c, β')] e) s a =
      VS.patConj β (semicircleM P.z) * VS.patConj β' (semicircleM P.z) *
        ∑ d, Split.stabOp s P.S (VS.patConj β (semicircleM P.z) *
          VS.patConj β' (semicircleM P.z)) a d * (P.S c d : ℂ) := by
  have hP := (stochasticSymm_iff_profileHyp (S := P.S)).mp hS
  have h := (hES N P.S hP s hs (patM P.z (qvSig β [(c, β')]))
    (norm_patM_lt_one hz _)).2.1 (obsSeq P.S (qvSites [(c, β')] e))
  have h1 : patM P.z (qvSig β [(c, β')]) 1 = VS.patConj β (semicircleM P.z) := by
    simp [patM, qvSig]
  have h2 : patM P.z (qvSig β [(c, β')]) 2 = VS.patConj β' (semicircleM P.z) := by
    simp [patM, qvSig]
  have h3 : obsSeq P.S (qvSites [(c, β')] e) 1 = Split.rowObs P.S c := by
    simp [obsSeq, qvSites]
  unfold PsiData.mChain
  change Split.chainM s P.S _ _ 1 2 a = _
  rw [h, h1, h2, h3]
  simp [Matrix.mulVec, dotProduct, Split.rowObs, Finset.mul_sum]

theorem qv_patConj_mul_not (β : Bool) (m : ℂ) :
    VS.patConj β m * VS.patConj (!β) m = m * conj m := by
  cases β <;> simp [VS.patConj, mul_comm]

/-- **(K1) for the stability operator**: along the VS flow,
`|stabOp_s(m m̄)(a,b)| ≤ δ_ab + C_K Υ_s(a,b)`, from `stabOp = 1 + s Θ̂_s` and (K1).
-/
theorem qv_stabOp_le (d : VSData) {m W : ℕ} (hm : 4 ≤ m) (hW : 0 < W) (P : PsiData (m * W))
    (hPW : P.W = W) (hPD : P.D = d.D) (hPS : P.S = shortRingProfile d.b m W)
    (hz : BulkDomain (m * W) d.delta0 d.kappa d.C0 P.z) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (a b : Fin (m * W)) :
    ‖Split.stabOp s P.S (semicircleM P.z * conj (semicircleM P.z)) a b‖ ≤
      (if a = b then 1 else 0) + Propagator.vsCK d * P.ups s a b := by
  have hN : 0 < m * W := Nat.mul_pos (by omega) hW
  have hη := hz.im_pos hN
  have hS := shortRingProfile_stochasticSymm d.b_pos d.b_lt_half (m := m) (by omega) hW
  have hmn := norm_semicircleM_lt_one hη.ne'
  have ht : ‖(s : ℂ) * (semicircleM P.z * conj (semicircleM P.z))‖ < 1 := by
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hs0]
    have h0 := norm_nonneg (semicircleM P.z)
    nlinarith [mul_le_mul hmn.le hmn.le h0 zero_le_one]
  rw [hPS, ← Evol.one_add_smul_vsKernel hS ht]
  have hK := (Propagator.lemmaK_K1_single d.b_pos d.b_lt_half d.delta0_pos d.kappa_pos
    d.C0_ge_one d.D_ge_six hm hW hz hs0 hs1).1 a b
  have hu : P.ups s = polynomialControl (m * W) W d.D (vsHeight P.z s) := by
    unfold PsiData.ups
    rw [hPW, hPD]
  rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  refine (norm_add_le _ _).trans ?_
  have hK' : ‖(s : ℂ) * vsKernel (shortRingProfile d.b m W) (semicircleM P.z)
      (conj (semicircleM P.z)) s a b‖ ≤ Propagator.vsCK d * P.ups s a b := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0, hu]
    have hK0 := norm_nonneg (vsKernel (shortRingProfile d.b m W) (semicircleM P.z)
      (conj (semicircleM P.z)) s a b)
    calc s * ‖vsKernel (shortRingProfile d.b m W) (semicircleM P.z)
          (conj (semicircleM P.z)) s a b‖
        ≤ 1 * ‖vsKernel (shortRingProfile d.b m W) (semicircleM P.z)
          (conj (semicircleM P.z)) s a b‖ := mul_le_mul_of_nonneg_right hs1 hK0
      _ ≤ _ := by rw [one_mul]; exact hK
  refine add_le_add ?_ hK'
  split_ifs <;> simp

end BlockBand.Native.ErdosRiabov.QV
