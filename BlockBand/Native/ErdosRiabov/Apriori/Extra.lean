module

public import BlockBand.Native.ErdosRiabov.Discharge.MBound
public import BlockBand.Native.ErdosRiabov.Forcing.Contr

/-!
# The extra `M`-bound along the VS flow

The extra bound on deterministic `M`-chains with equal first and last spectral parameter
(the extra `M`-bound lemma of Erdős–Riabov).

* `isoBAt_of_mbIsoB`, `mbIsoB_of_isoBAt`: the bridge between `MBound.MBIsoB` (all times) and
  `Forcing.IsoBAt` (one time);
* `apr_chainM_recur` (`Split.chainTilde_eq`): `M_{[1,k+1]} =
  K[m_1 (A_1 M_{[2,k+1]} + t Σ_{i=2}^k 𝒮[M_{[1,i]}] M_{[i,k+1]})]`, `K = (1 - t m_1 m_{k+1} S)⁻¹`;
  `apr_chainM_seg`: the sub-chains are pattern `M`-terms;
* `apr_stab_colSum`: for `m_{k+1} = m_1`, `Σ_q |K_{qa}| ≤ c_7 = 1 + C_K C₁''/c_m`;
* `apr_sRowDiag`: `Σ_b S_{ab} s^iso_n(b,y,b) ≤ C_S s^iso_n(a,y,a)` (`n ≥ 2`);
* **`mbounds_extra`**: under `MBCtx d P`, `t ∈ [0,1]`, `k ≥ 2` and the isotropic bounds
  `IsoBAt P t n (I n)` for `1 ≤ n ≤ k`: `Forcing.ExtraBAt P t k (extraConst d I k)`, i.e. for
  patterns of length `k+1` with
  `σ_0 = σ_k`, `Σ_q |M_qq| ≤ E_k η⁻¹ ℓη s^av_k(w_0..w_{k-1})`,
  `E_k = c_7 C_S ((C₀+1) I_k + C_wc Σ_{i=2}^k I_i I_{k-i+2})`;
* `mbounds_extra_uncond`: the same bound with `I_n = mbConstI d Λ (mzeroConst d) n`
  (`Discharge.mbBounds_joint_uncond`; only `MBCtx`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Apriori

open Function Set
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Psi BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow BlockBand.Native.ErdosRiabov.Evol
open BlockBand.Native.ErdosRiabov.Propagator BlockBand.Native.ErdosRiabov.Contr
open BlockBand.Native.ErdosRiabov.MBound
open BlockBand.Native.ErdosRiabov.Forcing (IsoBAt ExtraBAt constS)
open BlockBand.Internal.Contracts.Inputs (shortRingProfile polynomialControl)
open scoped ComplexConjugate BigOperators Matrix

variable {N : ℕ}

/-!
## The bridge `MBIsoB` ↔ `IsoBAt`
-/

/-- The all-times bound `MBIsoB P n I` gives the one-time bound `IsoBAt P t n I` at every
`t ∈ [0,1]`. -/
theorem isoBAt_of_mbIsoB {P : PsiData N} {n : ℕ} {I : ℝ} (h : MBIsoB P n I) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : IsoBAt P t n I := fun σ x a =>
  (h t ht σ a x).trans (le_of_eq (by ring))

/-- The one-time bounds `IsoBAt P t n I` at every `t ∈ [0,1]` give the all-times bound
`MBIsoB P n I`. -/
theorem mbIsoB_of_isoBAt {P : PsiData N} {n : ℕ} {I : ℝ}
    (h : ∀ t ∈ Icc (0 : ℝ) 1, IsoBAt P t n I) : MBIsoB P n I := fun t ht σ a x =>
  (h t ht σ x a).trans (le_of_eq (by ring))

/-!
## The recursion
-/

theorem apr_prod_split (m : ℕ → ℂ) {k i : ℕ} (h1 : 1 < i) (h2 : i < k + 1) :
    (∏ j ∈ Finset.Icc 1 (k + 1), m j) * m i =
      (∏ j ∈ Finset.Icc 1 i, m j) * ∏ j ∈ Finset.Icc i (k + 1), m j := by
  have e1 : Finset.Icc 1 (k + 1) = Finset.Icc 1 i ∪ Finset.Ioc i (k + 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    constructor
    · intro h
      omega
    · intro h
      omega
  have e2 : Finset.Icc i (k + 1) = insert i (Finset.Ioc i (k + 1)) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]
    constructor
    · intro h
      omega
    · intro h
      omega
  have hd : Disjoint (Finset.Icc 1 i) (Finset.Ioc i (k + 1)) :=
    Finset.disjoint_left.mpr fun x hx hx' => by
      simp only [Finset.mem_Icc, Finset.mem_Ioc] at hx hx'
      omega
  have hn : i ∉ Finset.Ioc i (k + 1) := by simp
  rw [e1, Finset.prod_union hd, e2, Finset.prod_insert hn]
  ring

theorem apr_prod_head (m : ℕ → ℂ) (k : ℕ) :
    ∏ j ∈ Finset.Icc 1 (k + 1), m j = m 1 * ∏ j ∈ Finset.Icc 2 (k + 1), m j := by
  have e : Finset.Icc 1 (k + 1) = insert 1 (Finset.Icc 2 (k + 1)) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert]
    constructor
    · intro h
      omega
    · intro h
      omega
  rw [e, Finset.prod_insert (by simp)]

/-- **Recursion for `M`-chains** (`Split.chainTilde_eq` with `S` replaced by `tS`):
`M_{[1,k+1]} = K *ᵥ (m_1 • (A_1 M_{[2,k+1]} + Σ_{1<i<k+1} t • 𝒮[M_{[1,i]}] M_{[i,k+1]}))`,
`K = (1 - t m_1 m_{k+1} S)⁻¹` (`k ≥ 1`).
-/
theorem apr_chainM_recur (t : ℝ) (S : Matrix (Fin N) (Fin N) ℝ) (m : ℕ → ℂ)
    (A : ℕ → Fin N → ℂ) {k : ℕ} (hk : 1 ≤ k) :
    Split.chainM t S m A 1 (k + 1) = Split.stabOp t S (m 1 * m (k + 1)) *ᵥ
      (m 1 • (A 1 * Split.chainM t S m A 2 (k + 1) + ∑ i ∈ Finset.Ioo 1 (k + 1),
        (t : ℂ) • (Split.selfEnergy S (Split.chainM t S m A 1 i) *
          Split.chainM t S m A i (k + 1)))) := by
  unfold Split.chainM
  rw [Split.chainTilde_eq t S m A 1 (k + 1), ite_eq_left (by omega : 1 < k + 1),
    show (1 : ℕ) + 1 = 2 from rfl, ← Matrix.mulVec_smul]
  congr 1
  funext a
  simp only [Pi.smul_apply, Pi.add_apply, Pi.mul_apply, Finset.sum_apply, smul_eq_mul,
    Split.selfEnergy, Matrix.mulVec_smul]
  have hs : ∀ i ∈ Finset.Ioo 1 (k + 1), (∏ j ∈ Finset.Icc 1 (k + 1), m j) *
      (↑t * m 1 * m i * ((Split.profileC S *ᵥ Split.chainTilde t S m A 1 i) a *
        Split.chainTilde t S m A i (k + 1) a)) =
      m 1 * (↑t * ((∏ j ∈ Finset.Icc 1 i, m j) *
        (Split.profileC S *ᵥ Split.chainTilde t S m A 1 i) a *
          ((∏ j ∈ Finset.Icc i (k + 1), m j) * Split.chainTilde t S m A i (k + 1) a))) := by
    intro i hi
    have h := apr_prod_split m (Finset.mem_Ioo.mp hi).1 (Finset.mem_Ioo.mp hi).2
    linear_combination (↑t * m 1 * (Split.profileC S *ᵥ Split.chainTilde t S m A 1 i) a *
      Split.chainTilde t S m A i (k + 1) a) * h
  rw [mul_add, mul_add, Finset.mul_sum, Finset.mul_sum, Finset.sum_congr rfl hs,
    apr_prod_head m k]
  ring

/-- The sub-chains are pattern `M`-terms:
`M_{[s+1, s+n]}` of the pattern `σ` at the sites `w`
is `Psi.PsiData.mChain` of `(σ_s, …, σ_{s+n-1})` at `(w_s, …, w_{s+n-1})`.
-/
theorem apr_chainM_seg (P : PsiData N) {K : ℕ} (σ : Fin K → Bool) (w : Fin K → Fin N) (t : ℝ)
    {s n j l : ℕ} (hj : j = s + 1) (hl : l = s + n) (h : s + n ≤ K) :
    Split.chainM t P.S (patM P.z σ) (obsSeq P.S w) j l =
      P.mChain (fun r : Fin n => σ ⟨s + r, by have := r.isLt; omega⟩)
        (fun r : Fin n => w ⟨s + r, by have := r.isLt; omega⟩) t := by
  subst hj hl
  rw [PsiData.mChain]
  calc Split.chainM t P.S (patM P.z σ) (obsSeq P.S w) (s + 1) (s + n)
      = Split.chainM t P.S (patM P.z σ) (obsSeq P.S w) (1 + s) (n + s) := by
        rw [Nat.add_comm s 1, Nat.add_comm s n]
    _ = _ := mb_chainM_shift t P.S _ _ s 1 n
    _ = _ := ?_
  refine mb_chainM_congr t P.S (fun p hp1 hp2 => ?_) (fun p hp1 hp2 => ?_)
  · rw [mb_patM_apply _ _ (by omega) (by omega), mb_patM_apply _ _ hp1 hp2]
    congr 2
    apply Fin.ext
    simp only
    omega
  · rw [mb_obsSeq_apply _ _ (by omega) (by omega), mb_obsSeq_apply _ _ hp1 (by omega)]
    congr 2
    apply Fin.ext
    simp only
    omega

/-!
## Generic estimates
-/

/-- `Σ_q |(K *ᵥ x)_q| ≤ c Σ_a |x_a|` if every column sum of `|K|` is `≤ c`. -/
theorem apr_mulVec_sum_le (K : Matrix (Fin N) (Fin N) ℂ) (x : Fin N → ℂ) {c : ℝ}
    (hK : ∀ a, ∑ q, ‖K q a‖ ≤ c) : ∑ q, ‖(K *ᵥ x) q‖ ≤ c * ∑ a, ‖x a‖ := by
  calc ∑ q, ‖(K *ᵥ x) q‖ ≤ ∑ q, ∑ a, ‖K q a‖ * ‖x a‖ := Finset.sum_le_sum fun q _ => by
        simp only [Matrix.mulVec, dotProduct]
        exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun a _ => norm_mul _ _))
    _ = ∑ a, (∑ q, ‖K q a‖) * ‖x a‖ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => by rw [Finset.sum_mul]
    _ ≤ ∑ a, c * ‖x a‖ :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_right (hK a) (norm_nonneg _)
    _ = c * ∑ a, ‖x a‖ := by rw [Finset.mul_sum]

/-- `S`-row Schwarz with a general constant (`Σ_a S_{xa} Υ(a,y) ≤ C Υ(x,y)`). -/
theorem apr_sRowSchwarz (P : PsiData N) (t : ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hU : ∀ x y, 0 ≤ P.ups t x y) (hsym : ∀ x y, P.ups t x y = P.ups t y x)
    (hS : ∀ x y, 0 ≤ P.S x y) (hSU : ∀ x y, ∑ a, P.S x a * P.ups t a y ≤ C * P.ups t x y)
    (x u v : Fin N) :
    ∑ a, P.S x a * Real.sqrt (P.ups t u a * P.ups t a v) ≤
      C * Real.sqrt (P.ups t x u * P.ups t x v) := by
  have e : ∀ a, P.S x a * Real.sqrt (P.ups t u a * P.ups t a v) =
      Real.sqrt (P.S x a * P.ups t u a) * Real.sqrt (P.S x a * P.ups t a v) := by
    intro a
    rw [← Real.sqrt_mul (mul_nonneg (hS _ _) (hU _ _)),
      show P.S x a * P.ups t u a * (P.S x a * P.ups t a v) =
        P.S x a ^ 2 * (P.ups t u a * P.ups t a v) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (hS _ _)]
  simp_rw [e]
  refine (Real.sum_mul_le_sqrt_mul_sqrt _ _ _).trans ?_
  have h1 : ∑ a, Real.sqrt (P.S x a * P.ups t u a) ^ 2 ≤ C * P.ups t x u := by
    simp_rw [Real.sq_sqrt (mul_nonneg (hS _ _) (hU _ _))]
    calc ∑ a, P.S x a * P.ups t u a = ∑ a, P.S x a * P.ups t a u :=
          Finset.sum_congr rfl fun a _ => by rw [hsym u a]
      _ ≤ _ := hSU x u
  have h2 : ∑ a, Real.sqrt (P.S x a * P.ups t a v) ^ 2 ≤ C * P.ups t x v := by
    simp_rw [Real.sq_sqrt (mul_nonneg (hS _ _) (hU _ _))]
    exact hSU x v
  calc Real.sqrt (∑ a, Real.sqrt (P.S x a * P.ups t u a) ^ 2) *
        Real.sqrt (∑ a, Real.sqrt (P.S x a * P.ups t a v) ^ 2)
      ≤ Real.sqrt (C * P.ups t x u) * Real.sqrt (C * P.ups t x v) :=
        mul_le_mul (Real.sqrt_le_sqrt h1) (Real.sqrt_le_sqrt h2) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
    _ = C * Real.sqrt (P.ups t x u * P.ups t x v) := by
        rw [Real.sqrt_mul hC, Real.sqrt_mul hC, Real.sqrt_mul (hU _ _),
          show Real.sqrt C * Real.sqrt (P.ups t x u) * (Real.sqrt C * Real.sqrt (P.ups t x v)) =
            (Real.sqrt C * Real.sqrt C) * (Real.sqrt (P.ups t x u) * Real.sqrt (P.ups t x v))
            by ring,
          Real.mul_self_sqrt hC]

/-- The `S`-row bound with a general constant: `Σ_b S_{xb} s^iso_n(b,u,b) ≤ C s^iso_n(x,u,x)`
(`n = m+2`). -/
theorem apr_sRowDiag_gen (P : PsiData N) (t : ℝ) {C : ℝ} (hC : 0 ≤ C) (hL : 0 < P.lEta t)
    (hU : ∀ x y, 0 ≤ P.ups t x y) (hsym : ∀ x y, P.ups t x y = P.ups t y x)
    (hS : ∀ x y, 0 ≤ P.S x y) (hSU : ∀ x y, ∑ a, P.S x a * P.ups t a y ≤ C * P.ups t x y)
    {m : ℕ} (x : Fin N) (u : Fin (m + 1 + 1) → Fin N) :
    ∑ b, P.S x b * P.sIso b b u t ≤ C * P.sIso x x u t := by
  have hM : 0 ≤ contrPathProd (P.ups t) (fun n => isoPoint x x u (n + 1)) m :=
    contrPathProd_nonneg hU _ _
  have he : 0 ≤ P.lEta t ^ (-(((m + 1 + 1 : ℕ) : ℝ) - 1) / 2) := Real.rpow_nonneg hL.le _
  have hb : ∀ b, P.S x b * P.sIso b b u t =
      P.lEta t ^ (-(((m + 1 + 1 : ℕ) : ℝ) - 1) / 2) *
        Real.sqrt (contrPathProd (P.ups t) (fun n => isoPoint x x u (n + 1)) m) *
        (P.S x b * Real.sqrt (P.ups t (u ⟨m, by omega⟩) b * P.ups t b (u ⟨0, by omega⟩))) := by
    intro b
    rw [Forcing.sIso_split P t b b u, Forcing.pathProd_indep P t b b x x u,
      show P.ups t b (u ⟨0, by omega⟩) *
          (contrPathProd (P.ups t) (fun n => isoPoint x x u (n + 1)) m *
            P.ups t (u ⟨m, by omega⟩) b) =
        contrPathProd (P.ups t) (fun n => isoPoint x x u (n + 1)) m *
          (P.ups t (u ⟨m, by omega⟩) b * P.ups t b (u ⟨0, by omega⟩)) by ring,
      Real.sqrt_mul hM]
    ring
  have hx : P.sIso x x u t = P.lEta t ^ (-(((m + 1 + 1 : ℕ) : ℝ) - 1) / 2) *
      Real.sqrt (contrPathProd (P.ups t) (fun n => isoPoint x x u (n + 1)) m) *
      Real.sqrt (P.ups t x (u ⟨m, by omega⟩) * P.ups t x (u ⟨0, by omega⟩)) := by
    rw [Forcing.sIso_split P t x x u, hsym (u ⟨m, by omega⟩) x,
      show P.ups t x (u ⟨0, by omega⟩) *
          (contrPathProd (P.ups t) (fun n => isoPoint x x u (n + 1)) m *
            P.ups t x (u ⟨m, by omega⟩)) =
        contrPathProd (P.ups t) (fun n => isoPoint x x u (n + 1)) m *
          (P.ups t x (u ⟨m, by omega⟩) * P.ups t x (u ⟨0, by omega⟩)) by ring,
      Real.sqrt_mul hM]
    ring
  rw [Finset.sum_congr rfl fun b _ => hb b, ← Finset.mul_sum, hx]
  calc P.lEta t ^ (-(((m + 1 + 1 : ℕ) : ℝ) - 1) / 2) *
        Real.sqrt (contrPathProd (P.ups t) (fun n => isoPoint x x u (n + 1)) m) *
        ∑ b, P.S x b * Real.sqrt (P.ups t (u ⟨m, by omega⟩) b * P.ups t b (u ⟨0, by omega⟩))
      ≤ P.lEta t ^ (-(((m + 1 + 1 : ℕ) : ℝ) - 1) / 2) *
        Real.sqrt (contrPathProd (P.ups t) (fun n => isoPoint x x u (n + 1)) m) *
        (C * Real.sqrt (P.ups t x (u ⟨m, by omega⟩) * P.ups t x (u ⟨0, by omega⟩))) :=
        mul_le_mul_of_nonneg_left
          (apr_sRowSchwarz P t hC hU hsym hS hSU x (u ⟨m, by omega⟩) (u ⟨0, by omega⟩))
          (mul_nonneg he (Real.sqrt_nonneg _))
    _ = _ := by ring

/-!
## The VS inputs
-/

/-- `c_7 = 1 + C_K C₁''/c_m`, the row-sum constant of `1 + tΞ̂_t`. -/
def aprC7 (d : VSData) : ℝ := 1 + vsCK d * d.C1pp / d.cm

/-- `E_k = c_7 C_S ((C₀+1) I_k + C_wc Σ_{i=2}^k I_i I_{k-i+2})` -/
def extraConst (d : VSData) (I : ℕ → ℝ) (k : ℕ) : ℝ :=
  aprC7 d * constS d *
    ((d.C0 + 1) * I k + d.Cwc * ∑ i ∈ Finset.Ioo 1 (k + 1), I i * I (k - i + 2))

section VS

variable {d : VSData} {m W : ℕ} {P : PsiData (m * W)} (hc : MBCtx d P)

include hc in
theorem apr_ups_pos {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (x y : Fin (m * W)) : 0 < P.ups t x y := by
  have hN : 0 < m * W := Nat.mul_pos (by have := hc.hm; omega) hc.hW
  unfold PsiData.ups
  rw [hc.hPW, hc.hPD]
  exact BlockBand.Adapters.ErdosRiabov.polynomialControl_pos hN hc.hW _
    (hc.inputs ht).height_pos x y

include hc in
/-- `Σ_a S_{xa} Υ_t(a,y) ≤ C_S Υ_t(x,y)`. -/
theorem apr_sUps {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (x y : Fin (m * W)) :
    ∑ a, P.S x a * P.ups t a y ≤ constS d * P.ups t x y := by
  have hin := hc.inputs ht
  have hD0 : 0 ≤ d.D := by linarith [d.D_ge_six]
  have hu : P.ups t = polynomialControl (m * W) W d.D (vsHeight P.z t) := by
    unfold PsiData.ups
    rw [hc.hPW, hc.hPD]
  have h := (LemmaK.lemmaK_K4_explicit d.b_pos d.b_lt_half hc.hm hc.hW d.C0_ge_one hD0
    hin.height_pos hin.height_le x y).2
  rw [Matrix.mul_apply] at h
  rw [hc.hPS, hu]
  exact h

theorem constS_nonneg (d : VSData) : 0 ≤ constS d := by
  unfold constS
  positivity

include hc in
/-- **`S`-row bound**: `Σ_b S_{xb} s^iso_n(b,u,b) ≤ C_S s^iso_n(x,u,x)` for `n ≥ 2`. -/
theorem apr_sRowDiag {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {n : ℕ} (hn : 2 ≤ n) (x : Fin (m * W))
    (u : Fin n → Fin (m * W)) :
    ∑ b, P.S x b * P.sIso b b u t ≤ constS d * P.sIso x x u t := by
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 + 1 := ⟨n - 2, by omega⟩
  have hin := hc.inputs ht
  exact apr_sRowDiag_gen P t (constS_nonneg d) hin.lEta_pos hin.nonneg hin.symm
    hc.stoch.nonneg (apr_sUps hc ht) x u

include hc in
theorem apr_sIso_pos {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {n : ℕ} (a b : Fin (m * W))
    (x : Fin n → Fin (m * W)) : 0 < P.sIso a b x t := by
  unfold PsiData.sIso
  refine mul_pos (Real.rpow_pos_of_pos (hc.inputs ht).lEta_pos _) (Real.sqrt_pos.mpr ?_)
  exact Finset.prod_pos fun i _ => apr_ups_pos hc ht _ _

include hc in
/-- An isotropic bound `IsoBAt P t n I` forces `I ≥ 0`. -/
theorem apr_isoB_nonneg {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {n : ℕ} {I : ℝ}
    (h : IsoBAt P t n I) : 0 ≤ I := by
  have hN : 0 < m * W := Nat.mul_pos (by have := hc.hm; omega) hc.hW
  obtain ⟨a0⟩ : Nonempty (Fin (m * W)) := ⟨⟨0, hN⟩⟩
  have h1 := h (fun _ => false) (fun _ => a0) a0
  have hpos : 0 < Real.sqrt (P.lEta t) * P.sIso a0 a0 (fun _ : Fin n => a0) t :=
    mul_pos (Real.sqrt_pos.mpr (hc.inputs ht).lEta_pos) (apr_sIso_pos hc ht _ _ _)
  by_contra hneg
  have hneg := not_le.mp hneg
  have := mul_neg_of_neg_of_pos hneg hpos
  have := norm_nonneg (P.mChain (fun _ : Fin n => false) (fun _ => a0) t a0)
  linarith

include hc in

/-- For `m_{k+1} = m_1`, the column sums of `|K|`, `K = (1 - t m_1² S)⁻¹`, are at most
`c_7 = aprC7 d` (from `Evol.one_add_smul_vsKernel`). -/
theorem apr_stab_colSum {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (b : Bool) (a : Fin (m * W)) :
    ∑ q, ‖Split.stabOp t P.S (VS.patConj b (semicircleM P.z) * VS.patConj b (semicircleM P.z))
      q a‖ ≤ aprC7 d := by
  have hm := mb_norm_m_lt hc.zpos
  have hmm : ‖(t : ℂ) * (semicircleM P.z * semicircleM P.z)‖ < 1 :=
    norm_smul_lt_one hm hm ht.1 ht.2
  have K7 := (lemmaK_K7_single d.b_pos d.b_lt_half d.delta0_pos d.kappa_pos d.C0_ge_one
    d.D_ge_six hc.hm hc.hW hc.hz ht.1 le_rfl ht.2 a).2.1
  rw [← hc.hPS] at K7
  have hK7 : ∑ x, ‖(1 + (t : ℂ) • vsKernel P.S (semicircleM P.z) (semicircleM P.z) t) a x‖ ≤
      aprC7 d := K7
  have hμ : ‖VS.patConj b (semicircleM P.z)‖ < 1 := by rw [norm_patConj]; exact hm
  have hn : ‖(t : ℂ) * (VS.patConj b (semicircleM P.z) * VS.patConj b (semicircleM P.z))‖ < 1 :=
    norm_smul_lt_one hμ hμ ht.1 ht.2
  rw [← one_add_smul_vsKernel hc.stoch hn]
  have hsym : ∀ q, (1 + (t : ℂ) • vsKernel P.S (VS.patConj b (semicircleM P.z))
      (VS.patConj b (semicircleM P.z)) t) q a = (1 + (t : ℂ) • vsKernel P.S
        (VS.patConj b (semicircleM P.z)) (VS.patConj b (semicircleM P.z)) t) a q := by
    intro q
    rw [Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
      vsKernel_symm hc.stoch hn q a]
    congr 1
    by_cases h : q = a
    · subst h
      rfl
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]
  rw [Finset.sum_congr rfl fun q _ => by rw [hsym q]]
  cases b
  · exact hK7
  · refine le_of_eq_of_le (Finset.sum_congr rfl fun q _ => ?_) hK7
    show ‖(1 + (t : ℂ) • vsKernel P.S (conj (semicircleM P.z)) (conj (semicircleM P.z)) t) a q‖ =
      ‖(1 + (t : ℂ) • vsKernel P.S (semicircleM P.z) (semicircleM P.z) t) a q‖
    rw [Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply,
      LemmaK.lemmaK_vsKernel_conj hc.stoch hmm a q, ← Complex.norm_conj]
    congr 1
    rw [map_add, smul_eq_mul, smul_eq_mul, map_mul, Complex.conj_ofReal, Complex.conj_conj]
    congr 1
    by_cases h : a = q
    · subst h
      simp
    · simp [Matrix.one_apply_ne h]

/-!
## The two terms
-/

include hc in

/-- The first term:
`Σ_a |A_1(a)| |M_{[2,k+1]}(a)| ≤ C_S (C₀+1)/η · I_k · L s^av_k(w')`.
-/
theorem apr_first_term {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {k : ℕ} (hk : 2 ≤ k)
    (σ : Fin (k + 1) → Bool) (w : Fin (k + 1) → Fin (m * W)) {Ik : ℝ} (hIk0 : 0 ≤ Ik)
    (hIk : IsoBAt P t k Ik) :
    ∑ a, ‖obsSeq P.S w 1 a * Split.chainM t P.S (patM P.z σ) (obsSeq P.S w) 2 (k + 1) a‖ ≤
      constS d * (d.C0 + 1) / vsHeight P.z t * Ik *
        (P.lEta t * P.sAv (fun j : Fin k => w j.castSucc) t) := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
  have hin := hc.inputs ht
  have hL := hin.lEta_pos
  have hη := hin.height_pos
  have hCS := constS_nonneg d
  have hseg := apr_chainM_seg P σ w t (s := 1) (n := k + 2) (j := 2) (l := k + 2 + 1) rfl
    (by ring) (by omega)
  set wT : Fin (k + 2) → Fin (m * W) := fun r => w ⟨1 + r, by have := r.isLt; omega⟩
  have hA1 : ∀ a, ‖obsSeq P.S w 1 a‖ = P.S (w ⟨0, by omega⟩) a := by
    intro a
    rw [mb_obsSeq_apply _ _ le_rfl (by omega)]
    simp only [Split.rowObs, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (hc.stoch.nonneg _ _)
  have hrow := apr_sRowDiag hc ht (n := k + 2) (by omega) (w ⟨0, by omega⟩) wT
  have hdiag := mb_LsAv_update_last P t hL (n := k) wT (w ⟨0, by omega⟩)
  have hrot : update wT (Fin.last (k + 1)) (w ⟨0, by omega⟩) =
      mbRotTo (0 : Fin (k + 2)) (fun j : Fin (k + 2) => w j.castSucc) := by
    funext u
    rw [mbRotTo_val]
    by_cases hu : u = Fin.last (k + 1)
    · subst hu
      rw [update_self]
      congr 1
      apply Fin.ext
      show 0 = ((k + 1 + ((0 : Fin (k + 2)) + 1)) % (k + 2) : ℕ)
      rw [Fin.val_zero, show k + 1 + (0 + 1) = k + 2 by ring, Nat.mod_self]
    · rw [update_of_ne hu]
      have hu' : (u : ℕ) < k + 1 := by
        have := u.isLt
        have : (u : ℕ) ≠ k + 1 := fun h => hu (Fin.ext h)
        omega
      show w _ = w _
      congr 1
      apply Fin.ext
      show 1 + (u : ℕ) = ((u : ℕ) + ((0 : Fin (k + 2)) + 1)) % (k + 2)
      rw [Fin.val_zero, Nat.mod_eq_of_lt (by omega)]
      ring
  rw [hrot, mb_sAv_rotTo] at hdiag
  have h1le : 1 ≤ (d.C0 + 1) / vsHeight P.z t := (one_le_div hη).mpr hin.height_le
  calc ∑ a, ‖obsSeq P.S w 1 a * Split.chainM t P.S (patM P.z σ) (obsSeq P.S w) 2 (k + 2 + 1) a‖
      ≤ ∑ a, P.S (w ⟨0, by omega⟩) a * (Ik * Real.sqrt (P.lEta t) * P.sIso a a wT t) := by
        refine Finset.sum_le_sum fun a _ => ?_
        rw [norm_mul, hA1, hseg]
        exact mul_le_mul_of_nonneg_left (hIk _ _ a) (hc.stoch.nonneg _ _)
    _ = Ik * Real.sqrt (P.lEta t) * ∑ a, P.S (w ⟨0, by omega⟩) a * P.sIso a a wT t := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring
    _ ≤ Ik * Real.sqrt (P.lEta t) * (constS d * P.sIso (w ⟨0, by omega⟩) (w ⟨0, by omega⟩) wT t) :=
        mul_le_mul_of_nonneg_left hrow (mul_nonneg hIk0 (Real.sqrt_nonneg _))
    _ = constS d * Ik * (P.lEta t * P.sAv (fun j : Fin (k + 2) => w j.castSucc) t) := by
        rw [hdiag]
        ring
    _ ≤ _ := by
        have h0 : 0 ≤ constS d * Ik * (P.lEta t * P.sAv (fun j : Fin (k + 2) => w j.castSucc) t) :=
          mul_nonneg (mul_nonneg hCS hIk0) (mb_LsAv_pos_nonneg hc ht _)
        calc constS d * Ik * (P.lEta t * P.sAv (fun j : Fin (k + 2) => w j.castSucc) t)
            ≤ (d.C0 + 1) / vsHeight P.z t *
                (constS d * Ik * (P.lEta t * P.sAv (fun j : Fin (k + 2) => w j.castSucc) t)) :=
              le_mul_of_one_le_left h0 h1le
          _ = _ := by ring

include hc in

/-- The pair `i = r+2 ∈ [2, k]`:
`Σ_a |𝒮[M_{[1,i]}](a)| |M_{[i,k+1]}(a)| ≤
C_S C_wc/η · I_i I_{k-i+2} · L s^av_k(w')`.
-/
theorem apr_pair_term {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {k r : ℕ} (hr : r + 2 ≤ k)
    (σ : Fin (k + 1) → Bool) (w : Fin (k + 1) → Fin (m * W)) {I₁ I₂ : ℝ} (hI₁0 : 0 ≤ I₁)
    (hI₂0 : 0 ≤ I₂) (hI₁ : IsoBAt P t (r + 2) I₁) (hI₂ : IsoBAt P t (k - r - 1 + 1) I₂) :
    ∑ a, ‖Split.selfEnergy P.S (Split.chainM t P.S (patM P.z σ) (obsSeq P.S w) 1 (r + 2)) a‖ *
        ‖Split.chainM t P.S (patM P.z σ) (obsSeq P.S w) (r + 2) (k + 1) a‖ ≤
      constS d * d.Cwc / vsHeight P.z t * (I₁ * I₂) *
        (P.lEta t * P.sAv (fun j : Fin k => w j.castSucc) t) := by
  have hin := hc.inputs ht
  have hL := hin.lEta_pos
  have hCS := constS_nonneg d
  have hseg1 := apr_chainM_seg P σ w t (s := 0) (n := r + 2) (j := 1) (l := r + 2) rfl
    (by ring) (by omega)
  have hseg2 := apr_chainM_seg P σ w t (s := r + 1) (n := k - r - 1 + 1) (j := r + 2)
    (l := k + 1) (by ring) (by omega) (by omega)
  set wH : Fin (r + 2) → Fin (m * W) := fun u => w ⟨0 + u, by have := u.isLt; omega⟩
  set wR : Fin (k - r - 1 + 1) → Fin (m * W) :=
    fun u => w ⟨r + 1 + u, by have := u.isLt; omega⟩
  have hw : r + 1 + (k - r - 1) = k := by omega
  set wv : Fin (r + 1 + (k - r - 1)) → Fin (m * W) :=
    fun u => (fun j : Fin k => w j.castSucc) (Fin.cast hw u)
  have hSe : ∀ a, ‖Split.selfEnergy P.S
      (Split.chainM t P.S (patM P.z σ) (obsSeq P.S w) 1 (r + 2)) a‖ ≤
      constS d * I₁ * Real.sqrt (P.lEta t) * P.sIso a a wH t := by
    intro a
    have e : Split.selfEnergy P.S (Split.chainM t P.S (patM P.z σ) (obsSeq P.S w) 1 (r + 2)) a =
        ∑ b, (P.S a b : ℂ) * Split.chainM t P.S (patM P.z σ) (obsSeq P.S w) 1 (r + 2) b := by
      simp only [Split.selfEnergy, Matrix.mulVec, dotProduct, Split.profileC, Matrix.map_apply]
    rw [e]
    calc _ ≤ ∑ b, P.S a b * (I₁ * Real.sqrt (P.lEta t) * P.sIso b b wH t) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc.stoch.nonneg _ _),
            hseg1]
          exact mul_le_mul_of_nonneg_left (hI₁ _ _ b) (hc.stoch.nonneg _ _)
      _ = I₁ * Real.sqrt (P.lEta t) * ∑ b, P.S a b * P.sIso b b wH t := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun b _ => by ring
      _ ≤ I₁ * Real.sqrt (P.lEta t) * (constS d * P.sIso a a wH t) :=
          mul_le_mul_of_nonneg_left (apr_sRowDiag hc ht (by omega) a wH)
            (mul_nonneg hI₁0 (Real.sqrt_nonneg _))
      _ = _ := by ring
  have hM2 : ∀ a, ‖Split.chainM t P.S (patM P.z σ) (obsSeq P.S w) (r + 2) (k + 1) a‖ ≤
      I₂ * Real.sqrt (P.lEta t) * P.sIso a a wR t := fun a => by
    rw [hseg2]
    exact hI₂ _ _ a
  have hdiag : ∀ a, Real.sqrt (P.lEta t) * P.sIso a a wH t =
      P.lEta t * P.sAv (update wH (Fin.last (r + 1)) a) t := fun a =>
    (mb_LsAv_update_last P t hL (n := r) wH a).symm
  have hins := avInsertion_of P t hin.nonneg hL (K := d.Cwc / vsHeight P.z t) hin.schwarz
    (i := r + 1) (j := k - r - 1) (by omega) (by omega)
    (fun a => update wH (Fin.last (r + 1)) a) wR wv (fun q => update_self _ _ _)
    (fun q n hn => by
      rw [update_of_ne (by simp [Fin.ext_iff]; omega)]
      show w _ = w _
      congr 1
      apply Fin.ext
      show 0 + n = n
      omega)
    (fun n hn => by
      show w _ = w _
      congr 1)
  have hwv : P.sAv wv t = P.sAv (fun j : Fin k => w j.castSucc) t :=
    mb_sAv_cast P hw (fun j : Fin k => w j.castSucc) t
  rw [hwv] at hins
  have hpw : Real.sqrt (P.lEta t) * P.lEta t ^ (-(1 / 2 : ℝ)) = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hL]
    norm_num
  calc _ ≤ ∑ a, (constS d * I₁ * Real.sqrt (P.lEta t) * P.sIso a a wH t) *
          (I₂ * Real.sqrt (P.lEta t) * P.sIso a a wR t) :=
        Finset.sum_le_sum fun a _ => mul_le_mul (hSe a) (hM2 a) (norm_nonneg _)
          (mul_nonneg (mul_nonneg (mul_nonneg hCS hI₁0) (Real.sqrt_nonneg _))
            (apr_sIso_pos hc ht _ _ _).le)
    _ = constS d * I₁ * I₂ * P.lEta t * Real.sqrt (P.lEta t) *
          ∑ a, P.sAv (update wH (Fin.last (r + 1)) a) t * P.sIso a a wR t := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        have h := hdiag a
        calc constS d * I₁ * Real.sqrt (P.lEta t) * P.sIso a a wH t *
              (I₂ * Real.sqrt (P.lEta t) * P.sIso a a wR t)
            = constS d * I₁ * I₂ * Real.sqrt (P.lEta t) * P.sIso a a wR t *
                (Real.sqrt (P.lEta t) * P.sIso a a wH t) := by ring
          _ = _ := by rw [h]; ring
    _ ≤ constS d * I₁ * I₂ * P.lEta t * Real.sqrt (P.lEta t) *
          (d.Cwc / vsHeight P.z t * P.lEta t ^ (-(1 / 2 : ℝ)) *
            P.sAv (fun j : Fin k => w j.castSucc) t) :=
        mul_le_mul_of_nonneg_left hins (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCS hI₁0)
          hI₂0) hL.le) (Real.sqrt_nonneg _))
    _ = constS d * d.Cwc / vsHeight P.z t * (I₁ * I₂) *
          (P.lEta t * P.sAv (fun j : Fin k => w j.castSucc) t) *
            (Real.sqrt (P.lEta t) * P.lEta t ^ (-(1 / 2 : ℝ))) := by ring
    _ = _ := by rw [hpw, mul_one]

/-!
## The extra `M`-bound
-/

include hc in

/-- **The extra `M`-bound**: under `MBCtx d P`, `0 ≤ t ≤ 1`, `k ≥ 2` and the isotropic bounds
`IsoBAt P t n (I n)`
for `1 ≤ n ≤ k`:
`Forcing.ExtraBAt P t k (extraConst d I k)`, i.e. for every pattern `σ` of
length `k+1` with `σ_0 = σ_k` and all sites `w`,
`Σ_q |(M^σ_t(w))_qq| ≤ E_k η_t⁻¹ ℓ_tη_t s^av_{k,t}(w_0, …, w_{k-1})`.
Deterministic.
-/
theorem mbounds_extra {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {k : ℕ} (hk : 2 ≤ k) (I : ℕ → ℝ)
    (hI : ∀ n, 1 ≤ n → n ≤ k → IsoBAt P t n (I n)) : ExtraBAt P t k (extraConst d I k) := by
  intro σ hσ w
  have ht : t ∈ Icc (0 : ℝ) 1 := ⟨ht0, ht1⟩
  have hin := hc.inputs ht
  have hL := hin.lEta_pos
  have hη := hin.height_pos
  have hCS := constS_nonneg d
  have hCwc := d.one_le_Cwc
  have hC0 := d.C0_ge_one
  have hI0 : ∀ n, 1 ≤ n → n ≤ k → 0 ≤ I n := fun n h1 h2 => apr_isoB_nonneg hc ht (hI n h1 h2)
  have hX : 0 ≤ P.lEta t * P.sAv (fun j : Fin k => w j.castSucc) t := mb_LsAv_pos_nonneg hc ht _
  -- the pattern values
  have hm1 : patM P.z σ 1 = VS.patConj (σ ⟨0, by omega⟩) (semicircleM P.z) :=
    patM_of_mem P.z σ ⟨0, by omega⟩
  have hmk : patM P.z σ (k + 1) = patM P.z σ 1 := by
    have h1 : patM P.z σ (k + 1) = VS.patConj (σ (Fin.last k)) (semicircleM P.z) :=
      patM_of_mem P.z σ (Fin.last k)
    have h0 : (⟨0, by omega⟩ : Fin (k + 1)) = 0 := Fin.ext (by simp)
    rw [h1, hm1, h0, hσ]
  have hrec := apr_chainM_recur t P.S (patM P.z σ) (obsSeq P.S w) (k := k) (by omega)
  rw [hmk] at hrec
  set u : Fin (m * W) → ℂ := obsSeq P.S w 1 * Split.chainM t P.S (patM P.z σ) (obsSeq P.S w) 2
    (k + 1) + ∑ i ∈ Finset.Ioo 1 (k + 1), (t : ℂ) • (Split.selfEnergy P.S
      (Split.chainM t P.S (patM P.z σ) (obsSeq P.S w) 1 i) *
        Split.chainM t P.S (patM P.z σ) (obsSeq P.S w) i (k + 1)) with hu
  have hstab : ∀ a, ∑ q, ‖Split.stabOp t P.S (patM P.z σ 1 * patM P.z σ 1) q a‖ ≤ aprC7 d := by
    intro a
    rw [hm1]
    exact apr_stab_colSum hc ht _ a
  have hstep1 : ∑ q, ‖P.mChain σ w t q‖ ≤ aprC7 d * ∑ a, ‖u a‖ := by
    have e : P.mChain σ w t = Split.stabOp t P.S (patM P.z σ 1 * patM P.z σ 1) *ᵥ
        (patM P.z σ 1 • u) := hrec
    rw [e]
    refine (apr_mulVec_sum_le _ _ hstab).trans (mul_le_mul_of_nonneg_left ?_ (by
      unfold aprC7
      have := (vsCK_pos d).le
      have := d.one_le_C1pp
      have := d.cm_pos
      positivity))
    refine Finset.sum_le_sum fun a _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, norm_mul]
    have : ‖patM P.z σ 1‖ ≤ 1 := (norm_patM_lt_one hc.zpos.ne' σ 1).le
    nlinarith [norm_nonneg (u a), norm_nonneg (patM P.z σ 1)]
  -- the sum over `a`
  have hua : ∀ a, ‖u a‖ ≤ ‖obsSeq P.S w 1 a *
      Split.chainM t P.S (patM P.z σ) (obsSeq P.S w) 2 (k + 1) a‖ +
      ∑ i ∈ Finset.Ioo 1 (k + 1), t * (‖Split.selfEnergy P.S
        (Split.chainM t P.S (patM P.z σ) (obsSeq P.S w) 1 i) a‖ *
          ‖Split.chainM t P.S (patM P.z σ) (obsSeq P.S w) i (k + 1) a‖) := by
    intro a
    rw [hu]
    simp only [Pi.add_apply, Pi.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine (norm_add_le _ _).trans (add_le_add le_rfl ((norm_sum_le _ _).trans
      (Finset.sum_le_sum fun i _ => ?_)))
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
  have hstep2 : ∑ a, ‖u a‖ ≤ ∑ a, ‖obsSeq P.S w 1 a *
      Split.chainM t P.S (patM P.z σ) (obsSeq P.S w) 2 (k + 1) a‖ +
      ∑ i ∈ Finset.Ioo 1 (k + 1), t * ∑ a, ‖Split.selfEnergy P.S
        (Split.chainM t P.S (patM P.z σ) (obsSeq P.S w) 1 i) a‖ *
          ‖Split.chainM t P.S (patM P.z σ) (obsSeq P.S w) i (k + 1) a‖ := by
    refine (Finset.sum_le_sum fun a _ => hua a).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, Finset.sum_comm]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
  -- the two bounds
  have hF := apr_first_term hc ht hk σ w (hI0 k (by omega) le_rfl) (hI k (by omega) le_rfl)
  have hP : ∑ i ∈ Finset.Ioo 1 (k + 1), t * ∑ a, ‖Split.selfEnergy P.S
        (Split.chainM t P.S (patM P.z σ) (obsSeq P.S w) 1 i) a‖ *
          ‖Split.chainM t P.S (patM P.z σ) (obsSeq P.S w) i (k + 1) a‖ ≤
      ∑ i ∈ Finset.Ioo 1 (k + 1), constS d * d.Cwc / vsHeight P.z t * (I i * I (k - i + 2)) *
        (P.lEta t * P.sAv (fun j : Fin k => w j.castSucc) t) := by
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' := Finset.mem_Ioo.mp hi
    obtain ⟨r, rfl⟩ : ∃ r, i = r + 2 := ⟨i - 2, by omega⟩
    have hIe : I (k - r - 1 + 1) = I (k - (r + 2) + 2) := congrArg I (by omega)
    have h := apr_pair_term hc ht (k := k) (r := r) (by omega) σ w (hI0 _ (by omega) (by omega))
      (hI0 _ (by omega) (by omega)) (hI (r + 2) (by omega) (by omega))
      (hI (k - r - 1 + 1) (by omega) (by omega))
    rw [hIe] at h
    have h0 : 0 ≤ ∑ a, ‖Split.selfEnergy P.S
        (Split.chainM t P.S (patM P.z σ) (obsSeq P.S w) 1 (r + 2)) a‖ *
          ‖Split.chainM t P.S (patM P.z σ) (obsSeq P.S w) (r + 2) (k + 1) a‖ :=
      Finset.sum_nonneg fun a _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    calc _ ≤ 1 * ∑ a, ‖Split.selfEnergy P.S
          (Split.chainM t P.S (patM P.z σ) (obsSeq P.S w) 1 (r + 2)) a‖ *
            ‖Split.chainM t P.S (patM P.z σ) (obsSeq P.S w) (r + 2) (k + 1) a‖ :=
          mul_le_mul_of_nonneg_right ht1 h0
      _ ≤ _ := by rw [one_mul]; exact h
  have hc7 : 0 ≤ aprC7 d := by
    unfold aprC7
    have := (vsCK_pos d).le
    have := d.one_le_C1pp
    have := d.cm_pos
    positivity
  have hsum : ∑ i ∈ Finset.Ioo 1 (k + 1), constS d * d.Cwc / vsHeight P.z t *
      (I i * I (k - i + 2)) * (P.lEta t * P.sAv (fun j : Fin k => w j.castSucc) t) =
      constS d * d.Cwc / vsHeight P.z t * (P.lEta t * P.sAv (fun j : Fin k => w j.castSucc) t) *
        ∑ i ∈ Finset.Ioo 1 (k + 1), I i * I (k - i + 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  calc ∑ q, ‖P.mChain σ w t q‖ ≤ aprC7 d * ∑ a, ‖u a‖ := hstep1
    _ ≤ aprC7 d * (constS d * (d.C0 + 1) / vsHeight P.z t * I k *
          (P.lEta t * P.sAv (fun j : Fin k => w j.castSucc) t) +
        ∑ i ∈ Finset.Ioo 1 (k + 1), constS d * d.Cwc / vsHeight P.z t * (I i * I (k - i + 2)) *
          (P.lEta t * P.sAv (fun j : Fin k => w j.castSucc) t)) :=
        mul_le_mul_of_nonneg_left (hstep2.trans (add_le_add hF hP)) hc7
    _ = _ := by
        rw [hsum]
        unfold extraConst
        ring

include hc in

/-- **The extra `M`-bound with explicit constants**: with `I_n = mbConstI d Λ (mzeroConst d) n`
(`Discharge.mbBounds_joint_uncond`), for `t ∈ [0,1]` and `k ≥ 2`:
`Forcing.ExtraBAt P t k (extraConst d (mbConstI d Λ (mzeroConst d)) k)`, `Λ = mbLambda d (m W)`.
Only hypothesis: `MBCtx d P`.
-/
theorem mbounds_extra_uncond {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {k : ℕ} (hk : 2 ≤ k) :
    ExtraBAt P t k (extraConst d (mbConstI d (mbLambda d (m * W)) (MZero.mzeroConst d)) k) :=
  mbounds_extra hc ht0 ht1 hk _ fun n h1 _ =>
    isoBAt_of_mbIsoB (Discharge.mbBounds_joint_uncond hc n h1).2 ⟨ht0, ht1⟩

end VS

/-!
## The log-power form
-/

/-- `e_i + e_{k-i+2} ≤ e_k` for `2 ≤ i ≤ k` (`e_k = 2^k − 4`, `MBound.mbPowExp`). -/
theorem mbPowExp_add_le {i k : ℕ} (hi : 2 ≤ i) (hik : i ≤ k) :
    mbPowExp i + mbPowExp (k - i + 2) ≤ mbPowExp k := by
  unfold mbPowExp
  obtain ⟨a, rfl⟩ : ∃ a, i = a + 2 := ⟨i - 2, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, k = a + 2 + b := ⟨k - (a + 2), by omega⟩
  have h1 : 2 ^ (a + 2) = 4 * 2 ^ a := by ring
  have h2 : 2 ^ (a + 2 + b - (a + 2) + 2) = 4 * 2 ^ b := by
    rw [show a + 2 + b - (a + 2) + 2 = b + 2 by omega]
    ring
  have h3 : 2 ^ (a + 2 + b) = 4 * (2 ^ a * 2 ^ b) := by ring
  obtain ⟨x, hx⟩ : ∃ x, 2 ^ a = x + 1 := ⟨2 ^ a - 1, by have := Nat.one_le_two_pow (n := a); omega⟩
  obtain ⟨y, hy⟩ : ∃ y, 2 ^ b = y + 1 := ⟨2 ^ b - 1, by have := Nat.one_le_two_pow (n := b); omega⟩
  rw [h1, h2, h3, hx, hy, show (x + 1) * (y + 1) = x * y + x + y + 1 by ring]
  generalize x * y = q
  omega

/-- The coefficient of the log-power form of `E_k`:
`c_7 C_S ((C₀+1) c_k + C_wc Σ_{i=2}^k c_i c_{k-i+2}) C_log^{e_k}` (`c_j = mbPowC d B j`). -/
def extraLogC (d : VSData) (B : ℝ) (k : ℕ) : ℝ :=
  aprC7 d * constS d * ((d.C0 + 1) * mbPowC d B k +
    d.Cwc * ∑ i ∈ Finset.Ioo 1 (k + 1), mbPowC d B i * mbPowC d B (k - i + 2)) *
      mbLogC d ^ mbPowExp k

/-- **Log-power form of the constant**: for `N ≥ 2`, `Λ = mbLambda d N`, and `B ≥ 1` bounding
`B₀ j` for `j ≤ k`: `E_k = extraConst d (mbConstI d Λ B₀) k ≤ C (log N)^{2^k − 4}`,
`C = extraLogC d B k`. -/
theorem extraConst_le_log_pow (d : VSData) {N : ℕ} (hN : 2 ≤ N) {B : ℝ} (hB : 1 ≤ B)
    (B₀ : ℕ → ℝ) (hB0 : ∀ j, 0 ≤ B₀ j) {k : ℕ} (hBk : ∀ j, j ≤ k → B₀ j ≤ B) :
    extraConst d (mbConstI d (mbLambda d N) B₀) k ≤
      extraLogC d B k * Real.log N ^ mbPowExp k := by
  obtain ⟨h0, h1, h2⟩ := mbLambda_le_log d hN
  have hIj : ∀ j, j ≤ k → mbConstI d (mbLambda d N) B₀ j ≤
      mbPowC d B j * (mbLogC d * Real.log N) ^ mbPowExp j := fun j hj =>
    (mbConst_le_pow d B₀ h0 h1 h2 hB hB0 j (fun i hi => hBk i (by omega)) j le_rfl).2
  have hI0 : ∀ j, 0 ≤ mbConstI d (mbLambda d N) B₀ j := mbConstI_nonneg d _ B₀ h0 hB0
  have hc : ∀ j, 0 ≤ mbPowC d B j := fun j => (zero_le_one.trans (mbPowC_ge_one d hB j))
  have hL0 : 0 ≤ mbLogC d * Real.log N := zero_le_one.trans h2
  have hc7 : 0 ≤ aprC7 d := by
    unfold aprC7
    have := (vsCK_pos d).le
    have := d.one_le_C1pp
    have := d.cm_pos
    positivity
  have hCS := constS_nonneg d
  have hC0 : 0 ≤ d.C0 + 1 := by linarith [d.C0_ge_one]
  have hCwc : 0 ≤ d.Cwc := by linarith [d.one_le_Cwc]
  have hsum : ∑ i ∈ Finset.Ioo 1 (k + 1),
      mbConstI d (mbLambda d N) B₀ i * mbConstI d (mbLambda d N) B₀ (k - i + 2) ≤
      ∑ i ∈ Finset.Ioo 1 (k + 1), mbPowC d B i * mbPowC d B (k - i + 2) *
        (mbLogC d * Real.log N) ^ mbPowExp k := by
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' := Finset.mem_Ioo.mp hi
    calc _ ≤ (mbPowC d B i * (mbLogC d * Real.log N) ^ mbPowExp i) *
          (mbPowC d B (k - i + 2) * (mbLogC d * Real.log N) ^ mbPowExp (k - i + 2)) :=
          mul_le_mul (hIj i (by omega)) (hIj _ (by omega)) (hI0 _)
            (mul_nonneg (hc _) (pow_nonneg hL0 _))
      _ = mbPowC d B i * mbPowC d B (k - i + 2) *
          (mbLogC d * Real.log N) ^ (mbPowExp i + mbPowExp (k - i + 2)) := by
          rw [pow_add]
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h2 (mbPowExp_add_le (by omega)
          (by omega))) (mul_nonneg (hc _) (hc _))
  have hIk := hIj k le_rfl
  unfold extraConst extraLogC
  calc aprC7 d * constS d * ((d.C0 + 1) * mbConstI d (mbLambda d N) B₀ k + d.Cwc *
        ∑ i ∈ Finset.Ioo 1 (k + 1),
          mbConstI d (mbLambda d N) B₀ i * mbConstI d (mbLambda d N) B₀ (k - i + 2))
      ≤ aprC7 d * constS d * ((d.C0 + 1) * (mbPowC d B k * (mbLogC d * Real.log N) ^
          mbPowExp k) + d.Cwc * ∑ i ∈ Finset.Ioo 1 (k + 1), mbPowC d B i *
            mbPowC d B (k - i + 2) * (mbLogC d * Real.log N) ^ mbPowExp k) :=
        mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hIk hC0)
          (mul_le_mul_of_nonneg_left hsum hCwc)) (mul_nonneg hc7 hCS)
    _ = _ := by
        rw [← Finset.sum_mul, mul_pow]
        ring

/-- `ExtraBAt` is monotone in the constant. -/
theorem extraBAt_mono {d : VSData} {m W : ℕ} {P : PsiData (m * W)} (hc : MBCtx d P) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) {k : ℕ} {E E' : ℝ} (h : ExtraBAt P t k E) (hE : E ≤ E') :
    ExtraBAt P t k E' := fun σ hσ w =>
  (h σ hσ w).trans (by
    have hη := (hc.inputs ht).height_pos
    have hX := mb_LsAv_pos_nonneg hc ht (fun j : Fin k => w j.castSucc)
    have e : ∀ E₀ : ℝ, E₀ / vsHeight P.z t * P.lEta t * P.sAv (fun j : Fin k => w j.castSucc) t =
        E₀ / vsHeight P.z t * (P.lEta t * P.sAv (fun j : Fin k => w j.castSucc) t) :=
      fun E₀ => by ring
    rw [e, e]
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hE hη.le) hX)

/-- **The extra `M`-bound in log-power form**: under `MBCtx d P` only, for `t ∈ [0,1]`, `k ≥ 2`
and `B = Σ_{j ≤ k} mzeroConst d j`: `Forcing.ExtraBAt P t k (C (log N)^{2^k − 4})`, `N = m W`,
`C = extraLogC d B k`. -/
theorem mbounds_extra_log_uncond {d : VSData} {m W : ℕ} {P : PsiData (m * W)} (hc : MBCtx d P)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {k : ℕ} (hk : 2 ≤ k) :
    ExtraBAt P t k (extraLogC d (∑ j ∈ Finset.range (k + 1), MZero.mzeroConst d j) k *
      Real.log ((m * W : ℕ) : ℝ) ^ mbPowExp k) := by
  have hN : 2 ≤ m * W :=
    calc 2 ≤ 4 := by norm_num
      _ ≤ m := hc.hm
      _ ≤ m * W := Nat.le_mul_of_pos_right m hc.hW
  obtain ⟨hB, hBk⟩ := Discharge.mzeroConst_le_sum d k
  exact extraBAt_mono hc ⟨ht0, ht1⟩ (mbounds_extra_uncond hc ht0 ht1 hk)
    (extraConst_le_log_pow d hN hB (MZero.mzeroConst d) (MZero.mzeroConst_nonneg d) hBk)

end BlockBand.Native.ErdosRiabov.Apriori
