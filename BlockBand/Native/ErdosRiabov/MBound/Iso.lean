module

public import BlockBand.Native.ErdosRiabov.MBound.Base
public import BlockBand.Native.ErdosRiabov.Contr.MoreLocal

/-!
# The isotropic `M`-bound

The diagonal entries of the deterministic `M`-chains are bounded by `I_k √L s^iso_k`, by the
tensor Duhamel formula and the bounds on the isotropic `M`-forcing.

For `k = n+3`, `Y_t(x) = (M^σ_t(x'))_{aa}` (`Psi.PsiData.mChain`, the site `x_{k-1}` unused):
* `mbIsoM_evol` (unconditional): `d/dt Y = (⊕_{j<k-1} Â_j) Y + F^iso`, the generator being
  `propOp (vsTensorGen …)` with the factors `Propagator.propFactorIso σ` (identity last), and
  `F^iso = mbLastM + mbFIso`: the pair `(1,k)` gives the last line
  `m_1 m_k Σ_q (I + tÂ_k)_{aq} Tr[M^σ_t](x[k ↦ q])` (`mbLastM`, via `Evol.mGlue_cyc`), the pairs
  `2 ≤ j-i ≤ k-2` give `mbFIso` (adjacent pairs are the generator);
* `mbFIso_bound`: the iso insertion (`Contr.isoSublin_vs`, the Schwarz bound for `Υ`):
  `|mbFIso| ≤ (C_wc/η) Σ I_{p+1} I_{k-p+1} √L s^iso_k(a,x',a)`;
* `mb_lastM_bound`: `|mbLastM| ≤ ((C₀+1) + C_K C_wc)/η · A_k √L s^iso_k(a,x',a)`
  (`δ`-part by `L s^av_k(x', a) = √L s^iso_k(a,x',a)` and `η ≤ C₀+1`; `Υ`-part by
  `Contr.isoAv_vs`);
* **`mbBounds_iso`**: `|Y_t(x)| ≤ I_k √(L_t) s^iso_{k,t}(a,x',a)` with
  `I_k = C_P^{k-1} (B₀ + Λ F^iso_k)`, `F^iso_k = C_wc Σ I I + (C₀ + 1 + C_K C_wc) A_k` (`mbIsoK`),
  by the tensor Duhamel formula and `Propagator.goodProps_iso_apply`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.MBound

open Function Set MeasureTheory
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Psi BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow BlockBand.Native.ErdosRiabov.Evol
open BlockBand.Native.ErdosRiabov.Propagator BlockBand.Native.ErdosRiabov.Contr
open BlockBand.Internal.Contracts.Inputs (shortRingProfile polynomialControl)
open scoped ComplexConjugate BigOperators

variable {N : ℕ}

/-!
## Size functions
-/

theorem mb_sIso_cast (P : PsiData N) {m m' : ℕ} (h : m = m') (a b : Fin N)
    (x : Fin m' → Fin N) (t : ℝ) : P.sIso a b (fun r => x (Fin.cast h r)) t = P.sIso a b x t := by
  subst h
  rfl

/-- Closing the averaged chain at `a`: `L s^av_k(x', a) = √L s^iso_k(a, x', a)` (`k = n+2`). -/
theorem mb_LsAv_update_last (P : PsiData N) (t : ℝ) (hL : 0 < P.lEta t) {n : ℕ}
    (x : Fin (n + 2) → Fin N) (a : Fin N) :
    P.lEta t * P.sAv (update x (Fin.last (n + 1)) a) t =
      Real.sqrt (P.lEta t) * P.sIso a a x t := by
  rw [contr_sAv_eq P (by omega), contr_sIso_eq]
  have h0 : update x (Fin.last (n + 1)) a ⟨0, by omega⟩ = x ⟨0, by omega⟩ :=
    update_of_ne (by simp [Fin.ext_iff]) _ _
  have hcp : ∀ m, m ≤ n + 1 → contrCycPt (update x (Fin.last (n + 1)) a)
      (update x (Fin.last (n + 1)) a ⟨0, by omega⟩) m = isoPoint a a x (m + 1) := by
    intro m hm
    rw [contr_cycPt_lt _ _ (by omega : m < n + 2)]
    rcases Nat.lt_or_ge m (n + 1) with h | h
    · have e1 : update x (Fin.last (n + 1)) a ⟨m, by omega⟩ = x ⟨m, by omega⟩ :=
        update_of_ne (by simp [Fin.ext_iff]; omega) _ _
      rw [e1, contr_isoPoint_succ _ _ _ (by omega : m + 1 < n + 2)]
    · obtain rfl : m = n + 1 := by omega
      rw [contr_isoPoint_of_le _ _ _ (m := n + 1 + 1) (by omega) (by omega)]
      exact update_self _ _ _
  have hprod : contrPathProd (P.ups t) (contrCycPt (update x (Fin.last (n + 1)) a)
      (update x (Fin.last (n + 1)) a ⟨0, by omega⟩)) (n + 2) =
      contrPathProd (P.ups t) (isoPoint a a x) (n + 2) := by
    unfold contrPathProd
    conv_lhs => rw [Finset.prod_range_succ]
    conv_rhs => rw [Finset.prod_range_succ']
    congr 1
    · refine Finset.prod_congr rfl fun m hm => ?_
      have hm' := Finset.mem_range.mp hm
      rw [hcp m (by omega), hcp (m + 1) (by omega)]
    · rw [hcp (n + 1) le_rfl, contr_cycPt_ge _ _ (by omega : n + 2 ≤ n + 1 + 1), h0,
        contr_isoPoint_of_le _ _ _ (m := n + 1 + 1) (by omega) (by omega), contr_isoPoint_zero,
        contr_isoPoint_succ _ _ _ (by omega : 0 + 1 < n + 2)]
  rw [hprod, ← mul_assoc, ← mul_assoc]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hL, mul_comm, ← Real.rpow_add_one hL.ne']
  congr 1
  push_cast
  ring

/-!
## The isotropic forcing
-/

section Defs

variable {k : ℕ}

/-- The isotropic `M`-forcing at the entry `a` (pairs with `2 ≤ j - i ≤ k - 2`):
`Σ_{i<j} Σ_q (M_{[i,j]})_{qq} (M^{(q)}_{[1,i],[j,k]})_{aa}` (`Evol.aM`, `Evol.bMiso`). -/
def mbFIso (P : PsiData N) (σ : Fin k → Bool) (a : Fin N) (x : Fin k → Fin N) (t : ℝ) : ℂ :=
  ∑ j : Fin k, ∑ i with i < j,
    if 2 ≤ (j : ℕ) - i ∧ (j : ℕ) - i ≤ k - 2 then
      ∑ q, aM P σ x t i j q * bMiso P σ x t a a i j q
    else 0

/-- The last line `m_1 m_k Σ_q (I + tÂ_k)_{aq} Tr[M^σ_t](x[l ↦ q])` (`l` the last slot). -/
def mbLastM (P : PsiData N) (σ : Fin k → Bool) (x : Fin k → Fin N) (t : ℝ) (a : Fin N)
    (l : Fin k) : ℂ :=
  ∑ q, patM P.z σ 1 * patM P.z σ k * (1 + (t : ℂ) • aKer P σ l t) a q *
    avM P σ (update x l q) t

/-- The isotropic generator `⊕_{j<k-1} Â_j` (factors `propFactorIso σ`, identity last). -/
def mbIsoGen (P : PsiData N) (σ : Fin k → Bool) (t : ℝ) :
    Matrix (Fin k → Fin N) (Fin k → Fin N) ℂ :=
  vsTensorGen P.S (fun j => (propFactorIso σ j).mu1 P.z) (fun j => (propFactorIso σ j).mu2 P.z) t

/-- The iso pair sum `Σ_{i<j, 2 ≤ j-i ≤ k-2} I(j-i+1) I(k-(j-i)+1)`. -/
def mbFIsoPairSum (k : ℕ) (I : ℕ → ℝ) : ℝ :=
  ∑ j : Fin k, ∑ i with i < j,
    if 2 ≤ (j : ℕ) - i ∧ (j : ℕ) - i ≤ k - 2 then I ((j : ℕ) - i + 1) * I (k - j + i + 1)
    else 0

end Defs

/-- The forcing `F^iso(a; x) = mbLastM + mbFIso` for chain length `k = n+3`. -/
def mbGIso (P : PsiData N) {n : ℕ} (σ : Fin (n + 3) → Bool) (a : Fin N) (t : ℝ) :
    (Fin (n + 3) → Fin N) → ℂ :=
  fun x => mbLastM P σ x t a (Fin.last (n + 2)) + mbFIso P σ a x t

/-- `F^iso_k = C_wc Σ I I + (C₀ + 1 + C_K C_wc) A_k` (`C_Θ = C_K C_wc`). -/
def mbFIsoC (d : VSData) (k : ℕ) (Ak : ℝ) (I : ℕ → ℝ) : ℝ :=
  d.Cwc * mbFIsoPairSum k I + (d.C0 + 1 + vsCK d * d.Cwc) * Ak

/-- `I_k = C_P^{k-1} (B₀ + Λ F^iso_k)`. -/
def mbIsoK (d : VSData) (Λ : ℝ) (k : ℕ) (Ak : ℝ) (I : ℕ → ℝ) (B₀ : ℝ) : ℝ :=
  kernelActionConst d ^ (k - 1) * (B₀ + Λ * mbFIsoC d k Ak I)

theorem mbFIsoPairSum_nonneg {k : ℕ} {I : ℕ → ℝ} (hI0 : ∀ n, 0 ≤ I n) :
    0 ≤ mbFIsoPairSum k I := by
  unfold mbFIsoPairSum
  refine Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => ?_
  split_ifs
  · exact mul_nonneg (hI0 _) (hI0 _)
  · exact le_rfl

/-!
## The evolution of the diagonal entry
-/

section Evol

variable {k : ℕ} (P : PsiData N) (σ : Fin k → Bool) (x : Fin k → Fin N) (t : ℝ)

/-- `M^{(q)}_{[1,i],[j,k]}` (`Evol.mGlue`) is the pattern `M`-term of the glued pattern. -/
theorem mb_mGlue_eq {i j : Fin k} (hij : i < j) (q a : Fin N) :
    mGlue P σ x t i j q a = P.mChain (mbGluePat σ i j) (mbGlueSites x i j q) t a := by
  have hj := j.isLt
  have hn : k - ((j : ℕ) + 1) + ((i : ℕ) + 1) + 1 = k - j + i + 1 := by omega
  rw [mGlue, PsiData.mChain, hn]
  refine congrFun (mb_chainM_congr t P.S (fun p hp1 hp2 => ?_) (fun p hp1 hp2 => ?_)) a
  · unfold Split.glueChain
    rw [mb_patM_apply _ _ hp1 hp2]
    by_cases hp : p ≤ (i : ℕ) + 1
    · rw [ite_eq_left hp, mb_patM_apply _ _ hp1 (by omega)]
      congr 2
      unfold mbGluePat
      rw [dite_eq_left (by simp only; omega)]
    · rw [ite_eq_right hp, mb_patM_apply _ _ (by omega) (by omega)]
      congr 2
      unfold mbGluePat
      rw [dite_eq_right (by simp only; omega)]
      congr 1
      apply Fin.ext
      simp only
      omega
  · unfold Split.glueObs
    rw [mb_obsSeq_apply P.S (mbGlueSites x i j q) hp1 (by omega)]
    by_cases hp : p < (i : ℕ) + 1
    · rw [ite_eq_left hp, mb_obsSeq_apply _ _ hp1 (by omega)]
      congr 2
      unfold mbGlueSites
      rw [dite_eq_left (by simp only; omega)]
    · rw [ite_eq_right hp]
      by_cases hp' : p = (i : ℕ) + 1
      · rw [ite_eq_left hp']
        unfold mbGlueSites
        rw [dite_eq_right (by simp only; omega), ite_eq_left (by simp only; omega)]
      · rw [ite_eq_right hp', mb_obsSeq_apply _ _ (by omega) (by omega)]
        congr 2
        unfold mbGlueSites
        rw [dite_eq_right (by simp only; omega), ite_eq_right (by simp only; omega)]
        congr 1
        apply Fin.ext
        simp only
        omega

/-- Adjacent pair `(s, s+1)`: `Σ_q aM bMiso_{aa} = Σ_q (Â_s)_{x_s q} (M^σ_t(x[s ↦ q]))_{aa}`. -/
theorem mb_pair_adj_iso (hS : ∀ a b, P.S a b = P.S b a) (a : Fin N) {s : Fin k}
    (hs : (s : ℕ) + 1 < k) :
    ∑ q, aM P σ x t s ⟨(s : ℕ) + 1, hs⟩ q * bMiso P σ x t a a s ⟨(s : ℕ) + 1, hs⟩ q =
      ∑ q, aKer P σ s t (x s) q * P.mChain σ (update x s q) t a := by
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [aM_adj P σ x t hS hs, bMiso, ite_eq_left rfl, mChain_update_adj P σ x t hs]

/-- The pair `(1, k)`: `Σ_q (M_{[1,k]})_{qq} (M^{(q)}_{[1,1],[k,k]})_{aa}` is the last line. -/
theorem mb_pair_cyc_iso (hSS : StochasticSymm P.S) (hz : P.z.im ≠ 0) (ht : t ∈ Icc (0 : ℝ) 1)
    (hk : 2 ≤ k) (a : Fin N) :
    ∑ q, aM P σ x t ⟨0, by omega⟩ ⟨k - 1, by omega⟩ q *
        bMiso P σ x t a a ⟨0, by omega⟩ ⟨k - 1, by omega⟩ q =
      mbLastM P σ x t a ⟨k - 1, by omega⟩ := by
  have hS := hSS.symm
  have hl : ((⟨k - 1, by omega⟩ : Fin k) : ℕ) + 1 = k := by simp only; omega
  have hA : ∀ q, aM P σ x t ⟨0, by omega⟩ ⟨k - 1, by omega⟩ q = P.mChain σ x t q := by
    intro q
    rw [aM, mSeg]
    simp only [Nat.zero_add]
    rw [show k - 1 + 1 = k by omega]
    rfl
  have hB : ∀ q, bMiso P σ x t a a ⟨0, by omega⟩ ⟨k - 1, by omega⟩ q =
      mGlue P σ x t ⟨0, by omega⟩ ⟨k - 1, by omega⟩ q a := fun q => by
    rw [bMiso, ite_eq_left rfl]
  have hX : ∀ p, avM P σ (update x ⟨k - 1, by omega⟩ p) t =
      ∑ q, P.mChain σ x t q * (P.S p q : ℂ) := by
    intro p
    rw [avM, mChain_update_last P σ x t hl, obsSeq_update, hl, update_self]
    rfl
  have hn : ‖(t : ℂ) * (patM P.z σ k * patM P.z σ 1)‖ < 1 :=
    norm_smul_lt_one (norm_patM_lt_one hz σ _) (norm_patM_lt_one hz σ _) ht.1 ht.2
  unfold mbLastM
  simp_rw [hA, hB, hX, aKer_last P σ t hl, one_add_smul_vsKernel hSS hn, mGlue_cyc P σ x t hk]
  rw [mul_comm (patM P.z σ k)]
  have := sum_iso_alg hS (Split.stabOp t P.S (patM P.z σ 1 * patM P.z σ k))
    (patM P.z σ 1 * patM P.z σ k) (fun q => P.mChain σ x t q) a
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Split.rowObs] at this ⊢
  rw [this]

end Evol

/-- **The evolution of the isotropic `M`-terms** (ER without `k/2`, VS form; a statement about
`Evol.mDerivP`, the explicit right-hand side of `Split.DerivStatement`, with no hypothesis): for
`k = n+3`, stochastic symmetric `S`, `Im z ≠ 0`, `t ∈ [0,1]`,
`d/dt (M^σ_t)_{aa} = (⊕_{j<k-1} Â_j)[(M^σ_t)_{aa}] + mbLastM + mbFIso`.
-/
theorem mbIsoM_evol (P : PsiData N) (hSS : StochasticSymm P.S) (hz : P.z.im ≠ 0) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) {n : ℕ} (σ : Fin (n + 3) → Bool) (a : Fin N)
    (x : Fin (n + 3) → Fin N) :
    mDerivP P σ x t a =
      propOp (mbIsoGen P σ t) (fun y => P.mChain σ y t a) x + mbGIso P σ a t x := by
  have hS := hSS.symm
  have hd : dMiso P σ a a x t = mDerivP P σ x t a := by rw [dMiso, ite_eq_left rfl]
  rw [← hd, dMiso_split]
  set T : Fin (n + 3) → Fin (n + 3) → ℂ :=
    fun i j => ∑ q, aM P σ x t i j q * bMiso P σ x t a a i j q
  have hsplit : ∀ j : Fin (n + 3), ∀ i ∈ (Finset.univ.filter fun i : Fin (n + 3) => i < j),
      T i j = (if (j : ℕ) = i + 1 then T i j else 0) +
        (if (j : ℕ) - i = n + 3 - 1 then T i j else 0) +
        (if 2 ≤ (j : ℕ) - i ∧ (j : ℕ) - i ≤ n + 3 - 2 then T i j else 0) := by
    intro j i hi
    have hij : (i : ℕ) < j := (Finset.mem_filter.mp hi).2
    have hjk := j.isLt
    by_cases h1 : (j : ℕ) = i + 1
    · rw [ite_eq_left h1, ite_eq_right (by omega), ite_eq_right (by omega)]
      ring
    · by_cases h2 : (j : ℕ) - i = n + 3 - 1
      · rw [ite_eq_right h1, ite_eq_left h2, ite_eq_right (by omega)]
        ring
      · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left (by omega)]
        ring
  have e : ∑ j : Fin (n + 3), ∑ i with i < j, T i j =
      (∑ j : Fin (n + 3), ∑ i with i < j, if (j : ℕ) = i + 1 then T i j else 0) +
        (∑ j : Fin (n + 3), ∑ i with i < j, if (j : ℕ) - i = n + 3 - 1 then T i j else 0) +
        mbFIso P σ a x t := by
    rw [Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl (hsplit j)]
    simp only [Finset.sum_add_distrib]
    rfl
  rw [e, lAdj_eq, lCyc_eq (by omega), add_assoc]
  simp only [mbGIso]
  congr 1
  · rw [mbIsoGen, propOp_vsTensorGen_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases hs : (s : ℕ) + 1 < n + 3
    · rw [dite_eq_left hs]
      have hf : propFactorIso σ s = propFactorOf σ s := by
        unfold propFactorIso
        rw [ite_eq_left hs]
      simp only [hf]
      rw [← aKer_eq_factor]
      exact mb_pair_adj_iso P σ x t hS a hs
    · rw [dite_eq_right hs]
      have hf : propFactorIso σ s = .ident := by
        unfold propFactorIso
        rw [ite_eq_right hs]
      simp [hf, PropFactor.mu1, vsKernel_zero_left]
  · congr 1
    exact mb_pair_cyc_iso P σ x t hSS hz ht (by omega) a

/-!
## The bounds on the forcing
-/

section Bound

variable (P : PsiData N) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {d : VSData}
  (hin : ContrVSInputs d P t)
include ht hin

/-- One pair `(i, j)` of `mbFIso`, `2 ≤ j - i ≤ k - 2`:
`|Σ_q (M_{[i,j]})_{qq} (M^{(q)})_{aa}| ≤ (C_wc/η) I₁ I₂ √L s^iso_k(a,x',a)` under
`IsoB(j-i+1, I₁)` and `IsoB(k-j+i+1, I₂)`.
-/
theorem mb_pair_iso_bound {k : ℕ} (σ : Fin k → Bool) (a : Fin N) (x : Fin k → Fin N)
    (i j : Fin k) (h2 : 2 ≤ (j : ℕ) - i) (hk : (j : ℕ) - i ≤ k - 2) {I₁ I₂ : ℝ} (hI₁ : 0 ≤ I₁)
    (hI₂ : 0 ≤ I₂) (hI₁b : MBIsoB P ((j : ℕ) - i + 1) I₁) (hI₂b : MBIsoB P (k - j + i + 1) I₂) :
    ‖∑ q, aM P σ x t i j q * bMiso P σ x t a a i j q‖ ≤
      d.Cwc / vsHeight P.z t * (I₁ * I₂) * (Real.sqrt (P.lEta t) * P.sIso a a x t) := by
  have hij : i < j := by rw [Fin.lt_def]; omega
  have hjk := j.isLt
  have hr : (i : ℕ) + (k - 1 - j) + 2 = k - j + i + 1 := by omega
  have hw : (i : ℕ) + ((j : ℕ) - i) + (k - 1 - j) + 1 = k := by omega
  set zq : Fin N → Fin ((i : ℕ) + (k - 1 - j) + 2) → Fin N :=
    fun q r => mbGlueSites x i j q (Fin.cast hr r)
  set w : Fin ((i : ℕ) + ((j : ℕ) - i) + (k - 1 - j) + 1) → Fin N := fun r => x (Fin.cast hw r)
  have hzpre : ∀ (q : Fin N) (n : ℕ) (hn : n < (i : ℕ)),
      zq q ⟨n, by omega⟩ = w ⟨n, by omega⟩ := fun q n hn =>
    mbGlueSites_lt x i j q (r := ⟨n, by omega⟩) hn
  have hzmid : ∀ q, zq q ⟨i, by omega⟩ = q := fun q =>
    mbGlueSites_eq_q x i j q (r := ⟨i, by omega⟩) rfl
  have hzpost : ∀ (q : Fin N) (n : ℕ) (hn : n < k - 1 - j),
      zq q ⟨(i : ℕ) + 1 + n, by omega⟩ = w ⟨(i : ℕ) + ((j : ℕ) - i) + n, by omega⟩ := by
    intro q n hn
    refine (mbGlueSites_gt x i j q (r := ⟨(i : ℕ) + 1 + n, by omega⟩) (by simp only; omega)
      (by simp only; omega)).trans ?_
    show x _ = x _
    congr 1
    apply Fin.ext
    show (i : ℕ) + 1 + n + j - i - 1 = (i : ℕ) + ((j : ℕ) - i) + n
    omega
  have hy : ∀ (n : ℕ) (hn : n < (j : ℕ) - i),
      mbSubSites x i j ⟨n, by omega⟩ = w ⟨(i : ℕ) + n, by omega⟩ := by
    intro n hn
    simp only [mbSubSites, w]
    congr 1
    apply Fin.ext
    show min ((i : ℕ) + n) (k - 1) = (i : ℕ) + n
    omega
  have hins := isoSublin_vs d P hin (r := i) (p := (j : ℕ) - i) (s := k - 1 - j) (by omega) a a
    (mbSubSites x i j) zq w hzpre hzmid hzpost hy
  have hpw : Real.sqrt (P.lEta t) = P.lEta t ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  calc ‖∑ q, aM P σ x t i j q * bMiso P σ x t a a i j q‖
      ≤ ∑ q, ‖aM P σ x t i j q‖ * ‖bMiso P σ x t a a i j q‖ :=
        (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun _ _ => norm_mul _ _))
    _ ≤ ∑ q, (I₁ * (Real.sqrt (P.lEta t) * P.sIso q q (mbSubSites x i j) t)) *
          (I₂ * (Real.sqrt (P.lEta t) * P.sIso a a (zq q) t)) := by
        refine Finset.sum_le_sum fun q _ => ?_
        have hb : bMiso P σ x t a a i j q =
            P.mChain (mbGluePat σ i j) (mbGlueSites x i j q) t a := by
          rw [bMiso, ite_eq_left rfl, mb_mGlue_eq P σ x t hij]
        have hz : P.sIso a a (zq q) t = P.sIso a a (mbGlueSites x i j q) t :=
          mb_sIso_cast P hr a a _ t
        rw [mb_aM_eq P σ x t hij.le, hb, hz]
        exact mul_le_mul (hI₁b t ht _ q _) (hI₂b t ht _ a _) (norm_nonneg _)
          (mul_nonneg hI₁ (mul_nonneg (Real.sqrt_nonneg _) (mb_sIso_nonneg P hin _ _ _)))
    _ = I₁ * I₂ * Real.sqrt (P.lEta t) *
          ∑ q, P.lEta t ^ (1 / 2 : ℝ) * P.sIso q q (mbSubSites x i j) t * P.sIso a a (zq q) t := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [← hpw]
        ring
    _ ≤ I₁ * I₂ * Real.sqrt (P.lEta t) * (d.Cwc / vsHeight P.z t * P.sIso a a w t) :=
        mul_le_mul_of_nonneg_left hins (mul_nonneg (mul_nonneg hI₁ hI₂) (Real.sqrt_nonneg _))
    _ = _ := by
        rw [mb_sIso_cast P hw a a x t]
        ring

/-- The iso insertion bound: if `IsoB(n, I n)` for `3 ≤ n ≤ k-1` (`I ≥ 0`), then
`|mbFIso(a; x)| ≤ (C_wc/η) · mbFIsoPairSum k I · √L s^iso_k(a,x',a)`.
-/
theorem mbFIso_bound {k : ℕ} (I : ℕ → ℝ) (hI0 : ∀ n, 0 ≤ I n)
    (hI : ∀ n, 3 ≤ n → n + 1 ≤ k → MBIsoB P n (I n)) (σ : Fin k → Bool) (a : Fin N)
    (x : Fin k → Fin N) :
    ‖mbFIso P σ a x t‖ ≤
      d.Cwc / vsHeight P.z t * mbFIsoPairSum k I * (Real.sqrt (P.lEta t) * P.sIso a a x t) := by
  unfold mbFIso mbFIsoPairSum
  rw [Finset.mul_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [Finset.mul_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  have hij := (Finset.mem_filter.mp hi).2
  have hij' : (i : ℕ) < j := hij
  have hjk := j.isLt
  split_ifs with hc
  · have := mb_pair_iso_bound P ht hin σ a x i j hc.1 hc.2 (hI0 _) (hI0 _)
      (hI _ (by omega) (by omega)) (hI _ (by omega) (by omega))
    simpa only [mul_assoc] using this
  · simp

end Bound

section VS

variable {d : VSData} {m W : ℕ} {P : PsiData (m * W)} (hA : MBAlg) (hc : MBCtx d P)

include hc in

/-- The last line:
`|mbLastM(a; x)| ≤ ((C₀+1) + C_K C_wc)/η · A_k √L s^iso_k(a,x',a)` under
`AvB(k, A_k)` (`k = n+3`).
-/
theorem mb_lastM_bound {n : ℕ} (σ : Fin (n + 3) → Bool) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {A : ℝ} (hA0 : 0 ≤ A) (hAb : MBAvB P (n + 3) A) (a : Fin (m * W))
    (x : Fin (n + 3) → Fin (m * W)) :
    ‖mbLastM P σ x t a (Fin.last (n + 2))‖ ≤
      (d.C0 + 1 + vsCK d * d.Cwc) / vsHeight P.z t * A *
        (Real.sqrt (P.lEta t) * P.sIso a a x t) := by
  have hin := hc.inputs ht
  have hL := hin.lEta_pos
  have hη := hin.height_pos
  have hU := hin.nonneg
  have hCK := (vsCK_pos d).le
  have hz := hc.zpos
  have hl : ((Fin.last (n + 2) : Fin (n + 3)) : ℕ) + 1 = n + 3 := rfl
  have hker : ∀ q, ‖(1 + (t : ℂ) • aKer P σ (Fin.last (n + 2)) t) a q‖ ≤
      ‖(1 : Matrix (Fin (m * W)) (Fin (m * W)) ℂ) a q‖ + vsCK d * P.ups t a q := by
    intro q
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    have hK : ‖aKer P σ (Fin.last (n + 2)) t a q‖ ≤ vsCK d * P.ups t a q := by
      rw [aKer_last P σ t hl]
      have h1 : patM P.z σ (n + 3) = VS.patConj (σ (Fin.last (n + 2))) (semicircleM P.z) :=
        patM_of_mem P.z σ (Fin.last (n + 2))
      have h2 : patM P.z σ 1 = VS.patConj (σ ⟨0, by omega⟩) (semicircleM P.z) :=
        patM_of_mem P.z σ ⟨0, by omega⟩
      rw [h1, h2]
      exact mb_kernel_bound hc _ _ ht a q
    calc t * ‖aKer P σ (Fin.last (n + 2)) t a q‖ ≤ 1 * ‖aKer P σ (Fin.last (n + 2)) t a q‖ :=
          mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hK
  have hterm : ∀ q, ‖patM P.z σ 1 * patM P.z σ (n + 3) *
      (1 + (t : ℂ) • aKer P σ (Fin.last (n + 2)) t) a q *
        avM P σ (update x (Fin.last (n + 2)) q) t‖ ≤
      (‖(1 : Matrix (Fin (m * W)) (Fin (m * W)) ℂ) a q‖ + vsCK d * P.ups t a q) *
        (A * (P.lEta t * P.sAv (update x (Fin.last (n + 2)) q) t)) := by
    intro q
    rw [norm_mul, norm_mul, norm_mul]
    have hm1 := (norm_patM_lt_one hz.ne' σ 1).le
    have hmk := (norm_patM_lt_one hz.ne' σ (n + 3)).le
    have hmm : ‖patM P.z σ 1‖ * ‖patM P.z σ (n + 3)‖ ≤ 1 := by
      nlinarith [norm_nonneg (patM P.z σ 1), norm_nonneg (patM P.z σ (n + 3))]
    calc _ ≤ 1 * ‖(1 + (t : ℂ) • aKer P σ (Fin.last (n + 2)) t) a q‖ *
          ‖avM P σ (update x (Fin.last (n + 2)) q) t‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmm (norm_nonneg _))
            (norm_nonneg _)
      _ ≤ _ := by
          rw [one_mul]
          exact mul_le_mul (hker q) (hAb t ht σ _) (norm_nonneg _)
            (add_nonneg (norm_nonneg _) (mul_nonneg hCK (hU _ _)))
  have hsum1 : ∑ q, ‖(1 : Matrix (Fin (m * W)) (Fin (m * W)) ℂ) a q‖ *
      (A * (P.lEta t * P.sAv (update x (Fin.last (n + 2)) q) t)) =
      A * (P.lEta t * P.sAv (update x (Fin.last (n + 2)) a) t) := by
    rw [Finset.sum_eq_single a]
    · rw [Matrix.one_apply_eq, norm_one, one_mul]
    · intro q _ hq
      rw [Matrix.one_apply_ne (Ne.symm hq), norm_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ a) h
  have hsum2 : ∑ q, P.ups t a q * P.sAv (update x (Fin.last (n + 2)) q) t ≤
      d.Cwc / vsHeight P.z t * P.lEta t ^ (-(1 / 2 : ℝ)) * P.sIso a a x t :=
    isoAv_vs d P hin (p := n + 2) (by omega) a (fun q => update x (Fin.last (n + 2)) q) x
      (fun q => update_self _ _ _)
      (fun q n' hn' => update_of_ne (by simp [Fin.ext_iff]; omega) _ _)
  have hLsI : 0 ≤ Real.sqrt (P.lEta t) * P.sIso a a x t :=
    mul_nonneg (Real.sqrt_nonneg _) (mb_sIso_nonneg P hin _ _ _)
  have hLh : P.lEta t * P.lEta t ^ (-(1 / 2 : ℝ)) = Real.sqrt (P.lEta t) := by
    rw [Real.sqrt_eq_rpow, mul_comm, ← Real.rpow_add_one hL.ne']
    norm_num
  have h1le : 1 ≤ (d.C0 + 1) / vsHeight P.z t := (one_le_div hη).mpr hin.height_le
  calc ‖mbLastM P σ x t a (Fin.last (n + 2))‖
      ≤ ∑ q, (‖(1 : Matrix (Fin (m * W)) (Fin (m * W)) ℂ) a q‖ + vsCK d * P.ups t a q) *
          (A * (P.lEta t * P.sAv (update x (Fin.last (n + 2)) q) t)) := by
        unfold mbLastM
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => hterm q)
    _ = A * (P.lEta t * P.sAv (update x (Fin.last (n + 2)) a) t) +
          vsCK d * A * P.lEta t *
            ∑ q, P.ups t a q * P.sAv (update x (Fin.last (n + 2)) q) t := by
        rw [← hsum1, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun q _ => ?_
        ring
    _ ≤ A * (Real.sqrt (P.lEta t) * P.sIso a a x t) + vsCK d * A * P.lEta t *
          (d.Cwc / vsHeight P.z t * P.lEta t ^ (-(1 / 2 : ℝ)) * P.sIso a a x t) := by
        rw [mb_LsAv_update_last P t hL (n := n + 1) x a]
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hsum2 (mul_nonneg (mul_nonneg hCK hA0) hL.le))
    _ = A * (Real.sqrt (P.lEta t) * P.sIso a a x t) + vsCK d * d.Cwc / vsHeight P.z t * A *
          (Real.sqrt (P.lEta t) * P.sIso a a x t) := by
        rw [← hLh]
        ring
    _ ≤ (d.C0 + 1) / vsHeight P.z t * A * (Real.sqrt (P.lEta t) * P.sIso a a x t) +
          vsCK d * d.Cwc / vsHeight P.z t * A * (Real.sqrt (P.lEta t) * P.sIso a a x t) := by
        refine add_le_add ?_ le_rfl
        rw [mul_assoc]
        exact le_mul_of_one_le_left (mul_nonneg hA0 hLsI) h1le
    _ = _ := by ring

include hc in

/-- The full isotropic forcing:
`|F^iso(a; x)| ≤ F^iso_k/η · √L s^iso_k(a,x',a)` under
`AvB(k, A_k)` and `IsoB(n, I n)` for `3 ≤ n ≤ k-1`.
-/
theorem mbGIso_bound {n : ℕ} (σ : Fin (n + 3) → Bool) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {Ak : ℝ} (hAk0 : 0 ≤ Ak) (hAk : MBAvB P (n + 3) Ak) (I : ℕ → ℝ) (hI0 : ∀ n, 0 ≤ I n)
    (hIso : ∀ n', 3 ≤ n' → n' + 1 ≤ n + 3 → MBIsoB P n' (I n')) (a : Fin (m * W))
    (x : Fin (n + 3) → Fin (m * W)) :
    ‖mbGIso P σ a t x‖ ≤
      mbFIsoC d (n + 3) Ak I / vsHeight P.z t * (Real.sqrt (P.lEta t) * P.sIso a a x t) := by
  have h1 := mb_lastM_bound hc σ ht hAk0 hAk a x
  have h2 := mbFIso_bound P ht (hc.inputs ht) I hI0 hIso σ a x
  show ‖mbLastM P σ x t a (Fin.last (n + 2)) + mbFIso P σ a x t‖ ≤ _
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add h1 h2
    _ = _ := by
        unfold mbFIsoC
        ring

include hA hc in
theorem mb_hasDerivAt_Y_iso {n : ℕ} (σ : Fin (n + 3) → Bool) (a : Fin (m * W)) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun r => fun x => P.mChain σ x r a)
      (propOp (mbIsoGen P σ s) (fun x => P.mChain σ x s a) + mbGIso P σ a s) s := by
  rw [hasDerivAt_pi]
  intro x
  have h := hasDerivAt_mChain P hA.deriv hc.zpos.ne' hc.stoch (by omega) σ x hs a
  rw [mbIsoM_evol P hc.stoch hc.zpos.ne' hs σ a x] at h
  exact h

include hA hc in
theorem mb_contOn_GIso {n : ℕ} (σ : Fin (n + 3) → Bool) (a : Fin (m * W)) :
    ContinuousOn (fun r => mbGIso P σ a r) (Icc (0 : ℝ) 1) := by
  have hY : ∀ y, ContinuousOn (fun r => P.mChain σ y r a) (Icc (0 : ℝ) 1) := fun y r hr =>
    (hasDerivAt_mChain P hA.deriv hc.zpos.ne' hc.stoch (by omega) σ y hr
      a).continuousAt.continuousWithinAt
  have hK : ∀ (j : Fin (n + 3)) (u v : Fin (m * W)), ContinuousOn
      (fun r => vsKernel P.S ((propFactorIso σ j).mu1 P.z) ((propFactorIso σ j).mu2 P.z) r u v)
      (Icc (0 : ℝ) 1) := fun j u v r hr =>
    (hasDerivAt_vsKernel hc.stoch (norm_smul_lt_one (mb_norm_mu1_lt hc.zpos _)
      (mb_norm_mu2_lt hc.zpos _) hr.1 hr.2) u v).continuousAt.continuousWithinAt
  have hD : ContinuousOn (fun r => fun x => mDerivP P σ x r a -
      propOp (mbIsoGen P σ r) (fun y => P.mChain σ y r a) x) (Icc (0 : ℝ) 1) := by
    refine continuousOn_pi.2 fun x =>
      ContinuousOn.sub (continuousOn_mDerivP P hc.zpos.ne' hc.stoch σ x a) ?_
    simp only [mbIsoGen, propOp_vsTensorGen_apply]
    exact continuousOn_finsetSum _ fun j _ => continuousOn_finsetSum _ fun q _ =>
      (hK j _ _).mul (hY _)
  refine hD.congr fun r hr => ?_
  funext x
  show mbGIso P σ a r x = mDerivP P σ x r a - propOp (mbIsoGen P σ r) (fun y => P.mChain σ y r a) x
  rw [mbIsoM_evol P hc.stoch hc.zpos.ne' hr σ a x]
  ring

include hA hc in

/-- **The isotropic `M`-bounds** (under `Split.DerivStatement`, through `MBAlg`, and the initial
bound `hInit` for the entry `a`): for `k = n+3`, a pattern
`σ`, `AvB(k, A_k)`, `IsoB(n', I n')` for `3 ≤ n' ≤ k-1`, and `t ∈ [0,1]`,
`|(M^σ_t(x'))_{aa}| ≤ I_k √(ℓ_tη_t) s^iso_{k,t}(a,x',a)`, `I_k = C_P^{k-1}(B₀ + Λ F^iso_k)`
(`mbIsoK`), `Λ = c_m⁻¹ log((C₀+1)N)`.
-/
theorem mbBounds_iso {n : ℕ} (σ : Fin (n + 3) → Bool) {Ak : ℝ} (hAk0 : 0 ≤ Ak)
    (hAk : MBAvB P (n + 3) Ak) (I : ℕ → ℝ) (hI0 : ∀ n, 0 ≤ I n)
    (hIso : ∀ n', 3 ≤ n' → n' + 1 ≤ n + 3 → MBIsoB P n' (I n')) {B₀ : ℝ} (hB₀ : 0 ≤ B₀)
    (a : Fin (m * W))
    (hInit : ∀ y, ‖P.mChain σ y 0 a‖ ≤ B₀ * (Real.sqrt (P.lEta 0) * P.sIso a a y 0)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (x : Fin (n + 3) → Fin (m * W)) :
    ‖P.mChain σ x t a‖ ≤
      mbIsoK d (mbLambda d (m * W)) (n + 3) Ak I B₀ * (Real.sqrt (P.lEta t) * P.sIso a a x t) := by
  have hΛ0 : 0 ≤ mbLambda d (m * W) :=
    mbLambda_nonneg d (Nat.mul_pos (by have := hc.hm; omega) hc.hW)
  have hP := mbFIsoPairSum_nonneg (k := n + 3) hI0
  have hCP := kernelActionConst_ge_one d
  have hCwc := d.one_le_Cwc
  have hCK := (vsCK_pos d).le
  have hC0 := d.C0_ge_one
  have hFc : 0 ≤ mbFIsoC d (n + 3) Ak I := by
    unfold mbFIsoC
    exact add_nonneg (mul_nonneg (by linarith) hP)
      (mul_nonneg (by nlinarith) hAk0)
  have hGc := mb_contOn_GIso hA hc σ a
  have hint : IntervalIntegrable (fun s => propOp (goodProp P.S P.z (propFactorIso σ) s t)
      (mbGIso P σ a s)) volume 0 t := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le ht.1]
    have hsub : Icc (0 : ℝ) t ⊆ Icc 0 1 := Icc_subset_Icc le_rfl ht.2
    refine ContinuousOn.clm_apply (fun s hs => ?_) (hGc.mono hsub)
    exact (hasDerivAt_propOp_vsTensorProp_left hc.stoch (fun _ => mb_norm_mu1_lt hc.zpos _)
      (fun _ => mb_norm_mu2_lt hc.zpos _) hs.1 (hs.2.trans ht.2) ht.1 ht.2
      ).continuousAt.continuousWithinAt
  have hdu := vsTensorProp_duhamel (X := fun r => fun x => P.mChain σ x r a) hc.stoch
    (fun _ => mb_norm_mu1_lt hc.zpos _) (fun _ => mb_norm_mu2_lt hc.zpos _) le_rfl zero_le_one
    ht.1 ht.2 (fun s hs => by
      rw [uIcc_of_le ht.1] at hs
      exact mb_hasDerivAt_Y_iso hA hc σ a ⟨hs.1, hs.2.trans ht.2⟩) hint
  have hdux := congrFun hdu x
  have hL0 := (hc.inputs (t := 0) ⟨le_rfl, zero_le_one⟩).lEta_pos
  have hlast := propFactorIso_last (n := n + 1) σ
  have hsq : ∀ {s : ℝ}, 0 < P.lEta s →
      Real.sqrt (P.lEta s) * Real.sqrt (P.lEta t / P.lEta s) = Real.sqrt (P.lEta t) := by
    intro s hLs
    rw [← Real.sqrt_mul hLs.le]
    congr 1
    field_simp
  have h0 : ‖propOp (goodProp P.S P.z (propFactorIso σ) 0 t) (fun x => P.mChain σ x 0 a) x‖ ≤
      kernelActionConst d ^ (n + 2) * B₀ * (Real.sqrt (P.lEta t) * P.sIso a a x t) := by
    have h := goodProps_iso_apply d hc.hm hc.hW P hc.hPW hc.hPD hc.hz le_rfl ht.1 ht.2
      (propFactorIso σ) hlast a a (mul_nonneg hB₀ (Real.sqrt_nonneg _))
      (fun x => P.mChain σ x 0 a) (fun y => (hInit y).trans (le_of_eq (by ring))) x
    rw [← hc.hPS] at h
    refine h.trans (le_of_eq ?_)
    rw [← hsq hL0]
    ring
  have hb : ∀ s ∈ Icc (0 : ℝ) t, ‖propOp (goodProp P.S P.z (propFactorIso σ) s t)
      (mbGIso P σ a s) x‖ ≤
      (kernelActionConst d ^ (n + 2) * mbFIsoC d (n + 3) Ak I *
        (Real.sqrt (P.lEta t) * P.sIso a a x t)) * (vsHeight P.z s)⁻¹ := by
    intro s hs
    have hs1 : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans ht.2⟩
    have hins := hc.inputs hs1
    have hηs := hins.height_pos
    have hLs := hins.lEta_pos
    have hF := mbGIso_bound hc σ hs1 hAk0 hAk I hI0 hIso a
    have hφ : 0 ≤ mbFIsoC d (n + 3) Ak I / vsHeight P.z s * Real.sqrt (P.lEta s) :=
      mul_nonneg (div_nonneg hFc hηs.le) (Real.sqrt_nonneg _)
    have h := goodProps_iso_apply d hc.hm hc.hW P hc.hPW hc.hPD hc.hz hs.1 hs.2 ht.2
      (propFactorIso σ) hlast a a hφ (mbGIso P σ a s)
      (fun y => (hF y).trans (le_of_eq (by ring))) x
    rw [← hc.hPS] at h
    refine h.trans (le_of_eq ?_)
    rw [← hsq hLs]
    field_simp
  have hI := mb_norm_integral_le hc.zpos ht hint x hb
  have hΛ : ∫ s in (0 : ℝ)..t, (vsHeight P.z s)⁻¹ ≤ mbLambda d (m * W) :=
    (vsIntRules (Nat.mul_pos (by have := hc.hm; omega) hc.hW) hc.hW d.delta0_pos.le
      d.kappa_pos (by linarith [d.C0_ge_one]) hc.hz ht.1 ht.2 one_pos).1
  have hLx : 0 ≤ Real.sqrt (P.lEta t) * P.sIso a a x t :=
    mul_nonneg (Real.sqrt_nonneg _) (mb_sIso_nonneg P (hc.inputs ht) _ _ _)
  have hc0 : 0 ≤ kernelActionConst d ^ (n + 2) * mbFIsoC d (n + 3) Ak I *
      (Real.sqrt (P.lEta t) * P.sIso a a x t) :=
    mul_nonneg (mul_nonneg (pow_nonneg (by linarith) _) hFc) hLx
  rw [hdux, Pi.add_apply]
  calc _ ≤ kernelActionConst d ^ (n + 2) * B₀ * (Real.sqrt (P.lEta t) * P.sIso a a x t) +
        kernelActionConst d ^ (n + 2) * mbFIsoC d (n + 3) Ak I *
          (Real.sqrt (P.lEta t) * P.sIso a a x t) * ∫ s in (0 : ℝ)..t, (vsHeight P.z s)⁻¹ :=
      (norm_add_le _ _).trans (add_le_add h0 hI)
    _ ≤ kernelActionConst d ^ (n + 2) * B₀ * (Real.sqrt (P.lEta t) * P.sIso a a x t) +
        kernelActionConst d ^ (n + 2) * mbFIsoC d (n + 3) Ak I *
          (Real.sqrt (P.lEta t) * P.sIso a a x t) * mbLambda d (m * W) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hΛ hc0)
    _ = _ := by
      unfold mbIsoK
      rw [show n + 3 - 1 = n + 2 by omega]
      ring

end VS

end BlockBand.Native.ErdosRiabov.MBound
