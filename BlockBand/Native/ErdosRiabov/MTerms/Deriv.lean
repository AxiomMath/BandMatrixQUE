module

public import BlockBand.Native.ErdosRiabov.MTerms.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Complex.RealDeriv

/-!
# Deterministic `M`-terms: the `σ`-derivative

Proves `Split.DerivStatement`, the variance-scaling form of the Erdős–Riabov derivative formula
for `M`-terms (arXiv 2506.06441v1) without the Ornstein–Uhlenbeck term `k/2 · M`: at fixed `m`,
`d/dσ M_{[1,k]} = ∑_{1 ≤ i < j ≤ k} ∑_q (M_{[i,j]})_q M^{(q)}_{[1,i],[j,k]}`.

Setting: `n : ℕ`, a profile `S` with `ProfileHyp S`, `σ ∈ [0,1]`, spectral data `m : ℕ → ℂ`
with `‖m i‖ < 1` for all `i`, diagonal observables `A : ℕ → Fin n → ℂ`, `k ≥ 1`. The derivative
is the two-sided real derivative `HasDerivAt` at `σ` (also at `σ ∈ {0, 1}`: the stability
operators stay invertible near `σ`, `MTerms.Basic.eventually_isUnit_det`).

Main declarations.
* `Deriv.chainM_rec`: the `M`-level recursion (no division, no hypotheses)
  `M_{[p,q]} = m_p K_{pq} (A_p M_{[p+1,q]} + σ ∑_{p<i<q} S[M_{[p,i]}] M_{[i,q]})`.
* Glued chains: `Deriv.chainM_glue_left` (windows ending at `r ≤ i` are original windows),
  `Deriv.chainM_glue_right` (windows starting at `r > i` are shifted original windows),
  `Deriv.chainM_glue_rec` (the recursion of a glued window at its first index with these
  identifications).
* `Deriv.rhs σ S m A p q`: the right-hand side on the window `[p,q]`;
  `Deriv.rhs_step`: it satisfies the differentiated recursion (the regrouping
  `Deriv.regroup_one`, `Deriv.regroup_two`, `Deriv.regroup_three`).
* `Deriv.hasDerivAt_window`: `d/dσ M_{[p,q]} = rhs_{[p,q]}` for all `p, q` (vector form).
* `deriv_holds : DerivStatement` (the window `p = 1`, coordinate `a`).

Inputs: Mathlib; `BlockBand.Native.ErdosRiabov.Split.MTermsStatement`;
`BlockBand.Native.ErdosRiabov.MTerms.Basic` (`chainTilde_of_lt`, `chainTilde_of_le`,
`chainM_eq_smul`, `chainM_self`, `chainM_congr`, `chainM_shift`, `norm_mul_lt_one_of_lt_one`,
`hasDerivAt_stabOp_mulVec_of_hasDerivAt`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.MTerms

open BlockBand.Native.ErdosRiabov.Split Matrix Finset

namespace Deriv

variable {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ} {σ : ℝ} {m : ℕ → ℂ} {A : ℕ → Fin n → ℂ}

/-!
### Elementary algebra
-/

/-- `S[c v] = c S[v]`. -/
theorem selfEnergy_smul (S : Matrix (Fin n) (Fin n) ℝ) (c : ℂ) (v : Fin n → ℂ) :
    selfEnergy S (c • v) = c • selfEnergy S v :=
  mulVec_smul _ _ _

/-- `S[∑ v_i] = ∑ S[v_i]`. -/
theorem selfEnergy_sum {ι : Type*} (S : Matrix (Fin n) (Fin n) ℝ) (s : Finset ι)
    (v : ι → Fin n → ℂ) : selfEnergy S (∑ i ∈ s, v i) = ∑ i ∈ s, selfEnergy S (v i) :=
  mulVec_sum _ _ _

/-- `S[u + v] = S[u] + S[v]`. -/
theorem selfEnergy_add (S : Matrix (Fin n) (Fin n) ℝ) (u v : Fin n → ℂ) :
    selfEnergy S (u + v) = selfEnergy S u + selfEnergy S v :=
  mulVec_add _ _ _

/-- `∑_x v_x S^x w = S[v] w` (symmetry of `S`). -/
theorem sum_smul_rowObs_mul (hS : ProfileHyp S) (v w : Fin n → ℂ) :
    ∑ x, v x • (rowObs S x * w) = selfEnergy S v * w := by
  funext a
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.mul_apply, rowObs, selfEnergy, mulVec,
    dotProduct, profileC_apply, smul_eq_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hS.symm x a]
  ring

/-- `S[v] · m_q = m_q S[v]` for the constant vector `m_q`. -/
theorem mul_const_eq_smul (v : Fin n → ℂ) (c : ℂ) : v * (fun _ => c) = c • v := by
  funext a
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- `(∏_{p}^{i} m) (∏_{i}^{q} m) = m_i ∏_{p}^{q} m` for `p ≤ i ≤ q`. -/
theorem prod_Icc_mul_prod_Icc (m : ℕ → ℂ) {p i q : ℕ} (hpi : p ≤ i) (hiq : i ≤ q) :
    (∏ r ∈ Icc p i, m r) * (∏ r ∈ Icc i q, m r) = m i * ∏ r ∈ Icc p q, m r := by
  have h1 : Icc p q = Icc p i ∪ Ioc i q := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hd : Disjoint (Icc p i) (Ioc i q) := by
    rw [Finset.disjoint_left]
    intro r h1 h2
    rw [Finset.mem_Icc] at h1
    rw [Finset.mem_Ioc] at h2
    omega
  rw [h1, Finset.prod_union hd, ← Finset.Ioc_insert_left hiq,
    Finset.prod_insert Finset.left_notMem_Ioc]
  ring

/-- `∏_{p}^{q} m = m_p ∏_{p+1}^{q} m` for `p ≤ q`. -/
theorem prod_Icc_eq_mul (m : ℕ → ℂ) {p q : ℕ} (hpq : p ≤ q) :
    ∏ r ∈ Icc p q, m r = m p * ∏ r ∈ Icc (p + 1) q, m r := by
  have h : Icc p q = insert p (Icc (p + 1) q) := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [h, Finset.prod_insert (by simp)]

/-!
### The `M`-level recursion
-/

/-- `M`-level recursion (no division): for `p < q`,
`M_{[p,q]} = m_p K_{pq} (A_p M_{[p+1,q]} + σ ∑_{p<i<q} S[M_{[p,i]}] M_{[i,q]})`. -/
theorem chainM_rec {p q : ℕ} (h : p < q) :
    chainM σ S m A p q = m p • (stabOp σ S (m p * m q) *ᵥ
      (A p * chainM σ S m A (p + 1) q +
        (σ : ℂ) • ∑ i ∈ Ioo p q, selfEnergy S (chainM σ S m A p i) * chainM σ S m A i q)) := by
  rw [chainM_eq_smul, chainTilde_of_lt h, ← mulVec_smul, ← mulVec_smul]
  congr 1
  rw [smul_add, smul_add, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum,
    prod_Icc_eq_mul m h.le, chainM_eq_smul, mul_smul_comm, smul_smul]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_Ioo] at hi
  rw [chainM_eq_smul, chainM_eq_smul, selfEnergy_smul, smul_mul_smul_comm,
    prod_Icc_mul_prod_Icc m hi.1.le hi.2.le, prod_Icc_eq_mul m h.le]
  simp only [smul_smul]
  congr 1
  ring

/-!
### Glued chains
-/

/-- `gm_t = m_t` for `t ≤ i`. -/
theorem glueChain_of_le {i j t : ℕ} (h : t ≤ i) : glueChain i j m t = m t := by
  unfold glueChain
  exact ite_eq_left h

/-- `gm_t = m_{t + (j-i-1)}` for `i < t`, `i < j`. -/
theorem glueChain_of_gt {i j t : ℕ} (hij : i < j) (h : i < t) :
    glueChain i j m t = m (t + (j - i - 1)) := by
  unfold glueChain
  rw [ite_eq_right (by omega), show t + j - i - 1 = t + (j - i - 1) by omega]

/-- `gA_t = A_t` for `t < i`. -/
theorem glueObs_of_lt {i j t : ℕ} (B : Fin n → ℂ) (h : t < i) : glueObs i j B A t = A t := by
  unfold glueObs
  exact ite_eq_left h

/-- `gA_i = B`. -/
theorem glueObs_self {i j : ℕ} (B : Fin n → ℂ) : glueObs i j B A i = B := by
  unfold glueObs
  rw [ite_eq_right (lt_irrefl i), ite_eq_left rfl]

/-- `gA_t = A_{t + (j-i-1)}` for `i < t`, `i < j`. -/
theorem glueObs_of_gt {i j t : ℕ} (B : Fin n → ℂ) (hij : i < j) (h : i < t) :
    glueObs i j B A t = A (t + (j - i - 1)) := by
  unfold glueObs
  rw [ite_eq_right (by omega), ite_eq_right (by omega),
    show t + j - i - 1 = t + (j - i - 1) by omega]

/-- Glued windows ending at or before the glue point are original windows. -/
theorem chainM_glue_left {i j p r : ℕ} (B : Fin n → ℂ) (hr : r ≤ i) :
    chainM σ S (glueChain i j m) (glueObs i j B A) p r = chainM σ S m A p r :=
  chainM_congr (fun _ _ ht => glueChain_of_le (by omega))
    (fun _ _ ht => glueObs_of_lt B (by omega))

/-- Glued windows starting after the glue point are shifted original windows. -/
theorem chainM_glue_right {i j r r' : ℕ} (B : Fin n → ℂ) (hij : i < j) (hr : i < r) :
    chainM σ S (glueChain i j m) (glueObs i j B A) r r' =
      chainM σ S m A (r + (j - i - 1)) (r' + (j - i - 1)) := by
  rw [← chainM_shift]
  exact chainM_congr (fun _ ht _ => glueChain_of_gt hij (by omega))
    (fun _ ht _ => glueObs_of_gt B hij (by omega))

/-- Recursion of a glued window `[p, q - j + i + 1]` (`p ≤ i < j ≤ q`) at its first index, with
the sub-windows identified: those ending at `r ≤ i` are original windows `M_{[p,r]}`, those
starting at `r ≥ i + 1` are the original windows `M_{[r + j - i - 1, q]}`. -/
theorem chainM_glue_rec {i j p q : ℕ} (B : Fin n → ℂ) (hpi : p ≤ i) (hij : i < j)
    (hjq : j ≤ q) :
    chainM σ S (glueChain i j m) (glueObs i j B A) p (q - j + i + 1) =
      m p • (stabOp σ S (m p * m q) *ᵥ
        (glueObs i j B A p *
            chainM σ S (glueChain i j m) (glueObs i j B A) (p + 1) (q - j + i + 1) +
          (σ : ℂ) • ∑ r ∈ Ioc p i, selfEnergy S (chainM σ S m A p r) *
            chainM σ S (glueChain i j m) (glueObs i j B A) r (q - j + i + 1) +
          (σ : ℂ) • ∑ r ∈ Ico j q, selfEnergy S
            (chainM σ S (glueChain i j m) (glueObs i j B A) p (r - j + i + 1)) *
              chainM σ S m A r q)) := by
  rw [chainM_rec (by omega : p < q - j + i + 1), glueChain_of_le hpi,
    glueChain_of_gt hij (by omega : i < q - j + i + 1),
    show q - j + i + 1 + (j - i - 1) = q by omega,
    add_assoc (glueObs i j B A p * _), ← smul_add]
  congr 4
  have hsplit : Ioo p (q - j + i + 1) = Ioc p i ∪ Ioo i (q - j + i + 1) := by
    ext r
    simp only [Finset.mem_Ioo, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hd : Disjoint (Ioc p i) (Ioo i (q - j + i + 1)) := by
    rw [Finset.disjoint_left]
    intro r h1 h2
    rw [Finset.mem_Ioc] at h1
    rw [Finset.mem_Ioo] at h2
    omega
  have hmap : Ico j q = (Ioo i (q - j + i + 1)).map (addRightEmbedding (j - i - 1)) := by
    rw [Finset.map_add_right_Ioo]
    ext r
    simp only [Finset.mem_Ico, Finset.mem_Ioo]
    omega
  rw [hsplit, Finset.sum_union hd, hmap, Finset.sum_map]
  congr 1
  · refine Finset.sum_congr rfl fun r hr => ?_
    rw [Finset.mem_Ioc] at hr
    rw [chainM_glue_left B hr.2]
  · refine Finset.sum_congr rfl fun r hr => ?_
    rw [Finset.mem_Ioo] at hr
    rw [addRightEmbedding_apply, show r + (j - i - 1) - j + i + 1 = r by omega,
      chainM_glue_right B hij hr.1, show q - j + i + 1 + (j - i - 1) = q by omega]

/-!
### The right-hand side on a window
-/

/-- The glued chain `M^{(x)}_{[1,i],[j,k]}` restricted to the window `[p, r]`. -/
def glued (σ : ℝ) (S : Matrix (Fin n) (Fin n) ℝ) (m : ℕ → ℂ) (A : ℕ → Fin n → ℂ)
    (i j : ℕ) (x : Fin n) (p r : ℕ) : Fin n → ℂ :=
  chainM σ S (glueChain i j m) (glueObs i j (rowObs S x) A) p r

/-- The right-hand side of the derivative formula on the window `[p, q]`:
`∑_{p ≤ i < j ≤ q} ∑_x (M_{[i,j]})_x M^{(x)}_{[p,i],[j,q]}`. -/
def rhs (σ : ℝ) (S : Matrix (Fin n) (Fin n) ℝ) (m : ℕ → ℂ) (A : ℕ → Fin n → ℂ)
    (p q : ℕ) : Fin n → ℂ :=
  ∑ i ∈ Icc p q, ∑ j ∈ Ioc i q, ∑ x, chainM σ S m A i j x • glued σ S m A i j x p (q - j + i + 1)

/-- The term `i = q` of `rhs` is an empty sum. -/
theorem rhs_Ico (p q : ℕ) :
    rhs σ S m A p q =
      ∑ i ∈ Ico p q, ∑ j ∈ Ioc i q, ∑ x,
        chainM σ S m A i j x • glued σ S m A i j x p (q - j + i + 1) := by
  rw [rhs]
  symm
  refine Finset.sum_subset Finset.Ico_subset_Icc_self fun i hi hni => ?_
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [Finset.mem_Icc] at hi
  rw [Finset.mem_Ico] at hni
  rw [Finset.mem_Ioc] at hj
  omega

/-- First part of the regrouping: the `A_p`/`S^x` terms. -/
theorem regroup_one (hS : ProfileHyp S) {p q : ℕ} (h : p < q) :
    ∑ i ∈ Ico p q, ∑ j ∈ Ioc i q, ∑ x, chainM σ S m A i j x •
        (glueObs i j (rowObs S x) A p * glued σ S m A i j x (p + 1) (q - j + i + 1)) =
      m q • selfEnergy S (chainM σ S m A p q) +
        ∑ i ∈ Ioo p q, selfEnergy S (chainM σ S m A p i) * chainM σ S m A i q +
        A p * rhs σ S m A (p + 1) q := by
  rw [← Finset.Ioo_insert_left h, Finset.sum_insert Finset.left_notMem_Ioo]
  have hp : ∑ j ∈ Ioc p q, ∑ x, chainM σ S m A p j x •
        (glueObs p j (rowObs S x) A p * glued σ S m A p j x (p + 1) (q - j + p + 1)) =
      ∑ j ∈ Ioc p q, selfEnergy S (chainM σ S m A p j) * chainM σ S m A j q := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_Ioc] at hj
    have hx : ∀ x, glueObs p j (rowObs S x) A p * glued σ S m A p j x (p + 1) (q - j + p + 1) =
        rowObs S x * chainM σ S m A j q := by
      intro x
      rw [glueObs_self, glued, chainM_glue_right _ hj.1 (Nat.lt_succ_self p),
        show p + 1 + (j - p - 1) = j by omega, show q - j + p + 1 + (j - p - 1) = q by omega]
    simp only [hx]
    exact sum_smul_rowObs_mul hS _ _
  have hq : ∑ j ∈ Ioc p q, selfEnergy S (chainM σ S m A p j) * chainM σ S m A j q =
      m q • selfEnergy S (chainM σ S m A p q) +
        ∑ i ∈ Ioo p q, selfEnergy S (chainM σ S m A p i) * chainM σ S m A i q := by
    rw [← Finset.Ioo_insert_right h, Finset.sum_insert Finset.right_notMem_Ioo, chainM_self,
      mul_const_eq_smul]
  have hrest : ∑ i ∈ Ioo p q, ∑ j ∈ Ioc i q, ∑ x, chainM σ S m A i j x •
        (glueObs i j (rowObs S x) A p * glued σ S m A i j x (p + 1) (q - j + i + 1)) =
      A p * rhs σ S m A (p + 1) q := by
    rw [rhs_Ico, Finset.Ico_add_one_left_eq_Ioo, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_Ioo] at hi
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [glueObs_of_lt _ hi.1, mul_smul_comm]
  rw [hp, hq, hrest]

/-- Second part of the regrouping: the terms `S[M_{[p,r]}] M^{(x)}_{[r,i],[j,q]}`. -/
theorem regroup_two {p q : ℕ} :
    ∑ i ∈ Ico p q, ∑ j ∈ Ioc i q, ∑ x, chainM σ S m A i j x •
        ((σ : ℂ) • ∑ r ∈ Ioc p i, selfEnergy S (chainM σ S m A p r) *
          glued σ S m A i j x r (q - j + i + 1)) =
      (σ : ℂ) • ∑ r ∈ Ioo p q, selfEnergy S (chainM σ S m A p r) * rhs σ S m A r q := by
  simp only [rhs_Ico, Finset.smul_sum, Finset.mul_sum, mul_smul_comm, smul_smul]
  symm
  refine (Finset.sum_comm' (t' := Ico p q) (s' := fun i => Ioc p i) ?_).trans ?_
  · intro r i
    simp only [Finset.mem_Ioo, Finset.mem_Ico, Finset.mem_Ioc]
    omega
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun r _ => ?_
  rw [mul_comm]

/-- Third part of the regrouping: the terms `S[M^{(x)}_{[p,i],[j,r]}] M_{[r,q]}`. -/
theorem regroup_three {p q : ℕ} :
    ∑ i ∈ Ico p q, ∑ j ∈ Ioc i q, ∑ x, chainM σ S m A i j x •
        ((σ : ℂ) • ∑ r ∈ Ico j q, selfEnergy S (glued σ S m A i j x p (r - j + i + 1)) *
          chainM σ S m A r q) =
      (σ : ℂ) • ∑ r ∈ Ioo p q, selfEnergy S (rhs σ S m A p r) * chainM σ S m A r q := by
  simp only [rhs_Ico, selfEnergy_sum, selfEnergy_smul, Finset.smul_sum, Finset.sum_mul,
    smul_mul_assoc, smul_smul]
  symm
  refine (Finset.sum_comm' (t' := Ico p q) (s' := fun i => Ioo i q) ?_).trans ?_
  · intro r i
    simp only [Finset.mem_Ioo, Finset.mem_Ico]
    omega
  refine Finset.sum_congr rfl fun i _ => ?_
  refine (Finset.sum_comm' (t' := Ioc i q) (s' := fun j => Ico j q) ?_).trans ?_
  · intro r j
    simp only [Finset.mem_Ioo, Finset.mem_Ico, Finset.mem_Ioc]
    omega
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun r _ => ?_
  rw [mul_comm]

/-- The right-hand side satisfies the differentiated recursion: for `p < q`,
`rhs_{[p,q]} = m_p K_{pq} (m_q S[M_{[p,q]}] + A_p rhs_{[p+1,q]} + ∑_i S[M_{[p,i]}] M_{[i,q]}
  + σ ∑_i (S[rhs_{[p,i]}] M_{[i,q]} + S[M_{[p,i]}] rhs_{[i,q]}))`. -/
theorem rhs_step (hS : ProfileHyp S) {p q : ℕ} (h : p < q) :
    rhs σ S m A p q = m p • (stabOp σ S (m p * m q) *ᵥ
      (m q • selfEnergy S (chainM σ S m A p q) + ∑ i ∈ Ioo p q,
          selfEnergy S (chainM σ S m A p i) * chainM σ S m A i q +
        A p * rhs σ S m A (p + 1) q +
        (σ : ℂ) • ∑ i ∈ Ioo p q, (selfEnergy S (rhs σ S m A p i) * chainM σ S m A i q +
          selfEnergy S (chainM σ S m A p i) * rhs σ S m A i q))) := by
  have hG : ∀ i ∈ Ico p q, ∀ j ∈ Ioc i q, ∀ x : Fin n,
      glued σ S m A i j x p (q - j + i + 1) =
        m p • (stabOp σ S (m p * m q) *ᵥ
          (glueObs i j (rowObs S x) A p * glued σ S m A i j x (p + 1) (q - j + i + 1) +
            (σ : ℂ) • ∑ r ∈ Ioc p i, selfEnergy S (chainM σ S m A p r) *
              glued σ S m A i j x r (q - j + i + 1) +
            (σ : ℂ) • ∑ r ∈ Ico j q, selfEnergy S (glued σ S m A i j x p (r - j + i + 1)) *
              chainM σ S m A r q)) := by
    intro i hi j hj x
    rw [Finset.mem_Ico] at hi
    rw [Finset.mem_Ioc] at hj
    exact chainM_glue_rec _ hi.1 hj.1 hj.2
  rw [rhs_Ico]
  rw [Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj =>
    Finset.sum_congr rfl fun x _ => by rw [hG i hi j hj x]]
  simp only [smul_comm _ (m p), ← mulVec_smul, ← Finset.smul_sum, ← mulVec_sum]
  congr 2
  simp only [smul_add, Finset.sum_add_distrib]
  rw [regroup_one hS h, regroup_two, regroup_three]
  abel

/-!
### Derivatives
-/

/-- `d/dσ S[v(σ)] = S[v'(σ)]`. -/
theorem hasDerivAt_selfEnergy {v : ℝ → Fin n → ℂ} {v' : Fin n → ℂ} (hv : HasDerivAt v v' σ) :
    HasDerivAt (fun s => selfEnergy S (v s)) (selfEnergy S v') σ := by
  rw [hasDerivAt_pi]
  intro a
  have h := HasDerivAt.fun_sum (u := Finset.univ)
    fun b _ => HasDerivAt.const_mul (profileC S a b) (hasDerivAt_pi.mp hv b)
  simpa only [selfEnergy, mulVec, dotProduct] using h

/-- Window form of the derivative formula: for all `p, q`,
`d/dσ M_{[p,q]} = ∑_{p ≤ i < j ≤ q} ∑_x (M_{[i,j]})_x M^{(x)}_{[p,i],[j,q]}`. -/
theorem hasDerivAt_window (hS : ProfileHyp S) (hσ : σ ∈ Set.Icc (0 : ℝ) 1)
    (hm : ∀ i, ‖m i‖ < 1) (p q : ℕ) :
    HasDerivAt (fun s : ℝ => chainM s S m A p q) (rhs σ S m A p q) σ := by
  induction hd : q - p using Nat.strong_induction_on generalizing p q with
  | _ d ih =>
  rcases lt_or_ge p q with h | h
  · have ih' : ∀ p' q', q' - p' < q - p →
        HasDerivAt (fun s : ℝ => chainM s S m A p' q') (rhs σ S m A p' q') σ :=
      fun p' q' hlt => ih (q' - p') (by omega) p' q' rfl
    have h1 := ih' (p + 1) q (by omega)
    have hA : HasDerivAt (fun s : ℝ => A p * chainM s S m A (p + 1) q)
        (A p * rhs σ S m A (p + 1) q) σ := HasDerivAt.const_mul (A p) h1
    have hsum : HasDerivAt
        (fun s : ℝ => ∑ i ∈ Ioo p q, selfEnergy S (chainM s S m A p i) * chainM s S m A i q)
        (∑ i ∈ Ioo p q, (selfEnergy S (rhs σ S m A p i) * chainM σ S m A i q +
          selfEnergy S (chainM σ S m A p i) * rhs σ S m A i q)) σ := by
      refine HasDerivAt.fun_sum fun i hi => ?_
      rw [Finset.mem_Ioo] at hi
      exact HasDerivAt.fun_mul (hasDerivAt_selfEnergy (ih' p i (by omega))) (ih' i q (by omega))
    have hs : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 σ := by
      simpa using HasDerivAt.ofReal_comp (hasDerivAt_id σ)
    have hX := HasDerivAt.fun_add hA (HasDerivAt.fun_smul hs hsum)
    have hK := HasDerivAt.fun_const_smul (m p) (hasDerivAt_stabOp_mulVec_of_hasDerivAt hS hσ
      (norm_mul_lt_one_of_lt_one (hm p) (hm q)) hX)
    have hfun : (fun s : ℝ => chainM s S m A p q) = fun s : ℝ => m p •
        (stabOp s S (m p * m q) *ᵥ (A p * chainM s S m A (p + 1) q + (s : ℂ) •
          ∑ i ∈ Ioo p q, selfEnergy S (chainM s S m A p i) * chainM s S m A i q)) :=
      funext fun s => chainM_rec h
    rw [hfun]
    refine HasDerivAt.congr_deriv hK ?_
    rw [rhs_step hS h, chainM_rec h, ← mulVec_add, selfEnergy_smul, smul_smul, one_smul]
    congr 2
    rw [selfEnergy, mul_comm (m q), ← smul_mulVec]
    abel
  · have hfun : (fun s : ℝ => chainM s S m A p q) =
        fun _ => (∏ i ∈ Icc p q, m i) • (fun _ : Fin n => (1 : ℂ)) := by
      funext s
      rw [chainM_eq_smul, chainTilde_of_le h]
    have hz : rhs σ S m A p q = 0 := by
      refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_
      rw [Finset.mem_Icc] at hi
      rw [Finset.mem_Ioc] at hj
      omega
    rw [hfun, hz]
    exact hasDerivAt_const σ _

end Deriv

/-- `DerivStatement` (the derivative formula without the Ornstein–Uhlenbeck term `k/2 · M`):
`d/dσ M_{[1,k]} = ∑_{1 ≤ i < j ≤ k} ∑_q (M_{[i,j]})_q M^{(q)}_{[1,i],[j,k]}`. -/
theorem deriv_holds : DerivStatement := by
  intro n S hS σ hσ m hm A k _ a
  have h := hasDerivAt_pi.mp (Deriv.hasDerivAt_window (A := A) hS hσ hm 1 k) a
  convert h using 1
  simp only [Deriv.rhs, Deriv.glued, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

end BlockBand.Native.ErdosRiabov.MTerms
