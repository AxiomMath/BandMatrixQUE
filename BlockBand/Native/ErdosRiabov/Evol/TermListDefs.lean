module

public import BlockBand.Native.ErdosRiabov.Evol.TermListAlg

/-!
# Term families of the forcing: definitions and the pair expansion

The term families of the forcing and the expansion of the `G`-drift minus the `M`-derivative
into them.

For a pair of 0-based slots `i < j` and a site `q` (1-based `[i+1, j+1]` in Erdős–Riabov):
* `aG = (G_{[i,j]})_qq`, `aM = (M^{(t)}_{[i,j]})_qq` (`mSeg`);
* av: `bG = Tr[G_{[1,i]} S^q G_{[j,k]} S^{x_k}]`, `bM = Tr[M^{(q)}_{[1,i],[j,k]} S^{x_k}]`;
  iso: `bG = (G_{[1,i]} S^q G_{[j,k]})_{ab}`, `bM = δ_ab (M^{(q)}_{[1,i],[j,k]})_{aa}`;
  `M^{(q)}_{[1,i],[j,k]} = M(z_1, S^{x_1}, …, z_i, S^q, z_j, S^{x_j}, …, z_k)` (`mGlue`, with the
  observable `S^{x_j}` after `z_j`, i.e. `Split.glueObs`).
The families (the Ornstein–Uhlenbeck term `k/2` is absent):
* (F1) `famF1 = ∑_j G_{[1,j]} 𝒮[G_j - m_j] G_{[j,k]} B_{k-1}` (matrix; av: trace, iso: entry);
* (FQ) `famQ = ∑_{i<j} ∑_q (aG - aM)(bG - bM)`;
* (FM) `famM1 = ∑_{i<j, j-i ≤ k-2} ∑_q (aG - aM) bM`, `famM2 = ∑_{i<j, j-i ≥ 2} ∑_q aM (bG - bM)`;
* (L) `lAdj = ∑_{j = i+1} ∑_q aM (bG - bM)` and `lCyc = ∑_{(i,j) = (1,k)} ∑_q (aG - aM) bM`.
`dGav_split`/`dGiso_split`: the `G`-drift is `famF1 + ∑_{i<j} ∑_q aG bG` (`𝒮[X] = ∑_q X_qq S^q`);
`dMav_split`/`dMiso_split`: the `M`-derivative is `∑_{i<j} ∑_q aM bM` (the explicit sum of
`Split.DerivStatement`'s right-hand side; no `DerivStatement` is used);
`pair_expand`: `∑ (aG bG - aM bM) = famQ + famM1 + famM2 + lAdj + lCyc`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Evol

open Matrix Finset Function
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Chains
open BlockBand.Native.ErdosRiabov.Psi

variable {N k : ℕ}

/-!
### Generic pair families
-/

section Families

variable (aG aM bG bM : Fin k → Fin k → Fin N → ℂ)

/-- (FQ) `∑_{i<j} ∑_q (aG - aM)(bG - bM)`. -/
def famQ : ℂ := ∑ j : Fin k, ∑ i with i < j, ∑ q, (aG i j q - aM i j q) * (bG i j q - bM i j q)

/-- (FM, first) `∑_{i<j, j-i ≤ k-2} ∑_q (aG - aM) bM`. -/
def famM1 : ℂ :=
  ∑ j : Fin k, ∑ i with i < j,
    if (j : ℕ) - i ≤ k - 2 then ∑ q, (aG i j q - aM i j q) * bM i j q else 0

/-- (FM, second) `∑_{i<j, j-i ≥ 2} ∑_q aM (bG - bM)`. -/
def famM2 : ℂ :=
  ∑ j : Fin k, ∑ i with i < j, if 2 ≤ (j : ℕ) - i then ∑ q, aM i j q * (bG i j q - bM i j q) else 0

/-- (L, adjacent pairs) `∑_{j = i+1} ∑_q aM (bG - bM)`. -/
def lAdj : ℂ :=
  ∑ j : Fin k, ∑ i with i < j, if (j : ℕ) = i + 1 then ∑ q, aM i j q * (bG i j q - bM i j q) else 0

/-- (L, the pair `(1,k)`) `∑_q (aG - aM) bM`. -/
def lCyc : ℂ :=
  ∑ j : Fin k, ∑ i with i < j,
    if (j : ℕ) - i = k - 1 then ∑ q, (aG i j q - aM i j q) * bM i j q else 0

theorem split_two {c d : Prop} [Decidable c] [Decidable d] (h : c ↔ ¬d) (X : ℂ) :
    X = (if c then X else 0) + (if d then X else 0) := by
  by_cases hc : c
  · simp [hc, h.mp hc]
  · have hd : d := by by_contra hd; exact hc (h.mpr hd)
    simp [hc, hd]

/-- **Pair expansion**: `AB - A_M B_M = (A - A_M)(B - B_M) + (A - A_M) B_M + A_M (B - B_M)`,
sorted by `j - i`. -/
theorem pair_expand :
    ∑ j : Fin k, ∑ i with i < j, ∑ q, (aG i j q * bG i j q - aM i j q * bM i j q) =
      famQ aG aM bG bM + famM1 aG aM bM + famM2 aM bG bM + lAdj aM bG bM + lCyc aG aM bM := by
  have hterm : ∀ j : Fin k, ∀ i ∈ (Finset.univ.filter fun i : Fin k => i < j),
      ∑ q, (aG i j q * bG i j q - aM i j q * bM i j q) =
        ∑ q, (aG i j q - aM i j q) * (bG i j q - bM i j q) +
        (if (j : ℕ) - i ≤ k - 2 then ∑ q, (aG i j q - aM i j q) * bM i j q else 0) +
        (if 2 ≤ (j : ℕ) - i then ∑ q, aM i j q * (bG i j q - bM i j q) else 0) +
        (if (j : ℕ) = i + 1 then ∑ q, aM i j q * (bG i j q - bM i j q) else 0) +
        (if (j : ℕ) - i = k - 1 then ∑ q, (aG i j q - aM i j q) * bM i j q else 0) := by
    intro j i hi
    have hij : i < j := (Finset.mem_filter.mp hi).2
    have hij' : (i : ℕ) < j := hij
    have hjk : (j : ℕ) < k := j.isLt
    have e1 := split_two (c := (j : ℕ) - i ≤ k - 2) (d := (j : ℕ) - i = k - 1) (by omega)
      (∑ q, (aG i j q - aM i j q) * bM i j q)
    have e2 := split_two (c := 2 ≤ (j : ℕ) - i) (d := (j : ℕ) = i + 1) (by omega)
      (∑ q, aM i j q * (bG i j q - bM i j q))
    have e0 : ∑ q, (aG i j q * bG i j q - aM i j q * bM i j q) =
        ∑ q, (aG i j q - aM i j q) * (bG i j q - bM i j q) +
          ∑ q, (aG i j q - aM i j q) * bM i j q + ∑ q, aM i j q * (bG i j q - bM i j q) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun q _ => by ring
    linear_combination e0 + e1 + e2
  rw [Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl (hterm j)]
  simp only [Finset.sum_add_distrib]
  rfl

end Families

/-!
### The objects of the pattern
-/

section Pattern

variable (P : PsiData N) (σ : Fin k → Bool) (x : Fin k → Fin N) (t : ℝ)
  (H : Matrix (Fin N) (Fin N) ℂ)

/-- `M^{(t)}_{[i+1, j+1]}` (diagonal). -/
def mSeg (i j : Fin k) : Fin N → ℂ :=
  Split.chainM t P.S (patM P.z σ) (obsSeq P.S x) ((i : ℕ) + 1) ((j : ℕ) + 1)

/-- `M^{(q)}_{[1,i+1],[j+1,k]}` (with the observable `S^{x_j}` after `z_j`). -/
def mGlue (i j : Fin k) (q : Fin N) : Fin N → ℂ :=
  Split.chainM t P.S (Split.glueChain ((i : ℕ) + 1) ((j : ℕ) + 1) (patM P.z σ))
    (Split.glueObs ((i : ℕ) + 1) ((j : ℕ) + 1) (Split.rowObs P.S q) (obsSeq P.S x)) 1
    (k - ((j : ℕ) + 1) + ((i : ℕ) + 1) + 1)

/-- `aG = (G_{[i,j]})_qq` for slots `B`. -/
def aG (B : Fin k → Matrix (Fin N) (Fin N) ℂ) (i j : Fin k) (q : Fin N) : ℂ :=
  gSeg B (slotsH P.z σ t H) i j q q

/-- `aM = (M_{[i,j]})_qq`. -/
def aM (i j : Fin k) (q : Fin N) : ℂ := mSeg P σ x t i j q

/-- av `bG = Tr[G_{[1,i]} S^q G_{[j,k]} S^{x_k}]`. -/
def bGav (i j : Fin k) (q : Fin N) : ℂ :=
  trace (gHead (avSlots P.S x) (slotsH P.z σ t H) i * obsMat P.S q *
    gTail (avSlots P.S x) (slotsH P.z σ t H) j)

/-- av `bM = Tr[M^{(q)}_{[1,i],[j,k]} S^{x_k}]`. -/
def bMav (i j : Fin k) (q : Fin N) : ℂ := ∑ a, mGlue P σ x t i j q a * obsSeq P.S x k a

/-- iso `bG = (G_{[1,i]} S^q G_{[j,k]})_{ab}`. -/
def bGiso (a b : Fin N) (i j : Fin k) (q : Fin N) : ℂ :=
  (gHead (isoSlots P.S x) (slotsH P.z σ t H) i * obsMat P.S q *
    gTail (isoSlots P.S x) (slotsH P.z σ t H) j) a b

/-- iso `bM = δ_ab (M^{(q)}_{[1,i],[j,k]})_{aa}`. -/
def bMiso (a b : Fin N) (i j : Fin k) (q : Fin N) : ℂ :=
  if a = b then mGlue P σ x t i j q a else 0

/-- (F1) `∑_j G_{[1,j]} 𝒮[G_j - m_j] G_{[j,k]} B_{k-1}` -/
def famF1 (B : Fin k → Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  ∑ j, pairIns B (slotsH P.z σ t H)
    (fun X => bandSelfEnergy P.S (X - VS.patConj (σ j) (semicircleM P.z) • 1)) j j

/-- The iso last line `δ_ab m_1 m_k ∑_q (I + tÂ_k)_{aq} 𝒳^k(x', q)` (`l` is the last slot). -/
def lastLine (a b : Fin N) (l : Fin k) : ℂ :=
  if a = b then ∑ q, patM P.z σ 1 * patM P.z σ k * (1 + (t : ℂ) • aKer P σ l t) a q *
    P.avErr σ (update x l q) t H else 0

end Pattern

/-!
### The `G`-drift and the `M`-derivative as pair sums
-/

theorem famF1_eq (P : PsiData N) (σ : Fin k → Bool) (t : ℝ) (H : Matrix (Fin N) (Fin N) ℂ)
    (B : Fin k → Matrix (Fin N) (Fin N) ℂ) :
    famF1 P σ t H B = ∑ j, gHead B (slotsH P.z σ t H) j *
      bandSelfEnergy P.S (slotsH P.z σ t H j - VS.patConj (σ j) (semicircleM P.z) • 1) *
        gTail B (slotsH P.z σ t H) j := by
  unfold famF1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pairIns_eq, gSeg_self]

theorem dGmat_split (P : PsiData N) (hS : ∀ a b, P.S a b = P.S b a) (σ : Fin k → Bool)
    (t : ℝ) (H : Matrix (Fin N) (Fin N) ℂ) (B : Fin k → Matrix (Fin N) (Fin N) ℂ) :
    dGmat P.S P.z σ B t H = famF1 P σ t H B + ∑ j : Fin k, ∑ i with i < j, ∑ q,
      gSeg B (slotsH P.z σ t H) i j q q •
        (gHead B (slotsH P.z σ t H) i * obsMat P.S q * gTail B (slotsH P.z σ t H) j) := by
  unfold dGmat famF1
  rw [Finset.sum_add_distrib, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  exact pairIns_bandSelfEnergy hS _ _ i j

theorem dGav_split (P : PsiData N) (hS : ∀ a b, P.S a b = P.S b a) (σ : Fin k → Bool)
    (x : Fin k → Fin N) (t : ℝ) (H : Matrix (Fin N) (Fin N) ℂ) :
    dGav P σ x t H = trace (famF1 P σ t H (avSlots P.S x)) +
      ∑ j : Fin k, ∑ i with i < j, ∑ q,
        aG P σ t H (avSlots P.S x) i j q * bGav P σ x t H i j q := by
  rw [dGav, dGmat_split P hS, trace_add]
  congr 1
  simp only [trace_sum, trace_smul, smul_eq_mul, aG, bGav]

theorem dGiso_split (P : PsiData N) (hS : ∀ a b, P.S a b = P.S b a) (σ : Fin k → Bool)
    (a b : Fin N) (x : Fin k → Fin N) (t : ℝ) (H : Matrix (Fin N) (Fin N) ℂ) :
    dGiso P σ a b x t H = famF1 P σ t H (isoSlots P.S x) a b +
      ∑ j : Fin k, ∑ i with i < j, ∑ q,
        aG P σ t H (isoSlots P.S x) i j q * bGiso P σ x t H a b i j q := by
  rw [dGiso, dGmat_split P hS, Matrix.add_apply]
  congr 1
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, aG, bGiso]

theorem sum_swap_outer {α β γ δ : Type*} (s : Finset α) (u : α → Finset β) (v : Finset γ)
    (w : Finset δ) (C : α → β → γ → ℂ) (G : α → β → γ → δ → ℂ) (o : δ → ℂ) :
    ∑ d ∈ w, (∑ a ∈ s, ∑ b ∈ u a, ∑ c ∈ v, C a b c * G a b c d) * o d =
      ∑ a ∈ s, ∑ b ∈ u a, ∑ c ∈ v, C a b c * ∑ d ∈ w, G a b c d * o d := by
  simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]

theorem dMav_split (P : PsiData N) (σ : Fin k → Bool) (x : Fin k → Fin N) (t : ℝ) :
    dMav P σ x t = ∑ j : Fin k, ∑ i with i < j, ∑ q, aM P σ x t i j q * bMav P σ x t i j q := by
  unfold dMav mDerivP mDeriv
  rw [sum_swap_outer, sum_Icc_Ioc_reindex]
  rfl

theorem dMiso_split (P : PsiData N) (σ : Fin k → Bool) (a b : Fin N) (x : Fin k → Fin N)
    (t : ℝ) :
    dMiso P σ a b x t =
      ∑ j : Fin k, ∑ i with i < j, ∑ q, aM P σ x t i j q * bMiso P σ x t a b i j q := by
  unfold dMiso mDerivP mDeriv
  by_cases hab : a = b
  · simp only [hab, ite_true, bMiso, aM, mSeg, mGlue]
    rw [sum_Icc_Ioc_reindex]
  · simp only [hab, ite_false, bMiso, mul_zero, Finset.sum_const_zero]

end BlockBand.Native.ErdosRiabov.Evol
