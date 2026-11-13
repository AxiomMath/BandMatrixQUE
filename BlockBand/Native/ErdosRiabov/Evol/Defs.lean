module

public import BlockBand.Native.ErdosRiabov.Evol.SubDet
public import BlockBand.Native.ErdosRiabov.Psi.Cont
public import BlockBand.Native.ErdosRiabov.Kernel.VSKernelExtra

/-!
# Evolution equations: drift objects, `M`-derivative, kernel identity

Definitions for the evolution equations of the chain fluctuations along the VS flow: the
resolvent drift, the deterministic `M`-parts and their derivatives, the generator terms and the
forcing.

Notation: data `P : PsiData N`, pattern `σ : Fin k → Bool`, sites
`x : Fin k → Fin N` (0-based), `z_{j,t} = patZ`, `m_j = patM z σ (j+1)`, `m = semicircleM z`.
* `slotsH z σ t H = ((H - z_{j,t})⁻¹)_j`, and the Itô drift matrix of resolvent chains
  `dGmat S z σ B t H = ∑_j (∑_{i<j} G_{[0,i]} 𝒮[G_{[i,j]}] G_{[j,k)} +
  G_{[0,j]} 𝒮[G_j - m_j] G_{[j,k)})` (`Chains.pairIns`, `𝒮 = Chains.bandSelfEnergy S`);
  `chainDrift_eq_reTr_dGmat`: for `t ≤ 1` it is the VS `chainDrift` (`VS.chainDrift_vs`).
* The `M`-parts `avM` (`Tr[M S^{x_k}]`), `isoM` (`δ_ab M_a`) and their derivatives `dMav`,
  `dMiso`; the `G`-drifts `dGav = Tr[dGmat]`, `dGiso = (dGmat)_{ab}`.
* Generator kernels `aKer j t = Â_{j,t} = vsKernel S m_j m_{j+1} t` (cyclic: `m_{k+1} = m_1`;
  this is `T̂_t` for `σ_{j+1} ≠ σ_j` and `X̂`, `X̂̄` otherwise) and the generator terms
  `aTermAv = (⊕_{j=1}^k Â_j)[𝒳]`, `aTermIso = (⊕_{j=1}^{k-1} Â_j)[𝒴]`, `Â_j` acting on the
  site `x_j`.
* **Forcing** (the remainder, split further elsewhere):
  `forcingAv = dGav - dMav - aTermAv`, `forcingIso = dGiso - dMiso - aTermIso`.
* `vsKernel_eq_vsY_mul`: `Â = Y(I + tÂ)`, i.e. `|m|²S(I + tT̂) = T̂`, `m²S(I + tX̂) = X̂`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Evol

open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Chains
open BlockBand.Native.CEH.Flow
open Set
open scoped ComplexConjugate

variable {N k : ℕ}

/-- Resolvent slots `G_j = (H - z_{j,t})⁻¹`. -/
def slotsH (z : ℂ) (σ : Fin k → Bool) (t : ℝ) (H : Matrix (Fin N) (Fin N) ℂ) :
    Fin k → Matrix (Fin N) (Fin N) ℂ :=
  fun j => (H - patZ z σ t j • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹

/-- The Itô drift matrix of resolvent chains. -/
def dGmat (S : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (σ : Fin k → Bool)
    (B : Fin k → Matrix (Fin N) (Fin N) ℂ) (t : ℝ) (H : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  ∑ j, ((∑ i with i < j, pairIns B (slotsH z σ t H) (bandSelfEnergy S) i j) +
    pairIns B (slotsH z σ t H)
      (fun X => bandSelfEnergy S (X - VS.patConj (σ j) (semicircleM z) • 1)) j j)

/-- The right-hand side of `Split.DerivStatement`: `d/dσ M^{(σ)}_{[1,k]}` (diagonal). -/
def mDeriv (S : Matrix (Fin N) (Fin N) ℝ) (mm : ℕ → ℂ) (A : ℕ → Fin N → ℂ) (k : ℕ) (s : ℝ) :
    Fin N → ℂ :=
  fun a => ∑ i ∈ Finset.Icc 1 k, ∑ j ∈ Finset.Ioc i k, ∑ q : Fin N,
    Split.chainM s S mm A i j q *
      Split.chainM s S (Split.glueChain i j mm) (Split.glueObs i j (Split.rowObs S q) A) 1
        (k - j + i + 1) a

/-- Next index in the cyclic order (1-based value of `m_{j+1}`, `m_{k+1} = m_1`). -/
def nextIdx (j : Fin k) : ℕ := if j.val + 1 < k then j.val + 2 else 1

section Pattern

variable (P : PsiData N)

/-- `Tr[M^{(s)}_{[1,k]} S^{x_k}]`. -/
def avM (σ : Fin k → Bool) (x : Fin k → Fin N) (s : ℝ) : ℂ :=
  ∑ a, P.mChain σ x s a * obsSeq P.S x k a

/-- `δ_ab (M^{(s)}_{[1,k]})_{aa}`. -/
def isoM (σ : Fin k → Bool) (a b : Fin N) (x : Fin k → Fin N) (s : ℝ) : ℂ :=
  if a = b then P.mChain σ x s a else 0

/-- The `M`-derivative `d/ds M^{(s)}_{[1,k]}` of the pattern (diagonal). -/
def mDerivP (σ : Fin k → Bool) (x : Fin k → Fin N) (s : ℝ) : Fin N → ℂ :=
  mDeriv P.S (patM P.z σ) (obsSeq P.S x) k s

/-- `d/ds Tr[M^{(s)} S^{x_k}]`. -/
def dMav (σ : Fin k → Bool) (x : Fin k → Fin N) (s : ℝ) : ℂ :=
  ∑ a, mDerivP P σ x s a * obsSeq P.S x k a

/-- `d/ds δ_ab M^{(s)}_{aa}`. -/
def dMiso (σ : Fin k → Bool) (a b : Fin N) (x : Fin k → Fin N) (s : ℝ) : ℂ :=
  if a = b then mDerivP P σ x s a else 0

/-- `G`-drift of `𝒳`: `Tr[dGmat]` with the averaged slots. -/
def dGav (σ : Fin k → Bool) (x : Fin k → Fin N) (t : ℝ) (H : Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  Matrix.trace (dGmat P.S P.z σ (avSlots P.S x) t H)

/-- `G`-drift of `𝒴`: `(dGmat)_{ab}` with the isotropic slots. -/
def dGiso (σ : Fin k → Bool) (a b : Fin N) (x : Fin k → Fin N) (t : ℝ)
    (H : Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  dGmat P.S P.z σ (isoSlots P.S x) t H a b

/-- The generator kernel `Â_{j,t} = vsKernel S m_j m_{j+1} t` (cyclic). -/
def aKer (σ : Fin k → Bool) (j : Fin k) (t : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  vsKernel P.S (patM P.z σ (j.val + 1)) (patM P.z σ (nextIdx j)) t

/-- `(⊕_{j=1}^k Â_{j,t})[𝒳^k_t](x) = ∑_j ∑_q (Â_j)_{x_j q} 𝒳(x[x_j := q])`. -/
def aTermAv (σ : Fin k → Bool) (x : Fin k → Fin N) (t : ℝ) (H : Matrix (Fin N) (Fin N) ℂ) :
    ℂ :=
  ∑ j, ∑ q, aKer P σ j t (x j) q * P.avErr σ (Function.update x j q) t H

/-- `(⊕_{j=1}^{k-1} Â_{j,t})[𝒴^k_t](a, x', b)`. -/
def aTermIso (σ : Fin k → Bool) (a b : Fin N) (x : Fin k → Fin N) (t : ℝ)
    (H : Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  ∑ j with j.val + 1 < k, ∑ q, aKer P σ j t (x j) q * P.isoErr σ a b (Function.update x j q) t H

/-- Averaged forcing `𝓕^av` (remainder form). -/
def forcingAv (σ : Fin k → Bool) (x : Fin k → Fin N) (t : ℝ)
    (H : Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  dGav P σ x t H - dMav P σ x t - aTermAv P σ x t H

/-- Isotropic forcing `𝓕^iso` (remainder form). -/
def forcingIso (σ : Fin k → Bool) (a b : Fin N) (x : Fin k → Fin N) (t : ℝ)
    (H : Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  dGiso P σ a b x t H - dMiso P σ a b x t - aTermIso P σ a b x t H

theorem aTermAv_add_forcingAv (σ : Fin k → Bool) (x : Fin k → Fin N) (t : ℝ)
    (H : Matrix (Fin N) (Fin N) ℂ) :
    aTermAv P σ x t H + forcingAv P σ x t H = dGav P σ x t H - dMav P σ x t := by
  unfold forcingAv
  ring

theorem aTermIso_add_forcingIso (σ : Fin k → Bool) (a b : Fin N) (x : Fin k → Fin N) (t : ℝ)
    (H : Matrix (Fin N) (Fin N) ℂ) :
    aTermIso P σ a b x t H + forcingIso P σ a b x t H =
      dGiso P σ a b x t H - dMiso P σ a b x t := by
  unfold forcingIso
  ring

/-!
### The `M`-derivative
-/

/-- **`M`-derivative** (VS form, no `k/2 · M`), under the hypothesis `Split.DerivStatement`
(proved as `MTerms.deriv_holds`).
-/
theorem hasDerivAt_mChain (hD : Split.DerivStatement) (hz : P.z.im ≠ 0)
    (hS : StochasticSymm P.S) (hk : 1 ≤ k) (σ : Fin k → Bool) (x : Fin k → Fin N) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (a : Fin N) :
    HasDerivAt (fun r => P.mChain σ x r a) (mDerivP P σ x s a) s :=
  hD N P.S (stochasticSymm_iff_profileHyp.mp hS) s hs (patM P.z σ)
    (norm_patM_lt_one hz σ) (obsSeq P.S x) k hk a

theorem norm_glueChain_lt_one {z : ℂ} (hz : z.im ≠ 0) (σ : Fin k → Bool) (i j p : ℕ) :
    ‖Split.glueChain i j (patM z σ) p‖ < 1 := by
  unfold Split.glueChain
  split_ifs <;> exact norm_patM_lt_one hz σ _

theorem continuousOn_mDerivP (hz : P.z.im ≠ 0) (hS : StochasticSymm P.S) (σ : Fin k → Bool)
    (x : Fin k → Fin N) (a : Fin N) :
    ContinuousOn (fun s => mDerivP P σ x s a) (Icc 0 1) := by
  unfold mDerivP mDeriv
  refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ =>
    continuousOn_finsetSum _ fun q _ => ?_
  exact ((continuous_apply q).comp_continuousOn
    (continuousOn_chainM hS (norm_patM_lt_one hz σ) _ i j)).mul
    ((continuous_apply a).comp_continuousOn
      (continuousOn_chainM hS (norm_glueChain_lt_one hz σ i j) _ 1 _))

theorem hasDerivAt_avM (hD : Split.DerivStatement) (hz : P.z.im ≠ 0) (hS : StochasticSymm P.S)
    (hk : 1 ≤ k) (σ : Fin k → Bool) (x : Fin k → Fin N) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun r => avM P σ x r) (dMav P σ x s) s := by
  unfold avM dMav
  exact HasDerivAt.fun_sum fun a _ =>
    (hasDerivAt_mChain P hD hz hS hk σ x hs a).mul_const _

theorem hasDerivAt_isoM (hD : Split.DerivStatement) (hz : P.z.im ≠ 0)
    (hS : StochasticSymm P.S) (hk : 1 ≤ k) (σ : Fin k → Bool) (a b : Fin N)
    (x : Fin k → Fin N) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun r => isoM P σ a b x r) (dMiso P σ a b x s) s := by
  unfold isoM dMiso
  by_cases hab : a = b
  · simp only [hab, ite_true]
    exact hasDerivAt_mChain P hD hz hS hk σ x hs b
  · simp only [hab, ite_false]
    exact hasDerivAt_const _ _

theorem continuousOn_dMav (hz : P.z.im ≠ 0) (hS : StochasticSymm P.S) (σ : Fin k → Bool)
    (x : Fin k → Fin N) : ContinuousOn (fun s => dMav P σ x s) (Icc 0 1) := by
  unfold dMav
  exact continuousOn_finsetSum _ fun a _ =>
    (continuousOn_mDerivP P hz hS σ x a).mul continuousOn_const

theorem continuousOn_dMiso (hz : P.z.im ≠ 0) (hS : StochasticSymm P.S) (σ : Fin k → Bool)
    (a b : Fin N) (x : Fin k → Fin N) : ContinuousOn (fun s => dMiso P σ a b x s) (Icc 0 1) := by
  unfold dMiso
  by_cases hab : a = b
  · simp only [hab, ite_true]
    exact continuousOn_mDerivP P hz hS σ x b
  · simp only [hab, ite_false]
    exact continuousOn_const

end Pattern

/-!
### Re / Im of complex derivatives
-/

theorem hasDerivAt_re {f : ℝ → ℂ} {f' : ℂ} {s : ℝ} (h : HasDerivAt f f' s) :
    HasDerivAt (fun r => (f r).re) f'.re s := by
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt s h

theorem hasDerivAt_im {f : ℝ → ℂ} {f' : ℂ} {s : ℝ} (h : HasDerivAt f f' s) :
    HasDerivAt (fun r => (f r).im) f'.im s := by
  exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt s h

/-!
### The kernel identity `Â = Y(I + tÂ)`
-/

/-- `Â_t = Y(I + tÂ_t)` (`Y = μμ'S`, `‖tμμ'‖ < 1`): `|m|²S(I + tT̂) = T̂`, `m²S(I + tX̂) = X̂`. -/
theorem vsKernel_eq_vsY_mul {S : Matrix (Fin N) (Fin N) ℝ} (hS : StochasticSymm S) {μ μ' : ℂ}
    {t : ℝ} (ht : ‖(t : ℂ) * (μ * μ')‖ < 1) :
    vsKernel S μ μ' t = vsY S μ μ' * (1 + (t : ℂ) • vsKernel S μ μ' t) := by
  have h := one_sub_vsY_mul_inv hS ht
  have hinv : (1 - (t : ℂ) • vsY S μ μ')⁻¹ =
      1 + (t : ℂ) • (vsY S μ μ' * (1 - (t : ℂ) • vsY S μ μ')⁻¹) := by
    rw [sub_mul, one_mul, smul_mul_assoc] at h
    exact sub_eq_iff_eq_add.mp h
  unfold vsKernel
  conv_lhs => rw [hinv]

/-!
### The VS chain drift as `Re tr(K dGmat)`
-/

variable {p : BlockBand.Parameters}

open BlockBand.Native.ErdosRiabov.VS in
/-- For `t ≤ 1` the VS `chainDrift` along the saturated pattern parameters is
`Re tr(K · dGmat)` at `H = ringMatrixFin p y` (`S = shortRingProfile p.b p.n p.W`). -/
theorem chainDrift_eq_reTr_dGmat {z : ℂ} (hz : 0 < z.im) (σ : Fin k → Bool)
    (B : Fin k → RingMat p) (K : RingMat p) {t : ℝ} (ht : t ≤ 1)
    (y : Fin (Stochastic.ringDim p) → ℝ) :
    chainDrift 0 (vsPatternSpec z (semicircleM z) σ) B K t y =
      reTr K (dGmat (Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W) z σ B t
        (ringMatrixFin p y)) := by
  have hy := semicircleM_im_pos hz
  have hδ : 0 ≤ z.im / (2 * (semicircleM z).im) := by positivity
  have hslots : ringSlots 0 (vsPatternSpec z (semicircleM z) σ) t y =
      slotsH z σ t (ringMatrixFin p y) := by
    funext j
    simp only [ringSlots, resSlots, res, zero_add, slotsH]
    rw [patZ_eq_vsPatternSpec z σ ht hδ j]
  have h := chainDrift_vs (p := p) 0 (fun j => VS.patConj (σ j) z)
    (fun j => VS.patConj (σ j) (semicircleM z)) hδ B K ht y
  change chainDrift 0 (fun j => vsSpec (VS.patConj (σ j) z) (VS.patConj (σ j) (semicircleM z))
    (vsSat (z.im / (2 * (semicircleM z).im)))) B K t y = _
  rw [h]
  rw [dGmat, reTr_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [reTr_add, reTr_sum]
  change (∑ i with i < j, reTr K (pairIns B (ringSlots 0 (vsPatternSpec z (semicircleM z) σ) t y)
      _ i j)) + reTr K (pairIns B (ringSlots 0 (vsPatternSpec z (semicircleM z) σ) t y) _ j j) = _
  rw [hslots]

end BlockBand.Native.ErdosRiabov.Evol
