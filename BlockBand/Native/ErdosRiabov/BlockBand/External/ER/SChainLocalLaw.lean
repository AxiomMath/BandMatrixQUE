module

public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.ExternalBandLocalClosure
public import BlockBand.Native.ErdosRiabov.BlockBand.External.ER.Clause1CyclicControl
public import BlockBand.Native.ErdosRiabov.BlockBand.Analysis.ERControlKernels

/-!
# ER `S`-chains, their deterministic approximations, and the `Ψ`-local law

This module encodes the objects of Erdős–Riabov, *The Zigzag Strategy for Random
Band Matrices*, arXiv:2506.06441v1, Section 5.2 (resolvent chains with the special
observables `S^x`, the deterministic approximations `M`, the size functions, the loss
exponents and the `Ψ`-functions) and Definition 5.3 (local laws in terms of `Ψ`),
specialized to the exact Gaussian ring, with the exponential control function of ER
Example 2.7 (`erExample27Control`). Only definitions and elementary facts are stated
here; no local law is asserted.

Conventions (all as in ER):

* `N = p.L`, `S = siteCovariance p = varianceProfile p` (row-stochastic, `S_ab ≤ C/W`),
  `G(z) = (H - z)⁻¹ = shortRingGreen H z`, `m = erSemicircleStieltjes` (the
  Schwarz-reflected semicircle transform, so `Im m · Im z > 0` on both half-planes).
* `S^x` is the diagonal matrix carrying row `x` of `S` (ER (3.7)).
* the self-energy on diagonal matrices is `𝒮[diag r] = diag (S r)` (ER Section 3,
  complex Hermitian class with `E h² = 0`), so every `M` is diagonal and is stored as
  the vector of its diagonal.
* `ℓ(η) = min (W / √η, N)` (`erLocalizationLength`) and `|x-y|_N` (`erSiteDistance`).

Decay constant.  ER Example 2.7 fixes "a constant `c₀ > 0`"; Proposition 2.8(ii)
asserts admissibility for "some small `c₀`" depending on the model parameters, which
include `κ` and the height ceiling `C₀` (Definition 2.9).  The decay `c₀` is therefore
kept as an explicit argument of the control function.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace ERNative.BlockBand
namespace GaussianRing
namespace ERSChainLocalLaw

open MeasureTheory
open scoped ENNReal BigOperators
open ERProfile ERRingAdapter ERExternalBandLocalClosure

local instance (p : Params) : NeZero p.n := p.nNeZero

/-!
## Deterministic objects
-/

section Deterministic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The ordered product `G₁ A₁ G₂ A₂ ⋯ A_{k-1} G_k` of ER (3.2)/(5.19), for a chain
of length `k = n + 1`: `G₁` is the first resolvent, and `A i`, `G i` (`i : Fin n`) are
the `(i+1)`-st observable and the `(i+2)`-nd resolvent.  For `n = 0` it is `G₁`. -/
def erChainProduct (G₁ : Matrix ι ι ℂ) {n : ℕ} (A G : Fin n → Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  G₁ * (List.ofFn fun i => A i * G i).prod

/-- ER (11.2), the normalized deterministic approximation `M̃_{[j,k]}` (0-based
indices `j ≤ k`), stored as the diagonal of a diagonal matrix:

`M̃_{[j,k]} = (1 - m_j m_k S)⁻¹ [A_j M̃_{[j+1,k]} + ∑_{j<i<k} m_j m_i 𝒮[M̃_{[j,i]}] M̃_{[i,k]}]`,

with `M̃_{[j,j]} = 1` and `𝒮[diag r] = diag (S r)`.  Here `m i` is the value of the
semicircle transform at the `i`-th spectral parameter and `A i` is the diagonal of the
`i`-th observable.  The inverse is the matrix inverse of `1 - m_j m_k S`. -/
def erMtilde (S : Matrix ι ι ℂ) (m : ℕ → ℂ) (A : ℕ → ι → ℂ) (j k : ℕ) : ι → ℂ :=
  if h : j < k then
    Matrix.mulVec (1 - (m j * m k) • S)⁻¹
      (A j * erMtilde S m A (j + 1) k +
        ∑ i ∈ (Finset.Ioo j k).attach,
          (m j * m i.1) • (Matrix.mulVec S (erMtilde S m A j i.1) * erMtilde S m A i.1 k))
  else 1
termination_by k - j
decreasing_by
  all_goals first
    | omega
    | (have hi := Finset.mem_Ioo.mp i.2; omega)

/-- ER (11.1): `M_{[j,k]} = M̃_{[j,k]} ∏_{i=j}^{k} m_i` (diagonal stored as a vector). -/
def erM (S : Matrix ι ι ℂ) (m : ℕ → ℂ) (A : ℕ → ι → ℂ) (j k : ℕ) : ι → ℂ :=
  (∏ i ∈ Finset.Icc j k, m i) • erMtilde S m A j k

theorem erMtilde_self (S : Matrix ι ι ℂ) (m : ℕ → ℂ) (A : ℕ → ι → ℂ) (j : ℕ) :
    erMtilde S m A j j = 1 := by
  rw [erMtilde]
  simp

/-- The convention `M_{[j,j]} = m(z_j)` of ER (3.3). -/
theorem erM_self (S : Matrix ι ι ℂ) (m : ℕ → ℂ) (A : ℕ → ι → ℂ) (j : ℕ) :
    erM S m A j j = fun _ => m j := by
  funext a
  simp [erM, erMtilde_self]

/-- ER (5.28), isotropic size function of a chain of length `k = n + 1`:
`(ℓη)^{-(k-1)/2} √(Υ_{a x₁} Υ_{x₁ x₂} ⋯ Υ_{x_{k-2} x_{k-1}} Υ_{x_{k-1} b})`,
written as the product over the consecutive pairs of the path `a, x₁, …, x_{k-1}, b`.
For `k = 1` it is `√Υ_ab` (`erSizeIso_zero`). -/
def erSizeIso (Υ : ι → ι → ℝ) (ℓη : ℝ) {n : ℕ} (a : ι) (x : Fin n → ι) (b : ι) : ℝ :=
  let y : Fin (n + 2) → ι := Fin.cons a (Fin.snoc x b)
  Real.rpow ℓη (-(n : ℝ) / 2) * Real.sqrt (∏ i : Fin (n + 1), Υ (y i.castSucc) (y i.succ))

/-- ER (5.28), averaged size function of a chain of length `k = n + 1`:
`1 / (ℓη)` for `k = 1`, and `(ℓη)^{-k/2} √(Υ_{x_k x₁} ∏_{j=2}^{k} Υ_{x_{j-1} x_j})`
(the cyclic product) for `k ≥ 2`. -/
def erSizeAv (Υ : ι → ι → ℝ) (ℓη : ℝ) {n : ℕ} (x : Fin (n + 1) → ι) : ℝ :=
  if n = 0 then 1 / ℓη
  else
    Real.rpow ℓη (-((n : ℝ) + 1) / 2) *
      Real.sqrt (∏ i : Fin (n + 1), Υ (x i) (x (finRotate (n + 1) i)))

omit [Fintype ι] [DecidableEq ι] in
theorem erSizeIso_zero (Υ : ι → ι → ℝ) (ℓη : ℝ) (a : ι) (x : Fin 0 → ι) (b : ι) :
    erSizeIso Υ ℓη a x b = Real.sqrt (Υ a b) := by
  have h1 : (Fin.cons a (Fin.snoc x b) : Fin 2 → ι) (Fin.castSucc 0) = a := rfl
  have h2 : (Fin.cons a (Fin.snoc x b) : Fin 2 → ι) (Fin.succ 0) = b := by
    simp [Fin.snoc]
  have h0 : Real.rpow ℓη (-((0 : ℕ) : ℝ) / 2) = 1 := by
    rw [show (-((0 : ℕ) : ℝ) / 2) = 0 by simp]
    exact Real.rpow_zero ℓη
  simp only [erSizeIso]
  rw [h0, one_mul, Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, h1, h2]

end Deterministic

/-- ER (5.31), the isotropic loss exponent `α_k` for maximal chain length `K`:
`0` for `k ≤ K/2` and `½ √(2k/K - 1)` for `k ≥ K/2 + 1`. -/
def erIsoLoss (K k : ℕ) : ℝ :=
  if 2 * k ≤ K then 0 else (1 / 2) * Real.sqrt (2 * (k : ℝ) / K - 1)

/-- ER (5.31), the averaged loss exponent `β_k = α_{k+1}` for `k ≤ K - 1` and
`β_K = ½ + α_{K/2+1}`. -/
def erAvLoss (K k : ℕ) : ℝ :=
  if k ≤ K - 1 then erIsoLoss K (k + 1) else 1 / 2 + erIsoLoss K (K / 2 + 1)

/-!
## The Gaussian-ring specialization
-/

/-- ER (3.7): the diagonal observable `S^x`, `(S^x)_{ab} = δ_ab S_{xa}`. -/
def erSObservable (p : Params) (x : Site p.n p.W) :
    Matrix (Site p.n p.W) (Site p.n p.W) ℂ :=
  Matrix.diagonal fun a => erComplexVarianceProfile p x a

/-- ER (5.19): the `S`-chain `G_{[1,k]}(x') = G₁ S^{x₁} G₂ ⋯ S^{x_{k-1}} G_k` with
`G_j = (H - z_j)⁻¹`, for `k = n + 1` spectral parameters `z` and `n` sites `x`. -/
def erSChain (p : Params) (H : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) {n : ℕ}
    (z : Fin (n + 1) → ℂ) (x : Fin n → Site p.n p.W) :
    Matrix (Site p.n p.W) (Site p.n p.W) ℂ :=
  erChainProduct (shortRingGreen H (z 0)) (fun i => erSObservable p (x i))
    (fun i => shortRingGreen H (z i.succ))

/-- ER (5.20): the deterministic approximation `M_{[1,k]}(x')` of `erSChain`, the
diagonal matrix produced by the recursion (11.1)--(11.2) with `m_j = m(z_j)` and
`A_j = S^{x_j}`. -/
def erSChainM (p : Params) {n : ℕ} (z : Fin (n + 1) → ℂ) (x : Fin n → Site p.n p.W) :
    Matrix (Site p.n p.W) (Site p.n p.W) ℂ :=
  Matrix.diagonal
    (erM (erComplexVarianceProfile p)
      (fun i => if h : i < n + 1 then erSemicircleStieltjes (z ⟨i, h⟩) else 0)
      (fun i a => if h : i < n then erComplexVarianceProfile p (x ⟨i, h⟩) a else 0)
      0 n)

/-- ER (2.29), Example 2.7: the exponentially decaying control function
`Υ_η(x,y) = e^{-c₀ |x-y|_N / ℓ} / (ℓη) + (ℓ/η) N^{-D}` with `ℓ = ℓ(η)`. -/
def erExample27Control (p : Params) (c₀ D : ℝ) : ERControlFamily p :=
  fun η x y =>
    Real.exp (-c₀ * (erSiteDistance p x y : ℝ) / erLocalizationLength p η) /
        (erLocalizationLength p η * η) +
      erLocalizationLength p η / η * Real.rpow (p.L : ℝ) (-D)

/-- The finite spectral set `𝒟 = {ẑ_j, \bar ẑ_j : j ∈ [K]}` of ER (5.27), indexed by
`Fin K × Bool` (`true` selects `ẑ_j`, `false` its complex conjugate). -/
def erDomainPoint {K : ℕ} (zhat : Fin K → ℂ) (s : Fin K × Bool) : ℂ :=
  if s.2 then zhat s.1 else starRingEnd ℂ (zhat s.1)

/-- `η = min_j |Im z_j|`, the height representing a tuple in ER (5.28). -/
def erTupleHeight {n : ℕ} (z : Fin (n + 1) → ℂ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun i => |(z i).im|

/-- ER (5.32), `Ψ^iso_k` for `k = n + 1`, maximal chain length `K`, control
`Υ = erExample27Control p c₀ D`:
`max_{z ∈ 𝒟^k} max_{a,b} max_{x'} |(G_{[1,k]} - M_{[1,k]})_{ab}(x')| /
  ((ℓη)^{α_k} s^iso_k(a,x',b))`, with `η = min_j |Im z_j|`, `ℓ = ℓ(η)`. -/
def erPsiIso (p : Params) (c₀ D : ℝ) (K : ℕ) (zhat : Fin K → ℂ)
    (H : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) (n : ℕ) : ℝ :=
  ⨆ t : (Fin (n + 1) → Fin K × Bool) × Site p.n p.W × Site p.n p.W ×
      (Fin n → Site p.n p.W),
    ‖(erSChain p H (fun i => erDomainPoint zhat (t.1 i)) t.2.2.2 -
        erSChainM p (fun i => erDomainPoint zhat (t.1 i)) t.2.2.2) t.2.1 t.2.2.1‖ /
      (Real.rpow
          (erLocalizationLength p (erTupleHeight fun i => erDomainPoint zhat (t.1 i)) *
            erTupleHeight fun i => erDomainPoint zhat (t.1 i))
          (erIsoLoss K (n + 1)) *
        erSizeIso
          (erExample27Control p c₀ D (erTupleHeight fun i => erDomainPoint zhat (t.1 i)))
          (erLocalizationLength p (erTupleHeight fun i => erDomainPoint zhat (t.1 i)) *
            erTupleHeight fun i => erDomainPoint zhat (t.1 i))
          t.2.1 t.2.2.2 t.2.2.1)

/-- ER (5.32), `Ψ^av_k` for `k = n + 1`:
`max_{z ∈ 𝒟^k} max_{x} |Tr[(G_{[1,k]} - M_{[1,k]})(x') S^{x_k}]| /
  ((ℓη)^{β_k} s^av_k(x))`, where `x' = (x₁,…,x_{k-1})`. -/
def erPsiAv (p : Params) (c₀ D : ℝ) (K : ℕ) (zhat : Fin K → ℂ)
    (H : Matrix (Site p.n p.W) (Site p.n p.W) ℂ) (n : ℕ) : ℝ :=
  ⨆ t : (Fin (n + 1) → Fin K × Bool) × (Fin (n + 1) → Site p.n p.W),
    ‖Matrix.trace
        ((erSChain p H (fun i => erDomainPoint zhat (t.1 i)) (Fin.init t.2) -
            erSChainM p (fun i => erDomainPoint zhat (t.1 i)) (Fin.init t.2)) *
          erSObservable p (t.2 (Fin.last n)))‖ /
      (Real.rpow
          (erLocalizationLength p (erTupleHeight fun i => erDomainPoint zhat (t.1 i)) *
            erTupleHeight fun i => erDomainPoint zhat (t.1 i))
          (erAvLoss K (n + 1)) *
        erSizeAv
          (erExample27Control p c₀ D (erTupleHeight fun i => erDomainPoint zhat (t.1 i)))
          (erLocalizationLength p (erTupleHeight fun i => erDomainPoint zhat (t.1 i)) *
            erTupleHeight fun i => erDomainPoint zhat (t.1 i))
          t.2)

/-- ER (3.1): comparability `max_j η_j ≤ C̃₀ min_j η_j` of the fixed parameters. -/
def ERComparable {K : ℕ} (zhat : Fin K → ℂ) (Ccomp : ℝ) : Prop :=
  ∀ i j, |(zhat i).im| ≤ Ccomp * |(zhat j).im|

/-!
## The bulk box lies in ER's spectral domain
-/

/-!
## The definitional `k = 1` extraction
-/

theorem erLocalizationLength_pos (p : Params) {η : ℝ} (hη : 0 < η) :
    0 < erLocalizationLength p η := by
  have hW : (0 : ℝ) < p.W := by exact_mod_cast p.W_pos
  have hL : (0 : ℝ) < p.L := by exact_mod_cast p.L_pos
  exact lt_min (div_pos hW (Real.sqrt_pos.mpr hη)) hL

theorem erExample27Control_pos (p : Params) (c₀ D : ℝ) {η : ℝ} (hη : 0 < η)
    (x y : Site p.n p.W) : 0 < erExample27Control p c₀ D η x y := by
  have hℓ := erLocalizationLength_pos p hη
  have hL : (0 : ℝ) < p.L := by exact_mod_cast p.L_pos
  unfold erExample27Control
  have h1 : 0 < Real.exp (-c₀ * (erSiteDistance p x y : ℝ) / erLocalizationLength p η) /
      (erLocalizationLength p η * η) := by positivity
  have h2 : 0 ≤ erLocalizationLength p η / η * Real.rpow (p.L : ℝ) (-D) :=
    mul_nonneg (div_nonneg hℓ.le hη.le) (Real.rpow_nonneg hL.le _)
  linarith

/-!
## Extraction to the published tail bound
-/

end ERSChainLocalLaw
end GaussianRing
end ERNative.BlockBand
