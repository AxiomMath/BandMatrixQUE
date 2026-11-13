module

public import BlockBand.Native.ErdosRiabov.Flow.Exponents
public import BlockBand.Native.ErdosRiabov.Flow.Scales
public import BlockBand.Native.ErdosRiabov.Split.MTermsStatement
public import BlockBand.Native.ErdosRiabov.Chains.ChainBounds
public import BlockBand.Native.ErdosRiabov.VS.ResolventItoVS

/-!
# Patterns, chains, size functions and the control quantities `Ψ`

Definitions of the resolvent chains, their deterministic approximations, the size functions and
the control quantities along the VS characteristic, with the lower bound on the size functions.

Data (`PsiData N`): bandwidth `W`, profile `S` on `Fin N`, decay `D` of the control, terminal
spectral parameter `z`. Along the VS characteristic (`Flow.vsTraj`, `t ∈ [0,1]`):
* a **pattern** is `σ : Fin k → Bool` (`true` = conjugate); `z_{j,t} = patZ z σ t j ∈ {z_t, z̄_t}`,
  and `m_j = patM z σ j ∈ {m, m̄}` (1-based, as in `Split`); for `t ≤ 1` these are the VS
  saturated parameters (`patZ_eq_vsPatternSpec`);
* **observables** `(S^x)_{ab} = δ_{ab} S_{xa}` (`obsMat`, diagonal `Split.rowObs`);
* **chains** `G_1 B_1 ⋯ G_k B_k`, `G_j = (H - z_j)⁻¹` (`gChain`, the `Chains.slotProd` of the
  resolvent slots; `resChain_zero_eq_gChain` identifies it with `Chains.resChain 0 L z B y` at
  `H = L y`). The isotropic chain `G_{[1,k]}(x')` uses `isoSlots` (`S^{x_j}`, last slot `1`); the
  averaged one `G_{[1,k]}(x') S^{x_k}` uses `avSlots`. Sites are `x : Fin k → Fin N` (0-based;
  the isotropic quantities ignore `x_{k-1}`);
* **M-terms** `M^{(t)}_{[1,k]} = Split.chainM t S m A 1 k` with `A_p = S^{x_{p-1}}` (`mChain`);
* `𝒴 = ((G - M)_{[1,k]})_{ab}` (`isoErr`), `𝒳 = Tr[(G - M)_{[1,k]} S^{x_k}]` (`avErr`);
* **size functions** with `Υ_t = polynomialControl N W D η_t`,
  `η_t = Kernel.vsHeight z t`, `ℓη = lEta t`: `sIso`, `sAv` (`s^av_1 = 1/(ℓη)`);
* loss exponents `α_k = Flow.Expo.lossAlpha k`, `β_k = Flow.Expo.lossBeta k` (`K = 8`);
* **control quantities** `Ψ^iso_{k,t}(H) = max_{σ,a,b,x} |𝒴|/((ℓη)^{α_k} s^iso)` and
  `Ψ^av_{k,t}(H) = max_{σ,x} |𝒳|/((ℓη)^{β_k} s^av)` (`bigPsiIso`, `bigPsiAv`; finite maxima,
  taken in `ℝ≥0` so that no nonemptiness is needed).

Proved here: the max characterization (`le_bigPsiIso_iff`, `isoRatio_le_bigPsiIso`, …), the
bridges, `‖m_j‖ < 1`, and the **floor** (`sIso_floor`, `sAv_floor`): on `z ∈ 𝒟`, `t ∈ [0,1]`,
`1 ≤ k`, both size functions are `≥ (A N)^{-k(2+D)}`, `A = 1 + √(C₀+1)`, from
`Kernel.polynomialControl_lower`; hence `≥ N^{-K(2D''+1)}` for `k ≤ K`, `N ≥ A^{K(2+D)}`
(`sizes_floor_vsK`, with `floor_exponent_le_of_vsData`). Continuity, the value `Ψ_0 = 0` and
the stopping time are treated separately.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Psi

open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Internal.Contracts.Inputs (polynomialControl)
open scoped ComplexConjugate NNReal

variable {N k : ℕ}

/-- Data of the control quantities: bandwidth `W`, profile `S`, decay `D`, terminal point `z`. -/
structure PsiData (N : ℕ) where
  W : ℕ
  S : Matrix (Fin N) (Fin N) ℝ
  D : ℝ
  z : ℂ

/-- Pattern spectral parameter `z_{j,t} ∈ {z_t, z̄_t}` (`true` = conjugate). -/
def patZ (z : ℂ) (σ : Fin k → Bool) (t : ℝ) (j : Fin k) : ℂ := VS.patConj (σ j) (vsTraj z t)

/-- 1-based pattern values `m_i = m(z_i) ∈ {m, m̄}` for `1 ≤ i ≤ k` (`0` otherwise). -/
def patM (z : ℂ) (σ : Fin k → Bool) (i : ℕ) : ℂ :=
  if h : 1 ≤ i ∧ i ≤ k then VS.patConj (σ ⟨i - 1, by omega⟩) (semicircleM z) else 0

/-- The observable matrix `(S^x)_{ab} = δ_{ab} S_{xa}`. -/
def obsMat (S : Matrix (Fin N) (Fin N) ℝ) (x : Fin N) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal (Split.rowObs S x)

/-- 1-based diagonal observables `A_p = S^{x_{p-1}}` (`1 ≤ p ≤ k`), constant `1` otherwise. -/
def obsSeq (S : Matrix (Fin N) (Fin N) ℝ) (x : Fin k → Fin N) (p : ℕ) : Fin N → ℂ :=
  if h : 1 ≤ p ∧ p ≤ k then Split.rowObs S (x ⟨p - 1, by omega⟩) else fun _ => 1

/-- Isotropic slots: `S^{x_j}` for `j < k-1`, the identity in the last slot. -/
def isoSlots (S : Matrix (Fin N) (Fin N) ℝ) (x : Fin k → Fin N) :
    Fin k → Matrix (Fin N) (Fin N) ℂ :=
  fun j => if j.val + 1 < k then obsMat S (x j) else 1

/-- Averaged slots: `S^{x_j}` in every slot (the last one is `S^{x_k}` of the trace). -/
def avSlots (S : Matrix (Fin N) (Fin N) ℝ) (x : Fin k → Fin N) :
    Fin k → Matrix (Fin N) (Fin N) ℂ :=
  fun j => obsMat S (x j)

/-- The chain `G_1 B_1 ⋯ G_k B_k`, `G_j = (H - w_j)⁻¹`. -/
def gChain (w : Fin k → ℂ) (B : Fin k → Matrix (Fin N) (Fin N) ℂ)
    (H : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Chains.slotProd B (fun j => (H - w j • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹)

/-- Iso sites `a = p_0, x_0, …, x_{k-2}, p_k = b` of the isotropic size function. -/
def isoPoint (a b : Fin N) (x : Fin k → Fin N) (i : ℕ) : Fin N :=
  if i = 0 then a else if h : i < k then x ⟨i - 1, by omega⟩ else b

/-- Index set of `Ψ^iso_k`: pattern, `a`, `b`, sites. -/
abbrev IsoIdx (N k : ℕ) : Type := (Fin k → Bool) × Fin N × Fin N × (Fin k → Fin N)

/-- Index set of `Ψ^av_k`: pattern, sites. -/
abbrev AvIdx (N k : ℕ) : Type := (Fin k → Bool) × (Fin k → Fin N)

namespace PsiData

variable (P : PsiData N)

/-- `Υ_t = polynomialControl N W D η_t`, `η_t = vsHeight z t`. -/
def ups (t : ℝ) : Matrix (Fin N) (Fin N) ℝ := polynomialControl N P.W P.D (vsHeight P.z t)

/-- `ℓ_t η_t`. -/
def lEta (t : ℝ) : ℝ := localizationLength N P.W (vsHeight P.z t) * vsHeight P.z t

/-- The M-term `M^{(t)}_{[1,k]}` (diagonal) of pattern `σ` and sites `x`. -/
def mChain (σ : Fin k → Bool) (x : Fin k → Fin N) (t : ℝ) : Fin N → ℂ :=
  Split.chainM t P.S (patM P.z σ) (obsSeq P.S x) 1 k

/-- `𝒴^k_t(a, x', b) = ((G - M)_{[1,k],t}(x'))_{ab}`. -/
def isoErr (σ : Fin k → Bool) (a b : Fin N) (x : Fin k → Fin N) (t : ℝ)
    (H : Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  gChain (patZ P.z σ t) (isoSlots P.S x) H a b - if a = b then P.mChain σ x t a else 0

/-- `𝒳^k_t(x) = Tr[(G - M)_{[1,k],t}(x') S^{x_k}]` (unnormalized trace). -/
def avErr (σ : Fin k → Bool) (x : Fin k → Fin N) (t : ℝ) (H : Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  Matrix.trace (gChain (patZ P.z σ t) (avSlots P.S x) H) -
    ∑ a, P.mChain σ x t a * obsSeq P.S x k a

/-- Isotropic size function `s^iso_{k,t}(a, x', b)` -/
def sIso (a b : Fin N) (x : Fin k → Fin N) (t : ℝ) : ℝ :=
  P.lEta t ^ (-((k : ℝ) - 1) / 2) *
    Real.sqrt (∏ i ∈ Finset.range k, P.ups t (isoPoint a b x i) (isoPoint a b x (i + 1)))

/-- Averaged size function `s^av_{k,t}(x)` (`s^av_1 = 1/(ℓη)`). -/
def sAv (x : Fin k → Fin N) (t : ℝ) : ℝ :=
  if k = 1 then (P.lEta t)⁻¹
  else P.lEta t ^ (-(k : ℝ) / 2) * Real.sqrt (∏ j : Fin k, P.ups t (x j) (x (finRotate k j)))

/-- The isotropic ratio `|𝒴|/((ℓη)^{α_k} s^iso)`. -/
def isoRatio (i : IsoIdx N k) (t : ℝ) (H : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  ‖P.isoErr i.1 i.2.1 i.2.2.1 i.2.2.2 t H‖ /
    (P.lEta t ^ Expo.lossAlpha k * P.sIso i.2.1 i.2.2.1 i.2.2.2 t)

/-- The averaged ratio `|𝒳|/((ℓη)^{β_k} s^av)`. -/
def avRatio (i : AvIdx N k) (t : ℝ) (H : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  ‖P.avErr i.1 i.2 t H‖ / (P.lEta t ^ Expo.lossBeta k * P.sAv i.2 t)

/-- `Ψ^iso_{k,t}(H)`: the maximum of the isotropic ratios. -/
def bigPsiIso (k : ℕ) (t : ℝ) (H : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  ((Finset.univ.sup fun i : IsoIdx N k => (P.isoRatio i t H).toNNReal : ℝ≥0) : ℝ)

/-- `Ψ^av_{k,t}(H)`: the maximum of the averaged ratios. -/
def bigPsiAv (k : ℕ) (t : ℝ) (H : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  ((Finset.univ.sup fun i : AvIdx N k => (P.avRatio i t H).toNNReal : ℝ≥0) : ℝ)

/-!
### The maximum
-/

theorem le_sup_toNNReal_iff {ι : Type} [Fintype ι] (f : ι → ℝ) {c : ℝ} (hc : 0 < c) :
    c ≤ ((Finset.univ.sup fun i => (f i).toNNReal : ℝ≥0) : ℝ) ↔ ∃ i, c ≤ f i := by
  rw [← Real.toNNReal_le_iff_le_coe, Finset.le_sup_iff (by simpa using hc)]
  constructor
  · rintro ⟨i, -, hi⟩
    refine ⟨i, ?_⟩
    have h1 : 0 < (f i).toNNReal := lt_of_lt_of_le (by simpa using hc) hi
    rwa [Real.toNNReal_le_toNNReal_iff (Real.toNNReal_pos.mp h1).le] at hi
  · rintro ⟨i, hi⟩
    exact ⟨i, Finset.mem_univ _, Real.toNNReal_le_toNNReal hi⟩

theorem le_sup_toNNReal {ι : Type} [Fintype ι] (f : ι → ℝ) (i : ι) :
    f i ≤ ((Finset.univ.sup fun i => (f i).toNNReal : ℝ≥0) : ℝ) :=
  (Real.le_coe_toNNReal (f i)).trans
    (NNReal.coe_le_coe.mpr (Finset.le_sup (f := fun i => (f i).toNNReal) (Finset.mem_univ i)))

theorem bigPsiIso_nonneg (t : ℝ) (H : Matrix (Fin N) (Fin N) ℂ) : 0 ≤ P.bigPsiIso k t H :=
  NNReal.coe_nonneg _

theorem bigPsiAv_nonneg (t : ℝ) (H : Matrix (Fin N) (Fin N) ℂ) : 0 ≤ P.bigPsiAv k t H :=
  NNReal.coe_nonneg _

theorem isoRatio_le_bigPsiIso (i : IsoIdx N k) (t : ℝ) (H : Matrix (Fin N) (Fin N) ℂ) :
    P.isoRatio i t H ≤ P.bigPsiIso k t H :=
  le_sup_toNNReal (fun i => P.isoRatio i t H) i

theorem avRatio_le_bigPsiAv (i : AvIdx N k) (t : ℝ) (H : Matrix (Fin N) (Fin N) ℂ) :
    P.avRatio i t H ≤ P.bigPsiAv k t H :=
  le_sup_toNNReal (fun i => P.avRatio i t H) i

/-- For `c > 0`: `c ≤ Ψ^iso_{k,t}(H)` iff some isotropic ratio is `≥ c`. -/
theorem le_bigPsiIso_iff (t : ℝ) (H : Matrix (Fin N) (Fin N) ℂ) {c : ℝ} (hc : 0 < c) :
    c ≤ P.bigPsiIso k t H ↔ ∃ i : IsoIdx N k, c ≤ P.isoRatio i t H :=
  le_sup_toNNReal_iff (fun i => P.isoRatio i t H) hc

/-- For `c > 0`: `c ≤ Ψ^av_{k,t}(H)` iff some averaged ratio is `≥ c`. -/
theorem le_bigPsiAv_iff (t : ℝ) (H : Matrix (Fin N) (Fin N) ℂ) {c : ℝ} (hc : 0 < c) :
    c ≤ P.bigPsiAv k t H ↔ ∃ i : AvIdx N k, c ≤ P.avRatio i t H :=
  le_sup_toNNReal_iff (fun i => P.avRatio i t H) hc

end PsiData

/-!
### Bridges
-/

/-- `Chains.resChain 0 L w B y` is `gChain w B (L y)`. -/
theorem resChain_zero_eq_gChain {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →ₗ[ℝ] Matrix (Fin N) (Fin N) ℂ) (w : Fin k → ℂ)
    (B : Fin k → Matrix (Fin N) (Fin N) ℂ) (y : V) :
    Chains.resChain 0 L w B y = gChain w B (L y) := by
  simp only [Chains.resChain, gChain]
  congr 1
  funext j
  simp [Chains.resSlots, Chains.res]

/-- On `t ≤ 1` the pattern parameters are the VS saturated ones. -/
theorem patZ_eq_vsPatternSpec (z : ℂ) (σ : Fin k → Bool) {t : ℝ} (ht : t ≤ 1)
    (hδ : 0 ≤ z.im / (2 * (semicircleM z).im)) (j : Fin k) :
    patZ z σ t j = VS.vsPatternSpec z (semicircleM z) σ j t := by
  unfold patZ VS.vsPatternSpec
  rw [VS.vsSpec_of_le_one _ _ hδ ht]
  cases σ j <;> simp [VS.patConj, vsTraj, map_add, map_mul, map_sub]

theorem patM_of_mem (z : ℂ) (σ : Fin k → Bool) (j : Fin k) :
    patM z σ (j.val + 1) = VS.patConj (σ j) (semicircleM z) := by
  have h : 1 ≤ j.val + 1 ∧ j.val + 1 ≤ k := ⟨by omega, j.isLt⟩
  simp only [patM, h, and_self, dite_true, Nat.add_sub_cancel, Fin.eta]

theorem norm_patConj (b : Bool) (w : ℂ) : ‖VS.patConj b w‖ = ‖w‖ := by
  cases b <;> simp [VS.patConj]

/-- `‖m_i‖ < 1` for every `i` (`Im z ≠ 0`). -/
theorem norm_patM_lt_one {z : ℂ} (hz : z.im ≠ 0) (σ : Fin k → Bool) (i : ℕ) :
    ‖patM z σ i‖ < 1 := by
  unfold patM
  split_ifs
  · rw [norm_patConj]
    exact norm_semicircleM_lt_one hz
  · simp

/-!
### The floor of the size functions
-/

/-- `X^{-(1+D)} ≤ Υ_h(x,y)` for `X = (1+√H) N`, `0 < h ≤ H`, `H ≥ 1`, `1 ≤ W ≤ N`, `D ≥ 0`. -/
theorem rpow_le_polynomialControl {W : ℕ} (hW : 0 < W) (hWN : W ≤ N) {D : ℝ} (hD : 0 ≤ D)
    {H h : ℝ} (hH : 1 ≤ H) (hh : 0 < h) (hhH : h ≤ H) (x y : Fin N) :
    ((1 + Real.sqrt H) * N) ^ (-(1 + D)) ≤ polynomialControl N W D h x y := by
  have hN : 0 < N := lt_of_lt_of_le hW hWN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hWN' : (W : ℝ) ≤ N := by exact_mod_cast hWN
  have hsH : 1 ≤ Real.sqrt H := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hH
  set A := 1 + Real.sqrt H
  have hX : 1 ≤ A * N := by nlinarith
  have hX0 : 0 < A * N := by linarith
  refine le_trans ?_ (polynomialControl_lower hWN hW hD hH hh hhH x y)
  set d : ℝ := (cyclicDistance N x y : ℝ)
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have hdN : d ≤ N := by
    have := Adapters.ErdosRiabov.two_mul_cyclicDistance_le N x y
    have h2 : (2 * cyclicDistance N x y : ℝ) ≤ N := by exact_mod_cast this
    simp only [d]
    linarith
  have h1 : (A * N) ^ (-(1 : ℝ)) ≤ ((W : ℝ) * Real.sqrt H)⁻¹ := by
    rw [Real.rpow_neg_one]
    apply inv_anti₀ (by positivity)
    nlinarith
  have hq : 0 < 1 + Real.sqrt H * d / W := by positivity
  have h2 : (A * N) ^ (-D) ≤ (1 + Real.sqrt H * d / W) ^ (-D) := by
    apply Real.rpow_le_rpow_of_nonpos hq _ (by linarith)
    have : Real.sqrt H * d / W ≤ Real.sqrt H * N := by
      rw [div_le_iff₀ (by linarith)]
      have hs0 := Real.sqrt_nonneg H
      nlinarith [mul_le_mul_of_nonneg_left hdN hs0,
        mul_le_mul_of_nonneg_left hW1 (mul_nonneg hs0 (by linarith : (0 : ℝ) ≤ N))]
    nlinarith
  rw [show -(1 + D) = -(1 : ℝ) + -D by ring, Real.rpow_add hX0]
  exact mul_le_mul h1 h2 (Real.rpow_nonneg hX0.le _) (by positivity)

theorem rpow_le_prod {ι : Type} (s : Finset ι) (f : ι → ℝ) {X e : ℝ} (hX : 0 < X)
    (hf : ∀ i ∈ s, X ^ (-e) ≤ f i) : X ^ (-e * s.card) ≤ ∏ i ∈ s, f i := by
  have h := Finset.prod_le_prod₀ (fun i _ => (Real.rpow_pos_of_pos hX (-e)).le) hf
  rw [Finset.prod_const, ← Real.rpow_natCast, ← Real.rpow_mul hX.le] at h
  exact h

theorem rpow_le_sqrt_prod {ι : Type} (s : Finset ι) (f : ι → ℝ) {X e : ℝ} (hX : 0 < X)
    (hf : ∀ i ∈ s, X ^ (-e) ≤ f i) : X ^ (-e * s.card / 2) ≤ Real.sqrt (∏ i ∈ s, f i) := by
  have h := Real.sqrt_le_sqrt (rpow_le_prod s f hX hf)
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hX.le] at h
  convert h using 2
  ring

namespace PsiData

variable (P : PsiData N)

/-- `0 < η_t ≤ C₀+1`, `0 < ℓ_tη_t ≤ W √(C₀+1)` on `z ∈ 𝒟`, `t ∈ [0,1]`. -/
theorem height_bounds {δ₀ κ C₀ : ℝ} {W : ℕ} (hN : 0 < N) (hW : 0 < W) (hWN : W ≤ N) (hκ : 0 < κ)
    (hC₀ : 0 ≤ C₀) (hz : BulkDomain N δ₀ κ C₀ P.z) (hPW : P.W = W) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    0 < vsHeight P.z t ∧ vsHeight P.z t ≤ C₀ + 1 ∧ 0 < P.lEta t ∧
      P.lEta t ≤ (W : ℝ) * Real.sqrt (C₀ + 1) := by
  obtain ⟨_, _, _, _, hbd, _, hC, _, _, _, _⟩ := vsFlow_b hN hκ hC₀ hz
  have hη := hz.im_pos hN
  have hpos : 0 < vsHeight P.z t := hη.trans_le (hbd t ht0 ht1).1
  have hle : vsHeight P.z t ≤ C₀ + 1 := (hbd t ht0 ht1).2.trans hC
  refine ⟨hpos, hle, ?_, ?_⟩
  · unfold lEta
    rw [hPW]
    exact mul_pos (Adapters.ErdosRiabov.loc_pos hN hW hpos) hpos
  · unfold lEta
    rw [hPW]
    exact (loc_bounds_of_le hWN (by linarith) hpos hle).2

/-- **Floor of `s^iso`**: on `z ∈ 𝒟` (`N, W ≥ 1`, `W ≤ N`, `κ > 0`, `C₀ ≥ 0`, `D ≥ 0`),
`t ∈ [0,1]`, `k ≥ 1`: `s^iso_{k,t}(a,x',b) ≥ (A N)^{-k(2+D)}`, `A = 1 + √(C₀+1)`. -/
theorem sIso_floor {δ₀ κ C₀ : ℝ} {W : ℕ} (hN : 0 < N) (hW : 0 < W) (hWN : W ≤ N) (hκ : 0 < κ)
    (hC₀ : 0 ≤ C₀) (hD : 0 ≤ P.D) (hz : BulkDomain N δ₀ κ C₀ P.z) (hPW : P.W = W)
    (hk : 1 ≤ k) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (a b : Fin N) (x : Fin k → Fin N) :
    ((1 + Real.sqrt (C₀ + 1)) * N) ^ (-((k : ℝ) * (2 + P.D))) ≤ P.sIso a b x t := by
  obtain ⟨hη, hηC, hL, hLW⟩ := P.height_bounds hN hW hWN hκ hC₀ hz hPW ht0 ht1
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hWN' : (W : ℝ) ≤ N := by exact_mod_cast hWN
  have hsH : 1 ≤ Real.sqrt (C₀ + 1) := Real.one_le_sqrt.mpr (by linarith)
  set X := (1 + Real.sqrt (C₀ + 1)) * N
  have hX : 1 ≤ X := by nlinarith
  have hX0 : 0 < X := by linarith
  have hLX : P.lEta t ≤ X := hLW.trans (by nlinarith)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hups : ∀ i ∈ Finset.range k, X ^ (-(1 + P.D)) ≤
      P.ups t (isoPoint a b x i) (isoPoint a b x (i + 1)) := fun i _ => by
    unfold ups
    rw [hPW]
    exact rpow_le_polynomialControl hW hWN hD (by linarith) hη hηC _ _
  have hsq := rpow_le_sqrt_prod _ _ hX0 hups
  rw [Finset.card_range] at hsq
  have hl : X ^ (-((k : ℝ) - 1) / 2) ≤ P.lEta t ^ (-((k : ℝ) - 1) / 2) :=
    Real.rpow_le_rpow_of_nonpos hL hLX (by linarith)
  unfold sIso
  calc X ^ (-((k : ℝ) * (2 + P.D)))
      ≤ X ^ (-((k : ℝ) - 1) / 2 + -(1 + P.D) * k / 2) :=
        Real.rpow_le_rpow_of_exponent_le hX (by nlinarith)
    _ = X ^ (-((k : ℝ) - 1) / 2) * X ^ (-(1 + P.D) * k / 2) := Real.rpow_add hX0 _ _
    _ ≤ _ := mul_le_mul hl hsq (Real.rpow_nonneg hX0.le _) (Real.rpow_nonneg hL.le _)

/-- **Floor of `s^av`**: under the hypotheses of `sIso_floor`,
`s^av_{k,t}(x) ≥ (A N)^{-k(2+D)}`. -/
theorem sAv_floor {δ₀ κ C₀ : ℝ} {W : ℕ} (hN : 0 < N) (hW : 0 < W) (hWN : W ≤ N) (hκ : 0 < κ)
    (hC₀ : 0 ≤ C₀) (hD : 0 ≤ P.D) (hz : BulkDomain N δ₀ κ C₀ P.z) (hPW : P.W = W)
    (hk : 1 ≤ k) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x : Fin k → Fin N) :
    ((1 + Real.sqrt (C₀ + 1)) * N) ^ (-((k : ℝ) * (2 + P.D))) ≤ P.sAv x t := by
  obtain ⟨hη, hηC, hL, hLW⟩ := P.height_bounds hN hW hWN hκ hC₀ hz hPW ht0 ht1
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hWN' : (W : ℝ) ≤ N := by exact_mod_cast hWN
  have hsH : 1 ≤ Real.sqrt (C₀ + 1) := Real.one_le_sqrt.mpr (by linarith)
  set X := (1 + Real.sqrt (C₀ + 1)) * N
  have hX : 1 ≤ X := by nlinarith
  have hX0 : 0 < X := by linarith
  have hLX : P.lEta t ≤ X := hLW.trans (by nlinarith)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  unfold sAv
  split_ifs with h1
  · subst h1
    calc X ^ (-(((1 : ℕ) : ℝ) * (2 + P.D))) ≤ X ^ (-(1 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hX (by push_cast; linarith)
      _ = X⁻¹ := Real.rpow_neg_one X
      _ ≤ (P.lEta t)⁻¹ := inv_anti₀ hL hLX
  · have hups : ∀ j ∈ (Finset.univ : Finset (Fin k)), X ^ (-(1 + P.D)) ≤
        P.ups t (x j) (x (finRotate k j)) := fun j _ => by
      unfold ups
      rw [hPW]
      exact rpow_le_polynomialControl hW hWN hD (by linarith) hη hηC _ _
    have hsq := rpow_le_sqrt_prod _ _ hX0 hups
    rw [Finset.card_univ, Fintype.card_fin] at hsq
    have hl : X ^ (-(k : ℝ) / 2) ≤ P.lEta t ^ (-(k : ℝ) / 2) :=
      Real.rpow_le_rpow_of_nonpos hL hLX (by linarith)
    calc X ^ (-((k : ℝ) * (2 + P.D)))
        ≤ X ^ (-(k : ℝ) / 2 + -(1 + P.D) * k / 2) :=
          Real.rpow_le_rpow_of_exponent_le hX (by nlinarith)
      _ = X ^ (-(k : ℝ) / 2) * X ^ (-(1 + P.D) * k / 2) := Real.rpow_add hX0 _ _
      _ ≤ _ := mul_le_mul hl hsq (Real.rpow_nonneg hX0.le _) (Real.rpow_nonneg hL.le _)

/-- From `(A N)^{-k(2+D)}` to `N^{-K(2D''+1)}` (`k ≤ K = 8`, `N ≥ A^{K(2+D)}`,
`K(2+D) + 1 ≤ K(2D''+1)`). -/
theorem floor_to_vsK {A D Dpp : ℝ} (hA : 1 ≤ A) (hD : 0 ≤ D) (hN : 0 < N)
    (hDpp : (vsK : ℝ) * (2 + D) + 1 ≤ (vsK : ℝ) * (2 * Dpp + 1))
    (hNA : A ^ ((vsK : ℝ) * (2 + D)) ≤ N) (hk : k ≤ vsK) :
    (N : ℝ) ^ (-((vsK : ℝ) * (2 * Dpp + 1))) ≤ (A * N) ^ (-((k : ℝ) * (2 + D))) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hA0 : 0 < A := by linarith
  have hX : 1 ≤ A * N := by nlinarith
  have hkK : (k : ℝ) ≤ vsK := by exact_mod_cast hk
  set E := (vsK : ℝ) * (2 + D)
  have hE : 0 ≤ E := by unfold E vsK; positivity
  calc (N : ℝ) ^ (-((vsK : ℝ) * (2 * Dpp + 1)))
      ≤ (N : ℝ) ^ (-(E + 1)) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    _ = (N : ℝ)⁻¹ * (N : ℝ) ^ (-E) := by
        rw [show -(E + 1) = -(1 : ℝ) + -E by ring, Real.rpow_add hN0, Real.rpow_neg_one]
    _ ≤ (A ^ E)⁻¹ * (N : ℝ) ^ (-E) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hN0.le _)
        exact inv_anti₀ (Real.rpow_pos_of_pos hA0 _) hNA
    _ = (A * N) ^ (-E) := by
        rw [Real.mul_rpow hA0.le hN0.le, Real.rpow_neg hA0.le]
    _ ≤ (A * N) ^ (-((k : ℝ) * (2 + D))) :=
        Real.rpow_le_rpow_of_exponent_le hX (by unfold E; nlinarith)

/-- **Floor of both size functions** (`≥ N^{-K(2D''+1)}`): under the hypotheses of
`sIso_floor`, `k ≤ K = 8`, `K(2+D) + 1 ≤ K(2D''+1)` and `N ≥ A^{K(2+D)}`,
`A = 1 + √(C₀+1)`, both size functions are `≥ N^{-K(2D''+1)}`. -/
theorem sizes_floor_vsK {δ₀ κ C₀ Dpp : ℝ} {W : ℕ} (hN : 0 < N) (hW : 0 < W) (hWN : W ≤ N)
    (hκ : 0 < κ) (hC₀ : 0 ≤ C₀) (hD : 0 ≤ P.D) (hz : BulkDomain N δ₀ κ C₀ P.z)
    (hPW : P.W = W) (hk : 1 ≤ k) (hkK : k ≤ vsK)
    (hDpp : (vsK : ℝ) * (2 + P.D) + 1 ≤ (vsK : ℝ) * (2 * Dpp + 1))
    (hNA : (1 + Real.sqrt (C₀ + 1)) ^ ((vsK : ℝ) * (2 + P.D)) ≤ N)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∀ (a b : Fin N) (x : Fin k → Fin N),
        (N : ℝ) ^ (-((vsK : ℝ) * (2 * Dpp + 1))) ≤ P.sIso a b x t) ∧
      ∀ x : Fin k → Fin N, (N : ℝ) ^ (-((vsK : ℝ) * (2 * Dpp + 1))) ≤ P.sAv x t := by
  have hA : 1 ≤ 1 + Real.sqrt (C₀ + 1) := by linarith [Real.sqrt_nonneg (C₀ + 1)]
  have hf := floor_to_vsK (N := N) (k := k) hA hD hN hDpp hNA hkK
  exact ⟨fun a b x => hf.trans (P.sIso_floor hN hW hWN hκ hC₀ hD hz hPW hk ht0 ht1 a b x),
    fun x => hf.trans (P.sAv_floor hN hW hWN hκ hC₀ hD hz hPW hk ht0 ht1 x)⟩

end PsiData

/-- The parameter block satisfies the exponent condition of the floor:
`K(2+D) + 1 ≤ K(2D''+1)` for `D'' = (1+2C₀'')(D+1)/2`. -/
theorem floor_exponent_le_of_vsData (d : VSData) :
    (vsK : ℝ) * (2 + d.D) + 1 ≤ (vsK : ℝ) * (2 * d.Dpp + 1) := by
  have h1 := d.one_le_C0pp
  have hD := d.D_ge_six
  unfold VSData.Dpp vsK
  push_cast
  nlinarith

end BlockBand.Native.ErdosRiabov.Psi
