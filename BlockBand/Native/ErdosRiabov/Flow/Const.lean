module

public import BlockBand.Native.ErdosRiabov.Kernel.Semicircle
public import BlockBand.Adapters.ErdosRiabov.ShortRingAdmissibility

/-!
# The VS parameters and constants

`VSData` records the model data (`0 < b < 1/2`, `0 < δ₀ < ζ₀`, `κ > 0`, `C₀ ≥ 1`, `D ≥ 6`) and the
tolerance `ε > 0`. From it we define
* the hierarchy depth `K = 8`;
* `s_κ = bulkSin κ`, `κ' = phaseConst κ`, `c_m = imLower κ C₀`, `r = √(C₀+1)`;
* the ceiling `C₀'' = 2(C₀+1)`;
* `C₁'' = admissibilityConstant b κ' C₀'' D`, `D'' = (1+2C₀'')(D+1)/2`, and
  `C_wc = (C₁'')^{3/2}`, `C_rev = (C₀+1)^{1+D/2}`, `c_♭ = min 1 (16 c_m)`;
* the exponents `ξ = min(ε,δ₀)/200`, `ν = ξ/640` and the thresholds `ψ^iso_k = N^{ξ+kν}`,
  `ψ^av_k = N^{ξ+(k+3/2)ν}`;
* the slack `ε' = ν/16 ∈ (0, ν/8)`;
and prove positivity and order facts (`vsConst_facts`, `vsThreshold_facts`).

The kernel constant `C_K` is defined with the kernel bounds, not here.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Flow

open BlockBand.Native.ErdosRiabov.Kernel

/-- The model data `b, δ₀, ζ₀, κ, C₀, D` together with the tolerance `ε`. -/
structure VSData where
  b : ℝ
  delta0 : ℝ
  zeta0 : ℝ
  kappa : ℝ
  C0 : ℝ
  D : ℝ
  eps : ℝ
  b_pos : 0 < b
  b_lt_half : b < 1 / 2
  delta0_pos : 0 < delta0
  delta0_lt_zeta0 : delta0 < zeta0
  kappa_pos : 0 < kappa
  C0_ge_one : 1 ≤ C0
  D_ge_six : 6 ≤ D
  eps_pos : 0 < eps

/-- The hierarchy depth `K = 8`. -/
def vsK : ℕ := 8

namespace VSData

variable (d : VSData)

/-- `s_κ`. -/
def sK : ℝ := bulkSin d.kappa

/-- `κ' = min κ 1`. -/
def kappaP : ℝ := phaseConst d.kappa

/-- `c_m = s_κ/(C₀+1)`. -/
def cm : ℝ := imLower d.kappa d.C0

/-- `r = √(C₀+1)`. -/
def r : ℝ := Real.sqrt (d.C0 + 1)

/-- The ceiling `C₀'' = 2(C₀+1)`. -/
def C0pp : ℝ := 2 * (d.C0 + 1)

/-- `C₁'' = admissibilityConstant b κ' C₀'' D`. -/
def C1pp : ℝ :=
  Adapters.ErdosRiabov.admissibilityConstant d.b d.b_pos d.b_lt_half d.kappaP d.C0pp d.D

/-- `D'' = (1+2C₀'')(D+1)/2`. -/
def Dpp : ℝ := (1 + 2 * d.C0pp) * (d.D + 1) / 2

/-- `C_wc = (C₁'')^{3/2}`. -/
def Cwc : ℝ := d.C1pp ^ (3 / 2 : ℝ)

/-- `C_rev = (C₀+1)^{1+D/2}`. -/
def Crev : ℝ := (d.C0 + 1) ^ (1 + d.D / 2)

/-- `c_♭ = min 1 (16 c_m)`. -/
def cflat : ℝ := min 1 (16 * d.cm)

/-- `ξ = min(ε,δ₀)/200`. -/
def xi : ℝ := min d.eps d.delta0 / 200

/-- `ν = ξ/(10K²) = ξ/640`. -/
def nu : ℝ := d.xi / 640

/-- The slack `ε' = ν/16` (any value in `(0, ν/8)` is admissible). -/
def epsP : ℝ := d.nu / 16

/-- Isotropic thresholds `ψ^iso_k = N^{ξ+kν}`. -/
def psiIso (N : ℕ) (k : ℝ) : ℝ := (N : ℝ) ^ (d.xi + k * d.nu)

/-- Averaged thresholds `ψ^av_k = N^{ξ+(k+3/2)ν}`. -/
def psiAv (N : ℕ) (k : ℝ) : ℝ := (N : ℝ) ^ (d.xi + (k + 3 / 2) * d.nu)

theorem kappa_hat_bounds : 0 < min d.kappa 2 ∧ min d.kappa 2 ≤ 2 :=
  ⟨lt_min d.kappa_pos two_pos, min_le_right _ _⟩

theorem sK_pos : 0 < d.sK := by
  have h := d.kappa_hat_bounds
  have h1 : 0 < min d.kappa 2 * (4 - min d.kappa 2) := mul_pos h.1 (by linarith)
  unfold sK bulkSin
  positivity

theorem sK_le_one : d.sK ≤ 1 := by
  unfold sK bulkSin
  rw [div_le_one two_pos, Real.sqrt_le_left zero_le_two]
  nlinarith [sq_nonneg (min d.kappa 2 - 2)]

theorem kappaP_pos : 0 < d.kappaP := lt_min d.kappa_pos one_pos

theorem kappaP_le_one : d.kappaP ≤ 1 := min_le_right _ _

theorem kappaP_le_kappa : d.kappaP ≤ d.kappa := min_le_left _ _

theorem C0_add_one_pos : 0 < d.C0 + 1 := by linarith [d.C0_ge_one]

theorem cm_pos : 0 < d.cm := div_pos d.sK_pos d.C0_add_one_pos

theorem cm_le_sK : d.cm ≤ d.sK := by
  have h := d.sK_pos
  unfold cm imLower
  unfold sK at h ⊢
  rw [div_le_iff₀ d.C0_add_one_pos]
  nlinarith [d.C0_ge_one]

theorem cm_le_half : d.cm ≤ 1 / 2 := by
  have h := d.sK_le_one
  unfold cm imLower
  unfold sK at h
  rw [div_le_iff₀ d.C0_add_one_pos]
  nlinarith [d.C0_ge_one]

theorem r_sq : d.r ^ 2 = d.C0 + 1 := Real.sq_sqrt d.C0_add_one_pos.le

theorem one_lt_r : 1 < d.r := by
  unfold r
  rw [Real.lt_sqrt zero_le_one]
  linarith [d.C0_ge_one]

theorem C0pp_ge : d.C0 + 1 ≤ d.C0pp := by
  unfold C0pp
  linarith [d.C0_ge_one]

theorem one_le_C0pp : 1 ≤ d.C0pp := by
  linarith [d.C0pp_ge, d.C0_ge_one]

theorem one_le_C1pp : 1 ≤ d.C1pp := by
  unfold C1pp Adapters.ErdosRiabov.admissibilityConstant
  exact le_max_left _ _

theorem Dpp_pos : 0 < d.Dpp := by
  unfold Dpp
  have := d.one_le_C0pp
  have := d.D_ge_six
  positivity

theorem one_le_Cwc : 1 ≤ d.Cwc := Real.one_le_rpow d.one_le_C1pp (by norm_num)

theorem one_le_Crev : 1 ≤ d.Crev := by
  apply Real.one_le_rpow (by linarith [d.C0_ge_one])
  linarith [d.D_ge_six]

theorem cflat_pos : 0 < d.cflat := lt_min one_pos (by linarith [d.cm_pos])

theorem cflat_le_one : d.cflat ≤ 1 := min_le_left _ _

theorem xi_pos : 0 < d.xi := div_pos (lt_min d.eps_pos d.delta0_pos) (by norm_num)

theorem xi_le_eps : d.xi ≤ d.eps / 200 :=
  div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)

theorem xi_le_delta0 : d.xi ≤ d.delta0 / 200 :=
  div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)

theorem xi_lt_delta0_div : d.xi < d.delta0 / 100 := by
  linarith [d.xi_le_delta0, d.delta0_pos]

theorem nu_pos : 0 < d.nu := div_pos d.xi_pos (by norm_num)

theorem nu_eq : d.nu = d.xi / (10 * (vsK : ℝ) ^ 2) := by
  unfold nu vsK
  norm_num

theorem epsP_pos : 0 < d.epsP := div_pos d.nu_pos (by norm_num)

theorem epsP_lt : d.epsP < d.nu / 8 := by
  unfold epsP
  linarith [d.nu_pos]

/-- The top threshold exponent is below `ε`: `ξ + (K+3/2)ν < ξ + ε`, i.e. `(K+3/2)ν < ε`
(used in the zig step: `ψ_k ≤ N^{ξ+(K+3/2)ν} ≤ N^{ξ+ε}`). -/
theorem top_exponent_lt_eps : ((vsK : ℝ) + 3 / 2) * d.nu < d.eps := by
  unfold vsK nu
  have := d.xi_le_eps
  have := d.xi_pos
  have := d.eps_pos
  push_cast
  nlinarith

/-- Positivity and order facts of the absolute, bulk, ceiling, flatness (`c_♭`), tolerance and slack
constants, all depending only on the data `d` (not on `N`, `m`, `W`, `z`). -/
theorem vsConst_facts :
    vsK = 8 ∧ 0 < d.sK ∧ d.sK ≤ 1 ∧ 0 < d.kappaP ∧ d.kappaP ≤ 1 ∧ d.kappaP ≤ d.kappa ∧
      0 < d.cm ∧ d.cm ≤ d.sK ∧ d.cm ≤ 1 / 2 ∧ d.r ^ 2 = d.C0 + 1 ∧ 1 < d.r ∧
      d.C0 + 1 ≤ d.C0pp ∧ 1 ≤ d.C1pp ∧ 0 < d.Dpp ∧ 1 ≤ d.Cwc ∧ 1 ≤ d.Crev ∧
      0 < d.cflat ∧ d.cflat ≤ 1 ∧ 0 < d.xi ∧ d.xi ≤ d.eps / 200 ∧ d.xi ≤ d.delta0 / 200 ∧
      d.xi < d.delta0 / 100 ∧ 0 < d.nu ∧ d.nu = d.xi / 640 ∧ 0 < d.epsP ∧
      d.epsP < d.nu / 8 ∧ ((vsK : ℝ) + 3 / 2) * d.nu < d.eps :=
  ⟨rfl, d.sK_pos, d.sK_le_one, d.kappaP_pos, d.kappaP_le_one, d.kappaP_le_kappa, d.cm_pos,
    d.cm_le_sK, d.cm_le_half, d.r_sq, d.one_lt_r, d.C0pp_ge, d.one_le_C1pp, d.Dpp_pos,
    d.one_le_Cwc, d.one_le_Crev, d.cflat_pos, d.cflat_le_one, d.xi_pos, d.xi_le_eps,
    d.xi_le_delta0, d.xi_lt_delta0_div, d.nu_pos, rfl, d.epsP_pos, d.epsP_lt,
    d.top_exponent_lt_eps⟩

/-- `ψ^av_k = N^{3ν/2} ψ^iso_k` (`N ≥ 1`). -/
theorem psiAv_eq {N : ℕ} (hN : 0 < N) (k : ℝ) :
    d.psiAv N k = (N : ℝ) ^ (3 / 2 * d.nu) * d.psiIso N k := by
  unfold psiAv psiIso
  rw [← Real.rpow_add (by exact_mod_cast hN)]
  congr 1
  ring

/-- For `N ≥ 1` and real indices `k ≤ k'`:
`1 ≤ N^ξ ≤ ψ^iso_k ≤ ψ^av_k`; both families are monotone in `k`;
`ψ^av_k = N^{3ν/2} ψ^iso_k`;
`ψ^av_k ≤ ψ^iso_{k+2}`; and for `k ≤ K`,
`ψ^av_k ≤ N^{ξ+ε}` (so also `ψ^iso_k ≤ N^{ξ+ε}`).
-/
theorem vsThreshold_facts {N : ℕ} (hN : 0 < N) {k k' : ℝ} (hk : 0 ≤ k) (hkk : k ≤ k') :
    1 ≤ (N : ℝ) ^ d.xi ∧ (N : ℝ) ^ d.xi ≤ d.psiIso N k ∧ d.psiIso N k ≤ d.psiAv N k ∧
      d.psiIso N k ≤ d.psiIso N k' ∧ d.psiAv N k ≤ d.psiAv N k' ∧
      d.psiAv N k = (N : ℝ) ^ (3 / 2 * d.nu) * d.psiIso N k ∧
      d.psiAv N k ≤ d.psiIso N (k + 2) ∧
      (k ≤ (vsK : ℝ) → d.psiAv N k ≤ (N : ℝ) ^ (d.xi + d.eps)) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hnu := d.nu_pos
  have hxi := d.xi_pos
  have mono : ∀ a b : ℝ, a ≤ b → (N : ℝ) ^ a ≤ (N : ℝ) ^ b :=
    fun a b h => Real.rpow_le_rpow_of_exponent_le hN1 h
  refine ⟨Real.one_le_rpow hN1 hxi.le, mono _ _ (by nlinarith), mono _ _ (by nlinarith),
    mono _ _ (by nlinarith), mono _ _ (by nlinarith), d.psiAv_eq hN k,
    mono _ _ (by nlinarith), fun hkK => mono _ _ ?_⟩
  have := d.top_exponent_lt_eps
  nlinarith

end VSData

end BlockBand.Native.ErdosRiabov.Flow
