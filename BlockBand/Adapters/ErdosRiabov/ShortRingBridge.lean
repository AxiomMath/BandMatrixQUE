module

public import Mathlib
public import BlockBand.Internal.Contracts.Inputs
public import BlockBand.Adapters.ErdosRiabov.CyclicModel.ERAdmissibilityComplete

/-!
# The Erdős–Riabov cycle and the cyclic block sites

The row-major site equivalence `ZMod n × Fin W ≃ Fin (nW)` carries the short-ring profile,
the semicircle branch, the cyclic distance, the localization length, the spectral domain and
the kernels `Θ`, `Ξ` of the Erdős–Riabov cycle to their counterparts on the cyclic block sites.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Adapters.ErdosRiabov

open BlockBand.External
open scoped BigOperators

local instance (p : CyclicModel.Params) : NeZero p.n := p.nNeZero

/-- The model record of the short ring with `m` blocks of width `W` and bond `b`. -/
def cyclicModelParams (b : ℝ) (m W : ℕ) (hb0 : 0 < b) (hb : b < 1 / 2) (hm : 4 ≤ m) (hW : 0 < W) :
    CyclicModel.Params where
  n := m
  W := W
  b := b
  n_ge_four := hm
  W_ge_one := hW
  b_pos := hb0
  b_lt_half := hb

/-- The row-major site equivalence onto the cycle `Fin (n W)`. -/
def siteEquiv (p : CyclicModel.Params) : CyclicModel.Conventions.Site p.n p.W ≃ Fin (p.n * p.W) :=
  p.siteIndexEquiv

theorem siteEquiv_val (p : CyclicModel.Params) (x : CyclicModel.Conventions.Site p.n p.W) :
    (siteEquiv p x).val = x.2.val + p.W * x.1.val :=
  p.siteIndexEquiv_apply_val x

theorem siteEquiv_div (p : CyclicModel.Params) (x : CyclicModel.Conventions.Site p.n p.W) :
    (siteEquiv p x).val / p.W = x.1.val := by
  rw [siteEquiv_val, Nat.add_mul_div_left _ _ p.W_pos, Nat.div_eq_of_lt x.2.isLt, zero_add]

/-- `(k+1) mod m` for `k < m`. -/
theorem succ_mod_eq {m k : ℕ} (hk : k < m) : (k + 1) % m = if k + 1 = m then 0 else k + 1 := by
  split_ifs with h
  · rw [h, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

theorem zmod_val_add_one (p : CyclicModel.Params) (k : ZMod p.n) :
    (k + 1).val = (k.val + 1) % p.n := by
  have : Fact (1 < p.n) := ⟨by have := p.n_ge_four; omega⟩
  rw [ZMod.val_add, ZMod.val_one]

/-- The contract profile is the variance profile under the row-major equivalence. -/
theorem shortRingProfile_siteEquiv (p : CyclicModel.Params) (x y : CyclicModel.Conventions.Site p.n p.W) :
    Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W (siteEquiv p x) (siteEquiv p y) =
      CyclicModel.GaussianRing.varianceProfile p x y := by
  have hn := p.n_ge_four
  have hk := x.1.val_lt
  have hl := y.1.val_lt
  unfold Internal.Contracts.Inputs.shortRingProfile CyclicModel.GaussianRing.varianceProfile
    CyclicModel.GaussianRing.blockWeight
  rw [siteEquiv_div, siteEquiv_div]
  have e1 : y.1 = x.1 ↔ x.1.val = y.1.val := by
    rw [eq_comm]; exact ZMod.val_injective _ |>.eq_iff.symm
  have e2 : y.1 = x.1 + 1 ↔ y.1.val = (x.1.val + 1) % p.n := by
    rw [← zmod_val_add_one]; exact (ZMod.val_injective _).eq_iff.symm
  have e3 : y.1 = x.1 - 1 ↔ x.1.val = (y.1.val + 1) % p.n := by
    rw [← zmod_val_add_one, eq_sub_iff_add_eq, eq_comm]; exact (ZMod.val_injective _).eq_iff.symm
  simp only [e1, e2, e3, CyclicModel.Params.c, CyclicModel.Conventions.diagonalWeight]
  rw [succ_mod_eq hk, succ_mod_eq hl]
  have hW : (p.W : ℝ) ≠ 0 := ne_of_gt p.real_W_pos
  split_ifs <;> first | omega | (field_simp; ring)

/-- And semicircle branches coincide (same explicit formula). -/
theorem semicircleM_eq_erSemicircleStieltjes (z : ℂ) :
    ErdosRiabov.semicircleM z = CyclicModel.GaussianRing.erSemicircleStieltjes z := rfl

theorem cyclicDistance_siteEquiv (p : CyclicModel.Params) (x y : CyclicModel.Conventions.Site p.n p.W) :
    ErdosRiabov.cyclicDistance (p.n * p.W) (siteEquiv p x) (siteEquiv p y) =
      CyclicModel.GaussianRing.erSiteDistance p x y := rfl

theorem localizationLength_eq_erLocalizationLength (p : CyclicModel.Params) (η : ℝ) :
    ErdosRiabov.localizationLength (p.n * p.W) p.W η =
      CyclicModel.GaussianRing.erLocalizationLength p η := rfl

/-- The spectral domain is the one, with `κ, δ₀, C₀` read off the native
parameters.
-/
theorem spectralDomain_iff_erSpectralDomain (q : ErdosRiabov.ModelParameters) (p : CyclicModel.Params) (z : ℂ) :
    ErdosRiabov.SpectralDomain q (p.n * p.W) z ↔
      CyclicModel.GaussianRing.ERSpectralDomain p q.kappa q.delta0 q.C0 z := Iff.rfl

/-- The complexified contract profile, reindexed, is the complex profile. -/
theorem profile_submatrix (p : CyclicModel.Params) :
    ((Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W).map (algebraMap ℝ ℂ)).submatrix
        (siteEquiv p) (siteEquiv p) = CyclicModel.GaussianRing.erComplexVarianceProfile p := by
  ext x y
  simp only [Matrix.submatrix_apply, Matrix.map_apply, shortRingProfile_siteEquiv,
    CyclicModel.GaussianRing.erComplexVarianceProfile]
  rfl

/-- `A (1 - A)⁻¹` commutes with reindexing by an equivalence. -/
theorem kernel_submatrix {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℂ) (e : κ ≃ ι) :
    (A * (1 - A)⁻¹).submatrix e e = A.submatrix e e * (1 - A.submatrix e e)⁻¹ := by
  have h1 : (1 - A).submatrix e e = 1 - A.submatrix e e := by
    ext i j
    simp [Matrix.one_apply]
  rw [← Matrix.submatrix_mul_equiv A (1 - A)⁻¹ e e e, ← Matrix.inv_submatrix_equiv, h1]

theorem theta_siteEquiv (p : CyclicModel.Params) (z₁ z₂ : ℂ) (x y : CyclicModel.Conventions.Site p.n p.W) :
    ErdosRiabov.theta (Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W) z₁ z₂
        (siteEquiv p x) (siteEquiv p y) = CyclicModel.GaussianRing.erTheta p z₁ z₂ x y := by
  set c : ℂ := ErdosRiabov.semicircleM z₁ * starRingEnd ℂ (ErdosRiabov.semicircleM z₂)
  have hA : (c • (Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W).map
      (algebraMap ℝ ℂ)).submatrix (siteEquiv p) (siteEquiv p) =
        c • CyclicModel.GaussianRing.erComplexVarianceProfile p := by
    rw [← profile_submatrix]
    ext i j
    simp
  have h := kernel_submatrix (c • (Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W).map
    (algebraMap ℝ ℂ)) (siteEquiv p)
  rw [hA] at h
  exact congrFun (congrFun h x) y

theorem xi_siteEquiv (p : CyclicModel.Params) (z₁ z₂ : ℂ) (x y : CyclicModel.Conventions.Site p.n p.W) :
    ErdosRiabov.xi (Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W) z₁ z₂
        (siteEquiv p x) (siteEquiv p y) = CyclicModel.GaussianRing.erXi p z₁ z₂ x y := by
  set c : ℂ := ErdosRiabov.semicircleM z₁ * ErdosRiabov.semicircleM z₂
  have hA : (c • (Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W).map
      (algebraMap ℝ ℂ)).submatrix (siteEquiv p) (siteEquiv p) =
        c • CyclicModel.GaussianRing.erComplexVarianceProfile p := by
    rw [← profile_submatrix]
    ext i j
    simp
  have h := kernel_submatrix (c • (Internal.Contracts.Inputs.shortRingProfile p.b p.n p.W).map
    (algebraMap ℝ ℂ)) (siteEquiv p)
  rw [hA] at h
  exact congrFun (congrFun h x) y

end BlockBand.Adapters.ErdosRiabov
