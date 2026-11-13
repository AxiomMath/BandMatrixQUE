module

public import BlockBand.Critical.MatrixClosing.Poles.Upgrade
public import BlockBand.Critical.MatrixClosing.Poles.Reduction
public import BlockBand.Critical.Herglotz.NearConv

/-!
# Matrix closing, poles clause: the marked atoms of a simple spectrum

* `markVec V K ℓ = √N V^*u_ℓ`, `markRes = π⁻¹ markVec markVec^*` (`canonicalResidue`),
  `markPts ρ E K ℓ = Nρ(λ_ℓ(K) - E)`, `markAtoms ρ E V K = ofAtoms 0 markPts markRes`.
* `atomSum_markAtoms`: on simple spectrum, `atomSum φ = Σ_ℓ 1_{res_ℓ ≠ 0} φ(x_ℓ, res_ℓ)`.
* `canonicalResidue_relativeMark`: for unimodular phases `π⁻¹z_ℓz_ℓ^* = res_ℓ`
  (`z_ℓ = √N θ_ℓ V^*u_ℓ`, the marks of the relative mixed vectors theorem).
* **`exp_atomSum_sub_bound`**: `0 ≤ exp(-atomSum φ) - exp(-Σ_ℓ φ(x_ℓ, π⁻¹z_ℓz_ℓ^*)) ≤
  1 - exp(-Σ_ℓ ψ(x_ℓ, z_ℓ))` for every nonnegative `ψ` with `φ(x, 0) ≤ ψ(x, 0)` (the atoms with
  zero residue have zero mark).
* `atomSum_ofAtoms_const`: the vague coordinate of `ofAtoms` ignores the constant.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.MatrixClosing.Poles

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Critical.RelativeVectors
open BlockBand.Critical.Herglotz BlockBand.Critical.WeightedDensity
open BlockBand.Coarea.FreshPalm
open scoped ComplexConjugate ComplexOrder

variable {N r : ℕ}

/-!
## Canonical residues
-/

theorem canonicalResidue_smul_of_norm_eq_one {a : ℂ} (ha : ‖a‖ = 1) (g : Fin r → ℂ) :
    canonicalResidue (a • g) = canonicalResidue g := by
  ext i j
  rw [canonicalResidue_apply, canonicalResidue_apply]
  have h : a * conj a = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ha]; simp
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  linear_combination (Real.pi : ℂ)⁻¹ * g i * conj (g j) * h

theorem eq_zero_of_canonicalResidue_eq_zero {g : Fin r → ℂ} (h : canonicalResidue g = 0) :
    g = 0 := by
  funext i
  have h1 := congrFun (congrFun h i) i
  rw [canonicalResidue_apply, Matrix.zero_apply, Complex.mul_conj] at h1
  have hpi : (Real.pi : ℂ)⁻¹ ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)
  have h2 : ((Complex.normSq (g i) : ℝ) : ℂ) = 0 := (mul_eq_zero.1 h1).resolve_left hpi
  exact Complex.normSq_eq_zero.1 (Complex.ofReal_eq_zero.1 h2)

/-!
## The marked atoms of `K`
-/

/-- The phase-free mark `√N V^*u_ℓ`. -/
def markVec (V : Matrix (Fin N) (Fin r) ℂ) (K : Matrix (Fin N) (Fin N) ℂ) (ℓ : Fin N) :
    Fin r → ℂ :=
  ((Real.sqrt N : ℝ) : ℂ) • (Vᴴ *ᵥ freshEigenvector K ℓ)

theorem relativeMark_eq_smul (V : Matrix (Fin N) (Fin r) ℂ) (K : Matrix (Fin N) (Fin N) ℂ)
    (θ : Fin N → ℂ) (ℓ : Fin N) : relativeMark V K θ ℓ = θ ℓ • markVec V K ℓ := by
  unfold relativeMark markVec
  rw [smul_comm]

/-- The residue `π⁻¹ z_ℓ z_ℓ^* = (N/π) V^*u_ℓu_ℓ^*V` of the `ℓ`-th marked atom. -/
def markRes (V : Matrix (Fin N) (Fin r) ℂ) (K : Matrix (Fin N) (Fin N) ℂ) (ℓ : Fin N) :
    Matrix (Fin r) (Fin r) ℂ :=
  canonicalResidue (markVec V K ℓ)

theorem markRes_posSemidef (V : Matrix (Fin N) (Fin r) ℂ) (K : Matrix (Fin N) (Fin N) ℂ)
    (ℓ : Fin N) : (markRes V K ℓ).PosSemidef :=
  canonicalResidue_posSemidef _

/-- The unfolded locations `Nρ(λ_ℓ(K) - E)`. -/
def markPts (ρ E : ℝ) (K : Matrix (Fin N) (Fin N) ℂ) (ℓ : Fin N) : ℝ :=
  (N : ℝ) * ρ * (freshEigenvalue K ℓ - E)

/-- The finite atomic Herglotz function with poles `Nρ(λ_ℓ(K) - E)` and residues
`π⁻¹ z_ℓ z_ℓ^*` (constant `0`; only its atoms matter). -/
def markAtoms (ρ E : ℝ) (V : Matrix (Fin N) (Fin r) ℂ) (K : Matrix (Fin N) (Fin N) ℂ) :
    AtomicHerglotz r :=
  ofAtoms 0 isHermitian_zero (markPts ρ E K) (markRes V K) (markRes_posSemidef V K)

theorem canonicalResidue_relativeMark {V : Matrix (Fin N) (Fin r) ℂ}
    {K : Matrix (Fin N) (Fin N) ℂ} {θ : Fin N → ℂ} (hθ : ∀ ℓ, ‖θ ℓ‖ = 1) (ℓ : Fin N) :
    canonicalResidue (relativeMark V K θ ℓ) = markRes V K ℓ := by
  rw [relativeMark_eq_smul, canonicalResidue_smul_of_norm_eq_one (hθ ℓ)]
  rfl

theorem markPts_injective {ρ E : ℝ} {K : Matrix (Fin N) (Fin N) ℂ} (hK : SimpleSpectrum K)
    (hN : 0 < N) (hρ : ρ ≠ 0) : Function.Injective (markPts ρ E K) := by
  intro ℓ m h
  have hNρ : (N : ℝ) * ρ ≠ 0 := mul_ne_zero (by exact_mod_cast hN.ne') hρ
  unfold markPts at h
  exact hK.2 (by linarith [mul_left_cancel₀ hNρ h])

theorem fiberCard_of_injective {n : ℕ} {pts : Fin n → ℝ} (hp : Function.Injective pts)
    (ℓ : Fin n) : fiberCard pts ℓ = 1 := by
  unfold fiberCard
  rw [Finset.sum_eq_single ℓ]
  · simp
  · intro m _ hm; simp [hp.ne hm]
  · simp

theorem fiberRes_of_injective {n : ℕ} {pts : Fin n → ℝ} (hp : Function.Injective pts)
    (res : Fin n → Matrix (Fin r) (Fin r) ℂ) (ℓ : Fin n) : fiberRes pts res ℓ = res ℓ := by
  unfold fiberRes
  rw [Finset.sum_eq_single ℓ]
  · simp
  · intro m _ hm; simp [hp.ne hm]
  · simp

/-- **Atoms of a simple spectrum**: on simple spectrum, the vague coordinate of the marked atoms is
the sum over the atoms with nonzero residue. -/
theorem atomSum_markAtoms {ρ E : ℝ} {V : Matrix (Fin N) (Fin r) ℂ}
    {K : Matrix (Fin N) (Fin N) ℂ} (hK : SimpleSpectrum K) (hN : 0 < N) (hρ : ρ ≠ 0)
    (φ : CompactlySupportedContinuousMap (ℝ × Matrix (Fin r) (Fin r) ℂ) ℝ) :
    (markAtoms ρ E V K).atomSum φ =
      ∑ ℓ, if markRes V K ℓ = 0 then 0 else φ (markPts ρ E K ℓ, markRes V K ℓ) := by
  have hp := markPts_injective (E := E) hK hN hρ
  refine (atomSum_ofAtoms _ _ _ _ _ φ).trans (Finset.sum_congr rfl fun ℓ _ => ?_)
  rw [fiberCard_of_injective hp, fiberRes_of_injective hp]
  simp

/-- **The zero-residue defect** (pointwise, simple spectrum, unimodular phases): with
`s = Σ_ℓ φ(x_ℓ, π⁻¹z_ℓz_ℓ^*)` the full marked sum of the canonical test and `ψ` any nonnegative
mark test dominating `φ(·, 0)` at the zero mark,
`0 ≤ exp(-atomSum φ) - exp(-s) ≤ 1 - exp(-Σ_ℓ ψ(x_ℓ, z_ℓ))`. -/
theorem exp_atomSum_sub_bound {ρ E : ℝ} {V : Matrix (Fin N) (Fin r) ℂ}
    {K : Matrix (Fin N) (Fin N) ℂ} (hK : SimpleSpectrum K) (hN : 0 < N) (hρ : ρ ≠ 0)
    {θ : Fin N → ℂ} (hθ : ∀ ℓ, ‖θ ℓ‖ = 1)
    (φ : CompactlySupportedContinuousMap (ℝ × Matrix (Fin r) (Fin r) ℂ) ℝ) (hφ : ∀ p, 0 ≤ φ p)
    (ψ : ℝ × (Fin r → ℂ) → ℝ) (hψ0 : ∀ p, 0 ≤ ψ p) (hψ : ∀ x, φ (x, 0) ≤ ψ (x, 0)) :
    0 ≤ Real.exp (-(markAtoms ρ E V K).atomSum φ) -
        Real.exp (-∑ ℓ, canonTest φ (markPts ρ E K ℓ, relativeMark V K θ ℓ)) ∧
      Real.exp (-(markAtoms ρ E V K).atomSum φ) -
          Real.exp (-∑ ℓ, canonTest φ (markPts ρ E K ℓ, relativeMark V K θ ℓ)) ≤
        1 - Real.exp (-∑ ℓ, ψ (markPts ρ E K ℓ, relativeMark V K θ ℓ)) := by
  classical
  set a := (markAtoms ρ E V K).atomSum φ
  set d : ℝ := ∑ ℓ, if markRes V K ℓ = 0 then φ (markPts ρ E K ℓ, 0) else 0
  set sψ := ∑ ℓ, ψ (markPts ρ E K ℓ, relativeMark V K θ ℓ)
  have hs : ∑ ℓ, canonTest φ (markPts ρ E K ℓ, relativeMark V K θ ℓ) = a + d := by
    rw [show a = _ from atomSum_markAtoms hK hN hρ φ, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [canonTest_apply]
    simp only
    rw [canonicalResidue_relativeMark hθ]
    split_ifs with h
    · rw [h, zero_add]
    · rw [add_zero]
  have hd0 : 0 ≤ d := Finset.sum_nonneg fun ℓ _ => by split_ifs <;> simp [hφ]
  have hdψ : d ≤ sψ := by
    refine Finset.sum_le_sum fun ℓ _ => ?_
    split_ifs with h
    · have hz : relativeMark V K θ ℓ = 0 := by
        rw [relativeMark_eq_smul, eq_zero_of_canonicalResidue_eq_zero h, smul_zero]
      rw [hz]; exact hψ _
    · exact hψ0 _
  have ha0 : 0 ≤ a := atomSum_nonneg _ hφ
  rw [hs]
  have e1 : Real.exp (-a) - Real.exp (-(a + d)) = Real.exp (-a) * (1 - Real.exp (-d)) := by
    rw [neg_add, Real.exp_add]; ring
  rw [e1]
  have h1 : 0 ≤ 1 - Real.exp (-d) := by
    have := Real.exp_le_one_iff.2 (neg_nonpos.2 hd0); linarith
  have h2 : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.2 ha0)
  have h3 : Real.exp (-sψ) ≤ Real.exp (-d) := Real.exp_le_exp.2 (neg_le_neg hdψ)
  refine ⟨mul_nonneg (Real.exp_pos _).le h1, ?_⟩
  calc Real.exp (-a) * (1 - Real.exp (-d)) ≤ 1 * (1 - Real.exp (-d)) :=
        mul_le_mul_of_nonneg_right h2 h1
    _ ≤ 1 - Real.exp (-sψ) := by linarith

/-- The vague coordinate of `ofAtoms` depends only on the atoms. -/
theorem atomSum_ofAtoms_const {n : ℕ} (C0 C1 : Matrix (Fin r) (Fin r) ℂ) (h0 : C0.IsHermitian)
    (h1 : C1.IsHermitian) (pts : Fin n → ℝ) (res : Fin n → Matrix (Fin r) (Fin r) ℂ)
    (hres : ∀ ℓ, (res ℓ).PosSemidef)
    (f : CompactlySupportedContinuousMap (ℝ × Matrix (Fin r) (Fin r) ℂ) ℝ) :
    (ofAtoms C0 h0 pts res hres).atomSum f = (ofAtoms C1 h1 pts res hres).atomSum f := rfl

end BlockBand.Critical.MatrixClosing.Poles
