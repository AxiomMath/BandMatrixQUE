module

public import BlockBand.SourceProcess.ClosingAux.Contraction
public import BlockBand.SourceProcess.ClosingAux.Corner
public import BlockBand.SourceProcess.Closing.Routes
public import BlockBand.SourceProcess.Closing.PhysHardy

/-!
# `ClosedReflection` holds: `‖r‖ < 1` for the closed physical path

`closedReflection_holds : ClosedReflection`.
For `0 < b < 1/2`, `-2 < E < 2`, `0 < s < T`, `0 < h < 1`, every `W ≥ max(1, ⌈1/T⌉ + 1)` and
almost every growth sample `ω`, the omitted block `N = Π𝕊A` of the path closed at time `s` has
`N^n → 0`. Almost-sure inputs: Hermitian GUE blocks, invertible pencils `H_j - E`
(`ae_isUnit_pathPencil_growth`), invertible Ginibre bonds (`ae_isUnit_growth_bond`, needs `b > 0`)
and unitarity of `𝕊` (`ae_scattering_unitary`). The proof:
1. `A = farEmbed A_-` is an orthogonal projection, `ΠΠᴴ = A` (`h² < 1`);
2. an input `v = Av` scattered entirely into `ran ΠᴴΠ` (a far-port subspace) has zero near
   output; the near output of a far input is `-2iη ℝ_{near,far} v_far`, and `ℝ_{near,far}` is
   injective (`corner_injective`, at final length `⌊WT⌋ ≥ 1`), so `v = 0`;
3. `eigen_closingN` + Gelfand (`tendsto_closingN_pow`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ClosingAux

open MeasureTheory Matrix Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Transmission.Bridge BlockBand.SourceProcess.Closing

variable {W : ℕ}

theorem farEmbed_mulVec_near (X : Matrix (Fin W) (Fin W) ℂ) (v : Fin 2 × Fin W → ℂ) (i : Fin W) :
    (farEmbed X *ᵥ v) (0, i) = 0 := by
  simp [farEmbed, mulVec, dotProduct]

/-- The near output of a far input: `(𝕊v)_near = -2iη ℝ_{near,far} v_far`. -/
theorem scattering_mulVec_near (b E : ℝ) (n : ℕ) (ω : GrowthPath W) (v : Fin 2 × Fin W → ℂ)
    (hv : ∀ j, v (0, j) = 0) (i : Fin W) :
    (scatteringMatrix b E W n ω *ᵥ v) (0, i) =
      -(((2 * etaZ b E : ℝ) : ℂ) * Complex.I) *
        (portBlock (boundaryResolvent b E W n ω) 0 1 *ᵥ fun j => v (1, j)) i := by
  simp only [scatteringMatrix, mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, hv,
    mul_zero, Finset.sum_const_zero, zero_add, portBlock, of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hne : ((0 : Fin 2), i) ≠ ((1 : Fin 2), j) := fun h => by
    have := congrArg Prod.fst h; simp at this
  rw [Matrix.sub_apply, Matrix.smul_apply, one_apply_ne hne, smul_eq_mul]
  ring

/-- The injectivity hypothesis of `eigen_closingN` for the physical closing data. -/
theorem phys_hinj {b E : ℝ} (hη : 0 < etaZ b E) (h : ℝ) {nS nT : ℕ} (hn : 1 ≤ nT)
    (ω : GrowthPath W) (hM : IsUnit (fullPathMatrix b E W nT ω)) (hB : ∀ k, IsUnit (ω.2 k))
    (v : Fin 2 × Fin W → ℂ) (hA : farEmbed (omittedProj b E h W nS ω) *ᵥ v = v)
    (hP : ((farEmbed (closingPairing b E h W nS ω))ᴴ * farEmbed (closingPairing b E h W nS ω)) *ᵥ
      (scatteringMatrix b E W nT ω *ᵥ v) = scatteringMatrix b E W nT ω *ᵥ v) : v = 0 := by
  have hv0 : ∀ j, v (0, j) = 0 := fun j => by
    rw [← hA]; exact farEmbed_mulVec_near _ _ _
  rw [farEmbed_conjTranspose, farEmbed_mul] at hP
  have hc : -(((2 * etaZ b E : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    refine neg_ne_zero.2 (mul_ne_zero ?_ Complex.I_ne_zero)
    exact_mod_cast (by positivity : (2 * etaZ b E : ℝ) ≠ 0)
  have hfar : (fun j => v (1, j)) = 0 := by
    refine corner_injective b E hn ω hM hB (funext fun i => ?_)
    have h1 := scattering_mulVec_near b E nT ω v hv0 i
    rw [← hP, farEmbed_mulVec_near] at h1
    exact (mul_eq_zero.1 h1.symm).resolve_left hc
  funext z
  obtain ⟨p, j⟩ := z
  fin_cases p
  · exact hv0 j
  · exact congrFun hfar j

/-- **`ClosedReflection` holds.** -/
theorem closedReflection_holds : ClosedReflection := by
  intro b hb0 hb E hE1 hE2 s T h hs hsT hh0 hh1
  have hT : 0 < T := by linarith
  filter_upwards [eventually_ge_atTop (⌈1 / T⌉₊ + 1)] with W hW
  have hW1 : 1 ≤ W := by omega
  have hnT : 1 ≤ ⌊(W : ℝ) * T⌋₊ := by
    refine Nat.le_floor ?_
    have h1 : 1 / T ≤ (⌈1 / T⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈1 / T⌉₊ + 1 : ℕ) : ℝ) ≤ W := by exact_mod_cast hW
    push_cast at h2
    have h3 : 1 / T * T = 1 := by field_simp
    push_cast
    nlinarith
  have hη : 0 < (boundaryZ b E).im := boundaryZ_im_pos (by linarith) hE1 hE2
  have hh2 : h ^ 2 < 1 := by nlinarith
  filter_upwards [FullSourceStops.ae_scattering_unitary hb hE1 hE2 hW1, ae_growth_isHermitian W b,
    ae_isUnit_pathPencil_growth hb hW1 E, ae_isUnit_growth_bond hb0 hW1] with ω hU hA hF hB
  have hM := isUnit_fullPathMatrix b E ⌊(W : ℝ) * T⌋₊ ω hA hη (hF _)
  refine tendsto_closingN_pow ?_ ?_ ?_ (hU _).1
    (phys_hinj hη h hnT ω hM hB)
  · rw [farEmbed_mul, omittedProj_mul_self]
  · rw [farEmbed_conjTranspose, omittedProj_conjTranspose]
  · rw [farEmbed_conjTranspose, farEmbed_mul, closingPairing_mul_conj b E h hh2]

/-- **The physical closing covariance identity, unconditionally**:
`ae_phaseAvg_physClosingDefect` with its hypothesis `N^n → 0` discharged by
`closedReflection_holds`. For all large `W`, almost surely
`E_z (C(z) - 1)(C(z) - 1)ᴴ = 2 farEmbed(A_-)`. -/
theorem eventually_ae_phaseAvg_physClosingDefect {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hE1 : -2 < E) (hE2 : E < 2) {s T h : ℝ} (hs : 0 < s) (hsT : s < T) (hh0 : 0 < h)
    (hh1 : h < 1) :
    ∀ᶠ W in atTop, ∀ᵐ ω ∂growthPathLaw W b,
      phaseAvg (fun θ => (physClosingMap b E s T h W ω (phase θ) - 1) *
          (physClosingMap b E s T h W ω (phase θ) - 1)ᴴ) =
        (2 : ℂ) • farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ ω) := by
  have hh2 : h ^ 2 < 1 := by nlinarith
  filter_upwards [closedReflection_holds b hb0 hb E hE1 hE2 s T h hs hsT hh0 hh1,
    eventually_ge_atTop 1] with W hW hW1
  filter_upwards [hW, ae_phaseAvg_physClosingDefect hb hE1 hE2 hW1 s T h hh2] with ω hN hD
  exact hD hN

end BlockBand.SourceProcess.ClosingAux
