module

public import BlockBand.LocalWindow.ProofPartTwoLargeRhoSection
public import BlockBand.LocalWindow.ProofPartTwoClassB

/-!
# From the compressed grid window to the eigenvectors of the Schur matrix

The deterministic transfer of the large-`ρ` branch of part (ii) of the physical local-window
lemma: window data for the compressed grid matrix give the overlap bound for every unit
eigenvector of the Schur matrix.

## Main results

* **`largeRho_actual_transfer`**: deterministic, at one exterior point. For a simple pole label
  `j₀` separated from the energy `E` and the grid energy `e`, `4K ≤ |ρ(E)|` and a unit
  eigenvector `u` of `schurA` with eigenvalue `|λ| ≤ K`, the window bound `NatWindowGood` and the
  count bound for the compressed grid matrix bound `|u*Ju - c₀|`. The centre comparison
  (compressed centre at the grid vs the target centre `c₀`) is the hypothesis `hcen`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.LocalWindow.ProofPartTwo

open MeasureTheory Matrix Set
open BlockBand.Coarea BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.External BlockBand.LocalWindow.ProofETH BlockBand.LocalWindow.ProofCount
open scoped ENNReal Matrix.Norms.L2Operator

variable {p : Parameters} {i : ZMod p.n}

attribute [local instance] pairSite_nonempty

/-- At one exterior point `ω` (`H_R, V` Hermitian), a pole label `j₀` simple and separated at
radius `ε > 0` from both the energy `E` (not a pole) and the grid energy `e`, a pair
matrix `G`, `M = F_reg(E) - E + G` with `‖M‖ ≤ K`, `4K ≤ |ρ(E)|`, and a unit `u` with
`A(E) u = λu`, `|λ| ≤ K`, `|λ - μ| ≤ h/2` (`h = (2W-1)^{-1+β}`).
Let `U = poleIsometry sel j₀ ω`.
If the compressed window bound `NatWindowGood (compRegF e) sel' s' μ β ε' (U*JU) (U*GU)` holds for
a contraction `J`, at most `n_S` compressed eigenvalues lie in `[μ - h, μ + h]`, and the compressed
centre is within `η` of `c₀` on that window, then with `r_g = (‖C‖²/ε² + 1)|E - e|`,
`q = 2K/|ρ|`, `τ = (r_g + 4K²/|ρ|)/(h/2)`:
`|u*Ju - c₀| ≤ n_S · 2N^{ε'}N^{-1/2} + η + 2τ + (1 + |c₀|)τ² + q(2 + q) + 2q|c₀|`.
-/
theorem largeRho_actual_transfer (sel : CEH.EigenpairSelection (2 * p.W))
    (sel' : CEH.EigenpairSelection (2 * p.W - 1)) {ε : ℝ} (hε : 0 < ε) {om : SplitState p i}
    (hH : om.1.IsHermitian) (hV : om.2.2.IsHermitian) {j₀ : ExteriorSite p i}
    (hs : PoleSimple hH j₀) {E e : ℝ} (hsepE : PoleSeparated ε hH j₀ E)
    (hsepe : PoleSeparated ε hH j₀ e) (hdet : (om.1 - (E : ℂ) • 1).det ≠ 0)
    {G : PairMatrix p i} {K : ℝ} (hK : 0 < K)
    (hMG : ‖regF hH j₀ om.2.1 om.2.2 E - (E : ℂ) • 1 + G‖ ≤ K)
    (hρ : 4 * K ≤ |poleRho hH j₀ om.2.1 E|) {lam : ℝ} (hlam : |lam| ≤ K)
    {u : PairSite p i → ℂ} (hu : sqNorm u = 1)
    (heig : schurA p i om G E *ᵥ u = (lam : ℂ) • u) {J : PairMatrix p i} (hJ : ‖J‖ ≤ 1)
    {s' μ β ε' nS η : ℝ} {c₀ : ℂ}
    (hwin : NatWindowGood (compRegF sel ε j₀ e om) sel' s' μ β ε'
      ((poleIsometry sel j₀ om)ᴴ * J * poleIsometry sel j₀ om)
      ((poleIsometry sel j₀ om)ᴴ * G * poleIsometry sel j₀ om))
    (hcount : ∀ hX : ((poleIsometry sel j₀ om)ᴴ * G * poleIsometry sel j₀ om).IsHermitian,
      ((Finset.univ.filter fun k => sel'.eigenvalue (natDeformed (compRegF sel ε j₀ e om)
        ((poleIsometry sel j₀ om)ᴴ * G * poleIsometry sel j₀ om) hX) k ∈
          Icc (μ - compressRadius p β) (μ + compressRadius p β)).card : ℝ) ≤ nS)
    (hlamμ : |lam - μ| ≤ compressRadius p β / 2)
    (hcen : ∀ lam' ∈ Icc (μ - compressRadius p β) (μ + compressRadius p β),
      ‖nativeCentre ((poleIsometry sel j₀ om)ᴴ * J * poleIsometry sel j₀ om)
          (compRegM sel ε j₀ e om) s' lam' - c₀‖ ≤ η) :
    ‖star u ⬝ᵥ (J *ᵥ u) - c₀‖ ≤
      nS * compressTol p ε' + η +
        2 * (((‖om.2.1‖ ^ 2 / ε ^ 2 + 1) * |E - e| + 4 * K ^ 2 / |poleRho hH j₀ om.2.1 E|) /
          (compressRadius p β / 2)) +
        (1 + ‖c₀‖) * (((‖om.2.1‖ ^ 2 / ε ^ 2 + 1) * |E - e| +
          4 * K ^ 2 / |poleRho hH j₀ om.2.1 E|) / (compressRadius p β / 2)) ^ 2 +
        2 * K / |poleRho hH j₀ om.2.1 E| * (2 + 2 * K / |poleRho hH j₀ om.2.1 E|) +
        2 * (2 * K / |poleRho hH j₀ om.2.1 E|) * ‖c₀‖ := by
  set U := poleIsometry sel j₀ om with hUdef
  set w := poleDir hH j₀ om.2.1 with hwdef
  set ρ := poleRho hH j₀ om.2.1 E with hρdef
  set hN := compressRadius p β with hhN
  obtain ⟨hUU, hUw, hcompl⟩ := poleIsometry_spec sel hH hs
  have hw : sqNorm w = 1 := sqNorm_poleDir hH j₀ om.2.1
  have hN0 : 0 < hN := by
    have : (0 : ℝ) < ((2 * p.W - 1 : ℕ) : ℝ) := by
      have := p.W_pos
      exact_mod_cast (by omega : 0 < 2 * p.W - 1)
    exact Real.rpow_pos_of_pos this _
  -- the eigen-equation in the rank-one form
  set M := regF hH j₀ om.2.1 om.2.2 E - (E : ℂ) • 1 + G with hMdef
  have heig' : (M + (ρ : ℂ) • vecMulVec w (star w)) *ᵥ u = (lam : ℂ) • u := by
    have h := heig
    unfold schurA at h
    rw [schurK0_pole_decomp om hH j₀ hdet] at h
    rw [show M + (ρ : ℂ) • vecMulVec w (star w) = regF hH j₀ om.2.1 om.2.2 E - (E : ℂ) • 1 +
        ((poleRho hH j₀ om.2.1 E : ℝ) : ℂ) •
          vecMulVec (poleDir hH j₀ om.2.1) (star (poleDir hH j₀ om.2.1)) + G by
      rw [hMdef]; abel]
    exact h
  -- the compressed grid matrix and its selected eigenpairs
  obtain ⟨hX, hwin'⟩ := hwin
  set Y := natDeformed (compRegF sel ε j₀ e om) (Uᴴ * G * U) hX with hYdef
  set ek := sel'.eigenvector Y with hekdef
  set mu := sel'.eigenvalue Y with hmudef
  have he : IsOrthonormalFamily ek := fun a b => sel'.orthonormal Y a b
  have heigA : ∀ a, Y.1 *ᵥ ek a = (mu a : ℂ) • ek a := fun a => sel'.eigen_equation Y a
  have hYeq : Y.1 = Uᴴ * (regF hH j₀ om.2.1 om.2.2 e - (e : ℂ) • 1 + G) * U := by
    rw [hYdef]
    show compRegM sel ε j₀ e om + Uᴴ * G * U = _
    rw [compRegM_eq sel ε hH hV hs hsepe, Matrix.mul_add, Matrix.add_mul]
  set rg := (‖om.2.1‖ ^ 2 / ε ^ 2 + 1) * |E - e| with hrgdef
  have hrg : 0 ≤ rg := by positivity
  have hBA : ‖Uᴴ * M * U - Y.1‖ ≤ rg := by
    rw [hYeq, ← Matrix.sub_mul, ← Matrix.mul_sub]
    refine (opNorm_compress_le hUU _).trans ?_
    rw [hMdef, show regF hH j₀ om.2.1 om.2.2 E - (E : ℂ) • 1 + G -
        (regF hH j₀ om.2.1 om.2.2 e - (e : ℂ) • 1 + G) =
        (regF hH j₀ om.2.1 om.2.2 E - (E : ℂ) • (1 : PairMatrix p i)) -
          (regF hH j₀ om.2.1 om.2.2 e - (e : ℂ) • (1 : PairMatrix p i)) by abel]
    exact opNorm_regK_sub_le hε om hH j₀ hsepE hsepe
  -- the window around `λ`
  set S := Finset.univ.filter fun a => |mu a - lam| < hN / 2 with hSdef
  have hS : ∀ a ∉ S, hN / 2 ≤ |mu a - lam| := by
    intro a ha
    simpa [hSdef] using ha
  have hSwin : ∀ a ∈ S, mu a ∈ Icc (μ - hN) (μ + hN) := by
    intro a ha
    have h1 : |mu a - lam| < hN / 2 := by simpa [hSdef] using ha
    have h2 := abs_lt.mp h1
    have h3 := abs_le.mp hlamμ
    exact ⟨by linarith, by linarith⟩
  have hcard : (S.card : ℝ) ≤ nS := by
    refine le_trans ?_ (hcount hX)
    exact_mod_cast Finset.card_le_card fun a ha =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ a, hSwin a ha⟩
  have hpair : ∀ a ∈ S, ∀ b ∈ S,
      ‖star (ek a) ⬝ᵥ ((Uᴴ * J * U) *ᵥ ek b) -
          (if a = b then nativeCentre (Uᴴ * J * U) (compRegM sel ε j₀ e om) s' (mu a)
            else 0)‖ ≤ compressTol p ε' :=
    fun a ha b hb => hwin' a b (hSwin a ha) (hSwin b hb)
  have hcen' : ∀ a ∈ S,
      ‖nativeCentre (Uᴴ * J * U) (compRegM sel ε j₀ e om) s' (mu a) - c₀‖ ≤ η :=
    fun a ha => hcen (mu a) (hSwin a ha)
  have hε1 : 0 ≤ compressTol p ε' := by unfold compressTol; positivity
  have hη : 0 ≤ η :=
    le_trans (norm_nonneg _) (hcen μ ⟨by linarith, by linarith⟩)
  have hT := largeRho_window_transfer hK hMG hUU hUw hcompl hw hu hρ hlam heig' hJ Y.2 he heigA
    hrg (half_pos hN0) hBA hS hε1 hη hpair hcen'
  refine hT.trans ?_
  have hS' : (S.card : ℝ) * compressTol p ε' ≤ nS * compressTol p ε' :=
    mul_le_mul_of_nonneg_right hcard hε1
  linarith

end BlockBand.LocalWindow.ProofPartTwo
