module

public import BlockBand.Endpoints.Response.RemoteHigherWindowEnergy
public import BlockBand.Endpoints.Poisson.SingleCollarPathsLaw
public import BlockBand.Endpoints.Poisson.SequentialCollarsCertificateLaw

/-!
# The window transfer of fractional clock moments at one width

At one width `W`, for a base bulk energy `E`, a bulk energy `e`, a path length `m ≥ 1`, a source
`q ≥ 0`, `0 < p ≤ 1`, `r > 0` and Hölder exponents `a, a'`, the `r`-th moment of `H_p = Tr A^p`
of the near clock at energy `e` is bounded by the `ra`-th moment at energy `E`
(`rhw_window_moment_le`):
`E_e H_p^r ≤ K_A K_λ |p|^{2pr} (E_E H_p^{ra})^{1/a} + (E_e H_p^{2r})^{1/2} P(bad)^{1/2}`,
with `K_A`, `K_λ` the likelihood constants of `rhw_transfer_holder` and `P(bad)` bounded by
`rhw_bad_ports_le`.

Law: `growthPathLaw W b`, through its `m`-marginal `pathLaw W m b`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.Endpoints (nearClock)
open scoped ENNReal NNReal ComplexOrder

variable {W m : ℕ}

/-!
## Measurability and positivity on path samples
-/

theorem rhw_measurable_rhwFull (E : ℝ) (z : ℂ) :
    Measurable fun π : PathSample W m => rhwFull E z π := by
  have hH := measurable_pathMatrix (W := W) (r := m)
  have hC := measurable_pathPortCoupling (W := W) (r := m)
  refine Measurable.of_eval_matrix _ fun x y => ?_
  rcases x with x | x <;> rcases y with y | y <;>
    simp only [rhwFull, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  · exact (hH.eval_matrix (i := x) (j := y)).sub measurable_const
  · exact hC.eval_matrix
  · exact (measurable_conjTranspose''.comp hC).eval_matrix
  · exact measurable_const

theorem rhw_measurable_rhwU (E : ℝ) (z : ℂ) :
    Measurable fun π : PathSample W m => rhwU E z π := by
  have h := measurable_matrix_inv.comp (rhw_measurable_rhwFull (W := W) (m := m) E z)
  refine Measurable.of_eval_matrix _ fun x y => ?_
  exact h.eval_matrix

theorem rhw_measurable_rhwClock (E : ℝ) (z : ℂ) (q : ℝ → ℝ) :
    Measurable fun π : PathSample W m => rhwClock E z W m q π := by
  have hU := rhw_measurable_rhwU (W := W) (m := m) E z
  have hUH : Measurable fun π : PathSample W m => (rhwU E z π)ᴴ :=
    measurable_conjTranspose''.comp hU
  have hk : ∀ k : ℕ, Measurable fun π : PathSample W m =>
      ((q (((k + 1 : ℕ) : ℝ) / W) / (W : ℝ) ^ 2 : ℝ) : ℂ) •
        ((rhwU E z π)ᴴ * tagProjection W m k * rhwU E z π) := fun k =>
    rhw_measurable_matrix_smul _ (rhw_measurable_matrix_mul
      (rhw_measurable_matrix_mul hUH measurable_const) hU)
  have hS : Measurable fun π : PathSample W m => rhwSource E z W m q π := by
    refine Measurable.of_eval_matrix _ fun x y => ?_
    simp only [rhwSource, Matrix.sum_apply]
    exact Finset.measurable_sum _ fun k _ => (hk k).eval_matrix
  refine Measurable.of_eval_matrix _ fun x y => ?_
  exact hS.eval_matrix

theorem rhw_rhwClock_posSemidef (E : ℝ) (z : ℂ) (q : ℝ → ℝ) (hq : ∀ x, 0 ≤ q x)
    (π : PathSample W m) : (rhwClock E z W m q π).PosSemidef := by
  unfold rhwClock
  rw [ns_portBlock_eq]
  refine PosSemidef.conjTranspose_mul_mul_same ?_ _
  unfold rhwSource
  refine posSemidef_sum _ fun k _ => ?_
  have hc : (0 : ℂ) ≤ (((q (((k + 1 : ℕ) : ℝ) / W) / (W : ℝ) ^ 2 : ℝ)) : ℂ) := by
    rw [Complex.zero_le_real]
    exact div_nonneg (hq _) (sq_nonneg _)
  refine PosSemidef.smul ?_ hc
  refine PosSemidef.conjTranspose_mul_mul_same ?_ _
  unfold tagProjection
  rw [posSemidef_diagonal_iff]
  intro x
  split_ifs <;> simp

/-!
## The transfer at one width
-/

/-- The block likelihood constant `exp((a'-1)(2nWδ² + 4α²M²)/(2t))`, `t = (1-2b)/W`. -/
def rhwBlockConst (W n : ℕ) (b δ α M a' : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp ((a' - 1) * (2 * n * W * δ ^ 2 + 4 * α ^ 2 * M ^ 2) /
    (2 * ((1 - 2 * b) / W))))

/-- The window transfer of `E H_p^r` at one width. -/
theorem rhw_window_moment_le (hW : 1 ≤ W) (hm : 1 ≤ m) {b E e : ℝ} (hb : 0 < b)
    (hb' : b < 1 / 2) (hE1 : -2 < E) (hE2 : E < 2) (he1 : -2 < e) (he2 : e < 2)
    {q : ℝ → ℝ} (hq : ∀ x, 0 ≤ q x) {p r : ℝ} (hp : 0 < p) (hr : 0 < r) {a a' : ℝ}
    (ha : a.HolderConjugate a') (hκ : 0 < 1 - a' * (1 - (rhwLam b E e ^ 2)⁻¹)) {M : ℝ} :
    ∫⁻ ω, ENNReal.ofReal (fracTrace p (nearClock b e W m q ω)) ^ r ∂growthPathLaw W b ≤
      rhwBlockConst W m b (e - E) (rhwAlpha b E e) M a' * rhwScaleConst W (rhwLam b E e) a' *
          (ENNReal.ofReal (Complex.normSq (rhwP b E e) ^ p) ^ (r * a) *
            ∫⁻ ω, ENNReal.ofReal (fracTrace p (nearClock b E W m q ω)) ^ (r * a)
              ∂growthPathLaw W b) ^ (1 / a) +
        (∫⁻ ω, ENNReal.ofReal (fracTrace p (nearClock b e W m q ω)) ^ (2 * r)
          ∂growthPathLaw W b) ^ (1 / 2 : ℝ) *
          (4 ^ (W * W) * ENNReal.ofReal (Real.exp (-(M / (2 * (b / W)))))) ^ (1 / 2 : ℝ) := by
  have hb1 : b < 1 := by linarith
  have ha0 : 0 < a := ha.pos
  have hlam := rhw_lam_pos hb1 hE1 hE2 he1 he2
  have hmap := scp_growthPathLaw_map_pathAt (W := W) b hm
  have hpath := scp_measurable_pathAt (W := W) m
  set z := boundaryZ b E
  set z' := boundaryZ b e
  set c : ℝ := Complex.normSq (rhwP b E e) with hc
  have hc0 : 0 ≤ c := Complex.normSq_nonneg _
  set F : Matrix (Fin W) (Fin W) ℂ → ℝ≥0∞ := fun A => ENNReal.ofReal (fracTrace p A) ^ r
  set Ge : PathSample W m → ℝ≥0∞ := fun π => F (rhwClock e z' W m q π)
  set G : PathSample W m → ℝ≥0∞ := fun π => F ((c : ℂ) • rhwClock E z W m q π)
  have hFm : ∀ {g : PathSample W m → Matrix (Fin W) (Fin W) ℂ}, Measurable g →
      (∀ π, (g π).IsHermitian) → Measurable fun π => F (g π) := fun hg hh =>
    (ENNReal.measurable_ofReal.comp (rh_measurable_fracTrace hg hh hp)).pow_const r
  have hGe : Measurable Ge := hFm (rhw_measurable_rhwClock e z' q)
    fun π => (rhw_rhwClock_posSemidef e z' q hq π).isHermitian
  have hG : Measurable G := hFm (rhw_measurable_matrix_smul _ (rhw_measurable_rhwClock E z q))
    fun π => ((rhw_rhwClock_posSemidef E z q hq π).smul (Complex.zero_le_real.mpr hc0)).isHermitian
  -- pass to the path law
  have hL : ∫⁻ ω, ENNReal.ofReal (fracTrace p (nearClock b e W m q ω)) ^ r ∂growthPathLaw W b =
      ∫⁻ π, Ge π ∂pathLaw W m b := by
    rw [← hmap, lintegral_map hGe hpath]; rfl
  have hL2 : ∫⁻ ω, ENNReal.ofReal (fracTrace p (nearClock b e W m q ω)) ^ (2 * r)
      ∂growthPathLaw W b = ∫⁻ π, Ge π ^ (2 : ℝ) ∂pathLaw W m b := by
    rw [← hmap, lintegral_map (hGe.pow_const _) hpath]
    refine lintegral_congr fun ω => ?_
    show _ = (ENNReal.ofReal (fracTrace p (rhwClock e z' W m q (pathAt W m ω))) ^ r) ^ (2 : ℝ)
    rw [← ENNReal.rpow_mul, mul_comm r 2]; rfl
  have hGa : ∫⁻ π, G π ^ a ∂pathLaw W m b = ENNReal.ofReal (c ^ p) ^ (r * a) *
      ∫⁻ ω, ENNReal.ofReal (fracTrace p (nearClock b E W m q ω)) ^ (r * a) ∂growthPathLaw W b := by
    rw [← hmap, lintegral_map (hG.pow_const _) hpath, ← lintegral_const_mul' _ _
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)]
    refine lintegral_congr fun ω => ?_
    show (ENNReal.ofReal (fracTrace p ((c : ℂ) • rhwClock E z W m q (pathAt W m ω))) ^ r) ^ a = _
    rw [fracTrace_smul (rhw_rhwClock_posSemidef E z q hq _).isHermitian hc0,
      ENNReal.ofReal_mul (Real.rpow_nonneg hc0 _), ENNReal.mul_rpow_of_nonneg _ _ hr.le,
      ENNReal.mul_rpow_of_nonneg _ _ ha0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    rfl
  -- split on the good event
  have hgood := rhw_measurableSet_good (W := W) (n := m) M
  rw [hL, ← lintegral_add_compl Ge hgood, ← lintegral_indicator hgood,
    ← lintegral_indicator hgood.compl]
  refine add_le_add ?_ ?_
  · -- the good event: the transform
    have hpt : (rhwGood W m M).indicator Ge =
        (rhwGood W m M).indicator (fun π => G (rhwT (e - E) (rhwAlpha b E e) (rhwLam b E e) π)) := by
      funext π
      simp only [Set.indicator, Ge, G]
      split_ifs
      · rw [rhw_clock_transform (E := E) (δ := e - E) (by ring) hlam.ne' (boundaryZ_ne_zero hb1 hE1 hE2)
          (boundaryZ_ne_zero hb1 he1 he2) (rhw_alpha_eq hb1 hE1 hE2 he1 he2) q π]
        rfl
      · rfl
    rw [hpt]
    refine (rhw_transfer_holder hW hb hb' hlam ha hκ hG).trans (le_of_eq ?_)
    rw [hGa]
    rfl
  · -- the bad event: Cauchy–Schwarz
    have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq (pathLaw W m b) Real.HolderConjugate.two_two
      hGe.aemeasurable (measurable_one.indicator hgood.compl).aemeasurable
    have hind : (rhwGood W m M)ᶜ.indicator Ge = fun π => Ge π * (rhwGood W m M)ᶜ.indicator 1 π := by
      funext π
      by_cases h : π ∈ (rhwGood W m M)ᶜ
      · simp [Set.indicator_of_mem h]
      · simp [Set.indicator_of_notMem h]
    rw [hind]
    refine hcs.trans ?_
    rw [hL2]
    gcongr
    have h1 : ∫⁻ π, (rhwGood W m M)ᶜ.indicator 1 π ^ (2 : ℝ) ∂pathLaw W m b =
        pathLaw W m b (rhwGood W m M)ᶜ := by
      have : ∀ π, (rhwGood W m M)ᶜ.indicator (1 : PathSample W m → ℝ≥0∞) π ^ (2 : ℝ) =
          (rhwGood W m M)ᶜ.indicator 1 π := by
        intro π
        by_cases h : π ∈ (rhwGood W m M)ᶜ
        · simp [Set.indicator_of_mem h]
        · simp [Set.indicator_of_notMem h]
      simp_rw [this]
      rw [lintegral_indicator_one hgood.compl]
    rw [h1]
    exact rhw_bad_ports_le hW hb M

end BlockBand.Endpoints
