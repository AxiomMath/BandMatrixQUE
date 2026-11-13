module

public import BlockBand.Palm.MomentFlow.RemLine
public import BlockBand.Palm.MomentFlow.StepsRemoval
public import BlockBand.Palm.MomentFlow.BridgeIdentity

/-!
# The removal average uniformly in time, for regular versions of the conditional moments

`(1/N) Σ_j η F_r(u, ξ^{i,j})·coef/((λ_i - λ_j)² + η²) = Im m(λ_i + iη) F_{r-1}(u, ξ - δ_i) + err`,
with the restored coefficients of the removal identity (`coef = 1 + ξ_j` and target `ξ^{i,j}`
for `j ≠ i`; `coef = ξ_i` and target `ξ` for `j = i`).

* `remKernel`, `remCoef`, `remTarget`: the kernel `N⁻¹η/((λ_j - λ_i)² + η²)` and the
  coefficients and targets of the removal identity.
* `remove_mem_sector`: `ξ - δ_i` lies in the `(r-1)`-sector.
* `le_of_dense_open`: an inequality between functions continuous on `[a,c]` that holds on a dense
  subset of the relatively open set `{u < δ}` holds on all of it.
* `continuousOn_freshDyson_clamp_path`: `s ↦ m_s(clamp(λ(s)) + iη)` is continuous on
  `[c₀-s₀, c₀]` for every continuous path `λ` (joint Lipschitz bound `freshDyson_window_lipschitz`).
* **`removal_average_uniform`** (hypotheses `ExternalLocalGUE`, `MDEBranchIdentification`,
  `GaussianLpGradient`, `DysonBrownianMotion`): with the same constant `Cst` and the **same**
  `𝓛`-measurable `B` (`P(B) ≤ N^{-D}`) as `removal_average_fixed_time`, for **every** pair of
  versions `Φ` (sector `r`) and `Ψ` (sector `r-1`) of the conditional moments that are a.s.
  continuous in time on `[a,c]` (e.g. those of `momentGeneratorBridge_start`), every height,
  window `δ`, configuration and occupied label `i`: a.e. off `B`, for **all** `s ∈ [a,c]` with
  `|λ_i(s) - E| < δ`, the removal-average inequality holds with `Φ, Ψ` in place of the
  conditional expectations.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open MeasureTheory ProbabilityTheory Matrix Set Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Internal.Contracts.Inputs BlockBand.External BlockBand.Palm.CoarseRelative
open BlockBand.Palm
open scoped ENNReal NNReal

variable {N : ℕ}

/-- The resolvent kernel `N⁻¹ η/((λ_j - λ_i)² + η²)` at time `s`. -/
def remKernel (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N) (s : ℝ) (i j : Fin N)
    (η : ℝ) : ℝ :=
  (N : ℝ)⁻¹ * (η / ((flowEigenvalue F a ω s j - flowEigenvalue F a ω s i) ^ 2 + η ^ 2))

/-- Coefficient of the removal identity: `ξ_i` for `j = i`, `1 + ξ_j` otherwise. -/
def remCoef (ξ : Occ N) (i j : Fin N) : ℝ := if j = i then (ξ i : ℝ) else (ξ j : ℝ) + 1

/-- Target of the removal identity: `ξ` for `j = i`, `ξ^{i,j}` otherwise. -/
def remTarget (ξ : Occ N) (i j : Fin N) : Occ N := if j = i then ξ else move ξ i j

theorem remove_mem_sector {r : ℕ} {ξ : Occ N} (hξ : ξ ∈ sector N r) {i : Fin N} (hi : 0 < ξ i) :
    remove ξ i ∈ sector N (r - 1) := by
  classical
  rw [mem_sector] at hξ ⊢
  have h1 : ∑ k, remove ξ i k = (ξ i - 1) + ∑ k ∈ Finset.univ \ {i}, ξ k := by
    unfold remove
    exact Finset.sum_update_of_mem (Finset.mem_univ i) _ _
  have h2 : ∑ k, ξ k = ξ i + ∑ k ∈ Finset.univ \ {i}, ξ k := by
    rw [Finset.sdiff_singleton_eq_erase, Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  omega

theorem remTarget_mem_sector {r : ℕ} {ξ : Occ N} (hξ : ξ ∈ sector N r) {i : Fin N}
    (hi : 0 < ξ i) (j : Fin N) : remTarget ξ i j ∈ sector N r := by
  unfold remTarget
  split_ifs with h
  · exact hξ
  · exact move_mem_sector hξ (Ne.symm h) hi

/-- Continuity extension from a dense subset of a relatively open set. -/
theorem le_of_dense_open {a c δ : ℝ} {S : Set (Icc a c)} (hS : Dense S) {f g u : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a c)) (hg : ContinuousOn g (Icc a c))
    (hu : ContinuousOn u (Icc a c)) (h : ∀ x ∈ S, u x < δ → f x ≤ g x) :
    ∀ s ∈ Icc a c, u s < δ → f s ≤ g s := by
  intro s hs hus
  set U : Set (Icc a c) := {x | u x < δ}
  have hU : IsOpen U := isOpen_lt hu.domRestrict continuous_const
  set T : Set (Icc a c) := {x | f x ≤ g x}
  have hT : IsClosed T := isClosed_le hf.domRestrict hg.domRestrict
  have hsub : U ∩ S ⊆ T := fun x hx => h x hx.2 hx.1
  have hcl : U ⊆ closure (U ∩ S) := hS.open_subset_closure_inter hU
  exact (hT.closure_subset_iff.2 hsub) (hcl (show (⟨s, hs⟩ : Icc a c) ∈ U from hus))

/-- `s ↦ m_s(clamp(λ(s)) + iη)` is continuous on the regularity window. -/
theorem continuousOn_freshDyson_clamp_path (hN : 0 < N) {F : Matrix (Fin N) (Fin N) ℂ}
    {A c₀ E r₀ s₀ v₀ : ℝ} (hK : FreshConstants c₀ r₀ s₀ v₀) (hC : FreshClass F A c₀ E r₀ s₀ v₀)
    {η : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1) {lam : ℝ → ℝ} (hlam : Continuous lam) :
    ContinuousOn (fun s => freshDyson F s ⟨clampWin E (r₀ / 2) (lam s), η⟩)
      (Icc (c₀ - s₀) c₀) := by
  have hr0 := hK.2.2.1
  have hκ : 0 < c₀ - s₀ := by linarith [hK.1, hK.2.2.2.2.1]
  set L := dysonLipConst c₀ s₀ v₀
  have hL : 0 ≤ L := dysonLipConst_nonneg c₀ s₀ v₀
  have hK0 : 0 ≤ L * (1 + 1 / Real.sqrt (c₀ - s₀)) := by positivity
  have hlip : LipschitzOnWith (Real.toNNReal (L * (1 + 1 / Real.sqrt (c₀ - s₀))))
      (fun p : ℝ × ℝ => freshDyson F p.1 ⟨clampWin E (r₀ / 2) p.2, η⟩)
      (Icc (c₀ - s₀) c₀ ×ˢ univ) := by
    refine LipschitzOnWith.of_dist_le_mul fun p hp p' hp' => ?_
    rw [dist_eq_norm, Real.coe_toNNReal _ hK0]
    have hx : |(⟨clampWin E (r₀ / 2) p.2, η⟩ : ℂ).re - E| ≤ r₀ :=
      (clampWin_mem (by linarith) _).trans (by linarith)
    have hx' : |(⟨clampWin E (r₀ / 2) p'.2, η⟩ : ℂ).re - E| ≤ r₀ :=
      (clampWin_mem (by linarith) _).trans (by linarith)
    refine (freshDyson_window_lipschitz hN hK hC hp.1 hp'.1 hx hx' hη hη1 hη hη1).trans ?_
    have e : (⟨clampWin E (r₀ / 2) p.2, η⟩ : ℂ) - ⟨clampWin E (r₀ / 2) p'.2, η⟩ =
        ((clampWin E (r₀ / 2) p.2 - clampWin E (r₀ / 2) p'.2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [e, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |clampWin E (r₀ / 2) p.2 - clampWin E (r₀ / 2) p'.2| ≤ dist p p' :=
      (clampWin_sub_le _ _ _ _).trans (by rw [← Real.dist_eq, Prod.dist_eq]; exact le_max_right _ _)
    have h2 : |p.1 - p'.1| ≤ dist p p' := by rw [← Real.dist_eq, Prod.dist_eq]; exact le_max_left _ _
    have hsq : 0 < Real.sqrt (c₀ - s₀) := Real.sqrt_pos.2 hκ
    have h3 : |p.1 - p'.1| / Real.sqrt (c₀ - s₀) ≤ dist p p' / Real.sqrt (c₀ - s₀) :=
      div_le_div_of_nonneg_right h2 hsq.le
    calc L * (|clampWin E (r₀ / 2) p.2 - clampWin E (r₀ / 2) p'.2| +
          |p.1 - p'.1| / Real.sqrt (c₀ - s₀))
        ≤ L * (dist p p' + dist p p' / Real.sqrt (c₀ - s₀)) := by gcongr
      _ = L * (1 + 1 / Real.sqrt (c₀ - s₀)) * dist p p' := by ring
  have hg : Continuous (fun s : ℝ => (s, lam s)) := continuous_id.prodMk hlam
  have := hlip.continuousOn.comp hg.continuousOn (fun s hs => ⟨hs, mem_univ (lam s)⟩)
  exact this

/-- **Removal average uniformly in time**, for a.s. continuous versions of the conditional moments.
-/
theorem removal_average_uniform (hELG : ExternalLocalGUE) (hMDE : MDEBranchIdentification)
    (hLp : GaussianLpGradient) (hDBM : ∀ N : ℕ, DysonBrownianMotion N)
    {A c₀ r₀ s₀ v₀ : ℝ} (hK : FreshConstants c₀ r₀ s₀ v₀) {ε : ℝ} (hε : 0 < ε)
    (hε4 : ε < 1 / 4) :
    ∃ Cst : ℝ, 0 ≤ Cst ∧ ∀ (r : ℕ) (D : ℝ), ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ), FreshClass F A c₀ E r₀ s₀ v₀ →
      ∀ q : Fin N → ℂ, quadForm (freshGamma F c₀ E) q = 1 →
      ∀ a c : ℝ, 0 < a → a < c → c ≤ c₀ → c₀ - s₀ ≤ a → c - a ≤ 1 →
        ∃ B : Set (FlowSample N), MeasurableSet[pathSigma F a a c] B ∧
          flowLaw N a B ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) ∧
          ∀ Φ Ψ : ℝ → Occ N → FlowSample N → ℝ,
          (∀ σ ∈ Icc a c, ∀ ζ ∈ sector N r, Φ σ ζ =ᵐ[flowLaw N a] condMoment F a c q σ ζ) →
          (∀ σ ∈ Icc a c, ∀ ζ ∈ sector N (r - 1),
            Ψ σ ζ =ᵐ[flowLaw N a] condMoment F a c q σ ζ) →
          (∀ᵐ ω ∂flowLaw N a, ∀ ζ : Occ N, ContinuousOn (fun σ => Φ σ ζ ω) (Icc a c) ∧
            ContinuousOn (fun σ => Ψ σ ζ ω) (Icc a c)) →
          ∀ η : ℝ, (N : ℝ) ^ (-(1 - 4 * ε)) ≤ η → η ≤ 1 →
          ∀ δ : ℝ, 0 ≤ δ → δ ≤ r₀ / 2 → ∀ ξ ∈ sector N r, ∀ i : Fin N, 0 < ξ i →
          ∀ᵐ ω ∂flowLaw N a, ω ∉ B → ∀ s ∈ Icc a c, |flowEigenvalue F a ω s i - E| < δ →
            |∑ j, remKernel F a ω s i j η * remCoef ξ i j * Φ s (remTarget ξ i j) ω -
              (freshDyson F s ⟨flowEigenvalue F a ω s i, η⟩).im * Ψ s (remove ξ i) ω| ≤
              (Cst * (N : ℝ) ^ ε / Real.sqrt ((N : ℝ) * η) +
                  v₀⁻¹ * slowConst c₀ r₀ s₀ v₀ * (δ + η + (c₀ - s))) * Ψ s (remove ξ i) ω +
              max 1 ((N : ℝ) * nsq q) ^ r *
                ((N : ℝ) * ((N : ℝ)⁻¹ * η⁻¹ * max 1 ((N : ℝ) * nsq q)) + v₀⁻¹) *
                (N : ℝ) ^ (-D) := by
  obtain ⟨Cst, hCst, hfix⟩ := removal_average_fixed_time hELG hMDE hLp hDBM (A := A) hK hε hε4
  refine ⟨Cst, hCst, fun r D => ?_⟩
  obtain ⟨N₁, hN₁⟩ := hfix r D
  refine ⟨max N₁ 1, fun N hN F E hC q hq a c ha hac hc hac₀ hca => ?_⟩
  have hNpos : 0 < N := lt_of_lt_of_le one_pos (le_of_max_le_right hN)
  obtain ⟨B, hB, hPB, hR⟩ := hN₁ N (le_of_max_le_left hN) F E hC q hq a c ha hac hc hac₀ hca
  refine ⟨B, hB, hPB, fun Φ Ψ hΦ hΨ hcont η hη hη1 δ hδ hδr ξ hξ i hi => ?_⟩
  have hNp : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hη0 : 0 < η := lt_of_lt_of_le (Real.rpow_pos_of_pos hNp _) hη
  set μ := flowLaw N a
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense (Icc a c)
  have : Countable S := hSc.to_subtype
  -- the fixed-time statement, rewritten with the versions, at the times of `S`
  have hpt : ∀ d : S, ∀ᵐ ω ∂μ, ω ∉ B → |flowEigenvalue F a ω (d : ℝ) i - E| ≤ δ →
      |∑ j, remKernel F a ω (d : ℝ) i j η * remCoef ξ i j * Φ (d : ℝ) (remTarget ξ i j) ω -
        (freshDyson F (d : ℝ) ⟨flowEigenvalue F a ω (d : ℝ) i, η⟩).im *
          Ψ (d : ℝ) (remove ξ i) ω| ≤
        (Cst * (N : ℝ) ^ ε / Real.sqrt ((N : ℝ) * η) +
            v₀⁻¹ * slowConst c₀ r₀ s₀ v₀ * (δ + η + (c₀ - (d : ℝ)))) *
          Ψ (d : ℝ) (remove ξ i) ω +
        max 1 ((N : ℝ) * nsq q) ^ r *
          ((N : ℝ) * ((N : ℝ)⁻¹ * η⁻¹ * max 1 ((N : ℝ) * nsq q)) + v₀⁻¹) * (N : ℝ) ^ (-D) := by
    intro d
    have hd : (d : ℝ) ∈ Icc a c := (d : Icc a c).2
    have h := hR (d : ℝ) hd η hη hη1 δ hδ hδr ξ hξ i
    set X : FlowSample N → Fin N → ℝ := fun ω k => flowOverlap F a q (d : ℝ) k ω
    have hX : ∀ᵐ ω ∂μ, ∀ j, (μ[fun ω' => momentMonomial (X ω') (remove ξ i) * X ω' j |
        pathSigma F a a c]) ω = remCoef ξ i j * Φ (d : ℝ) (remTarget ξ i j) ω := by
      refine ae_all_iff.2 fun j => ?_
      by_cases hji : j = i
      · subst hji
        have h1 := condExp_remove_mul_self (m := pathSigma F a a c) μ X hi
        have h2 := hΦ (d : ℝ) hd ξ hξ
        filter_upwards [h1, h2] with ω e1 e2
        have c1 : remCoef ξ j j = (ξ j : ℝ) := by simp [remCoef]
        have c2 : remTarget ξ j j = ξ := by simp [remTarget]
        rw [e1, Pi.smul_apply, smul_eq_mul, c1, c2, e2]
        rfl
      · have h1 := condExp_remove_mul_ne (m := pathSigma F a a c) μ X ξ (Ne.symm hji)
        have h2 := hΦ (d : ℝ) hd (move ξ i j) (move_mem_sector hξ (Ne.symm hji) hi)
        filter_upwards [h1, h2] with ω e1 e2
        have c1 : remCoef ξ i j = (ξ j : ℝ) + 1 := by simp [remCoef, hji]
        have c2 : remTarget ξ i j = move ξ i j := by simp [remTarget, hji]
        rw [e1, Pi.smul_apply, smul_eq_mul, c1, c2, e2]
        rfl
    have hP := hΨ (d : ℝ) hd (remove ξ i) (remove_mem_sector hξ hi)
    filter_upwards [h, hX, hP] with ω e1 e2 e3 hωB hωE
    have k := e1 hωB hωE
    have e4 : ∀ j, (N : ℝ)⁻¹ * (η / ((flowEigenvalue F a ω (d : ℝ) j -
        flowEigenvalue F a ω (d : ℝ) i) ^ 2 + η ^ 2)) *
        (μ[fun ω' => momentMonomial (fun k => flowOverlap F a q (d : ℝ) k ω') (remove ξ i) *
          flowOverlap F a q (d : ℝ) j ω' | pathSigma F a a c]) ω =
        remKernel F a ω (d : ℝ) i j η * remCoef ξ i j * Φ (d : ℝ) (remTarget ξ i j) ω := by
      intro j
      have := e2 j
      simp only [X] at this
      rw [this, remKernel]; ring
    have e5 : (μ[fun ω' => momentMonomial (fun k => flowOverlap F a q (d : ℝ) k ω') (remove ξ i) |
        pathSigma F a a c]) ω = Ψ (d : ℝ) (remove ξ i) ω := by
      rw [e3]; rfl
    simp only [e4, e5] at k
    exact k
  have hall : ∀ᵐ ω ∂μ, ∀ d : S, ω ∉ B → |flowEigenvalue F a ω (d : ℝ) i - E| ≤ δ →
      |∑ j, remKernel F a ω (d : ℝ) i j η * remCoef ξ i j * Φ (d : ℝ) (remTarget ξ i j) ω -
        (freshDyson F (d : ℝ) ⟨flowEigenvalue F a ω (d : ℝ) i, η⟩).im *
          Ψ (d : ℝ) (remove ξ i) ω| ≤
        (Cst * (N : ℝ) ^ ε / Real.sqrt ((N : ℝ) * η) +
            v₀⁻¹ * slowConst c₀ r₀ s₀ v₀ * (δ + η + (c₀ - (d : ℝ)))) *
          Ψ (d : ℝ) (remove ξ i) ω +
        max 1 ((N : ℝ) * nsq q) ^ r *
          ((N : ℝ) * ((N : ℝ)⁻¹ * η⁻¹ * max 1 ((N : ℝ) * nsq q)) + v₀⁻¹) * (N : ℝ) ^ (-D) :=
    ae_all_iff.2 hpt
  filter_upwards [hall, hcont] with ω h1 h2 hωB s hs hsδ
  -- continuity of all terms along `[a, c]`
  have hlamc : ∀ k, Continuous (fun σ => flowEigenvalue F a ω σ k) :=
    fun k => continuous_flowEigenvalue hC.1 a ω k
  have hwin : Icc a c ⊆ Icc (c₀ - s₀) c₀ := fun σ hσ => ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  have hVc : ContinuousOn (fun σ => (freshDyson F σ
      ⟨clampWin E (r₀ / 2) (flowEigenvalue F a ω σ i), η⟩).im) (Icc a c) :=
    (Complex.continuous_im.comp_continuousOn
      (continuousOn_freshDyson_clamp_path hNpos hK hC hη0.le hη1 (hlamc i))).mono hwin
  have hkc : ∀ j, Continuous (fun σ => remKernel F a ω σ i j η) := fun j => by
    unfold remKernel
    refine continuous_const.mul (continuous_const.div ((((hlamc j).sub (hlamc i)).pow 2).add
      continuous_const) fun σ => by positivity)
  set u : ℝ → ℝ := fun σ => |flowEigenvalue F a ω σ i - E|
  have huc : ContinuousOn u (Icc a c) :=
    (continuous_abs.comp ((hlamc i).sub continuous_const)).continuousOn
  set f : ℝ → ℝ := fun σ =>
    |∑ j, remKernel F a ω σ i j η * remCoef ξ i j * Φ σ (remTarget ξ i j) ω -
      (freshDyson F σ ⟨clampWin E (r₀ / 2) (flowEigenvalue F a ω σ i), η⟩).im *
        Ψ σ (remove ξ i) ω|
  set g : ℝ → ℝ := fun σ =>
    (Cst * (N : ℝ) ^ ε / Real.sqrt ((N : ℝ) * η) +
        v₀⁻¹ * slowConst c₀ r₀ s₀ v₀ * (δ + η + (c₀ - σ))) * Ψ σ (remove ξ i) ω +
      max 1 ((N : ℝ) * nsq q) ^ r *
        ((N : ℝ) * ((N : ℝ)⁻¹ * η⁻¹ * max 1 ((N : ℝ) * nsq q)) + v₀⁻¹) * (N : ℝ) ^ (-D)
  have hfc : ContinuousOn f (Icc a c) := by
    refine continuous_abs.comp_continuousOn (ContinuousOn.sub ?_ (hVc.mul (h2 _).2))
    refine continuousOn_finsetSum _ fun j _ => ?_
    exact (((hkc j).mul continuous_const).continuousOn).mul (h2 _).1
  have hgc : ContinuousOn g (Icc a c) := by
    refine ContinuousOn.add (ContinuousOn.mul ?_ (h2 _).2) continuousOn_const
    exact (continuous_const.add (continuous_const.mul
      (continuous_const.add (continuous_const.sub continuous_id)))).continuousOn
  have hdense : ∀ x ∈ S, u x < δ → f x ≤ g x := by
    intro x hx hux
    have hlE : |flowEigenvalue F a ω (x : ℝ) i - E| ≤ r₀ / 2 := hux.le.trans hδr
    have := h1 ⟨x, hx⟩ hωB hux.le
    simp only [f, g]
    rw [clampWin_of_mem hlE]
    exact this
  have hfin := le_of_dense_open hSd hfc hgc huc hdense s hs hsδ
  have hlE : |flowEigenvalue F a ω s i - E| ≤ r₀ / 2 := hsδ.le.trans hδr
  simp only [f, g] at hfin
  rw [clampWin_of_mem hlE] at hfin
  exact hfin

end BlockBand.Palm.MomentFlow
