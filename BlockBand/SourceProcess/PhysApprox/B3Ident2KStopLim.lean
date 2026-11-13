module

public import BlockBand.SourceProcess.PhysApprox.B3Ident2KGrid
public import BlockBand.SourceProcess.PhysApprox.B3Ident2Main

/-!
# The `𝒦` stop in the limit (`CapIdentKStop` proved)

Measure: the candidate's `Q`; at finite `W` the closed law conditioned on the physical cap event.
Domain: `CapIdentPremise`. Inputs: `ComplexKStoppedMomentMax` (at the horizon
`T' = max T (s + t + 1)` and level `R = L + Σ d_* m + 2`), `modulusS` (from
`ComplexClosedSummed`, `ComplexClosedLindeberg`), `tendsto_capProb`.

* `exists_norm_kJ_le`: the `𝒦` birth jumps are bounded.
* `eventually_condObs_psiGrid_le` (finite `W`): the conditioned value of every approximation of
  the grid functional is at most `(2 + 2C_J² + 2C + N·#cols·θ)/(p/2)`, `p = P(μ(s) ∈ cap)`:
  pointwise bound `ofReal_fGrid_le`, `ComplexKStoppedMomentMax`, and the bad event inside the
  modulus events (`bad_subset`, `modulusS` with probability `θ` per column).

Proved from it in sibling modules:
* `integral_fGrid_le` (limit): the same bound for `∫ fGrid(obs) dQ`, via `integral_le_of_fddAll`.
* **`kStop_dominated`**: for every level `L`, horizon `t` and entry `ij`, the births-removed
  `|𝒦_ij(v) − 𝒦_ij(0)|²` on `v ≤ t ∧ σ_L` is dominated by `g = sup_q 1_{A_q}|𝒦(q) − 𝒦(0)|²`
  over non-birth rationals `q ∈ [0, t]` (`A_q`: trace below `L` at all rational times `≤ q`), and
  `∫⁻ g ≤ 2(2 + 2C_J² + 2C)/p` (monotone convergence over finite sets of `q`; each finite set is
  refined into a non-birth grid fine enough for `modulusS`).
* **`capIdentKStop_holds : CapIdentKStop`**.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.Ident2

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.CapLimit BlockBand.Internal.Contracts.Layers
open scoped NNReal ENNReal

variable {K np : ℕ}

theorem kJ_eq_sel (E s : ℝ) (τ m : Fin np → ℝ) (t : ℝ≥0) :
    kJ E s τ m t = ∑ j, if decide (τ j - s ≤ (t : ℝ)) then
      (matchedA E * (m j : ℂ)) • Matrix.single j j (1 : ℂ) else 0 := by
  simp only [kJ, kBirthJump, decide_eq_true_eq]

/-- The `𝒦` birth jumps are bounded. -/
theorem exists_norm_kJ_le (E s : ℝ) (τ m : Fin np → ℝ) :
    ∃ C : ℝ, ∀ t i j, ‖kJ E s τ m t i j‖ ≤ C := by
  set F : (Fin np → Bool) → Matrix (Fin np) (Fin np) ℂ := fun x => ∑ j, if x j then
    (matchedA E * (m j : ℂ)) • Matrix.single j j (1 : ℂ) else 0
  refine ⟨∑ x : Fin np → Bool, ∑ i, ∑ j, ‖F x i j‖, fun t i j => ?_⟩
  rw [kJ_eq_sel]
  set x : Fin np → Bool := fun j => decide (τ j - s ≤ (t : ℝ))
  have h1 : ‖F x i j‖ ≤ ∑ j', ‖F x i j'‖ :=
    Finset.single_le_sum (f := fun j' => ‖F x i j'‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ j)
  have h2 : ∑ j', ‖F x i j'‖ ≤ ∑ i', ∑ j', ‖F x i' j'‖ :=
    Finset.single_le_sum (f := fun i' => ∑ j', ‖F x i' j'‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  have h3 : ∑ i', ∑ j', ‖F x i' j'‖ ≤ ∑ x' : Fin np → Bool, ∑ i', ∑ j', ‖F x' i' j'‖ :=
    Finset.single_le_sum (f := fun x' => ∑ i', ∑ j', ‖F x' i' j'‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (Finset.mem_univ x)
  exact h1.trans (h2.trans h3)

variable {α : Type} [Fintype α] [Nonempty α]
variable {b E s h : ℝ} {τ m : Fin np → ℝ}
  {Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ} {φ : ℕ → ℕ}

theorem modEvent_mono {T δ δ' η : ℝ} (hδ : δ ≤ δ') {W : ℕ}
    (V : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (col : SrcCol K (Fin np)) :
    modEvent b E s h τ m T δ η W V col ⊆ modEvent b E s h τ m T δ' η W V col :=
  fun _ ⟨hy, t, ht, t', ht', hd, hη⟩ => ⟨hy, t, ht, t', ht', hd.trans hδ, hη⟩

/-- **The finite-`W` bound of the conditioned approximations.** -/
theorem eventually_condObs_psiGrid_le (hb : b < 1) (hm : ∀ i, 0 ≤ m i) (hs0 : 0 ≤ s)
    (hτ : ∀ j, s < τ j) {L R T δ θ N C CJ p : ℝ} (hN : 0 ≤ N) (hC : 0 ≤ C) (hθ : 0 ≤ θ)
    (hp : 0 < p) (hR : L + ∑ i, dStar b * m i + 2 ≤ R) {r : α → ℚ} {a₀ : α} (hr0 : r a₀ = 0)
    (hrn : ∀ a, 0 ≤ (r a : ℝ)) (hrT : ∀ a, s + (r a : ℝ) ≤ T) (hδ : 0 ≤ δ)
    (hdense : ∀ x : ℝ, 0 ≤ x → (∃ a, x < r a) → ∃ c, (r c : ℝ) ≤ x ∧ x - δ ≤ r c)
    {κ : α → ℂ} (hκ : ∀ a, ‖κ a‖ ≤ CJ) (ij : Fin np × Fin np)
    (hcap : ∀ᶠ n in atTop, growthPathLaw (φ n) b (physCapEventC b E s h K (φ n)) ≠ 0 ∧
      p / 2 ≤ (growthPathLaw (φ n) b (physCapEventC b E s h K (φ n))).toReal)
    (hmod : ∀ᶠ n in atTop, ∀ col, closedLaw b (φ n) np (modEvent b E s h τ m T δ
      (1 / (Fintype.card (SrcCol K (Fin np)) : ℝ)) (φ n) (Vs (φ n)) col) ≤ ENNReal.ofReal θ)
    (hZ : ∀ᶠ n in atTop, ∫⁻ y, kMaxZ b E s h τ m R T (φ n) (Vs (φ n)) ij y
      ∂closedLaw b (φ n) np ≤ ENNReal.ofReal C) (k : ℕ) :
    ∀ᶠ n in atTop, condObsTestAll b E s h τ m (φ n) (Vs (φ n)) (gIdx ij) (gTime r)
      (psiGrid L r N hN κ a₀ k) ≤
      (2 + 2 * CJ ^ 2 + N * (Fintype.card (SrcCol K (Fin np)) : ℝ) * θ + 2 * C) / (p / 2) := by
  set nc : ℝ := (Fintype.card (SrcCol K (Fin np)) : ℝ)
  have hnc : 0 ≤ nc := Nat.cast_nonneg _
  filter_upwards [hcap, hmod, hZ] with n hn hmn hZn
  set W := φ n
  set μ := closedLaw b W np
  set Bad := gridBad b E s h τ m L R W (Vs W) r
  set F : ProbedPath W np × ℝ → ℝ≥0∞ := fun y =>
    (ENNReal.ofReal (2 + 2 * CJ ^ 2) + (toMeasurable μ Bad).indicator
      (fun _ => ENNReal.ofReal N) y) + 2 * kMaxZ b E s h τ m R T W (Vs W) ij y
  have hFpt : ∀ y, y.1.1 ∈ physCapEventC b E s h K W →
      ENNReal.ofReal (psiGrid L r N hN κ a₀ k
        (fun l => b3ObsAll b E s h τ m W (Vs W) (gIdx ij l) (gTime r l) y)) ≤ F y := by
    intro y hy
    rw [psiGrid_apply]
    refine (ENNReal.ofReal_le_ofReal (psiFun_le_fGrid hN k _)).trans ?_
    refine (ofReal_fGrid_le (R := R) ij hN hr0 hrn hκ hτ hrT y hy).trans ?_
    have hind : Bad.indicator (fun _ => ENNReal.ofReal N) y ≤
        (toMeasurable μ Bad).indicator (fun _ => ENNReal.ofReal N) y :=
      Set.indicator_le_indicator_of_subset (subset_toMeasurable _ _) (fun _ => bot_le) y
    calc ENNReal.ofReal (2 + 2 * CJ ^ 2) + 2 * kMaxZ b E s h τ m R T W (Vs W) ij y +
          Bad.indicator (fun _ => ENNReal.ofReal N) y
        = (ENNReal.ofReal (2 + 2 * CJ ^ 2) + Bad.indicator (fun _ => ENNReal.ofReal N) y) +
          2 * kMaxZ b E s h τ m R T W (Vs W) ij y := by ring
      _ ≤ F y := add_le_add_left (add_le_add_right hind _) _
  have hBad : μ Bad ≤ (Fintype.card (SrcCol K (Fin np)) : ℝ≥0∞) * ENNReal.ofReal θ := by
    refine (measure_mono (bad_subset hb hm hs0 hr0 hrn hR hrT hdense hδ ij)).trans
      ((measure_iUnion_fintype_le _ _).trans ?_)
    refine (Finset.sum_le_sum fun col _ => hmn col).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hlin : ∫⁻ y, F y ∂μ ≤
      ENNReal.ofReal (2 + 2 * CJ ^ 2 + N * nc * θ + 2 * C) := by
    have hmeas : Measurable fun y : ProbedPath W np × ℝ =>
        ENNReal.ofReal (2 + 2 * CJ ^ 2) + (toMeasurable μ Bad).indicator
          (fun _ => ENNReal.ofReal N) y :=
      (measurable_const.indicator (measurableSet_toMeasurable _ _)).const_add _
    have := BlockBand.Transmission.Bridge.isProbabilityMeasure_growthPathLaw W b
    have hprob : IsProbabilityMeasure μ := by
      simp only [μ, closedLaw]; infer_instance
    rw [lintegral_add_left hmeas, lintegral_add_left measurable_const, lintegral_const,
      lintegral_indicator_const (measurableSet_toMeasurable _ _), measure_toMeasurable,
      lintegral_const_mul' _ _ (by norm_num), measure_univ, mul_one]
    have e : ENNReal.ofReal (2 + 2 * CJ ^ 2 + N * nc * θ + 2 * C) =
        ENNReal.ofReal (2 + 2 * CJ ^ 2) + ENNReal.ofReal N *
          ((Fintype.card (SrcCol K (Fin np)) : ℝ≥0∞) * ENNReal.ofReal θ) +
          2 * ENNReal.ofReal C := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_add (by positivity) (by positivity), mul_assoc,
        ENNReal.ofReal_mul hN, ENNReal.ofReal_mul hnc, ENNReal.ofReal_natCast,
        ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    rw [e]
    gcongr
  have hfin : ∫⁻ y, F y ∂μ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlin
  refine (condObsTestAll_le hn.1 (gIdx ij) (gTime r) _ (fun x => psiFun_nonneg hN k x) hFpt
    hfin).trans ?_
  have hnum : (∫⁻ y, F y ∂μ).toReal ≤ 2 + 2 * CJ ^ 2 + N * nc * θ + 2 * C :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hlin
  exact div_le_div₀ (by positivity) hnum (by positivity) hn.2

end BlockBand.SourceProcess.PhysApprox.B3.Ident2
