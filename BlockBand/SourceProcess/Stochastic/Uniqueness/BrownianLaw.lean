module
public import BlockBand.SourceProcess.Stochastic.Levy.Brownian
public import Mathlib.Probability.Process.FiniteDimensionalLaws
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Joint law of an initial value and a filtration Brownian motion

Setting: arbitrary probability spaces `(Ω, 𝓖, Q)` with raw filtrations, `B` a `d`-dimensional
`𝓖`-Brownian motion (`IsFiltrationBrownian`: adapted, a.s. continuous, `B_0 = 0` a.s.,
increments independent of the past with law `N(0, (t-s) I)`), `ξ` a `𝓖_0`-measurable random
variable.

* `map_prod_increment`: for `V` `𝓖_r`-measurable and `r ≤ t`,
  `law(V, B_t - B_r) = law(V) ⊗ N(0, (t-r) I)`.
* **`map_initial_brownian_eq`**: for monotone times `s_0 ≤ … ≤ s_n`, the law of
  `(ξ, B_{s_0}, …, B_{s_n})` depends only on the law of `ξ` (two-space form).
* `initBrownian ξ B : Ω → (Option ℚ≥0 → ℝ^d)`: `none ↦ ξ`, `some q ↦ B_q`.
* **`map_initBrownian_eq`**: the law of `(ξ, (B_q)_{q ∈ ℚ≥0})` on the countable product depends
  only on the law of `ξ` (two-space form; projective-limit uniqueness).
* `map_eq_of_fdd_eq₂'`: two-space fdd determination of laws on product spaces.
-/

namespace BlockBand.SourceProcess.Stochastic.Uniqueness
open MeasureTheory ProbabilityTheory Filter Set
open BlockBand.SourceProcess.Stochastic.Levy
open scoped NNReal ENNReal

variable {d : ℕ}

section OneSpace

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω}
  {𝓖 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → Fin d → ℝ}

theorem brownian_measurable (hB : IsFiltrationBrownian Q 𝓖 B) (t : ℝ≥0) : Measurable (B t) :=
  ((hB.adapted t).mono (𝓖.le t)).measurable

variable [IsProbabilityMeasure Q]

/-- **One increment.** For a `𝓖_r`-measurable `V` and `r ≤ t`, `V` and `B_t - B_r` are
independent: `law(V, B_t - B_r) = law(V) ⊗ N(0, (t - r) I)`. -/
theorem map_prod_increment (hB : IsFiltrationBrownian Q 𝓖 B) {r t : ℝ≥0} (hrt : r ≤ t)
    {E : Type*} [MeasurableSpace E] {V : Ω → E} (hV : Measurable[𝓖 r] V) :
    Q.map (fun ω => (V ω, B t ω - B r ω)) = (Q.map V).prod (gaussPi d (t - r)) := by
  have hVm : Measurable V := hV.mono (𝓖.le r) le_rfl
  have hind : IndepFun V (fun ω => B t ω - B r ω) Q := by
    rw [IndepFun_iff_Indep]
    exact (indep_of_indep_of_le_right (hB.indep r t hrt) hV.comap_le).symm
  rw [hind.map_prod_eq_prod_map_map hVm.aemeasurable (hB.hasLaw r t hrt).aemeasurable,
    (hB.hasLaw r t hrt).map_eq]

/-- Base case: `law(ξ, B_{s_0})` is the image of `law(ξ) ⊗ N(0, s_0 I)`. -/
theorem map_initial_brownian_zero (hB : IsFiltrationBrownian Q 𝓖 B) {S : Type*}
    [MeasurableSpace S] {ξ : Ω → S} (hξ : Measurable[𝓖 0] ξ) (s : Fin 1 → ℝ≥0) :
    Q.map (fun ω => (ξ ω, fun j => B (s j) ω)) =
      ((Q.map ξ).prod (gaussPi d (s 0 - 0))).map
        (fun p : S × (Fin d → ℝ) => (p.1, fun _ : Fin 1 => p.2)) := by
  have hξm : Measurable ξ := hξ.mono (𝓖.le 0) le_rfl
  have hφ : Measurable fun p : S × (Fin d → ℝ) => (p.1, fun _ : Fin 1 => p.2) :=
    measurable_fst.prodMk (Measurable.of_eval fun _ => measurable_snd)
  have hΔ : Measurable fun ω => B (s 0) ω - B 0 ω :=
    (brownian_measurable hB _).sub (brownian_measurable hB _)
  rw [← map_prod_increment hB (zero_le : (0 : ℝ≥0) ≤ s 0) hξ,
    Measure.map_map hφ (hξm.prodMk hΔ)]
  refine Measure.map_congr ?_
  filter_upwards [hB.zero] with ω hω
  simp only [Function.comp_apply, hω, sub_zero]
  congr 1
  funext j
  rw [Subsingleton.elim j 0]

theorem measurable_snoc_add {S : Type*} [MeasurableSpace S] (n : ℕ) :
    Measurable fun p : (S × (Fin (n + 1) → Fin d → ℝ)) × (Fin d → ℝ) =>
      (p.1.1, (Fin.snoc p.1.2 (p.1.2 (Fin.last n) + p.2) : Fin (n + 2) → Fin d → ℝ)) := by
  refine measurable_fst.fst.prodMk (Measurable.of_eval fun j => ?_)
  induction j using Fin.lastCases with
  | last => simp only [Fin.snoc_last]; fun_prop
  | cast j => simp only [Fin.snoc_castSucc]; fun_prop

/-- Induction step: `law(ξ, B_{s_0}, …, B_{s_{n+1}})` is the image of
`law(ξ, B_{s_0}, …, B_{s_n}) ⊗ N(0, (s_{n+1} - s_n) I)`. -/
theorem map_initial_brownian_succ (hB : IsFiltrationBrownian Q 𝓖 B) {S : Type*}
    [MeasurableSpace S] {ξ : Ω → S} (hξ : Measurable[𝓖 0] ξ) {n : ℕ}
    (s : Fin (n + 2) → ℝ≥0) (hs : Monotone s) :
    Q.map (fun ω => (ξ ω, fun j => B (s j) ω)) =
      ((Q.map fun ω => (ξ ω, fun j => B (Fin.init s j) ω)).prod
        (gaussPi d (s (Fin.last (n + 1)) - Fin.init s (Fin.last n)))).map
          fun p => (p.1.1, (Fin.snoc p.1.2 (p.1.2 (Fin.last n) + p.2) :
            Fin (n + 2) → Fin d → ℝ)) := by
  have hs' : Monotone (Fin.init s) := fun i j hij => hs (Fin.castSucc_le_castSucc_iff.2 hij)
  have hrt : Fin.init s (Fin.last n) ≤ s (Fin.last (n + 1)) := hs (Fin.castSucc_lt_last _).le
  have hV : Measurable[𝓖 (Fin.init s (Fin.last n))]
      fun ω => (ξ ω, fun j => B (Fin.init s j) ω) := by
    refine (hξ.mono (𝓖.mono zero_le) le_rfl).prodMk
      (@Measurable.of_eval _ _ _ (𝓖 _) _ _ fun j => ?_)
    exact ((hB.adapted _).mono (𝓖.mono (hs' (Fin.le_last j)))).measurable
  have hVm : Measurable fun ω => (ξ ω, fun j => B (Fin.init s j) ω) := hV.mono (𝓖.le _) le_rfl
  have hΔ : Measurable fun ω => B (s (Fin.last (n + 1))) ω - B (Fin.init s (Fin.last n)) ω :=
    (brownian_measurable hB _).sub (brownian_measurable hB _)
  rw [← map_prod_increment hB hrt hV, Measure.map_map (measurable_snoc_add n) (hVm.prodMk hΔ)]
  congr 1
  funext ω
  simp only [Function.comp_apply, add_sub_cancel]
  congr 1
  exact (Fin.snoc_init_self (α := fun _ => Fin d → ℝ) fun j => B (s j) ω).symm

end OneSpace

/-- **Finite-dimensional laws of `(ξ, B)`.** For monotone times `s_0 ≤ … ≤ s_n`, the law of
`(ξ, B_{s_0}, …, B_{s_n})` depends only on the law of the `𝓖_0`-measurable `ξ`. -/
theorem map_initial_brownian_eq {S : Type*} [MeasurableSpace S]
    {Ω₁ : Type*} [MeasurableSpace Ω₁] {Q₁ : Measure Ω₁} [IsProbabilityMeasure Q₁]
    {𝓖₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₁)} {B₁ : ℝ≥0 → Ω₁ → Fin d → ℝ}
    (hB₁ : IsFiltrationBrownian Q₁ 𝓖₁ B₁) {ξ₁ : Ω₁ → S} (hξ₁ : Measurable[𝓖₁ 0] ξ₁)
    {Ω₂ : Type*} [MeasurableSpace Ω₂] {Q₂ : Measure Ω₂} [IsProbabilityMeasure Q₂]
    {𝓖₂ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₂)} {B₂ : ℝ≥0 → Ω₂ → Fin d → ℝ}
    (hB₂ : IsFiltrationBrownian Q₂ 𝓖₂ B₂) {ξ₂ : Ω₂ → S} (hξ₂ : Measurable[𝓖₂ 0] ξ₂)
    (hξ : Q₁.map ξ₁ = Q₂.map ξ₂) :
    ∀ (n : ℕ) (s : Fin (n + 1) → ℝ≥0), Monotone s →
      Q₁.map (fun ω => (ξ₁ ω, fun j => B₁ (s j) ω)) =
        Q₂.map (fun ω => (ξ₂ ω, fun j => B₂ (s j) ω)) := by
  intro n
  induction n with
  | zero =>
    intro s _
    rw [map_initial_brownian_zero hB₁ hξ₁, map_initial_brownian_zero hB₂ hξ₂, hξ]
  | succ n ih =>
    intro s hs
    rw [map_initial_brownian_succ hB₁ hξ₁ s hs, map_initial_brownian_succ hB₂ hξ₂ s hs,
      ih (Fin.init s) fun i j hij => hs (Fin.castSucc_le_castSucc_iff.2 hij)]

/-- The joint process `(ξ, (B_q)_{q ∈ ℚ≥0})`, indexed by `Option ℚ≥0`. -/
def initBrownian {Ω : Type*} (ξ : Ω → Fin d → ℝ) (B : ℝ≥0 → Ω → Fin d → ℝ) (ω : Ω) :
    Option ℚ≥0 → Fin d → ℝ :=
  fun o => o.elim (ξ ω) fun q => B (q : ℝ≥0) ω

theorem measurable_initBrownian {Ω : Type*} [MeasurableSpace Ω] {ξ : Ω → Fin d → ℝ}
    {B : ℝ≥0 → Ω → Fin d → ℝ} (hξ : Measurable ξ) (hB : ∀ t, Measurable (B t)) :
    Measurable (initBrownian ξ B) := by
  refine Measurable.of_eval fun o => ?_
  cases o with
  | none => exact hξ
  | some q => exact hB _

/-- **Two-space finite-dimensional determination** on a product `Π i, X i`. -/
theorem map_eq_of_fdd_eq₂' {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {Q₁ : Measure Ω₁}
    {Q₂ : Measure Ω₂} [IsFiniteMeasure Q₁] {F : Ω₁ → ∀ i, X i} {G : Ω₂ → ∀ i, X i}
    (hF : AEMeasurable F Q₁) (hG : AEMeasurable G Q₂)
    (h : ∀ I : Finset ι, Q₁.map (fun ω => I.restrict (F ω)) = Q₂.map (fun ω => I.restrict (G ω))) :
    Q₁.map F = Q₂.map G := by
  have h1 := isProjectiveLimit_map (P := Q₁) (X := fun i ω => F ω i) hF
  have h2 := isProjectiveLimit_map (P := Q₂) (X := fun i ω => G ω i) hG
  have hfam : (fun I : Finset ι => Q₁.map (fun ω => I.restrict fun i => F ω i)) =
      fun I => Q₂.map (fun ω => I.restrict fun i => G ω i) := funext h
  rw [hfam] at h1
  have : ∀ I : Finset ι, IsFiniteMeasure (Q₂.map (fun ω => I.restrict fun i => G ω i)) :=
    fun I => by rw [← h I]; infer_instance
  exact h1.unique h2

theorem monotone_cons_zero {k : ℕ} {g : Fin k → ℝ≥0} (hg : Monotone g) :
    Monotone (Fin.cons (0 : ℝ≥0) g : Fin (k + 1) → ℝ≥0) := by
  intro i j hij
  induction i using Fin.cases with
  | zero => simp only [Fin.cons_zero]; exact zero_le
  | succ i =>
    induction j using Fin.cases with
    | zero => exact absurd hij (by simp)
    | succ j => simpa using hg (Fin.succ_le_succ_iff.1 hij)

/-- Sorted times `0, q_1 < … < q_k` of the rational indices of a finite `I ⊆ Option ℚ≥0`. -/
def finTimes (I : Finset (Option ℚ≥0)) : Fin ((Finset.eraseNone I).card + 1) → ℝ≥0 :=
  Fin.cons 0 fun j => (((Finset.eraseNone I).orderIsoOfFin rfl j : ℚ≥0) : ℝ≥0)

theorem monotone_finTimes (I : Finset (Option ℚ≥0)) : Monotone (finTimes I) :=
  monotone_cons_zero fun i j hij => by
    exact_mod_cast (((Finset.eraseNone I).orderIsoOfFin rfl).monotone hij :
      (Finset.eraseNone I).orderIsoOfFin rfl i ≤ (Finset.eraseNone I).orderIsoOfFin rfl j)

/-- Reading the restriction to `I` off `(ξ, B_{finTimes I})`. -/
def finRead (I : Finset (Option ℚ≥0))
    (p : (Fin d → ℝ) × (Fin ((Finset.eraseNone I).card + 1) → Fin d → ℝ)) : I → Fin d → ℝ :=
  fun i => i.1.elim p.1 fun q =>
    p.2 (if h : q ∈ Finset.eraseNone I then
      (((Finset.eraseNone I).orderIsoOfFin rfl).symm ⟨q, h⟩).succ else 0)

theorem measurable_finRead (I : Finset (Option ℚ≥0)) : Measurable (finRead (d := d) I) := by
  refine Measurable.of_eval fun i => ?_
  rcases i with ⟨o, ho⟩
  cases o with
  | none => exact measurable_fst
  | some q =>
    dsimp only [finRead, Option.elim]
    exact (measurable_pi_apply _).comp measurable_snd

theorem map_restrict_initBrownian {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {ξ : Ω → Fin d → ℝ} {B : ℝ≥0 → Ω → Fin d → ℝ} (hξ : Measurable ξ)
    (hB : ∀ t, Measurable (B t)) (I : Finset (Option ℚ≥0)) :
    Q.map (fun ω => I.restrict (initBrownian ξ B ω)) =
      (Q.map fun ω => (ξ ω, fun j => B (finTimes I j) ω)).map (finRead I) := by
  classical
  rw [Measure.map_map (measurable_finRead I) (hξ.prodMk (Measurable.of_eval fun j => hB _))]
  congr 1
  funext ω
  funext i
  rcases i with ⟨o, ho⟩
  cases o with
  | none => rfl
  | some q =>
    have hq : q ∈ Finset.eraseNone I := Finset.mem_eraseNone.2 ho
    simp only [Function.comp_apply, Finset.restrict, initBrownian, Option.elim, finRead,
      hq, dite_true, finTimes, Fin.cons_succ, OrderIso.apply_symm_apply]

/-- **The law of `(ξ, (B_q)_{q ∈ ℚ≥0})` depends only on the law of `ξ`.** -/
theorem map_initBrownian_eq
    {Ω₁ : Type*} [MeasurableSpace Ω₁] {Q₁ : Measure Ω₁} [IsProbabilityMeasure Q₁]
    {𝓖₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₁)} {B₁ : ℝ≥0 → Ω₁ → Fin d → ℝ}
    (hB₁ : IsFiltrationBrownian Q₁ 𝓖₁ B₁) {ξ₁ : Ω₁ → Fin d → ℝ} (hξ₁ : Measurable[𝓖₁ 0] ξ₁)
    {Ω₂ : Type*} [MeasurableSpace Ω₂] {Q₂ : Measure Ω₂} [IsProbabilityMeasure Q₂]
    {𝓖₂ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₂)} {B₂ : ℝ≥0 → Ω₂ → Fin d → ℝ}
    (hB₂ : IsFiltrationBrownian Q₂ 𝓖₂ B₂) {ξ₂ : Ω₂ → Fin d → ℝ} (hξ₂ : Measurable[𝓖₂ 0] ξ₂)
    (hξ : Q₁.map ξ₁ = Q₂.map ξ₂) :
    Q₁.map (initBrownian ξ₁ B₁) = Q₂.map (initBrownian ξ₂ B₂) := by
  have hm₁ := measurable_initBrownian (hξ₁.mono (𝓖₁.le 0) le_rfl) (brownian_measurable hB₁)
  have hm₂ := measurable_initBrownian (hξ₂.mono (𝓖₂.le 0) le_rfl) (brownian_measurable hB₂)
  refine map_eq_of_fdd_eq₂' hm₁.aemeasurable hm₂.aemeasurable fun I => ?_
  rw [map_restrict_initBrownian (hξ₁.mono (𝓖₁.le 0) le_rfl) (brownian_measurable hB₁),
    map_restrict_initBrownian (hξ₂.mono (𝓖₂.le 0) le_rfl) (brownian_measurable hB₂),
    map_initial_brownian_eq hB₁ hξ₁ hB₂ hξ₂ hξ _ _ (monotone_finTimes I)]

end BlockBand.SourceProcess.Stochastic.Uniqueness
