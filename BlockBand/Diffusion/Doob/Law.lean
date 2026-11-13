module

public import BlockBand.Diffusion.Doob.Dual
public import BlockBand.Diffusion.Doob.Ext
public import BlockBand.Diffusion.Markov.Doob

/-!
# The Doob killed law of the one-pair boundary dual

`dkLbkDoobKilledLaw_of`: `DkLbkCornerHeatIdentity D0` implies `DkLbkDoobKilledLaw D0`. The proof is
by induction on the number `k` of times:
* `k = 0`: `σ₀ > 0` a.s. and `(x + y) H(z) = 1`;
* `k → k + 1`: write the time string as `ts' ⧺ t` and put `s = t_k`. For a measurable `A` and a
  test pair `(g, k)`, with `u = dkU D0 g k t` (`u(t, ·) = ℓ (g ⊗ k)`,
  `u(s, w) = ℓ(w) P_{t-s}(g ⊗ k)(w)`), the conditional duality `dk_dual_duality` on the
  `𝓖_s`-set `{Z_{ts'} ∈ A, N_s = 1}` turns `E[1_A(Z_{ts'}) ℓ g k(Z_t); t < σ₀]` into
  `E[1_A(Z_{ts'}) u(s, Z_s); s < σ₀]`, which the induction hypothesis evaluates; Tonelli and
  `ℓ H = 1` off the corner identify the result with the right side at `k + 1`. The two sides
  are integrals against two measures on `(ℝ²)^k × ℝ²` concentrated on `(ℝ²)^k × (0,∞) × (0,1)`
  (the dual is in the open chamber at positive times before `σ₀`; the strip boundary is null),
  so `dk_measure_ext` gives equality for every measurable `F`.

The only hypothesis is `DkLbkCornerHeatIdentity D0` (used for the uniform bound of
the duality functions, `P_t H ≤ H`). The base transition law, Chapman–Kolmogorov and the strong
Markov property are not used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Diffusion

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

/-!
### Bookkeeping for time strings
-/

theorem dk_lastTime_snoc {k : ℕ} (ts : Fin k → ℝ) (r : ℝ) :
    dkLastTime (Fin.snoc ts r : Fin (k + 1) → ℝ) = r := by
  simp only [dkLastTime, ← Fin.succ_last, Fin.cons_succ, Fin.snoc_last]

theorem dk_lastPoint_snoc {α : Type*} (z : α) {k : ℕ} (zs : Fin k → α) (w : α) :
    dkLastPoint z (Fin.snoc zs w : Fin (k + 1) → α) = w := by
  simp only [dkLastPoint, ← Fin.succ_last, Fin.cons_succ, Fin.snoc_last]

theorem dk_fddProd_snoc {α : Type*} (p : ℝ → α → α → ℝ) (z : α) {k : ℕ} (ts : Fin k → ℝ)
    (r : ℝ) (zs : Fin k → α) (w : α) :
    dkFddProd p z (Fin.snoc ts r : Fin (k + 1) → ℝ) (Fin.snoc zs w : Fin (k + 1) → α) =
      dkFddProd p z ts zs * ENNReal.ofReal (p (r - dkLastTime ts) (dkLastPoint z zs) w) := by
  unfold dkFddProd dkLastTime dkLastPoint
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.cons_snoc_eq_snoc_cons, Fin.snoc_castSucc, Fin.snoc_last]

theorem dk_measurable_cons {α : Type*} [MeasurableSpace α] (z : α) {k : ℕ} (j : Fin (k + 1)) :
    Measurable fun zs : Fin k → α => (Fin.cons z zs : Fin (k + 1) → α) j := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simp only [Fin.cons_zero]
    exact measurable_const
  · simp only [Fin.cons_succ]
    exact measurable_pi_apply i

theorem dk_fddProd_measurable {p : ℝ → ℝ × ℝ → ℝ × ℝ → ℝ}
    (hp : Measurable fun w : ℝ × (ℝ × ℝ) × (ℝ × ℝ) => p w.1 w.2.1 w.2.2) (z : ℝ × ℝ) {k : ℕ}
    (ts : Fin k → ℝ) : Measurable fun zs : Fin k → ℝ × ℝ => dkFddProd p z ts zs := by
  unfold dkFddProd
  refine Finset.measurable_prod _ fun i _ => ?_
  exact (hp.comp ((measurable_const.prodMk ((dk_measurable_cons z i.castSucc).prodMk
    (measurable_pi_apply i))))).ennreal_ofReal

theorem dk_lastTime_nonneg {k : ℕ} {ts : Fin k → ℝ} (hpos : ∀ i, 0 < ts i) :
    0 ≤ dkLastTime ts := by
  cases k with
  | zero => simp [dkLastTime]
  | succ m =>
    simp only [dkLastTime, ← Fin.succ_last, Fin.cons_succ]
    exact (hpos _).le

/-!
### Auxiliary facts
-/

theorem measurable_dkLastPoint (z : ℝ × ℝ) {k : ℕ} :
    Measurable fun zs : Fin k → ℝ × ℝ => dkLastPoint z zs :=
  dk_measurable_cons z (Fin.last k)

theorem measurable_dkHarm : Measurable dkHarm := (measurable_fst.add measurable_snd).inv

theorem measurable_snoc_pair {E : Type*} [MeasurableSpace E] {k : ℕ} :
    Measurable fun q : (Fin k → E) × E => (Fin.snoc q.1 q.2 : Fin (k + 1) → E) := by
  refine measurable_pi_iff.2 fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]; exact measurable_snd
  · simp only [Fin.snoc_castSucc]; exact (measurable_pi_apply j).comp measurable_fst

theorem dkFddProd_eq_zero_of_last {D0 : ℝ} {z : ℝ × ℝ} (hz : z ∈ exBaseStrip) {k : ℕ}
    (ts : Fin k → ℝ) {zs : Fin k → ℝ × ℝ} (h : dkLastPoint z zs ∉ exBaseStrip) :
    dkFddProd (exKernel D0) z ts zs = 0 := by
  cases k with
  | zero => exact absurd hz h
  | succ m =>
    have hl : dkLastPoint z zs = zs (Fin.last m) := by
      simp only [dkLastPoint, ← Fin.succ_last, Fin.cons_succ]
    rw [hl] at h
    unfold dkFddProd
    refine Finset.prod_eq_zero (Finset.mem_univ (Fin.last m)) ?_
    rw [exKernel_eq_zero_of_notMem h, ENNReal.ofReal_zero]

theorem volume_strip_boundary :
    (volume : Measure (ℝ × ℝ)) {w | w ∈ exBaseStrip ∧ w ∉ exOpenStrip} = 0 := by
  have hsub : {w : ℝ × ℝ | w ∈ exBaseStrip ∧ w ∉ exOpenStrip} ⊆
      ({0} ×ˢ univ) ∪ (univ ×ˢ {0}) ∪ (univ ×ˢ {1}) := by
    rintro ⟨a, b⟩ ⟨⟨ha, hb0, hb1⟩, hno⟩
    have ha' : (0 : ℝ) ≤ a := ha
    simp only [exOpenStrip, mem_prod, mem_Ioi, mem_Ioo, not_and_or, not_lt] at hno ha hb0 hb1
    simp only [mem_union, mem_prod, mem_singleton_iff, mem_univ, and_true, true_and]
    rcases hno with h | h | h
    · left; left; linarith
    · left; right; linarith
    · right; linarith
  refine measure_mono_null hsub (measure_union_null (measure_union_null ?_ ?_) ?_) <;>
    rw [Measure.volume_eq_prod, Measure.prod_prod] <;> simp

theorem finProd_symm_apply_zero (w : ℝ × ℝ) : finProd.symm w 0 = w.1 := rfl

theorem finProd_symm_apply_one (w : ℝ × ℝ) : finProd.symm w 1 = w.2 := rfl

theorem finProd_apply' (v : Fin 2 → ℝ) : finProd v = (v 0, v 1) := rfl

theorem dkHarm_mul {w : ℝ × ℝ} (hw : 0 < w.1 + w.2) : (w.1 + w.2) * dkHarm w = 1 := by
  rw [dkHarm]; field_simp

theorem pos_of_mem_strip_ne {w : ℝ × ℝ} (hw : w ∈ exBaseStrip) (h0 : w ≠ (0, 0)) :
    0 < w.1 + w.2 := by
  have h1' : (0 : ℝ) ≤ w.1 := hw.1
  have h2' : (0 : ℝ) ≤ w.2 := hw.2.1
  rcases (add_nonneg h1' h2').lt_or_eq with h | h
  · exact h
  · exfalso; apply h0
    have h1 : w.1 = 0 := by linarith
    have h2 : w.2 = 0 := by linarith
    exact Prod.ext h1 h2

/-!
### The induction
-/

section Law

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {D0 x y : ℝ} {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}
  (hD0 : 0 < D0) (hCH : DkLbkCornerHeatIdentity D0)
  (hP : IsDkBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y) (hz : IsDkDualStart ![x] ![y])

/-- The killed-path form of the left side. -/
def dkKillLHS (P : Measure Ω) (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ) {k : ℕ}
    (ts : Fin k → ℝ) (F : (Fin k → ℝ × ℝ) → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ ω, (if ENNReal.ofReal (dkLastTime ts) < dkDualExtinction N ω
    then F (fun i => finProd (dkZf N X Y (ts i).toNNReal ω)) else 0) ∂P

/-- The right side. -/
def dkKillRHS (D0 x y : ℝ) {k : ℕ} (ts : Fin k → ℝ) (F : (Fin k → ℝ × ℝ) → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ zs, F zs * dkFddProd (exKernel D0) (x, y) ts zs *
    ENNReal.ofReal ((x + y) * dkHarm (dkLastPoint (x, y) zs))

include hP in
/-- On good paths the level is `1` exactly before the lifetime. -/
theorem ae_level_iff : ∀ᵐ ω ∂P, ∀ r : ℝ≥0, N r ω = 1 ↔ (r : ℝ≥0∞) < dkDualExtinction N ω :=
  hP.ae_good.mono fun _ h r => dk_level_eq_one_iff h.2 h.1.1 r

include hz in
theorem dk_xy_pos : 0 < x + y := by
  obtain ⟨-, -, -, -, h⟩ := hz
  simpa using h 0 0

include hz in
theorem dk_xy_strip : (x, y) ∈ exBaseStrip := dk_start_mem_strip hz

include hz in
theorem dk_xy_ne : ((x, y) : ℝ × ℝ) ≠ (0, 0) := fun h => by
  have := dk_xy_pos hz
  simp only [Prod.mk.injEq] at h
  linarith [h.1, h.2]

include hD0 hCH hP hz

omit hCH in
/-- **The base case `k = 0`.** -/
theorem dk_killed_zero (ts : Fin 0 → ℝ) {F : (Fin 0 → ℝ × ℝ) → ℝ≥0∞} (hF : Measurable F) :
    dkKillLHS P N X Y ts F = dkKillRHS D0 x y ts F := by
  have := hP.prob
  set zs₀ : Fin 0 → ℝ × ℝ := fun i => i.elim0
  have hc : ∀ zs : Fin 0 → ℝ × ℝ, zs = zs₀ := fun zs => funext fun i => i.elim0
  unfold dkKillLHS dkKillRHS
  have hL : ∫⁻ ω, (if ENNReal.ofReal (dkLastTime ts) < dkDualExtinction N ω
      then F (fun i => finProd (dkZf N X Y (ts i).toNNReal ω)) else 0) ∂P = F zs₀ := by
    rw [lintegral_congr_ae (g := fun _ => F zs₀) (hP.ae_killed.mono fun ω h => by
      have : ENNReal.ofReal (dkLastTime ts) = 0 := by simp [dkLastTime]
      simp only [this, h.2.2.2.2, ↓reduceIte, hc])]
    simp
  have hm : Measurable fun zs : Fin 0 → ℝ × ℝ => F zs * dkFddProd (exKernel D0) (x, y) ts zs *
      ENNReal.ofReal ((x + y) * dkHarm (dkLastPoint (x, y) zs)) :=
    (hF.mul (dk_fddProd_measurable (exKernel_measurable hD0) _ ts)).mul
      ((measurable_const.mul (measurable_dkHarm.comp (measurable_dkLastPoint _))).ennreal_ofReal)
  rw [hL, volume_pi, lintegral_pi_zero volume hm zs₀]
  have hl : dkLastPoint (x, y) zs₀ = (x, y) := rfl
  have hH : (x + y) * dkHarm (x, y) = 1 := dkHarm_mul (w := (x, y)) (dk_xy_pos hz)
  rw [hl, hH, ENNReal.ofReal_one, mul_one]
  simp [dkFddProd]

omit [MeasurableSpace Ω] hCH hP hz in
/-- The slice `w ↦ u(s, w)` of the duality function is measurable (`s < t`). -/
theorem measurable_dkU_slice {g k : ℝ → ℝ} (hgk : IsDkTestPair g k) {s t : ℝ} (hst : s < t) :
    Measurable fun w : ℝ × ℝ => dkU D0 g k t (s, finProd.symm w) := by
  have e : (fun w : ℝ × ℝ => dkU D0 g k t (s, finProd.symm w)) =
      fun w => (w.1 + w.2) * exProdSol D0 g k t (s, w) := by
    funext w
    rw [dkU_eq_exProdSol]
    simp only
    rw [ContinuousLinearEquiv.apply_symm_apply, dkEll_apply, finProd_symm_apply_zero,
      finProd_symm_apply_one]
  rw [e]
  exact (measurable_fst.add measurable_snd).mul
    (measurable_exProdSol D0 hgk.contg.measurable hgk.contk.measurable hst hD0)

omit [MeasurableSpace Ω] hD0 hCH hP hz in
/-- On good paths, the last point of the string of killed points is the killed point at the
last time. -/
theorem dk_lastPoint_killed {k : ℕ} {ts : Fin k → ℝ} {ω : Ω}
    (h0 : dkZf N X Y 0 ω = finProd.symm (x, y)) :
    finProd.symm (dkLastPoint (x, y) fun i => finProd (dkZf N X Y (ts i).toNNReal ω)) =
      dkZf N X Y (dkLastTime ts).toNNReal ω := by
  cases k with
  | zero => simp [dkLastPoint, dkLastTime, h0]
  | succ m =>
    simp only [dkLastPoint, dkLastTime, ← Fin.succ_last, Fin.cons_succ,
      ContinuousLinearEquiv.symm_apply_apply]

/-- **The key identity**: both sides agree on the duality tests. -/
theorem dk_key_identity {k : ℕ}
    (IH : ∀ F : (Fin k → ℝ × ℝ) → ℝ≥0∞, Measurable F →
      ∀ ts : Fin k → ℝ, StrictMono ts → (∀ i, 0 < ts i) →
        dkKillLHS P N X Y ts F = dkKillRHS D0 x y ts F)
    {ts' : Fin k → ℝ} (hts' : StrictMono ts') (hpos' : ∀ i, 0 < ts' i) {t : ℝ}
    (ht : dkLastTime ts' < t) {A : Set (Fin k → ℝ × ℝ)} (hA : MeasurableSet A)
    {g k₂ : ℝ → ℝ} (hgk : IsDkTestPair g k₂) :
    ∫⁻ ω in {ω | N t.toNNReal ω = 1}, dkTestFun A g k₂
        ((fun i => finProd (dkZf N X Y (ts' i).toNNReal ω)), finProd (dkZf N X Y t.toNNReal ω))
        ∂P =
      ∫⁻ a, ∫⁻ w, dkFddProd (exKernel D0) (x, y) ts' a *
        ENNReal.ofReal (exKernel D0 (t - dkLastTime ts') (dkLastPoint (x, y) a) w) *
          ENNReal.ofReal ((x + y) * dkHarm w) * dkTestFun A g k₂ (a, w)
        ∂(volume : Measure (ℝ × ℝ)) ∂(Measure.pi fun _ : Fin k => (volume : Measure (ℝ × ℝ))) := by
  have := hP.prob
  set s := dkLastTime ts' with hsdef
  have hs0 : 0 ≤ s := dk_lastTime_nonneg hpos'
  have ht0 : 0 < t := lt_of_le_of_lt hs0 ht
  set sN : ℝ≥0 := s.toNNReal with hsN
  set tN : ℝ≥0 := t.toNNReal with htN
  have hsNR : (sN : ℝ) = s := Real.coe_toNNReal _ hs0
  have htNR : (tN : ℝ) = t := Real.coe_toNNReal _ ht0.le
  have hst : sN < tN := by rw [← NNReal.coe_lt_coe, hsNR, htNR]; exact ht
  have htN0 : 0 < tN := lt_of_le_of_lt zero_le hst
  set u : ℝ × (Fin 2 → ℝ) → ℝ := dkU D0 g k₂ (tN : ℝ) with hu
  set Zs : Ω → Fin k → ℝ × ℝ := fun ω i => finProd (dkZf N X Y (ts' i).toNNReal ω) with hZs
  set B : Set Ω := {ω | Zs ω ∈ A} ∩ {ω | N sN ω = 1} with hB
  -- measurability
  have hZsm : Measurable[𝓖 sN] Zs := by
    refine @Measurable.of_eval Ω (Fin k) (fun _ => ℝ × ℝ) (𝓖 sN) _ Zs fun i => ?_
    have hle : (ts' i).toNNReal ≤ sN := by
      cases k with
      | zero => exact i.elim0
      | succ m =>
        refine Real.toNNReal_le_toNNReal ?_
        simp only [hsdef, dkLastTime, ← Fin.succ_last, Fin.cons_succ]
        exact hts'.monotone (Fin.le_last i)
    exact finProd.continuous.measurable.comp
      (((stronglyMeasurable_dkZf hP _).measurable).mono (𝓖.mono hle) le_rfl)
  have hBm : MeasurableSet[𝓖 sN] B :=
    (hZsm hA).inter ((hP.adapted sN).1 (measurableSet_singleton 1))
  have hBm' : MeasurableSet B := 𝓖.le sN B hBm
  have hEm : MeasurableSet {ω | N tN ω = 1} :=
    𝓖.le tN _ ((hP.adapted tN).1 (measurableSet_singleton 1))
  obtain ⟨hit, his, hdual⟩ := dk_dual_duality hD0 hCH hP hz hgk hst
  -- nonnegativity of the duality function along the path
  have hnn : ∀ r : ℝ≥0, r ≤ tN → ∀ᵐ ω ∂P, 0 ≤ u ((r : ℝ), dkZf N X Y r ω) := fun r hr => by
    filter_upwards [hP.ae_killed] with ω h
    obtain ⟨R, hR⟩ := hgk.supp
    by_cases h1 : (r : ℝ≥0∞) < dkDualExtinction N ω
    · rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ r) with h0 | h0
      · subst h0
        rw [h.2.2.1]
        rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ tN) with h2 | h2
        · exact absurd h2.symm htN0.ne'
        have hlt : ((0 : ℝ≥0) : ℝ) < (tN : ℝ) := by exact_mod_cast h2
        rw [hu, dkU_eq_integral D0 g k₂ hlt]
        refine mul_nonneg ?_ (integral_nonneg fun z' => mul_nonneg (exKernel_nonneg hD0 _ _ _)
          (mul_nonneg (hgk.g_nonneg _) (hgk.k_nonneg _)))
        rw [dkEll_apply, finProd_symm_apply_zero, finProd_symm_apply_one]
        exact (dk_xy_pos hz).le
      · exact (dkU_le hD0 hCH hgk hR (by exact_mod_cast hr) (h.1 r h0 h1)).1
    · push Not at h1
      rw [h.2.1 r h1, hu, dkU_zero]
  
  have hL1 : ∀ᵐ ω ∂P, {ω | N tN ω = 1}.indicator (fun ω => dkTestFun A g k₂
      (Zs ω, finProd (dkZf N X Y tN ω))) ω =
      B.indicator (fun ω => ENNReal.ofReal (u ((tN : ℝ), dkZf N X Y tN ω))) ω := by
    filter_upwards [hP.ae_killed, ae_level_iff hP, hP.ae_good] with ω h hlev hg
    by_cases hN : N tN ω = 1
    · have hσ : (tN : ℝ≥0∞) < dkDualExtinction N ω := (hlev tN).1 hN
      have hNs : N sN ω = 1 := by
        have h1 := dk_level_le_one hg.2 hg.1.1 sN
        have h2 : N tN ω ≤ N sN ω := hg.2.antitone hst.le
        omega
      rw [indicator_of_mem (show ω ∈ {ω | N tN ω = 1} from hN)]
      have hu' : u ((tN : ℝ), dkZf N X Y tN ω) = (dkZf N X Y tN ω 0 + dkZf N X Y tN ω 1) *
          (g (dkZf N X Y tN ω 0) * k₂ (dkZf N X Y tN ω 1)) := by
        rw [hu, dkU_terminal, dkEll_apply]
      by_cases hZA : Zs ω ∈ A
      · rw [indicator_of_mem (show ω ∈ B from ⟨hZA, hNs⟩), hu']
        simp only [dkTestFun, indicator_of_mem hZA, Pi.one_apply, one_mul]
        congr 1
        simp only [finProd]
        rw [mul_assoc]
        rfl
      · rw [indicator_of_notMem (show ω ∉ B from fun hB' => hZA hB'.1)]
        simp [dkTestFun, indicator_of_notMem hZA]
    · rw [indicator_of_notMem (show ω ∉ {ω | N tN ω = 1} from hN)]
      have hσ : dkDualExtinction N ω ≤ tN := by
        by_contra hc; push Not at hc; exact hN ((hlev tN).2 hc)
      by_cases hωB : ω ∈ B
      · rw [indicator_of_mem hωB, h.2.1 tN hσ, hu, dkU_zero, ENNReal.ofReal_zero]
      · rw [indicator_of_notMem hωB]
  
  set Φ : ℝ × ℝ → ℝ≥0∞ := fun w => ENNReal.ofReal (u ((sN : ℝ), finProd.symm w)) with hΦ
  have hΦm : Measurable Φ :=
    (measurable_dkU_slice hD0 hgk (by exact_mod_cast hst)).ennreal_ofReal
  set F' : (Fin k → ℝ × ℝ) → ℝ≥0∞ := fun zs => A.indicator 1 zs * Φ (dkLastPoint (x, y) zs)
    with hF'
  have hF'm : Measurable F' :=
    (measurable_const.indicator hA).mul (hΦm.comp (measurable_dkLastPoint _))
  have hL5 : ∀ᵐ ω ∂P, B.indicator (fun ω => ENNReal.ofReal (u ((sN : ℝ), dkZf N X Y sN ω))) ω =
      (if ENNReal.ofReal (dkLastTime ts') < dkDualExtinction N ω then F' (Zs ω) else 0) := by
    filter_upwards [hP.ae_killed, ae_level_iff hP] with ω h hlev
    have hlast := dk_lastPoint_killed (ts := ts') h.2.2.1
    have hiff : N sN ω = 1 ↔ ENNReal.ofReal (dkLastTime ts') < dkDualExtinction N ω := hlev sN
    by_cases hN : N sN ω = 1
    · have hc := hiff.1 hN
      simp only [hc, ↓reduceIte]
      have hΦe : Φ (dkLastPoint (x, y) (Zs ω)) =
          ENNReal.ofReal (u ((sN : ℝ), dkZf N X Y sN ω)) := by
        simp only [hΦ, hZs]; rw [hlast]
      by_cases hZA : Zs ω ∈ A
      · rw [indicator_of_mem (show ω ∈ B from ⟨hZA, hN⟩)]
        simp only [hF', indicator_of_mem hZA, Pi.one_apply, one_mul, hΦe]
      · rw [indicator_of_notMem (show ω ∉ B from fun hB' => hZA hB'.1)]
        simp [hF', indicator_of_notMem hZA]
    · have hc : ¬ ENNReal.ofReal (dkLastTime ts') < dkDualExtinction N ω := fun h' => hN (hiff.2 h')
      simp only [hc, ↓reduceIte]
      rw [indicator_of_notMem (show ω ∉ B from fun hB' => hN hB'.2)]
  -- the left side
  have hLHS : ∫⁻ ω in {ω | N tN ω = 1}, dkTestFun A g k₂ (Zs ω, finProd (dkZf N X Y tN ω))
      ∂P = dkKillRHS D0 x y ts' F' := by
    rw [← lintegral_indicator hEm, lintegral_congr_ae hL1, lintegral_indicator hBm',
      ← ofReal_integral_eq_lintegral_ofReal hit.integrableOn (ae_restrict_of_ae (hnn tN le_rfl)),
      hdual B hBm, ofReal_integral_eq_lintegral_ofReal his.integrableOn
        (ae_restrict_of_ae (hnn sN hst.le)), ← lintegral_indicator hBm',
      lintegral_congr_ae hL5]
    exact IH F' hF'm ts' hts' hpos'
  rw [hLHS, dkKillRHS, volume_pi]
  -- the right side, `a` by `a`
  have hrect : ∀ᵐ a ∂(Measure.pi fun _ : Fin k => (volume : Measure (ℝ × ℝ))),
      dkLastPoint (x, y) a ≠ (0, 0) := by
    have h1 : ∀ᵐ w ∂(volume : Measure (ℝ × ℝ)), w ≠ (0, 0) :=
      (measure_eq_zero_iff_ae_notMem.1 (measure_singleton ((0 : ℝ), (0 : ℝ)))).mono
        fun w h => h
    exact ae_lastPoint h1 (dk_xy_ne hz)
  refine lintegral_congr_ae (hrect.mono fun a ha => ?_)
  dsimp only
  set w₀ := dkLastPoint (x, y) a with hw₀
  by_cases hstrip : w₀ ∈ exBaseStrip
  swap
  · have h0 := dkFddProd_eq_zero_of_last (D0 := D0) (dk_xy_strip hz) ts' hstrip
    simp [h0]
  have hpos : 0 < w₀.1 + w₀.2 := pos_of_mem_strip_ne hstrip ha
  set I : ℝ := ∫ z', exKernel D0 (t - s) w₀ z' * (g z'.1 * k₂ z'.2) with hI
  have hτ : 0 < t - s := sub_pos.2 ht
  have hgkm : Measurable fun z' : ℝ × ℝ => g z'.1 * k₂ z'.2 :=
    (hgk.contg.measurable.comp measurable_fst).mul (hgk.contk.measurable.comp measurable_snd)
  have hint : Integrable fun z' => exKernel D0 (t - s) w₀ z' * (g z'.1 * k₂ z'.2) :=
    integrable_exKernel_mul hD0 hτ hstrip hgkm.aestronglyMeasurable (C := 1) fun z' => by
      rw [abs_of_nonneg (mul_nonneg (hgk.g_nonneg _) (hgk.k_nonneg _))]
      exact hgk.mul_le_one _ _
  have hI0 : 0 ≤ I := integral_nonneg fun z' => mul_nonneg (exKernel_nonneg hD0 _ _ _)
    (mul_nonneg (hgk.g_nonneg _) (hgk.k_nonneg _))
  -- the inner integral
  have hinner : ∫⁻ w, ENNReal.ofReal (exKernel D0 (t - s) w₀ w) *
      ENNReal.ofReal ((x + y) * dkHarm w) *
        ENNReal.ofReal ((w.1 + w.2) * g w.1 * k₂ w.2) =
      ENNReal.ofReal (x + y) * ENNReal.ofReal I := by
    have hae : ∀ᵐ w ∂(volume : Measure (ℝ × ℝ)), w ≠ (0, 0) :=
      (measure_eq_zero_iff_ae_notMem.1 (measure_singleton ((0 : ℝ), (0 : ℝ)))).mono
        fun w h => h
    rw [hI, ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun z' => mul_nonneg
      (exKernel_nonneg hD0 _ _ _) (mul_nonneg (hgk.g_nonneg _) (hgk.k_nonneg _))),
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr_ae (hae.mono fun w hw => ?_)
    dsimp only
    by_cases hws : w ∈ exBaseStrip
    · have hwp : 0 < w.1 + w.2 := pos_of_mem_strip_ne hws hw
      have hp0 := exKernel_nonneg hD0 (t - s) w₀ w
      have hgk0 : 0 ≤ g w.1 * k₂ w.2 := mul_nonneg (hgk.g_nonneg _) (hgk.k_nonneg _)
      have hH0 : 0 ≤ (x + y) * dkHarm w := mul_nonneg (dk_xy_pos hz).le
        (by rw [dkHarm]; exact inv_nonneg.2 hwp.le)
      rw [← ENNReal.ofReal_mul hp0, ← ENNReal.ofReal_mul (mul_nonneg hp0 hH0),
        ← ENNReal.ofReal_mul (dk_xy_pos hz).le]
      congr 1
      have hHw := dkHarm_mul hwp
      calc exKernel D0 (t - s) w₀ w * ((x + y) * dkHarm w) * ((w.1 + w.2) * g w.1 * k₂ w.2)
          = (x + y) * (exKernel D0 (t - s) w₀ w * (g w.1 * k₂ w.2)) *
              ((w.1 + w.2) * dkHarm w) := by ring
        _ = (x + y) * (exKernel D0 (t - s) w₀ w * (g w.1 * k₂ w.2)) := by rw [hHw, mul_one]
    · simp [exKernel_eq_zero_of_notMem hws]
  have hΦw : Φ w₀ * ENNReal.ofReal ((x + y) * dkHarm w₀) =
      ENNReal.ofReal (x + y) * ENNReal.ofReal I := by
    have hU : u ((sN : ℝ), finProd.symm w₀) = (w₀.1 + w₀.2) * I := by
      rw [hu, dkU_eq_integral D0 g k₂ (by exact_mod_cast hst), hsNR, htNR,
        ContinuousLinearEquiv.apply_symm_apply, dkEll_apply, finProd_symm_apply_zero,
        finProd_symm_apply_one]
    have hH0 : 0 ≤ (x + y) * dkHarm w₀ := mul_nonneg (dk_xy_pos hz).le
      (by rw [dkHarm]; exact inv_nonneg.2 hpos.le)
    show ENNReal.ofReal (u ((sN : ℝ), finProd.symm w₀)) * _ = _
    rw [hU, ← ENNReal.ofReal_mul (mul_nonneg hpos.le hI0),
      ← ENNReal.ofReal_mul (dk_xy_pos hz).le]
    congr 1
    have hHw := dkHarm_mul hpos
    calc (w₀.1 + w₀.2) * I * ((x + y) * dkHarm w₀) = (x + y) * I * ((w₀.1 + w₀.2) * dkHarm w₀) :=
          by ring
      _ = (x + y) * I := by rw [hHw, mul_one]
  -- assemble
  have hcomp : ∀ w, dkFddProd (exKernel D0) (x, y) ts' a *
      ENNReal.ofReal (exKernel D0 (t - s) w₀ w) * ENNReal.ofReal ((x + y) * dkHarm w) *
        dkTestFun A g k₂ (a, w) =
      A.indicator 1 a * dkFddProd (exKernel D0) (x, y) ts' a *
        (ENNReal.ofReal (exKernel D0 (t - s) w₀ w) * ENNReal.ofReal ((x + y) * dkHarm w) *
          ENNReal.ofReal ((w.1 + w.2) * g w.1 * k₂ w.2)) := fun w => by
    simp only [dkTestFun]; ring
  simp only [hcomp]
  rw [lintegral_const_mul' _ _ (by
    refine ENNReal.mul_ne_top (by by_cases h : a ∈ A <;> simp [h]) ?_
    unfold dkFddProd; exact ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top), hinner]
  simp only [hF']
  rw [← hw₀]
  calc A.indicator 1 a * Φ w₀ * dkFddProd (exKernel D0) (x, y) ts' a *
        ENNReal.ofReal ((x + y) * dkHarm w₀)
      = A.indicator 1 a * dkFddProd (exKernel D0) (x, y) ts' a *
          (Φ w₀ * ENNReal.ofReal ((x + y) * dkHarm w₀)) := by ring
    _ = _ := by rw [hΦw]

/-- **The induction step.** -/
theorem dk_killed_succ {k : ℕ}
    (IH : ∀ F : (Fin k → ℝ × ℝ) → ℝ≥0∞, Measurable F →
      ∀ ts : Fin k → ℝ, StrictMono ts → (∀ i, 0 < ts i) →
        dkKillLHS P N X Y ts F = dkKillRHS D0 x y ts F)
    {ts' : Fin k → ℝ} (hts' : StrictMono ts') (hpos' : ∀ i, 0 < ts' i) {t : ℝ}
    (ht : dkLastTime ts' < t) {F : (Fin (k + 1) → ℝ × ℝ) → ℝ≥0∞} (hF : Measurable F) :
    dkKillLHS P N X Y (Fin.snoc ts' t) F = dkKillRHS D0 x y (Fin.snoc ts' t) F := by
  have := hP.prob
  set s := dkLastTime ts' with hsdef
  have hs0 : 0 ≤ s := dk_lastTime_nonneg hpos'
  have ht0 : 0 < t := lt_of_le_of_lt hs0 ht
  set tN : ℝ≥0 := t.toNNReal with htN
  set Ψ : Ω → (Fin k → ℝ × ℝ) × (ℝ × ℝ) := fun ω =>
    ((fun i => finProd (dkZf N X Y (ts' i).toNNReal ω)), finProd (dkZf N X Y tN ω)) with hΨ
  have hΨm : Measurable Ψ := by
    refine Measurable.prodMk (measurable_pi_iff.2 fun i => ?_) ?_
    · exact finProd.continuous.measurable.comp ((stronglyMeasurable_dkZf hP _).measurable.mono
        (𝓖.le _) le_rfl)
    · exact finProd.continuous.measurable.comp ((stronglyMeasurable_dkZf hP _).measurable.mono
        (𝓖.le _) le_rfl)
  set E : Set Ω := {ω | N tN ω = 1} with hE
  have hEm : MeasurableSet E := 𝓖.le tN _ ((hP.adapted tN).1 (measurableSet_singleton 1))
  set μL : Measure ((Fin k → ℝ × ℝ) × (ℝ × ℝ)) := (P.restrict E).map Ψ with hμL
  set K : (Fin k → ℝ × ℝ) × (ℝ × ℝ) → ℝ≥0∞ := fun q =>
    dkFddProd (exKernel D0) (x, y) ts' q.1 *
      ENNReal.ofReal (exKernel D0 (t - s) (dkLastPoint (x, y) q.1) q.2) *
        ENNReal.ofReal ((x + y) * dkHarm q.2) with hK
  have hKm : Measurable K := by
    refine ((dk_fddProd_measurable (exKernel_measurable hD0) _ ts').comp measurable_fst).mul
      ?_ |>.mul ?_
    · exact ((exKernel_measurable hD0).comp (measurable_const.prodMk
        (((measurable_dkLastPoint _).comp measurable_fst).prodMk measurable_snd))).ennreal_ofReal
    · exact (measurable_const.mul (measurable_dkHarm.comp measurable_snd)).ennreal_ofReal
  set μR : Measure ((Fin k → ℝ × ℝ) × (ℝ × ℝ)) :=
    ((Measure.pi fun _ : Fin k => (volume : Measure (ℝ × ℝ))).prod volume).withDensity K
    with hμR
  -- (a) the left side as an integral against `μL`
  have hLa : ∀ G : (Fin (k + 1) → ℝ × ℝ) → ℝ≥0∞, Measurable G →
      dkKillLHS P N X Y (Fin.snoc ts' t) G = ∫⁻ q, G (Fin.snoc q.1 q.2) ∂μL := by
    intro G hG
    have hGm : Measurable fun q : (Fin k → ℝ × ℝ) × (ℝ × ℝ) => G (Fin.snoc q.1 q.2) :=
      hG.comp measurable_snoc_pair
    rw [hμL, lintegral_map hGm hΨm, ← lintegral_indicator hEm, dkKillLHS, dk_lastTime_snoc]
    refine lintegral_congr_ae ((ae_level_iff hP).mono fun ω hlev => ?_)
    have hfun : (fun i => finProd (dkZf N X Y ((Fin.snoc ts' t : Fin (k + 1) → ℝ) i).toNNReal
        ω)) = Fin.snoc (Ψ ω).1 (Ψ ω).2 := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [hΨ, htN]
      · simp [hΨ]
    have hiff : ENNReal.ofReal t < dkDualExtinction N ω ↔ ω ∈ E := (hlev tN).symm
    by_cases hω : ω ∈ E
    · simp only [hiff.2 hω, ↓reduceIte, indicator_of_mem hω, hfun]
    · have hc : ¬ ENNReal.ofReal t < dkDualExtinction N ω := fun h => hω (hiff.1 h)
      simp only [hc, ↓reduceIte, indicator_of_notMem hω]
  -- (b) the right side as an integral against `μR`
  have hRb : ∀ G : (Fin (k + 1) → ℝ × ℝ) → ℝ≥0∞, Measurable G →
      dkKillRHS D0 x y (Fin.snoc ts' t) G = ∫⁻ q, G (Fin.snoc q.1 q.2) ∂μR := by
    intro G hG
    have hGm : Measurable fun q : (Fin k → ℝ × ℝ) × (ℝ × ℝ) => G (Fin.snoc q.1 q.2) :=
      hG.comp measurable_snoc_pair
    have hint : Measurable fun zs : Fin (k + 1) → ℝ × ℝ => G zs *
        dkFddProd (exKernel D0) (x, y) (Fin.snoc ts' t) zs *
          ENNReal.ofReal ((x + y) * dkHarm (dkLastPoint (x, y) zs)) :=
      (hG.mul (dk_fddProd_measurable (exKernel_measurable hD0) _ _)).mul
        ((measurable_const.mul (measurable_dkHarm.comp (measurable_dkLastPoint _))).ennreal_ofReal)
    rw [dkKillRHS, volume_pi, lintegral_pi_snoc volume hint, hμR,
      lintegral_withDensity_eq_lintegral_mul _ hKm hGm, lintegral_prod _ (hKm.mul hGm).aemeasurable]
    refine lintegral_congr fun a => lintegral_congr fun w => ?_
    simp only [dk_fddProd_snoc, dk_lastPoint_snoc, hK, Pi.mul_apply]
    ring
  -- (c) the two measures agree
  have hμ : μL = μR := by
    have : IsFiniteMeasure μL := by rw [hμL]; infer_instance
    refine dk_measure_ext ?_ ?_ fun A hA g k₂ hgk => ?_
    · have hOm : MeasurableSet {q : (Fin k → ℝ × ℝ) × (ℝ × ℝ) | q.2 ∈ exOpenStrip} :=
        measurable_snd (measurableSet_Ioi.prod measurableSet_Ioo)
      rw [hμL, ae_map_iff hΨm.aemeasurable hOm]
      refine (ae_restrict_iff' hEm).2 ?_
      filter_upwards [hP.ae_killed, ae_level_iff hP] with ω h hlev hωE
      have hσ : (tN : ℝ≥0∞) < dkDualExtinction N ω := (hlev tN).1 hωE
      have hpos : 0 < tN := by rw [htN]; exact Real.toNNReal_pos.2 ht0
      have hm := h.1 tN hpos hσ
      exact ⟨hm.1, hm.2.1, hm.2.2⟩
    · rw [hμR, ae_withDensity_iff hKm]
      have hnull : (((Measure.pi fun _ : Fin k => (volume : Measure (ℝ × ℝ))).prod volume)
          (univ ×ˢ {w | w ∈ exBaseStrip ∧ w ∉ exOpenStrip})) = 0 := by
        rw [Measure.prod_prod, volume_strip_boundary, mul_zero]
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with q hq hKq
      have hstrip : q.2 ∈ exBaseStrip := by
        by_contra hc
        apply hKq
        simp only [hK, exKernel_eq_zero_of_notMem hc, ENNReal.ofReal_zero, mul_zero, zero_mul]
      by_contra hc
      exact hq ⟨mem_univ _, hstrip, hc⟩
    · have hkey := dk_key_identity hD0 hCH hP hz IH hts' hpos' ht hA hgk
      have hTm : Measurable (dkTestFun A g k₂) := measurable_dkTestFun hA hgk.contg.measurable
        hgk.contk.measurable
      rw [hμL, lintegral_map hTm hΨm, hμR, lintegral_withDensity_eq_lintegral_mul _ hKm hTm,
        lintegral_prod _ (hKm.mul hTm).aemeasurable]
      exact hkey
  rw [hLa F hF, hRb F hF, hμ]

/-- **The killed finite-dimensional law, killed-path form.** -/
theorem dk_killed_law {k : ℕ} {ts : Fin k → ℝ} (hts : StrictMono ts) (hpos : ∀ i, 0 < ts i)
    {F : (Fin k → ℝ × ℝ) → ℝ≥0∞} (hF : Measurable F) :
    dkKillLHS P N X Y ts F = dkKillRHS D0 x y ts F := by
  induction k with
  | zero => exact dk_killed_zero hD0 hP hz ts hF
  | succ m ih =>
    have IH : ∀ F : (Fin m → ℝ × ℝ) → ℝ≥0∞, Measurable F →
        ∀ ts : Fin m → ℝ, StrictMono ts → (∀ i, 0 < ts i) →
          dkKillLHS P N X Y ts F = dkKillRHS D0 x y ts F := fun F hF ts hts hpos =>
      ih hts hpos hF
    have hinit : StrictMono (Fin.init ts) := fun i j hij => hts (Fin.castSucc_lt_castSucc_iff.2 hij)
    have hpinit : ∀ i, 0 < Fin.init ts i := fun i => hpos _
    have hlt : dkLastTime (Fin.init ts) < ts (Fin.last m) := by
      cases m with
      | zero => simpa [dkLastTime] using hpos (Fin.last 0)
      | succ n =>
        simp only [dkLastTime, ← Fin.succ_last, Fin.cons_succ, Fin.init]
        exact hts (Fin.castSucc_lt_last _)
    have e : ts = Fin.snoc (Fin.init ts) (ts (Fin.last m)) := (Fin.snoc_init_self ts).symm
    rw [e]
    exact dk_killed_succ hD0 hCH hP hz IH hinit hpinit hlt hF

end Law

/-!
### The main result
-/

/-- **The Doob killed law of the one-pair boundary dual** (`DkLbkDoobKilledLaw D0`, a copy of
`LbkDoobKilledLaw D0`), for every `D₀ > 0`, from the corner heat identity
`DkLbkCornerHeatIdentity D0`. -/
theorem dkLbkDoobKilledLaw_of {D0 : ℝ} (hD0 : 0 < D0) (hCH : DkLbkCornerHeatIdentity D0) :
    DkLbkDoobKilledLaw D0 := by
  intro x y hz Ω m 𝓖 P N X Y hP k ts hts hpos F hF
  have := hP.prob
  have hL := dk_killed_law hD0 hCH hP hz hts hpos hF
  rw [dkKillLHS, dkKillRHS] at hL
  rw [← hL]
  refine lintegral_congr_ae ?_
  filter_upwards [hP.ae_good, hP.ae_dkZf_eq] with ω hg he
  by_cases hc : ENNReal.ofReal (dkLastTime ts) < dkDualExtinction N ω
  · simp only [hc, ↓reduceIte]
    congr 1
    funext i
    have hti : ((ts i).toNNReal : ℝ≥0∞) < dkDualExtinction N ω := by
      refine lt_of_le_of_lt ?_ hc
      cases k with
      | zero => exact i.elim0
      | succ n =>
        simp only [dkLastTime, ← Fin.succ_last, Fin.cons_succ]
        exact ENNReal.ofReal_le_ofReal (hts.monotone (Fin.le_last i))
    rw [he, dkZ, dkPt_eq_of_lt hg.2 hg.1.1 hti, ContinuousLinearEquiv.apply_symm_apply]
    rfl
  · simp only [hc, ↓reduceIte]

end BlockBand.Diffusion
