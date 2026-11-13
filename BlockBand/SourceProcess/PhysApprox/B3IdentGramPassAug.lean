module

public import BlockBand.SourceProcess.PhysApprox.B3IdentGramPassStop
public import BlockBand.SourceProcess.PhysApprox.B3IdentGramAddFun

/-!
# The augmented observables of a generator process

No measure appears except in `fddConvOff_freeze`. The observables are indexed as `complexObs`
(`LIdx K np`); a Gram process `G` *reads* observables `X` if `X (Sum.inl e) u ω = G_e(u, ω)`.

* `exists_lamA_bound`, `exists_lam_bound`: on feasible states the cut drift integrand and a
  generator are bounded (compact boxes).
* The two layers of `augProc`: `a1` (the clamped cut drift integrand, first layer:
  `A^χ_e`) and `a2` (the clamped generator, second layer: `∫ Λ`); `X3` the augmented
  observables; `zOf` reads the state `(Y_t, x(t), Y_0)` off the augmented vector.
* **`X2_A_eq`**, **`zOf_X2_eq`**: along a feasible path, the first augmentation gives the cut
  drift integral `genA`, and `zOf` reads off the state `stZ` (the clamps are inactive).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Pass

open MeasureTheory ProbabilityTheory Filter Topology Matrix Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open BlockBand.SourceProcess.PhysApprox.B3.Ident2
open scoped NNReal ENNReal

variable {K np : ℕ}

/-!
## Clamping
-/

/-- Clamp the real and imaginary parts to `[-L, L]`. -/
def clampC (L : ℝ) (w : ℂ) : ℂ :=
  (max (-L) (min L w.re) : ℝ) + (max (-L) (min L w.im) : ℝ) * Complex.I

@[fun_prop] theorem continuous_clampC (L : ℝ) : Continuous (clampC L) := by
  unfold clampC; fun_prop

theorem clampC_eq {L : ℝ} {w : ℂ} (h : ‖w‖ ≤ L) : clampC L w = w := by
  have h1 := abs_le.1 ((Complex.abs_re_le_norm w).trans h)
  have h2 := abs_le.1 ((Complex.abs_im_le_norm w).trans h)
  have e1 : max (-L) (min L w.re) = w.re := by rw [min_eq_right h1.2, max_eq_right h1.1]
  have e2 : max (-L) (min L w.im) = w.im := by rw [min_eq_right h2.2, max_eq_right h2.1]
  rw [clampC, e1, e2, Complex.re_add_im]

theorem norm_clampC_le {L : ℝ} (hL : 0 ≤ L) (w : ℂ) : ‖clampC L w‖ ≤ 2 * L := by
  have hb : ∀ x : ℝ, |max (-L) (min L x)| ≤ L := fun x =>
    abs_le.2 ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  unfold clampC
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs]
  linarith [hb w.re, hb w.im]

/-!
## Time-`0` observables held constant
-/

/-- The observables `X` with the observables `X (j0 k)` held at their time-`0` value adjoined. -/
def freeze {I J : Type*} {Ω : Type*} (j0 : J → I) (X : I → ℝ≥0 → Ω → ℂ) :
    I ⊕ J → ℝ≥0 → Ω → ℂ
  | Sum.inl i => X i
  | Sum.inr k => fun _ ω => X (j0 k) 0 ω

theorem fddConvOff_freeze {I J : Type*} {B : Set ℝ≥0} (h0 : (0 : ℝ≥0) ∉ B) (j0 : J → I)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {μ : (n : ℕ) → Measure (Ω n)}
    {X : (n : ℕ) → I → ℝ≥0 → Ω n → ℂ} {Ω' : Type*} [MeasurableSpace Ω'] {Q : Measure Ω'}
    {Y : I → ℝ≥0 → Ω' → ℂ} (hF : AddFun.FddConvOff B μ X Q Y) :
    AddFun.FddConvOff B μ (fun n => freeze j0 (X n)) Q (freeze j0 Y) := by
  intro ι _ i u hu ψ
  let i' : ι → I := fun l => Sum.elim id j0 (i l)
  let u' : ι → ℝ≥0 := fun l => Sum.elim (fun _ => u l) (fun _ => 0) (i l)
  have hu' : ∀ l, u' l ∉ B := fun l => by
    simp only [u']
    rcases i l with a | k
    · exact hu l
    · exact h0
  have eX : ∀ n (ω : Ω n) (l : ι), freeze j0 (X n) (i l) (u l) ω = X n (i' l) (u' l) ω := by
    intro n ω l
    simp only [i', u']
    rcases i l with a | k <;> rfl
  have eY : ∀ (ω : Ω') (l : ι), freeze j0 Y (i l) (u l) ω = Y (i' l) (u' l) ω := by
    intro ω l
    simp only [i', u']
    rcases i l with a | k <;> rfl
  have hl : (∫ ω, ψ (fun l => Y (i' l) (u' l) ω) ∂Q) =
      ∫ ω, ψ (fun l => freeze j0 Y (i l) (u l) ω) ∂Q := by
    congr 1; funext ω; congr 1; funext l; exact (eY ω l).symm
  rw [← hl]
  refine (hF ι i' u' hu' ψ).congr fun n => ?_
  congr 1; funext ω; congr 1; funext l; exact (eX n ω l).symm

theorem measurable_uncurry_freeze {I J : Type*} {Ω : Type*} [MeasurableSpace Ω] (j0 : J → I)
    {X : I → ℝ≥0 → Ω → ℂ} (hX : ∀ i, Measurable (Function.uncurry (X i))) :
    ∀ q, Measurable (Function.uncurry (freeze j0 X q))
  | Sum.inl i => hX i
  | Sum.inr k => (hX (j0 k)).comp (measurable_const.prodMk measurable_snd)

/-!
## Bounds on feasible states
-/

section Bounds

variable {b E s : ℝ} {τ m : Fin np → ℝ} {χ : ℝ → ℝ} (hχ : Continuous χ) {Rχ : ℝ}
  (hR : ∀ c, Rχ < |c| → χ c = 0 ∧ deriv χ c = 0 ∧ deriv (deriv χ) c = 0)
include hχ hR

omit hR in
theorem continuous_lamA (e : GIdx K np) : Continuous (lamA (K := K) (np := np) χ b E e) :=
  ((continuous_drE b E e).comp (continuous_snd.add continuous_fst)).mul
    ((continuous_cutC hχ).comp continuous_snd)

/-- **The cut drift integrand is bounded on feasible states.** -/
theorem exists_lamA_bound :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (e : GIdx K np) (t : ℝ≥0) (H : GSt K np),
      GramFeasible (srcSignature K (Fin np)) H →
        ‖lamA χ b E e (gramJ b s τ m t, H - gramJ b s τ m t)‖ ≤ L := by
  obtain ⟨CJ, hCJ⟩ := exists_norm_gramJ_le (K := K) b s τ m
  set BY := 2 * (Rχ + (Fintype.card (SrcCol K (Fin np)) : ℝ) * CJ) + CJ
  have hbox : IsCompact {y : GSt K np | ∀ e : GIdx K np, ‖gramEntry e y‖ ≤ BY} := isCompact_box BY
  have hAc : ∀ e : GIdx K np, ∃ C : ℝ, ∀ J ∈ Set.range (fun t : ℝ≥0 => gramJ (K := K) b s τ m t),
      ∀ y ∈ {y : GSt K np | ∀ e : GIdx K np, ‖gramEntry e y‖ ≤ BY},
        ‖lamA χ b E e (J, y)‖ ≤ C := fun e =>
    exists_bound_finite_compact (continuous_lamA hχ e) (finite_range_gramJ b s τ m) hbox
  choose CAf hCAf using hAc
  have hCA0 : 0 ≤ ∑ e : GIdx K np, |CAf e| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨∑ e : GIdx K np, |CAf e|, hCA0, fun e t H hH => ?_⟩
  by_cases h0 : lamA χ b E e (gramJ b s τ m t, H - gramJ b s τ m t) = 0
  · rw [h0, norm_zero]; exact hCA0
  · have hy : H - gramJ b s τ m t ∈ {y : GSt K np | ∀ e : GIdx K np, ‖gramEntry e y‖ ≤ BY} :=
      fun e' => entry_sub_le_of_feasible hH (hCJ t) (abs_trRe_gramJ_le hCJ t)
        (lamA_ne_zero hR b E e h0) e'
    exact (hCAf e _ ⟨t, rfl⟩ _ hy).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun e => |CAf e|) (fun _ _ => abs_nonneg _) (Finset.mem_univ e)))

omit hχ hR in
/-- **A generator is bounded on feasible states with a bounded drift coordinate.** -/
theorem exists_lam_bound {Λ : GSt K np × ZSt K np → ℂ} (hΛ : Continuous Λ)
    (hΛv : ∀ p, Λ p ≠ 0 → |trRe p.2.1| ≤ Rχ ∧ |trRe p.2.2.2| ≤ Rχ) (HA : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (t : ℝ≥0) (Gt G0 : GSt K np) (A : GIdx K np → ℂ),
      GramFeasible (srcSignature K (Fin np)) Gt → GramFeasible (srcSignature K (Fin np)) G0 →
      (∀ e, ‖A e‖ ≤ HA) →
        ‖Λ (gramJ b s τ m t, (Gt - gramJ b s τ m t, fun e => gramEntry e (Gt - gramJ b s τ m t) -
          gramEntry e (G0 - gramJ b s τ m 0) - A e, G0 - gramJ b s τ m 0))‖ ≤ L := by
  obtain ⟨CJ, hCJ⟩ := exists_norm_gramJ_le (K := K) b s τ m
  set BY := 2 * (Rχ + (Fintype.card (SrcCol K (Fin np)) : ℝ) * CJ) + CJ
  set box := {y : GSt K np | ∀ e : GIdx K np, ‖gramEntry e y‖ ≤ BY}
  have hbox : IsCompact box := isCompact_box BY
  set Kreg : Set (ZSt K np) :=
    box ×ˢ (Set.pi univ fun _ => Metric.closedBall (0 : ℂ) (BY + BY + HA)) ×ˢ box
  have hKreg : IsCompact Kreg :=
    hbox.prod ((isCompact_univ_pi fun _ => isCompact_closedBall _ _).prod hbox)
  obtain ⟨C1, hC1⟩ := exists_bound_finite_compact hΛ (finite_range_gramJ (K := K) b s τ m) hKreg
  refine ⟨max C1 0, le_max_right _ _, fun t Gt G0 A hGt hG0 hA => ?_⟩
  set p : GSt K np × ZSt K np := (gramJ b s τ m t, (Gt - gramJ b s τ m t,
    fun e => gramEntry e (Gt - gramJ b s τ m t) - gramEntry e (G0 - gramJ b s τ m 0) - A e,
    G0 - gramJ b s τ m 0))
  by_cases h0 : Λ p = 0
  · rw [h0, norm_zero]; exact le_max_right _ _
  · obtain ⟨h1, h2⟩ := hΛv p h0
    have hY : Gt - gramJ b s τ m t ∈ box := fun e =>
      entry_sub_le_of_feasible hGt (hCJ t) (abs_trRe_gramJ_le hCJ t) h1 e
    have hY0 : G0 - gramJ b s τ m 0 ∈ box := fun e =>
      entry_sub_le_of_feasible hG0 (hCJ 0) (abs_trRe_gramJ_le hCJ 0) h2 e
    have hz : p.2 ∈ Kreg := by
      refine ⟨hY, fun e _ => ?_, hY0⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
        (add_le_add (hY e) (hY0 e))) (hA e))
    exact (hC1 _ ⟨t, rfl⟩ _ hz).trans (le_max_left _ _)

end Bounds

/-!
## The augmented observables
-/

/-- First layer: the clamped cut drift integrand of the Gram observables at `r`. -/
def a1 (χ : ℝ → ℝ) (b E s : ℝ) (τ m : Fin np → ℝ) (LA : ℝ) :
    GIdx K np → ℝ≥0 → (GIdx K np → ℂ) → ℂ :=
  fun e r x => clampC LA (lamA χ b E e (gramJ b s τ m r, gramOfEntries x - gramJ b s τ m r))

/-- The Gram observables, the inputs of the first layer. -/
def j1 : GIdx K np → LIdx K np ⊕ GIdx K np := fun e => Sum.inl (Sum.inl e)

/-- The inputs of the second layer: Gram observables at `r`, held at `0`, and `A^χ` at `r`. -/
def j2 : GIdx K np ⊕ GIdx K np ⊕ GIdx K np → (LIdx K np ⊕ GIdx K np) ⊕ GIdx K np
  | Sum.inl e => Sum.inl (Sum.inl (Sum.inl e))
  | Sum.inr (Sum.inl e) => Sum.inl (Sum.inr e)
  | Sum.inr (Sum.inr e) => Sum.inr e

/-- The state `(Y_r, x(r), Y_0)` read off the second-layer inputs. -/
def zOf (b s : ℝ) (τ m : Fin np → ℝ) (r : ℝ≥0) (x : GIdx K np ⊕ GIdx K np ⊕ GIdx K np → ℂ) :
    ZSt K np :=
  (gramOfEntries (fun e => x (Sum.inl e)) - gramJ b s τ m r,
    fun e => gramEntry e (gramOfEntries (fun e => x (Sum.inl e)) - gramJ b s τ m r) -
      gramEntry e (gramOfEntries (fun e => x (Sum.inr (Sum.inl e))) - gramJ b s τ m 0) -
        x (Sum.inr (Sum.inr e)),
    gramOfEntries (fun e => x (Sum.inr (Sum.inl e))) - gramJ b s τ m 0)

@[fun_prop] theorem continuous_zOf (b s : ℝ) (τ m : Fin np → ℝ) (r : ℝ≥0) :
    Continuous (zOf (K := K) b s τ m r) := by
  have hG : Continuous fun x : GIdx K np ⊕ GIdx K np ⊕ GIdx K np → ℂ =>
      gramOfEntries (fun e => x (Sum.inl e)) :=
    continuous_gramOfEntries.comp (continuous_pi fun e => continuous_apply _)
  have h0 : Continuous fun x : GIdx K np ⊕ GIdx K np ⊕ GIdx K np → ℂ =>
      gramOfEntries (fun e => x (Sum.inr (Sum.inl e))) :=
    continuous_gramOfEntries.comp (continuous_pi fun e => continuous_apply _)
  refine (hG.sub continuous_const).prodMk ((continuous_pi fun e => ?_).prodMk
    (h0.sub continuous_const))
  exact (((ClosedLimit.continuous_gramEntry e).comp (hG.sub continuous_const)).sub
    ((ClosedLimit.continuous_gramEntry e).comp (h0.sub continuous_const))).sub
    (continuous_apply _)

/-- Second layer: the clamped generator of the state read off the inputs. -/
def a2 (Λ : GSt K np × ZSt K np → ℂ) (b s : ℝ) (τ m : Fin np → ℝ) (LL : ℝ) :
    Unit → ℝ≥0 → (GIdx K np ⊕ GIdx K np ⊕ GIdx K np → ℂ) → ℂ :=
  fun _ r x => clampC LL (Λ (gramJ b s τ m r, zOf b s τ m r x))

/-- The first augmentation: observables, time-`0` Gram observables and `A^χ`. -/
def X2 (χ : ℝ → ℝ) (b E s : ℝ) (τ m : Fin np → ℝ) (LA : ℝ) {Ω : Type*}
    (X : LIdx K np → ℝ≥0 → Ω → ℂ) : (LIdx K np ⊕ GIdx K np) ⊕ GIdx K np → ℝ≥0 → Ω → ℂ :=
  AddFun.augProc (a1 χ b E s τ m LA) j1 (freeze (fun e => Sum.inl e) X)

/-- The second augmentation: with the integral of the generator. -/
def X3 (χ : ℝ → ℝ) (b E s : ℝ) (τ m : Fin np → ℝ) (LA : ℝ) (Λ : GSt K np × ZSt K np → ℂ)
    (LL : ℝ) {Ω : Type*} (X : LIdx K np → ℝ≥0 → Ω → ℂ) :
    ((LIdx K np ⊕ GIdx K np) ⊕ GIdx K np) ⊕ Unit → ℝ≥0 → Ω → ℂ :=
  AddFun.augProc (a2 Λ b s τ m LL) j2 (X2 χ b E s τ m LA X)

/-!
## Identification along a feasible path
-/

section Ident

variable {Ω : Type*} {b E s : ℝ} {τ m : Fin np → ℝ} {χ : ℝ → ℝ} {LA : ℝ}
  {X : LIdx K np → ℝ≥0 → Ω → ℂ} {G : ℝ≥0 → Ω → GSt K np}
  (hXG : ∀ e u ω, X (Sum.inl e) u ω = gramEntry e (G u ω)) {ω : Ω}
  (hfe : ∀ u, GramFeasible (srcSignature K (Fin np)) (G u ω))
  (hLA : ∀ (e : GIdx K np) (t : ℝ≥0) (H : GSt K np), GramFeasible (srcSignature K (Fin np)) H →
    ‖lamA χ b E e (gramJ b s τ m t, H - gramJ b s τ m t)‖ ≤ LA)
include hXG

omit hXG in
theorem gramOfEntries_read (hXG : ∀ e u ω, X (Sum.inl e) u ω = gramEntry e (G u ω)) (u : ℝ≥0)
    (ω : Ω) : gramOfEntries (fun e => X (Sum.inl e) u ω) = G u ω := by
  simp only [hXG]; exact gramOfEntries_entries _

include hfe hLA in
theorem X2_A_eq (e : GIdx K np) (t : ℝ≥0) :
    X2 χ b E s τ m LA X (Sum.inr e) t ω = genA χ b E s τ m G e t ω := by
  simp only [X2, AddFun.augProc, AddFun.addFun, genA]
  refine setIntegral_congr_fun measurableSet_Ioc fun r _ => ?_
  simp only [a1, j1, freeze]
  rw [gramOfEntries_read hXG, clampC_eq (hLA e _ _ (hfe _))]
  rfl

include hfe hLA in
theorem zOf_X2_eq (t : ℝ≥0) :
    zOf b s τ m t (fun k => X2 χ b E s τ m LA X (j2 k) t ω) = stZ χ b E s τ m G t ω := by
  have e1 : (fun e => X2 χ b E s τ m LA X (j2 (Sum.inl e)) t ω) = fun e => X (Sum.inl e) t ω :=
    rfl
  have e2 : (fun e => X2 χ b E s τ m LA X (j2 (Sum.inr (Sum.inl e))) t ω) =
      fun e => X (Sum.inl e) 0 ω := rfl
  simp only [zOf, e1, e2, gramOfEntries_read hXG]
  simp only [j2, X2_A_eq hXG hfe hLA]
  rfl

end Ident

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Pass
