module

public import BlockBand.SourceProcess.FullSourceGenerator.LimVersion

/-!
# Martingale increments against unbounded continuous cylinder tests

If a process has martingale increments against bounded continuous cylinder tests, then by
truncation the same holds for continuous square-integrable cylinder tests, in particular for the
tests `φ(past)·Ψ(Z_s)` of the ordinary words (`slot_test_zero`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceGenerator.GenLim

open MeasureTheory Filter Topology MvPolynomial
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Transmission.Generator
open scoped ENNReal

theorem abs_clamp_le {N : ℝ} (hN : 0 ≤ N) (x : ℝ) : |max (-N) (min N x)| ≤ |x| := by
  rw [abs_le]
  constructor
  · exact le_max_of_le_right (le_min (by linarith [abs_nonneg x]) (neg_abs_le x))
  · exact max_le (by linarith [abs_nonneg x]) ((min_le_right _ _).trans (le_abs_self x))

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {I : Type*}
  {obs : I → ℝ → Ω → ℂ} {D : Set ℝ} {inc : ℝ → ℝ → Ω → ℂ}

/-- **Martingale increments against a real continuous `L²` cylinder test** (truncation). -/
theorem integral_real_mul_eq_zero (hM : IsMartingaleIncrements P obs D inc) {s t : ℝ}
    (hs : s ∈ D) (ht : t ∈ D) (hst : s ≤ t) (hinc : MemLp (inc s t) 2 P) {m : ℕ}
    (i : Fin m → I) (u : Fin m → ℝ) (hu : ∀ l, u l ∈ D ∧ u l ≤ s)
    (hobs : Measurable fun ω => fun l => obs (i l) (u l) ω) {g : (Fin m → ℂ) → ℝ}
    (hg : Continuous g) (hg2 : MemLp (fun ω => ((g (fun l => obs (i l) (u l) ω) : ℝ) : ℂ)) 2 P) :
    ∫ ω, ((g (fun l => obs (i l) (u l) ω) : ℝ) : ℂ) * inc s t ω ∂P = 0 := by
  set Y : Ω → Fin m → ℂ := fun ω l => obs (i l) (u l) ω
  have hzero : ∀ N : ℕ, ∫ ω, ((clampBCF g hg N (Y ω) : ℝ) : ℂ) * inc s t ω ∂P = 0 :=
    fun N => by
      have := (hM s t hs ht hst).2 m i u hu (clampBCF g hg N)
      simpa only [Complex.real_smul] using this
  have hb := (integrable_mul_of_memLp hg2 hinc).norm
  have hlim := tendsto_integral_of_dominated_convergence
    (F := fun N : ℕ => fun ω => ((clampBCF g hg N (Y ω) : ℝ) : ℂ) * inc s t ω) _
    (fun N => ((Complex.measurable_ofReal.comp
      ((clampBCF g hg N).continuous.measurable.comp hobs)).aestronglyMeasurable).mul
        hinc.aestronglyMeasurable) hb
    (fun N => Eventually.of_forall fun ω => by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, clampBCF_apply]
      exact mul_le_mul_of_nonneg_right (abs_clamp_le (Nat.cast_nonneg N) _) (norm_nonneg _))
    (Eventually.of_forall fun ω => by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈|g (Y ω)|⌉₊] with N hN
      have hN' : |g (Y ω)| ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN)
      rw [clampBCF_apply, min_eq_right (le_of_abs_le hN'),
        max_eq_right (neg_le_of_abs_le hN')])
  exact tendsto_nhds_unique hlim (by simp only [hzero]; exact tendsto_const_nhds)

/-- **Martingale increments against a complex continuous `L²` cylinder test.** -/
theorem integral_mul_eq_zero_of_memLp (hM : IsMartingaleIncrements P obs D inc) {s t : ℝ}
    (hs : s ∈ D) (ht : t ∈ D) (hst : s ≤ t) (hinc : MemLp (inc s t) 2 P) {m : ℕ}
    (i : Fin m → I) (u : Fin m → ℝ) (hu : ∀ l, u l ∈ D ∧ u l ≤ s)
    (hobs : Measurable fun ω => fun l => obs (i l) (u l) ω) {G : (Fin m → ℂ) → ℂ}
    (hG : Continuous G) (hG2 : MemLp (fun ω => G (fun l => obs (i l) (u l) ω)) 2 P) :
    ∫ ω, G (fun l => obs (i l) (u l) ω) * inc s t ω ∂P = 0 := by
  set Y : Ω → Fin m → ℂ := fun ω l => obs (i l) (u l) ω
  have hGm : Measurable fun ω => G (Y ω) := hG.measurable.comp hobs
  have hre : MemLp (fun ω => (((G (Y ω)).re : ℝ) : ℂ)) 2 P :=
    hG2.of_le (Complex.measurable_ofReal.comp (Complex.measurable_re.comp hGm)).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact Complex.abs_re_le_norm _)
  have him : MemLp (fun ω => (((G (Y ω)).im : ℝ) : ℂ)) 2 P :=
    hG2.of_le (Complex.measurable_ofReal.comp (Complex.measurable_im.comp hGm)).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact Complex.abs_im_le_norm _)
  have h1 := integral_real_mul_eq_zero hM hs ht hst hinc i u hu hobs
    (Complex.continuous_re.comp hG) hre
  have h2 := integral_real_mul_eq_zero hM hs ht hst hinc i u hu hobs
    (Complex.continuous_im.comp hG) him
  have e : ∀ ω, G (Y ω) * inc s t ω = (((G (Y ω)).re : ℝ) : ℂ) * inc s t ω +
      Complex.I * ((((G (Y ω)).im : ℝ) : ℂ) * inc s t ω) := fun ω => by
    conv_lhs => rw [← Complex.re_add_im (G (Y ω))]
    ring
  rw [integral_congr_ae (Eventually.of_forall e), integral_add (integrable_mul_of_memLp hre hinc)
    ((integrable_mul_of_memLp him hinc).const_mul _), integral_const_mul]
  simp only [Function.comp] at h1 h2
  rw [h1, h2]; ring

variable {nT nI : ℕ} {Z : TraceWord nT nI → ℝ → Ω → ℂ} {t₀ : ℝ}

/-- **The test `φ(past)·Ψ(Z_s)`** for martingale increments of the ordinary words. -/
theorem slot_test_zero (hm : ∀ w, IsOrdinaryWord w → ∀ t, t₀ ≤ t → Measurable (Z w t))
    (hM : IsMartingaleIncrements P (fun w : {w : TraceWord nT nI // IsOrdinaryWord w} => Z w.1)
      (Set.Ici t₀) inc) {s t : ℝ} (hs : t₀ ≤ s) (hst : s ≤ t) (hinc : MemLp (inc s t) 2 P)
    {Ψ : TracePoly nT nI} (hΨ : IsOrdinaryPoly Ψ)
    (h2 : MemLp (fun ω => eval (fun w => Z w s ω) Ψ) 2 P) {m : ℕ}
    {ws : Fin m → TraceWord nT nI} {us : Fin m → ℝ} (hws : ∀ l, IsOrdinaryWord (ws l) ∧ t₀ ≤ us l)
    (hus : ∀ l, us l ≤ s) (φ : BoundedContinuousFunction (Fin m → ℂ) ℝ) :
    ∫ ω, ((φ (fun l => Z (ws l) (us l) ω) : ℝ) : ℂ) * eval (fun w => Z w s ω) Ψ * inc s t ω ∂P
      = 0 := by
  have hsl := slot_ord hws hΨ hs
  set e := Fintype.equivFin (Fin m ⊕ Ψ.vars)
  set i' : Fin (Fintype.card (Fin m ⊕ Ψ.vars)) → {w : TraceWord nT nI // IsOrdinaryWord w} :=
    fun j => ⟨slotW ws Ψ (e.symm j), (hsl (e.symm j)).1⟩
  set u' : Fin (Fintype.card (Fin m ⊕ Ψ.vars)) → ℝ := fun j => slotT us Ψ s (e.symm j)
  have hu' : ∀ j, u' j ∈ Set.Ici t₀ ∧ u' j ≤ s := fun j => by
    refine ⟨(hsl (e.symm j)).2, ?_⟩
    simp only [u']
    rcases e.symm j with l | w
    · exact hus l
    · exact le_rfl
  set G : (Fin (Fintype.card (Fin m ⊕ Ψ.vars)) → ℂ) → ℂ := fun y => slotG φ Ψ fun i => y (e i)
  have hG : Continuous G := (continuous_slotG φ Ψ).comp (continuous_pi fun i => continuous_apply _)
  have hGv : ∀ ω, G (fun j => Z (i' j).1 (u' j) ω) =
      ((φ (fun l => Z (ws l) (us l) ω) : ℝ) : ℂ) * eval (fun w => Z w s ω) Ψ := fun ω => by
    simp only [G, i', u', Equiv.symm_apply_apply]
    exact slotG_apply φ Ψ ws us s (fun w τ => Z w τ ω)
  have hobs : Measurable fun ω => fun j => Z (i' j).1 (u' j) ω :=
    measurable_pi_iff.mpr fun j => hm _ (i' j).2 _ (hu' j).1
  have hG2 : MemLp (fun ω => G (fun j => Z (i' j).1 (u' j) ω)) 2 P := by
    refine (h2.const_mul (‖φ‖ : ℂ)).of_le (hG.measurable.comp hobs).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    rw [hGv, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg
      (norm_nonneg φ)]
    exact mul_le_mul_of_nonneg_right (φ.norm_coe_le_norm _) (norm_nonneg _)
  have := integral_mul_eq_zero_of_memLp hM (Set.mem_Ici.mpr hs) (Set.mem_Ici.mpr (hs.trans hst))
    hst hinc i' u' hu' hobs hG hG2
  simpa only [hGv] using this

end BlockBand.SourceProcess.FullSourceGenerator.GenLim
