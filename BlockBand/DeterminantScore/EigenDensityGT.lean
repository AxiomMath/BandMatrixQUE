module

public import BlockBand.DeterminantScore.EigenDensityWeyl
public import BlockBand.External.Prekopa.SourceStatement

/-!
# Log-concavity of `Δ I_K` through the Gelfand–Tsetlin formula and Prékopa

A finite-dimensional argument, with no Brownian-bridge discretization and no repeated-eigenvalue
limit: with `K = V diag(k) V*`, `I_K(λ) = ∫ exp(Σ_r (k_r/t)(U diag(λ) U*)_{rr}) dU`
(`hcizIntegral_eq`). By the Gelfand–Tsetlin formula (`GelfandTsetlinStatement`),
`Δ(λ) I_K(λ) = c_m ∫ 1_{GT}(λ,y) exp(Σ_r (k_r/t) d_r(λ,y)) dy`; the integrand is log-concave
jointly in `(λ, y)` (indicator of a convex polyhedron times the exponential of a linear form), so
the marginal is log-concave by Prékopa's theorem (`Prekopa.SourceContract`). This holds for every
Hermitian `K`, repeated eigenvalues included.

* `hczLogConcave_of`: `SourceContract → GelfandTsetlinStatement → HCIZLogConcaveStatement`.
* `orderedEigenDensity_of_weyl_gt`: `SourceContract → WeylIntegrationStatement →
  GelfandTsetlinStatement → OrderedEigenDensityStatement`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.EigenDensity

open MeasureTheory Matrix BlockBand.DeterminantScore.Sector
open BlockBand.QUE.Haar
open BlockBand.DeterminantScore.SpectralConvexity (weylChamber vandermonde_pos
  OrderedEigenDensityStatement)
open scoped ENNReal NNReal

variable {m : ℕ}

/-- The diagonal phase `Σ_r k_r Re(U diag(λ) U*)_{rr}`. -/
noncomputable def diagPhase (k lam : Fin m → ℝ) (U : Matrix (Fin m) (Fin m) ℂ) : ℝ :=
  ∑ r, k r * ((U * diagonal (fun i => (lam i : ℂ)) * star U) r r).re

theorem re_trace_diagonal_mul (d : Fin m → ℝ) (B : Matrix (Fin m) (Fin m) ℂ) :
    (diagonal (fun i => (d i : ℂ)) * B).trace.re = ∑ i, d i * (B i i).re := by
  simp [Matrix.trace, Matrix.diagonal_mul, Complex.re_sum]

theorem hcizPhase_eq_diagPhase (t : ℝ) {K : Matrix (Fin m) (Fin m) ℂ} (hK : K.IsHermitian)
    (U : Matrix.unitaryGroup (Fin m) ℂ) (lam : Fin m → ℝ) :
    hcizPhase t K U lam = diagPhase (fun r => hK.eigenvalues r / t) lam
      (star (hK.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ) * (U : Matrix (Fin m) (Fin m) ℂ)) := by
  set V : Matrix (Fin m) (Fin m) ℂ := (hK.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℂ)
  set W : Matrix (Fin m) (Fin m) ℂ := (U : Matrix (Fin m) (Fin m) ℂ)
  set D : Matrix (Fin m) (Fin m) ℂ := diagonal (fun i => (hK.eigenvalues i : ℂ))
  set L : Matrix (Fin m) (Fin m) ℂ := diagonal (fun i => (lam i : ℂ))
  have hKs : K = V * D * star V := BlockBand.DeterminantScore.NegativeSpread.spectral_eq hK
  have htr : (L * (Wᴴ * K * W)).trace = (D * (star V * W * L * star (star V * W))).trace := by
    rw [hKs, star_mul, star_star, Matrix.star_eq_conjTranspose]
    simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm L, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.trace_mul_comm Wᴴ, Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.trace_mul_comm V]
    simp only [Matrix.mul_assoc, Matrix.star_eq_conjTranspose]
  have h1 := re_trace_diagonal_mul lam (Wᴴ * K * W)
  have h2 := re_trace_diagonal_mul (fun i => hK.eigenvalues i) (star V * W * L * star (star V * W))
  rw [hcizPhase_apply, diagPhase]
  rw [htr] at h1
  have h3 : ∑ i, ((Wᴴ * K * W) i i).re / t * lam i = (∑ i, lam i * ((Wᴴ * K * W) i i).re) / t := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
  have h4 : ∑ r, hK.eigenvalues r / t * ((star V * W * L * star (star V * W)) r r).re =
      (∑ r, hK.eigenvalues r * ((star V * W * L * star (star V * W)) r r).re) / t := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [h3, h4, ← h1, ← h2]

/-- `I_K(λ) = ∫ exp(Σ_r (k_r/t)(U diag(λ) U*)_{rr}) dU` with `k` the eigenvalues of `K`
(spectral theorem and left invariance of Haar measure). -/
theorem hcizIntegral_eq (t : ℝ) {K : Matrix (Fin m) (Fin m) ℂ} (hK : K.IsHermitian)
    (lam : Fin m → ℝ) :
    hcizIntegral t K lam = ∫ U, Real.exp (diagPhase (fun r => hK.eigenvalues r / t) lam
      (U : Matrix (Fin m) (Fin m) ℂ)) ∂(unitaryProbability (A := Fin m)) := by
  unfold hcizIntegral
  simp_rw [hcizPhase_eq_diagPhase t hK]
  have := integral_unitary_translate (fun U : Matrix.unitaryGroup (Fin m) ℂ =>
    Real.exp (diagPhase (fun r => hK.eigenvalues r / t) lam (U : Matrix (Fin m) (Fin m) ℂ)))
    (star hK.eigenvectorUnitary)
  simpa using this

/-- Coordinates of a Gelfand–Tsetlin pattern below a top row of length `m`: rows
`r = 0, …, m-2` (zero-based), entries `i = 0, …, r`. -/
abbrev GTIndex (m : ℕ) := {p : Fin m × Fin m // p.2 ≤ p.1 ∧ p.1.val + 1 < m}

/-- Entry `(r, i)` of the pattern `z = (λ, y)`: `y` on rows `r ≤ m-2`, the top row `r = m-1` is `λ`. -/
noncomputable def gtEntry (z : (Fin m → ℝ) × (GTIndex m → ℝ)) (r i : ℕ) : ℝ :=
  if h : i ≤ r ∧ r + 1 < m then
    z.2 ⟨(⟨r, by omega⟩, ⟨i, by omega⟩), Fin.mk_le_mk.2 h.1, h.2⟩
  else if h' : r + 1 = m ∧ i < m then z.1 ⟨i, h'.2⟩ else 0

/-- Row-sum increments `d_r = Σ_{i≤r} z_{r,i} - Σ_{i<r} z_{r-1,i}`; for the corner eigenvalues of
`M = U diag(λ) U*` this is `M_{rr}`. -/
noncomputable def gtDiag (z : (Fin m → ℝ) × (GTIndex m → ℝ)) (r : Fin m) : ℝ :=
  ∑ i ∈ Finset.range (r.val + 1), gtEntry z r.val i -
    ∑ i ∈ Finset.range r.val, gtEntry z (r.val - 1) i

/-- The Gelfand–Tsetlin interlacing set `z_{r+1,i} ≤ z_{r,i} ≤ z_{r+1,i+1}`, a closed convex polyhedron
in `(λ, y)` jointly. -/
def GTSet (m : ℕ) : Set ((Fin m → ℝ) × (GTIndex m → ℝ)) :=
  {z | ∀ r i : ℕ, r + 1 < m → i ≤ r →
    gtEntry z (r + 1) i ≤ gtEntry z r i ∧ gtEntry z r i ≤ gtEntry z (r + 1) (i + 1)}

theorem gtEntry_add (a b : ℝ) (z w : (Fin m → ℝ) × (GTIndex m → ℝ)) (r i : ℕ) :
    gtEntry (a • z + b • w) r i = a * gtEntry z r i + b * gtEntry w r i := by
  unfold gtEntry
  split_ifs <;> simp

theorem gtDiag_add (a b : ℝ) (z w : (Fin m → ℝ) × (GTIndex m → ℝ)) (r : Fin m) :
    gtDiag (a • z + b • w) r = a * gtDiag z r + b * gtDiag w r := by
  simp only [gtDiag, gtEntry_add, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem convex_GTSet : Convex ℝ (GTSet m) := by
  intro z hz w hw a b ha hb hab r i hr hi
  simp only [gtEntry_add]
  obtain ⟨h1, h2⟩ := hz r i hr hi
  obtain ⟨h3, h4⟩ := hw r i hr hi
  constructor
  · exact add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h3 hb)
  · exact add_le_add (mul_le_mul_of_nonneg_left h2 ha) (mul_le_mul_of_nonneg_left h4 hb)

theorem continuous_gtEntry (r i : ℕ) : Continuous fun z : (Fin m → ℝ) × (GTIndex m → ℝ) =>
    gtEntry z r i := by
  unfold gtEntry
  split_ifs
  · exact (continuous_apply _).comp continuous_snd
  · exact (continuous_apply _).comp continuous_fst
  · exact continuous_const

theorem isClosed_GTSet : IsClosed (GTSet m) := by
  have : GTSet m = ⋂ r : ℕ, ⋂ i : ℕ, {z | r + 1 < m → i ≤ r →
      gtEntry z (r + 1) i ≤ gtEntry z r i ∧ gtEntry z r i ≤ gtEntry z (r + 1) (i + 1)} := by
    ext z; simp [GTSet]
  rw [this]
  refine isClosed_iInter fun r => isClosed_iInter fun i => ?_
  by_cases h : r + 1 < m ∧ i ≤ r
  · simp only [h.1, h.2, forall_const]
    exact (isClosed_le (continuous_gtEntry _ _) (continuous_gtEntry _ _)).inter
      (isClosed_le (continuous_gtEntry _ _) (continuous_gtEntry _ _))
  · rw [not_and_or] at h
    rcases h with h | h <;> simp [h]

/-- `1_{GT}(λ, y) exp(Σ_r k_r d_r(λ, y))`. -/
noncomputable def gtIntegrand (k : Fin m → ℝ) (z : (Fin m → ℝ) × (GTIndex m → ℝ)) : ℝ≥0∞ := by
  classical
  exact if z ∈ GTSet m then ENNReal.ofReal (Real.exp (∑ r, k r * gtDiag z r)) else 0

/-- **Gelfand–Tsetlin (Baryshnikov) formula** for the orbital integral: for `U` Haar and `λ` in
the chamber, the eigenvalues of the top-left corners of `U diag(λ) U*` are uniform on the
Gelfand–Tsetlin polytope `GT(λ)` of volume `Δ(λ)/∏_{r<m} r!`, and `(U diag(λ) U*)_{rr} = d_r`
(corner traces). Hence for every `k`,
`Δ(λ) ∫ exp(Σ_r k_r (U diag(λ) U*)_{rr}) dU = c_m ∫_{GT(λ)} exp(Σ_r k_r d_r) dy`, `c_m = ∏_{r<m} r!`.
A classical identity (Y. Baryshnikov, GUEs and queues, PTRF 119 (2001)); volume convention:
Lebesgue measure on the free entries `y` of the pattern. It is proved from the bordered-matrix law
as `gelfandTsetlin_of_border`. -/
def GelfandTsetlinStatement : Prop :=
  ∀ m : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ lam ∈ weylChamber m, ∀ k : Fin m → ℝ,
    ENNReal.ofReal (BlockBand.DeterminantScore.SpectralConvexity.vandermonde lam *
      ∫ U, Real.exp (diagPhase k lam (U : Matrix (Fin m) (Fin m) ℂ))
        ∂(unitaryProbability (A := Fin m))) =
      ENNReal.ofReal c * ∫⁻ y : GTIndex m → ℝ, gtIntegrand k (lam, y)

theorem convex_weylChamber : Convex ℝ (weylChamber m) := by
  intro x hx y hy a b ha hb hab i j hij
  have h1 := hx hij
  have h2 := hy hij
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rcases ha.lt_or_eq with ha' | ha'
  · nlinarith [mul_lt_mul_of_pos_left h1 ha', mul_le_mul_of_nonneg_left h2.le hb]
  · subst ha'
    have hb1 : b = 1 := by linarith
    subst hb1
    simpa using h2

theorem measurable_gtIntegrand (k : Fin m → ℝ) (lam : Fin m → ℝ) :
    Measurable fun y : GTIndex m → ℝ => gtIntegrand k (lam, y) := by
  have hc : Continuous fun y : GTIndex m → ℝ => ((lam, y) : (Fin m → ℝ) × (GTIndex m → ℝ)) :=
    continuous_const.prodMk continuous_id
  have hs : MeasurableSet {y : GTIndex m → ℝ | (lam, y) ∈ GTSet m} :=
    (isClosed_GTSet.preimage hc).measurableSet
  classical
  unfold gtIntegrand
  refine Measurable.ite hs ?_ measurable_const
  refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_)
  refine Finset.measurable_sum _ fun r _ => measurable_const.mul ?_
  unfold gtDiag
  refine Continuous.measurable ?_
  exact (continuous_finsetSum _ fun i _ => (continuous_gtEntry _ _).comp hc).sub
    (continuous_finsetSum _ fun i _ => (continuous_gtEntry _ _).comp hc)

theorem lintegral_completion_eq' {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {g : α → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ y : NullMeasurableSpace α μ, g y ∂μ.completion = ∫⁻ y, g y ∂μ := by
  let ι : NullMeasurableSpace α μ → α := fun y => y
  have hid : Measurable ι := fun s hs =>
    (MeasurableSet.nullMeasurableSet (μ := μ) hs : NullMeasurableSet s μ)
  have hmap : @Measure.map (NullMeasurableSpace α μ) α _ _ ι μ.completion = μ := by
    ext s hs
    rw [Measure.map_apply hid hs]
    rfl
  conv_rhs => rw [← hmap]
  rw [lintegral_map hg hid]

/-- **Log-concavity of the marginal**: `λ ↦ ∫ 1_{GT}(λ,y) e^{Σ k_r d_r} dy` is log-concave on `ℝ^m`
(Prékopa's theorem, jointly log-concave integrand on a convex polyhedron). -/
theorem logConcave_gtMarginal (hP : BlockBand.External.Prekopa.SourceContract)
    (k : Fin m → ℝ) :
    BlockBand.External.Prekopa.LogConcave fun lam : Fin m → ℝ =>
      ∫⁻ y : GTIndex m → ℝ, gtIntegrand k (lam, y) := by
  classical
  set N := Fintype.card (GTIndex m)
  let e : GTIndex m ≃ Fin N := Fintype.equivFin _
  let T : (Fin N → ℝ) → (GTIndex m → ℝ) := fun y i => y (e i)
  have hT : ∀ (z w : (Fin m → ℝ) × (Fin N → ℝ)) (a b : ℝ),
      ((a • z + b • w).1, T (a • z + b • w).2) = a • (z.1, T z.2) + b • (w.1, T w.2) := by
    intro z w a b; rfl
  set F : (Fin m → ℝ) × (Fin N → ℝ) → ℝ≥0 := fun z =>
    if (z.1, T z.2) ∈ GTSet m then
      Real.toNNReal (Real.exp (∑ r, k r * gtDiag (z.1, T z.2) r)) else 0 with hFdef
  have hFcoe : ∀ z, (F z : ℝ≥0∞) = gtIntegrand k (z.1, T z.2) := by
    intro z
    simp only [hFdef, gtIntegrand]
    split_ifs <;> rfl
  have hF : BlockBand.External.Prekopa.JointLogConcave m N F := by
    intro z w a ha ha1
    have hb : 0 < 1 - a := by linarith
    simp only [hFcoe, gtIntegrand]
    by_cases hz : (z.1, T z.2) ∈ GTSet m
    · by_cases hw : (w.1, T w.2) ∈ GTSet m
      · have hc : ((a • z + (1 - a) • w).1, T (a • z + (1 - a) • w).2) ∈ GTSet m := by
          rw [hT]; exact convex_GTSet hz hw ha.le hb.le (by ring)
        rw [ite_eq_left hz, ite_eq_left hw, ite_eq_left hc,
          ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le ha.le,
          ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hb.le,
          ← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add, hT]
        simp only [gtDiag_add]
        apply le_of_eq
        congr 1
        rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun r _ => by ring
      · rw [ite_eq_right hw, ENNReal.zero_rpow_of_pos hb, mul_zero]
        exact bot_le
    · rw [ite_eq_right hz, ENNReal.zero_rpow_of_pos ha, zero_mul]
      exact bot_le
  have hLC := hP.theorem6 m N F Set.univ hF convex_univ
  have hmarg : ∀ lam, BlockBand.External.Prekopa.marginal F Set.univ lam =
      ∫⁻ y : GTIndex m → ℝ, gtIntegrand k (lam, y) := by
    intro lam
    unfold BlockBand.External.Prekopa.marginal
    have hu : ∀ y : NullMeasurableSpace (Fin N → ℝ) (volume : Measure (Fin N → ℝ)),
        (if y ∈ (Set.univ : Set (Fin N → ℝ)) then (F (lam, y) : ℝ≥0∞) else 0) = F (lam, y) :=
      fun y => ite_eq_left trivial
    refine (lintegral_congr hu).trans ?_
    have hTm : Measurable T := measurable_pi_iff.2 fun i => measurable_pi_apply _
    have hFm : Measurable fun y : Fin N → ℝ => (F (lam, y) : ℝ≥0∞) := by
      simp only [hFcoe]
      exact (measurable_gtIntegrand k lam).comp hTm
    refine (lintegral_completion_eq' (volume : Measure (Fin N → ℝ)) hFm).trans ?_
    simp only [hFcoe]
    have hmp := MeasureTheory.volume_measurePreserving_piCongrLeft (fun _ : Fin N => ℝ) e
    rw [← hmp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
    refine lintegral_congr fun y => ?_
    congr 2
    funext i
    simp [T, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  intro x y a ha ha1
  have := hLC x y a ha ha1
  simp only [hmarg] at this
  exact this

/-- **`HCIZLogConcaveStatement` from the Gelfand–Tsetlin formula and Prékopa** (covers repeated
eigenvalues of `K` directly, no limit needed). -/
theorem hczLogConcave_of (hP : BlockBand.External.Prekopa.SourceContract)
    (hG : GelfandTsetlinStatement) : HCIZLogConcaveStatement := by
  intro m t K ht hK
  obtain ⟨c, hc, hrep⟩ := hG m
  set k : Fin m → ℝ := fun r => hK.eigenvalues r / t
  set Φ : (Fin m → ℝ) → ℝ≥0∞ := fun lam => ∫⁻ y : GTIndex m → ℝ, gtIntegrand k (lam, y)
  set p : (Fin m → ℝ) → ℝ := fun lam =>
    BlockBand.DeterminantScore.SpectralConvexity.vandermonde lam * hcizIntegral t K lam with hp
  have hppos : ∀ lam ∈ weylChamber m, 0 < p lam := fun lam hlam =>
    mul_pos (vandermonde_pos hlam) (hcizIntegral_pos _ _ _)
  have hΦ : ∀ lam ∈ weylChamber m, ENNReal.ofReal (p lam) = ENNReal.ofReal c * Φ lam := by
    intro lam hlam
    simp only [hp]
    rw [hcizIntegral_eq t hK]
    exact hrep lam hlam k
  have hLC := logConcave_gtMarginal hP k
  refine ⟨convex_weylChamber, fun x hx y hy a b ha hb hab => ?_⟩
  have hz := convex_weylChamber hx hy ha hb hab
  simp only [smul_eq_mul]
  rcases ha.lt_or_eq with ha' | ha'
  · rcases hb.lt_or_eq with hb' | hb'
    · have hb1 : b = 1 - a := by linarith
      subst hb1
      have ha1 : a < 1 := by linarith
      have h1 := hLC x y a ha' ha1
      have hc0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.2 hc).ne'
      have hcT : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
      have h2 : (ENNReal.ofReal c * Φ x) ^ a * (ENNReal.ofReal c * Φ y) ^ (1 - a) ≤
          ENNReal.ofReal c * Φ (a • x + (1 - a) • y) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ ha'.le, ENNReal.mul_rpow_of_nonneg _ _ hb'.le]
        calc ENNReal.ofReal c ^ a * Φ x ^ a * (ENNReal.ofReal c ^ (1 - a) * Φ y ^ (1 - a))
            = (ENNReal.ofReal c ^ a * ENNReal.ofReal c ^ (1 - a)) * (Φ x ^ a * Φ y ^ (1 - a)) := by
              ring
          _ = ENNReal.ofReal c * (Φ x ^ a * Φ y ^ (1 - a)) := by
              rw [← ENNReal.rpow_add _ _ hc0 hcT, add_sub_cancel, ENNReal.rpow_one]
          _ ≤ ENNReal.ofReal c * Φ (a • x + (1 - a) • y) := by gcongr
      rw [← hΦ x hx, ← hΦ y hy, ← hΦ _ hz,
        ENNReal.ofReal_rpow_of_nonneg (hppos x hx).le ha'.le,
        ENNReal.ofReal_rpow_of_nonneg (hppos y hy).le hb'.le,
        ← ENNReal.ofReal_mul (by have := hppos x hx; positivity),
        ENNReal.ofReal_le_ofReal_iff (hppos _ hz).le] at h2
      have h3 := Real.log_le_log (by have := hppos x hx; have := hppos y hy; positivity) h2
      have hx1 : 0 < p x ^ a := Real.rpow_pos_of_pos (hppos x hx) a
      have hy1 : 0 < p y ^ (1 - a) := Real.rpow_pos_of_pos (hppos y hy) (1 - a)
      rw [Real.log_mul hx1.ne' hy1.ne', Real.log_rpow (hppos x hx),
        Real.log_rpow (hppos y hy)] at h3
      simp only [p] at h3 ⊢
      linarith
    · subst hb'
      have : a = 1 := by linarith
      subst this
      simp
  · subst ha'
    have : b = 1 := by linarith
    subst this
    simp

/-- **`OrderedEigenDensityStatement`** (the eigenvalue density of `K + G_m(t)`) from the Weyl
integration formula, the Gelfand–Tsetlin formula and Prékopa's theorem. -/
theorem orderedEigenDensity_of_weyl_gt (hP : BlockBand.External.Prekopa.SourceContract)
    (hW : WeylIntegrationStatement) (hG : GelfandTsetlinStatement) :
    OrderedEigenDensityStatement :=
  orderedEigenDensity_of (weylHCIZDensity_of hW) (hczLogConcave_of hP hG)

end BlockBand.DeterminantScore.EigenDensity
