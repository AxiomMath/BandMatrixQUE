module

public import BlockBand.SourceProcess.PhysApprox.IdentK.FiniteWCond
public import BlockBand.SourceProcess.PhysApprox.B3ModulAdapt
public import BlockBand.SourceProcess.CapLaw.Coords

/-!
# Adaptedness, Hermitian symmetry, the discrete state

* `measurable_physTseq_past`: the entrance coordinates `physTseq … k` (observable
  index `inr (inl k)`) are `b3Sigma W n_s`-measurable (`n_s = closeLen s W`, any `j ≥ n_s`).
  `physTseq` is `selT V` of the scattering matrix at length `n_s` (`selT_phys`), which
  only reads the path up to `n_s` (`scatteringMatrix_extPast`).
* `measurable_b3ObsAll_past`: every observable `b3ObsAll … i u` with `⌊W(s+u)⌋ ≤ j` is
  `b3Sigma W j`-measurable (for a `growthSigma W n_s`-measurable frame).
* `conj_gramEntry_b3`: `conj (G_e) = G_{e*}` for the finite-`W` closed Gram state
  (`gramPair` with the Hermitian near projection).
* `zeta`: the discrete drift-free state at length `j` (discrete jumps `b3JumpAt`, `b3KJumpAt`;
  drift slot `0`; initial values at `n_s`), and its `b3Sigma W j`-measurability.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK.FW

open MeasureTheory Filter Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open scoped NNReal ENNReal ComplexConjugate

variable {W np K : ℕ}

/-!
## Generic measurability helpers (any σ-algebra on the domain)
-/

section Generic

variable {α : Type*} {mα : MeasurableSpace α}

theorem measurable_gst_of_entries {f : α → GSt K np}
    (h : ∀ e : GIdx K np, Measurable fun x => gramEntry e (f x)) : Measurable f := by
  have e : f = fun x => gramOfEntries fun e => gramEntry e (f x) := by
    funext x; exact (gramOfEntries_gramEntry _).symm
  rw [e]
  unfold gramOfEntries
  exact (measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun c => h (0, a, c)).prodMk
    (measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun c => h (1, a, c))

theorem measurable_kst_of_entries {f : α → KSt np}
    (h : ∀ a : KIdx np, Measurable fun x => f x a.1 a.2) : Measurable f :=
  measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun c => h (a, c)

theorem measurable_test_of {r : ℕ} {f : Fin r → α → ℂ} (hf : ∀ l, Measurable (f l))
    (ψ : BoundedContinuousFunction (Fin r → ℂ) ℝ) : Measurable fun x => ψ fun l => f l x :=
  ψ.continuous.measurable.comp (measurable_pi_iff.2 hf)

theorem measurable_pi_of {ι : Type*} [Countable ι] {f : α → ι → ℂ}
    (h : ∀ i, Measurable fun x => f x i) : Measurable f := measurable_pi_iff.2 h

end Generic

/-!
## Flag 3: the entrance coordinates are measurable at the closing length
-/

theorem physTseq_rho (b E s : ℝ) {j : ℕ} (hj : closeLen s W ≤ j) (k : ℕ)
    (y : ProbedPath W np × ℝ) :
    physTseq b E s W (Modul.rho W j np y).1.1 k = physTseq b E s W y.1.1 k := by
  obtain ⟨V, -, hV⟩ := EigenSelConstruct.measurableEigenSelection_holds (Fin W)
  rw [← selT_phys hV b E s, ← selT_phys hV b E s]
  simp only [Modul.rho, ClosedSumProof.scatteringMatrix_extPast hj b E]

/-- **The entrance coordinates are `b3Sigma W j`-measurable for `j ≥ n_s`.** -/
theorem measurable_physTseq_past (b E s : ℝ) {j : ℕ} (hj : closeLen s W ≤ j) (k : ℕ) :
    Measurable[b3Sigma W j np] fun y : ProbedPath W np × ℝ => physTseq b E s W y.1.1 k :=
  Modul.measurable_of_rho ((CapLaw.measurable_physTseq b E s W k).comp
    (measurable_fst.comp measurable_fst)) (physTseq_rho b E s hj k)

/-!
## The observables are adapted
-/

theorem le_limLenAll (s : ℝ) (W : ℕ) (u : ℝ≥0) : closeLen s W ≤ limLenAll s W u :=
  Nat.floor_mono (mul_le_mul_of_nonneg_left (by linarith [u.2]) (Nat.cast_nonneg W))

theorem measurable_b3ObsAll_past {b E s h : ℝ} {τ m : Fin np → ℝ}
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hV : Measurable[growthSigma W (closeLen s W)] Vs) (i : LIdx K np) {u : ℝ≥0} {j : ℕ}
    (hu : limLenAll s W u ≤ j) :
    Measurable[b3Sigma W j np] (b3ObsAll b E s h τ m W Vs i u) := by
  have h0 := le_limLenAll s W u
  rcases i with e | k | ij
  · exact Modul.measurable_b3X_past s h τ m h0 hu hV (Sum.inl e)
  · exact Complex.measurable_ofReal.comp (measurable_physTseq_past b E s (h0.trans hu) k)
  · exact Modul.measurable_b3X_past s h τ m h0 hu hV (Sum.inr ij)

/-- A bounded continuous test of finitely many adapted observables is adapted. -/
theorem measurable_test_past {b E s h : ℝ} {τ m : Fin np → ℝ}
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hV : Measurable[growthSigma W (closeLen s W)] Vs) {r : ℕ} (i : Fin r → LIdx K np)
    (u : Fin r → ℝ≥0) {j : ℕ} (hu : ∀ l, limLenAll s W (u l) ≤ j)
    (ψ : BoundedContinuousFunction (Fin r → ℂ) ℝ) :
    Measurable[b3Sigma W j np] fun y => ψ (fun l => b3ObsAll b E s h τ m W Vs (i l) (u l) y) :=
  measurable_test_of (fun l => measurable_b3ObsAll_past hV (i l) (hu l)) ψ

/-!
## Flag 4: Hermitian symmetry of the finite-`W` Gram state
-/

/-- **`conj (G_e) = G_{e*}`** for the finite-`W` closed Gram state. -/
theorem conj_gramEntry_b3 (b E s h : ℝ) (τ m : Fin np → ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (y : ProbedPath W np × ℝ)
    (e : GIdx K np) :
    conj (gramEntry e (b3ClosedGramAt b E s h τ m W j Vs y)) =
      gramEntry (eStar e) (b3ClosedGramAt b E s h τ m W j Vs y) :=
  ClosedSumProof.star_gramEntry _ (nearPortProj_conjTranspose (W := W)) _ e

/-- The diagonal Gram coordinates are real. -/
theorem im_gramEntry_diag_b3 (b E s h : ℝ) (τ m : Fin np → ℝ) (W j : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (y : ProbedPath W np × ℝ)
    (σ : Fin 2) (k : SrcCol K (Fin np)) :
    (gramEntry (σ, k, k) (b3ClosedGramAt b E s h τ m W j Vs y)).im = 0 := by
  have h := conj_gramEntry_b3 b E s h τ m W j Vs y (σ, k, k)
  exact Complex.conj_eq_iff_im.1 h

/-!
## The discrete state
-/

/-- The closed Gram state at length `j` is `b3Sigma W j`-measurable (`n_s ≤ i ≤ j`). -/
theorem measurable_b3ClosedGramAt_past {b E s h : ℝ} {τ m : Fin np → ℝ} {i j : ℕ}
    (hs : closeLen s W ≤ i) (hij : i ≤ j)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hV : Measurable[growthSigma W (closeLen s W)] Vs) :
    Measurable[b3Sigma W j np] (b3ClosedGramAt b E s h τ m W i Vs) :=
  measurable_gst_of_entries fun e =>
    Modul.measurable_b3X_past (b := b) (E := E) s h τ m (np := np) hs hij hV (Sum.inl e)

theorem measurable_b3ClosedKAt_past {b E s h : ℝ} {τ m : Fin np → ℝ} {i j : ℕ}
    (hs : closeLen s W ≤ i) (hij : i ≤ j)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hV : Measurable[growthSigma W (closeLen s W)] Vs) :
    Measurable[b3Sigma W j np] (b3ClosedKAt b E s h τ m W i) :=
  measurable_kst_of_entries fun a =>
    Modul.measurable_b3X_past (b := b) (E := E) s h τ m (Vs := Vs) hs hij hV (Sum.inr a)

/-- **The discrete drift-free state at length `j`**:
`((G_j − J_j, 0, G_{n_s}), 𝒦_j − J^𝒦_j, 𝒦_j − J^𝒦_j − 𝒦_{n_s}, 𝒦_{n_s})`. -/
def zeta (b E s h : ℝ) (τ m : Fin np → ℝ) (W : ℕ)
    (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (j : ℕ)
    (y : ProbedPath W np × ℝ) : ZK K np :=
  ((b3ClosedGramAt b E s h τ m W j Vs y - b3JumpAt b s τ m W j, 0,
      b3ClosedGramAt b E s h τ m W (closeLen s W) Vs y),
    b3ClosedKAt b E s h τ m W j y - b3KJumpAt E s τ m W j,
    fun a => (b3ClosedKAt b E s h τ m W j y - b3KJumpAt E s τ m W j) a.1 a.2 -
      b3ClosedKAt b E s h τ m W (closeLen s W) y a.1 a.2,
    b3ClosedKAt b E s h τ m W (closeLen s W) y)

theorem measurable_zeta_past {b E s h : ℝ} {τ m : Fin np → ℝ} {j : ℕ} (hs : closeLen s W ≤ j)
    {Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hV : Measurable[growthSigma W (closeLen s W)] Vs) :
    Measurable[b3Sigma W j np] (zeta b E s h τ m W Vs j) := by
  have hX := fun c => Modul.measurable_b3X_past (b := b) (E := E) s h τ m (np := np) hs le_rfl hV c
  have hX0 := fun c => Modul.measurable_b3X_past (b := b) (E := E) s h τ m (np := np)
    (le_refl (closeLen s W)) hs hV c
  have hG : Measurable[b3Sigma W j np] fun y =>
      b3ClosedGramAt b E s h τ m W j Vs y - b3JumpAt (K := K) b s τ m W j :=
    measurable_gst_of_entries fun e => by
      simp only [gramEntry_sub']; exact (hX (Sum.inl e)).sub measurable_const
  have hG0 : Measurable[b3Sigma W j np] (b3ClosedGramAt b E s h τ m W (closeLen s W) Vs) :=
    measurable_gst_of_entries fun e => hX0 (Sum.inl e)
  have hK : Measurable[b3Sigma W j np] fun y =>
      b3ClosedKAt b E s h τ m W j y - b3KJumpAt E s τ m W j :=
    measurable_kst_of_entries fun a => by
      simp only [Matrix.sub_apply]; exact (hX (Sum.inr a)).sub measurable_const
  have hK0 : Measurable[b3Sigma W j np] (b3ClosedKAt b E s h τ m W (closeLen s W)) :=
    measurable_kst_of_entries fun a => hX0 (Sum.inr a)
  refine (hG.prodMk (measurable_const.prodMk hG0)).prodMk
    (hK.prodMk ((measurable_pi_of fun a => ?_).prodMk hK0))
  simp only [Matrix.sub_apply]
  exact ((hX (Sum.inr a)).sub measurable_const).sub (hX0 (Sum.inr a))

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK.FW
