module

public import BlockBand.Window.Count.Statement

/-!
# The refined count: scalar identities and the fresh-block split

* `matchedA_quadratic`, `commonZ_eq`: for `|E| ≤ 2`, `a² + E a + 1 = 0`, hence
  `z₀ = a⁻¹ + 2ba = -E - (1-2b)a` (the `z₀` of the fresh count lemma).
* `abs_phaseCount_le`: `|Θ_z(F)| ≤ dim` for every matrix and every `z`.
* `RingFreshBlockSplit`: an everywhere form of the fresh-block split. This everywhere form cannot
  hold: the transport clauses fail at non-Hermitian `H`. The proofs use the almost-sure form
  `RingFreshBlockSplitAE` (proved as `ringFreshBlockSplitAE`).
  The split expresses Schur inertia `N_H(E) = N_{H_R}(E) + N_-(A_k - E - Σ)` a.s., the
  transport of `Σ` and its phase/trace to `Fin W` coordinates, and the independence of the
  fresh block `A_k ~ GUE_W(c/W)` from `Σ` (the law of `(Σ, A_k)` is a product).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Window.Count

open MeasureTheory ProbabilityTheory
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open scoped ENNReal NNReal

theorem matchedA_quadratic {E : ℝ} (hE : |E| ≤ 2) :
    matchedA E ^ 2 + (E : ℂ) * matchedA E + 1 = 0 := by
  have hs : Real.sqrt (4 - E * E) * Real.sqrt (4 - E * E) = 4 - E * E := by
    rw [Real.mul_self_sqrt]; nlinarith [abs_le.mp hE]
  apply Complex.ext <;> simp [matchedA, sq, Complex.mul_re, Complex.mul_im] <;> nlinarith [hs]

theorem matchedA_ne_zero {E : ℝ} (hE : |E| ≤ 2) : matchedA E ≠ 0 := by
  intro h
  have := matchedA_quadratic hE
  rw [h] at this; simp at this

/-- `z₀ = a⁻¹ + 2ba = -E - (1-2b) a` on `|E| ≤ 2`. -/
theorem commonZ_eq (b : ℝ) {E : ℝ} (hE : |E| ≤ 2) :
    commonZ b E = -(E : ℂ) - ((1 - 2 * b : ℝ) : ℂ) * matchedA E := by
  have ha := matchedA_ne_zero hE
  have hq := matchedA_quadratic hE
  unfold commonZ
  have hinv : (matchedA E)⁻¹ = -(E : ℂ) - matchedA E := by
    field_simp
    linear_combination hq
  rw [hinv]; push_cast; ring

theorem abs_le_two_of_mem_bulk {κ E : ℝ} (hκ : 0 < κ) (hE : E ∈ bulkInterval κ) : |E| ≤ 2 := by
  obtain ⟨h1, h2⟩ := hE
  rw [abs_le]; constructor <;> linarith

theorem abs_phaseCount_le {ι : Type} [Fintype ι] [DecidableEq ι] (z : ℂ) (F : Matrix ι ι ℂ) :
    |phaseCount z F| ≤ Fintype.card ι := by
  unfold phaseCount BlockBand.Internal.Contracts.Inputs.spectralSum
  rw [abs_div, abs_of_pos Real.pi_pos, div_le_iff₀ Real.pi_pos]
  calc |(F.charpoly.roots.map (fun w => Complex.arg (z - (w.re : ℂ)))).sum|
      ≤ (F.charpoly.roots.map (fun w => |Complex.arg (z - (w.re : ℂ))|)).sum := by
        simpa [Multiset.map_map] using
          Multiset.abs_sum_le_sum_abs (s := F.charpoly.roots.map
            (fun w => Complex.arg (z - (w.re : ℂ))))
    _ ≤ (F.charpoly.roots.map (fun _ => Real.pi)).sum :=
        Multiset.sum_map_le_sum_map _ _ fun w _ => abs_le.mpr
          ⟨(Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩
    _ = Multiset.card F.charpoly.roots * Real.pi := by simp
    _ ≤ Fintype.card ι * Real.pi := by
        gcongr
        exact_mod_cast (Polynomial.card_roots' _).trans (by simp)

/-- The fresh-block split of the physical ring, in an everywhere form. For every
admissible `p`, realization `model` of the physical law, block `k` and real `E` there are
measurable `Σ̃, Ã : SiteMatrix → Matrix (Fin W) (Fin W) ℂ` (`Σ̃` Hermitian) such that
1. (Schur inertia) a.s. `N_H(E) = N_{H_R}(E) + N_-(Ã - E - Σ̃)`, with `H_R` the
   ring with block `k` deleted, written as `N_{H_R}(E) = Ξ_{n-1} - Θ_{z₀}(Σ_k)` through the
   definition of `ringCompensatedPhase`;
2. (transport) `Θ_{z₀}(Σ_k(H)) = Θ_{z₀}(Σ̃(H))` and `W⁻¹ Tr(z₀ - Σ_k(H))⁻¹ = W⁻¹ Tr(z₀ - Σ̃(H))⁻¹`
   for `Σ_k = oneBlockComplement p k · E`, `z₀ = commonZ b E`;
3. (fresh block) the law of `(Σ̃, Ã)` is `law(Σ̃) ⊗ GUE_W(c/W)`.
This everywhere form cannot hold: the transport clauses fail at non-Hermitian `H`. The proofs use
the almost-sure form `RingFreshBlockSplitAE` (proved as `ringFreshBlockSplitAE`). -/
def RingFreshBlockSplit : Prop :=
  ∀ (p : BlockBand.Parameters) (model : p.GaussianRingModel) (k : ZMod p.n) (E : ℝ),
    ∃ (Sg Af : p.SiteMatrix → Matrix (Fin p.W) (Fin p.W) ℂ),
      Measurable Sg ∧ Measurable Af ∧ (∀ H, (Sg H).IsHermitian) ∧
      (∀ᵐ H ∂(model.law : Measure p.SiteMatrix),
        (physicalCount p H E : ℝ) =
          ringCompensatedPhase p k H E -
            phaseCount (commonZ p.b E) (oneBlockComplement p k H E) +
            negativeCount (Af H - (E : ℂ) • 1 - Sg H)) ∧
      (∀ H, phaseCount (commonZ p.b E) (oneBlockComplement p k H E) =
        phaseCount (commonZ p.b E) (Sg H)) ∧
      (∀ H, oneBlockTrace p k ((commonZ p.b E • 1 - oneBlockComplement p k H E)⁻¹) =
        (p.W : ℂ)⁻¹ * ((commonZ p.b E • 1 - Sg H)⁻¹).trace) ∧
      (model.law : Measure p.SiteMatrix).map (fun H => (Sg H, Af H)) =
        ((model.law : Measure p.SiteMatrix).map Sg).prod
          (gueMeasure (Fin p.W) (Real.toNNReal (p.c / p.W)))

end BlockBand.Window.Count
